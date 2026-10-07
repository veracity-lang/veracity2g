#!/usr/bin/env python3
"""Render DSWP task decompositions as JPG images.

For every input .vcy file (or every .vcy file in an input folder) this runs

    ./vcy interp <file> --dswp --synthesize-locks --emit-tasks

from the repository root, parses the printed tasks, and draws them as a
graph: one card per task (header = id + Doall/Sequential, body = code with
synthesized locks highlighted), arrows labelled with the variables each
dependency carries and its commute condition, and dotted arrows from the
Init task to the tasks it spawns.

Usage (from anywhere):
    python reports/tasks_to_jpg.py benchmarks/global_commutativity/intro.vcy
    python reports/tasks_to_jpg.py benchmarks/global_commutativity/ -o reports/tasks-img
    python reports/tasks_to_jpg.py a.vcy b.vcy some_dir/ --save-txt
"""

import argparse
import math
import os
import re
import subprocess
import sys
import textwrap

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch, Rectangle

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
VCY = os.path.join(REPO_ROOT, "vcy")
VCY_ARGS = ["interp", None, "--dswp", "--synthesize-locks", "--emit-tasks"]

# ---------------------------------------------------------------- parsing

HEADER_RE = re.compile(r"^=== (Init Task|Task (\d+) \((\w+)\)) ===\s*$")
DEP_RE = re.compile(
    r"from (\d+) \[new job: (true|false)\]: (.*?)(?= AND from \d+ \[new job: |$)"
)


def parse_deps(s):
    """'{from 1 [new job: false]: int x / commute_cond: ... AND from 4 ...}'"""
    s = s.strip()
    if s.startswith("{") and s.endswith("}"):
        s = s[1:-1]
    deps = []
    for m in DEP_RE.finditer(s):
        payload = m.group(3).strip()
        vars_, cond = payload, None
        if " / commute_cond: " in payload:
            vars_, cond = payload.split(" / commute_cond: ", 1)
        deps.append(
            {
                "task": int(m.group(1)),
                "new_job": m.group(2) == "true",
                "vars": vars_.strip(),
                "cond": cond.strip() if cond else None,
            }
        )
    return deps


def parse_tasks(output):
    """Return (init, tasks); init is a dict or None, tasks a list of dicts."""
    init, tasks, cur = None, [], None
    for line in output.splitlines():
        m = HEADER_RE.match(line)
        if m:
            if m.group(1) == "Init Task":
                cur = {"id": "init", "label": "Init", "spawns": [],
                       "deps_in": [], "deps_out": [], "body": []}
                init = cur
            else:
                cur = {"id": int(m.group(2)), "label": m.group(3), "spawns": [],
                       "deps_in": [], "deps_out": [], "body": []}
                tasks.append(cur)
            continue
        if cur is None:
            continue
        if line.startswith("spawns:"):
            cur["spawns"] = [int(x) for x in re.findall(r"\d+", line)]
        elif line.startswith("deps_in:"):
            cur["deps_in"] = parse_deps(line[len("deps_in:"):])
        elif line.startswith("deps_out:"):
            cur["deps_out"] = parse_deps(line[len("deps_out:"):])
        else:
            cur["body"].append(line.rstrip())
    for t in ([init] if init else []) + tasks:
        while t["body"] and not t["body"][-1].strip():
            t["body"].pop()
        while t["body"] and not t["body"][0].strip():
            t["body"].pop(0)
    return init, tasks


# ---------------------------------------------------------------- drawing

FS = 9                 # font size (pt)
CW = 0.6 * FS          # monospace char width (pt)
LH = 1.3 * FS          # line height (pt)
PAD = 8                # inner card padding (pt)
GAP_X, GAP_Y = 170, 130  # gaps between cards (pt), room for edge labels
LABEL_WRAP = 40         # wrap width for edge labels (chars)
RAD_CANDIDATES = (0.15, -0.15, 0.3, -0.3, 0.5, -0.5, 0.7, -0.7)  # arrow curvatures to try

COLORS = {
    "Init": ("#5b6770", "#eef1f3"),
    "Doall": ("#2a7d4f", "#eaf6ef"),
    "Sequential": ("#2f5d9e", "#eaf0f9"),
}
LOCK_COLOR = "#c0392b"
EDGE_COLOR = "#444444"
COND_EDGE_COLOR = "#d68910"


def card_lines(t):
    """List of (text, kind) lines for a card body (dependencies go on the edges)."""
    lines = []
    if t["id"] == "init" and t["spawns"]:
        lines += [("spawns: " + ", ".join(map(str, t["spawns"])), "meta"), ("", "meta")]
    for b in t["body"]:
        kind = "lock" if re.search(r"mutex_(lock|unlock)", b) else "code"
        lines.append((b.replace("\t", "  "), kind))
    return lines


def collect_edges(tasks):
    """{(src, dst): [dep, ...]} from deps_out, plus deps_in entries not mirrored there."""
    edges = {}
    for t in tasks:
        for d in t["deps_out"]:
            edges.setdefault((t["id"], d["task"]), []).append(d)
    for t in tasks:
        for d in t["deps_in"]:
            key = (d["task"], t["id"])
            if key not in edges:
                edges.setdefault(key, []).append(d)
    return edges


def edge_label(deps):
    """Text for an edge: the variables carried, then any commute conditions."""
    parts = []
    vars_ = sorted({v.strip() for d in deps for v in d["vars"].split(";") if v.strip()
                    and v.strip() != "[]"})
    if vars_:
        parts += textwrap.wrap(", ".join(vars_), LABEL_WRAP)
    for cond in dict.fromkeys(d["cond"] for d in deps if d["cond"]):
        parts += textwrap.wrap("commute: " + cond, LABEL_WRAP, subsequent_indent="  ")
    return "\n".join(parts)


def box_contains(box, x, y, margin=2):
    return (box.get_x() - margin <= x <= box.get_x() + box.get_width() + margin and
            box.get_y() - margin <= y <= box.get_y() + box.get_height() + margin)


def arc_points(a, b, rad, n=200):
    """Sampled arc3 curve between the centres of boxes a and b (y-down data coords)."""
    ax_, ay = a.get_x() + a.get_width() / 2, a.get_y() + a.get_height() / 2
    bx, by = b.get_x() + b.get_width() / 2, b.get_y() + b.get_height() / 2
    # arc3 control point, converted from matplotlib's y-up display coordinates
    cx, cy = (ax_ + bx) / 2 - rad * (by - ay), (ay + by) / 2 + rad * (bx - ax_)
    return [((1 - u) ** 2 * ax_ + 2 * (1 - u) * u * cx + u ** 2 * bx,
             (1 - u) ** 2 * ay + 2 * (1 - u) * u * cy + u ** 2 * by)
            for u in (i / n for i in range(n + 1))]


def choose_rad(a, b, others):
    """Curvature whose visible part crosses the fewest other cards (ties: least bent)."""
    best = None
    for rad in RAD_CANDIDATES:
        pts = [p for p in arc_points(a, b, rad)
               if not box_contains(a, *p) and not box_contains(b, *p)]
        hits = sum(1 for p in pts for o in others if box_contains(o, *p, margin=6))
        if best is None or hits < best[0]:
            best = (hits, rad)
        if hits == 0:
            break
    return best[1]


def label_size(text):
    lines = text.split("\n")
    fs = FS - 1
    return (max(len(l) for l in lines) * 0.6 * fs + fs,
            len(lines) * 1.15 * 1.2 * fs + fs)


def rects_overlap(r1, r2, margin=3):
    return not (r1[2] + margin < r2[0] or r2[2] + margin < r1[0] or
                r1[3] + margin < r2[1] or r2[3] + margin < r1[1])


def place_label(pts, size, boxes, taken):
    """Point along pts (the visible part of an edge) where a label of the given
    size overlaps the fewest cards and already placed labels."""
    w, h = size
    best = None
    for frac in (0.5, 0.4, 0.6, 0.3, 0.7, 0.2, 0.8, 0.12, 0.88):
        x, y = pts[int(frac * (len(pts) - 1))]
        r = (x - w / 2, y - h / 2, x + w / 2, y + h / 2)
        cost = sum(rects_overlap(r, (o.get_x(), o.get_y(), o.get_x() + o.get_width(),
                                     o.get_y() + o.get_height())) for o in boxes)
        cost += 2 * sum(rects_overlap(r, t) for t in taken)
        if best is None or cost < best[0]:
            best = (cost, (x, y), r)
        if cost == 0:
            break
    taken.append(best[2])
    return best[1]


def render(init, tasks, title, out_path):
    cards = ([init] if init else []) + tasks
    for c in cards:
        c["lines"] = card_lines(c)
        c["w"] = max([len(s) for s, _ in c["lines"]] + [24]) * CW + 2 * PAD
        c["h"] = (len(c["lines"]) + 1) * LH + 2 * PAD + 4  # +1 for header

    # Layout: Init on its own row, then tasks in a grid (sorted by id).
    rows = []
    if init:
        rows.append([init])
    ordered = sorted(tasks, key=lambda t: t["id"])
    ncol = max(1, min(4, math.ceil(math.sqrt(len(ordered))))) if ordered else 1
    for i in range(0, len(ordered), ncol):
        rows.append(ordered[i:i + ncol])

    # Widen the horizontal gap so the widest edge label fits between cards.
    labels = [edge_label(d) for (src, dst), d in collect_edges(tasks).items() if src != dst]
    gap_x = min(420, max([GAP_X] + [label_size(l)[0] + 30 for l in labels if l]))

    row_w = [sum(c["w"] for c in r) + gap_x * (len(r) - 1) for r in rows]
    total_w = max(row_w + [400]) + 2 * gap_x
    title_h = 3 * LH
    y = title_h
    for r, rw in zip(rows, row_w):
        x = (total_w - rw) / 2
        rh = max(c["h"] for c in r)
        for c in r:
            c["x"], c["y"] = x, y   # top-left, y grows downward
            x += c["w"] + gap_x
        y += rh + GAP_Y
    total_h = y - GAP_Y + LH * 4  # room for legend

    fig = plt.figure(figsize=(total_w / 72, total_h / 72), dpi=150)
    ax = fig.add_axes([0, 0, 1, 1])
    ax.set_xlim(0, total_w)
    ax.set_ylim(total_h, 0)
    ax.axis("off")

    ax.text(total_w / 2, LH * 1.5, title, ha="center", va="center",
            fontsize=FS + 4, fontweight="bold")

    patches = {}
    for c in cards:
        dark, light = COLORS.get(c["label"], COLORS["Sequential"])
        box = FancyBboxPatch((c["x"], c["y"]), c["w"], c["h"],
                             boxstyle="round,pad=0,rounding_size=6",
                             fc=light, ec=dark, lw=1.5, zorder=2)
        ax.add_patch(box)
        patches[c["id"]] = box
        ax.add_patch(Rectangle((c["x"], c["y"]), c["w"], LH + PAD,
                               fc=dark, ec=dark, zorder=3))
        name = "Init Task" if c["id"] == "init" else f"Task {c['id']}  ({c['label']})"
        ax.text(c["x"] + PAD, c["y"] + (LH + PAD) / 2, name, color="white",
                fontsize=FS + 1, fontweight="bold", va="center",
                family="monospace", zorder=4)
        ty = c["y"] + LH + PAD + PAD
        for s, kind in c["lines"]:
            style = dict(fontsize=FS, family="monospace", va="top", zorder=4)
            if kind == "lock":
                style.update(color=LOCK_COLOR, fontweight="bold")
            elif kind == "meta":
                style.update(color="#555555")
            ax.text(c["x"] + PAD, ty, s, **style)
            ty += LH

    # Edges between tasks, each labelled with the variables it carries and
    # its commute condition (if any).
    label_style = dict(fontsize=FS - 1, family="monospace", ha="center", va="center",
                       zorder=6, linespacing=1.15)
    taken = []  # rectangles of labels already placed
    for (src, dst), deps in collect_edges(tasks).items():
        if src not in patches or dst not in patches:
            continue
        has_cond = any(d["cond"] for d in deps)
        new_job = any(d["new_job"] for d in deps)
        color = COND_EDGE_COLOR if has_cond else EDGE_COLOR
        label = edge_label(deps)
        a, b = patches[src], patches[dst]
        bbox = dict(boxstyle="round,pad=0.25", fc="white", ec=color, lw=0.6, alpha=0.95)
        if src == dst:
            # self-loop on the card's right edge
            x = a.get_x() + a.get_width()
            y0 = a.get_y() + LH + PAD + 6
            ax.add_patch(FancyArrowPatch(
                (x, y0), (x, y0 + 2.2 * LH), arrowstyle="-|>", mutation_scale=12,
                connectionstyle="arc3,rad=-1.6", lw=1.4, color=color,
                linestyle="--" if new_job else "-", zorder=5))
            if label:
                lx, ly = x + 2.2 * LH + 4, y0 + 1.1 * LH
                w, h = label_size(label)
                taken.append((lx, ly - h / 2, lx + w, ly + h / 2))
                ax.text(lx, ly, label, color=color, bbox=bbox,
                        **dict(label_style, ha="left"))
            continue
        others = [p for k, p in patches.items() if k not in (src, dst)]
        rad = choose_rad(a, b, others)
        ca = (a.get_x() + a.get_width() / 2, a.get_y() + a.get_height() / 2)
        cb = (b.get_x() + b.get_width() / 2, b.get_y() + b.get_height() / 2)
        ax.add_patch(FancyArrowPatch(
            ca, cb, patchA=a, patchB=b, arrowstyle="-|>", mutation_scale=14,
            connectionstyle=f"arc3,rad={rad}", lw=1.6 if has_cond else 1.2,
            color=color, linestyle="--" if new_job else "-", zorder=1.5))
        if label:
            pts = [p for p in arc_points(a, b, rad)
                   if not box_contains(a, *p) and not box_contains(b, *p)]
            if not pts:
                pts = [((ca[0] + cb[0]) / 2, (ca[1] + cb[1]) / 2)]
            lx, ly = place_label(pts, label_size(label), patches.values(), taken)
            ax.text(lx, ly, label, color=color, bbox=bbox, **label_style)
    if init:
        a = patches["init"]
        for s in init["spawns"]:
            if s not in patches:
                continue
            b = patches[s]
            ca = (a.get_x() + a.get_width() / 2, a.get_y() + a.get_height() / 2)
            cb = (b.get_x() + b.get_width() / 2, b.get_y() + b.get_height() / 2)
            ax.add_patch(FancyArrowPatch(
                ca, cb, patchA=a, patchB=b, arrowstyle="-|>", mutation_scale=10,
                lw=0.8, color="#999999", linestyle=":", zorder=1))

    legend = ("legend:  solid = dependency    dashed = new job    "
              "orange = has commute condition    loop = self-dependency    dotted = spawn    "
              "red = synthesized lock")
    ax.text(total_w / 2, total_h - LH * 1.5, legend, ha="center", va="center",
            fontsize=FS - 1, color="#666666")

    fig.savefig(out_path, format="jpg", dpi=150,
                pil_kwargs={"quality": 92}, facecolor="white")
    plt.close(fig)


# ---------------------------------------------------------------- driver

def collect_inputs(paths, recursive):
    files = []
    for p in paths:
        if os.path.isdir(p):
            if recursive:
                for root, _, names in os.walk(p):
                    files += [os.path.join(root, n) for n in names if n.endswith(".vcy")]
            else:
                files += [os.path.join(p, n) for n in os.listdir(p) if n.endswith(".vcy")]
        elif os.path.isfile(p):
            files.append(p)
        else:
            print(f"warning: {p} not found, skipping", file=sys.stderr)
    return sorted(set(os.path.abspath(f) for f in files))


def run_vcy(path, timeout):
    args = [VCY] + [path if a is None else a for a in VCY_ARGS]
    proc = subprocess.run(args, cwd=REPO_ROOT, capture_output=True,
                          text=True, timeout=timeout)
    return proc.stdout, proc.stderr, proc.returncode


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("inputs", nargs="+", help=".vcy files and/or folders")
    ap.add_argument("-o", "--out-dir",
                    default=os.path.join(REPO_ROOT, "reports", "tasks-img"),
                    help="output folder for the .jpg files (default: reports/tasks-img)")
    ap.add_argument("-r", "--recursive", action="store_true",
                    help="search folders recursively")
    ap.add_argument("--save-txt", action="store_true",
                    help="also save the raw --emit-tasks output next to each jpg")
    ap.add_argument("--timeout", type=int, default=120,
                    help="per-file timeout in seconds (default: 120)")
    args = ap.parse_args()

    if not os.path.exists(VCY):
        sys.exit(f"error: {VCY} not found — run `make` in the repo root first")

    files = collect_inputs(args.inputs, args.recursive)
    if not files:
        sys.exit("error: no .vcy input files found")
    os.makedirs(args.out_dir, exist_ok=True)

    ok, failed = 0, []
    for f in files:
        name = os.path.splitext(os.path.basename(f))[0]
        rel = os.path.relpath(f, REPO_ROOT)
        try:
            out, err, rc = run_vcy(f, args.timeout)
        except subprocess.TimeoutExpired:
            failed.append((rel, "timeout"))
            print(f"[FAIL] {rel}: timeout")
            continue
        init, tasks = parse_tasks(out)
        if not tasks and init is None:
            msg = (out + err).strip().splitlines()
            failed.append((rel, msg[-1] if msg else f"exit code {rc}"))
            print(f"[FAIL] {rel}: {failed[-1][1]}")
            continue
        if args.save_txt:
            with open(os.path.join(args.out_dir, name + ".txt"), "w") as fh:
                fh.write(out)
        jpg = os.path.join(args.out_dir, name + ".jpg")
        render(init, tasks, rel, jpg)
        ok += 1
        print(f"[ OK ] {rel} -> {os.path.relpath(jpg)}  ({len(tasks)} tasks)")

    print(f"\n{ok} image(s) written to {args.out_dir}, {len(failed)} failed")
    return 1 if failed and not ok else 0


if __name__ == "__main__":
    sys.exit(main())
