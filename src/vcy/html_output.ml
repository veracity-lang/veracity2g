let read_file path =
  let ic = open_in path in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.to_string s

let html_escape s =
  let buf = Buffer.create (String.length s + 16) in
  String.iter (function
    | '<' -> Buffer.add_string buf "&lt;"
    | '>' -> Buffer.add_string buf "&gt;"
    | '&' -> Buffer.add_string buf "&amp;"
    | '"' -> Buffer.add_string buf "&quot;"
    | c   -> Buffer.add_char   buf c
  ) s;
  Buffer.contents buf

(* Parse "file:[sl.sc-el.ec]" → (sl, el) line range, ignoring columns. *)
let parse_line_range s =
  try
    let bracket = String.index s '[' in
    let dot1    = String.index_from s (bracket + 1) '.' in
    let dash    = String.index_from s (dot1 + 1)    '-' in
    let dot2    = String.index_from s (dash + 1)    '.' in
    let close   = String.index_from s (dot2 + 1)    ']' in
    let sl = int_of_string (String.sub s (bracket+1) (dot1 - bracket - 1)) in
    let el = int_of_string (String.sub s (dash+1)    (dot2 - dash   - 1)) in
    ignore close;
    Some (sl, el)
  with _ -> None

(* Run dot -Tsvg on a .dot file; return the SVG string or None. *)
let dot_to_svg dot_path =
  let svg_path = Filename.remove_extension dot_path ^ ".svg" in
  let cmd = Printf.sprintf "dot -Tsvg %s -o %s 2>/dev/null"
              (Filename.quote dot_path) (Filename.quote svg_path) in
  if Sys.command cmd = 0 then
    (try Some (read_file svg_path) with _ -> None)
  else None

(* Collect all SVGs from a directory: pre-built .svg files first,
   then .dot files converted via graphviz. *)
let svgs_of_subdir subdir =
  try
    let entries = Sys.readdir subdir |> Array.to_list |> List.sort String.compare in
    (* Pre-built SVGs and HTML fragments (e.g. the variable table) are
       included in sorted order — "heap_diagram.svg" before "heap_table.html". *)
    let prebuilt = entries
      |> List.filter (fun f ->
           let ext = Filename.extension f in
           (ext = ".svg" || ext = ".html") && f <> "index.html")
      |> List.filter_map (fun f ->
           try Some (read_file (Filename.concat subdir f)) with _ -> None)
    in
    let dot_svgs = entries
      |> List.filter (fun f -> Filename.extension f = ".dot")
      |> List.map (fun f -> Filename.concat subdir f)
      |> List.filter_map dot_to_svg
    in
    prebuilt @ dot_svgs
  with _ -> []


let css = {|<style>
*{box-sizing:border-box}
body{margin:0;padding:20px 24px;background:#1e1e1e;color:#d4d4d4;
     font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif}
h1{color:#569cd6;margin:0 0 4px}
.meta{color:#888;font-size:.85em;margin-bottom:18px}
.meta code{color:#9cdcfe;background:#2d2d2d;padding:1px 5px;border-radius:3px}
.layout{display:flex;gap:20px;align-items:flex-start}
.src-panel{flex:1 1 auto;min-width:0;overflow-x:auto}
table.src{border-collapse:collapse;width:100%;font-family:'Consolas','Monaco',monospace;
          font-size:.85em;background:#252526;border-radius:6px;overflow:hidden}
table.src td{padding:1px 8px;white-space:pre;vertical-align:top}
.ln{color:#555;user-select:none;text-align:right;border-right:1px solid #333;
    padding-right:10px;min-width:44px}
.code{color:#d4d4d4}
tr.cm{background:#132236;cursor:pointer}
tr.cm:hover{background:#1b3a5e}
tr.cm.active{background:#1f3f6e}
tr.cm .ln{color:#4ec9b0}
tr.cm .code{color:#9cdcfe}
.badge{display:inline-block;background:#0e639c;color:#fff;font-size:.72em;
       border-radius:3px;padding:0 5px;margin-left:10px;vertical-align:middle}
/* side diagram panel */
.diag-panel{display:none;flex:0 0 60%;position:sticky;top:20px;
            background:#252526;border:1px solid #3c3c3c;border-radius:8px;
            padding:20px;max-height:calc(100vh - 40px);overflow-y:auto}
.diag-panel h2{margin-top:0;color:#569cd6;font-size:1.1em}
.mloc{color:#888;font-size:.82em;margin-bottom:8px}
.mcond{background:#1a1a1a;border:1px solid #333;border-radius:4px;
       padding:10px 14px;font-family:monospace;color:#4ec9b0;
       word-break:break-all;margin-bottom:14px}
.diagrams svg{max-width:100%;height:auto;display:block;background:#fff;
              border:1px solid #ccc;border-radius:4px;margin:6px 0}
.nodiag{color:#666;font-style:italic;font-size:.9em}
.mlinks{margin-top:14px;font-size:.9em}
.mlinks a{color:#4ec9b0;text-decoration:none}
.mlinks a:hover{text-decoration:underline}
.closebtn{float:right;cursor:pointer;font-size:1.5em;color:#666;line-height:1}
.closebtn:hover{color:#d4d4d4}
</style>|}

let js_prefix = {|<script>
var _activeRow = null;
function openModal(n){
  var panel = document.getElementById('diag-panel');
  var content = document.getElementById('diag-content');
  var d = commuteData[n];
  if(!d){
    content.innerHTML =
      '<span class="closebtn" onclick="closePanel()">&times;</span>' +
      '<h2>Commute Block ' + n + '</h2>' +
      '<div class="mloc" style="color:#888">No query data &mdash; verification did not reach this block.</div>';
    panel.style.display = 'block';
    if(_activeRow){ _activeRow.classList.remove('active'); }
    var rows = document.querySelectorAll('tr.cm');
    rows.forEach(function(r){ if(r.getAttribute('data-cid')==String(n)){ _activeRow=r; r.classList.add('active'); } });
    return;
  }
  content.innerHTML =
    '<span class="closebtn" onclick="closePanel()">&times;</span>' +
    '<h2>Commute Block ' + n + '</h2>' +
    '<div class="mloc">' + d.loc + '</div>' +
    '<div class="mcond">' + d.cond + '</div>' +
    '<div class="diagrams">' + d.diagrams + '</div>' +
    '<div class="mlinks">' + d.link + '</div>';
  panel.style.display = 'block';
  if(_activeRow){ _activeRow.classList.remove('active'); }
  var rows = document.querySelectorAll('tr.cm');
  rows.forEach(function(r){ if(r.getAttribute('data-cid')==String(n)){ _activeRow=r; r.classList.add('active'); } });
}
function closePanel(){
  document.getElementById('diag-panel').style.display='none';
  if(_activeRow){ _activeRow.classList.remove('active'); _activeRow=null; }
}
document.addEventListener('keydown',function(e){
  if(e.key==='Escape') closePanel();
});
|}

let js_suffix = {|</script>|}

let dswp_css = {|<style>
*{box-sizing:border-box}
body{margin:0;padding:20px 24px;background:#1e1e1e;color:#d4d4d4;
     font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif}
h1{color:#569cd6;margin:0 0 4px}
h2{color:#4ec9b0;margin:24px 0 10px;font-size:1.05em;text-transform:uppercase;
   letter-spacing:.06em;border-bottom:1px solid #3c3c3c;padding-bottom:6px}
.meta{color:#888;font-size:.85em;margin-bottom:18px}
.meta strong{color:#9cdcfe}
.svg-wrap{background:#fff;border:1px solid #3c3c3c;border-radius:6px;
          overflow:auto;max-width:100%;margin-bottom:20px}
.svg-wrap svg{display:block;max-width:100%;height:auto}
.tasks-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(320px,1fr));
            gap:14px;margin-bottom:20px}
.task-card{background:#252526;border:1px solid #3c3c3c;border-radius:8px;padding:16px}
.task-card h3{margin:0 0 8px;color:#569cd6;font-size:1em;display:flex;
              align-items:center;gap:8px}
.badge{display:inline-block;font-size:.72em;border-radius:3px;padding:1px 6px;
       font-weight:600;vertical-align:middle}
.badge-doall{background:#0e7c0e;color:#fff}
.badge-seq{background:#7c4a0e;color:#fff}
.deps{font-size:.82em;color:#888;margin-bottom:6px}
.deps strong{color:#b5b5b5}
.task-body{background:#1a1a1a;border:1px solid #333;border-radius:4px;
           padding:10px 12px;font-family:'Consolas','Monaco',monospace;
           font-size:.83em;color:#d4d4d4;white-space:pre-wrap;
           word-break:break-all;margin:8px 0 0;max-height:300px;overflow-y:auto}
.init-task{background:#252526;border:1px solid #3c3c3c;border-radius:8px;
           padding:16px;margin-bottom:14px}
.init-task h3{margin:0 0 8px;color:#c586c0;font-size:1em}
.init-task .task-body{color:#ce9178}
table.src{border-collapse:collapse;width:100%;
          font-family:'Consolas','Monaco',monospace;font-size:.85em;
          background:#252526;border-radius:6px;overflow:hidden}
table.src td{padding:1px 8px;white-space:pre;vertical-align:top}
.ln{color:#555;user-select:none;text-align:right;border-right:1px solid #333;
    padding-right:10px;min-width:44px}
.nosvg{color:#666;font-style:italic;font-size:.9em;padding:16px}
</style>|}
(* Resolve this run's output directory: a directory handed down by a calling
   tool (or --out-dir) wins; otherwise $VERACITY_OUT; otherwise a fresh
   ./veracity_output/run_NNNN/ in the CWD.  Output lands next to the user's
   work rather than in /tmp, where it used to be reaped and unfindable. *)
(* Scan pretty-printed VCY text for commute block line ranges.
   Returns [(start_line, end_line)] in appearance order (1-indexed).
   Relies on the pretty-printer always emitting "commute_" as a line prefix. *)
let find_commute_line_ranges text =
  let lines = String.split_on_char '\n' text in
  let ranges  = ref [] in
  let depth   = ref 0 in
  let active  = ref false in
  let c_start = ref 0 in
  let c_base  = ref 0 in
  List.iteri (fun i line ->
    let lineno  = i + 1 in
    let trimmed = String.trim line in
    let n       = String.length trimmed in
    if (not !active) && n >= 8 && String.sub trimmed 0 8 = "commute_" then begin
      active  := true;
      c_start := lineno;
      c_base  := !depth
    end;
    String.iter (function
      | '{' -> incr depth
      | '}' ->
        decr depth;
        if !active && !depth = !c_base then begin
          ranges := (!c_start, lineno) :: !ranges;
          active := false
        end
      | _ -> ()
    ) line
  ) lines;
  List.rev !ranges

let create_session_dir () =
  Servois2.Rundir.resolve ~root:Util.output_root ~tool:"veracity"
    ~env_var:"VERACITY_OUT"

let generate ?(rewritten_source : string option = None) ~source_file ~session_dir ~records =
  (* 1. Read source *)
  let source_text =
    try read_file source_file
    with _ ->
      Printf.eprintf "html_output: cannot read %s\n" source_file; ""
  in
  let source_lines = String.split_on_char '\n' source_text in

  (* 3. Build a map: line number → list of commute indices covering it *)
  let line_map : (int, int list) Hashtbl.t = Hashtbl.create 32 in
  List.iteri (fun i (r : Util.commute_record) ->
    match parse_line_range r.loc_str with
    | None -> ()
    | Some (sl, el) ->
      for l = sl to el do
        let cur = try Hashtbl.find line_map l with Not_found -> [] in
        if not (List.mem i cur) then
          Hashtbl.replace line_map l (cur @ [i])
      done
  ) records;

  (* 4. Build source table HTML *)
  let src_buf = Buffer.create 8192 in
  Buffer.add_string src_buf "<table class=\"src\">\n";
  List.iteri (fun i line ->
    let lineno   = i + 1 in
    let commutes = try Hashtbl.find line_map lineno with Not_found -> [] in
    match commutes with
    | [] ->
      Buffer.add_string src_buf
        (Printf.sprintf "<tr><td class=\"ln\">%d</td><td class=\"code\">%s</td></tr>\n"
           lineno (html_escape line))
    | cid :: _ ->
      let is_first = match parse_line_range (List.nth records cid).loc_str with
        | Some (sl, _) -> sl = lineno | None -> false in
      let badge = if is_first then
        Printf.sprintf "<span class=\"badge\">&#128269; commute %d</span>" cid
        else "" in
      Buffer.add_string src_buf
        (Printf.sprintf
           "<tr class=\"cm\" data-cid=\"%d\" onclick=\"openModal(%d)\"><td class=\"ln\">%d</td>\
            <td class=\"code\">%s%s</td></tr>\n"
           cid cid lineno (html_escape line) badge)
  ) source_lines;
  Buffer.add_string src_buf "</table>\n";

  (* 5. Build JS commute data object *)
  let js_buf = Buffer.create 8192 in
  Buffer.add_string js_buf "var commuteData = {\n";
  List.iteri (fun i (r : Util.commute_record) ->
    let svgs = svgs_of_subdir r.subdir in
    let diag_html = match svgs with
      | [] -> "<p class=\\\"nodiag\\\">No diagrams (graphviz not available or no satisfying model found).</p>"
      | _  -> String.concat "\\n" (List.map (fun s ->
            (* escape backslashes then quotes for JS string *)
            s |> Str.global_replace (Str.regexp_string "\\") "\\\\"
              |> Str.global_replace (Str.regexp_string "\"") "\\\""
              |> Str.global_replace (Str.regexp_string "\n") "\\n"
          ) svgs)
    in
    let examine_rel  = Printf.sprintf "commute_%04d/index.html" i in
    let examine_full = Filename.concat session_dir examine_rel in
    let examine_link =
      if Sys.file_exists examine_full then
        Printf.sprintf "<a href=\\\"%s\\\">Open Servois2 query viewer &rarr;</a>" examine_rel
      else
        "<span style=\\\"color:#555\\\">Servois2 query viewer not available</span>"
    in
    let js_escape s =
      s |> Str.global_replace (Str.regexp_string "\\") "\\\\"
        |> Str.global_replace (Str.regexp_string "\"") "\\\""
        |> Str.global_replace (Str.regexp_string "\n") "\\n"
    in
    Buffer.add_string js_buf
      (Printf.sprintf "  %d:{loc:\"%s\",cond:\"%s\",diagrams:\"%s\",link:\"%s\"},\n"
         i (js_escape r.loc_str) (js_escape r.condition) diag_html examine_link)
  ) records;
  Buffer.add_string js_buf "};\n";

  (* 6. Optional rewritten-program section with interactive commute highlighting *)
  let rewritten_section = match rewritten_source with
    | None -> ""
    | Some text ->
      let rw_lines  = String.split_on_char '\n' text in
      let rw_ranges = find_commute_line_ranges text in
      (* Build line → commute-index map (same semantics as the original line_map) *)
      let rw_lmap : (int, int) Hashtbl.t = Hashtbl.create 16 in
      List.iteri (fun idx (sl, el) ->
        for l = sl to el do Hashtbl.replace rw_lmap l idx done
      ) rw_ranges;
      let rw_buf = Buffer.create 4096 in
      Buffer.add_string rw_buf "<table class=\"src\">\n";
      List.iteri (fun i line ->
        let lineno = i + 1 in
        match Hashtbl.find_opt rw_lmap lineno with
        | None ->
          Buffer.add_string rw_buf
            (Printf.sprintf
               "<tr><td class=\"ln\">%d</td><td class=\"code\">%s</td></tr>\n"
               lineno (html_escape line))
        | Some cid ->
          let is_first = match List.nth_opt rw_ranges cid with
            | Some (sl, _) -> sl = lineno | None -> false in
          let badge = if is_first then
            Printf.sprintf "<span class=\"badge\">&#128269; commute %d</span>" cid
            else "" in
          Buffer.add_string rw_buf
            (Printf.sprintf
               "<tr class=\"cm\" data-cid=\"%d\" onclick=\"openModal(%d)\">\
                <td class=\"ln\">%d</td>\
                <td class=\"code\">%s%s</td></tr>\n"
               cid cid lineno (html_escape line) badge)
      ) rw_lines;
      Buffer.add_string rw_buf "</table>\n";
      Printf.sprintf
        {|<section style="margin-top:28px">
<h2 style="color:#569cd6;border-bottom:1px solid #3c3c3c;padding-bottom:6px;margin-bottom:12px">
  Rewritten Program
  <span style="font-size:.72em;color:#888;font-weight:normal">&nbsp;(--rewrite-commute)</span>
</h2>
<div class="src-panel">
%s
</div>
</section>|}
        (Buffer.contents rw_buf)
  in

  (* 7. Assemble the full page *)
  let html = Printf.sprintf {|<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Veracity: %s</title>
%s
</head>
<body>
<h1>Veracity Analysis</h1>
<div class="meta">
  Source: <strong>%s</strong><br>
  Session: <code>%s</code>
</div>
<div class="layout">
  <div class="src-panel">
%s
  </div>
  <div class="diag-panel" id="diag-panel">
    <div id="diag-content"></div>
  </div>
</div>
%s
%s
%s
%s
</body>
</html>|}
    (Filename.basename source_file)
    css
    (html_escape source_file)
    (html_escape session_dir)
    (Buffer.contents src_buf)
    rewritten_section
    js_prefix
    (Buffer.contents js_buf)
    js_suffix
  in

  let out_path = Filename.concat session_dir "index.html" in
  let oc = open_out out_path in
  output_string oc html;
  close_out oc;

  (* Same manifest schema at every level of the tree, so one script can walk it
     from any node.  Each commute subdir is a Servois2 run, recorded by relative
     path so the tree stays movable. *)
  let children =
    List.map
      (fun (r : Util.commute_record) ->
        { Servois2.Rundir.child_tool = "servois2";
          child_path = Filename.basename r.Util.subdir })
      records
  in
  Servois2.Rundir.write_manifest ~dir:session_dir ~tool:"veracity"
    ~input:source_file
    ~result:(Printf.sprintf "%d commutes" (List.length records))
    ~artifacts:[ { Servois2.Rundir.kind = "report"; path = "index.html" } ]
    ~children ();
  out_path

(* Render a Dswp_task.dependency list as readable HTML. *)
let dep_list_html deps =
  if deps = [] then "<span style=\"color:#555\">none</span>"
  else
    String.concat ", " (List.map (fun (d : Dswp_task.dependency) ->
      let vars = Dswp_task.str_of_vars_list d.vars in
      Printf.sprintf
        "<span style=\"color:#9cdcfe\">T%d</span>[<span style=\"color:#ce9178\">%s</span>]"
        d.pred_task (html_escape vars)
    ) deps)

let svg_section_html label dot_path =
  match dot_to_svg dot_path with
  | Some svg ->
    Printf.sprintf "<h2>%s</h2><div class=\"svg-wrap\">%s</div>\n" label svg
  | None ->
    Printf.sprintf "<h2>%s</h2><p class=\"nosvg\">\
      (Graphviz not available or .dot file missing: %s)</p>\n"
      label (html_escape dot_path)

(* Generate a standalone HTML report for a DSWP analysis.
   pdg_dot   — path to the PDG .dot file (session_dir/pdg.dot)
   tasks_dot — path to the SCC task DAG .dot file (session_dir/dag-scc.dot) *)
let generate_dswp ~source_file ~session_dir
                  ~(init_task : Dswp_task.init_task option)
                  ~(tasks : Dswp_task.dswp_task list)
                  ~pdg_dot ~tasks_dot =
  let source_text =
    try read_file source_file
    with _ ->
      Printf.eprintf "html_output: cannot read %s\n" source_file; ""
  in
  let source_lines = String.split_on_char '\n' source_text in

  (* Source listing — plain, no commute annotations *)
  let src_buf = Buffer.create 4096 in
  Buffer.add_string src_buf "<table class=\"src\">\n";
  List.iteri (fun i line ->
    Buffer.add_string src_buf
      (Printf.sprintf "<tr><td class=\"ln\">%d</td>\
                       <td class=\"code\">%s</td></tr>\n"
         (i + 1) (html_escape line))
  ) source_lines;
  Buffer.add_string src_buf "</table>\n";

  (* Init task card *)
  let init_html = match init_task with
    | None -> ""
    | Some it ->
      let spawns = String.concat ", " (List.map string_of_int it.Dswp_task.jobs) in
      let body_str = Ast_print.AstPP.string_of_block it.Dswp_task.decls in
      Printf.sprintf
        "<div class=\"init-task\">\
           <h3>Init Task &mdash; spawns: [%s]</h3>\
           <pre class=\"task-body\">%s</pre>\
         </div>\n"
        (html_escape spawns)
        (html_escape (String.trim body_str))
  in

  (* Task cards *)
  let task_cards_html =
    String.concat "\n" (List.map (fun (t : Dswp_task.dswp_task) ->
      let label_badge = match t.Dswp_task.label with
        | Dswp_task.Doall      -> "<span class=\"badge badge-doall\">Doall</span>"
        | Dswp_task.Sequential -> "<span class=\"badge badge-seq\">Sequential</span>"
      in
      let body_str = Ast_print.AstPP.string_of_block t.Dswp_task.body in
      Printf.sprintf
        "<div class=\"task-card\" id=\"task-%d\">\
           <h3>Task %d %s</h3>\
           <div class=\"deps\"><strong>deps_in:</strong> %s</div>\
           <div class=\"deps\"><strong>deps_out:</strong> %s</div>\
           <pre class=\"task-body\">%s</pre>\
         </div>"
        t.Dswp_task.id t.Dswp_task.id label_badge
        (dep_list_html t.Dswp_task.deps_in)
        (dep_list_html t.Dswp_task.deps_out)
        (html_escape (String.trim body_str))
    ) tasks)
  in

  let html = Printf.sprintf {|<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>Veracity DSWP: %s</title>
%s
</head>
<body>
<h1>Veracity DSWP Analysis</h1>
<div class="meta">
  Source: <strong>%s</strong> &mdash; %d task(s) generated
</div>

%s
%s

<h2>Init Task</h2>
%s

<h2>Generated Tasks</h2>
<div class="tasks-grid">
%s
</div>

<h2>Source</h2>
%s

</body>
</html>|}
    (Filename.basename source_file)
    dswp_css
    (html_escape source_file)
    (List.length tasks)
    (svg_section_html "Program Dependency Graph" pdg_dot)
    (svg_section_html "Task Graph" tasks_dot)
    (if init_html = "" then "<p style=\"color:#555\">none</p>" else init_html)
    task_cards_html
    (Buffer.contents src_buf)
  in

  let out_path = Filename.concat session_dir "dswp.html" in
  let oc = open_out out_path in
  output_string oc html;
  close_out oc;
  out_path
