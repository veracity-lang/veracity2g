Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* ================================================================= *)
(*  Loop-Comm Rule \u2014 Rocq Formalization                               *)
(*                                                                     *)
(*  Rule (from image):                                                 *)
(*    {I \u2227 B} S {I \u2227 \u03c6}                                               *)
(*    \u03c6 \u21d2 C1 \u22b3\u25c1 S                                                    *)
(*    {I} C1 {I}                                                       *)
(*    {I \u2227 B} C1 {B}                                                  *)
(*    {I \u2227 \u00acB} C1 {\u00acB}                                                *)
(*    \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500                                    *)
(*    I \u27f9 C1 \u22b3\u25c1 (while B do S)                                       *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(* 0.  Basic types                                                    *)
(* ----------------------------------------------------------------- *)

(** A [state] is just a function from variable names to integers. *)
Definition var := string.
Definition state := var -> Z.

(** Update a state: [st [ x |-> v ]] *)
Definition update (st : state) (x : var) (v : Z) : state :=
  fun y => if String.eqb y x then v else st y.

Notation "st '[' x '|->' v ']'" := (update st x v) (at level 10).

(* ----------------------------------------------------------------- *)
(* 1.  Assertions and Hoare triples                                   *)
(* ----------------------------------------------------------------- *)

(** An [assertion] is a predicate on states. *)
Definition assertion := state -> Prop.

(** Conjunction of two assertions. *)
Definition aand (P Q : assertion) : assertion := fun st => P st /\ Q st.
Notation "P '\u2227' Q" := (aand P Q) (at level 80, right associativity).

(** Negation of an assertion. *)
Definition anot (P : assertion) : assertion := fun st => ~ P st.
Notation "'\u00ac' P" := (anot P) (at level 75, right associativity).

(** Assertion implication (pointwise). *)
Definition aimp (P Q : assertion) : Prop := forall st, P st -> Q st.
Notation "P '\u2286' Q" := (aimp P Q) (at level 70).

(* ----------------------------------------------------------------- *)
(* 2.  Commands and big-step semantics                                *)
(* ----------------------------------------------------------------- *)

Inductive com : Type :=
  | CSkip
  | CAsgn   (x : var) (e : state -> Z)
  | CSeq    (c1 c2 : com)
  | CIf     (b : state -> bool) (c1 c2 : com)
  | CWhile  (b : state -> bool) (body : com).

Notation "x '::=' e"          := (CAsgn x e)         (at level 60).
Notation "c1 ;; c2"           := (CSeq c1 c2)         (at level 90, right associativity).
Notation "'IF' b 'THEN' c1 'ELSE' c2" := (CIf b c1 c2) (at level 80).
Notation "'WHILE' b 'DO' c"   := (CWhile b c)         (at level 80).

(** Big-step evaluation relation [\u27e8c, st\u27e9 \u21d3 st']. *)
Inductive eval : com -> state -> state -> Prop :=
  | E_Skip   : forall st,
      eval CSkip st st

  | E_Asgn   : forall st x e,
      eval (x ::= e) st (st[x |-> e st])

  | E_Seq    : forall c1 c2 st st' st'',
      eval c1 st st' ->
      eval c2 st' st'' ->
      eval (c1 ;; c2) st st''

  | E_IfTrue : forall b c1 c2 st st',
      b st = true ->
      eval c1 st st' ->
      eval (IF b THEN c1 ELSE c2) st st'

  | E_IfFalse : forall b c1 c2 st st',
      b st = false ->
      eval c2 st st' ->
      eval (IF b THEN c1 ELSE c2) st st'

  | E_WhileFalse : forall b body st,
      b st = false ->
      eval (WHILE b DO body) st st

  | E_WhileTrue : forall b body st st' st'',
      b st = true ->
      eval body st st' ->
      eval (WHILE b DO body) st' st'' ->
      eval (WHILE b DO body) st st''.

Notation "\u27e8 c , st \u27e9 \u21d3 st'" := (eval c st st') (at level 40).

(* ----------------------------------------------------------------- *)
(* 3.  Hoare triple  {P} c {Q}                                       *)
(* ----------------------------------------------------------------- *)

Definition hoare (P : assertion) (c : com) (Q : assertion) : Prop :=
  forall st st', \u27e8c, st\u27e9 \u21d3 st' -> P st -> Q st'.

Notation "[[ P ]] c [[ Q ]]" := (hoare P c Q) (at level 40).

(* ----------------------------------------------------------------- *)
(* 4.  Commutativity  \u03c6 \u27f9 C1 \u22b3\u25c1 S                                  *)
(*                                                                     *)
(*  "C1 commutes with S under \u03c6" means: whenever the pre-state       *)
(*  satisfies \u03c6, running C1 then S lands in the same final state     *)
(*  as running S then C1.                                             *)
(* ----------------------------------------------------------------- *)

Definition commutes_under (phi : assertion) (C1 S : com) : Prop :=
  forall st st',
    phi st ->
    (exists st_m, \u27e8C1, st\u27e9 \u21d3 st_m /\ \u27e8S, st_m\u27e9 \u21d3 st') <->
    (exists st_m, \u27e8S, st\u27e9 \u21d3 st_m /\ \u27e8C1, st_m\u27e9 \u21d3 st').

(** The conclusion of Loop-Comm uses a conditional version:
    the commutativity obligation is discharged once we know I holds. *)
Definition loop_commutes (I : assertion) (C1 : com) (loop : com) : Prop :=
  forall st st',
    I st ->
    (exists st_m, \u27e8C1, st\u27e9 \u21d3 st_m /\ \u27e8loop, st_m\u27e9 \u21d3 st') <->
    (exists st_m, \u27e8loop, st\u27e9 \u21d3 st_m /\ \u27e8C1, st_m\u27e9 \u21d3 st').

Notation "phi '\u27f9' C1 '\u22b3\u25c1' S" := (commutes_under phi C1 S)
  (at level 50, C1 at level 0, S at level 0).

Notation "I '\u27f9loop' C1 '\u22b3\u25c1' loop" := (loop_commutes I C1 loop)
  (at level 50, C1 at level 0, loop at level 0).

(* ----------------------------------------------------------------- *)
(* 5.  The Loop-Comm rule                                             *)
(* ----------------------------------------------------------------- *)

(**  Hypotheses (matching the five premises in the image):
       H1 : {I \u2227 B}  S  {I \u2227 \u03c6}
       H2 : \u03c6 \u27f9 C1 \u22b3\u25c1 S
       H3 : {I}       C1 {I}
       H4 : {I \u2227 B}  C1 {B}
       H5 : {I \u2227 \u00acB} C1 {\u00acB}
     Conclusion:
       I \u27f9loop C1 \u22b3\u25c1 (while B do S)
*)

Axiom Loop_Comm :
  forall (I phi : assertion)
         (B     : state -> bool)
         (S C1  : com),
  let bP  : assertion := fun st => B st = true  in
  let bN  : assertion := fun st => B st = false in
  (* H1 *) hoare ( I \u2227 bP ) S  ( I \u2227 phi )  ->
  (* H2 *) (phi \u27f9 C1 \u22b3\u25c1 S)           ->
  (* H3 *) hoare ( I )     C1 ( I )          ->
  (* H4 *) hoare ( I \u2227 bP ) C1 ( bP )        ->
  (* H5 *) hoare ( I \u2227 bN ) C1 ( bN )        ->
  I \u27f9loop C1 \u22b3\u25c1 (WHILE B DO S).

(* ================================================================= *)
(* 6.  Concrete instantiation                                         *)
(*                                                                     *)
(*  Variables: c, x, n  (all integers)                                *)
(*                                                                     *)
(*  C1  \u225c  if (c > 0) { c := c \u2212 1 }                                 *)
(*          (i.e., IF c>0 THEN c::=c-1 ELSE SKIP)                    *)
(*                                                                     *)
(*  S / loop body  \u225c  c := c+1 ;; x := x+1                           *)
(*                                                                     *)
(*  Loop  \u225c  WHILE x<n DO (c := c+1 ;; x := x+1)                    *)
(*                                                                     *)
(*  I   \u225c  c >= 0                                                     *)
(*  \u03c6   \u225c  c \u2260 0                                                      *)
(*  B   \u225c  x < n                                                       *)
(* ================================================================= *)

(** ---- variable names ---- *)
Definition vC := "c"%string.
Definition vX := "x"%string.
Definition vN := "n"%string.

(** ---- assertions ---- *)

(** I : c >= 0 *)
Definition I_inv : assertion := fun st => (st vC >= 0)%Z.

(** \u03c6 : c \u2260 0 *)
Definition phi_inv : assertion := fun st => (st vC <> 0)%Z.

(** B : x < n  (as a bool for the command language) *)
Definition B_fun : state -> bool :=
  fun st => Z.ltb (st vX) (st vN).

Definition B_assert : assertion := fun st => B_fun st = true.
Definition notB_assert : assertion := fun st => B_fun st = false.

(** ---- commands ---- *)

(** C1 : if (c > 0) { c := c - 1 } *)
Definition C1 : com :=
  IF (fun st => Z.gtb (st vC) 0)
  THEN (vC ::= fun st => (st vC - 1)%Z)
  ELSE CSkip.

(** S (loop body) : c := c + 1 ;; x := x + 1 *)
Definition S_body : com :=
  (vC ::= fun st => (st vC + 1)%Z) ;;
  (vX ::= fun st => (st vX + 1)%Z).

(** loop : while (x < n) do S_body *)
Definition loop : com :=
  WHILE B_fun DO S_body.

(** ---- application of Loop_Comm ---- *)

(**  We now *state* (as a theorem to be proved, or check the shape)
     the commutativity conclusion for our concrete setting.          *)

Definition concrete_conclusion : Prop :=
  I_inv \u27f9loop C1 \u22b3\u25c1 loop.

(**  Applying the axiom reduces it to the five premises. *)
Theorem loop_comm_instance :
  (* H1 *) hoare ( I_inv \u2227 B_assert ) S_body ( I_inv \u2227 phi_inv )  ->
  (* H2 *) (phi_inv \u27f9 C1 \u22b3\u25c1 S_body)                        ->
  (* H3 *) hoare ( I_inv )             C1     ( I_inv )             ->
  (* H4 *) hoare ( I_inv \u2227 B_assert )  C1     ( B_assert )          ->
  (* H5 *) hoare ( I_inv \u2227 notB_assert ) C1   ( notB_assert )       ->
  concrete_conclusion.
Proof.
  intros H1 H2 H3 H4 H5.
  unfold concrete_conclusion, loop.
  exact (Loop_Comm I_inv phi_inv B_fun S_body C1 H1 H2 H3 H4 H5).
Qed.

(**  ------------------------------------------------------------------
     Sketch of how each premise would be proved interactively
     (left as [Admitted] \u2014 fill in with arithmetic automation):
     ------------------------------------------------------------------ *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

(** H1 : {I \u2227 B} S_body {I \u2227 \u03c6}
    After executing c:=c+1;; x:=x+1 from a state where c\u22650 and x<n,
    we get c'=c+1\u22651>0, so c'\u22650 (I) and c'\u22600 (\u03c6). *)
Lemma H1_proof :
  hoare ( I_inv \u2227 B_assert ) S_body ( I_inv \u2227 phi_inv ).
Proof.
  unfold hoare, S_body, I_inv, phi_inv, aand, B_assert.
  intros st st' Heval [HI HB].
  inversion Heval; subst.
  inversion H1; subst.
  inversion H4; subst.
  simpl.
  split; unfold update; simpl; lia.
Qed.

(** H3 : {I} C1 {I}
    C1 either decrements c (from c>0, giving c-1\u22650) or skips (c=0\u22650). *)
Lemma H3_proof :
  hoare ( I_inv ) C1 ( I_inv ).
Proof.
  unfold hoare, C1, I_inv.
  intros st st' Heval HI.
  inversion Heval; subst.
  - (* then branch: c > 0 *)
    match goal with
    | H : eval _ _ _ |- _ => inversion H; subst
    end.
    unfold update; simpl.
    match goal with
    | H : (Z.gtb _ _ = true) |- _ =>
        apply Z.gtb_lt in H; lia
    end.
  - (* else branch: skip *)
    match goal with
    | H : eval CSkip _ _ |- _ => inversion H; subst
    end.
    exact HI.
Qed.

(** H4 : {I \u2227 B} C1 {B}
    If x<n before C1, then C1 does not touch x, so x<n after. *)
Lemma H4_proof :
  hoare ( I_inv \u2227 B_assert ) C1 ( B_assert ).
Proof.
  unfold hoare, C1, I_inv, B_assert, B_fun, aand.
  intros st st' Heval [HI HB].
  inversion Heval; subst.
  - (* then branch: c > 0, assignment happens *)
    inversion H5; subst.
    unfold update; simpl.
    unfold B_fun in HB.
    (* vX and vN are not vC, so the update doesn't affect them *)
    replace (if String.eqb vX vC then st vC - 1 else st vX)
      with (st vX) by (unfold vX, vC; simpl; reflexivity).
    replace (if String.eqb vN vC then st vC - 1 else st vN)
      with (st vN) by (unfold vN, vC; simpl; reflexivity).
    exact HB.
  - (* else branch: skip, state unchanged *)
    inversion H5; subst.
    exact HB.
Qed.

(** H5 : {I \u2227 \u00acB} C1 {\u00acB}  \u2014 symmetric to H4 (C1 never touches x). *)
Lemma H5_proof :
  hoare ( I_inv \u2227 notB_assert ) C1 ( notB_assert ).
Proof.
  unfold hoare, C1, I_inv, notB_assert, B_fun, aand.
  intros st st' Heval [HI HB].
  inversion Heval; subst.
  - (* then branch: c > 0, assignment happens *)
    inversion H5; subst.
    unfold update; simpl.
    unfold B_fun in HB.
    replace (if String.eqb vX vC then st vC - 1 else st vX)
      with (st vX) by (unfold vX, vC; simpl; reflexivity).
    replace (if String.eqb vN vC then st vC - 1 else st vN)
      with (st vN) by (unfold vN, vC; simpl; reflexivity).
    exact HB.
  - (* else branch: skip, state unchanged *)
    inversion H5; subst.
    exact HB.
Qed.

(** H2 : \u03c6 \u27f9 C1 \u22b3\u25c1 S_body
    When c\u22600 (so c>0 since I holds), C1 decrements c and S increments it,
    so the net effect on (c,x) is the same in both orders.
    This is the most algebraic obligation and typically needs the most work. *)
Lemma H2_proof :
  (phi_inv \u27f9 C1 \u22b3\u25c1 S_body).
Proof.
  unfold commutes_under, phi_inv, C1, S_body.
  intros st st' Hphi.
  split.
  - (* C1 ; S  \u2192  S ; C1 *)
    intros Hex.
    destruct Hex as [st_m [HC1 HS]].
    match goal with
    | H : \u27e8 IF _ THEN _ ELSE _ , st \u27e9 \u21d3 st_m |- _ =>
        inversion H; subst
    end.
    + (* then branch: c > 0 *)
      match goal with
      | H : \u27e8 vC ::= _ , st \u27e9 \u21d3 st_m |- _ =>
          inversion H; subst
      end.
      match goal with
      | H : \u27e8 _ ;; _ , _ \u27e9 \u21d3 st' |- _ =>
          inversion H; subst
      end.
      match goal with
      | H : \u27e8 vC ::= _ , _ \u27e9 \u21d3 _ |- _ =>
          inversion H; subst
      end.
      match goal with
      | H : \u27e8 vX ::= _ , _ \u27e9 \u21d3 _ |- _ =>
          inversion H; subst
      end.
      eexists; split.
      * eapply E_Seq; eapply E_Asgn.
      * eapply E_IfTrue.
        -- unfold update; simpl.
           unfold vC, vX; simpl.
           match goal with
           | H : (?b >? 0) = true |- _ =>
               apply Z.gtb_lt in H; lia
           end.
        -- eapply E_Asgn.
    + (* else branch: c = 0, contradicts phi_inv *)
      match goal with
      | H : \u27e8 CSkip , st \u27e9 \u21d3 st_m |- _ =>
          inversion H; subst
      end.
      exfalso.
      match goal with
      | H : (_ >? 0) = false |- _ =>
          apply Z.gtb_false_lt in H; lia
      end.
  - (* S ; C1  \u2192  C1 ; S *)
    intros Hex.
    destruct Hex as [st_m [HS HC1]].
    match goal with
    | H : \u27e8 _ ;; _ , st \u27e9 \u21d3 st_m |- _ =>
        inversion H; subst
    end.
    match goal with
    | H : \u27e8 vC ::= _ , st \u27e9 \u21d3 _ |- _ =>
        inversion H; subst
    end.
    match goal with
    | H : \u27e8 vX ::= _ , _ \u27e9 \u21d3 st_m |- _ =>
        inversion H; subst
    end.
    match goal with
    | H : \u27e8 IF _ THEN _ ELSE _ , st_m \u27e9 \u21d3 st' |- _ =>
        inversion H; subst
    end.
    + (* then branch after S *)
      match goal with
      | H : \u27e8 vC ::= _ , _ \u27e9 \u21d3 st' |- _ =>
          inversion H; subst
      end.
      eexists; split.
      * eapply E_IfTrue.
        -- match goal with
           | H : (_ >? 0) = true |- _ =>
               unfold update; simpl; unfold vC, vX; simpl; exact H
           end.
        -- eapply E_Asgn.
      * eapply E_Seq; eapply E_Asgn.
    + (* else branch after S *)
      match goal with
      | H : \u27e8 CSkip , _ \u27e9 \u21d3 st' |- _ =>
          inversion H; subst
      end.
      eexists; split.
      * eapply E_IfFalse.
        -- match goal with
           | H : (_ >? 0) = false |- _ =>
               unfold update; simpl; unfold vC, vX; simpl; exact H
           end.
        -- eapply E_Asgn.
      * eapply E_Seq; eapply E_Asgn.
Qed.

(** ---- final packaged theorem ---- *)
Theorem loop_comm_concrete : concrete_conclusion.
Proof.
  apply loop_comm_instance.
  - exact H1_proof.
  - exact H2_proof.
  - exact H3_proof.
  - exact H4_proof.
  - exact H5_proof.
Qed.