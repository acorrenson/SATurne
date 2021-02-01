
(****************************************************

                    ,MMM8&&&.
                _..MMMMM88&&&&..._
            .::'''MMMMM88&&&&&&'''::.
           ::     MMMMM88&&&&&&     ::
           '::....MMMMM88&&&&&&....::'
              `''''MMMMM88&&&&''''`
                    'MMM8&&&'

                     SATurne
                ----------------
             A tiny verified solver

****************************************************)

(***************************************************
            Module -- Sat Solver
****************************************************)

Require Import Arith Lia List Recdef Program.Wf.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import SATurn.Sat.
Require Import SATurn.Clauses.
Require Import SATurn.Solver_aux.

(** Solutions to a SAT problem *)
(* Local Definition solutions : Type := list assignment. *)

Definition map (a : option assignment) (f : assignment -> assignment) :=
  match a with
  | None => None
  | Some x => Some (f x)
  end.

Definition union (a b : option assignment) :=
  match a with
  | None => b
  | Some _ => a
  end.

Function resolve (clauses : problem) {measure problem_size clauses} : option assignment :=
  match clauses with
  | [] => Some []
  | clause::clauses' =>
    match clause with
    | [] => None
    | lit::clause' =>
      let space_1 := propagate lit clauses' in
      let space_2 := propagate (lit_neg lit) (clause'::clauses') in
      let res1 := resolve space_1 in
      let res2 := resolve space_2 in
      union (map res1 (fun x => lit::x))
            (map res2 (fun x => (lit_neg lit)::x))
    end
  end.
Proof.
  all: intros clauses clause clauses' lit clause'; simpl.
  - destruct existsb; simpl.
    + destruct (propagate_variant (lit_neg lit) clauses'); lia.
    + destruct  (remove_lit_variant (lit_neg (lit_neg lit)) clause'),
                (propagate_variant (lit_neg lit) clauses'); lia.
  - destruct (propagate_variant lit clauses'); lia.
Defined.
  
(** Resolution algorithm *)
Function resolve_all (p : problem) {measure problem_size p} : list assignment :=
  match p with
  | [] => [[]]
  | c::pp =>
    match c with
    | [] => []
    | l::cc =>
      let p1 := propagate l pp in
      let p2 := propagate (lit_neg l) (cc::pp) in
      let s1 := List.map (List.cons l) (resolve_all p1) in
      let s2 := List.map (List.cons (lit_neg l)) (resolve_all p2) in
      s1 ++ s2
    end
  end.
Proof.
  (* Termination Proof *)
  all: intros p c pp l cc; simpl.
  - destruct existsb; simpl.
    + destruct  (propagate_variant (lit_neg l) pp); lia.
    + destruct  (remove_lit_variant (lit_neg (lit_neg l)) cc),
                (propagate_variant (lit_neg l) pp); lia.
  - destruct (propagate_variant l pp); lia.
Defined.

(* Lemma asg_eq_dec:
  forall (a1 a2:assignment),
  {a1 = a2} + {a1 <> a2}.
Proof.
  decide equality.
  apply lit_eqb_dec.
Qed.

Lemma resolve_invariant_1:
  forall c p a,
  In a (resolve (c :: p)) -> eval_clause c a = true.
Proof.
  intros c p asg H.
  induction c; auto.
  simpl.
  apply Bool.orb_true_iff.
  destruct (in_dec asg_eq_dec asg (resolve (c :: p))).
  + right. apply (IHc i).
Admitted.

Lemma resolve_invariant_2:
  forall c p a,
  In a (resolve (c::p)) -> In a (resolve p).
Proof.
Admitted.

Lemma resolve_correct:
  forall (a:assignment) (p:problem),
  List.In a (resolve p) -> eval p a = true.
Proof.
  induction p; intros; try auto; simpl.
  apply andb_true_intro; split.
  - apply (resolve_invariant_1 _ _ _ H).
  - apply (IHp (resolve_invariant_2 _ _ _ H)).
Qed.

Lemma resolve_complete:
  forall (a:assignment) (p:problem),
  eval p a = true -> List.In a (resolve p).
Proof.
Admitted.


Compute (resolve [[Pos 1]; [Neg 2; Neg 3]]). *)