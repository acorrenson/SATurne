Require Import Coq.Lists.ListSet.
Require Import ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Inductive literal : Type := P (n:nat) | N (n:nat).

(** Equality of literals is decidable *)
Definition lit_eq_dec : forall x y:literal, { x = y } + { x <> y}.
Proof.
  decide equality.
  + decide equality.
  + decide equality.
Defined.

Notation clause := (set literal).

(** Equality of clauses is decidable *)
Definition cl_eq_dec : forall x y: clause, { x = y } + { x <> y}.
Proof.
  decide equality.
  apply lit_eq_dec.
Defined.

Notation problem := (set clause).

Fixpoint negate l:literal :=
  match l with
  | P n => N n
  | N n => P n
  end.

Fixpoint propagate (l:literal) (p:problem) : problem := 
  match p with
  | c::rest =>
    if set_mem lit_eq_dec l c
    then propagate l rest 
    else (set_remove lit_eq_dec (negate l) c)::(propagate l rest)
  | nil => nil
  end.


Example trivial_propagation : propagate (P 0) ([[P 0]]) = [].
  auto.
Qed.

Example unsat_propagation : propagate (P 0) ([[N 0]]) = [[]].
  auto.
Qed.

(** TODOs :
  + define the notion of models
  + rewrite this definition with models
*)
Definition unsat (p : problem) := set_mem cl_eq_dec nil p = true.

Lemma smallest_unsat_problem :
  unsat [[]].
Proof.
  unfold unsat.
  simpl.
  reflexivity.
Qed.



