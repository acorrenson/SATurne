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
    else set_add cl_eq_dec (set_remove lit_eq_dec (negate l) c) (propagate l rest)
  | nil => nil
  end.

Fixpoint lit_eq l1 l2 :=
  match l1, l2 with
  | P a, P b 
  | N a, N b => Nat.eqb a b
  | _, _ => false
  end.

Fixpoint lit_neq l1 l2 := negb (lit_eq l1 l2).

Fixpoint propagate2 (l:literal) (p:problem) : problem :=
  let notIn x s := (List.forallb (lit_neq x) s) in
  List.map (List.filter (lit_neq (negate l))) (List.filter (notIn l) p).

Example trivial_propagation : propagate2 (P 0) ([[P 0]]) = [].
  auto.
Qed.

Example unsat_propagation : propagate2 (P 0) ([[N 0]]) = [[]].
  auto.
Qed.

Notation assignment := (set literal).

Inductive result : Type :=
  | Some (a : assignment)
  | None.

Require Import Recdef.

Check set_fold_left.

Definition nb_literals (p:problem) := 
  let all := set_fold_left (set_union lit_eq_dec) p (empty_set literal) in
  length all.

Fixpoint nb_literals2  (p:problem) := 
  match p with
  | c::r => length c + (nb_literals2 r)
  | nil => 0
  end.
  

(* Definition problem_length (p:problem) := 2 ^ (nb_literals p) - length p. *)

Lemma propagate_conserve_order : 
  forall u v : problem, lel u v -> forall l, nb_literals2 (propagate2 l u) <= nb_literals2 (propagate2 l u).
Proof.
  auto.
Qed.

Lemma empty_propagate : forall l, forall p, nb_literals2 (propagate2 l ([] :: p)) = nb_literals2 ([] :: p).
Proof.
  intros.
  simpl.
  induction p.
  + simpl. induction l; auto.
  + simpl. induction l.
    * unfold propagate2. simpl map.

Lemma propagate_decrease :
  forall l:literal, forall p:problem, nb_literals (propagate2 l p) <= nb_literals p.
Proof.
  intros.
  induction p.
  induction l.
  + auto.
  + auto.
  + induction a. 
    * intros. rewrite H. auto.
    * intros. cut (forall l, forall p, nb_literals (propagate2 l ([] :: p)) = nb_literals ([] :: p)).
      - intros.
  
  (* induction a.
    - cut (forall q : problem, nb_literals ([] :: q) = nb_literals q).
     * intros. symmetry in H. rewrite <- H. *)

Function resolve (p:problem) {measure problem_length p} : result  :=
  match p with
  | nil => Some nil
  | nil::_ => None
  | (l::c)::r =>
    match resolve (propagate l r) with
    | Some a => Some (l::a)
    | None =>
      match resolve (propagate (negate l) (c::r)) with
      | Some a => Some ((negate l)::a)
      | None => None
      end
    end
  end.
Proof.
  + intros.
    simpl.

(* Fixpoint resolve (p:problem) : result :=
  match p with
  | nil => Some nil
  | nil::_ => None
  | (l::c)::r =>
    match resolve (propagate l r) with
    | Some a => Some (l::a)
    | None =>
      match resolve (propagate (negate l) (c::r)) with
      | Some a => Some ((negate l)::a)
      | None => None
      end
    end
  end. *)


Fixpoint eval_clause (c:clause) (a:assignment) : bool :=
  match c with
  | l::rest =>
    if set_mem lit_eq_dec l a
    then true
    else eval_clause rest a
  | nil => false
  end.

Fixpoint eval (p:problem) (a:assignment) : bool :=
  match p with
  | c::rest =>
    if eval_clause c a
    then eval rest a
    else false
  | nil => true
  end.


Definition sat (p:problem) := exists a:assignment, eval p a = true.


Definition unsat (p : problem) := not (sat p).

Lemma smallest_unsat_problem :
  unsat [[]].
Proof.
  unfold unsat.
  unfold sat.
  unfold not.
  simpl.
  intro.
  elim H.
  intros.
  discriminate H0.
Qed.

Lemma smallest_sat_problem :
  sat [].
Proof.
  unfold sat.
  simpl.
  exists [].
  reflexivity.
Qed.