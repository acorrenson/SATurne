Require Import Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(** Type Literal *)
Inductive literal : Type := 
  P (n:nat) | N (n:nat).

(** Literals boolean equality *)
Fixpoint lit_eqb u v :=
  match u, v with
  | P a, P b | N a, N b => a =? b
  | _, _ => false
  end.

(** Literals negation *)
Fixpoint lit_neg l :=
  match l with
  | P n => N n
  | N n => P n
  end.

(** Type alias for clauses *)
Definition clause : Type := list literal.

(** Type alias for SAT problem *)
Definition problem : Type := list clause.

(** Remove a literal from a clause *)
Fixpoint remove_lit l c :=
  match c with
  | x::rest =>
    if lit_eqb x l
    then rest
    else x::(remove_lit l rest)
  | [] => []
  end.

(** Simplify a problem by propagating a literal *)
Fixpoint propagate (l:literal) (p:problem) : problem :=
  match p with
  | c::rest =>
    if List.existsb ((lit_eqb) l) c 
    then propagate l rest
    else (remove_lit (lit_neg l) c)::(propagate l rest)
  | [] => []
  end.

(** Naive size of a problem (number of literals) *)
Fixpoint problem_size (p:problem) :=
  match p with
  | c::rest => length c + problem_size rest
  | [] => 0
  end.

(** Removing a literal from a clause reduces its size *)
Lemma remove_lit_reduce_size :
  forall l:literal, forall c:clause, length (remove_lit l c) <= length c.
Proof.
  intros.
  induction c.
  + auto.
  + simpl.
    destruct (lit_eqb a l).
    - auto.
    - simpl. apply le_n_S. exact IHc.
Qed.

(** Simplyfing a problem by propatation of a literal reduces its size *)
Lemma propagate_reduce_problem_size: 
  forall p:problem, forall l:literal, problem_size (propagate l p) <= problem_size p.
Proof.
  intros.
  induction p.
  + auto.
  + simpl.
    destruct existsb.
    * rewrite IHp. rewrite plus_comm. apply le_plus_l.
    * simpl. apply Nat.add_le_mono.
      - apply remove_lit_reduce_size.
      - exact IHp.
Qed.
 

Require Import Recdef.

Definition assignment : Type := list literal.
Definition solutions : Type := list assignment.


(** Solve a problem *)
Function resolve_all (p:problem) {measure problem_size p} : solutions :=
  match p with
  | [] => [[]]
  | []::_ => []
  | (l::c)::r =>
    let p1 := (propagate l r) in
    let p2 := (propagate (lit_neg l) (c::r)) in
    let s1 := (List.map ((List.cons) l) (resolve_all p1)) in
    let s2 := (List.map ((List.cons) (lit_neg l)) (resolve_all p2)) in
    List.concat [s1; s2]
    end.
Proof.
  + intros; simpl; apply le_lt_n_Sm; destruct existsb; simpl.
    ++ rewrite plus_comm; apply le_plus_trans; apply propagate_reduce_problem_size.
    ++ rewrite Nat.add_le_mono.
      * auto.
      * apply remove_lit_reduce_size.
      * apply propagate_reduce_problem_size.
  + intros; simpl; apply le_lt_n_Sm; rewrite plus_comm; apply le_plus_trans; apply propagate_reduce_problem_size.
Defined.


Fixpoint eval_clause (c:clause) (a:assignment) : bool :=
  match c with
  | l::rest =>
    if List.existsb (lit_eqb l) a
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

