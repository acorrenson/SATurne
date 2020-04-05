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

Lemma eval_weak:
  forall c:clause, forall p: problem, forall a:assignment,
    eval (c::p) a = true -> eval p a = true.
Proof.
  intros.
  simpl eval in H.
  destruct (eval_clause c a) eqn:E1.
  - exact H.
  - discriminate H.
Qed.

Lemma eval_clause_weak: 
  forall c:clause, forall l:literal, forall a:assignment,
    eval_clause c a = true -> eval_clause (l::c) a = true.
Proof.
  intros.
  induction c.
  + discriminate H.
  + simpl.
    destruct existsb eqn:A.
    - reflexivity.
    - auto.
Qed.

Lemma eval_or:
  forall c:clause, forall p:problem, forall a:assignment,
    eval (c::p) a = true -> eval_clause c a = true \/ eval p a = true.
Proof.
  intros.
  - destruct (eval_clause c a) eqn: A.
    + auto.
    + right.
      apply eval_weak in H. exact H.
Qed.

Fixpoint wf_clause (p:clause) :=
  match p with
  | [] => True
  | l::rest =>
    if List.existsb (lit_eqb l) rest then False
    else if List.existsb (lit_eqb (lit_neg l)) rest then False
    else wf_clause rest
    end.

Fixpoint wf_problem (p:problem) :=
  match p with
  | [] => True
  | c::rest => (wf_clause c) /\ (wf_problem rest)
  end.

Lemma wf_p_c :
  forall p:problem, forall c:clause,
    wf_problem (c::p) -> wf_clause c.
Proof.
  intros.
  + simpl wf_problem in H.
    apply H.
Qed.

Lemma propagate_coherence :
  forall p:problem, forall a:assignment, forall l:literal, wf_problem p -> eval p a = true -> eval (propagate l p) a = true.
Proof.
  intros.
  induction p.
  + simpl; reflexivity.
  + simpl propagate.
    destruct existsb eqn:A.
    ++ rewrite IHp.
      * auto.
      * apply H.
      * apply eval_weak in H0. exact H0.
    ++ simpl eval.
      rewrite eval_clause_weak.
        

(* intros.
induction p.
+ auto.
+ simpl propagate.
  destruct existsb eqn: A.
  ++ rewrite IHp.
      * auto.
      * apply eval_weak in H. exact H.
  ++ apply eval_or.
  
  simpl. auto. destruct eval_clause eqn:E.
    * apply eval_weak in H.
      apply IHp. exact H.
    * auto. *)
