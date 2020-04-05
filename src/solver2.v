(* Require Import ZArith. *)
(* Require Import ZArith.ZArith. *)
Require Import Arith.
Require Import Coq.Lists.List.

Import ListNotations.

Inductive literal : Type := 
  P (n:nat) | N (n:nat).

Fixpoint lit_eqb u v :=
  match u, v with
  | P a, P b | N a, N b => a =? b
  | _, _ => false
  end.

Fixpoint lit_neg l :=
  match l with
  | P n => N n
  | N n => P n
  end.

Definition clause : Type := list literal.

Definition problem : Type := list clause.

Fixpoint remove_lit l c :=
  match c with
  | x::rest =>
    if lit_eqb x l
    then rest
    else x::(remove_lit l rest)
  | [] => []
  end.

Fixpoint propagate (l:literal) (p:problem) : problem :=
  match p with
  | c::rest =>
    if List.existsb ((lit_eqb) l) c 
    then propagate l rest
    else (remove_lit (lit_neg l) c)::(propagate l rest)
  | [] => []
  end.

Fixpoint problem_size (p:problem) :=
  match p with
  | c::rest => length c + problem_size rest
  | [] => 0
  end.

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

Inductive result : Type :=
  | Some : list literal -> result
  | None : result.


Function resolve_all (p:problem) {measure problem_size p} : list (list literal) :=
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
  + intros.
    simpl.
    destruct existsb;apply le_lt_n_Sm.
    ++ rewrite plus_comm; apply le_plus_trans; apply propagate_reduce_problem_size.
    ++ simpl. rewrite Nat.add_le_mono.
      * auto.
      * apply remove_lit_reduce_size.
      * apply propagate_reduce_problem_size.
  + intros.
    simpl.
    apply le_lt_n_Sm; rewrite plus_comm; apply le_plus_trans; apply propagate_reduce_problem_size.
Defined.


