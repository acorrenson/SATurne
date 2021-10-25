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
        Auxilary functions for the solver
****************************************************)

Require Import SATurn.Sat.
Require Import SATurn.Evaluation.
Require Import List Lia Arith.
Import ListNotations.

(** Remove a literal from a clause *)
Fixpoint remove_lit l c :=
  match c with
  | [] => []
  | x::rest =>
    if lit_eqb x l
    then rest
    else x::(remove_lit l rest)
  end.

(** Simplify a problem by propagating a literal *)
Fixpoint propagate (l : literal) (p : problem) : problem :=
  match p with
  | [] => []
  | c::rest =>
    if List.existsb ((lit_eqb) l) c 
    then propagate l rest
    else (remove_lit (lit_neg l) c)::(propagate l rest)
  end.

(** Naive size of a problem (number of literals) *)
Fixpoint problem_size (p:problem) :=
  match p with
  | [] => 0
  | c::rest => length c + problem_size rest
  end.

(** Removing a literal from a clause reduces its size *)
Lemma remove_lit_variant :
  forall (l : literal), forall (c : clause), length (remove_lit l c) <= length c.
Proof.
  induction c as [ | l' c IHc]; simpl; auto.
  destruct (lit_eqb l' l); simpl; lia.
Qed.

Lemma propagate_variant:
  forall (l : literal) (p : problem), problem_size (propagate l p) <= problem_size p.
Proof.
  induction p as [ | c p' IHp]; simpl; auto.
  destruct existsb; simpl; try lia.
  apply Nat.add_le_mono; try lia.
  apply remove_lit_variant.
Qed.

Lemma eval_clause_remove_neg l c a :
  ~ In l c ->
  eval_clause (remove_lit (lit_neg l) c) a = true ->
  eval_clause c (l :: a) = true.
Proof.
  revert a l. induction c as [ |l' c]; auto.
  intros a l Hin Ha. cbn in Ha. destruct (lit_eqb l' (lit_neg l)) eqn:HH.
  - rewrite lit_eqb_eq in HH. subst. cbn. rewrite !Bool.orb_true_iff.
    right. apply eval_clause_weaken; auto.
  - cbn. rewrite !Bool.orb_true_iff. cbn in Ha. rewrite Bool.orb_true_iff in Ha.
    destruct Ha as [?|Ha]; auto. destruct (lit_eqb l' l) eqn:Hll'; auto.
    right. apply IHc; auto. intro. apply Hin; right; auto.
Qed.

Lemma existsb_lit_notin l c : existsb (lit_eqb l) c = false -> ~ In l c.
Proof.
  intros ? ?. enough (existsb (lit_eqb l) c = true) by congruence.
  apply existsb_exists. eexists; split; eauto. apply lit_eqb_eq; auto.
Qed.
