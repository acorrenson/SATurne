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

From Coq Require Import List.
Require Import Clauses.
Import ListNotations.

Definition entails cs c :=
  forall m, ClauseSet.eval m cs = true -> Clause.eval m c = true.

Lemma mem_entails :
  forall cs c, ClauseSet.mem cs c = true -> entails cs c.
Proof.
  intros cs c Hmem m Hm.
  firstorder using ClauseSet.eval_true_forall.
Qed.

Lemma resolution :
  forall (cs : ClauseSet.t) (c1 c2 : Clause.t) (l1 l2 : Literal.t),
    entails cs (l1::c1) ->
    entails cs (l2::c2) ->
    Literal.neg l1 = l2 ->
    entails cs (c1 ++ c2).
Proof.
  intros cs c1 c2 l1 l2 H1 H2 Heq m Hm.
  specialize (H1 _ Hm); specialize (H2 _ Hm).
  destruct l1, l2; simpl in *; try easy.
  all: replace n0 with n in * by congruence.
  all: destruct (Model.satisfy m n) eqn:E; simpl in *.
  all: rewrite Clause.eval_app; intuition.
Qed.

Inductive resolvent : ClauseSet.t -> Clause.t -> Prop :=
  | resolvent_mem : forall cs c,
    ClauseSet.mem cs c = true -> resolvent cs c
  | resolvent_cut : forall cs c1 c2 l1 l2,
    ClauseSet.mem cs (l1::c1) = true ->
    ClauseSet.mem cs (l2::c2) = true ->
    Literal.neg l1 = l2 -> resolvent cs (c1 ++ c2).

Require Import Evaluation.

Theorem clause_set_clause_true :
  forall m cs c,
    ClauseSet.mem cs c = true ->
    ClauseSet.eval m cs = true ->
    Clause.eval m c = true.
Proof.
  intros m cs c Hmem Heval.
  firstorder using ClauseSet.eval_true_forall.
Qed.

Theorem resolvent_sound :
  forall cs c,
    resolvent cs c ->
    entails cs c.
Proof.
  intros cs c Hres.
  induction Hres as [ cs c Hmem | cs c1 c2 l1 l2 H1%mem_entails H2%mem_entails].
  + firstorder using ClauseSet.eval_true_forall.
  + eauto using resolution.
Qed.

Theorem resolvent_bot_unsat :
  forall cs, resolvent cs [] -> ClauseSet.unsat cs.
Proof.
  intros cs Hres [m Hm].
  now pose proof (resolvent_sound cs [] Hres _ Hm).
Qed.

Inductive proof_step : Type :=
  | proof_mem (c : Clause.t)
  | proof_cut (n : nat) (c1 c2 : Clause.t).

Definition conclusion (ps : proof_step) : Clause.t :=
  match ps with
  | proof_mem c => c
  | proof_cut _ c1 c2 => c1 ++ c2
  end.

Definition is_proof_step (context : ClauseSet.t) (ps : proof_step) : bool :=
  match ps with
  | proof_mem c =>
    ClauseSet.mem context c
  | proof_cut l c1 c2 =>
    ClauseSet.mem context (Literal.Neg l::c1) &&
    ClauseSet.mem context (Literal.Pos l::c2)
  end.

Lemma is_proof_step_sound' :
  forall ctx ps,
    is_proof_step ctx ps = true ->
    resolvent ctx (conclusion ps).
Proof.
  intros ctx ps.
  induction ps as [ | l c1 c2 ].
  - eauto using resolvent.
  - intros [H1 H2]%Bool.andb_true_iff.
    eauto using resolvent.
Qed.

Lemma is_proof_step_sound :
  forall ctx ps,
    is_proof_step ctx ps = true ->
    entails ctx (conclusion ps).
Proof.
  eauto using resolvent_sound, is_proof_step_sound'.
Qed.

Fixpoint is_proof (context : ClauseSet.t) (proof : list proof_step) (c : Clause.t) : bool :=
  match proof with
  | [] => ClauseSet.mem context c
  | ps::proof =>
    is_proof_step context ps &&
    is_proof ((conclusion ps)::context) proof c
  end.

Lemma is_proof_sound :
  forall proof ctx c,
  is_proof ctx proof c = true ->
  entails ctx c.
Proof.
  intros proof. induction proof; simpl.
  + eauto using mem_entails.
  + intros ctx c [H1%is_proof_step_sound H2%IHproof]%Bool.andb_true_iff m Hm.
    specialize (H1 m Hm); specialize (H2 m); simpl in *.
    intuition.
Qed.

Theorem proof_unsat :
  forall ctx proof, is_proof ctx proof [] = true -> ClauseSet.unsat ctx.
Proof.
  intros ctx proof Hproof [m Hm].
  now pose proof (is_proof_sound _ _ _ Hproof _ Hm).
Qed.