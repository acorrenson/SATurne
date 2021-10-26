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
  forall m cs c,
    resolvent cs c ->
    ClauseSet.eval m cs = true ->
    Clause.eval m c = true.
Proof.
  intros m cs c Hres Heval.
  induction Hres.
  + apply (ClauseSet.eval_true_forall cs m Heval c H).
  + pose proof (Hl1 := ClauseSet.eval_true_forall cs m Heval (l1 :: c1) H).
    pose proof (Hl2 := ClauseSet.eval_true_forall cs m Heval (l2 :: c2) H0).
    simpl in Hl1, Hl2.
    destruct (Literal.eval m l1) eqn:E1, (Literal.eval m l2) eqn:E2.
    * destruct l1, l2; simpl in H1; try discriminate.
      - inversion H1; subst.
        simpl in E1, E2.
        now destruct (Model.satisfy m n0).
      - inversion H1; subst.
        simpl in E1, E2.
        now destruct (Model.satisfy m n0).
    * apply Clause.eval_true_exists in Hl2 as [x [Hx Hx']].
      apply Clause.exists_eval_true.
      exists x; split; auto.
      apply in_or_app; auto.
    * apply Clause.eval_true_exists in Hl1 as [x [Hx Hx']].
      apply Clause.exists_eval_true.
      exists x; split; auto.
      apply in_or_app; auto.
    * destruct l1, l2; simpl in H1; try discriminate.
      - inversion H1; subst.
        simpl in E1, E2.
        now destruct (Model.satisfy m n0).
      - inversion H1; subst.
        simpl in E1, E2.
        now destruct (Model.satisfy m n0).
Qed.

Theorem resolvent_bot_unsat :
  forall cs, resolvent cs [] -> ClauseSet.unsat cs.
Proof.
  intros cs Hres [m Hm].
  now pose proof (resolvent_sound m cs _ Hres Hm).
Qed.

Inductive resolvent_seq : ClauseSet.t -> Clause.t -> Prop :=
  | resolvent_seq_base : forall cs c,
    resolvent cs c -> resolvent_seq cs c
  | resolvent_seq_step : forall cs c c',
    resolvent cs c ->
    resolvent_seq (c::cs) c' ->
    resolvent_seq cs c'.

Lemma resolvent_seq_sound :
  forall cs c m,
    resolvent_seq cs c ->
    ClauseSet.eval m cs = true ->
    Clause.eval m c = true.
Proof.
  intros cs c m Hres Heval.
  induction Hres.
  + eauto using resolvent_sound.
  + eapply IHHres.
    simpl; apply Bool.andb_true_iff; split; auto.
    eauto using resolvent_sound.
Qed.

Inductive proof_step : Type :=
  | proof_mem (c : Clause.t)
  | proof_cut (n : nat) (c1 c2 : Clause.t).

Definition conclusion (ut : proof_step) : Clause.t :=
  match ut with
  | proof_mem c => c
  | proof_cut _ c1 c2 => c1 ++ c2
  end.

Definition is_proof_step (context : ClauseSet.t) (ut : proof_step) : bool :=
  match ut with
  | proof_mem c =>
    ClauseSet.mem context c
  | proof_cut l c1 c2 =>
    ClauseSet.mem context (Literal.Neg l::c1) &&
    ClauseSet.mem context (Literal.Pos l::c2)
  end.

Lemma is_proof_step_sound' :
  forall ctx ut,
    is_proof_step ctx ut = true ->
    resolvent ctx (conclusion ut).
Proof.
  intros ctx ut.
  induction ut as [ | l c1 c2 ].
  - eauto using resolvent.
  - intros [H1 H2]%Bool.andb_true_iff.
    eauto using resolvent.
Qed.

Lemma is_proof_step_sound :
  forall ctx ut m,
    is_proof_step ctx ut = true ->
    ClauseSet.eval m ctx = true ->
    Clause.eval m (conclusion ut) = true.
Proof.
  eauto using resolvent_sound, is_proof_step_sound'.
Qed.

Fixpoint is_proof (context : ClauseSet.t) (uts : list proof_step) (c : Clause.t) : bool :=
  match uts with
  | [] => ClauseSet.mem context c
  | ut::uts =>
    is_proof_step context ut &&
    is_proof ((conclusion ut)::context) uts c
  end.

Lemma is_proof_sound' :
  forall uts ctx c,
  is_proof ctx uts c = true ->
  resolvent_seq ctx c.
Proof.
  intros uts.
  induction uts.
  - eauto using resolvent_seq_base, resolvent_mem.
  - intros. simpl in H.
    rewrite Bool.andb_true_iff in H.
    destruct H as [H1 H2].
    eapply resolvent_seq_step.
    + apply (is_proof_step_sound' _ _ H1).
    + apply (IHuts _ _ H2).
Qed.

Lemma is_proof_sound :
  forall uts ctx c m,
    is_proof ctx uts c = true ->
    ClauseSet.eval m ctx = true ->
    Clause.eval m c = true.
Proof.
  eauto using resolvent_seq_sound, is_proof_sound'.
Qed.

Theorem resolvent_seq_bot_unsat :
  forall cs, resolvent_seq cs [] -> ClauseSet.unsat cs.
Proof.
  intros cs Hres [m Hm].
  now pose proof (resolvent_seq_sound cs _ m Hres Hm).
Qed.