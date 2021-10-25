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
            Module -- Clausal form
****************************************************)

From Coq Require Import Arith List ListSet.
Import ListNotations.

Module Model.

Definition t := list nat.

Fixpoint satisfy (m : t) (n : nat) :=
  match m with
  | [] => false
  | x::xs =>
    if x =? n then true
    else satisfy xs n
  end.

Lemma In_satisfy :
  forall m n, In n m <-> satisfy m n = true.
Proof.
  intros.
  induction m.
  - split; inversion 1.
  - split; inversion 1; subst; simpl.
    + now rewrite Nat.eqb_refl.
    + destruct (a =? n); auto.
      now apply IHm.
    + destruct (a =? n) eqn:E.
      * apply Nat.eqb_eq in E; subst.
        now left.
      * firstorder.
Qed.

Definition sub_model (m1 m2 : t) : bool :=
  List.forallb (satisfy m2) m1.

Lemma sub_model_refl :
  forall m, sub_model m m = true.
Proof.
  induction m; simpl; auto.
  unfold sub_model in *.
  rewrite forallb_forall in IHm.
  rewrite Nat.eqb_refl; simpl.
  apply forallb_forall; intros.
  destruct (a =? x); auto.
Qed.

Definition eqb (m1 m2 : t) : bool :=
  sub_model m1 m2 && sub_model m2 m1.

Lemma eq_eqb :
  forall m1 m2, m1 = m2 -> eqb m1 m2 = true.
Proof.
  intros m _ <-.
  unfold eqb.
  now rewrite sub_model_refl.
Qed.

End Model.


Module Literal.

(** Type literal *)
Inductive t : Type :=
  | Pos : nat -> t
  | Neg : nat -> t.

Definition eqb (l1 l2 : t) :=
  match l1, l2 with
  | Pos u, Pos v 
  | Neg u, Neg v => u =? v
  | _, _ => false
  end.

Definition neg (l : t) :=
  match l with
  | Neg n => Pos n
  | Pos n => Neg n
  end.

Lemma eqb_eq :
  forall (l l' : t), eqb l l' = true <-> l = l'.
Proof.
  induction l as [ n | n ], l' as [ n' | n' ]; simpl;
  try easy.
  + rewrite (Nat.eqb_eq); split; now inversion 1.
  + rewrite (Nat.eqb_eq); split; now inversion 1.
Qed.

Lemma eqb_false :
  forall (l l' : t), eqb l l' = false -> l <> l'.
Proof.
  intros l l' Heq <-.
  destruct l; simpl in Heq; now rewrite Nat.eqb_refl in Heq.
Qed.

Lemma eq_dec :
  forall (l l' : t), { l = l' } + { l <> l' }.
Proof.
  decide equality; apply Nat.eq_dec.
Qed.

Lemma eqb_refl :
  forall l, eqb l l = true.
Proof.
  intros.
  now rewrite eqb_eq.
Qed.

Definition eval (m : Model.t) (l : t) : bool :=
  match l with
  | Pos n => Model.satisfy m n
  | Neg n => negb (Model.satisfy m n)
  end.

End Literal.

Module Clause.

Definition t : Type := list Literal.t.

Fixpoint mem (c : t) (l : Literal.t) : bool :=
  match c with
  | [] => false
  | l'::ls =>
    if Literal.eqb l l' then true
    else mem ls l
  end.

Lemma In_mem :
  forall l c, In l c <-> mem c l = true.
Proof.
  intros l c.
  induction c.
  - split; inversion 1.
  - split; intros.
    + induction H; subst; simpl.
      * now rewrite Literal.eqb_refl.
      * destruct Literal.eqb; auto.
        now rewrite <- IHc.
    + simpl in H.
      destruct Literal.eqb eqn:E; auto.
      * rewrite (proj1 (Literal.eqb_eq _ _) E).
        now left.
      * right.
        apply ((proj2 IHc) H).
Qed.

Definition sub_clause (c1 c2 : t) : bool :=
  List.forallb (mem c1) c2.

Lemma sub_clause_refl :
  forall c, sub_clause c c = true.
Proof.
  induction c as [ | l c IHc]; auto.
  apply forallb_forall; intros.
  inversion H; subst; simpl.
  - now rewrite Literal.eqb_refl.
  - destruct Literal.eqb; auto.
    now apply In_mem.
Qed.

Definition eqb (c1 c2 : t) : bool :=
  sub_clause c1 c2 && sub_clause c2 c1.

Lemma eq_eqb :
  forall c1 c2, c1 = c2 -> eqb c1 c2 = true.
Proof.
  intros c _ <-.
  unfold eqb.
  now rewrite sub_clause_refl.
Qed.

Lemma eqb_false :
  forall c1 c2, eqb c1 c2 = false -> c1 <> c2.
Proof.
  intros c1 c2 Heq <-.
  now rewrite (eq_eqb c1 c1 (eq_refl)) in Heq.
Qed.

Fixpoint eval (m : Model.t) (c : t) :=
  match c with
  | [] => false
  | x::xs =>
    if Literal.eval m x then true
    else eval m xs
  end.

Lemma eval_true_exists :
  forall c m, eval m c = true -> exists x, In x c /\ Literal.eval m x = true.
Proof.
  intros c m H.
  induction c; try easy.
  simpl in H.
  destruct (Literal.eval m a) eqn:E;
  firstorder.
Qed.

Lemma exists_eval_true :
  forall c m, (exists x, In x c /\ Literal.eval m x = true) -> eval m c = true.
Proof.
  intros c m [x [Hx Heval]].
  induction c; auto.
  destruct Hx; subst; simpl.
  + now rewrite Heval.
  + destruct (Literal.eval m a); auto.
Qed.

Lemma eval_app :
  forall c1 c2 m, eval m (c1 ++ c2) = (eval m c1 || eval m c2)%bool.
Proof.
  intros.
  induction c1; simpl; auto.
  now destruct (Literal.eval m a) eqn:E.
Qed.

Lemma eqb_equiv :
  forall c1 c2, eqb c1 c2 = true -> forall m, eval m c1 = true <-> eval m c2 = true.
Proof.
  intros c1 c2 [H1 H2]%Bool.andb_true_iff m.
  unfold sub_clause in *; split; intros.
  all:
    apply eval_true_exists in H as [l [Hin Heval]];
    apply exists_eval_true; exists l;
    rewrite forallb_forall in H1, H2;
    firstorder using In_mem.
Qed.

Lemma eqb_equiv' :
  forall c1 c2, eqb c1 c2 = true -> forall m, eval m c1 = false <-> eval m c2 = false.
Proof.
  intros c1 c2 H m; split; intros.
  + assert (~(eval m c1 = true)) by now destruct (eval m c1).
    destruct (eval m c2) eqn:E; auto.
    firstorder using eqb_equiv.
  + assert (~(eval m c2 = true)) by now destruct (eval m c2).
    destruct (eval m c1) eqn:E; auto.
    firstorder using eqb_equiv.
Qed.

Lemma eqb_eval_eq :
  forall c1 c2, eqb c1 c2 = true -> forall m, eval m c1 = eval m c2.
Proof.
  intros.
  destruct (eval m c1) eqn:E.
  + now rewrite (eqb_equiv c1 c2 H m) in E.
  + now rewrite (eqb_equiv' c1 c2 H m) in E.
Qed.

End Clause.


Module ClauseSet.

Definition t := list Clause.t.

Fixpoint mem (cs : t) (c : Clause.t) : bool :=
  match cs with
  | [] => false
  | c'::cs' =>
    if Clause.eqb c c' then true
    else mem cs' c
  end.

Lemma In_mem :
  forall cs c, In c cs -> mem cs c = true.
Proof.
  intros cs c Hccs.
  induction cs; simpl; auto.
  destruct Clause.eqb eqn:E; auto.
  apply Clause.eqb_false in E.
  destruct Hccs; auto.
Qed.

Fixpoint eval (m : Model.t) (cs : t) : bool :=
  match cs with
  | [] => true
  | c::cs => (Clause.eval m c && eval m cs)%bool
  end.

Lemma eval_app :
  forall c1 c2 m, eval m (c1 ++ c2) = (eval m c1 && eval m c2)%bool.
Proof.
  intros.
  induction c1; simpl; auto.
  destruct (Clause.eval m a) eqn:E; auto.
Qed.

Lemma eval_true_forall :
  forall cs m, eval m cs = true -> forall c, mem cs c = true -> Clause.eval m c = true.
Proof.
  intros cs m H c Hc.
  induction cs; try easy.
  simpl in H.
  destruct (Clause.eval m a) eqn:E; simpl in H; try easy.
  simpl in Hc.
  destruct (Clause.eqb c a) eqn:E'.
  + eapply Clause.eqb_equiv.
    apply E'.
    apply E.
  + firstorder.
Qed.

End ClauseSet.

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

Definition sat (cs : ClauseSet.t) :=
  exists m, ClauseSet.eval m cs = true.

Definition unsat (cs : ClauseSet.t) :=
  ~sat cs.

Theorem resolvent_bot_unsat :
  forall cs, resolvent cs [] -> unsat cs.
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
  forall cs, resolvent_seq cs [] -> unsat cs.
Proof.
  intros cs Hres [m Hm].
  now pose proof (resolvent_seq_sound cs _ m Hres Hm).
Qed.