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
From SATurn Require Import Model.
Import ListNotations.


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
  | Pos n => Model.get m n
  | Neg n => negb (Model.get m n)
  end.

End Literal.


Module Clause.

Definition t : Type := list Literal.t.

Definition mem (c : t) (l : Literal.t) : bool :=
  List.existsb (Literal.eqb l) c.

Lemma In_mem :
  forall l c, In l c <-> mem c l = true.
Proof.
  intros l c.
  split; [ intros | intros [l' [H1 ->%Literal.eqb_eq]]%existsb_exists]; auto.
  apply existsb_exists.
  eauto using Literal.eqb_refl.
Qed.
#[global]
Hint Resolve In_mem : core.

Definition sub_clause (c1 c2 : t) : bool :=
  List.forallb (mem c2) c1.

Lemma sub_clause_refl :
  forall c, sub_clause c c = true.
Proof.
  induction c as [ | l c IHc]; auto.
  apply forallb_forall.
  intros x [-> | H]; simpl.
  + now rewrite Literal.eqb_refl.
  + rewrite (proj1 (In_mem _ _) H); intuition.
Qed.

Definition eqb (c1 c2 : t) : bool :=
  sub_clause c1 c2 && sub_clause c2 c1.

Lemma eqb_refl :
  forall c, eqb c c = true.
Proof.
  intros c.
  apply Bool.andb_true_iff; auto using sub_clause_refl.
Qed.
#[global]
Hint Resolve eqb_refl : core.

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

Definition eval (m : Model.t) (c : t) :=
  existsb (Literal.eval m) c.

Lemma eval_true_iff :
  forall c m, eval m c = true <-> exists x, In x c /\ Literal.eval m x = true.
Proof.
  intros c m; split.
  + intros [x [H1 H2]]%existsb_exists. firstorder.
  + intros [x [Hx Heval]]. apply existsb_exists. firstorder.
Qed.

Lemma eval_false_iff :
  forall c m, eval m c = false <-> forall x, In x c -> Literal.eval m x = false.
Proof.
  intros c m; split.
  + induction c; try easy; simpl in *.
    intros [H1 H2]%Bool.orb_false_iff x [-> | Hx]; auto.
  + induction c; try easy; simpl; intuition.
Qed.

Lemma eval_app :
  forall c1 c2 m, eval m (c1 ++ c2) = (eval m c1 || eval m c2)%bool.
Proof.
  intros.
  induction c1; simpl; auto.
  now destruct (Literal.eval m a) eqn:E.
Qed.

Lemma sub_clause_in :
  forall c1 c2 l, sub_clause c1 c2 = true -> In l c1 -> In l c2.
Proof.
  intros c1 c2 l Hsub Hin. unfold sub_clause in Hsub.
  rewrite forallb_forall in Hsub.
  firstorder using In_mem.
Qed.

Lemma eqb_equiv :
  forall c1 c2 m, eqb c1 c2 = true -> eval m c1 = eval m c2.
Proof.
  intros c1 c2 m.
  destruct (eval m c1) eqn:E.
  + apply eval_true_iff in E as [x [Hx1 Hx2]].
    intros [H1%(sub_clause_in _ _ x) H2%(sub_clause_in _ _ x)]%Bool.andb_true_iff; auto.
    symmetry. apply eval_true_iff. firstorder.
  + pose proof (proj1 (eval_false_iff c1 m) E).
    intros [H1 H2]%Bool.andb_true_iff.
    symmetry. apply eval_false_iff. firstorder using sub_clause_in.
Qed.

End Clause.


Module ClauseSet.

Definition t := list Clause.t.

Definition mem (cs : t) (c : Clause.t) : bool :=
  existsb (Clause.eqb c) cs.

Lemma In_mem :
  forall cs c, In c cs -> mem cs c = true.
Proof.
  intros cs c Hin.
  apply existsb_exists; eauto.
Qed.

Definition eval (m : Model.t) (cs : t) : bool :=
  forallb (Clause.eval m) cs.

Lemma eval_app :
  forall c1 c2 m, eval m (c1 ++ c2) = (eval m c1 && eval m c2)%bool.
Proof.
  intros.
  induction c1; simpl; auto.
  destruct (Clause.eval m a) eqn:E; auto.
Qed.

Lemma eval_true_iff :
  forall cs m, eval m cs = true <-> forall c, ClauseSet.mem cs c = true -> Clause.eval m c = true.
Proof.
  intros cs m. split.
  + induction cs; try easy; simpl in *.
    intros [H1 H2]%Bool.andb_true_iff c [H | H]%Bool.orb_true_iff; auto.
    now rewrite (Clause.eqb_equiv _ a).
  + intros. apply forallb_forall.
    intros x Hx%In_mem.
    firstorder.
Qed.

Lemma eval_false_iff :
  forall cs m, eval m cs = false <-> exists c, In c cs /\ Clause.eval m c = false.
Proof.
  intros cs m; split.
  + induction cs; try easy.
    intros [H1 | H2]%Bool.andb_false_iff; firstorder.
  + induction cs; [ intros [c [[] _]] | intros [c [[->|Hc] Heval]]]; simpl.
    * now rewrite Heval.
    * apply Bool.andb_false_iff. firstorder.
Qed.

Definition sat (cs : ClauseSet.t) :=
  exists m, ClauseSet.eval m cs = true.

Definition unsat (cs : ClauseSet.t) :=
  ~sat cs.

End ClauseSet.