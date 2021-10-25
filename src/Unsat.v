Require Import Evaluation Sat List ListSet.
Import ListNotations.


Module Clause.

Definition sub_clause (c1 c2 : clause) : bool :=
  List.forallb (fun x => set_mem (lit_eqb_dec) x c1) c2.

Definition eqb (c1 c2 : clause) : bool :=
  sub_clause c1 c2 && sub_clause c2 c1.

Lemma In_set_mem :
  forall A l (x : A) Heq, In x l -> set_mem Heq x l = true.
Proof.
  induction l; intros; inversion H.
  - subst. simpl. now destruct Heq.
  - simpl. destruct Heq; auto.
Qed.

Lemma eq_sub_clause :
  forall c, sub_clause c c = true.
Proof.
  induction c as [ | l c IHc]; auto.
  apply forallb_forall; intros.
  inversion H; subst; simpl.
  - now destruct lit_eqb_dec.
  - destruct lit_eqb_dec; auto.
    now apply In_set_mem.
Qed.

Lemma eq_eqb :
  forall (c : clause), eqb c c = true.
Proof.
  induction c as [ | l c IHc ]; auto.
  unfold eqb.
  now rewrite !eq_sub_clause.
Qed.
End Clause.

Inductive resolution : problem -> clause -> Prop :=
  | unsat_axiom : forall c p, set_mem p c -> resolution p c.
  | unsat_res :
    forall p l1 c1 l2 c2,
      l
