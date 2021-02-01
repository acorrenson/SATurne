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
            Module -- Evaluation Model 
****************************************************)

Require Import Arith.
Require Import Lists.List.
Import ListNotations.

(** Type literal *)
Inductive literal : Type :=
  | Pos : nat -> literal
  | Neg : nat -> literal.

(** Type clause *)
Definition clause := (list literal).

(** Type problem *)
Definition problem := (list clause).

(** Type assignment*)
Definition assignment := (list literal).

(** Litteral boolean equality *)
Definition lit_eqb (l1 l2 : literal) :=
  match l1, l2 with
  | Pos u, Pos v 
  | Neg u, Neg v => u =? v
  | _, _ => false
  end.

(** Litteral negation *)
Definition lit_neg (l : literal) :=
  match l with
  | Pos u => Neg u
  | Neg u => Pos u
  end.

(** Equivalence of the boolean equality with the standard equality *)
Lemma lit_eqb_eq:
  forall x y:literal, lit_eqb x y = true <-> x = y.
Proof.
  intros.
  induction x as [n1 | n1]; induction y as [n2 | n2]; split; intros H.
  + simpl in H; apply (Nat.eqb_eq) in H; auto.
  + elim H; apply (Nat.eqb_eq); reflexivity.
  + discriminate H.
  + discriminate H.
  + discriminate H.
  + discriminate H.
  + simpl in H; apply (Nat.eqb_eq) in H; auto.
  + elim H; apply (Nat.eqb_eq); reflexivity.
Qed.

(** Decidability of the literal boolean equality *)
Lemma lit_eq_dec: 
  forall x y:literal, {x = y} + {x <> y}.
Proof.
  decide equality; [apply Nat.eq_dec | apply Nat.eq_dec].
Qed.

Lemma lit_eqb_dec:
  forall x y:literal, {lit_eqb x y = true} + {lit_eqb x y = false}.
Proof.
  intros [ n1 | n1 ] [ n2 | n2 ]; auto; simpl;
  induction (n1 =? n2); auto.
Qed.

(** A literal is always different from its negation *)
Lemma lit_eqb_neg_false :
  forall l, lit_eqb (lit_neg l) l = false.
Proof.
  intros []; auto.
Qed.

Definition clause_eq (c1 c2 : clause) : Prop :=
  forall (x : literal), In x c1 <-> In x c2.

Fixpoint clause_mem (l : literal) (c : clause) : bool :=
  match c with
  | [] => false
  | l'::c' =>
    lit_eqb l' l || clause_mem l c'
  end.

Fixpoint sub_clause (c1 c2 : clause) : bool :=
  match c1 with
  | [] => true
  | l::c1' =>
    clause_mem l c2 && sub_clause c1' c2
  end.

(* Lemma sub_clause_in_iff:
  forall c1 c2, sub_clause c1 c2 = true <-> forall l, In l c1 -> In l c2.
Proof.
  intros. split; intros.
  + inversion H.


Definition clause_eqb (c1 c2 : clause) : bool :=
  sub_clause c1 c2 && sub_clause c2 c1.

Lemma clause_eqb_eq:
  forall c1 c2, clause_eqb c1 c2 = true <-> clause_eq c1 c2.
Proof.
  intros. split. intros.
  + unfold clause_eqb in H. *)


Lemma clause_eqv_dec:
  forall (c1 c2 : clause), {c1 = c2} + {c1 <> c2}.
Proof.
  decide equality.
  apply lit_eq_dec.
Qed.

(* Lemma clause_eq_dec:
  forall (c1 c2 : clause), {clause_eq c1 c2} + {~ (clause_eq c1 c2)}.
Proof.
  intros.
  destruct (in_deb
Qed. *)


Lemma clause_eq_eq:
  forall (c1 c2 : clause), c1 = c2 -> clause_eq c1 c2.
Proof.
  induction c1 as [ | l1 c1' IH1 ];
  induction c2 as [ | l2 c2' IH2 ]; red; intros.
  + tauto.
  + discriminate.
  + discriminate.
  + inversion H. tauto.
Qed.

Definition clause_eqb (c1 c2 : clause) : bool.
Proof.
  destruct (clause_eqv_dec c1 c2).
  + apply true.
  + apply false.
Defined.

Lemma clause_eqb_eq:
  forall (c1 c2 : clause), clause_eqb c1 c2 = true <-> c1 = c2.
Proof.
  intros.
  unfold clause_eqb.
  destruct (clause_eqv_dec c1 c2).
  + tauto.
  + split.
    - discriminate.
    - contradiction.
Qed.
