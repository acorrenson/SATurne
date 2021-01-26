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
Lemma lit_eqb_dec: 
  forall x y:literal, {x = y} + {x <> y}.
Proof.
  decide equality; [apply Nat.eq_dec | apply Nat.eq_dec].
Qed.

(** A literal is always different from its negation *)
Lemma lit_eqb_neg_false :
  forall l, lit_eqb (lit_neg l) l = false.
Proof.
  intros.
  induction l.
  + auto.
  + auto.
Qed.