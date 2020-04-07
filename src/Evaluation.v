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
Definition clause : Type := list literal.

(** Type problem *)
Definition problem : Type := list clause.

(** Type assignment*)
Definition assignment : Type := list literal.

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
Hint Resolve lit_eqb_eq.

(** Decidability of the literal boolean equality *)
Lemma lit_eqb_dec: 
  forall x y:literal, {x = y} + {x <> y}.
Proof.
  decide equality; [apply Nat.eq_dec | apply Nat.eq_dec].
Qed.
Hint Resolve lit_eqb_dec.

(** A literal is always different from its negation *)
Lemma lit_eqb_neg_false :
  forall l, lit_eqb (lit_neg l) l = false.
Proof.
  intros.
  induction l.
  + auto.
  + auto.
Qed.
Hint Resolve lit_eqb_neg_false.

(** Evaluation of a clause for a given assignment *)
Fixpoint eval_clause (c:clause) (a:assignment) : bool :=
  match c with
  | l::rest =>
    List.existsb (lit_eqb l) a || eval_clause rest a
  | nil => false
  end.

(** Evaluation of a problem for a given assignment *)
Fixpoint eval (p:problem) (a:assignment) : bool :=
  match p with
  | c::rest =>
    eval_clause c a && eval rest a
  | nil => true
  end.

(** Any clause evaluates to false in the empty context *)
Lemma eval_clause_nil :
  forall c:clause, eval_clause c [] = false.
Proof.
  intros.
  induction c.
  + auto.
  + simpl. apply IHc; reflexivity.
Qed.
Hint Resolve eval_clause_nil.


