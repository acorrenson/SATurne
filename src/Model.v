From Coq Require Import Arith List ListSet.
Import ListNotations.

Ltac nat_eq :=
  match goal with
  | [ E : _ =? _ = true |- _ ] =>
    apply beq_nat_true in E as ->; clear E; nat_eq
    | [ E : _ =? _ = false |- _ ] =>
    apply beq_nat_false in E; clear E; nat_eq
  | _ =>
    simpl; try (rewrite Nat.eqb_refl in *); simpl; intuition
  end.

Ltac case_eq m n :=
  simpl in *; destruct (Nat.eqb m n) eqn:E; nat_eq.

Module Type MODEL.
  Parameter t : Type.
  Parameter get : t -> nat -> bool.
End MODEL.


Module LModel <: MODEL.

Definition t := list nat.

Fixpoint get (m : t) (n : nat) :=
  match m with
  | [] => false
  | x::xs =>
    if x =? n then true
    else get xs n
  end.

Lemma In_satisfy :
  forall m n, In n m <-> get m n = true.
Proof.
  intros. induction m. easy. split.
  + intros [-> | H]; [nat_eq | case_eq a n].
  + intros. case_eq a n.
Qed.

End LModel.


Definition t := nat -> bool.

Definition get (m : t) n := m n.

Definition inv (m : t) := fun x => negb (m x).