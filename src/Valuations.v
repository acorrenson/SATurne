Require Import Clauses List.
Import ListNotations.

Definition valuation : Type := (nat -> bool).

Definition eval_lit (v : valuation) (l : literal) :=
  match l with
  | Pos x => v x
  | Neg x => negb (v x)
  end.

Fixpoint eval_clause (v : valuation) (c : clause) : bool :=
  match c with
  | []    => false
  | l::ls => orb (eval_lit v l) (eval_clause v ls)
  end.

Fixpoint eval (v : valuation) (p : problem) : bool :=
  match p with
  | []    => true
  | c::cs => andb (eval_clause v c) (eval v cs)
  end.

Notation "[| x | v |]" := (eval v x).

Definition v_bot := fun (_ : nat) => false.

Definition v_top := fun (_ : nat) => true.

Definition substitute (v : valuation) (x : nat) (b : bool) :=
  fun y => if Nat.eqb y x then b else v y.

Fixpoint sem_asg (a : assignment) : valuation :=
  match a with
  | [] => v_bot
  | (Pos x)::xs => substitute (sem_asg xs) x true
  | (Neg x)::xs => substitute (sem_asg xs) x false
  end.

Coercion sem_asg : assignment >-> valuation.