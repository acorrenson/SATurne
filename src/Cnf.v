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

From Coq Require Import List Arith PeanoNat Lia.
Require Import Clauses.
Import ListNotations.

Module LProp.

(** Logic language *)
Inductive t : Type :=
  | And  : t -> t -> t
  | Or   : t -> t -> t
  | Neg  : t -> t
  | Atom : nat -> t.

Definition Impl (f1 f2 : t) := Or (Neg f1) f2.

Fixpoint eval (m : Model.t) (f : t) : bool :=
  match f with
  | And f1 f2  => (eval m f1 && eval m f2)%bool
  | Or f1 f2   => (eval m f1 || eval m f2)%bool
  | Neg f   => negb (eval m f)
  | Atom a  => Model.satisfy m a
  end.

Fixpoint negvar (f : t) : t :=
  match f with
  | And f1 f2 => And (negvar f1) (negvar f2)
  | Or f1 f2 => Or (negvar f1) (negvar f2)
  | Neg f => Neg (negvar f)
  | Atom a => Neg (Atom a)
  end.

Definition fmodel := nat -> bool.

Fixpoint fsatisfy (m : fmodel) (f : t) : bool :=
  match f with
  | And f1 f2 => fsatisfy m f1 && fsatisfy m f2
  | Or f1 f2 => fsatisfy m f1 || fsatisfy m f2
  | Neg f => negb (fsatisfy m f)
  | Atom a => m a
  end.

Definition inv (m : fmodel) : fmodel :=
  fun x => negb (m x).

Theorem negvar_sat :
  forall f m, fsatisfy m f = fsatisfy (inv m) (negvar f).
Proof.
  intros; induction f; simpl.
  + now rewrite IHf1, IHf2.
  + now rewrite IHf1, IHf2.
  + now rewrite IHf.
  + unfold inv.
    now rewrite Bool.negb_involutive.
Qed.

End LProp.

Module PreCnf.

Inductive t : Set :=
  | And   : t -> t -> t
  | Or    : t -> t -> t
  | Lit   : Literal.t -> t.

(** Conversion algorithm from [LProp.t] to [PreCnf.t] *)
Fixpoint remove_neg' (sign : bool) (f : LProp.t) : t :=
  match f with
  | LProp.And a b =>
    if sign then And (remove_neg' sign a) (remove_neg' sign b)
    else Or (remove_neg' false a) (remove_neg' false b)
  | LProp.Or a b =>
    if sign then Or (remove_neg' sign a) (remove_neg' sign b)
    else And (remove_neg' false a) (remove_neg' false b)
  | LProp.Neg a =>
    if sign then remove_neg' false a
    else remove_neg' true a
  | LProp.Atom n =>
    if sign then Lit (Literal.Pos n)
    else Lit (Literal.Neg n)
  end.

Definition remove_neg := remove_neg' true.

Fixpoint eval (m : Model.t) (f : PreCnf.t) : bool :=
  match f with
  | And f1 f2 => (eval m f1 && eval m f2)%bool
  | Or f1 f2 => (eval m f1 || eval m f2)%bool
  | Lit l => Literal.eval m l
  end.

  (* [remove_neg' false] inverse the denotations *)
Lemma remove_neg_false_negb:
  forall f m, eval m (remove_neg' false f) = negb (eval m (remove_neg' true f)).
Proof.
  intros.
  induction f; simpl.
  - rewrite IHf1, IHf2, Bool.negb_andb; reflexivity.
  - rewrite IHf1, IHf2, Bool.negb_orb; reflexivity.
  - rewrite IHf, Bool.negb_involutive; reflexivity.
  - reflexivity.
Qed.

Theorem remove_neg_correct:
  forall f m, LProp.eval m f = eval m (remove_neg f).
Proof.
  intros.
  induction f; simpl.
  - rewrite IHf1, IHf2; reflexivity.
  - rewrite IHf1, IHf2; reflexivity.
  - rewrite IHf. unfold remove_neg. simpl.
    rewrite remove_neg_false_negb; reflexivity.
  - reflexivity.
Qed.

End PreCnf.

Module Cnf.

(** Distribute a clause on a set of clauses *)
Definition merge_clause (c : Clause.t) (cs : ClauseSet.t) :=
  map (fun c' => c ++ c') cs.

(** Double distribute a set of clauses on another one *)
Fixpoint merge (cs cs' : ClauseSet.t) : ClauseSet.t :=
  match cs with
  | [] => []
  | c::cs => (merge_clause c cs') ++ (merge cs cs')
  end.

(** [PreCnf.t] to [ClauseSet.t] conversion *)
Fixpoint cnf' (f : PreCnf.t) : ClauseSet.t :=
  match f with
  | PreCnf.And a b => (cnf' a) ++ (cnf' b)
  | PreCnf.Or a b => merge (cnf' a) (cnf' b)
  | PreCnf.Lit a => [[a]]
  end.

(** CNF conversion *)
Definition cnf (f : LProp.t) : ClauseSet.t :=
  cnf' (PreCnf.remove_neg f).

(* [merge_clause] preserve the semantic *)
Theorem merge_clause_correct:
  forall c cs m, ClauseSet.eval m (merge_clause c cs)  = orb (Clause.eval m c) (ClauseSet.eval m cs).
Proof.
  induction cs; simpl; intuition.
  now rewrite Clause.eval_app, IHcs, Bool.orb_andb_distrib_r.
Qed.

(* [merge] preserve the semantic *)
Theorem merge_correct:
  forall cs cs' m, orb (ClauseSet.eval m cs) (ClauseSet.eval m cs') = ClauseSet.eval m (merge cs cs').
Proof.
  intros.
  induction cs; simpl; intuition.
  now rewrite ClauseSet.eval_app,
            merge_clause_correct,
            <- IHcs,
            Bool.orb_andb_distrib_l.
Qed.

(* [cnf'] preserve the semantic *)
Theorem cnf'_correct:
  forall f m, PreCnf.eval m f = ClauseSet.eval m (cnf' f).
Proof.
  intros.
  induction f; simpl.
  - now rewrite ClauseSet.eval_app, IHf1, IHf2.
  - now rewrite <- merge_correct, IHf1, IHf2.
  - now destruct (Literal.eval m t).
Qed.

(* [cnf] preserve the semantic *)
Theorem cnf_correct:
  forall f m, LProp.eval m f = ClauseSet.eval m (cnf f).
Proof.
  intros.
  unfold cnf.
  rewrite PreCnf.remove_neg_correct,
          cnf'_correct.
  reflexivity.
Qed.

Import LProp.

Notation P := (Atom 1).
Notation Q := (Atom 2).
Notation R := (Atom 3).

Compute (cnf (Impl (Impl Q P) (And (Neg P) (And Q R)))).

End Cnf.

Module Subst.

Declare Scope loc.
Delimit Scope loc with loc.

Inductive location : Type :=
  | There : location
  | Left : location -> location
  | Right : location -> location.

Inductive substitute : LProp.t -> LProp.t -> location -> LProp.t -> Prop :=
  | subst_there H F :
    substitute H F There F
  | subst_and_l H1 H1' H2 F l :
    substitute H1 F l H1' ->
    substitute (LProp.And H1 H2) F (Left l) (LProp.And H1' H2)
  | subst_and_r H1 H2 H2' F l :
    substitute H2 F l H2' ->
    substitute (LProp.And H1 H2) F (Right l) (LProp.And H1 H2')
  | subst_or_l H1 H1' H2 F l :
    substitute H1 F l H1' ->
    substitute (LProp.Or H1 H2) F (Left l) (LProp.Or H1' H2)
  | subst_or_r H1 H2 H2' F l :
    substitute H2 F l H2' ->
    substitute (LProp.Or H1 H2) F (Right l) (LProp.Or H1 H2')
  | subst_neg H H' F l :
    substitute H F l H' ->
    substitute (LProp.Neg H) F (Left l) (LProp.Neg H').
#[export] Hint Constructors substitute : core.

Import LProp.

Example test :
  substitute (And (And (Atom 1) (Atom 2)) (Atom 3)) (Atom 4) (Left (Left There)) (And (And (Atom 4) (Atom 2)) (Atom 3)).
Proof.
  auto.
Qed.

End Subst.