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
            Module -- Sat Problems 
****************************************************)

Require Import Arith.
Require Import Lists.List.
Require Import SATurn.Clauses.
Require Import SATurn.Valuations.
Import ListNotations.

(** Problem satisfiability *)
Definition sat (p:problem) : Prop :=
  exists (a : valuation), [| p | a |] = true.

(** Problem unsatisfiability *)
Definition unsat (p:problem) : Prop := ~ sat p.

(** The empty problem is satisfiable *)
Example smallest_sat_problem : sat [] .
Proof.
  unfold sat.
  exists v_bot; simpl; reflexivity.
Qed.

(** The smallest problem containing the empty clause is unsatisfiable *)
Example smallest_unsat_problem:
  unsat [[]].
Proof.
  unfold unsat.
  unfold sat.
  unfold not.
  simpl.
  intro H.
  elim H.
  intros _ H'.
  discriminate H'.
Qed.

Lemma sat_clause_decr:
  forall c p, 
  sat (c::p) -> sat p.
Proof.
  intros.
  induction H.
  simpl in H.
  destruct (andb_prop _ _ H) as [H1 H2].
  eexists.
  apply H2.
Qed.

Lemma model_sat:
  forall p (a : valuation),
  [| p | a |] = true -> sat p.
Proof.
  intros p a H. eexists. apply H.
Qed.

Lemma model_clause_decr:
  forall c p a,
  [| c::p | a |] = true -> [| p | a |] = true.
Proof.
  intros.
  simpl in H.
  destruct (andb_prop _ _ H).
  apply H1.
Qed.
