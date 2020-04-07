(****************************************************

                    ,MMM8&&&.
                _..MMMMM88&&&&..._
            .::'''MMMMM88&&&&&&'''::.
           ::     MMMMM88&&&&&&     ::
           '::....MMMMM88&&&&&&....::'
              `''''MMMMM88&&&&''''`
                    'MMM8&&&'

                     SATurn
                ----------------
             A tiny verified solver

****************************************************)


(***************************************************
            Module -- Sat Problems 
****************************************************)

Require Import Arith.
Require Import Lists.List.
Require Import Evaluation.
Import ListNotations.


(** Problem satisfiability *)
Definition sat (p:problem) : Prop :=
  exists (a:assignment), eval p a = true.

(** Problem unsatisfiability *)
Definition unsat (p:problem) : Prop := ~ sat p.

Lemma smallest_sat_problem : sat [] .
Proof.
  unfold sat.
  exists []; simpl; reflexivity.
Qed.
Hint Resolve smallest_sat_problem.

Lemma smallest_unsat_problem:
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
Hint Resolve smallest_unsat_problem.