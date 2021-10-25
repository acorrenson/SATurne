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
Require Import SATurn.Evaluation.
Import ListNotations.

(** Problem satisfiability *)
Definition sat (p:problem) : Prop :=
  exists (a:assignment), [| p | a |] = true.

(** Problem unsatisfiability *)
Definition unsat (p:problem) : Prop := ~ sat p.

(** The empty problem is satisfiable *)
Lemma smallest_sat_problem : sat [] .
Proof.
  unfold sat.
  exists []; simpl; reflexivity.
Qed.

(** The smallest problem containing the empty clause is unsatisfiable *)
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

Lemma sat_aff:
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

Lemma sol_sat:
  forall p a,
  [| p | a |] = true -> sat p.
Proof.
  intros p a H. eexists. apply H.
Qed.

Lemma sat_add_sol:
  forall c p a,
  [| c::p | a |] = true -> eval p a = true.
Proof.
  intros.
  simpl in H.
  destruct (andb_prop _ _ H).
  apply H1.
Qed.
