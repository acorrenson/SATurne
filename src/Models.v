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
            Module -- Models
****************************************************)

Require Import Clauses.
Require Import Sat.

Definition model (e : assignment) (p : problem) : Prop :=
  [| p | e |] = true.

Notation "e '|=a' p" := (model e p) (at level 80).

Definition valid (p : problem) : Prop :=
  forall e, e |=a p.

Notation "'|=' p" := (valid p) (at level 80).

Definition consequence (p : problem) (q : problem) : Prop :=
  forall e, e |=a p -> e |=a q.

Notation "p '|=l' q" := (valid p) (at level 80).

Example test1: valid nil.
Proof.
  red; intros.
  reflexivity.
Qed.

Definition equivalent (p q : problem) : Prop :=
  p |=l q /\ q |=l p.

Notation "p === q" := (equivalent p q) (at level 80).

Definition equisat (p q : problem) : Prop :=
  sat p <-> sat q.

Notation "p <~> q" := (equisat p q) (at level 80).

Definition reducible (p q : problem) : Prop :=
  p <~> q /\ p |=l q.

Notation "p ~> q" := (reducible p q) (at level 80).

Example test2: (nil ~> nil).
Proof.
  red; split.
  - red. reflexivity.
  - exact test1.
Qed.