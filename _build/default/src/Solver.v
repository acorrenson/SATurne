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
            Module -- Sat Solver
****************************************************)

Require Import Arith Lia List Recdef Program.Wf.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import SATurn.Sat.
Require Import SATurn.Evaluation.
Require Import SATurn.Solver_aux.

(** Solutions to a SAT problem *)
Local Definition solutions : Type := list assignment.

(** Resolution algorithm *)
Function resolve (p:problem) {measure problem_size p} : solutions :=
  match p with
  | [] => [[]]
  | c::pp =>
    match c with
    | [] => []
    | l::cc =>
      let p1 := propagate l pp in
      let p2 := propagate (lit_neg l) (cc::pp) in
      let s1 := List.map (List.cons l) (resolve p1) in
      let s2 := List.map (List.cons (lit_neg l)) (resolve p2) in
      s1 ++ s2
    end
  end.
Proof.
  (* Termination Proof *)
  all: intros p c pp l cc; simpl.
  - destruct existsb; simpl.
    + destruct  (propagate_variant (lit_neg l) pp); lia.
    + destruct  (remove_lit_variant (lit_neg (lit_neg l)) cc),
                (propagate_variant (lit_neg l) pp); lia.
  - destruct (propagate_variant l pp); lia.
Defined.

Lemma propagate_correct a l p:
  [| propagate l p | a |] = true ->
  [| p | l :: a |] = true.
Proof.
  revert a l. induction p as [ | c p IHp]; auto; cbn.
  intros a l Ha. destruct (existsb (lit_eqb l) c) eqn:HH.
  - apply existsb_exists in HH. destruct HH as [l' [? ->%lit_eqb_eq]].
    rewrite Bool.andb_true_iff. apply IHp in Ha. split; auto.
    eapply eval_clause_in; eauto. constructor; auto.
  - rewrite Bool.andb_true_iff. cbn in Ha. rewrite Bool.andb_true_iff in Ha.
    destruct Ha as [He Hp]. split; eauto. apply eval_clause_remove_neg; auto.
    now apply existsb_lit_notin.
Qed.

Lemma resolve_correct:
  forall (a:assignment) (p:problem),
  List.In a (resolve p) -> eval p a = true.
Proof.
  intros *. revert p a.
  refine (resolve_ind (fun _ _ => _) _ _ _).
  { intros ? ->. auto. }
  { intros * -> ->. auto. }
  intros * -> * -> p1 p2 H1 s1 H2 s2 a HIn. cbn.
  rewrite Bool.andb_true_iff, Bool.orb_true_iff.
  rewrite resolve_equation, in_app_iff in HIn. destruct HIn as [HIn|HIn].
  { apply in_map_iff in HIn. destruct HIn as [a' [<- HIn]]. fold p1 in HIn.
    specialize (H1 _ HIn). cbn. clear s1 H2 s2 p2. subst p1.
    rewrite Bool.orb_true_iff. rewrite lit_eqb_eq; split; auto.
    apply propagate_correct; auto. }
  { apply in_map_iff in HIn. destruct HIn as [a' [<- HIn]]. fold p2 in HIn.
    specialize (H2 _ HIn). clear s1 H1 s2 p1. subst p2. cbn.
    rewrite Bool.orb_true_iff. rewrite lit_eqb_eq. cbn in H2.
    destruct (existsb (lit_eqb (lit_neg l)) cc) eqn:Hlcc.
    { split. 2: now apply propagate_correct.
      destruct (existsb (lit_eqb l) a') eqn:?; auto. right.
      apply existsb_exists in Hlcc. destruct Hlcc as [? [? <-%lit_eqb_eq]].
      apply (eval_clause_in (lit_neg l)); auto. now constructor. }
    { rewrite lit_neg_twice in H2. cbn in H2. rewrite Bool.andb_true_iff in H2.
      destruct H2 as [? ?]. split. 2: now apply propagate_correct.
      destruct (existsb (lit_eqb l) a') eqn:?; auto. right.
      apply existsb_lit_notin in Hlcc. apply existsb_lit_notin in Heqb.
      eapply eval_clause_remove_neg; auto. now rewrite lit_neg_twice. } }
Qed.

Lemma resolve_complete:
  forall (a:assignment) (p:problem),
  eval p a = true -> List.In a (resolve p).
Proof.
Admitted.

