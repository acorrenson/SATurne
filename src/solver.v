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

Require Import Arith Lia.
Require Import Recdef.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import SATurn.Sat.
Require Import SATurn.Evaluation.

(** Remove a literal from a clause *)
Fixpoint remove_lit l c :=
  match c with
  | [] => []
  | x::rest =>
    if lit_eqb x l
    then rest
    else x::(remove_lit l rest)
  end.

(** Simplify a problem by propagating a literal *)
Fixpoint propagate (l:literal) (p:problem) : problem :=
  match p with
  | [] => []
  | c::rest =>
    if List.existsb ((lit_eqb) l) c 
    then propagate l rest
    else (remove_lit (lit_neg l) c)::(propagate l rest)
  end.

(** Naive size of a problem (number of literals) *)
Fixpoint problem_size (p:problem) :=
  match p with
  | [] => 0
  | c::rest => length c + problem_size rest
  end.

(** Removing a literal from a clause reduces its size *)
Lemma remove_lit_reduce_size :
  forall l:literal, forall c:clause, length (remove_lit l c) <= length c.
Proof.
  intros.
  induction c.
  + auto.
  + simpl.
    destruct (lit_eqb a l).
    - auto.
    - simpl. apply le_n_S. exact IHc.
Qed.

(** Simplyfing a problem by propatation of a literal reduces its size *)
Lemma propagate_reduce_problem_size: 
  forall p:problem, forall l:literal, problem_size (propagate l p) <= problem_size p.
Proof.
  intros.
  induction p.
  + auto.
  + simpl.
    destruct existsb.
    * rewrite IHp. rewrite plus_comm. apply le_plus_l.
    * simpl. apply Nat.add_le_mono.
      - apply remove_lit_reduce_size.
      - exact IHp.
Qed.

(** Solutions to a SAT problem *)
Definition solutions : Type := list assignment.

(* Function resolve_one (p : problem) {measure problem_size p}:=
  match p with
  | [] => Some []
  | c::pp =>
    match c with
    | [] => None
    | l::cc =>
      let pb1 := propagate l pp in
      let pb2 := propagate (lit_neg l) (cc::pp) in
      match resolve_one pb1 with
      | Some sol => Some (l::sol)
      | None     =>
        match resolve_one pb2 with
        | Some sol => Some ((lit_neg l)::sol)
        | None => None
        end
      end
    end
  end.
Proof.
Defined. *)

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
      let s1 := (List.map ((List.cons) l) (resolve p1)) in
      let s2 := (List.map ((List.cons) (lit_neg l)) (resolve p2)) in
      s1 ++ s2
    end
  end.
Proof.
  (* Termination Proof *)
  + intros; simpl; apply le_lt_n_Sm; destruct existsb; simpl.
    ++ rewrite plus_comm; apply le_plus_trans; apply propagate_reduce_problem_size.
    ++ rewrite Nat.add_le_mono.
      * auto.
      * apply remove_lit_reduce_size.
      * apply propagate_reduce_problem_size.
  + intros; simpl; apply le_lt_n_Sm.
    rewrite plus_comm.
    apply le_plus_trans.
    apply propagate_reduce_problem_size.
Defined.

Lemma resolve_clause:
  forall c p a,
  In a (resolve (c :: p)) -> eval_clause c a = true.
Proof.
  intros.
  induction c.
  - contradiction H.
  - simpl.
    apply Bool.orb_true_iff.
    right.
    apply IHc.
Admitted.

Lemma resolve_aff:
  forall c p a,
  In a (resolve (c::p)) -> In a (resolve p).
Proof.
  intros.
  induction c.
  - contradiction H.
  - unfold resolve in H.
    cbn in H.
Admitted.

Lemma resolve_correct:
  forall (p:problem) (a:assignment),
  List.In a (resolve p) -> eval p a = true.
Proof.
  intros p.
  induction p; intros.
  + inversion H; subst.
    - simpl. reflexivity.
    - contradiction.
  + simpl; apply andb_true_intro; split.
    - induction a.
      -- contradiction H.
      -- eapply resolve_clause.
          apply H.
    - apply IHp.
      eapply resolve_aff.
      apply H.
Qed.