
(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

module Nat =
 struct
 end

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

module Literal =
 struct
  type t =
  | Pos of int
  | Neg of int

  (** val eqb : t -> t -> bool **)

  let eqb l1 l2 =
    match l1 with
    | Pos u -> (match l2 with
                | Pos v -> (=) u v
                | Neg _ -> false)
    | Neg u -> (match l2 with
                | Pos _ -> false
                | Neg v -> (=) u v)
 end

module Clause =
 struct
  type t = Literal.t list

  (** val mem : t -> Literal.t -> bool **)

  let mem c l =
    existsb (Literal.eqb l) c

  (** val sub_clause : t -> t -> bool **)

  let sub_clause c1 c2 =
    forallb (mem c2) c1

  (** val eqb : t -> t -> bool **)

  let eqb c1 c2 =
    (&&) (sub_clause c1 c2) (sub_clause c2 c1)
 end

module ClauseSet =
 struct
  type t = Clause.t list

  (** val mem : t -> Clause.t -> bool **)

  let mem cs c =
    existsb (Clause.eqb c) cs
 end

type proof_step =
| Proof_mem of Clause.t
| Proof_cut of int * Clause.t * Clause.t

(** val conclusion : proof_step -> Clause.t **)

let conclusion = function
| Proof_mem c -> c
| Proof_cut (_, c1, c2) -> app c1 c2

(** val is_proof_step : ClauseSet.t -> proof_step -> bool **)

let is_proof_step context = function
| Proof_mem c -> ClauseSet.mem context c
| Proof_cut (l, c1, c2) ->
  (&&) (ClauseSet.mem context ((Literal.Neg l) :: c1))
    (ClauseSet.mem context ((Literal.Pos l) :: c2))

(** val is_proof : ClauseSet.t -> proof_step list -> Clause.t -> bool **)

let rec is_proof context proof c =
  match proof with
  | [] -> ClauseSet.mem context c
  | ps :: proof0 ->
    (&&) (is_proof_step context ps)
      (is_proof ((conclusion ps) :: context) proof0 c)
