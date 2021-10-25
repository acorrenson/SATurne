
(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

module Nat =
 struct
 end

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

  let rec mem c l =
    match c with
    | [] -> false
    | l' :: ls -> if Literal.eqb l l' then true else mem ls l

  (** val sub_clause : t -> t -> bool **)

  let sub_clause c1 c2 =
    forallb (mem c1) c2

  (** val eqb : t -> t -> bool **)

  let eqb c1 c2 =
    (&&) (sub_clause c1 c2) (sub_clause c2 c1)
 end

module ClauseSet =
 struct
  type t = Clause.t list

  (** val mem : t -> Clause.t -> bool **)

  let rec mem cs c =
    match cs with
    | [] -> false
    | c' :: cs' -> if Clause.eqb c c' then true else mem cs' c
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

let rec is_proof context uts c =
  match uts with
  | [] -> ClauseSet.mem context c
  | ut :: uts0 ->
    (&&) (is_proof_step context ut)
      (is_proof ((conclusion ut) :: context) uts0 c)
