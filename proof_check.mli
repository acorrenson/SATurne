
val app : 'a1 list -> 'a1 list -> 'a1 list

module Nat :
 sig
 end

val forallb : ('a1 -> bool) -> 'a1 list -> bool

module Literal :
 sig
  type t =
  | Pos of int
  | Neg of int

  val eqb : t -> t -> bool
 end

module Clause :
 sig
  type t = Literal.t list

  val mem : t -> Literal.t -> bool

  val sub_clause : t -> t -> bool

  val eqb : t -> t -> bool
 end

module ClauseSet :
 sig
  type t = Clause.t list

  val mem : t -> Clause.t -> bool
 end

type proof_step =
| Proof_mem of Clause.t
| Proof_cut of int * Clause.t * Clause.t

val conclusion : proof_step -> Clause.t

val is_proof_step : ClauseSet.t -> proof_step -> bool

val is_proof : ClauseSet.t -> proof_step list -> Clause.t -> bool
