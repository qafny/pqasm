open Datatypes
open PeanoNat

module Nat_as_OT =
 struct
  type t = int

  (** val compare : int -> int -> int OrderedType.coq_Compare **)

  let compare x y =
    match Nat.compare x y with
    | Eq -> OrderedType.EQ
    | Lt -> OrderedType.LT
    | Gt -> OrderedType.GT

  (** val eq_dec : int -> int -> bool **)

  let eq_dec =
    (=)
 end

module PairOrderedType =
 functor (O1:OrderedType.OrderedType) ->
 functor (O2:OrderedType.OrderedType) ->
 struct
  module MO1 = OrderedType.OrderedTypeFacts(O1)

  module MO2 = OrderedType.OrderedTypeFacts(O2)

  type t = O1.t * O2.t

  (** val compare : t -> t -> (O1.t * O2.t) OrderedType.coq_Compare **)

  let compare x y =
    let (a, b) = x in
    let (a0, b0) = y in
    let c = O1.compare a a0 in
    (match c with
     | OrderedType.LT -> OrderedType.LT
     | OrderedType.EQ ->
       let c0 = O2.compare b b0 in
       (match c0 with
        | OrderedType.LT -> OrderedType.LT
        | OrderedType.EQ -> OrderedType.EQ
        | OrderedType.GT -> OrderedType.GT)
     | OrderedType.GT -> OrderedType.GT)

  (** val eq_dec : t -> t -> bool **)

  let eq_dec x y =
    match compare x y with
    | OrderedType.EQ -> true
    | _ -> false
 end
