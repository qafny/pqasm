open PeanoNat

(** val update : (int -> 'a1) -> int -> 'a1 -> int -> 'a1 **)

let update f i x j =
  if Nat.eqb j i then x else f j
