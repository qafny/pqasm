open Bool
open PeanoNat

type var = int

type posi = var * int

(** val posi_eq : posi -> posi -> bool **)

let posi_eq r1 r2 =
  let (x1, y1) = r1 in
  let (x2, y2) = r2 in (&&) (Nat.eqb x1 x2) (Nat.eqb y1 y2)

(** val posi_eq_reflect : posi -> posi -> reflect **)

let posi_eq_reflect r1 r2 =
  let b = posi_eq r1 r2 in if b then ReflectT else ReflectF

(** val posi_eq_dec : posi -> posi -> bool **)

let posi_eq_dec x y =
  let h = posi_eq_reflect x y in
  (match h with
   | ReflectT -> true
   | ReflectF -> false)

type rz_val = int -> bool

(** val eupdate : (posi -> 'a1) -> posi -> 'a1 -> posi -> 'a1 **)

let eupdate f i x j =
  if posi_eq j i then x else f j
