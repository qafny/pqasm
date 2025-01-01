
type 'a set = 'a list

(** val set_add : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set **)

let rec set_add aeq_dec a = function
| [] -> a :: []
| a1 :: x1 -> if aeq_dec a a1 then a1 :: x1 else a1 :: (set_add aeq_dec a x1)

(** val set_mem : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> bool **)

let rec set_mem aeq_dec a = function
| [] -> false
| a1 :: x1 -> if aeq_dec a a1 then true else set_mem aeq_dec a x1

(** val set_diff : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_diff aeq_dec x y =
  match x with
  | [] -> []
  | a1 :: x1 ->
    if set_mem aeq_dec a1 y
    then set_diff aeq_dec x1 y
    else set_add aeq_dec a1 (set_diff aeq_dec x1 y)
