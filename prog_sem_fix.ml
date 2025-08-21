
type bool =
| True
| False

(** val xorb :
    bool -> bool -> bool **)

let xorb b1 b2 =
  match b1 with
  | True ->
    (match b2 with
     | True -> False
     | False -> True)
  | False -> b2

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst :
    ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd :
    ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length :
    'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val app :
    'a1 list -> 'a1 list -> 'a1
    list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) ->
    Cons (a, (app l1 m))

type sumbool =
| Left
| Right

(** val add :
    nat -> nat -> nat **)

let rec add n0 m =
  match n0 with
  | O -> m
  | S p -> S (add p m)

(** val mul :
    nat -> nat -> nat **)

let rec mul n0 m =
  match n0 with
  | O -> O
  | S p -> add m (mul p m)

(** val sub :
    nat -> nat -> nat **)

let rec sub n0 m =
  match n0 with
  | O -> n0
  | S k ->
    (match m with
     | O -> n0
     | S l -> sub k l)

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type reflect =
| ReflectT
| ReflectF

module Nat =
 struct
  (** val add :
      nat -> nat -> nat **)

  let rec add n0 m =
    match n0 with
    | O -> m
    | S p -> S (add p m)

  (** val mul :
      nat -> nat -> nat **)

  let rec mul n0 m =
    match n0 with
    | O -> O
    | S p -> add m (mul p m)

  (** val sub :
      nat -> nat -> nat **)

  let rec sub n0 m =
    match n0 with
    | O -> n0
    | S k ->
      (match m with
       | O -> n0
       | S l -> sub k l)

  (** val eqb :
      nat -> nat -> bool **)

  let rec eqb n0 m =
    match n0 with
    | O ->
      (match m with
       | O -> True
       | S _ -> False)
    | S n' ->
      (match m with
       | O -> False
       | S m' -> eqb n' m')

  (** val leb :
      nat -> nat -> bool **)

  let rec leb n0 m =
    match n0 with
    | O -> True
    | S n' ->
      (match m with
       | O -> False
       | S m' -> leb n' m')

  (** val ltb :
      nat -> nat -> bool **)

  let ltb n0 m =
    leb (S n0) m

  (** val pow :
      nat -> nat -> nat **)

  let rec pow n0 = function
  | O -> S O
  | S m0 -> mul n0 (pow n0 m0)

  (** val divmod :
      nat -> nat -> nat -> nat
      -> (nat, nat) prod **)

  let rec divmod x y q u =
    match x with
    | O -> Pair (q, u)
    | S x' ->
      (match u with
       | O ->
         divmod x' y (S q) y
       | S u' ->
         divmod x' y q u')

  (** val modulo :
      nat -> nat -> nat **)

  let modulo x = function
  | O -> x
  | S y' ->
    sub y'
      (snd (divmod x y' O y'))

  (** val b2n : bool -> nat **)

  let b2n = function
  | True -> S O
  | False -> O
 end

module Pos =
 struct
  (** val succ :
      positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val of_succ_nat :
      nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module N =
 struct
  (** val of_nat : nat -> n **)

  let of_nat = function
  | O -> N0
  | S n' ->
    Npos (Pos.of_succ_nat n')
 end

(** val update :
    (nat -> 'a1) -> nat -> 'a1
    -> nat -> 'a1 **)

let update f i x j =
  match Nat.eqb j i with
  | True -> x
  | False -> f j

type var = nat

type posi = (var, nat) prod

(** val posi_eq :
    posi -> posi -> bool **)

let posi_eq r1 r2 =
  let Pair (x1, y1) = r1 in
  let Pair (x2, y2) = r2 in
  (match Nat.eqb x1 x2 with
   | True -> Nat.eqb y1 y2
   | False -> False)

(** val posi_eq_reflect :
    posi -> posi -> reflect **)

let posi_eq_reflect r1 r2 =
  let b = posi_eq r1 r2 in
  (match b with
   | True -> ReflectT
   | False -> ReflectF)

(** val posi_eq_dec :
    posi -> posi -> sumbool **)

let posi_eq_dec x y =
  let h = posi_eq_reflect x y in
  (match h with
   | ReflectT -> Left
   | ReflectF -> Right)

(** val eupdate :
    (posi -> 'a1) -> posi ->
    'a1 -> posi -> 'a1 **)

let eupdate f i x j =
  match posi_eq j i with
  | True -> x
  | False -> f j

(** val allfalse :
    nat -> bool **)

let allfalse _ =
  False

(** val fb_push :
    bool -> (nat -> bool) ->
    nat -> bool **)

let fb_push b f = function
| O -> b
| S n0 -> f n0

(** val pos2fb :
    positive -> nat -> bool **)

let rec pos2fb = function
| XI p' ->
  fb_push True (pos2fb p')
| XO p' ->
  fb_push False (pos2fb p')
| XH -> fb_push True allfalse

(** val n2fb :
    n -> nat -> bool **)

let n2fb = function
| N0 -> allfalse
| Npos p -> pos2fb p

(** val nat2fb :
    nat -> nat -> bool **)

let nat2fb n0 =
  n2fb (N.of_nat n0)

(** val carry :
    bool -> nat -> (nat ->
    bool) -> (nat -> bool) ->
    bool **)

let rec carry b n0 f g =
  match n0 with
  | O -> b
  | S n' ->
    let c = carry b n' f g in
    let a = f n' in
    let b0 = g n' in
    xorb
      (xorb
        (match a with
         | True -> b0
         | False -> False)
        (match b0 with
         | True -> c
         | False -> False))
      (match a with
       | True -> c
       | False -> False)

(** val sumfb :
    bool -> (nat -> bool) ->
    (nat -> bool) -> nat -> bool **)

let sumfb b f g x =
  xorb
    (xorb (carry b x f g) (f x))
    (g x)

(** val natsum :
    nat -> (nat -> nat) -> nat **)

let rec natsum n0 f =
  match n0 with
  | O -> O
  | S n' ->
    add (f n') (natsum n' f)

(** val a_nat2fb :
    (nat -> bool) -> nat -> nat **)

let a_nat2fb f n0 =
  natsum n0 (fun i ->
    mul (Nat.b2n (f i))
      (Nat.pow (S (S O)) i))

type 'a set = 'a list

(** val set_add :
    ('a1 -> 'a1 -> sumbool) ->
    'a1 -> 'a1 set -> 'a1 set **)

let rec set_add aeq_dec a = function
| Nil -> Cons (a, Nil)
| Cons (a1, x1) ->
  (match aeq_dec a a1 with
   | Left -> Cons (a1, x1)
   | Right ->
     Cons (a1,
       (set_add aeq_dec a x1)))

(** val set_mem :
    ('a1 -> 'a1 -> sumbool) ->
    'a1 -> 'a1 set -> bool **)

let rec set_mem aeq_dec a = function
| Nil -> False
| Cons (a1, x1) ->
  (match aeq_dec a a1 with
   | Left -> True
   | Right ->
     set_mem aeq_dec a x1)

(** val set_diff :
    ('a1 -> 'a1 -> sumbool) ->
    'a1 set -> 'a1 set -> 'a1
    set **)

let rec set_diff aeq_dec x y =
  match x with
  | Nil -> Nil
  | Cons (a1, x1) ->
    (match set_mem aeq_dec a1 y with
     | True ->
       set_diff aeq_dec x1 y
     | False ->
       set_add aeq_dec a1
         (set_diff aeq_dec x1 y))

type aexp =
| BA of var
| Num of nat
| APlus of aexp * aexp
| AMult of aexp * aexp

type cbexp =
| CEq of aexp * aexp
| CLt of aexp * aexp

type rz_val_PQASM = nat

type mu =
| Add of posi list * nat
| Less of posi list * nat * posi
| Equal of posi list * 
   nat * posi
| ModMult of posi list * 
   nat * nat
| Equal_posi_list of posi list
   * posi list * posi

type iota =
| ISeq of iota * iota
| ICU of posi * iota
| Ora of mu
| Ry of posi * rz_val_PQASM

type exp =
| ESKIP
| Next of iota
| Had of posi list
| New of posi list
| ESeq of exp * exp
| Meas of var * posi list * exp
| IFa of cbexp * exp * exp

type basis_val =
| Nval of bool
| Rval of nat

type eta_state =
  posi -> basis_val

(** val pi32 : nat -> nat **)

let pi32 rmax =
  add
    (Nat.pow (S (S O))
      (sub rmax (S O)))
    (Nat.pow (S (S O))
      (sub rmax (S (S O))))

(** val angle_sum :
    rz_val_PQASM ->
    rz_val_PQASM -> nat -> nat **)

let angle_sum f g rmax =
  Nat.modulo (add f g)
    (Nat.pow (S (S O)) rmax)

(** val angle_sub :
    rz_val_PQASM ->
    rz_val_PQASM -> nat -> nat **)

let angle_sub f g rmax =
  match Nat.ltb f g with
  | True ->
    sub
      (Nat.pow (S (S O)) rmax)
      (sub g f)
  | False -> sub f g

(** val ry_rotate :
    eta_state -> posi ->
    rz_val_PQASM -> nat ->
    eta_state **)

let ry_rotate st p r rmax =
  match st p with
  | Nval b2 ->
    (match b2 with
     | True ->
       eupdate st p (Rval
         (angle_sub (pi32 rmax)
           r rmax))
     | False ->
       eupdate st p (Rval r))
  | Rval r1 ->
    eupdate st p (Rval
      (angle_sum r1 r rmax))

(** val set_diff_posi :
    posi set -> posi set ->
    posi set **)

let set_diff_posi =
  set_diff posi_eq_dec

(** val posi_list_to_bitstring_helper :
    posi list -> eta_state ->
    nat -> nat -> bool **)

let rec posi_list_to_bitstring_helper ps st n0 =
  match ps with
  | Nil -> allfalse
  | Cons (x, xs) ->
    (fun k ->
      match st x with
      | Nval b ->
        (match Nat.eqb k n0 with
         | True -> b
         | False ->
           posi_list_to_bitstring_helper
             xs st
             (add n0 (S O)) k)
      | Rval _ ->
        (match Nat.eqb k n0 with
         | True -> False
         | False ->
           posi_list_to_bitstring_helper
             xs st
             (add n0 (S O)) k))

(** val posi_list_to_bitstring :
    posi list -> eta_state ->
    nat -> bool **)

let posi_list_to_bitstring ps st =
  posi_list_to_bitstring_helper
    ps st O

(** val mu_addition :
    posi list -> nat ->
    eta_state -> nat -> bool **)

let mu_addition ps n0 st =
  sumfb False
    (posi_list_to_bitstring ps
      st) (nat2fb n0)

(** val mu_less :
    posi list -> nat ->
    eta_state -> posi -> posi
    -> basis_val **)

let mu_less ps n0 st q =
  match st q with
  | Nval j ->
    eupdate st q (Nval
      (xorb j
        (Nat.ltb
          (a_nat2fb
            (posi_list_to_bitstring
              ps st)
            (length ps)) n0)))
  | Rval _ -> st

(** val mu_eq :
    posi list -> nat ->
    eta_state -> posi -> posi
    -> basis_val **)

let mu_eq ps n0 st q =
  match st q with
  | Nval j ->
    eupdate st q (Nval
      (xorb j
        (Nat.eqb
          (a_nat2fb
            (posi_list_to_bitstring
              ps st)
            (length ps)) n0)))
  | Rval _ -> st

(** val mu_full_eq :
    posi list -> posi list ->
    eta_state -> posi -> posi
    -> basis_val **)

let mu_full_eq ps qs st q =
  match st q with
  | Nval j ->
    eupdate st q (Nval
      (xorb j
        (Nat.eqb
          (a_nat2fb
            (posi_list_to_bitstring
              ps st)
            (length ps))
          (a_nat2fb
            (posi_list_to_bitstring
              qs st)
            (length qs)))))
  | Rval _ -> st

(** val bitstring_to_eta' :
    eta_state -> posi list ->
    (nat -> bool) -> nat ->
    eta_state **)

let rec bitstring_to_eta' st l f n0 =
  match l with
  | Nil -> st
  | Cons (p, ps) ->
    eupdate
      (bitstring_to_eta' st ps
        f (add n0 (S O))) p
      (Nval (f n0))

(** val bitstring_to_eta :
    eta_state -> posi list ->
    (nat -> bool) -> eta_state **)

let bitstring_to_eta st l f =
  bitstring_to_eta' st l f O

(** val modmult :
    eta_state -> posi list ->
    nat -> nat -> eta_state **)

let modmult st ps c n0 =
  bitstring_to_eta st ps
    (nat2fb
      (Nat.modulo
        (mul c
          (a_nat2fb
            (posi_list_to_bitstring
              ps st)
            (length ps))) n0))

(** val mu_handling :
    nat -> mu -> eta_state ->
    eta_state **)

let mu_handling _ m st =
  match m with
  | Add (ps, n0) ->
    bitstring_to_eta st ps
      (mu_addition ps n0 st)
  | Less (ps, n0, p) ->
    mu_less ps n0 st p
  | Equal (ps, n0, p) ->
    mu_eq ps n0 st p
  | ModMult (ps, n0, m0) ->
    modmult st ps n0 m0
  | Equal_posi_list (ps, qs, p) ->
    mu_full_eq ps qs st p

(** val instr_sem :
    nat -> iota -> eta_state ->
    eta_state **)

let rec instr_sem rmax e st =
  match e with
  | ISeq (a, b) ->
    instr_sem rmax b
      (instr_sem rmax a st)
  | ICU (x, y) ->
    (match st x with
     | Nval j ->
       (match j with
        | True ->
          instr_sem rmax y st
        | False -> st)
     | Rval _ -> st)
  | Ora m ->
    mu_handling rmax m st
  | Ry (p, r) ->
    ry_rotate st p r rmax

(** val eval_aexp :
    (var -> nat) -> aexp -> nat **)

let rec eval_aexp env = function
| BA x -> env x
| Num n0 -> n0
| APlus (e1, e2) ->
  add (eval_aexp env e1)
    (eval_aexp env e2)
| AMult (e1, e2) ->
  mul (eval_aexp env e1)
    (eval_aexp env e2)

(** val eval_bexp :
    (var -> nat) -> cbexp ->
    bool **)

let eval_bexp env = function
| CEq (a, b) ->
  Nat.eqb (eval_aexp env a)
    (eval_aexp env b)
| CLt (a, b) ->
  Nat.ltb (eval_aexp env a)
    (eval_aexp env b)

type tstate =
  (posi list, eta_state) prod

type fstate =
  (var -> nat, tstate) prod

(** val new_env :
    var -> posi list -> fstate
    -> nat -> nat **)

let new_env x qs st =
  update (fst st) x
    (a_nat2fb
      (posi_list_to_bitstring
        qs (snd (snd st)))
      (length qs))

(** val add_list :
    posi list -> fstate -> (var
    -> nat, (posi list,
    eta_state) prod) prod **)

let add_list qs st =
  Pair ((fst st), (Pair
    ((app qs (fst (snd st))),
    (snd (snd st)))))

(** val prog_sem_fix :
    nat -> exp -> fstate ->
    fstate **)

let rec prog_sem_fix rmax e st =
  match e with
  | Next p ->
    Pair ((fst st), (Pair
      ((fst (snd st)),
      (instr_sem rmax p
        (snd (snd st))))))
  | New b -> add_list b st
  | ESeq (k, m) ->
    prog_sem_fix rmax m
      (prog_sem_fix rmax k st)
  | Meas (x, qs, e1) ->
    prog_sem_fix rmax e1 (Pair
      ((new_env x qs st), (Pair
      ((set_diff_posi
         (fst (snd st)) qs),
      (snd (snd st))))))
  | IFa (k, op1, op2) ->
    (match eval_bexp (fst st) k with
     | True ->
       prog_sem_fix rmax op1 st
     | False ->
       prog_sem_fix rmax op2 st)
  | _ -> st
