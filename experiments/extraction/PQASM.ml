open BasicUtility
open BinNat
open Datatypes
open ListSet
open MathSpec
open PeanoNat
open VectorStates

type aexp =
| BA of var
| Num of int
| APlus of aexp * aexp
| AMult of aexp * aexp

type cbexp =
| CEq of aexp * aexp
| CLt of aexp * aexp

type mu =
| Add of posi list * (int -> bool)
| Less of posi list * (int -> bool) * posi
| Equal of posi list * (int -> bool) * posi
| ModMult of posi list * (int -> bool) * (int -> bool)

type iota =
| ISeq of iota * iota
| ICU of posi * iota
| Ora of mu
| Ry of posi * rz_val

type exp =
| ESKIP
| Next of iota
| Had of posi list
| New of posi list
| ESeq of exp * exp
| Meas of var * posi list * exp
| IFa of cbexp * exp * exp

(** val x_var : var **)

let x_var =
  0

(** val y_var : var **)

let y_var =
  succ 0

(** val z_var : var **)

let z_var =
  succ (succ 0)

(** val lst_posi : int -> var -> (var * int) list **)

let rec lst_posi n x =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> [])
    (fun m -> (x, m) :: (lst_posi m x))
    n

(** val uniform_state : int -> int -> exp -> exp **)

let uniform_state n m p =
  ESeq ((ESeq ((ESeq ((ESeq ((New (lst_posi n x_var)), (New ((y_var,
    0) :: [])))), (Had (lst_posi n x_var)))), (Next (Ora (Less
    ((lst_posi n x_var), (nat2fb m), (y_var, 0))))))), (Meas (z_var,
    (lst_posi n x_var), (IFa ((CEq ((BA z_var), (Num (succ 0)))), ESKIP,
    p)))))

type basis_val =
| Nval of bool
| Rval of rz_val

type eta_state = posi -> basis_val

(** val pi32 : int -> bool **)

let pi32 =
  update (update allfalse 0 true) (succ 0) true

(** val angle_sum : rz_val -> rz_val -> int -> int -> bool **)

let angle_sum f g rmax =
  cut_n (sumfb false f g) rmax

(** val angle_sub : rz_val -> rz_val -> int -> int -> bool **)

let angle_sub f g rmax =
  cut_n (sumfb false f (negatem rmax g)) rmax

(** val ry_rotate : eta_state -> posi -> rz_val -> int -> eta_state **)

let ry_rotate st p r rmax =
  match st p with
  | Nval b2 ->
    if b2
    then eupdate st p (Rval (angle_sub pi32 r rmax))
    else eupdate st p (Rval r)
  | Rval r1 -> eupdate st p (Rval (angle_sum r1 r rmax))

(** val set_diff_posi : posi set -> posi set -> posi set **)

let set_diff_posi =
  set_diff posi_eq_dec

(** val posi_list_to_bitstring_helper :
    posi list -> eta_state -> int -> int -> bool **)

let rec posi_list_to_bitstring_helper ps st n k =
  match ps with
  | [] -> false
  | a :: b ->
    if Nat.eqb k n
    then (match st a with
          | Nval b0 -> b0
          | Rval _ -> false)
    else posi_list_to_bitstring_helper b st n k

(** val posi_list_to_bitstring : posi list -> eta_state -> int -> bool **)

let posi_list_to_bitstring ps st =
  posi_list_to_bitstring_helper ps st 0

(** val mu_addition :
    posi list -> (int -> bool) -> eta_state -> int -> bool **)

let mu_addition ps n st =
  sumfb false (posi_list_to_bitstring ps st) n

(** val mu_less_helper :
    posi list -> (int -> bool) -> eta_state -> int -> bool **)

let rec mu_less_helper ps bitstring st n =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> false)
    (fun k ->
    match ps with
    | [] -> false
    | a :: b ->
      (match st a with
       | Nval j ->
         if (&&) (bitstring n) j
         then mu_less_helper b bitstring st k
         else bitstring n
       | Rval _ -> false))
    n

(** val mu_less : posi list -> (int -> bool) -> eta_state -> bool **)

let mu_less ps n st =
  mu_less_helper (List.rev ps) n st (length ps)

(** val mu_eq_helper :
    posi list -> (int -> bool) -> eta_state -> int -> bool **)

let rec mu_eq_helper ps bitstring st n =
  (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
    (fun _ -> false)
    (fun k ->
    match ps with
    | [] -> true
    | a :: b ->
      (match st a with
       | Nval j ->
         if (&&) (bitstring n) j then mu_eq_helper b bitstring st k else false
       | Rval _ -> false))
    n

(** val mu_eq : posi list -> (int -> bool) -> eta_state -> bool **)

let mu_eq ps n st =
  mu_eq_helper (List.rev ps) n st (length ps)

(** val bitstring_to_eta : (int -> bool) -> posi list -> int -> eta_state **)

let rec bitstring_to_eta f l size posi0 =
  match l with
  | [] -> Nval false
  | x :: xs ->
    if posi_eq x posi0
    then Nval (f ((fun x y -> max 0 (x-y)) size (length (x :: xs))))
    else bitstring_to_eta f xs size posi0

(** val mu_handling : int -> mu -> eta_state -> eta_state **)

let mu_handling rmax m st =
  match m with
  | Add (ps, n) -> bitstring_to_eta (mu_addition ps n st) ps (length ps)
  | Less (ps, n, p) -> eupdate st p (Nval (mu_less ps n st))
  | Equal (ps, n, p) -> eupdate st p (Nval (mu_eq ps n st))
  | ModMult (ps, n, m0) ->
    bitstring_to_eta
      (nat2fb
        (Nat.modulo
          (( * ) (a_nat2fb (posi_list_to_bitstring ps st) rmax)
            (a_nat2fb n rmax)) (a_nat2fb m0 rmax))) ps (length ps)

(** val instr_sem : int -> iota -> eta_state -> eta_state **)

let rec instr_sem rmax e st =
  match e with
  | ISeq (a, b) -> instr_sem rmax b (instr_sem rmax a st)
  | ICU (x, y) ->
    (match st x with
     | Nval j -> if j then instr_sem rmax y st else st
     | Rval _ -> st)
  | Ora m -> mu_handling rmax m st
  | Ry (p, r) -> ry_rotate st p r rmax

(** val eval_aexp : (var -> int) -> aexp -> int **)

let rec eval_aexp env = function
| BA x -> env x
| Num n -> n
| APlus (e1, e2) -> (+) (eval_aexp env e1) (eval_aexp env e2)
| AMult (e1, e2) -> ( * ) (eval_aexp env e1) (eval_aexp env e2)

(** val eval_bexp : (var -> int) -> cbexp -> bool **)

let eval_bexp env = function
| CEq (a, b) -> Nat.eqb (eval_aexp env a) (eval_aexp env b)
| CLt (a, b) -> Nat.ltb (eval_aexp env a) (eval_aexp env b)

type tstate = posi list * eta_state

type fstate = (var -> int) * tstate

(** val new_env : var -> posi list -> fstate -> int -> int **)

let new_env x qs st b =
  if Nat.eqb b x
  then a_nat2fb (posi_list_to_bitstring qs (snd (snd st))) (length qs)
  else fst st b

(** val prog_sem_fix : int -> exp -> fstate -> fstate **)

let rec prog_sem_fix rmax e st =
  match e with
  | Next p -> ((fst st), ((fst (snd st)), (instr_sem rmax p (snd (snd st)))))
  | ESeq (k, m) -> prog_sem_fix rmax k (prog_sem_fix rmax m st)
  | Meas (x, qs, e1) ->
    prog_sem_fix rmax e1 ((new_env x qs st),
      ((set_diff_posi (fst (snd st)) qs), (snd (snd st))))
  | IFa (k, op1, op2) ->
    if eval_bexp (fst st) k
    then prog_sem_fix rmax op1 st
    else prog_sem_fix rmax op2 st
  | _ -> st

(** val bv2Eta : int -> var -> int -> eta_state **)

let bv2Eta n x l p =
  if (&&) (Nat.ltb (snd p) n) (Nat.eqb (fst p) x)
  then Nval (N.testbit_nat l (snd p))
  else Nval false

(** val bool_to_nat : bool -> int **)

let bool_to_nat = function
| true -> succ 0
| false -> 0

module Hamming =
 struct
  (** val state_qubits : int **)

  let state_qubits =
    succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ 0)))))))))))))))))))

  (** val hamming_qubits : int **)

  let hamming_qubits =
    succ (succ (succ (succ (succ (succ 0)))))

  (** val target_hamming_w : int **)

  let target_hamming_w =
    succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ 0))))))))))))))))

  (** val cvars : var list **)

  let cvars =
    z_var :: []

  (** val qvars : posi list **)

  let qvars =
    lst_posi state_qubits x_var

  (** val init_env : var -> int **)

  let init_env _ =
    0

  (** val init_st : eta_state **)

  let init_st _ =
    Nval false

  (** val repeat : posi list -> (posi -> exp) -> exp **)

  let rec repeat reg p =
    match reg with
    | [] -> ESKIP
    | p0 :: r -> ESeq ((p p0), (repeat r p))

  (** val hamming_weight_of_bitstring : int -> (int -> bool) -> int **)

  let rec hamming_weight_of_bitstring n bs =
    (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
      (fun _ -> 0)
      (fun m -> (+) (bool_to_nat (bs n)) (hamming_weight_of_bitstring m bs))
      n

  (** val hamming_state : int -> int -> int -> exp **)

  let hamming_state n h_n w =
    ESeq ((ESeq ((ESeq ((ESeq ((New (lst_posi n x_var)), (New
      (lst_posi h_n y_var)))), (Had (lst_posi n x_var)))),
      (repeat (lst_posi n x_var) (fun p -> Next (ICU (p, (Ora (Add
        ((lst_posi h_n y_var), (nat2fb (succ 0))))))))))), (Meas (z_var,
      (lst_posi h_n y_var), (IFa ((CEq ((BA z_var), (Num w))), ESKIP,
      ESKIP)))))

  (** val hamming_test_eq : exp -> int -> bool **)

  let hamming_test_eq e v =
    let (env, qstate) =
      prog_sem_fix state_qubits e (init_env, (qvars,
        (bv2Eta state_qubits x_var v)))
    in
    if Nat.eqb (env z_var) target_hamming_w
    then Nat.eqb
           (hamming_weight_of_bitstring state_qubits
             (posi_list_to_bitstring (fst qstate) (snd qstate)))
           target_hamming_w
    else true
 end

module SumState =
 struct
  (** val num_reg_test : int **)

  let num_reg_test =
    succ (succ (succ 0))

  (** val reg_size_test : int **)

  let reg_size_test =
    succ (succ (succ (succ 0)))

  (** val k_test : int **)

  let k_test =
    succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ 0)))))))))))))))))))

  (** val cvars : var list **)

  let cvars =
    z_var :: []

  (** val qvars : posi list **)

  let qvars =
    lst_posi (( * ) num_reg_test reg_size_test) x_var

  (** val init_env : var -> int **)

  let init_env _ =
    0

  (** val repeat : posi list -> (posi -> exp) -> exp **)

  let rec repeat reg p =
    match reg with
    | [] -> ESKIP
    | p0 :: r -> ESeq ((p p0), (repeat r p))

  (** val repeat_ind : posi list -> int -> (posi -> int -> exp) -> exp **)

  let rec repeat_ind reg index p =
    match reg with
    | [] -> ESKIP
    | p0 :: r ->
      ESeq ((p p0 index),
        (repeat_ind r ((fun x y -> max 0 (x-y)) index (succ 0)) p))

  (** val lst_var : int -> var -> var list **)

  let rec lst_var len start_var =
    (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
      (fun _ -> [])
      (fun len_m -> ((+) len_m start_var) :: (lst_var len_m start_var))
      len

  (** val repeat_reg : (posi list -> exp) -> var list -> int -> exp **)

  let rec repeat_reg p regs reg_size =
    match regs with
    | [] -> ESKIP
    | r :: rs -> ESeq ((p (lst_posi reg_size r)), (repeat_reg p rs reg_size))

  (** val pow_2 : int -> int **)

  let rec pow_2 n =
    (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
      (fun _ -> succ 0)
      (fun m -> ( * ) (succ (succ 0)) (pow_2 m))
      n

  (** val sum_state : int -> int -> int -> exp **)

  let sum_state num_reg reg_size target_sum =
    let prep_list = lst_var num_reg x_var in
    let sum_var = (+) x_var num_reg in
    ESeq ((ESeq ((ESeq ((repeat_reg (fun x -> New x) prep_list reg_size),
    (New (lst_posi ((+) reg_size num_reg) sum_var)))),
    (repeat_reg (fun lp ->
      repeat_ind lp reg_size (fun p index -> Next (ICU (p, (Ora (Add
        ((lst_posi ((+) reg_size num_reg) sum_var),
        (nat2fb (pow_2 index))))))))) prep_list reg_size))), (Meas (z_var,
    (lst_posi ((+) reg_size num_reg) sum_var), (IFa ((CEq ((BA z_var), (Num
    target_sum))), ESKIP, ESKIP)))))

  (** val bitstring_slice : int -> int -> int -> (int -> bool) -> int **)

  let rec bitstring_slice reg reg_size ind bs =
    (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
      (fun _ -> 0)
      (fun m ->
      (+) (( * ) (bitstring_slice reg reg_size m bs) (succ (succ 0)))
        (bool_to_nat
          (bs
            ((+) (( * ) ((fun x y -> max 0 (x-y)) reg (succ 0)) reg_size)
              ((fun x y -> max 0 (x-y)) ind (succ 0))))))
      ind

  (** val sum_of_bitstring : int -> int -> (int -> bool) -> int **)

  let rec sum_of_bitstring n reg_size bs =
    (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
      (fun _ -> 0)
      (fun m ->
      (+) (bitstring_slice n reg_size reg_size bs)
        (sum_of_bitstring m reg_size bs))
      n

  (** val sum_test_eq : exp -> int -> bool **)

  let sum_test_eq e v =
    let state_qubits0 = ( * ) num_reg_test reg_size_test in
    let (env, qstate) =
      prog_sem_fix state_qubits0 e (init_env, (qvars,
        (bv2Eta state_qubits0 x_var v)))
    in
    if Nat.eqb (env z_var) k_test
    then Nat.eqb
           (sum_of_bitstring num_reg_test reg_size_test
             (posi_list_to_bitstring (fst qstate) (snd qstate))) k_test
    else true
 end

module ModExpState =
 struct
  (** val c_test : int **)

  let c_test =
    succ (succ (succ 0))

  (** val coq_N_test : int **)

  let coq_N_test =
    succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
      0)))))))))))))))))))))))))))))))))

  (** val num_qubits_test : int **)

  let num_qubits_test =
    succ (succ (succ (succ (succ (succ (succ (succ 0)))))))

  (** val num_exp_qubits_test : int **)

  let num_exp_qubits_test =
    succ (succ (succ (succ (succ (succ (succ 0))))))

  (** val init_env : var -> int **)

  let init_env _ =
    0

  (** val qvars : posi list **)

  let qvars =
    lst_posi num_qubits_test x_var

  (** val mod_pow : int -> int -> int -> int -> int **)

  let rec mod_pow c n m max_iter =
    (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
      (fun _ -> Nat.modulo (succ 0) m)
      (fun l ->
      if Nat.eqb n 0
      then succ 0
      else let u = mod_pow c (Nat.div n (succ (succ 0))) m l in
           if Nat.eqb (Nat.modulo n (succ (succ 0))) 0
           then Nat.modulo (( * ) u u) m
           else Nat.modulo (( * ) (Nat.modulo (( * ) u u) m) c) m)
      max_iter

  (** val pow : int -> int -> int **)

  let rec pow c n =
    (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
      (fun _ -> succ 0)
      (fun m -> ( * ) c (pow c m))
      n

  (** val repeat : posi list -> (posi -> exp) -> exp **)

  let rec repeat reg p =
    match reg with
    | [] -> ESKIP
    | p0 :: r -> ESeq ((p p0), (repeat r p))

  (** val repeat_ind : posi list -> int -> (posi -> int -> exp) -> exp **)

  let rec repeat_ind reg index p =
    match reg with
    | [] -> ESKIP
    | p0 :: r ->
      ESeq ((repeat_ind r ((fun x y -> max 0 (x-y)) index (succ 0)) p),
        (p p0 index))

  (** val fst_reg : int -> (int -> bool) -> int **)

  let rec fst_reg reg_1_size bs =
    (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
      (fun _ -> 0)
      (fun m ->
      (+) (( * ) (fst_reg m bs) (succ (succ 0)))
        (bool_to_nat (bs ((fun x y -> max 0 (x-y)) reg_1_size (succ 0)))))
      reg_1_size

  (** val snd_reg : int -> int -> (int -> bool) -> int **)

  let rec snd_reg reg_1_size reg_2_size bs =
    (fun fO fS n -> if n=0 then fO () else fS (max 0 (n-1)))
      (fun _ -> 0)
      (fun m ->
      (+) (( * ) (snd_reg reg_1_size m bs) (succ (succ 0)))
        (bool_to_nat
          (bs ((fun x y -> max 0 (x-y)) ((+) reg_1_size reg_2_size) (succ 0)))))
      reg_2_size

  (** val mod_exp_state : int -> int -> int -> int -> exp **)

  let mod_exp_state num_qubits c num_exp_qubits n =
    ESeq ((ESeq ((ESeq ((New (lst_posi num_qubits x_var)), (New
      (lst_posi num_exp_qubits y_var)))), (Had
      (lst_posi num_qubits x_var)))),
      (repeat_ind (lst_posi num_qubits x_var) num_qubits (fun p i ->
        let a =
          mod_pow c
            (pow (succ (succ 0)) ((fun x y -> max 0 (x-y)) i (succ 0))) n
            ((+) i (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ 0)))))))))))))))))))))
        in
        Next (ICU (p, (Ora (ModMult ((lst_posi num_exp_qubits y_var),
        (nat2fb a), (nat2fb n)))))))))

  (** val mod_exp_test_eq : exp -> int -> bool **)

  let mod_exp_test_eq e v =
    let (_, qstate) =
      prog_sem_fix num_qubits_test e (init_env, (qvars,
        (bv2Eta num_qubits_test x_var v)))
    in
    Nat.eqb
      (snd_reg num_qubits_test num_exp_qubits_test
        (posi_list_to_bitstring (fst qstate) (snd qstate)))
      ((+)
        (mod_pow c_test
          (fst_reg num_qubits_test
            (posi_list_to_bitstring (fst qstate) (snd qstate))) coq_N_test
          num_qubits_test) (succ (succ 0)))
 end
