
type bool =
| True
| False

val xorb : bool -> bool -> bool

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

val app :
  'a1 list -> 'a1 list -> 'a1
  list

type sumbool =
| Left
| Right

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

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

module Nat :
 sig
  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat

  val sub : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val pow : nat -> nat -> nat

  val divmod :
    nat -> nat -> nat -> nat ->
    (nat, nat) prod

  val modulo : nat -> nat -> nat

  val b2n : bool -> nat
 end

module Pos :
 sig
  val succ :
    positive -> positive

  val of_succ_nat :
    nat -> positive
 end

module N :
 sig
  val of_nat : nat -> n
 end

val update :
  (nat -> 'a1) -> nat -> 'a1 ->
  nat -> 'a1

type var = nat

type posi = (var, nat) prod

val posi_eq :
  posi -> posi -> bool

val posi_eq_reflect :
  posi -> posi -> reflect

val posi_eq_dec :
  posi -> posi -> sumbool

val eupdate :
  (posi -> 'a1) -> posi -> 'a1
  -> posi -> 'a1

val allfalse : nat -> bool

val fb_push :
  bool -> (nat -> bool) -> nat
  -> bool

val pos2fb :
  positive -> nat -> bool

val n2fb : n -> nat -> bool

val nat2fb : nat -> nat -> bool

val carry :
  bool -> nat -> (nat -> bool)
  -> (nat -> bool) -> bool

val sumfb :
  bool -> (nat -> bool) -> (nat
  -> bool) -> nat -> bool

val natsum :
  nat -> (nat -> nat) -> nat

val a_nat2fb :
  (nat -> bool) -> nat -> nat

type 'a set = 'a list

val set_add :
  ('a1 -> 'a1 -> sumbool) ->
  'a1 -> 'a1 set -> 'a1 set

val set_mem :
  ('a1 -> 'a1 -> sumbool) ->
  'a1 -> 'a1 set -> bool

val set_diff :
  ('a1 -> 'a1 -> sumbool) ->
  'a1 set -> 'a1 set -> 'a1 set

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

val pi32 : nat -> nat

val angle_sum :
  rz_val_PQASM -> rz_val_PQASM
  -> nat -> nat

val angle_sub :
  rz_val_PQASM -> rz_val_PQASM
  -> nat -> nat

val ry_rotate :
  eta_state -> posi ->
  rz_val_PQASM -> nat ->
  eta_state

val set_diff_posi :
  posi set -> posi set -> posi
  set

val posi_list_to_bitstring_helper :
  posi list -> eta_state -> nat
  -> nat -> bool

val posi_list_to_bitstring :
  posi list -> eta_state -> nat
  -> bool

val mu_addition :
  posi list -> nat -> eta_state
  -> nat -> bool

val mu_less :
  posi list -> nat -> eta_state
  -> posi -> posi -> basis_val

val mu_eq :
  posi list -> nat -> eta_state
  -> posi -> posi -> basis_val

val mu_full_eq :
  posi list -> posi list ->
  eta_state -> posi -> posi ->
  basis_val

val bitstring_to_eta' :
  eta_state -> posi list ->
  (nat -> bool) -> nat ->
  eta_state

val bitstring_to_eta :
  eta_state -> posi list ->
  (nat -> bool) -> eta_state

val modmult :
  eta_state -> posi list -> nat
  -> nat -> eta_state

val mu_handling :
  nat -> mu -> eta_state ->
  eta_state

val instr_sem :
  nat -> iota -> eta_state ->
  eta_state

val eval_aexp :
  (var -> nat) -> aexp -> nat

val eval_bexp :
  (var -> nat) -> cbexp -> bool

type tstate =
  (posi list, eta_state) prod

type fstate =
  (var -> nat, tstate) prod

val new_env :
  var -> posi list -> fstate ->
  nat -> nat

val add_list :
  posi list -> fstate -> (var
  -> nat, (posi list,
  eta_state) prod) prod

val prog_sem_fix :
  nat -> exp -> fstate -> fstate
