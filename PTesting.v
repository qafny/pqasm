Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import MathSpec.
Require Import Classical_Prop.
Require Import RZArith.
Require Import PQASM.

Import Nat (eqb).
(**********************)
(** Unitary Programs **)
(**********************)

Declare Scope exp_scope.
Delimit Scope exp_scope with expScope.
Local Open Scope exp_scope.
Local Open Scope nat_scope.

(* Testing Semantics. *)


(* 
Define the equivalent testing syntax and eta_state
*)
Inductive mu_a := TAdd (ps: var) (n:N) (* we add nat to the bitstring represenation of ps *)
              | TLess (ps : var) (n:N) (p:posi) (* we compare ps with n (|ps| < n) store the boolean result in p. *)
              | TEqual (ps : var) (n:N) (p:posi) (* we compare ps with n (|ps| = n) store the boolean result in p. *)
              | TModMult (ps : var) (n:N) (m: N)
              | TEqual_posi_list (ps qs: var) (p:posi).

Inductive iota_a:= TISeq (k: iota_a) (m: iota_a) 
                 | TICU (x:posi) (y:iota_a)
                 | TOra (e:mu_a) 
                 | TRy (p: posi) (r: N).

Coercion TOra : mu_a >-> iota_a.

Inductive exp_a := TSKIP | TNext (p: iota_a) | THad (b:var) | TNew (b:var) (n:nat) 
| TSeq (k: exp_a) (m: exp_a) | TMeas (x:var) (qs:var) (e1:exp_a) | TIFa (k: cbexp) (op1: exp_a) (op2: exp_a).

Coercion TNext : iota_a >-> exp_a.
Notation "e0 {;} e1" := (TSeq e0 e1) (at level 50) : exp_scope.

Inductive basis_val_a := NvalA (b:N) | RvalA (f:nat -> N).

Definition eta_state_a : Type := var -> basis_val_a.

Definition grab_nval (b:basis_val_a) := match b with NvalA b => b | RvalA f => (N.of_nat 0) end.
Definition update_nval (st: eta_state_a) (x:var) (n:N) := update st x (NvalA n).
Definition grab_rval (b:basis_val_a) := match b with NvalA b => (fun _ => N.of_nat 0) | RvalA f => f end.

Definition allZero : nat -> N := fun _ => N.of_nat 0.

Definition pi32_a (rmax:N) : N:= (N.pow 2 (rmax-1)) + (N.pow 2 (rmax-2)).

Definition angle_sum_a (f g:N) (rmax:N) :N := (f + g) mod 2^rmax.

Definition angle_sub_a (f g: N) (rmax:N) :N := if N.ltb f g then (N.pow 2 rmax) - (g - f) else f - g.

Definition ry_rotate_a (st:eta_state_a) (p:posi) (r:N) (rmax:N): eta_state_a :=
   match st (fst p) with  NvalA b2 => if N.testbit b2 (N.of_nat (snd p))
                                     then update st (fst p) (RvalA (update allZero (snd p) (angle_sub_a (pi32_a rmax) r rmax)))
                                     else update st (fst p) (RvalA (update allZero (snd p) r))
                      | RvalA r1 => update st (fst p) (RvalA (update r1 (snd p) (angle_sum_a (r1 (snd p)) r rmax)))
   end.

Definition mu_handling_a (m: mu_a) (st: eta_state_a) : eta_state_a :=
  match m with 
  | TAdd ps n => update_nval st ps ((grab_nval (st ps)) + n)
  | TLess ps n p => if N.ltb (grab_nval (st ps)) n
                     then update_nval st (fst p) (N.lxor (grab_nval (st (fst p))) (N.pow 2 (N.of_nat (snd p)))) 
                     else st
  | TEqual ps n p => if N.eqb (grab_nval (st ps)) n 
                    then update_nval st (fst p) (N.lxor (grab_nval (st (fst p))) (N.pow 2 (N.of_nat (snd p)))) else st
  | TModMult ps n m =>  update_nval st ps ((n * (grab_nval (st ps))) mod m)
  | TEqual_posi_list ps qs p =>if N.eqb (grab_nval (st ps)) (grab_nval (st qs)) 
                 then update_nval st (fst p) (N.lxor (grab_nval (st (fst p))) (N.pow 2 (N.of_nat (snd p)))) else st
  end.
Fixpoint instr_sem_a (rmax: N) (e:iota_a) (st: eta_state_a): eta_state_a :=
   match e with 
   | TRy p r => ry_rotate_a st p r rmax
   | TISeq a b => instr_sem_a rmax b (instr_sem_a rmax a st)
   | TOra m => mu_handling_a m st
  | TICU x y => match st (fst x) with 
      | RvalA r =>  st 
      | NvalA v => if N.testbit v (N.of_nat (snd x)) then instr_sem_a rmax y st else st
        end  
   end.

Fixpoint eval_aexp (env: (var -> nat)) (e:aexp) :=
 match e with BA x => env x
            | Num n => n
            | e1 [+] e2 => (eval_aexp env e1) + (eval_aexp env e2)
            | e1 [*] e2 => (eval_aexp env e1) * (eval_aexp env e2)
 end.

Definition eval_bexp (env: (var -> nat)) (e:cbexp) :=
  match e with CEq a b => (eval_aexp env a) =? (eval_aexp env b)
             | CLt a b => (eval_aexp env a) <? (eval_aexp env b)
  end.

Definition tstate : Type := (var -> nat) * eta_state_a.

Definition fstate : Type := (var -> nat) * tstate.

Definition new_env (x:var) (qs:nat) (st:var -> nat) := update st x qs.

Fixpoint prog_sem_fix (rmax:nat) (e: exp_a)(st: fstate) : fstate := match e with 
| TNext p => (fst st, (fst (snd st) , instr_sem_a (N.of_nat rmax) p (snd (snd st))))
| TSeq k m => prog_sem_fix rmax m (prog_sem_fix rmax k st)
| TIFa k op1 op2=> if (eval_bexp (fst (snd st)) k) then (prog_sem_fix rmax op1 st) else (prog_sem_fix rmax op2 st)
| TSKIP => st
| THad b => st
| TNew x n => (new_env x n (fst st), snd st)
| TMeas x qs e1 => prog_sem_fix rmax e1 
          (fst st,(new_env x (N.to_nat (grab_nval ((snd (snd st)) qs))) (fst (snd st)), snd (snd st)))
end.

Definition env_equivb vars (st st' : var -> nat) :=
  forallb (fun x =>  st x =? st' x) vars.

Fixpoint foralln (n:nat) (f:nat -> bool) :=
   match n with 0 => true | S m => f m && foralln m f end.

  Definition rz_val_eq_a (rmax:N) (x y : N) := N.eqb (x mod (N.pow 2 rmax)) (y mod (N.pow 2 rmax)).

  Definition basis_val_eq_a (rmax: nat) (x y : basis_val_a) :=
      match (x,y) with (NvalA b, NvalA b') => N.eqb b b'
                   | (RvalA bl1, RvalA bl2) => foralln rmax (fun n => rz_val_eq_a (N.of_nat rmax) (bl1 n) (bl2 n))
                   | _ => false
      end.

Definition st_equivb (env:var -> nat) (vars: list var) (st st': eta_state_a) :=
  forallb (fun x => basis_val_eq_a (env x) (st x) (st' x)) vars.

From Coq Require Import Arith NArith.
From QuickChick Require Import QuickChick.
(* Require Import Testing. *)

(* Check shrinkNat. *)

Definition bv2Eta (n:nat) (x:var) (l: N) : eta_state_a := (fun y => if x =? y then NvalA (l mod (N.pow 2 (N.of_nat n))) else NvalA 0).

(*if there exists an input for which the test fails in our semantics, then in the original program that input will result in the program not having that property*)
(*test_fails_on_input -> program_will_have_bug_on_input*)
(*test_fails_on_input means given a certain input, a property does not hold *)
(*if test fails on input then program fails; how do we write 'test' and 'program'?*)
(* (forall A, if prog_sem_fix A != prog_sem A -> bug *)
Lemma translation_correctness: forall rmax phi phi' e e' r, @prog_sem rmax phi e r phi' e' -> True.
Proof. Admitted.

(* Examples. We use the constant hard-code variable names below. *)
Definition x_var : var := 0.
Definition y_var : var := 1.
Definition z_var : var := 2.
Definition u_var : var := 3.

Fixpoint lst_posi (n:nat) (x:var) :=
   match n with 0 => nil | S m => (lst_posi m x)++[(x, m)] end.
(* we prepare a superposition of m different basis-states, where n is the length of qubits in x_var. 
  nat2fb turns a nat number to a bitstring. 
  we define a function P for a one step process of the repeat-until-success.
  In Ocaml, you can input a variable name for P, 
 *)
Definition uniform_state (n:nat) (m:N) := 
          fun P => TNew x_var n {;} TNew y_var 1 {;} THad x_var
                             {;} TLess x_var m (y_var,0) {;} TMeas z_var y_var (TIFa (CEq (BA z_var) (Num 1)) TSKIP P).

Module Simple.

  Definition state_qubits := 60.

  Definition qvars : list var := y_var::[x_var].

  Definition init_env : var -> nat := fun _ => 0.

  Definition simple_eq (e:exp_a) (v:N) (n: nat) := 
     let (env,qstate) := prog_sem_fix state_qubits e (init_env,(init_env,bv2Eta n x_var v)) in
        if (fst qstate) z_var =? 1 then N.ltb (grab_nval ((snd qstate) x_var)) v else N.leb v (grab_nval ((snd qstate) x_var)).
  Conjecture uniform_correct :
    forall (n:nat) (vx : nat), vx < 2^n -> simple_eq (uniform_state n (N.of_nat vx) TSKIP) (N.of_nat vx) n = true.

End Simple.

Compute N.ltb 3 5.
Compute N.leb 3 5.
Compute N.ltb 5 5.
Compute N.leb 5 5.
(* QuickChick (Simple.uniform_correct 8).  *)

QuickChick (Simple.uniform_correct 60). 

Fixpoint repeat_operator_ICU_Add (a b: var) (n:nat):= 
  match n with 
| 0 => TSKIP 
| S m => (repeat_operator_ICU_Add a b m) {;} (TICU (a,m) (TOra (TAdd b 1)))
end.

Definition hamming_weight_superposition (n m:nat) := 
  fun P =>  TNew x_var n {;} TNew y_var n {;} THad x_var
                             {;} repeat_operator_ICU_Add x_var y_var n
                               {;} TMeas z_var y_var (TIFa (CEq (BA z_var) (Num m)) TSKIP P).

(* Takes a boolean and returns 1 if it's true and 0 if it's false *)
Definition bool_to_nat (b: bool) :=
  match b with
  | true => 1
  | false => 0
  end.

(* Returns an expression to run P on each qubit position in reg*)
Fixpoint repeat (reg: list posi) (P: (posi -> exp)) :=
    match reg with
    | nil => ESKIP
    | p::r => (P p) [;] (repeat r P)
    end.

Module Hamming.

  Definition state_qubits := 60.

  (* classical variables *)
  Definition cvars := [z_var].

  (* Quantum registers, accessible with x_var and y_var *)
  Definition qvars : list var := x_var::[y_var].

  (* Environment to start with; all variables set to 0 *)
  Definition init_env : var -> nat := fun _ => 0.

  (* not sure if this is actually needed *)
  Definition init_st : eta_state_a := fun _ => NvalA 0.

  (* For the hamming_test_eq, gets the hamming weight of a bitstring
    bs is the bitstring, n is the length of the bitstring *)
  Fixpoint hamming_weight_of_N' (n: nat) (bs: N) (re:nat) :=
    match n with
    | 0 => re
    | S m => if N.testbit bs (N.of_nat m) then hamming_weight_of_N' m bs (re+1) else hamming_weight_of_N' m bs re
    end.
  Definition hamming_weight_of_N n bs := hamming_weight_of_N' n bs 0.

  Definition hamming_test_eq (e:exp_a) (n:nat) (v:N) := 
     let (env,qstate) := prog_sem_fix state_qubits e (init_env,(init_env,bv2Eta state_qubits x_var v)) in
        (fst qstate) z_var =? hamming_weight_of_N state_qubits (grab_nval ((snd qstate) x_var)).

  Conjecture hamming_state_correct:
    forall (vx:nat), vx < 2 ^ state_qubits -> 
        hamming_test_eq (hamming_weight_superposition state_qubits 
             (hamming_weight_of_N state_qubits (N.of_nat vx)) TSKIP) state_qubits (N.of_nat vx) = true.

End Hamming.

QuickChick (Hamming.hamming_state_correct). 

Module AmplitudeAmplification.

  Definition state_qubits := 60.

  Definition qvars : list var := y_var::[x_var].

  (* Environment to start with; all variables set to 0 *)
  Definition init_env : var -> nat := fun _ => 0.

(* Like repeat, but also gives the function an index to work with*)
Fixpoint repeat_ry' (n:nat) (x y: var) (r:N) :=
  match n with
  | 0 => (TSKIP,r)
  | S m => let (cir,ra) := (repeat_ry' m x y r) in (cir {;} (TICU (x,m) (TRy (y,0) ra)), N.mul 2 ra)
  end.
Definition repeat_ry (n:nat) (x y: var) (r:N) := fst (repeat_ry' n x y r).

Definition amplitude_amplification_state (r:N) :=
    TNext (TRy (y_var,0) (r)) {;}
    repeat_ry state_qubits x_var y_var (2*r).

  Definition aa_state_eq (s:eta_state_a) (r:N) (x:N) (rmax:N) := 
     match s y_var with NvalA b => false | RvalA n => N.eqb (n 0) (((2*x + 1) * r) mod 2^rmax) end.

  Definition aa_test_eq (e:exp_a) (r:N) (v:N) := 
     let (env,qstate) := prog_sem_fix state_qubits e (init_env,(init_env,bv2Eta state_qubits x_var v)) in
            aa_state_eq (snd qstate) r (grab_nval ((snd qstate) x_var)) (N.of_nat state_qubits).

  Conjecture aa_state_correct:
    forall (vx:nat) (r: nat), vx < 2^state_qubits -> 
           r < 2^state_qubits -> aa_test_eq (amplitude_amplification_state (N.of_nat r)) (N.of_nat r) (N.of_nat vx) = true.

End AmplitudeAmplification.

QuickChick (AmplitudeAmplification.aa_state_correct). 

Module ModExpState.

  Definition c_test : N := 3.
  Definition N_test : N := 34.

  Definition num_qubits := 60.

  (* Environment to start with; all variables set to 0 *)
  Definition init_env : var -> nat := fun _ => 0.

  (* Quantum registers; x_var stores all of the state qubits*)
  Definition yvars:= (lst_posi num_qubits y_var).

  Definition xvars := (lst_posi num_qubits x_var).
  Definition qvars : list var := x_var::[y_var].
  
  (* the computation of c^(2^m) mod n can be very slow in Coq. *)
  Fixpoint cal_mod_pow (c n:N) (m:nat) :=
    match m with 0 => c
               | S h => N.modulo (N.mul (cal_mod_pow c n h) (cal_mod_pow c n h)) n
    end.

  Fixpoint repeat_modmult (size:nat) (reg reg1: var) (c:N) (n:N) :=
    match size with
      | 0 => TSKIP
      | S m => repeat_modmult m reg reg1 c n {;} (TICU (reg,m) (TModMult (reg1) (cal_mod_pow c n m) n))
     end.

  Definition mod_exp_state (c n: N) :=
    TNew x_var num_qubits {;} TNew y_var num_qubits {;} THad x_var {;}
    (TAdd y_var 1) {;} repeat_modmult 10 x_var y_var c n.

  Definition mod_exp_test_eq (e:exp_a) (v c n:N) := 
      let (env,qstate) := prog_sem_fix num_qubits e (init_env,(init_env,bv2Eta num_qubits x_var v)) in
          let vx := N.to_nat (grab_nval ((snd qstate) x_var)) in
        N.eqb (grab_nval ((snd qstate) y_var)) (N.modulo (N.pow c (N.of_nat vx)) n).

  Conjecture mod_exp_state_correct:
    forall (vx : nat), 1 < vx < 2^16 -> mod_exp_test_eq (mod_exp_state c_test N_test) (N.of_nat vx) c_test N_test = true.

End ModExpState.

QuickChick (ModExpState.mod_exp_state_correct).

Fixpoint bv2Etas (n:N) (xs:list (var * N)) : eta_state_a := 
      match xs with [] => (fun _ => NvalA 0)
                  | (x,v)::ys => 
            (fun y => if x =? y then NvalA  (v mod 2^n) else bv2Etas n ys y)
       end.

Module DistinctElements.

  Definition state_qubits := 60.

  Definition dis_state := 5.
  Definition xvars := (0::1::2::3::[4]).
  Definition zvar := 5.
  Definition yvar := 6.
  Definition uvar := 7.

  Definition init_env : var -> nat := fun v => if v =? yvar then 1 else state_qubits.

  Definition init_cstate : var -> nat := fun v => 0.

  Fixpoint lst_posi_q' (n j:nat) (x:var) :=
    match n with 0 => nil | S m => (lst_posi_q' m j x) ++ [(x, m + j * state_qubits)] end.
  Definition lst_posi_q (j:nat) (x:var) := lst_posi_q' state_qubits j x.

  Fixpoint repeat_qapp_aux (n j:nat) :=
     match n with 0 => TSKIP
                | S m => TEqual_posi_list m j (yvar, 0)
                           {;} TICU (yvar,0) (TOra (TAdd zvar 1))
                           {;}  TEqual_posi_list m j (yvar, 0)
                           {;} repeat_qapp_aux m j
     end.
  Fixpoint repeat_qapp' (n:nat) :=
    match n with 0 => TSKIP
               | S m => repeat_qapp_aux m m {;} repeat_qapp' m
    end.
  Definition repeat_qapp := repeat_qapp' (dis_state).

  Definition distinct_element_state := repeat_qapp {;} 
    TMeas uvar zvar (TIFa (CEq (BA uvar) (Num 0)) TSKIP TSKIP).

  Definition b2nat (b:bool) := if b then 1 else 0.
  
  Fixpoint distinct_state_aux (n j:nat) (st:eta_state_a):=
      match n with 0 => 0
                | S m => b2nat (N.eqb (grab_nval(st m)) (grab_nval(st j)))
                         + distinct_state_aux m j st
      end.
   Fixpoint distinct_state_right' (n:nat) (st:eta_state_a):=
      match n with 0 => 0
                 | S m => distinct_state_aux m m st + distinct_state_right' m st
      end.
   Definition distinct_state_right (st:eta_state_a) := distinct_state_right' (dis_state) st.


  Definition distinct_elem_test_eq (e:exp_a) (vs:list N) := 
    let (env,qstate) := prog_sem_fix state_qubits e (init_env,(init_cstate,bv2Etas (N.of_nat state_qubits) (combine xvars vs))) in
       (fst qstate) uvar =? distinct_state_right (snd qstate).


  Conjecture distinct_elem_state_correct:
    forall (vx0 vx1 vx2 vx3 vx4:nat), vx0 < 2 ^ (state_qubits) -> vx1 < 2 ^ (state_qubits) 
          -> vx2 < 2 ^ (state_qubits) -> vx3 < 2 ^ (state_qubits) -> vx4 < 2 ^ (state_qubits)
          -> distinct_elem_test_eq distinct_element_state
                  ((N.of_nat vx0)::(N.of_nat vx1)::(N.of_nat vx2)::(N.of_nat vx3)::[N.of_nat vx4]) = true.

End DistinctElements.

QuickChick (DistinctElements.distinct_elem_state_correct).
