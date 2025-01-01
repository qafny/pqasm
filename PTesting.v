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

(*Require Import OQASM.
Require Import Coq.QArith.QArith.*)
Import Nat (eqb).
(*Import Coq.FSets.FMapList.*)
(*From Coq Require Import BinaryString. 
From Coq Require Import Lists.ListSet.*)
(**********************)
(** Unitary Programs **)
(**********************)

Declare Scope exp_scope.
Delimit Scope exp_scope with expScope.
Local Open Scope exp_scope.
Local Open Scope nat_scope.

(* Testing Semantics. *)


(* need to redefine basis_val
Inductive basis_val := Nval (b:bool) | Rval (n:rz_val). (*same as PQASM, overrides Testing definition*)
*)

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

Definition tstate : Type := list posi * eta_state.

Definition fstate : Type := (var -> nat) * tstate.

Definition new_env (x:var) (qs:list posi) (st:fstate) :=
    update (fst st) x (a_nat2fb (posi_list_to_bitstring qs (snd (snd st))) (length qs)).
   

Definition add_list (qs:list posi) (st:fstate) :=
   (fst st, (qs ++ fst (snd st), snd (snd st))).

Fixpoint prog_sem_fix (rmax: nat) (e: exp)(st: fstate) : fstate := match e with 
| Next p => (fst st, (fst (snd st),instr_sem rmax p (snd (snd st))))
| ESeq k m => prog_sem_fix rmax m (prog_sem_fix rmax k st)
| IFa k op1 op2=> if (eval_bexp (fst st) k) then (prog_sem_fix rmax op1 st) else (prog_sem_fix rmax op2 st)
| ESKIP => st
| Had b => st
| New b => add_list b st
| Meas x qs e1 => prog_sem_fix rmax e1 ((new_env x qs st),(set_diff_posi (fst (snd st)) qs, snd (snd st)))
end.

Definition env_equivb vars (st st' : var -> nat) :=
  forallb (fun x =>  st x =? st' x) vars.

Definition st_equivb (rmax:nat) (vars: list posi) (st st': eta_state) :=
  forallb (fun x => basis_val_eq rmax (st x) (st' x)) vars.

From Coq Require Import Arith NArith.
From QuickChick Require Import QuickChick.
(* Require Import Testing. *)

Definition bv2Eta (n:nat) (x:var) (l: nat) : eta_state :=
   let f := nat2fb l in
   fun p => if (snd p <? n) && (fst p =? x) then Nval (f (snd p)) else Nval false.

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
Definition uniform_state (n:nat) (m:nat) := 
          fun P => New (lst_posi n x_var) [;] New ([(y_var,0)]) [;] Had (lst_posi n x_var)
                             [;] Less (lst_posi n x_var) m (y_var,0) [;] Meas z_var [(y_var,0)] (IFa (CEq z_var (Num 1)) ESKIP P).

Fixpoint repeat_operator_ICU_Add (a b: list posi):= 
  match a with 
| nil => ESKIP 
| h::t => (repeat_operator_ICU_Add t b) [;] (ICU h (Ora (Add b 1)))
end.

Definition hamming_weight_superposition (n m:nat) := 
  fun P =>  New (lst_posi n x_var) [;] New (lst_posi n y_var) [;] Had (lst_posi n x_var)
                             [;] repeat_operator_ICU_Add (lst_posi n x_var) (lst_posi n y_var)
                               [;] Meas z_var (lst_posi n x_var) (IFa (CEq z_var (Num 1)) ESKIP P).

Module Simple.

  (* Definition rmax := 16. 

  Definition m := 1000.
  *)

  (* Definition cvars := [z_var]. *)

  Definition qvars (n: nat) : list posi := (y_var,0)::(lst_posi n x_var).

  Definition init_env : var -> nat := fun _ => 0.

  (* Definition init_st : eta_state := fun _ => (Rval (fun (n:nat) => true)). *)

(*
  Fixpoint list_eq (x:posi) (l: list posi) :=
    match l with nil => false
               | y::ys => if posi_eq x y then true else list_eq x ys
    end.

  Fixpoint list_include (l1 l2: list posi) :=
    match l1 with nil => True
               | x::xs => (list_eq x l2) && list_include xs l2
    end. 
*)
  (* n= number of qubits to put in this state, m is their maximum value. Here, both lead to skips, but one sets z_var equal to 1, which affects how simple_eq tests it.*)
  Definition uniform_s (n:nat) (m:nat) := 
       Less (lst_posi n x_var) m (y_var,0) [;] Meas z_var ([(y_var,0)]) (IFa (CEq z_var (Num 1)) ESKIP ESKIP).
  Definition simple_eq (e:exp) (v:nat) (n: nat) := 
     let (env,qstate) := prog_sem_fix n e (init_env,(qvars n,bv2Eta n x_var v)) in
        if env z_var =? 1 then a_nat2fb (posi_list_to_bitstring (fst qstate) (snd qstate)) n <? v  else v <=?  a_nat2fb (posi_list_to_bitstring (fst qstate) (snd qstate)) n.
  Conjecture uniform_correct :
    forall (n:nat) (vx : nat), vx < 2^n -> simple_eq (uniform_s n vx) vx n = true.

End Simple.

QuickChick (Simple.uniform_correct 60). 

Definition exp_comparison (e1 e2: exp): bool :=
  match e1 with 
  | Next p => match e2 with 
        | Next q => true
        | _ => false
        end
  | ESKIP => match e2 with 
      | ESKIP => true
      | _ => false
      end
  | ESeq k m => match e2 with 
      | ESeq o p => true
      | _ => false
      end 
  | Had b=> match e2 with 
      | Had c => true
      | _ => false
      end  
| New b=> match e2 with 
      | New c => true
      | _ => false
      end 
  | Meas x qs e1 => match e2 with 
      | Meas y qs2 e2 => true
      | _ => false
      end 
  | IFa k op1 op2=> match e2 with 
      | IFa l op3 op4 => true
      | _ => false
      end              
  end.

(*
Definition exp_map_comparison (e1: (exp->exp)) (e2: (exp->exp)): bool:=
(exp_comparison (e1 ESKIP) (e2 ESKIP))
&& (exp_comparison (e1 IFa _ _ _) (e2 IFa)). 
Lemma exp_of_uniform_state: forall (m n: nat) (e1 e2 e3: exp), (exp_comparison (uniform_state m n e3) (ESeq e1 e2))=true.
Proof. intros. unfold uniform_state. unfold exp_comparison.  reflexivity. Qed. 
*)


Module Test_prop. 
Conjecture uniform_state_eskip_behavior: forall (m: nat) (n: nat),
exp_comparison ((uniform_state m n) ESKIP) ((uniform_state n m) ESKIP) = true.

Conjecture uniform_state_new_behavior: forall (m n o: nat) (x: var),
exp_comparison ((uniform_state m n) (New (lst_posi o x))) ((uniform_state n m) (New (lst_posi o x))) = true.

Conjecture uniform_state_new_eskip_behavior: forall (m n o: nat) (x: var),
exp_comparison ((uniform_state m n) (New (lst_posi o x))) ((uniform_state n m) ESKIP) = true.

End Test_prop.

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
  (* Definition target_hamming_w := 17. *)

  (* classical variables *)
  Definition cvars := [z_var].

  (* Fixpoint concat (l1 l2: list (var * nat)) :=
    match l1 with
    | nil => l2
    | _ => (fst l1)::(concat (snd l1) l2)
    end. *)

  (* Quantum registers, accessible with x_var and y_var *)
  Definition yvars:= (lst_posi state_qubits y_var).

  Definition xvars := (lst_posi state_qubits x_var).

  Definition qvars : list posi := yvars++xvars.

  (* Environment to start with; all variables set to 0 *)
  Definition init_env : var -> nat := fun _ => 0.

  (* not sure if this is actually needed *)
  Definition init_st : eta_state := fun _ => Nval false.

  (* For the hamming_test_eq, gets the hamming weight of a bitstring
    bs is the bitstring, n is the length of the bitstring *)
  Fixpoint hamming_weight_of_bitstring' (n: nat) (bs: (nat -> bool)) (re:nat) :=
    match n with
    | 0 => re
    | S m => if bs m then hamming_weight_of_bitstring' m bs (re+1) else hamming_weight_of_bitstring' m bs re
    end.
  Definition hamming_weight_of_bitstring n bs := hamming_weight_of_bitstring' n bs 0.

  (* Prepare a uniform superposition across all states that have a hamming weight equal to w.
    n is the number of qubits in the register being preapred; 
    h_n is the number of qubits to use when measuring the hamming weight
  *)
  Definition hamming_state (w:nat):=
    (repeat xvars (fun (p:posi) => (ICU p (Ora (Add yvars 1))))) [;]
      Meas z_var yvars (IFa (CEq z_var (Num w)) ESKIP ESKIP).

  Definition hamming_test_eq (e:exp) (n:nat) (v:nat) := 
     let (env,qstate) := prog_sem_fix state_qubits e (init_env,(qvars,bv2Eta state_qubits x_var v)) in
        env z_var =?  (hamming_weight_of_bitstring state_qubits 
           (posi_list_to_bitstring (xvars) (snd qstate))).

  Conjecture hamming_state_correct:
    forall (vx:nat), vx < 2 ^ state_qubits -> hamming_test_eq (hamming_state (hamming_weight_of_bitstring state_qubits (nat2fb vx)))
              (hamming_weight_of_bitstring state_qubits (nat2fb vx)) vx = true.

End Hamming.
(* Check @choose. *)
(* Check returnGen. *)
(* Sample (choose (0,10)). *)
QuickChick (Hamming.hamming_state_correct). 

Module AmplitudeAmplification.

  Definition state_qubits := 60.

  Definition qvars : list posi := (y_var,0)::(lst_posi state_qubits x_var).

  (* Environment to start with; all variables set to 0 *)
  Definition init_env : var -> nat := fun _ => 0.

(* Like repeat, but also gives the function an index to work with*)
Fixpoint repeat_ry (reg: list posi) (r:nat) :=
  match reg with
  | nil => ESKIP
  | p::xs => ((ICU p (Ry (y_var,0) r))) [;] (repeat_ry xs (2*r))
  end.
Definition amplitude_amplification_state (r:nat) (rmax:nat) :=
    Next (Ry (y_var,0) (r)) [;]
    repeat_ry (lst_posi rmax x_var) (2*r).

  Definition aa_state_eq (s:eta_state) (r:nat) (x:nat) (rmax:nat) := 
     match s (y_var,0) with Nval b => false | Rval n => n =? ((2*x + 1) * r) mod 2^rmax end.

  Definition aa_test_eq (e:exp) (v:nat) (r:nat) := 
     let (env,qstate) := prog_sem_fix state_qubits e (init_env,(qvars,bv2Eta state_qubits x_var r)) in
            aa_state_eq (snd qstate) r (a_nat2fb (posi_list_to_bitstring ((lst_posi state_qubits x_var)) (snd qstate)) state_qubits) state_qubits.

  Conjecture aa_state_correct:
    forall (r: nat) (vx:nat), r < 2^state_qubits -> aa_test_eq (amplitude_amplification_state r state_qubits) vx r = true.

End AmplitudeAmplification.

QuickChick (AmplitudeAmplification.aa_state_correct). 


Module ModExpState.

  Definition c_test := 3.
  Definition N_test := 34.

  Definition num_qubits := 60.

  (* Environment to start with; all variables set to 0 *)
  Definition init_env : var -> nat := fun _ => 0.

  (* Quantum registers; x_var stores all of the state qubits*)
  Definition yvars:= (lst_posi num_qubits y_var).

  Definition xvars := (lst_posi num_qubits x_var).
  Definition qvars : list posi := yvars++xvars.
  
  (* Returns c^n mod m. c is the base number, n is the exponent, m is the mod factor, 
  and max_iter is the maximum number of iterations this function should have. 
  It's needed to placate Coq. This function requires about log_2 n recursive steps. 
  Fixpoint mod_pow (c n m max_iter: nat) :=
    match max_iter with
    | 0 => 1 mod m
    | S l => 
      if n =? 0 then 1 
      else 
        let u := (mod_pow c (n/2) m l) in
          if (n mod 2 =? 0) then 
            ((u*u) mod m) 
          else 
            ((((u*u) mod m)*c) mod m)
    end.

  (* Returns c^n *)
  Fixpoint pow(c n: nat) :=
    match n with 
    | 0 => 1
    | S m => c * (pow c m)
    end.

  Fixpoint repeat (reg: list posi) (P: (posi -> exp)) :=
    match reg with
    | nil => ESKIP
    | p::r => (P p) [;] (repeat r P)
    end.

  (* Like repeat, but also gives the function an index to work with*)
  Fixpoint repeat_ind (reg: list posi) (index: nat) (P: (posi -> nat -> exp)) :=
    match reg with
    | nil => ESKIP
    | p::r => (repeat_ind r (index-1) P) [;] (P p index)
    end.

  Fixpoint fst_reg (reg_1_size: nat) (bs: (nat -> bool)) :=
    match reg_1_size with
    | 0 => 0
    | S m => (fst_reg m bs) * 2 + (bool_to_nat (bs (reg_1_size-1)))
    end.

  Fixpoint snd_reg (reg_1_size reg_2_size: nat) (bs: (nat -> bool)) :=
    match reg_2_size with
    | 0 => 0
    | S m => (snd_reg reg_1_size m bs) * 2 + (bool_to_nat (bs (reg_1_size + reg_2_size-1)))
    end.
*)
  Fixpoint repeat_modmult (reg reg1: list posi) (c:nat) (n:nat) :=
    match reg with
      | nil => ESKIP
      | p::xs => ((ICU p (ModMult (reg1) c n))) [;] (repeat_modmult xs reg1 (2*c) n)
     end.

  Definition mod_exp_state (c n: nat) :=
    (Add yvars 1) [;] repeat_modmult xvars yvars c n.

  Fixpoint cton (size:nat) (vx: nat -> bool) (c n:nat) :=
   match size with 0 => 1
                 | S m => if vx m then (2^m * c * (cton m vx c n)) mod n else cton m vx c n
   end.

  Definition mod_exp_test_eq (e:exp) (v c n:nat) := 
      let (env,qstate) := prog_sem_fix num_qubits e (init_env,(qvars,bv2Eta num_qubits x_var v)) in
          let vx := (posi_list_to_bitstring xvars (snd qstate)) in
          a_nat2fb (posi_list_to_bitstring yvars (snd qstate)) num_qubits =? cton num_qubits vx c n.
          
  Conjecture mod_exp_state_correct:
    forall (vx : nat), vx < 2^16 -> mod_exp_test_eq (mod_exp_state c_test N_test) vx c_test N_test = true.

End ModExpState.

QuickChick (ModExpState.mod_exp_state_correct).


Module DistinctElements.

  Definition state_qubits := 60.

  Definition dis_state := 2.

  Definition qvars : list posi := (lst_posi state_qubits z_var)++((y_var,0)::(lst_posi (dis_state * state_qubits) x_var)).

  Definition init_env : var -> nat := fun _ => 0.

  Fixpoint lst_posi_q' (n j:nat) (x:var) :=
    match n with 0 => nil | S m => (lst_posi_q' m j x) ++ [(x, m + j * state_qubits)] end.
  Definition lst_posi_q (j:nat) (x:var) := lst_posi_q' state_qubits j x.

  Fixpoint repeat_qapp_aux (n j:nat) :=
     match n with 0 => ESKIP
                | S m => Equal_posi_list (lst_posi_q m x_var) (lst_posi_q j x_var) (y_var, 0)
                           [;] ICU (y_var,0) (Ora (Add (lst_posi state_qubits z_var) 1))
                           [;]  Equal_posi_list (lst_posi_q m x_var) (lst_posi_q j x_var) (y_var, 0)
                           [;] repeat_qapp_aux m j
     end.
  Fixpoint repeat_qapp' (n:nat) :=
    match n with 0 => ESKIP
               | S m => repeat_qapp_aux m n [;] repeat_qapp' m
    end.
  Definition repeat_qapp := repeat_qapp' (dis_state-1).

  Definition distinct_element_state := repeat_qapp [;] 
    Meas u_var (lst_posi state_qubits z_var) (IFa (CEq z_var (Num 0)) ESKIP ESKIP).
  
  Fixpoint distinct_state_aux (n j:nat) (st:eta_state):=
      match n with 0 => true
                | S m => negb ((a_nat2fb (posi_list_to_bitstring (lst_posi_q m x_var) st) state_qubits)
                 =? (a_nat2fb (posi_list_to_bitstring (lst_posi_q j x_var) st) state_qubits))
                         && distinct_state_aux m j st
      end.
   Fixpoint distinct_state_right' (n:nat) (st:eta_state):=
      match n with 0 => true
                 | S m => distinct_state_aux m n st && distinct_state_right' m st
      end.
   Definition distinct_state_right (st:eta_state) := distinct_state_right' (dis_state-1) st.


  Definition distinct_elem_test_eq (e:exp) (v:nat) := 
    let (env,qstate) := prog_sem_fix state_qubits e (init_env,(qvars,bv2Eta state_qubits x_var v)) in
       distinct_state_right (snd qstate).

  Conjecture distinct_elem_state_correct:
    forall (vx : nat), distinct_elem_test_eq (distinct_element_state) vx = true.

End DistinctElements.

QuickChick (DistinctElements.distinct_elem_state_correct).


Module SumState.

  (* Number of quantum registers *)
  Definition num_reg_test := 3.

  (* Size of each register *)
  Definition reg_size_test := 4.

  (* Target Sum *)
  Definition k_test := 20.

  (* classical variables *)
  Definition cvars := [z_var].

  (* Quantum registers; x_var stores all of the state qbits*)
  Definition qvars : list posi := (lst_posi (num_reg_test*reg_size_test) x_var).

  (* Environment to start with; all variables set to 0 *)
  Definition init_env : var -> nat := fun _ => 0.

  (* Returns an expression to run P on each qubit position in reg*)
  Fixpoint repeat (reg: list posi) (P: (posi -> exp)) :=
    match reg with
    | nil => ESKIP
    | p::r => (P p) [;] (repeat r P)
    end.

  (* Like repeat, but also gives the function an index to work with*)
  Fixpoint repeat_ind (reg: list posi) (index: nat) (P: (posi -> nat -> exp)) :=
    match reg with
    | nil => ESKIP
    | p::r => (P p index) [;] (repeat_ind r (index-1) P)
    end.

  (* Returns a list of variables that start at start_var *)
  Fixpoint lst_var (len: nat) (start_var: var) :=
    match len with
    | 0 => nil
    | S len_m => ((len_m+(start_var:nat)):var)::(lst_var len_m start_var)
    end.

  (* Repeats an operation on a list of quantum registers *)
  Fixpoint repeat_reg (P: (list posi -> exp)) (regs: list var) (reg_size: nat):=
    match regs with
    | nil => ESKIP
    | r::rs => (P (lst_posi reg_size r)) [;] (repeat_reg P rs reg_size)
    end.

  Fixpoint pow_2 (n: nat) :=
    match n with
    | 0 => 1
    | S m => 2*(pow_2 (m))
    end.

  Definition sum_state (num_reg:nat) (reg_size:nat) (target_sum:nat) :=
    let prep_list := (lst_var num_reg x_var) in 
      let sum_var := ((x_var:nat)+num_reg):var in
        (repeat_reg New prep_list reg_size) [;] (New (lst_posi (reg_size+num_reg) sum_var)) [;]
        (
          repeat_reg (
            fun (lp: list posi) => (
              repeat_ind lp reg_size (fun (p: posi) (index: nat) => (
                ICU p (Ora (Add (lst_posi (reg_size + num_reg) sum_var) ( (pow_2 index))))
              ))
            )
          )
          prep_list
          reg_size
        ) [;]
        Meas z_var (lst_posi (reg_size+num_reg) sum_var) (IFa (CEq z_var (Num target_sum)) ESKIP ESKIP).

  (* Gets a register from a bitstring as a natural number *)
  Fixpoint bitstring_slice (reg: nat) (reg_size: nat) (ind: nat) (bs: (nat -> bool)) :=
    match ind with
    | 0 => 0
    | S m => (bitstring_slice reg reg_size m bs) * 2 + (bool_to_nat (bs ((reg - 1) * reg_size + (ind-1))))
    end.

  (* Sum of the integer values in a bitstring in big endian (MSB first) order. reg_size is the number of bits in each integer and n is the number of integers to add up*)
  Fixpoint sum_of_bitstring (n: nat) (reg_size: nat) (bs: (nat -> bool)) :=
    match n with
    | 0 => 0
    | S m => (bitstring_slice n reg_size reg_size bs) + (sum_of_bitstring m reg_size bs)
    end.

  (* Just need to get this to work *)
  Definition sum_test_eq (e:exp) (v:nat) :=
    let state_qubits := num_reg_test * reg_size_test in
      let (env,qstate) := prog_sem_fix state_qubits e (init_env,(qvars,bv2Eta state_qubits x_var v)) in
        if env z_var =? k_test then (sum_of_bitstring num_reg_test reg_size_test (posi_list_to_bitstring (fst qstate) (snd qstate))) =? k_test else true.

  Conjecture sum_state_correct:
    forall (vx : nat), sum_test_eq (sum_state num_reg_test reg_size_test k_test) vx = true.

End SumState.

(* QuickChick (SumState.sum_state_correct). *)

