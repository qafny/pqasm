Require Import Reals.
Require Import Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat.
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import MathSpec.
Require Import Classical_Prop.
Require Import PQASM.

Local Open Scope exp_scope.
Local Open Scope nat_scope.

Module DistinctElements.
  Definition rmax := 16.
  Definition m := 1000.
  Definition x_var : var := 0.
  Definition y_var : var := 1.
  Definition z_var : var := 2.

  Definition cvars := [z_var].
  Definition qvars : list posi := (y_var,0)::(lst_posi rmax x_var).
  Definition init_env : var -> nat := fun _ => 0.
  Definition init_st : eta_state := fun _ => Nval false.

  (* Compare a pair of qubits and add result to ancilla 
     We must ensure proper parentheses and no syntax ambiguities.
     Use '::nil' instead of '[...]' to avoid parsing errors.
  *)
  Definition compare_pair (q1 q2 ancilla: posi) : exp :=
    Next (ICU q1 (ICU q2 (Ora (Add (ancilla::nil) (nat2fb 1))))).

  (* Generate a sequence of pair comparisons *)
  Fixpoint compare_with_rest (i j: nat) : exp :=
    match j with
    | 0 => ESKIP
    | S k => compare_pair (x_var,i) (x_var,j) (y_var,0) [;] compare_with_rest i k
    end.

  Fixpoint compare_from (n i: nat) : exp :=
    match i with
    | 0 => ESKIP
    | S k => compare_with_rest k n [;] compare_from n k
    end.

  Fixpoint compare_all_pairs (n: nat) : exp :=
    match n with
    | 0 | 1 => ESKIP
    | S m => compare_from n m
    end.

  (* Main distinct elements circuit:
     Here we remove the recursive call in IFa.
  *)
  Definition distinct_s (n:nat) (m:nat) := 
       New ((y_var,0)::(lst_posi n x_var)) [;]    (* Initialize qubits and ancilla *)
       Had (lst_posi n x_var) [;]                 (* Create superposition *)
       compare_all_pairs n [;]                    (* Compare all pairs *)
       Meas z_var [(y_var,0)]                     (* Measure ancilla *)
       (IFa (CEq z_var (Num 0))                   (* If ancilla is 0, states are distinct *)
          ESKIP                                   (* Success case *)
          ESKIP).                                  (* Just ESKIP instead of recursion *)

  Definition simple_eq (e:exp) (v:N) := 
     let (env,qstate) := prog_sem_fix rmax e (init_env,(qvars,bv2Eta rmax x_var v)) in
        if env z_var =? 0                         (* Check if distinct *)
        then a_nat2fb (posi_list_to_bitstring (fst qstate) (snd qstate)) rmax <? m 
        else true.

  Conjecture distinct_correct :
    forall (vx : N), simple_eq (distinct_s rmax m) vx = true.

End DistinctElements.

From QuickChick Require Import QuickChick.
QuickChick DistinctElements.distinct_correct.
