(* GHZTest.v *)

Require Import Coq.Init.Nat.
Require Import Reals Psatz.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat.
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import MathSpec.
Require Import Classical_Prop.
From Coq Require Import BinaryString.
From Coq Require Import Lists.ListSet.

(* Import the main file that contains PQASM definitions. Adjust path if needed. *)
Require Import PQASM.

From Coq Require Import Arith NArith.
From QuickChick Require Import QuickChick.
Require Import Testing.

Open Scope nat_scope.
Open Scope exp_scope.

(* --------------------------------------------------------- *)
(* Using the code from PQASM, we have:                       *)
(* - x_var, y_var, z_var as variables                        *)
(* - Instructions like New, Had, Next (ICU ...), Meas, etc.  *)
(* - Functions like nat2fb, lst_posi, etc.                   *)
(* --------------------------------------------------------- *)

(* We will define a cnot operation using ICU and Ora(Add ...).
   The idea: CNOT ctrl tgt flips 'tgt' if 'ctrl' is 1. We know:
   Add ps (nat2fb 1) toggles the bit represented by ps if run under control.
   
   So, ICU ctrl (Ora(Add [tgt] (nat2fb 1))) means:
   - If the qubit at 'ctrl' is 1, add 1 to [tgt], flipping it.
   - If ctrl is 0, do nothing.
*)

Definition cnot (ctrl tgt: posi) : exp :=
  Next (ICU ctrl (Ora (Add [tgt] (nat2fb 1)))).

(* Prepare GHZ state on qubits (x_var,0),(x_var,1),(x_var,2).
   Steps:
   1. New qubits in state |000>
   2. Apply Had on the first qubit => (|000> + |100>)/√2
   3. CNOT from qubit 0 to qubit 1 => (|000> + |110>)/√2
   4. CNOT from qubit 0 to qubit 2 => (|000> + |111>)/√2 = GHZ
   5. Measure z_var and these qubits, though for testing let's say we just stop or measure them.
   
   We'll measure z_var and the GHZ qubits to finalize. This is arbitrary; you might choose not
   to measure z_var if not needed. But let's follow a similar pattern to uniform/hamming tests.
*)

Definition ghz_circuit : exp :=
  New [(x_var,0);(x_var,1);(x_var,2)] [;]
  Had [(x_var,0)] [;]
  (cnot (x_var,0) (x_var,1)) [;]
  (cnot (x_var,0) (x_var,2)) [;]
  Meas z_var [(x_var,0); (x_var,1); (x_var,2)] ESKIP.

(* We define a test function similar to hamming_test_eq or simple_eq.
   We'll assume that after running ghz_circuit, we measure (x_var,0),(x_var,1),(x_var,2).
   The GHZ state ideally yields |000> or |111> when measured.

   We'll start the simulation from |000> for simplicity.
*)

Definition ghz_test_eq (e:exp) (n: nat) : bool :=
  (* Start with v=0 -> |000> state for the three qubits x_var:0, x_var:1, x_var:2 *)
  let v := N0 in
  let init_env : var -> nat := fun _ => 0 in
  let init_state := (lst_posi 3 x_var, bv2Eta 3 x_var v) in

  let (env,qstate) := prog_sem_fix n e (init_env,init_state) in
  (* Extract the measured bits from qstate *)
  let bs := posi_list_to_bitstring (lst_posi 3 x_var) (snd qstate) in
  let measured_val := a_nat2fb bs 3 in

  (* Check if measured_val = 0 (|000>) or measured_val = 7 (|111>, since 111 in binary = 7) *)
  if (measured_val =? 0) || (measured_val =? 7)
  then true
  else false.

(* Conjecture stating that ghz_test_eq always returns true for all tested n.
   QuickChick will try random n and see if it passes.
*)

Conjecture ghz_state_correct :
  forall (a: nat), ghz_test_eq ghz_circuit a = true.

(* Test the conjecture *)
QuickChick ghz_state_correct.
