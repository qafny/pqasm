Require Import OQASM.
Require Import PQASM.
Require Import BasicUtility.
Require Import Coq.QArith.QArith.
Require Import List.
Import ListNotations.
(* Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat.  *)



(*repeat until success: Inductive success or fail
if fail -> repeat until success*)


(*Ry Had (posi)*)
Definition a: nat :=3.
Definition b: var := a.
Definition c: nat :=4.
Definition d: var := c.
Definition test: iota:= Ry (b,d) (5 / 4).

(*Need a fixpoint to create posi of length n*)

(*permutations*)

(*Fredkin gates; can be built with  a whole lot of CNOT and not gates*)

Definition permutations: iota:= ICU (b,d) (Ry (b,d) (5 / 4)).

(*Hamming weight*)
(*Ry then Z?*)
(*Z (Ry (posi) (arcsin(sqrt(k/n))))*)

(*Power of two:*)
(*uniform superposition: two cases: one with power of two, one with not*)
Definition position_one: posi := (b,a).
Definition position_two: posi := (b,c).
Definition hamming: e:= Had ((b,a)::(b,c)::nil).

(*not a power of two*)