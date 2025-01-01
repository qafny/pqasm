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
From Coq Require Import BinaryString.
From Coq Require Import Lists.ListSet.
(**********************)
(** Unitary Programs **)
(**********************)

Declare Scope exp_scope.
Delimit Scope exp_scope with expScope.
Local Open Scope exp_scope.
Local Open Scope nat_scope.


(* Defining typing rules here. *)

(* Defining the inductive relation for disjoint. *)
Inductive disjoint : list posi -> Prop :=
   dis_empty : disjoint nil
  | dis_many : forall q qs, ~ In q qs -> disjoint qs -> disjoint (q::qs). 

(* subset definition. May turn it into bool type function. *)
Inductive sublist : list posi -> list posi -> Prop :=
   sublist_empty : forall qs, sublist nil qs
 | sublist_many : forall q qs1 qs2, In q qs2 -> sublist qs1 qs2 -> sublist (q::qs1) qs2.

Inductive type_aexp : list var -> aexp -> Prop :=
   | ba_type : forall env x, In x env -> type_aexp env x
   | num_type : forall env n, type_aexp env (Num n)
   | plus_type : forall env e1 e2, type_aexp env e1 -> type_aexp env e2 -> type_aexp env (APlus e1 e2)
   | mult_type : forall env e1 e2, type_aexp env e1 -> type_aexp env e2 -> type_aexp env (AMult e1 e2).

Inductive type_cbexp : list var -> cbexp -> Prop :=
  | ceq_type : forall env a b, type_aexp env a -> type_aexp env b -> type_cbexp env (CEq a b)
  | clt_type : forall env a b, type_aexp env a -> type_aexp env b -> type_cbexp env (CLt a b).

Inductive type_mu : list posi -> mu -> Prop :=
   type_add : forall qs v, disjoint qs -> type_mu qs (Add qs v)
 | type_less: forall qs q v, disjoint (q::qs) -> type_mu (q::qs) (Less qs v q)
 | type_eq:   forall qs q v, disjoint (q::qs) -> type_mu (q::qs) (Equal qs v q). 

(* Equivalence Relations among records *)
Inductive rec_eq : list qrecord -> list qrecord -> Prop :=
   join_eq : forall q1 q2 q3 q4 q5 q6 qs, rec_eq ((q1,q2,q3)::(q4,q5,q6)::qs) ((q1++q4,q2++q5,q3++q6)::qs)
 | nor_split_eq : forall q1 q2 qs, rec_eq ((nil,q1++q2,nil)::qs) ((nil,q1,nil)::(nil,q2,nil)::qs)
 | had_split_eq : forall q1 q2 qs, rec_eq ((q1++q2,nil,nil)::qs) ((q1,nil,nil)::(q2,nil,nil)::qs)
 | swap_eq : forall qs1 qs2, rec_eq (qs1++qs2) (qs2++qs1).

(* Type Rules. *)

Inductive ityping : list qrecord -> iota -> list qrecord -> Prop :=
   rec_eq_ty : forall ia T1 T2 T3, rec_eq T1 T2 -> ityping T2 ia T3 -> ityping T1 ia T3
 | ry_nor : forall p r T, ityping ((nil,([p]),nil)::T) (Ry p r) ((nil,nil,([p]))::T)
 | ry_rot : forall th T p r ps, rot th = (p::ps) -> ityping (th::T) (Ry p r) (th::T)
 | mu_nor : forall qs mu th T, type_mu qs mu -> sublist qs (nor th) -> ityping (th::T) (Ora mu) (th::T)
 | cu_nor : forall q qs ia th T, nor th = (q::qs) -> ityping ((nor_sub th qs)::T) ia ((nor_sub th qs)::T) -> ityping (th::T) (ICU q ia) (th::T)
 | cu_had : forall q qs ia th T, nor th = (q::qs) -> ityping ((had_sub th qs)::T) ia ((had_sub th qs)::T) -> ityping (th::T) (ICU q ia) (th::T)
 | iseq_ty : forall qa qb T1 T2 T3, ityping T1 qa T2 -> ityping T2 qb T3 -> ityping T1 (ISeq qa qb) T2.

Inductive etype : list var -> list qrecord -> exp -> list qrecord -> Prop :=
   next_ty : forall s p T, ityping T p T -> etype s T (Next p) T
 | had_ty : forall qs s T, etype s ((nil,qs,nil)::T) (Had qs) ((qs,nil,nil)::T)
 | new_ty : forall qs s T, disjoint qs -> set_inter_posi qs (flat_union T) = nil -> etype s T (New qs) ((nil,qs,nil)::T)
 | eseq_ty : forall s qa qb T1 T2 T3, etype s T1 qa T2 -> etype s T2 qb T3 -> etype s T1 (ESeq qa qb) T2
 | eif_ty : forall b e1 e2 s T T1, type_cbexp s b -> etype s T e1 T1 -> etype s T e2 T1 -> etype s T (IFa b e1 e2) T
 | mea_ty : forall x qs e s th T T1, sublist qs (rec_union th) -> etype (x::s) ((qrecord_diff th qs)::T) e T1 -> etype s (th::T) (Meas x  qs e) T1.


(* The type progress theorem. It says that given a aenv being empty, and the program type checked, 
      a program is either SKIP or can always be evaluated. *)
Lemma type_progress : 
    forall rmax T T' phi e , etype nil T e T' 
          -> exists r phi' e', @prog_sem rmax phi e r phi' e'.
Proof.
  intros rmax T T' phi e Htype.
  induction Htype.
  - (* Case: Next *)
    exists R1, (app_inst rmax phi p), ESKIP.
    apply iota_sem.

  -  (* Case: Had *)
    exists R1, (apply_hads phi qs), ESKIP.
    apply had_sem.
  - (* Case: New *)
    exists R1, (add_new phi qs), ESKIP.
    apply new_sem.
     - (* Case: ESeq *)
    destruct IHHtype1 as [r1 [phi1 [e1' Hprog1]]].
    destruct IHHtype2 as [r2 [phi2 [e2' Hprog2]]].
    exists r1, phi1, (e1' [;] qb).
    apply seq_sem_2. 
    assumption.
 - (* Case: IFa *)
    destruct (simp_bexp b) eqn:Hb.
    + (* Simplifiable boolean expression *)
       destruct b0.
      * (* Case: b evaluates to true *)
        exists R1, phi, e1.
        apply if_sem_1.
        assumption.
      * (* Case: b evaluates to false *)
        exists R1, phi, e2.
        apply if_sem_2. 
        assumption.
    + (* Case: b evaluates to None *)
      exists R1, phi, (IFa b e1 e2).
      apply if_sem_3.
      assumption.
 - (* Case:  Meas *)
  remember (apply_mea rmax phi qs (fun _ => false)) as mea_res.
  destruct mea_res as [phi' rv].
  exists rv, phi', (exp_subst_c e x (a_nat2fb (fun _ => false) (length qs))).
  apply mea_sem.
 auto.
Qed.

(* type preservation. The theorem showing that a well-typed program,
    when it has one step evaluation, the output program is also type checked. *)
Definition aenv_consist (aenv aenv': list var) := forall x, In x aenv -> In x aenv'.

Definition nor_consist (s: list posi) (phi: state) :=
  forall i, i < (fst phi) -> forall p, In p s -> exists v, (snd ((snd phi) i)) p = Nval v.

Definition rot_consist (s: list posi) (phi: state) :=
  forall i, i < (fst phi) -> forall p, In p s -> exists v, (snd ((snd phi) i)) p = Rval v.

Definition type_consist (T:list qrecord) (phi:state) :=
  forall s, In s T -> nor_consist (had s) phi /\ nor_consist (nor s) phi /\ rot_consist (rot s) phi.

Check prog_sem_ind.
Print etype.
Require Import Coq.Init.Logic.

Require Import Coq.Arith.PeanoNat. 
Lemma refl_equal_lemma : forall (A : Type) (x : A),
  refl_equal x = eq_refl x.
Proof.
  intros A x.
  apply eq_refl.     (* To assert that x = x holds *)
Qed.
Require Import Coq.Classes.RelationClasses.

(* Reflexivity of rec_eq *)
Axiom rec_eq_refl : forall x, rec_eq x x.
(* Symmetry of rec_eq *)
Axiom rec_eq_symmetry : forall x y, rec_eq x y -> rec_eq y x.
Definition rec_eq_Symmetric : Symmetric rec_eq := rec_eq_symmetry.
(* Declare rec_eq as Reflexive *)
Definition rec_eq_Reflexive : Reflexive rec_eq := rec_eq_refl.
Lemma fst_apply_hads : forall phi qs, fst (apply_hads phi qs) = fst phi.
Proof.
  intros phi qs.
  unfold apply_hads.
  induction qs as [| q qs' IHqs].
  - (* Base case: qs = [] *)
    reflexivity.
  - (* Inductive case: qs = q :: qs' *)
    simpl.
     rewrite IHqs.
    unfold add_had.
Admitted.
Axiom had_ty_cort : forall qs s T, etype s T (Had qs) T.
Axiom remove_empty_record : forall qs T,
  qs = [] ->
  rec_eq ((qs, [], []) :: T) T.
Lemma had_f_ty: forall qs s T, etype s ((nil, qs, nil) :: T) (Had qs) ((qs, nil, nil) :: T).
Proof.
  intros qs s T.
  apply had_ty.
Qed.
Lemma type_preservation:
  forall rmax (aenv: list var) T T' phi phi' e e' r, etype aenv T e T' ->  @prog_sem rmax phi e r phi' e' -> type_consist T phi -> exists aenv' T1 T2, 
    etype aenv' T1 e T2 /\ rec_eq T' T2 /\ type_consist T2 phi'.
Proof.
intros rmax aenv T T' phi phi' e e' r Htype Hsem Hconsist.
  induction Htype; inversion Hsem; subst.
  - (* Case: Next *)
    exists s, T, T.
    split; [|split].
    + apply next_ty. assumption.
    + clear Hsem.
     induction T.
     induction H.
     apply IHityping.
     exact Hconsist.
     apply rec_eq_refl.
     apply rec_eq_refl.
     apply rec_eq_refl.
     apply rec_eq_refl.
     apply rec_eq_refl.
     apply rec_eq_refl.
     apply rec_eq_refl.
     + induction Hsem; subst.
      exact Hconsist.
      apply IHHsem.
      clear Hsem.
     exact Hconsist.
     exact Hconsist.
     exact Hconsist.
     exact Hconsist.
     assert (H_preserved: type_consist T (add_new phi bl)).
     {
      specialize (Hconsist).
      admit.
     }
      apply H_preserved.
   
       assert (H_preserved: type_consist T (app_inst rmax phi e)).
      {
       specialize (Hconsist).
        admit. 
       }
        apply H_preserved.
       assert (H_preserved: type_consist T (apply_hads phi bl)).
        {
        specialize (Hconsist).
         admit.
         }
         apply H_preserved.
        specialize (Hconsist).
        assert (H_preserved: type_consist T phi').
        {
        admit.
        }
        apply H_preserved.
 - (* Case: Had *)
    exists s, ((nil, qs, nil)::T), ((qs, nil, nil)::T).
    split; [apply had_ty | split].
    + apply rec_eq_refl.
    + assert (H_preserved: type_consist ((qs, nil, nil)::T) (apply_hads phi qs)).
      {
        admit.
      }
      apply H_preserved.
  - (* Case: New *)
    exists s, T, ((nil, qs, nil)::T).
    split; [apply new_ty; assumption | split].
    + apply rec_eq_refl.
    + assert (H_preserved: type_consist ((nil, qs, nil)::T) (add_new phi qs)).
      {
                intros s' [Heq | Hin].
        * subst s'. split; [|split].
          - intros i Hi q Hq. contradiction.
          - intros i Hi q Hq. exists false.
            admit.
          - intros i Hi q Hq. contradiction.
        * specialize (Hconsist s' Hin).
          destruct Hconsist as [Hhad [Hnor Hrot]].
          split; [|split]; intros i Hi q Hq;
          try (apply Hhad; assumption);
          try (apply Hnor; assumption);
          try (apply Hrot; assumption).
           
      }
      apply H_preserved.
  - (* Case: ESeq *)
    intros.
    destruct IHHtype1.
     destruct IHHtype2.
     destruct Hsem.
      easy.
      easy.
      easy.
      easy.
      easy.
      easy.
      easy.
      easy.
      easy.
      easy.
      easy.
      easy.
      easy.
 - exists s, T1, T3.
 repeat split.


 
Admitted.

