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

Definition disjoint_record (qs: list qrecord) := disjoint (flat_union qs).

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
 | ref_eq : forall qs, rec_eq qs qs
 | join_eq : forall q1 q2 q3 q4 q5 q6 qs, rec_eq ((q1,q2,q3)::(q4,q5,q6)::qs) ((q1++q4,q2++q5,q3++q6)::qs)
 | nor_split_eq : forall q1 q2 qs, rec_eq ((nil,q1++q2,nil)::qs) ((nil,q1,nil)::(nil,q2,nil)::qs)
 | had_split_eq : forall q1 q2 qs, rec_eq ((q1++q2,nil,nil)::qs) ((q1,nil,nil)::(q2,nil,nil)::qs)
 | swap_eq : forall qs1 qs2, rec_eq (qs1++qs2) (qs2++qs1).

(* Type Rules. *)

Inductive flag : Set := CF | MF.

Inductive ityping : list qrecord -> flag -> iota -> list qrecord -> Prop :=
   (*rec_eq_ty : forall g ia T1 T2 T3, rec_eq T1 T2 -> ityping T2 g ia T3 -> ityping T1 g ia T3 *)
 | ry_nor : forall p r T, ityping ((nil,([p]),nil)::T) CF (Ry p r) ((nil,nil,([p]))::T)
 | ry_rot : forall g th T p r ps, rot th = (p::ps) -> ityping (th::T) g (Ry p r) (th::T)
 | mu_nor : forall g qs mu th T, type_mu qs mu -> sublist qs (nor th) -> ityping (th::T) g (Ora mu) (th::T)
 | cu_nor : forall g q qs ia th T, nor th = (q::qs) ->
                      ityping ((nor_sub th qs)::T) MF ia ((nor_sub th qs)::T) -> ityping (th::T) g (ICU q ia) (th::T)
 | cu_had : forall g q qs ia th T, had th = (q::qs) -> 
                      ityping ((had_sub th qs)::T) MF ia ((had_sub th qs)::T) -> ityping (th::T) g (ICU q ia) (th::T)
 | iseq_ty : forall g qa qb T1 T2 T3, ityping T1 g qa T2 -> ityping T2 g qb T3 -> ityping T1 g (ISeq qa qb) T3.

Inductive etype : list var -> list qrecord -> exp -> list qrecord -> Prop :=
 | skip_ty : forall T s, etype s T ESKIP T
 | next_ty : forall s p T T1, ityping T CF p T1 -> etype s T (Next p) T1
 | had_ty : forall qs s T, etype s ((nil,qs,nil)::T) (Had qs) ((qs,nil,nil)::T)
 | new_ty : forall qs s T, disjoint qs -> set_inter_posi qs (flat_union T) = nil -> etype s T (New qs) ((nil,qs,nil)::T)
 | eseq_ty : forall s qa qb T1 T2 T3, etype s T1 qa T2 -> etype s T2 qb T3 -> etype s T1 (ESeq qa qb) T3
 | eif_ty : forall b e1 e2 s T T1, type_cbexp s b -> etype s T e1 T1 -> etype s T e2 T1 -> etype s T (IFa b e1 e2) T1
 | mea_ty : forall x qs e s th T T1, sublist qs (rec_union th) -> etype (x::s) ((qrecord_diff th qs)::T) e T1 -> etype s (th::T) (Meas x  qs e) T1.


(* The type progress theorem. It says that given a aenv being empty, and the program type checked, 
      a program is either SKIP or can always be evaluated. *)
Lemma aexp_not_none: forall aenv b, aenv = nil -> type_aexp aenv b -> simp_aexp b <> None.
Proof.
  intros. induction H0; subst. simpl in *. easy.
  easy. simpl in *. destruct (simp_aexp e1) eqn:eq1.
  destruct (simp_aexp e2) eqn:eq2. easy.
  assert (([] : list var) = []). easy. apply IHtype_aexp2 in H. easy.
  assert (([] : list var) = []). easy. apply IHtype_aexp1 in H. easy.
  simpl in *. destruct (simp_aexp e1) eqn:eq1.
  destruct (simp_aexp e2) eqn:eq2. easy.
  assert (([] : list var) = []). easy. apply IHtype_aexp2 in H. easy.
  assert (([] : list var) = []). easy. apply IHtype_aexp1 in H. easy.
Qed.

Lemma bool_not_none: forall aenv b, aenv = nil -> type_cbexp aenv b -> simp_bexp b <> None.
Proof.
  intros. induction H0; subst.
  simpl in *.
  assert (simp_aexp a <> None). eapply aexp_not_none; try easy.
  assert (simp_aexp b <> None). eapply aexp_not_none; try easy.
  destruct (simp_aexp a) eqn:eq1.
  destruct (simp_aexp b) eqn:eq2. easy. easy. easy.
  simpl in *.
  assert (simp_aexp a <> None). eapply aexp_not_none; try easy.
  assert (simp_aexp b <> None). eapply aexp_not_none; try easy.
  destruct (simp_aexp a) eqn:eq1.
  destruct (simp_aexp b) eqn:eq2. easy. easy. easy.
Qed.

Lemma type_progress : 
    forall rmax aenv T T' phi e , etype aenv T e T' -> aenv = nil 
          -> e = ESKIP \/ exists r phi' e', @prog_sem rmax phi e r phi' e'.
Proof.
  intros rmax aenv T T' phi e Htype.
  induction Htype; intros; subst.
  - (* case SKIP *)
    left. easy.
  - (* Case: Next *)
    right.
    exists R1, (app_inst rmax phi p), ESKIP.
    apply iota_sem.

  -  (* Case: Had *)
    right.
    exists R1, (apply_hads phi qs), ESKIP.
    apply had_sem.
  - (* Case: New *)
    right.
    exists R1, (add_new phi qs), ESKIP.
    apply new_sem.
  - (* Case: ESeq *)
    right.
    destruct IHHtype1 as [EP1 | [r1 [phi1 [e1' Hprog1]]]]. easy.
    subst.
    exists R1, phi, qb.
    apply seq_sem_1. subst.
    exists r1, phi1, (e1' [;] qb).
    apply seq_sem_2. 
    assumption.
 - (* Case: IFa *)
    right.
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
      apply bool_not_none in H. easy. easy.
 - (* Case:  Meas *)
  right.
  remember (apply_mea rmax phi qs (fun _ => false)) as mea_res.
  destruct mea_res as [phi' rv].
  exists rv, phi', (exp_subst_c e x (a_nat2fb (fun _ => false) (length qs))).
  apply mea_sem.
 auto.
Qed.

(* type preservation. The theorem showing that a well-typed program,
    when it has one step evaluation, the output program is also type checked. *)
Definition aenv_consist (aenv aenv': list var) := forall x, In x aenv -> In x aenv'.

Definition nor_consist_eta (s:list posi) (phi:eta_state) :=
   forall p, In p s -> exists v, phi p = Nval v.

Definition nor_consist (s: list posi) (phi: state) :=
  forall i, i < (fst phi) -> nor_consist_eta s (snd ((snd phi) i)).

Definition rot_consist_eta (s: list posi) (phi: eta_state) :=
  forall p, In p s -> exists v, phi p = Rval v.

Definition rot_consist (s: list posi) (phi: state) :=
  forall i, i < (fst phi) -> rot_consist_eta s (snd ((snd phi) i)).

Definition type_consist_eta (T:list qrecord) (phi:eta_state) :=
 forall s, In s T -> nor_consist_eta (had s) phi /\ nor_consist_eta (nor s) phi /\ rot_consist_eta (rot s) phi.


Definition type_no_change_eta (T:list qrecord) (phi phi':eta_state) :=
 forall s, ~ In s (flat_union T) -> phi s = phi' s.

Definition type_consist (T:list qrecord) (phi:state) :=
  forall i, i < fst phi -> type_consist_eta T (snd ((snd phi) i)).

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

Lemma had_f_ty: forall qs s T, etype s ((nil, qs, nil) :: T) (Had qs) ((qs, nil, nil) :: T).
Proof.
  intros qs s T.
  apply had_ty.
Qed.

Lemma disjoint_itype : forall g T T1 e, ityping T g e T1 -> disjoint_record T -> disjoint_record T1.
Proof.
  intros. induction H.
  unfold disjoint_record in *. simpl in *. easy.
  easy. easy. easy. easy.
  apply IHityping2. apply IHityping1. easy.
Qed.

Lemma rec_union_same : forall a b c d e f, a ++ b ++ c = d ++ e ++ f -> rec_union (a,b,c) = rec_union (d,e,f).
Proof.
  intros.
  unfold rec_union,had,nor in *. simpl in *. easy.
Qed.

Definition DIn (q:posi) (s:qrecord) := In q (fst (fst s)) \/ In q (snd (fst s)) \/ In q (snd s).

Axiom disjoint_not_in : forall q s s' T, disjoint_record (s::T) -> DIn q s -> In s' T -> ~ DIn q s'.

Axiom disjoint_not_rot_had: forall T q s, disjoint_record (s :: T) -> In q (rot s) -> ~ In q (had s).

Axiom disjoint_not_rot_nor: forall T q s, disjoint_record (s :: T) -> In q (rot s) -> ~ In q (nor s).

Lemma hadtoDIn : forall q s, In q (had s) -> DIn q s.
Proof.
  intros. unfold had in *. destruct s. destruct p. simpl in *. unfold DIn in *.
  left. easy.
Qed.

Lemma nortoDIn : forall q s, In q (nor s) -> DIn q s.
Proof.
  intros. unfold nor in *. destruct s. destruct p. simpl in *. unfold DIn in *.
  right. left. easy.
Qed.

Lemma rottoDIn : forall q s, In q (rot s) -> DIn q s.
Proof.
  intros. unfold nor in *. destruct s. destruct p. simpl in *. unfold DIn in *.
  right. right. easy.
Qed.

Lemma In_conv {A:Type}: forall (q: A) q' s, In q s -> ~ In q' s -> q <> q'.
Proof.
  intros. induction s. simpl in *. easy.
  simpl in *. apply not_or_and in H0. destruct H0. destruct H. rewrite H in *. easy.
  apply IHs; try easy.
Qed.

Lemma DIn_prop : forall q q' s, DIn q s -> ~ DIn q' s -> q <> q'.
Proof.
  intros. destruct s. destruct p.
  unfold DIn in *.
  apply not_or_and in H0. destruct H0. apply not_or_and in H1. destruct H1.
  destruct H. simpl in *. eapply In_conv. apply H. easy.
  destruct H. simpl in *. eapply In_conv. apply H. easy.
  simpl in *. eapply In_conv. apply H. easy. 
Qed.

Axiom mu_handling_preserve: forall rmax qs mu th T phi, 
  disjoint_record (th :: T) -> type_consist_eta (th :: T) phi -> sublist qs (nor th) -> 
    type_consist_eta (th :: T) (mu_handling rmax mu phi) /\ type_no_change_eta (th::T) (mu_handling rmax mu phi) phi.

Axiom etype_subst: forall x s T e T1 v, etype (x :: s) T e T1 -> etype s T (exp_subst_c e x v) T1.

Axiom mea_type_consist:  forall rmax qs th T phi phi' r v, 
 type_consist (th :: T) phi -> apply_mea rmax phi qs v = (phi', r) -> type_consist (qrecord_diff th qs :: T) phi'.

Axiom had_type_consist: forall qs T phi, disjoint_record (([], qs, []) :: T) -> type_consist (([], qs, []) :: T) phi ->
type_consist ((qs, [], []) :: T) (apply_hads phi qs).


Lemma ford_left_head : 
  forall T a qs, fold_left (fun (a0 : list posi) (b : qrecord) => a0 ++ had b ++ nor b ++ rot b) T
  (a :: qs ++ []) =
a
:: fold_left (fun (a0 : list posi) (b : qrecord) => a0 ++ had b ++ nor b ++ rot b)
     T (nor ([], qs, []) ++ []).
Proof.
  intros.
  rewrite <- fold_left_rev_right.
  rewrite <- fold_left_rev_right.
  remember (rev T) as Q. clear HeqQ.
  induction Q. simpl in *. easy.
  simpl in *.
  rewrite IHQ. easy.
Qed.

Lemma fold_left_head_1:
   forall (T:list qrecord) (a: list posi), 
    fold_left (fun (a0 : list posi) (b : qrecord) => a0 ++ rec_union b)  T a 
         = a ++ (fold_left (fun (a0 : list posi) (b : qrecord) => a0 ++ rec_union b) T nil).
Proof.
  intros.
  rewrite <- fold_left_rev_right.
  rewrite <- fold_left_rev_right.
  remember (rev T) as Q. clear HeqQ.
  induction Q; simpl in *.
  rewrite app_nil_r. easy.
  rewrite IHQ. rewrite app_assoc. easy.
Qed.

Axiom disjoint_move : forall l0 qs l, 
     disjoint (l0 ++ qs ++ l) <-> disjoint (qs ++ l0 ++ l).

Lemma not_in_app {A} : forall (a:A) l1 l2, ~ In a (l1 ++ l2) -> ~ In a l1 /\ ~ In a l2.
Proof.
  intros. induction l1. simpl in *. split. easy. easy. simpl in *.
  apply not_or_and in H. destruct H. apply IHl1 in H0. destruct H0.
  split; try easy. apply and_not_or. split; try easy.
Qed.

Lemma ityping_not_in: forall T g e T1 s, ityping T g e T1 -> ~ In s (flat_union T1) -> ~ In s (flat_union T).
Proof.
  intros. induction H; unfold flat_union in *; simpl in *.
  rewrite fold_left_head_1 in *.
  unfold rec_union, had, nor in *; simpl in *. easy. 1-4:easy.
  apply IHityping1. apply IHityping2. easy.
Qed.

Lemma itype_preservation: 
   forall rmax g T T1 phi e, disjoint_record T -> type_consist_eta T phi 
          -> ityping T g e T1 -> type_consist_eta T1 (instr_sem rmax e phi) /\ type_no_change_eta T1 (instr_sem rmax e phi) phi.
Proof.
  intros.
  generalize dependent phi.
  induction H1; simpl in *; intros.
 (* ry gate *)
  split.
  unfold type_consist_eta in *. intros.
  inv H1. split. simpl in *.
  unfold nor_consist_eta in *. intros. inv H1.
  split. 
  unfold nor_consist_eta in *. intros. inv H1.
  unfold rot_consist_eta in *. intros. inv H1.
  unfold ry_rotate in *.
  specialize (H0 ([], [p0], [])). simpl in *.
  assert ((nil:(list posi), [p0], nil:(list posi)) = (nil, [p0], nil) \/ In (nil, [p0], nil) T).
  left. easy. apply H0 in H1.
  destruct H1. destruct H2. unfold nor_consist_eta in *.
  specialize (H2 p0). simpl in *.
  assert (p0 = p0 \/ False). left ; easy.
  apply H2 in H4. destruct H4. rewrite H4.
  destruct x. rewrite eupdate_index_eq.
  exists ((angle_sub (pi32 rmax) r rmax)). easy.
  rewrite eupdate_index_eq.
  exists r. easy.
  easy.
  split.
  unfold nor_consist_eta in *. intros.
  unfold ry_rotate.
  destruct (phi p). destruct b.
  rewrite eupdate_index_neq. 
  assert (In s (([], [p], []) :: T)) by (right; easy). apply H0 in H3.
  destruct H3 as [G1 [G2 G3]].
  apply G1. easy.
  apply hadtoDIn in H1.
  apply disjoint_not_in with (q := p) (s' := s) in H as X1; try easy.
  assert (p0 <> p).
  apply DIn_prop with (s := s); try easy.
  intros R. subst. easy.
  unfold DIn. simpl in *. right. left. left. easy.
  rewrite eupdate_index_neq. 
  assert (In s (([], [p], []) :: T)) by (right; easy). apply H0 in H3.
  destruct H3 as [G1 [G2 G3]].
  apply G1. easy.
  apply hadtoDIn in H1.
  apply disjoint_not_in with (q := p) (s' := s) in H as X1; try easy.
  assert (p0 <> p).
  apply DIn_prop with (s := s); try easy.
  intros R. subst. easy.
  unfold DIn. simpl in *. right. left. left. easy.
  rewrite eupdate_index_neq. 
  assert (In s (([], [p], []) :: T)) by (right; easy). apply H0 in H3.
  destruct H3 as [G1 [G2 G3]].
  apply G1. easy.
  apply hadtoDIn in H1.
  apply disjoint_not_in with (q := p) (s' := s) in H as X1; try easy.
  assert (p0 <> p).
  apply DIn_prop with (s := s); try easy.
  intros R. subst. easy.
  unfold DIn. simpl in *. right. left. left. easy.
  split.
  unfold nor_consist_eta in *. intros.
  unfold ry_rotate.
  destruct (phi p). destruct b.
  rewrite eupdate_index_neq. 
  assert (In s (([], [p], []) :: T)) by (right; easy). apply H0 in H3.
  destruct H3 as [G1 [G2 G3]].
  apply G2. easy.
  apply nortoDIn in H1.
  apply disjoint_not_in with (q := p) (s' := s) in H as X1; try easy.
  assert (p0 <> p).
  apply DIn_prop with (s := s); try easy.
  intros R. subst. easy.
  unfold DIn. simpl in *. right. left. left. easy.
  rewrite eupdate_index_neq. 
  assert (In s (([], [p], []) :: T)) by (right; easy). apply H0 in H3.
  destruct H3 as [G1 [G2 G3]].
  apply G2. easy.
  apply nortoDIn in H1.
  apply disjoint_not_in with (q := p) (s' := s) in H as X1; try easy.
  assert (p0 <> p).
  apply DIn_prop with (s := s); try easy.
  intros R. subst. easy.
  unfold DIn. simpl in *. right. left. left. easy.
  rewrite eupdate_index_neq. 
  assert (In s (([], [p], []) :: T)) by (right; easy). apply H0 in H3.
  destruct H3 as [G1 [G2 G3]].
  apply G2. easy.
  apply nortoDIn in H1.
  apply disjoint_not_in with (q := p) (s' := s) in H as X1; try easy.
  assert (p0 <> p).
  apply DIn_prop with (s := s); try easy.
  intros R. subst. easy.
  unfold DIn. simpl in *. right. left. left. easy.
  unfold rot_consist_eta in *. intros.
  unfold ry_rotate.
  destruct (phi p). destruct b.
  rewrite eupdate_index_neq. 
  assert (In s (([], [p], []) :: T)) by (right; easy). apply H0 in H3.
  destruct H3 as [G1 [G2 G3]].
  apply G3. easy.
  apply rottoDIn in H1.
  apply disjoint_not_in with (q := p) (s' := s) in H as X1; try easy.
  assert (p0 <> p).
  apply DIn_prop with (s := s); try easy.
  intros R. subst. easy.
  unfold DIn. simpl in *. right. left. left. easy.
  rewrite eupdate_index_neq. 
  assert (In s (([], [p], []) :: T)) by (right; easy). apply H0 in H3.
  destruct H3 as [G1 [G2 G3]].
  apply G3. easy.
  apply rottoDIn in H1.
  apply disjoint_not_in with (q := p) (s' := s) in H as X1; try easy.
  assert (p0 <> p).
  apply DIn_prop with (s := s); try easy.
  intros R. subst. easy.
  unfold DIn. simpl in *. right. left. left. easy.
  rewrite eupdate_index_neq. 
  assert (In s (([], [p], []) :: T)) by (right; easy). apply H0 in H3.
  destruct H3 as [G1 [G2 G3]].
  apply G3. easy.
  apply rottoDIn in H1.
  apply disjoint_not_in with (q := p) (s' := s) in H as X1; try easy.
  assert (p0 <> p).
  apply DIn_prop with (s := s); try easy.
  intros R. subst. easy.
  unfold DIn. simpl in *. right. left. left. easy.
  unfold type_no_change_eta in *.
  intros. unfold ry_rotate.
  assert (p <> s).
  unfold flat_union,rec_union in *. simpl in *.
  replace ([p]) with (p :: [] ++ []) in H1 by easy.
  rewrite ford_left_head in H1. simpl in *.
  apply not_or_and  in H1. destruct H1.
  intros R. subst. easy.
  destruct (phi p). destruct b.
  rewrite eupdate_index_neq; easy.
  rewrite eupdate_index_neq; easy.
  rewrite eupdate_index_neq; easy.
  (* Ry gate Rot type *)
  split. 
  unfold type_consist_eta in *.
  intros. inv H2.
  assert (In p (rot s)). rewrite H0. simpl;left;easy.
  apply disjoint_not_rot_had with (T := T) in H2 as G1; try easy.
  apply disjoint_not_rot_nor with (T := T) in H2 as G2; try easy.
  unfold nor_consist_eta in *. split.
  intros.
  apply In_conv with (q' := p) in H3 as G3; try easy.
  assert (In s (s::T)). left; easy. apply H1 in H4.
  destruct H4 as [X1 [X2 X3]].
  unfold ry_rotate in *.
  destruct (phi p). destruct b.
  rewrite eupdate_index_neq.
  apply X1. easy. intros R. subst. easy.
  rewrite eupdate_index_neq.
  apply X1. easy. intros R. subst. easy.
  rewrite eupdate_index_neq.
  apply X1. easy. intros R. subst. easy.
  split.
  intros.
  apply In_conv with (q' := p) in H3 as G3; try easy.
  assert (In s (s::T)). left; easy. apply H1 in H4.
  destruct H4 as [X1 [X2 X3]].
  unfold ry_rotate in *.
  destruct (phi p). destruct b.
  rewrite eupdate_index_neq.
  apply X2. easy. intros R. subst. easy.
  rewrite eupdate_index_neq.
  apply X2. easy. intros R. subst. easy.
  rewrite eupdate_index_neq.
  apply X2. easy. intros R. subst. easy.
  unfold rot_consist_eta in *. intros.
  unfold ry_rotate in *.
  assert (In s (s::T)). left; easy. apply H1 in H4.
  destruct H4 as [X1 [X2 X3]].
  apply X3 in H3. destruct H3.
  destruct (phi p). destruct b.
  bdestruct (posi_eq p p0). subst.
  rewrite eupdate_index_eq.
  exists (angle_sub (pi32 rmax) r rmax). easy.
  rewrite eupdate_index_neq.
  exists x. easy. easy.
  bdestruct (posi_eq p p0). subst.
  rewrite eupdate_index_eq.
  exists r. easy.
  rewrite eupdate_index_neq.
  exists x. easy. easy.
  bdestruct (posi_eq p p0). subst.
  rewrite eupdate_index_eq.
  exists (angle_sum n r rmax). easy.
  rewrite eupdate_index_neq.
  exists x. easy. easy.
  assert (In p (rot th)). rewrite H0. left; easy.
  apply rottoDIn in H2 as G1.
  apply disjoint_not_in with (s' := s) (T := T) in G1 as G2; try easy.
  assert (In s (th :: T)) as G3.
  right; easy.
  specialize (H1 s G3).
  destruct H1 as [X1 [X2 X3]].
  unfold nor_consist_eta, ry_rotate in *. split.
  intros.
  apply X1 in H1 as X4. destruct X4.
  apply hadtoDIn in H1.
  apply DIn_prop with (q' := p) in H1 as X5; try easy.
  destruct (phi p). destruct b.
  rewrite eupdate_index_neq.
  exists x. easy. intros R. subst. easy.
  rewrite eupdate_index_neq.
  exists x. easy. intros R. subst. easy.
  rewrite eupdate_index_neq.
  exists x. easy. intros R. subst. easy.
  split.
  intros.
  apply X2 in H1 as X4. destruct X4.
  apply nortoDIn in H1.
  apply DIn_prop with (q' := p) in H1 as X5; try easy.
  destruct (phi p). destruct b.
  rewrite eupdate_index_neq.
  exists x. easy. intros R. subst. easy.
  rewrite eupdate_index_neq.
  exists x. easy. intros R. subst. easy.
  rewrite eupdate_index_neq.
  exists x. easy. intros R. subst. easy.
  unfold rot_consist_eta in *.
  intros.
  apply X3 in H1 as X4. destruct X4.
  apply rottoDIn in H1.
  apply DIn_prop with (q' := p) in H1 as X5; try easy.
  destruct (phi p). destruct b.
  rewrite eupdate_index_neq.
  exists x. easy. intros R. subst. easy.
  rewrite eupdate_index_neq.
  exists x. easy. intros R. subst. easy.
  rewrite eupdate_index_neq.
  exists x. easy. intros R. subst. easy.
  unfold type_no_change_eta in *.
  intros. unfold ry_rotate.
  assert (p <> s).
  unfold flat_union in *. simpl in *.
  rewrite fold_left_head_1 in H2.
  unfold rec_union in *.
  rewrite H0 in H2. simpl in *.
  apply not_in_app in H2. destruct H2.
  apply not_in_app in H2. destruct H2. apply not_in_app in H4. destruct H4.
  simpl in *. apply not_or_and in H5. destruct H5. easy.
  destruct (phi p). destruct b.
  rewrite eupdate_index_neq; easy.
  rewrite eupdate_index_neq; easy.
  rewrite eupdate_index_neq; easy.
  (* Oracle *)
  specialize (mu_handling_preserve rmax qs mu th T phi H H2 H1) as G1. easy.
  (* ICU Nor *)
  unfold nor, nor_sub,had in *. destruct th. destruct p. simpl in *. subst.
  assert (disjoint_record ((l0, qs, l) :: T)).
  clear H1 H2 IHityping.
  unfold disjoint_record in *. 
  unfold flat_union in *. simpl in *.
  rewrite fold_left_head_1 in *.
  remember (fold_left (fun (a0 : list posi) (b : qrecord) => a0 ++ rec_union b) T []) as Q.
  clear HeqQ.
  unfold rec_union,nor,had in *; simpl in *.
  rewrite <- app_assoc with (n := Q) in H.
  rewrite app_comm_cons in H.
  rewrite <- app_assoc with (n := Q) in H.
  rewrite disjoint_move in H.
  rewrite <- app_comm_cons in H.
  inv H.
  rewrite disjoint_move in H3.
  rewrite <- app_assoc with (n := Q).
  rewrite <- app_assoc with (n := Q). easy.
  assert (type_consist_eta ((l0, qs, l) :: T) phi).
  clear H0 IHityping H1.
  unfold type_consist_eta in *.
  intros. simpl in *. destruct H0. subst.
  unfold had,nor,rot,nor_consist_eta in *; simpl in *.
  assert ((l0, q :: qs, l) = (l0, q :: qs, l) \/ In (l0, q :: qs, l) T).
  left. easy.
  apply H2 in H0. destruct H0 as [X1 [X2 X3]].
  split. intros.
  apply X1. easy.
  split. intros. apply X2. simpl. right. easy.
  apply X3.
  assert ((l0, q :: qs, l) = s \/ In s T). right. easy.
  apply H2 in H1. destruct H1 as [X1 [X2 X3]].
  easy.
  destruct (IHityping H0 phi H3) as [G1 G2].
  split.
  assert (~ In q (flat_union ((l0, qs, l) :: T))).
  simpl in *.
  clear IHityping H1 H3 G1 G2.
  unfold disjoint_record in H.
  unfold flat_union in *. simpl in *.
  rewrite fold_left_head_1 in H. rewrite fold_left_head_1.
  unfold rec_union,had,nor in *. simpl in *.
  remember (fold_left
         (fun (a0 : list posi) (b : qrecord) =>
          a0 ++ fst (fst b) ++ snd (fst b) ++ rot b) T []) as Q. clear HeqQ.
  rewrite <- app_assoc with (n := Q) in H.
  rewrite app_comm_cons in H.
  rewrite <- app_assoc in H.
  rewrite disjoint_move in H.
  rewrite <- app_comm_cons in H.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  inv H.
  apply not_in_app in H4. destruct H4.
  apply not_in_app in H1. destruct H1.
  intros R.
  apply in_app_or in R. destruct R; try easy.
  apply in_app_or in H4. destruct H4; try easy.
  destruct (phi q). destruct b.
  unfold type_consist_eta in *.
  intros. simpl in *. destruct H5. subst.
  unfold had,nor,rot,nor_consist_eta in *; simpl in *.
  assert ((l0, qs, l) = (l0, qs, l) \/ In (l0, qs, l) T).
  left. easy.
  apply G1 in H5. destruct H5 as [X1 [X2 X3]]. simpl in *.
  split. intros.
  apply X1. easy.
  split. intros. destruct H5. subst. apply G2 in H4. rewrite H4.
  assert ((l0, p :: qs, l) = (l0, p :: qs, l) \/ In (l0, p :: qs, l) T).
  left. easy. apply H2 in H5. destruct H5 as [X4 [X5 X6]].
  apply X5. simpl in *. left. easy.
  apply X2. simpl. easy.
  apply X3.
  assert ((l0, qs, l) = s \/ In s T). right. easy.
  apply G1 in H6. destruct H6 as [X1 [X2 X3]].
  easy. easy. easy.
  destruct (phi q). destruct b.
  unfold type_no_change_eta in *.
  intros. apply G2.
  clear H0 H H2 IHityping H1 H3 G1 G2.
  unfold flat_union in *. simpl in *.
  rewrite fold_left_head_1 in H4. rewrite fold_left_head_1.
  unfold rec_union,nor,had in *. simpl in *.
  remember (fold_left
          (fun (a0 : list posi) (b : qrecord) =>
           a0 ++ fst (fst b) ++ snd (fst b) ++ rot b) T []) as Q.
  clear HeqQ.
  apply not_in_app in H4. destruct H4. apply not_in_app in H.
  destruct H. simpl in *.
  intros R.
  apply in_app_or in R.
  destruct R; try easy.
  apply in_app_or in H2.
  destruct H2; try easy.
  apply not_or_and in H1. destruct H1. easy.
  unfold type_no_change_eta in *. intros. easy.
  unfold type_no_change_eta in *. intros. easy.
  (* ICU Had *)
  unfold had_sub, nor ,had in *. destruct th. destruct p. simpl in *. subst.
  assert (disjoint_record ((qs, l1, l) :: T)).
  clear H1 H2 IHityping.
  unfold disjoint_record in *. 
  unfold flat_union in *. simpl in *.
  rewrite fold_left_head_1 in *.
  remember (fold_left (fun (a0 : list posi) (b : qrecord) => a0 ++ rec_union b) T []) as Q.
  clear HeqQ.
  unfold rec_union,nor,had in *; simpl in *.
  rewrite <- app_assoc with (n := Q) in H.
  rewrite <- app_assoc with (n := Q) in H.
  inv H.
  rewrite <- app_assoc with (n := Q).
  rewrite <- app_assoc with (n := Q). easy.
  assert (type_consist_eta ((qs, l1, l) :: T) phi).
  clear H IHityping H1.
  unfold type_consist_eta in *.
  intros. simpl in *. destruct H. subst.
  unfold had,nor,rot,nor_consist_eta in *; simpl in *.
  assert ((q :: qs, l1, l) = (q :: qs, l1, l) \/ In (q :: qs, l1, l) T).
  left. easy.
  apply H2 in H. destruct H as [X1 [X2 X3]].
  split. intros.
  apply X1. simpl in *. right. easy.
  split. intros. apply X2. simpl. easy.
  apply X3.
  assert ((q :: qs, l1, l) = s \/ In s T). right. easy.
  apply H2 in H1. destruct H1 as [X1 [X2 X3]].
  easy.
  destruct (IHityping H0 phi H3) as [G1 G2].
  split.
  assert (~ In q (flat_union ((qs, l1, l) :: T))).
  simpl in *.
  clear IHityping H1 H3 G1 G2.
  unfold disjoint_record in H.
  unfold flat_union in *. simpl in *.
  rewrite fold_left_head_1 in H. rewrite fold_left_head_1.
  unfold rec_union,had,nor in *. simpl in *.
  remember (fold_left
            (fun (a0 : list posi) (b : qrecord) =>
             a0 ++ fst (fst b) ++ snd (fst b) ++ rot b) T []) as Q. clear HeqQ.
  inv H. easy.
  destruct (phi q). destruct b.
  unfold type_consist_eta in *.
  intros. simpl in *. destruct H5. subst.
  unfold had,nor,rot,nor_consist_eta in *; simpl in *.
  assert ((qs, l1, l) = (qs, l1, l) \/ In (qs, l1, l) T).
  left. easy.
  apply G1 in H5. destruct H5 as [X1 [X2 X3]]. simpl in *.
  split. intros.
  destruct H5. subst. apply G2 in H4. rewrite H4.
  assert ((p :: qs, l1, l) = (p :: qs, l1, l) \/ In (p :: qs, l1, l) T).
  left. easy. apply H2 in H5. destruct H5 as [X4 [X5 X6]].
  apply X4. simpl in *. left. easy.
  apply X1. easy.
  split. intros.
  apply X2. simpl. easy.
  apply X3.
  assert ((qs, l1, l) = s \/ In s T). right. easy.
  apply G1 in H6. destruct H6 as [X1 [X2 X3]].
  easy. easy. easy.
  destruct (phi q). destruct b.
  unfold type_no_change_eta in *.
  intros. apply G2.
  clear H0 H H2 IHityping H1 H3 G1 G2.
  unfold flat_union in *. simpl in *.
  rewrite fold_left_head_1 in H4. rewrite fold_left_head_1.
  unfold rec_union,nor,had in *. simpl in *.
  remember (fold_left
          (fun (a0 : list posi) (b : qrecord) =>
           a0 ++ fst (fst b) ++ snd (fst b) ++ rot b) T []) as Q.
  clear HeqQ.
  apply not_or_and in H4. destruct H4. easy.
  unfold type_no_change_eta in *. intros. easy.
  unfold type_no_change_eta in *. intros. easy.
  (* Seq *)
  apply disjoint_itype in H1_ as G1; try easy.
  destruct (IHityping1 H phi H0) as [X1 X2].
  destruct (IHityping2 G1 (instr_sem rmax qa phi) X1) as [X3 X4].
  split. easy.
  unfold type_no_change_eta in *.
  intros. rewrite X4; try easy.
  rewrite X2. easy.
  apply ityping_not_in with (s := s) in H1_0; try easy.
Qed.


Lemma itype_preservation_app: forall n rmax g T T1 phi e,
   (forall i, i < n -> type_consist_eta T (snd (phi i))) -> disjoint_record T -> ityping T g e T1 ->
     (forall i, i < n -> type_consist_eta T1 (snd (app_inst' rmax n phi e i))).
Proof.
  induction n;intros; simpl in *. lia.
  assert (forall i, i < n -> type_consist_eta T (snd (phi i))).
  intros. apply H. lia.
  specialize (IHn rmax g T T1 phi e H3 H0 H1).
  bdestruct (i =? n). subst.
  rewrite update_index_eq.
  specialize (H n). apply H in H2. simpl in *.
  specialize (itype_preservation rmax g T T1 (snd (phi n)) e H0 H2 H1) as X1. easy.
  rewrite update_index_neq. apply IHn. lia. lia.
Qed.

Lemma add_elem_same_p : forall m i st p, i < m -> exists v, snd (add_new_elem m st p i) p = Nval v.
Proof.
  induction m; intros. lia.
  simpl in *.
  bdestruct (i =? m). subst.
  rewrite update_index_eq. unfold add_new_eta. simpl. rewrite eupdate_index_eq. exists false. easy.
  rewrite update_index_neq. apply IHm. lia. lia.
Qed.

Lemma add_elem_same_not : forall m i st p q, q <> p -> snd (add_new_elem m st q i) p = snd (st i) p.
Proof.
  induction m; intros.
  simpl in *. easy. simpl in *.
  bdestruct (i =? m). subst.
  rewrite update_index_eq. unfold add_new_eta;simpl in *.
  rewrite eupdate_index_neq. easy. easy.
  rewrite update_index_neq. apply IHm. easy. lia.
Qed.

Lemma member_not_in_set: forall T a s, set_mem posi_eq_dec a (flat_union T) = false -> In s T -> ~ In a (rec_union s).
Proof.
  induction T; intros; unfold flat_union in *; simpl in *.
  easy. destruct H0. subst.
  apply set_mem_complete1 in H.
  rewrite <- fold_left_rev_right in H. simpl in *.
  remember (rev T) as Q. clear IHT HeqQ.
  induction Q. simpl in *. easy. simpl in *. apply IHQ.
  remember (fold_right
         (fun (y : qrecord) (x : list posi) =>
          x ++ rec_union y) (rec_union s) Q ) as st.
  intros R. assert (set_In a0 st \/ set_In a0 (rec_union a)). left. easy.
  apply in_or_app in H0. easy.
  apply (IHT a0) in H0. easy.
  apply set_mem_complete1 in H. apply set_mem_complete2.
  rewrite <- fold_left_rev_right in H.
  rewrite <- fold_left_rev_right.
  remember (rev T) as Q. clear IHT HeqQ H0.
  induction Q. simpl in *. easy.
  simpl in *.
  remember (fold_right
         (fun (y : qrecord) (x : list posi) =>
          x ++ rec_union y) (rec_union a) Q) as V.
  assert (~ set_In a0 V).
  intros R. assert (set_In a0 (V ++ rec_union a1)). apply in_or_app. left. easy.
  easy. apply IHQ in H0.
  remember ((fold_right
          (fun (y : qrecord) (x : list posi) =>
           x ++ rec_union y) [] Q)) as W.
  intros R. apply in_app_or in R. destruct R. easy.
  assert (set_In a0 (V ++ rec_union a1)). apply in_or_app. right. easy. easy.
Qed.


Lemma type_preservation:
  forall rmax (aenv: list var) T T' phi phi' e e' r, disjoint_record T -> etype aenv T e T' 
        ->  @prog_sem rmax phi e r phi' e' -> type_consist T phi -> exists T1, 
    etype aenv T1 e' T' /\ type_consist T1 phi'.
Proof.
intros rmax aenv T T' phi phi' e e' r HDis Htype Hsem Hconsist.
generalize dependent e'.
  induction Htype.
  - (* Case: SKIP *) intros. inv Hsem.
  - (* Case: Next *)
    intros. inv Hsem.
    exists T1.
    split. constructor.
    unfold type_consist in *.
    intros. unfold app_inst in *. simpl in *.
    specialize (itype_preservation_app (fst phi) rmax CF T T1 (snd phi) p Hconsist HDis H i H0) as X1. easy.
 - (* Case: Had *)
    intros. inv Hsem.
    exists ((qs, nil, nil)::T).
    split. try constructor.
    apply had_type_consist; try easy.
(*
    induction qs. simpl in *. easy.
    simpl in *.
    unfold type_consist,add_had in *.
    intros. simpl in *.
    remember (fst (apply_hads phi qs)) as m.
    assert (disjoint_record  (([], qs, []) :: T)).
    unfold disjoint_record in *. 
    assert ((flat_union (([], a :: qs, []) :: T)) = a :: (flat_union (([], qs, []) :: T))).
    clear HDis Heqm IHqs Hconsist H.
    unfold flat_union,rec_union. simpl in *.
    rewrite ford_left_head. easy.
    rewrite H0 in HDis. inv HDis. easy.
    assert ((forall i : nat,
        i < fst phi -> type_consist_eta (([], qs, []) :: T) (snd (snd phi i)))).
    intros. apply Hconsist in H1.
    unfold type_consist_eta in *.
    intros.
    simpl in *. destruct H2. subst.
    unfold nor_consist_eta in *. simpl in *.
    split. intros. easy.
    split. intros. 
    assert (([]: list posi, a :: qs, [] : list posi) = ([], a :: qs, []) \/ In ([], a :: qs, []) T).
    left. easy. apply H1 in H3. destruct H3 as [X1 [X2 X3]].
    apply X2. simpl in *. right. apply H2. easy.
    assert (([], a :: qs, []) = s0 \/ In s0 T). right. easy.
    apply H1 in H3. easy.
    specialize (IHqs H0 H1).
    admit.
*)

  - (* Case: New *)
    intros. inv Hsem.
    exists ((nil, qs, nil)::T).
    split. constructor.
    induction qs. unfold type_consist in *. intros.
      unfold type_consist_eta in *. intros.
      simpl in *. destruct H2. subst.
      simpl in *. unfold had, nor in *. simpl in *. split.
      easy. easy. apply Hconsist. easy. easy.
      assert (disjoint qs).
      inv H. easy.
      simpl in H0.
      destruct (set_mem posi_eq_dec a (flat_union T)) eqn:G1. inv H0.
      specialize (IHqs H1 H0).
      unfold type_consist in *. intros. simpl in *.
      specialize (IHqs i H2).
      unfold type_consist_eta in *. intros.
      remember (add_new_list (fst phi) (snd phi) qs) as st.
      simpl in *. destruct H3.
      subst. unfold had, nor in *. simpl in *.
      split. unfold nor_consist_eta. intros. inv H3.
      split. unfold nor_consist_eta in *. intros. simpl in *. destruct H3.
      subst. apply add_elem_same_p. easy.
      specialize (IHqs ([], qs, [])).
      assert ((nil:(list posi), qs, nil:(list posi)) = ([], qs, []) \/ In ([], qs, []) T).
      left. easy. apply IHqs in H4. destruct H4 as [X1 [X2 X3]].
      simpl in *. rewrite add_elem_same_not. apply X2. easy.
      inv H. apply In_conv with (q := p) in H6; try easy. intros R. subst. easy.
      unfold rot_consist_eta in *. intros. simpl in *. easy.
      apply member_not_in_set with (s := s0) in G1 as G2; try easy.
      assert (([]:(list posi), qs, []:(list posi)) = s0 \/ In s0 T). right. easy.
      apply IHqs in H4.
      destruct H4 as [X1 [X2 X3]].
      unfold nor_consist_eta in *. split. intros.
      rewrite add_elem_same_not. apply X1 in H4. easy.
      intros R. subst. unfold rec_union in *.
      assert (In p (had s0 ++ nor s0 ++ rot s0)).
      apply in_or_app. left. easy. easy.
      split. intros. apply X2 in H4 as X5.
      rewrite add_elem_same_not. easy.
      intros R. subst.
      unfold rec_union in *.
      assert (In p (had s0 ++ nor s0 ++ rot s0)).
      apply in_or_app. right. apply in_or_app. left. easy. easy.
      unfold rot_consist_eta in *. intros. apply X3 in H4 as X4.
      rewrite add_elem_same_not. easy.
      intros R. subst.
      unfold rec_union in *.
      assert (In p (had s0 ++ nor s0 ++ rot s0)).
      apply in_or_app. right. apply in_or_app. right. easy. easy.

  - (* Case: ESeq *)
    intros. inv Hsem. inv Htype1.
    exists T2. split. easy. easy.
    destruct (IHHtype1 HDis Hconsist e1' H5) as [Ta [X1 X2]].
    exists Ta. split.
    eapply eseq_ty with (T2 := T2); try easy. easy.
  - (* Case IFa *)
    intros. inv Hsem.
    exists T. split. easy. easy.
    exists T. easy.
  - (* mea *)
    intros. inv Hsem.
    exists ((qrecord_diff th qs :: T)).
    split. apply etype_subst. easy.
    specialize (mea_type_consist rmax qs th T phi phi' r bl Hconsist H7) as X1. easy.
Qed.

