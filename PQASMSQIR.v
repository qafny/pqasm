Require Import Reals.
Require Import Psatz.
Require Import Complex.
Require Import SQIR.
Require Import VectorStates DensitySem UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat Permutation. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import Classical_Prop.
Require Import MathSpec.
Require Import PQASM.
Require Import PQASMProof.
(**********************)
(** Locus Definitions **)
(**********************)

From Coq Require Recdef.
Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Local Open Scope nat_scope.
Local Open Scope com_scope.

(*
Check OQASMProof.vars.

(avs: nat -> posi)
*)


Fixpoint nX (f : var -> nat) (dim:nat) (x:var) (n:nat) : base_ucom dim :=
     match n with 0 => SQIR.ID (f x)
               | S m => SQIR.useq (nX f dim x m) (SQIR.X ((f x) + m)) 
     end.

Fixpoint controlled_x_gen (f : var -> nat) (dim:nat) (x:var) (n : nat) (size:nat) : base_ucom dim :=
  match n with
  | 0 | 1 => SQIR.X ((f x) + (size-1))
  | S m  => control ((f x) + (size - n)) (controlled_x_gen f dim x m size)
  end.

Fixpoint gen_sr_gate' (f:var -> nat) (dim:nat) (x:var) (n:nat) (size:nat) : base_ucom dim := 
   match n with 0 => SQIR.ID ((f x))
             | S m => SQIR.useq (gen_sr_gate' f dim x m size) (SQIR.Rz (rz_ang (size - m)) ((f x) + m))
   end.
Definition gen_sr_gate (f:var -> nat) (dim:nat) (x:var) (n:nat) := gen_sr_gate' f dim x (S n) (S n).

Fixpoint gen_srr_gate' (f:var -> nat) (dim:nat) (x:var) (n:nat) (size:nat) : base_ucom dim := 
   match n with 0 => SQIR.ID ((f x))
             | S m => SQIR.useq (gen_srr_gate' f dim x m size) (SQIR.Rz (rrz_ang (size - m)) ((f x) + m))
   end.
Definition gen_srr_gate (f:var -> nat) (dim:nat) (x:var) (n:nat) := gen_srr_gate' f dim x (S n) (S n).

Fixpoint controlled_rotations_gen (f : var -> nat) (dim:nat) (x:var) (n : nat) (i:nat) : base_ucom dim :=
  match n with
  | 0 | 1 => SQIR.ID ((f x) + i)
  | S m  => SQIR.useq (controlled_rotations_gen f dim x m i)
                 (control ((f x) + (m+i)) (SQIR.Rz (rz_ang n) ((f x) + i)))
  end.

Fixpoint QFT_gen (f : var -> nat) (dim:nat) (x:var) (n : nat) (size:nat) : base_ucom dim :=
  match n with
  | 0    => SQIR.ID (f x)
  | S m => SQIR.useq  (QFT_gen f dim x m size)
             (SQIR.useq (SQIR.H ((f x) + m)) ((controlled_rotations_gen f dim x (size-m) m)))
  end.

Fixpoint nH (f : var -> nat) (dim:nat) (x:var) (n:nat) (b:nat) : base_ucom dim :=
     match n with 0 => SQIR.ID (f x)
               | S m => SQIR.useq (nH f dim x m b) (SQIR.H ((f x) + (b+m))) 
     end.

Definition trans_qft (f:var -> nat) size (dim:nat) (x:var) (b:nat) : (base_ucom dim) :=
          (SQIR.useq (QFT_gen f dim x b b) (nH f dim x (size - b) b)).

Definition trans_rqft (f:var -> nat) (size:nat) (dim:nat) (x:var) (b:nat) : (base_ucom dim) :=
             (invert (SQIR.useq (QFT_gen f dim x b b) (nH f dim x (size - b) b))).

Definition measure' {dim} n : base_com dim := (meas n skip skip).
(* avs is to support the compilation of OQASM, it is id with f. *)
Fixpoint trans_n_meas {dim} (n:nat) (p:nat) : base_com dim :=
  match n with 0 => SQIR.ID (p) | S m => measure' (p+m);trans_n_meas m p end.


Definition diff (f : var -> nat) (dim:nat) (x:var) (n : nat) : base_com dim := 
  nH f dim x n 0 ; nX f dim x n; 
   SQIR.H ((f x) + (n-1)); controlled_x_gen f dim x n n ; nX f dim x n; nH f dim x n 0.


(* M - x *)
Fixpoint negator0 i x : exp :=
  match i with
  | 0 => SKIP x (Num 0)
  | S i' => Seq (negator0 i' x) (X x (Num i'))
  end.

Fixpoint rz_adder' (x:var) (n:nat) (size:nat) (M: nat -> bool) :=
  match n with 
  | 0 => SKIP x (Num 0)
  | S m => Seq (rz_adder' x m size M) (if M m then SR (size - n) x else SKIP x (Num m))
  end.

Definition rz_adder (x:var) (n:nat) (M:nat -> bool) := rz_adder' x n n M.

Definition rz_sub_anti (x:var) (n:nat) (M:nat -> bool) := Seq (negator0 n x) (rz_adder x n M).

Fixpoint rz_sub' (x:var) (n:nat) (size:nat) (M: nat -> bool) :=
  match n with 
  | 0 => SKIP x (Num 0)
  | S m => Seq (rz_sub' x m size M) (if M m then SRR (size - n) x else SKIP x (Num m))
  end.

Definition rz_sub (x:var) (n:nat) (M:nat -> bool) := rz_sub' x n n M.

Definition CNOT (x: var) (i:aexp) (y : var) (c:aexp) := CU x i (X y c).

Definition rz_compare_half (x:var) (n:nat) (ca:var) (cv:aexp) (M:nat) := 
   Seq (Seq (rz_sub x n (nat2fb M)) (RQFT x n)) (CNOT x (Num 0) ca cv).

Fixpoint inv_exp p :=
  match p with
  | SKIP x a => SKIP x a
  | X x n => X x n
  | CU x n p => CU x n (inv_exp p)
  | SR n x => SRR n x
  | SRR n x => SR n x
 (* | HCNOT p1 p2 => HCNOT p1 p2 *)
  | RZ q x p1 => RRZ q x p1
  | RRZ q x p1 => RZ q x p1
  | QFT x b => RQFT x b
  | RQFT x b => QFT x b
  (*| H x => H x*)
  | Seq p1 p2 => Seq (inv_exp p2) (inv_exp p1)
   end.

(* M <? x *)
Definition rz_compare_anti (x:var) (n:nat) (ca:var) (cv:aexp) (M:nat) := 
 Seq (rz_compare_half x n ca cv M) (inv_exp (Seq (rz_sub_anti x n (nat2fb M)) (RQFT x n))).

Definition rz_compare (x:var) (n:nat) (ca:var) (cv:aexp) (M:nat) := 
  Seq (rz_compare_half x n ca cv M) (inv_exp (Seq (rz_sub x n (nat2fb M)) (RQFT x n))).

Definition rz_eq_circuit (x:var) (n:nat) (ca:var) (cv:aexp) (M:nat) :=
   Seq (Seq (X ca cv) (rz_compare_anti x n ca cv M)) (Seq (X ca cv) (rz_compare x n ca cv M)).

Definition rz_lt_circuit (x:var) (n:nat) (ca:var) (cv:aexp) (M:nat) := rz_compare x n ca cv M.

Section mergeSort.
  Variable A : Type.
  Variable le : A -> A -> bool.


  Fixpoint insert (x : A) (ls : list A) : list A :=
    match ls with
      | nil => x :: nil
      | h :: ls' =>
        if le x h
          then x :: ls
          else h :: insert x ls'
    end.


  Fixpoint merge (ls1 ls2 : list A) : list A :=
    match ls1 with
      | nil => ls2
      | h :: ls' => insert h (merge ls' ls2)
    end.

End mergeSort.

Inductive trans_exp_rel {dim rmax:nat} {env:aenv} {s:var -> nat}: exp -> (base_ucom dim) -> Prop :=
    etrans_skip : forall x v, trans_exp_rel (SKIP x (Num v)) (SQIR.ID ((s x)+v))
  | etrans_x : forall x v, trans_exp_rel (X x (Num v)) (SQIR.X ((s x)+v))
  | etrans_cu : forall x e v p, trans_exp_rel e p -> trans_exp_rel (CU x (Num v) e) (control ((s x)+v) p)
  | etrans_rz : forall q x v, trans_exp_rel (RZ q x (Num v)) (SQIR.Rz (rz_ang q) ((s x)+v))
  | etrans_rrz : forall q x v, trans_exp_rel (RRZ q x (Num v)) (SQIR.Rz (rrz_ang q) ((s x)+v))
  | etrans_sr : forall q x, trans_exp_rel (SR q x) (gen_sr_gate s dim x q)
  | etrans_srr : forall q x, trans_exp_rel (SR q x) (gen_srr_gate s dim x q)
  | etrans_qft : forall q x n, AEnv.MapsTo x (QT n) env -> trans_exp_rel (QFT x q) (trans_qft s n dim x q)
  | etrans_rqft : forall q x n, AEnv.MapsTo x (QT n) env -> trans_exp_rel (QFT x q) (trans_rqft s n dim x q)
  | etrans_seq: forall e1 e2 p1 p2,
          trans_exp_rel e1 p1 -> trans_exp_rel e2 p2 -> trans_exp_rel (QafnySyntax.Seq e1 e2) (SQIR.useq p1 p2).
            

Inductive pexpa := PExp (e:pexp) | LExp (x:var) (e:pexp).

Fixpoint combineSeq (el: list pexpa) :=
    match el with nil => Some PSKIP
                | (PExp e::el) =>
           match combineSeq el with None => None
                                  | Some e' => Some (PSeq e e')
           end
                | _ => None
    end.

Inductive trans_pexp_rel  {dim rmax:nat} : mode -> aenv -> (var -> nat)
                    -> type_map-> pexp -> type_map -> (base_com dim * option (list pexpa)) -> Prop :=
  | trans_pexp_skip : forall q env f T T',
      trans_pexp_rel q env f T PSKIP T' (skip,None)
  | trans_pexp_let_num : forall q env f T T' x v s e' e'',
      trans_pexp_rel q (AEnv.add x (CT) env) f T' (subst_pexp s x v) T' (e', Some e'') ->
      trans_pexp_rel q env f T (Let x (AE (Num v)) s) T' (e', Some e'')
  | trans_pexp_let_meas : forall env n f T x y l e,
      AEnv.MapsTo y (QT n) env ->
      trans_pexp_rel QM env f (((y,BNum 0,BNum n)::l,CH)::T)
            (Let x (Meas y) e) ((l,CH)::T) (trans_n_meas (f y) n, Some ([LExp y e]))
  | trans_pexp_appsu_index : forall q env f T T' x i,
      trans_pexp_rel q env f T (AppSU (RH (Index x (Num i)))) T' ((from_ucom (SQIR.H ((f x) + i))), None)
  | trans_pexp_appsu_rh_ba : forall q env f T T' x n,
      trans_pexp_rel q env f T (AppSU (RH (AExp (BA x)))) T' ((from_ucom (nH f dim x n 0)), None)
  | trans_pexp_appsu_sqft : forall q env f T T' x n,
      AEnv.MapsTo x (QT n) env ->
      trans_pexp_rel q env f T (AppSU (SQFT x)) T' ((from_ucom (trans_qft f n dim x 0)), None)
  | trans_pexp_appsu_srqft : forall q env f T T' x n,
      AEnv.MapsTo x (QT n) env ->
      trans_pexp_rel q env f T (AppSU (SRQFT x)) T' ((from_ucom (trans_rqft f n dim x 0)), None)
  | trans_pexp_appu : forall q env f T T' l e e',
      @trans_exp_rel dim rmax env f e e' ->
      trans_pexp_rel q env f T (AppU l e) T' ((from_ucom e'), None)

| trans_pexp_pseq_1 : forall q env f T T' e1 e2 e1' el,
      e1 <> PSKIP ->
      trans_pexp_rel q env f T e1 T' (e1', Some el) ->
      trans_pexp_rel q env f T (PSeq e1 e2) T' (e1', Some (el++[PExp e2]))

  | trans_pexp_pseq_2 : forall q env f T T' e1 e2 e1',
      trans_pexp_rel q env f T e1 T' (e1', None) -> 
      trans_pexp_rel q env f T (PSeq e1 e2) T' (e1', Some ([PExp e2]))

| trans_pexp_if_beq : forall env f T T' x y v n s ce,
      @trans_exp_rel dim rmax env f (rz_eq_circuit x (f x) y (Num v) n) ce ->
      trans_pexp_rel CM env f T (If (BEq (AExp (BA x)) (AExp (Num n)) y (Num v)) s) T'
                  (from_ucom ce, Some ([PExp (If (BTest y (Num v)) s)]))
| trans_pexp_if_blt : forall env f T T' x y v n s ce,
      @trans_exp_rel dim rmax env f (rz_lt_circuit x (f x) y (Num v) n) ce ->
      trans_pexp_rel CM env f T (If (BLt (AExp (BA x)) (AExp (Num n)) y (Num v)) s) T'
                  (from_ucom ce, Some ([PExp (If (BTest y (Num v)) s)]))
| trans_pexp_if_btest : forall env f T T' x v s e' el ea,
    trans_pexp_rel CM env f T s T' ((uc e'),Some el) ->
    combineSeq el = Some ea ->
    trans_pexp_rel CM env f T (If (BTest x (Num v)) s) T' ((uc (control (f x + v) e')),Some ([PExp (If (BTest x (Num v)) ea)])).

(*Function trans_pexp (f:OQASMProof.vars) (dim:nat) (e:pexp) (avs: nat -> posi) {struct e}: (option (base_com dim)) :=
  match e with PSKIP => Some skip
             | Let x (AE (Num n)) s => trans_pexp f dim (subst_pexp s x n) avs
             | Let x (AE (MNum r n)) s => trans_pexp f dim s avs
             | Let x (Meas y) s => match trans_pexp f dim s avs with None => None
                                    | Some cr => Some (trans_n_meas (vsize f y) (start f y) ; cr)
                                   end
             |AppSU (RH (Index x (Num i))) => Some (from_ucom (SQIR.H (find_pos f (x,i))))
             |AppSU (RH (AExp (BA x))) => Some (from_ucom (nH f dim x (vsize f x) 0))
             |AppSU (SQFT x) => Some (from_ucom (trans_qft f dim x (vsize f x)))
             |AppSU (SRQFT x) => Some (from_ucom (trans_rqft f dim x (vsize f x)))

             |AppU l e => match compile_exp_to_oqasm e
                            with None => None
                               | Some e' => match trans_exp f dim e' avs with (ce,_,_) => Some (from_ucom ce) end
                            end
             | PSeq e1 e2 => match trans_pexp f dim e1 avs with None => None
                                | Some e1' =>
                              match trans_pexp f dim e2 avs with None => None
                                 | Some e2' => Some (e1' ; e2')
                              end
                            end
           (*  | Diffuse (AExp (BA x)) => Some (diff f dim x (vsize f x)) *)

             | If (BEq (AExp (BA x)) (AExp (Num n)) y (Num v)) s => 
                   match trans_pexp f dim s avs with None => None
                      | Some e' =>
                    match trans_exp f dim (rz_eq_circuit x (vsize f x) (y,v) n) avs with (ce,_,_)
                             => Some (ce;e') 
                    end
                  end
             | If (BLt (AExp (BA x)) (AExp (Num n)) y (Num v)) s => 
                   match trans_pexp f dim s avs with None => None
                      | Some e' =>
                    match trans_exp f dim (rz_lt_circuit x (vsize f x) (y,v) n) avs with (ce,_,_)
                             => Some (ce;e') 
                    end
                  end

             | If (BTest x (Num v)) s => 
                   match trans_pexp f dim s avs with 
                      | Some (uc e') => Some (from_ucom (UnitaryOps.control (find_pos f (x,v)) e'))
                      | _ => None
                  end

       | _ => None
 end.*)


(*Inductive state_elem :=
                 | Nval (p:C) (r:rz_val)
                 | Hval (b:nat -> rz_val)
                 | Cval (m:nat) (b : nat -> C * rz_val).

Definition qstate := list (locus * state_elem).

Definition compile_val (v:val) (r_max : nat) : Vector 2 := 
   match v with nval b r => Cexp (2*PI * (turn_angle r r_max)) .* ∣ Nat.b2n b ⟩
            (* | hval b1 b2 r => RtoC(/ √ 2) * Cexp (2*PI * (turn_angle r r_max)) .*
                              ((RtoC ((z_phase b1))) .* ∣0⟩ .+ (RtoC ((z_phase b2))) .* ∣1⟩) *)
             | qval q r => RtoC(/ √ 2) * Cexp (2*PI * (turn_angle q r_max)) .* (∣0⟩ .+ (Cexp (2*PI * (turn_angle r r_max))) .* ∣1⟩)
  end.

Lemma WF_compile_val : forall v r, WF_Matrix (compile_val v r).
Proof.
  intros. unfold compile_val.
  destruct v;auto with wf_db.
Qed.

Hint Resolve WF_compile_val : wf_db.

(*example *)
Definition trans_state (avs : nat -> posi) (rmax : nat) (f : posi -> val) : (nat -> Vector 2) :=
        fun i => compile_val (f (avs i)) rmax.

function: posi -> nat
                 | Nval (p:C) (r:rz_val)
                 | Hval (b:nat -> rz_val)
                 | Cval (m:nat) (b : nat -> C * rz_val).*)

Check vsum.

Check find_pos.

Check allfalse.

Check fold_left.

     
Definition compile_val (v: val) (r_max : nat) : Vector 2 := 
   match v with 
   | nval b r => Cexp (2*PI * (turn_angle r r_max)) .* ∣ Nat.b2n b ⟩
   | qval q r => RtoC(/ √ 2) * Cexp (2*PI * (turn_angle q r_max)) .* (∣0⟩ .+ (Cexp (2*PI * (turn_angle r r_max))) .* ∣1⟩)
   end.

Definition outer_product {n : nat} (v : Vector n) : Matrix n n := v × (adjoint v).
     
(*To generate vector states*)
Definition gstate_vectors (avs : nat -> posi) (rmax : nat) (f : posi -> val) (n : nat) : list (Vector 2) :=
  map (fun i => compile_val (f (avs i)) rmax) (seq 0 n).

(* Function to calculate the dimension of a matrix. *)
Definition dim_of (m : nat) : nat := 2 ^ m.
     
(*Function to combine the vectors into a full quantum state *)
Definition cfull_state (state_vectors : list (Vector 2)) : 
      Matrix (dim_of (length state_vectors)) (dim_of (length state_vectors)) :=
      fold_left (fun (acc : Matrix (dim_of (length state_vectors)) 
                      (dim_of (length state_vectors))) (vec : Vector 2) => acc ⊗ vec) 
                         state_vectors (I (dim_of (length state_vectors))).


Check gstate_vectors.
Check cfull_state.
Check outer_product.

(*
Fixpoint perm_range (f: var -> nat) (v:rz_val) (x:var) (i:nat) (j:nat)  (n:nat) (acc:rz_val) :=
   match n with 0 => acc
              | S m => update (perm_range f v x i j m acc) ((f x) + (i+m)) (v (j+m))
   end.

Fixpoint perm_vector (f:var -> nat) (s:locus) (v:rz_val) (j:nat) := 
  match s with [] => Some allfalse
             | (x,BNum l, BNum r)::ne =>
          if l <=? r then
              (match perm_vector f ne v (j+(r-l))
                   with None => None
                      | Some acc => Some (perm_range f v x l j (r-l) acc)
               end)
          else None
             | _ => None
  end.

Fixpoint gen_qfun {d} (f: var -> nat) (s:locus) (size:nat) (m:nat) (b : nat -> C * rz_val)
   : option (nat -> Vector d) :=
   match m with 0 => Some (fun q => Zero)
              | S ma => match perm_vector f s (snd (b ma)) 0
                            with None => None
                               | Some acc =>
                         match gen_qfun f s size ma b
                              with None => None
                               | Some new_f =>
                Some (update new_f ma ((fst (b ma)).* (@basis_vector d (a_nat2fb acc size))))
                         end
                        end
   end.
*)

Definition make_pair (rmax:nat) (n:nat) (s:state_elem) :=
   match s with Nval p b => (1,fun x => if x =? 0 then (p,b) else (C0,allfalse))
                          | Cval m b => (m,b)
                          | Hval r => ((2^n), (sum_rotates n rmax r))
   end.

Fixpoint compose_state (rmax:nat) (s:qstate) :=
   match s with nil => Some (0,nil,1,fun x => (C0,allfalse))
              | (sa,st)::xs => 
         match compose_state rmax xs
                with None => None
                   | Some (na',sal,size,st') =>
         match ses_len sa with None => None
                             | Some na => 
               match make_pair rmax na st with (m,f) => 
                Some (na+na',sa++sal,m*size, car_fun_fch na m size f st')
               end
         end
        end
   end.

Fixpoint range_perm (start num cur:nat) (old:rz_val) (acc:rz_val) :=
   match num with 0 => acc
             | S m => update (range_perm start m cur old acc) (cur+m) (old (start + m))
   end.

Fixpoint locus_perm (l:list range) (f: var -> nat) (old:rz_val) (cur:nat) (acc:rz_val) :=
   match l with nil => Some acc
             | (x,BNum u, BNum v)::xs =>
               match (locus_perm xs f old (cur + (v - u)) acc) with None => None
                 | Some acca => 
                    Some (range_perm ((f x) + u) (v - u) cur old acca)
               end
             | _ => None
   end.

Fixpoint perm_all (l:list range) (f:var -> nat) (st: (nat -> C * (nat -> bool))) (m:nat) :=
   match m with 0 => Some (fun x => (C1, allfalse))
            | S n =>
            match perm_all l f st n with None => None
                | Some acc => 
              match locus_perm l f (snd (st n)) 0 (allfalse) with None => None
                      | Some re => Some (update acc n (fst (st n), re))
             end
           end
   end. 

Fixpoint f_to_vecs (dim:nat) (m:nat) (f:nat -> C * (nat -> bool)) :=
   match m with 0 => (fun x => I (2^dim))
              | S n => update (f_to_vecs dim n f) n ((fst (f n)) .* (f_to_vec dim (snd (f n))))
   end.

Definition trans_qstate (rmax:nat) (f:var -> nat) (s:qstate) (dim:nat) : option (Vector (2^dim)):=
    match compose_state rmax s with None => None
           | Some (qlength, ranges, size, st) => 
        if dim =? qlength then 
          match perm_all ranges f st size with None => None
                      | Some acc => Some (@vsum dim size (f_to_vecs dim size acc))
          end
        else None
     end.

Definition trans_state (rmax:nat) (f : var -> nat) (s:qstate) (dim : nat) : option (Density (2^dim)) :=
  match trans_qstate rmax f s dim with None => None 
         | Some st => Some (st† × st)
  end.

Definition env_eq (aenv:aenv) (f: var -> nat):= forall x n env, AEnv.MapsTo x (QT n) env -> f x = n.


Lemma trans_pexp_one_step_sem :
  forall (dim rmax : nat) (t : mode) (aenv : aenv) (f : var -> nat) (tenv : type_map) 
         (e : pexp) (tenv' : type_map) (phi : Density dim) (phi' : Density dim),
    dim > 0 ->
    env_eq aenv f ->
    @locus_system rmax t aenv tenv e tenv' ->
    forall (S S' : qstate) e' (r : R) (e'': pexp), 
      @step rmax aenv S e r S' e'' ->
      @trans_pexp_rel dim rmax t aenv f tenv e tenv' e' ->
      trans_state rmax f S dim = Some phi ->
      trans_state rmax f S' dim = Some phi' /\ r .* phi' = c_eval (fst(e')) phi.

Proof.
intros dim rmax t aenv f tenv e tenv' phi phi' Hdim 
Heq Hlocus S S' e' r e'' Hstep Htrans Htrans_state.
induction Htrans. inv Hstep. 
- admit.
- inv Hstep. admit.
- inv Hstep. admit.
- inv Hstep.
  * inv H2. unfold trans_state in Htrans_state. simpl in Htrans_state.
    remember (f x + i) as pos. unfold super. simpl in *.
Qed.
(* n is the length, f is the mapping from posi to nat, s is a locus, v is the virtual vector. *)


(*Fixpoint perm_range (f:OQASMProof.vars) (v:rz_val) (x:var) (i:nat) (j:nat)  (n:nat) (acc:rz_val) :=
   match n with 0 => acc
              | S m => update (perm_range f v x i j m acc) (find_pos f (x,i+m)) (v (j+m))
   end.

Fixpoint perm_vector (f:OQASMProof.vars) (s:locus) (v:rz_val) (j:nat) := 
  match s with [] => Some allfalse
             | (x,BNum l, BNum r)::ne =>
          if l <=? r then
              (match perm_vector f ne v (j+(r-l))
                   with None => None
                      | Some acc => Some (perm_range f v x l j (r-l) acc)
               end)
          else None
             | _ => None
  end.



Fixpoint gen_qfun {d} (f:OQASMProof.vars) (s:locus) (size:nat) (m:nat) (b : nat -> C * rz_val)
   : option (nat -> Vector d) :=
   match m with 0 => Some (fun q => Zero)
              | S ma => match perm_vector f s (snd (b ma)) 0
                            with None => None
                               | Some acc =>
                         match gen_qfun f s size ma b
                              with None => None
                               | Some new_f =>
                Some (update new_f ma ((fst (b ma)).* (@basis_vector d (a_nat2fb acc size))))
                         end
                        end
   end.

Definition trans_qstate (f:OQASMProof.vars) (s:qstate) :=
    match s with (sa,Cval m b)::nil =>
      match ses_len sa with None => None
                            | Some na => 
           match @gen_qfun (2^na) f sa na m b
              with None => None
                 | Some acc => Some (@vsum (2^na) m acc)
           end
      end
              | _ => None
   end.

Definition trans_state_qafny (f:OQASMProof.vars) (s:state) :=
  match s with (sa,q) => match trans_qstate f q 
       with None => None
          | Some acc => Some (sa,acc)
      end
  end.


Lemma trans_pexp_sem :
  forall dim e e' s s' t sa sa' tenv (tenv' : type_map) (aenv : aenv) rmax vs (avs : nat -> posi),
    (*vars_start_diff vs ->
    vars_finite_bij vs ->
    vars_sparse vs ->
    vars_anti_same vs ->
    exp_WF (size_env vs) e ->
    at_match (size_env vs) tenv ->
    exp_com_WF vs dim ->
    exp_com_gt vs avs dim ->
    well_typed_oexp (size_env vs) tenv e tenv' ->
    right_mode_env (size_env vs) tenv f ->
    avs_prop vs avs dim -> 
    exp_rmax (size_env vs) rmax e ->
    qft_uniform (size_env vs) tenv f ->
    qft_gt (size_env vs) tenv f ->*)
    dim > 0 ->
    @locus_system rmax t aenv tenv e tenv' ->
    @qfor_sem rmax aenv s e s' ->
    trans_pexp vs dim e avs = Some e' ->
    trans_state_qafny vs s' = Some sa' ->
    trans_state_qafny vs s = Some sa ->
    @nd_eval dim e' (snd sa) (snd sa').
Proof.
intros. generalize dependent tenv. generalize dependent tenv'. 
   induction H1 using qfor_sem_ind';
    intros; subst; simpl in *.
- rewrite H3 in H4. inv H4. inv H2. apply nd_skip.
- inv H5. rewrite H0 in *. inv H14. destruct a; simpl in *; try easy. inv H0.
  eapply IHqfor_sem; try easy. admit. apply H15. apply type_aexp_mo_no_simp in H12.
  rewrite H0 in H12. inv H12.
- inv H5. apply simp_aexp_no_eval in H0. rewrite H0 in H14. inv H14.
  destruct a; simpl in *; try easy. eapply IHqfor_sem; try easy. unfold trans_state_qafny in *.
  destruct (trans_qstate vs s'); try easy. admit. unfold trans_state_qafny in *. destruct s in *; simpl in *. admit. apply H15.
- admit.
- inv H3.
- admit.
- inv H3.
- inv H3.
- destruct b in *; simpl in *; try easy.
- destruct b in *; simpl in *; try easy.
- admit.
- admit. 
- inv H2.
Admitted.*)

 