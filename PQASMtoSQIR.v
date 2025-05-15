Require Import Reals.
Require Import Psatz.
Require Import Coq.btauto.Btauto Coq.NArith.Nnat Coq.Lists.List.
Require Import BasicUtility.
Require Import MathSpec.
Require Import Classical_Prop.
Require Import Dirac.
Require Import PQASM.
Require Import CLArith.
Require Import SQIR.
Import ListNotations.
(**********************)
(** Unitary Programs **)
(**********************)

(* Declare Scope exp_scope.
Delimit Scope exp_scope with exp.
Local Open Scope exp_scope. *)
Local Open Scope nat_scope.

(* irrelavent vars. *)
Definition vars_neq (l:list var) := forall n m x y,
   nth_error l m = Some x ->  nth_error l n = Some y -> n <> m -> x <> y.

Inductive expr := 
      | SKIP (p:posi) | X (p:posi) 
      | CUexpr (p:posi) (e:expr)
      | RZ (q:nat) (p:posi) (* 2 * PI * i / 2^q *)
      | RRZ (q:nat) (p:posi) 
      | SR (q:nat) (x:var) (* a series of RZ gates for QFT mode from q down to b. *)
      | SRR (q:nat) (x:var) (* a series of RRZ gates for QFT mode from q down to b. *)
      (*| HCNOT (p1:posi) (p2:posi) *)
      | QFT (x:var) (b:nat) (* H on x ; CR gates on everything within (size - b). *)
      | RQFT (x:var) (b:nat)
      (* | H (p:posi) *)
      (* | H (x:posi)  H on x ; CR gates on everything within (size - b). *)
      | Seq (s1:expr) (s2:expr)
      (* | Hadamard (* need to link with hadamard method in Quantum.vexternals/SQIR/externals/QWIRE/Quantum.v*)
      | Measr link to meas_op in Quantum.v? *)
         .
Definition vars := nat -> (nat * nat * (nat -> nat) * (nat -> nat)).
Definition start (vs :vars) (x:var) := fst (fst (fst (vs x))).
Definition vmap (vs:vars) (x:var) := snd (fst (vs x)).
Definition rz_ang (n:nat) : R := ((2%R * PI)%R / 2%R^n).
Definition rrz_ang (n:nat) : R := ((2%R * PI)%R - ((2%R * PI)%R / 2%R^n)).
Definition find_pos (f : vars) (p:posi) :=
      let (a,b) := p in start f a + (vmap f a b).
      Fixpoint gen_sr_gate' (f:vars) (dim:nat) (x:var) (n:nat) (size:nat) : base_ucom dim := 
         match n with 0 => SQIR.ID (find_pos f (x,0))
                   | S m => SQIR.useq (gen_sr_gate' f dim x m size) (SQIR.Rz (rz_ang (size - m)) (find_pos f (x,m)))
         end.
      Definition gen_sr_gate (f:vars) (dim:nat) (x:var) (n:nat) := gen_sr_gate' f dim x (S n) (S n).
      Fixpoint gen_srr_gate' (f:vars) (dim:nat) (x:var) (n:nat) (size:nat) : base_ucom dim := 
   match n with 0 => SQIR.ID (find_pos f (x,0))
             | S m => SQIR.useq (gen_srr_gate' f dim x m size) (SQIR.Rz (rrz_ang (size - m)) (find_pos f (x,m)))
   end.
Definition gen_srr_gate (f:vars) (dim:nat) (x:var) (n:nat) := gen_srr_gate' f dim x (S n) (S n).
Fixpoint nH (f : vars) (dim:nat) (x:var) (n:nat) (b:nat) : base_ucom dim :=
     match n with 0 => SQIR.ID (find_pos f (x,0))
               | S m => SQIR.useq (nH f dim x m b) (SQIR.H (find_pos f (x,b+m))) 
     end.
     Definition vsize (vs:vars) (x:var) := snd (fst (fst (vs x))).
     Fixpoint controlled_rotations_gen (f : vars) (dim:nat) (x:var) (n : nat) (i:nat) : base_ucom dim :=
  match n with
  | 0 | 1 => SQIR.ID (find_pos f (x,i))
  | S m  => SQIR.useq (controlled_rotations_gen f dim x m i)
                 (SQIR.UnitaryOps.control (find_pos f (x,m+i)) (SQIR.Rz (rz_ang n) (find_pos f (x,i))))
  end.
     Fixpoint QFT_gen (f : vars) (dim:nat) (x:var) (n : nat) (size:nat) : base_ucom dim :=
      match n with
      | 0    => SQIR.ID (find_pos f (x,0))
      | S m => SQIR.useq  (QFT_gen f dim x m size)
                 (SQIR.useq (SQIR.H (find_pos f (x,m))) ((controlled_rotations_gen f dim x (size-m) m)))
      end.
Definition trans_qft (f:vars) (dim:nat) (x:var) (b:nat) : base_ucom dim :=
         SQIR.useq (QFT_gen f dim x b b) (nH f dim x (vsize f x - b) b).

Definition trans_rqft (f:vars) (dim:nat) (x:var) (b:nat) : base_ucom dim :=
   SQIR.UnitaryOps.invert (SQIR.useq (QFT_gen f dim x b b) (nH f dim x (vsize f x - b) b)).

(* Fixpoint trans_exp (dim:nat) (expression:exp) (avs: nat -> posi) : (base_ucom dim * vars  * (nat -> posi)) :=
   match exp with 
   |ESKIP => (SQIR.ID (find_pos f p), f, avs)
   | Had b => (SQIR.X (find_pos f p), f, avs)
   | Next p => (SQIR.Rz (rz_ang q) (find_pos f p), f, avs)
   | New b => (SQIR.Rz (rrz_ang q) (find_pos f p), f, avs)
   | Meas x qs => (gen_sr_gate f dim x n, f, avs)
   | IFa k op1 op2 => (gen_srr_gate f dim x n, f, avs)
   | Eseq e1  e2 => match trans_exp f dim e1 avs with (e1', f', avs') => 
                        match trans_exp f' dim e2 avs' with (e2',f'',avs'') => (SQIR.useq e1' e2', f'', avs'') end
                  end
      end. *)
Definition posi_list_to_var  (ps : list posi) :=  var.
Fixpoint rz_adder_new' (x:var) (n:nat) (size:nat) (M: nat -> bool) :=
  match n with 
  | 0 => SKIP (x,0)
  | S m => Seq (rz_adder_new' x m size M) (if M m then SR (size - n) x else SKIP (x,m))
  end.

Fixpoint inv_exp p :=
  match p with
  | SKIP a => SKIP a
  | X n => X n
  | CUexpr n p => CUexpr n (inv_exp p)
  | SR n x => SRR n x
  | SRR n x => SR n x
 (* | HCNOT p1 p2 => HCNOT p1 p2 *)
  | RZ q p1 => RRZ q p1
  | RRZ q p1 => RZ q p1
  | QFT x b => RQFT x b
  | RQFT x b => QFT x b
  (*| H x => H x*)
  | Seq p1 p2 => Seq (inv_exp p2) (inv_exp p1)
   end.
Notation "p1 ; p2" := (Seq p1 p2) (at level 50) : exp_scope.
Definition rz_adder_new (x:var) (n:nat) (M:nat -> bool) := rz_adder_new' x n n M.
Fixpoint rz_sub_new' (x:var) (n:nat) (size:nat) (M: nat -> bool) :=
  match n with 
  | 0 => SKIP (x,0)
  | S m => Seq (rz_sub_new' x m size M) (if M m then SRR (size - n) x else SKIP (x,m))
  end.

Definition rz_sub_new (x:var) (n:nat) (M:nat -> bool) := rz_sub_new' x n n M.
Definition CNOT (x y : posi) := CUexpr x (X y).
Definition rz_compare_half_new (x:var) (n:nat) (c:posi) (M:nat) := 
   Seq (rz_sub_new x n (nat2fb M)) (Seq (RQFT x n) (CNOT (x,0) c)).

Definition rz_compare_new (x:var) (n:nat) (c:posi) (M:nat) := 
 Seq (rz_compare_half_new x n c M) (inv_exp ( Seq (rz_sub_new x n (nat2fb M)) (RQFT x n))).

Definition one_cu_adder (x:var) (n:nat) (c:posi) (M:nat -> bool) := CUexpr c (rz_adder_new x n M).

Definition qft_cu (x:var) (c:posi) (n:nat) := 
  Seq(RQFT x n) (Seq (CNOT (x,0) c) (QFT x n)).

Definition qft_acu (x:var) (c:posi) (n:nat) := 
  Seq (RQFT x n)  (Seq (X (x,0))  (Seq (CNOT (x,0) c)  (Seq (X (x,0))  (QFT x n)))).

Definition mod_adder_half (x:var) (n:nat) (c:posi) (A:nat -> bool) (M:nat -> bool) :=
   Seq (Seq (rz_adder_new x n A) (rz_sub_new x n M))  (Seq (qft_cu x c n)  (one_cu_adder x n c M)).

Definition clean_hbit (x:var) (n:nat) (c:posi) (M:nat -> bool) := 
   Seq (rz_sub_new x n M) (Seq (qft_acu x c n) ( inv_exp (rz_sub_new x n M))).

Definition mod_adder (x:var) (n:nat) (c:posi) (A:nat -> bool) (M:nat -> bool) :=
  Seq (mod_adder_half x n c A M) (clean_hbit x n c A).

(* modular multiplier: takes [x][0] -> [x][ax%N] where a and N are constant. *)
Fixpoint rz_modmult_new' (y:var) (x:var) (n:nat) (size:nat) (c:posi) (A:nat) (M:nat) :=
   match n with
   | 0 =>  (SKIP (y,0))
   | S m => Seq (rz_modmult_new' y x m size c A M)
           (CUexpr (x,size - n) (mod_adder y size c (nat2fb ((2^m * A) mod M)) (nat2fb M)))
   end.

Definition rz_modmult_half y x size c A M := 
  Seq (QFT y size) (Seq (rz_modmult_new' y x size size c A M)  (RQFT y size)).

Definition rz_modmult_full (y:var) (x:var) (n:nat) (c:posi) (A:nat) (Ainv :nat) (N:nat) :=
  Seq (rz_modmult_half y x n c A N) (inv_exp (rz_modmult_half x y n c Ainv N)).

Definition mu_compile (m: mu): option expr :=
match m with 
| Add ps n => Some (rz_adder_new (length ps) n (nat2fb n))
| Less ps n p => Some (rz_compare_new (length ps) n p n)
| Equal ps n p => Some (rz_compare_new (length ps) n p n)
(* | ModMult ps n m => Some (rz_modmult_full (length ps) (length ps) n p n n n ) *)
| _ => None
(* | Less ps n p => rz_compare x n p 
| Equal ps n p => rz_compare x n p 
| ModMult ps n m => rz_modmult_full y x n p m a b
| Equal_posi_list ps qs p => rz_compare x n p  *)
end.   
(* Fixpoint exp_compile (e: exp) (po: posi): expr :=
   match e with
   | ESKIP =>  SKIP po
   | Next p => exp_compile p po
   | Had b => Hadamard
   | New b => exp_compile b
   | ESeq k m => Seq exp_compile k exp_compile m
   | Meas x qs e1 => Measr
   | IFa k op1 op2 => exp_compile op1 exp_compile op2
   end. *)

Inductive type := Had (b:nat) | Phi (b:nat) | Nor.

Notation "p1 ; p2" := (Seq p1 p2) (at level 50) : exp_scope.

Fixpoint exp_elim (p:expr) :=
  match p with
  | CUexpr q p => match exp_elim p with
                 | SKIP a => SKIP a 
                 | p' => CUexpr q p'
                 end
  | Seq p1 p2 => match exp_elim p1, exp_elim p2 with
                  | SKIP _, p2' => p2'
                  | p1', SKIP _ => p1'
                  | p1', p2' => Seq p1' p2'
                  end
  | _ => p
  end.

Definition Z (p:posi) := RZ 1 p.

Fixpoint GCCX' x n size :=
  match n with
  | O | S O => X (x,n - 1)
  | S m => CUexpr (x,size-n) (GCCX' x m size)
  end.
Definition GCCX x n := GCCX' x n n.

Fixpoint nX x n := 
   match n with 0 => X (x,0)
            | S m =>Seq (X (x,m)) (nX x m)
   end.

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Module Env := FMapList.Make Nat_as_OT.
Module EnvFacts := FMapFacts.Facts (Env).

Definition env := Env.t type.
Definition empty_env := @Env.empty type.

(* Defining program semantic functions. *)
Definition put_cu (v:val) (b:bool) :=
    match v with nval x r => nval b r | a => a end.

Definition get_cua (v:val) := 
    match v with nval x r => x | _ => false end.

Lemma double_put_cu : forall (f:posi -> val) x v v', put_cu (put_cu (f x) v) v' = put_cu (f x) v'.
Proof.
  intros.
  unfold put_cu.
  destruct (f x). easy. easy.
Qed.

Definition get_cus (n:nat) (f:posi -> val) (x:var) := 
          fun i => if i <? n then (match f (x,i) with nval b r => b | _ => false end) else allfalse i.

Definition rotate (r :rz_val) (q:nat) := addto r q.

Definition times_rotate (v : val) (q:nat) := 
     match v with nval b r => if b then nval b (rotate r q) else nval b r
                  | qval rc r =>  qval rc (rotate r q)
     end.

Fixpoint sr_rotate' (st: posi -> val) (x:var) (n:nat) (size:nat) :=
   match n with 0 => st
              | S m => (sr_rotate' st x m size)[(x,m) |-> times_rotate (st (x,m)) (size - m)]
   end.
Definition sr_rotate st x n := sr_rotate' st x (S n) (S n).

Definition r_rotate (r :rz_val) (q:nat) := addto_n r q.

Definition times_r_rotate (v : val) (q:nat) := 
     match v with nval b r =>  if b then nval b (r_rotate r q) else nval b r
                  | qval rc r =>  qval rc (r_rotate r q)
     end.

Fixpoint srr_rotate' (st: posi -> val) (x:var) (n:nat) (size:nat) :=
   match n with 0 => st
              | S m => (srr_rotate' st x m size)[(x,m) |-> times_r_rotate (st (x,m)) (size - m)]
   end.
Definition srr_rotate st x n := srr_rotate' st x (S n) (S n).

Definition exchange (v: val) :=
     match v with nval b r => nval (negb b) r
                  | a => a
     end.

(* Semantics function for QFT gate. *)
Definition seq_val (v:val) :=
  match v with nval b r => b
             | _ => false
  end.

Fixpoint get_seq (f:posi -> val) (x:var) (base:nat) (n:nat) : (nat -> bool) :=
     match n with 0 => allfalse
              | S m => fun (i:nat) => if i =? (base + m) then seq_val (f (x,base+m)) else ((get_seq f x base m) i)
     end.

Definition up_qft (v:val) (f:nat -> bool) :=
   match v with nval b r => qval r f
              | a => a
   end.

(*A function to get the rotation angle of a state. *)
Definition get_r (v:val) :=
   match v with nval x r => r
              | qval rc r => rc
   end.

Definition up_h (v:val)  :=
   match v with nval true r => qval r (rotate allfalse 1)
              | nval false r => qval r allfalse
              | qval r f => nval (f 0) r
   end.

Fixpoint assign_h (f:posi -> val) (x:var) (n:nat) (i:nat) := 
   match i with 0 => f
          | S m => (assign_h f x n m)[(x,n+m) |-> up_h (f (x,n+m))]
  end.

(* Semantic function for RQFT gate. *)
Fixpoint assign_seq (f:posi -> val) (x:var) (vals : nat -> bool) (n:nat) := 
   match n with 0 => f
              | S m => (assign_seq f x vals m)[(x,m) |-> nval (vals m) (get_r (f (x,m)))]
   end.

Fixpoint assign_h_r (f:posi -> val) (x:var) (n:nat) (i:nat) := 
   match i with 0 => f
          | S m => (assign_h_r f x n m)[(x,n+m) |-> up_h (f (x,n+m))]
  end.

Definition get_r_qft (f:posi -> val) (x:var) :=
      match f (x,0) with qval rc g => g
                      | _ => allfalse
      end.

Definition turn_rqft (st : posi -> val) (x:var) (b:nat) (rmax : nat) := 
           assign_h_r (assign_seq st x (get_r_qft st x) b) x b (rmax - b).

(* This is the semantics for basic gate set of the language. *)
Fixpoint exp_sem (env:var -> nat) (e:expr) (st: posi -> val) : (posi -> val) :=
   match e with (SKIP p) => st
              | X p => (st[p |-> (exchange (st p))])
              | CUexpr p e' => if get_cua (st p) then exp_sem env e' st else st
              | RZ q p => (st[p |-> times_rotate (st p) q])
              | RRZ q p => (st[p |-> times_r_rotate (st p) q])
              | SR n x => sr_rotate st x n (*n is the highest position to rotate. *)
              | SRR n x => srr_rotate st x n
               | RQFT x b => turn_rqft st x b (env x)
              | Seq e1 e2 => exp_sem env e2 (exp_sem env e1 st)
              | _ => st
    end.

Definition or_not_r (x y:var) (n1 n2:nat) := x <> y \/ n1 < n2.

Definition or_not_eq (x y:var) (n1 n2:nat) := x <> y \/ n1 <= n2.

Inductive exp_fresh (aenv:var->nat): posi -> expr -> Prop :=
      | skip_fresh : forall p p1, p <> p1 -> exp_fresh aenv p (SKIP p1)
      | x_fresh : forall p p' , p <> p' -> exp_fresh aenv p (X p')
      | sr_fresh : forall p x n, or_not_r (fst p) x n (snd p) -> exp_fresh aenv p (SR n x)
      | srr_fresh : forall p x n, or_not_r (fst p) x n (snd p) -> exp_fresh aenv p (SRR n x)
      | cu_fresh : forall p p' e, p <> p' -> exp_fresh aenv p e -> exp_fresh aenv p (CUexpr p' e)
     (* | cnot_fresh : forall p p1 p2, p <> p1 -> p <> p2 -> exp_fresh aenv p (HCNOT p1 p2) *)
      | rz_fresh : forall p p' q, p <> p' -> exp_fresh aenv p (RZ q p')
      | rrz_fresh : forall p p' q, p <> p' -> exp_fresh aenv p (RRZ q p')
       (*all qubits will be touched in qft/rqft because of hadamard*)
      | qft_fresh : forall p x b, or_not_eq (fst p) x (aenv x) (snd p) -> exp_fresh aenv p (QFT x b)
      | rqft_fresh : forall p x b, or_not_eq (fst p) x (aenv x) (snd p) -> exp_fresh aenv p (RQFT x b)
      | seq_fresh : forall p e1 e2, exp_fresh aenv p e1 -> exp_fresh aenv p e2 -> exp_fresh aenv p (Seq e1 e2).

(* Defining matching shifting stack. *)
Inductive sexp := Ls | Rs | Re.

Definition opp_ls (s : sexp) := match s with Ls => Rs | Rs => Ls | Re => Re end.

Definition fst_not_opp (s:sexp) (l : list sexp) := 
   match l with [] => True
              | (a::al) => s <> opp_ls a
   end.

Inductive exp_neu_l (x:var) : list sexp -> expr ->  list sexp -> Prop :=
      | skip_neul : forall l p, exp_neu_l x l (SKIP p) l
      | x_neul : forall l p,  exp_neu_l x l (X p) l
      | sr_neul : forall l y n, exp_neu_l x l (SR n y) l
      | srr_neul : forall l y n, exp_neu_l x l (SRR n y) l
      | cu_neul : forall l p e, exp_neu_l x [] e [] -> exp_neu_l x l (CUexpr p e) l
      (*| hcnot_neul : forall l p1 p2, exp_neu_l x l (HCNOT p1 p2) l *)
      | rz_neul : forall l p q, exp_neu_l x l (RZ q p) l
      | rrz_neul : forall l p q, exp_neu_l x l (RRZ q p) l
      | qft_neul : forall l y b, exp_neu_l x l (QFT y b) l
      | rqft_neul : forall l y b, exp_neu_l x l (RQFT y b) l
      | seq_neul : forall l l' l'' e1 e2, exp_neu_l x l e1 l' -> exp_neu_l x l' e2 l'' -> exp_neu_l x l (Seq e1 e2) l''.

Definition exp_neu (xl : list var) (e:expr) : Prop :=
    forall x, In x xl -> exp_neu_l x [] e [].

Definition exp_neu_prop (l:list sexp) :=
    (forall i a, i + 1 < length l -> nth_error l i = Some a -> nth_error l (i+1) <> Some (opp_ls a)).

(* Type System. *)
Inductive well_typed_exp: env -> expr -> Prop :=
    | skip_refl : forall env, forall p, well_typed_exp env (SKIP p)
    | x_nor : forall env p, Env.MapsTo (fst p) Nor env -> well_typed_exp env (X p)
    (*| x_had : forall env p, Env.MapsTo (fst p) Had env -> well_typed_exp env (X p) *)
    (*| cnot_had : forall env p1 p2, p1 <> p2 -> Env.MapsTo (fst p1) Had env -> Env.MapsTo (fst p2) Had env
                         -> well_typed_exp env (HCNOT p1 p2) *)
    | rz_nor : forall env q p, Env.MapsTo (fst p) Nor env -> well_typed_exp env (RZ q p)
    | rrz_nor : forall env q p, Env.MapsTo (fst p) Nor env -> well_typed_exp env (RRZ q p)
    | sr_phi : forall env b m x, Env.MapsTo x (Phi b) env -> m < b -> well_typed_exp env (SR m x)
    | srr_phi : forall env b m x, Env.MapsTo x (Phi b) env -> m < b -> well_typed_exp env (SRR m x).

Fixpoint get_vars e : list var :=
    match e with SKIP p => [(fst p)]
              | X p => [(fst p)]
              | CUexpr p e => (fst p)::(get_vars e)
             (* | HCNOT p1 p2 => ((fst p1)::(fst p2)::[]) *)
              | RZ q p => ((fst p)::[])
              | RRZ q p => ((fst p)::[])
              | SR n x => (x::[])
              | SRR n x => (x::[])
              | QFT x b => (x::[])
              | RQFT x b => (x::[])
              | Seq e1 e2 => get_vars e1 ++ (get_vars e2)
   end.

Inductive well_typed_oexp (aenv: var -> nat) : env -> expr -> env -> Prop :=
    | exp_refl : forall env e, 
                well_typed_exp env e -> well_typed_oexp aenv env e env
    | qft_nor :  forall env env' x b, b <= aenv x -> 
               Env.MapsTo x Nor env -> Env.Equal env' (Env.add x (Phi b) env)
                   -> well_typed_oexp aenv env (QFT x b) env'
    | rqft_phi :  forall env env' x b, b <= aenv x ->
               Env.MapsTo x (Phi b) env -> Env.Equal env' (Env.add x Nor env) -> 
                 well_typed_oexp aenv env (RQFT x b) env'
    | pcu_nor : forall env p e, Env.MapsTo (fst p) Nor env -> exp_fresh aenv p e -> exp_neu (get_vars e) e ->
                       well_typed_oexp aenv env e env -> well_typed_oexp aenv env (CUexpr p e) env
    | pe_seq : forall env env' env'' e1 e2, well_typed_oexp aenv env e1 env' -> 
                 well_typed_oexp aenv env' e2 env'' -> well_typed_oexp aenv env (Seq e1 e2) env''.

Inductive exp_WF (aenv:var -> nat): expr -> Prop :=
      | skip_wf : forall p, snd p < aenv (fst p) -> exp_WF aenv (SKIP p)
      | x_wf : forall p, snd p < aenv (fst p)  -> exp_WF aenv  (X p)
      | cu_wf : forall p e, snd p < aenv (fst p)  -> exp_WF aenv  e -> exp_WF aenv  (CUexpr p e)
    (*  | hcnot_wf : forall p1 p2, snd p1 < aenv (fst p1) 
                              -> snd p2 < aenv (fst p2)  -> exp_WF aenv  (HCNOT p1 p2) *)
      | rz_wf : forall p q, snd p < aenv (fst p)  -> exp_WF aenv  (RZ q p)
      | rrz_wf : forall p q, snd p < aenv (fst p)  -> exp_WF aenv  (RRZ q p)
      | sr_wf : forall n x, n < aenv x -> exp_WF aenv  (SR n x)
      | ssr_wf : forall n x, n < aenv x -> exp_WF aenv  (SRR n x)       
      | seq_wf : forall e1 e2, exp_WF aenv e1 -> exp_WF aenv  e2 -> exp_WF aenv  (Seq e1 e2)
      | qft_wf : forall x b, b <= aenv x -> 0 < aenv x -> exp_WF aenv (QFT x b)
      | rqft_wf : forall x b, b <= aenv x -> 0 < aenv x -> exp_WF aenv (RQFT x b).

Fixpoint init_v (n:nat) (x:var) (M: nat -> bool) :=
      match n with 0 => (SKIP (x,0))
                | S m => if M m then Seq (init_v m x M) (X (x,m)) else init_v m x M
      end.

Inductive right_mode_val : type -> val -> Prop :=
    | right_nor: forall b r, right_mode_val Nor (nval b r)

    | right_phi: forall n rc r, right_mode_val (Phi n) (qval rc r).

Definition right_mode_env (aenv: var -> nat) (env: env) (st: posi -> val)
            := forall t p, snd p < aenv (fst p) -> Env.MapsTo (fst p) t env -> right_mode_val t (st p).

(* helper functions/lemmas for NOR states. *)
Definition nor_mode (f : posi -> val)  (x:posi) : Prop :=
       match f x with nval a b => True | _ => False end.

Definition nor_modes (f:posi -> val) (x:var) (n:nat) :=
      forall i, i < n -> nor_mode f (x,i).

Definition get_snd_r (f:posi -> val) (p:posi) :=
    match (f p) with qval rc r => r | _ => allfalse end.

Definition qft_gt (aenv: var -> nat) (tenv:env) (f:posi -> val) :=
   forall x b, Env.MapsTo x (Phi b) tenv -> (forall i,0 < b <= i -> get_r_qft f x i = false)
                                      /\ (forall j, b <= j < aenv x -> (forall i, 0 < i -> get_snd_r f (x,j) i = false )).

Definition at_match (aenv: var -> nat) (tenv:env) := forall x b, Env.MapsTo x (Phi b) tenv -> b <= aenv x.
