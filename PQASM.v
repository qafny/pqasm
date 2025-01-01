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

(*Require Import OQASM.
Require Import Coq.QArith.QArith.*)
Import Nat (eqb).
(*Import Coq.FSets.FMapList.*)
(*From Coq Require Import BinaryString.*)
From Coq Require Import Lists.ListSet.
(**********************)
(** Unitary Programs **)
(**********************)

Declare Scope exp_scope.
Delimit Scope exp_scope with expScope.
Local Open Scope exp_scope.
Local Open Scope nat_scope.

(* Defining the data syntax, for classical arithmetic and boolean expressions. *)

Inductive aexp := BA (x:var) | Num (n:nat) | APlus (e1:aexp) (e2:aexp) | AMult (e1:aexp) (e2:aexp).

(* Coercion means that in a function or an inductive relation, var can be viewed as aexp. *)
Coercion BA : var >-> aexp.

(* Turnning prefix notation to mixfix notation. *)
Notation "e0 [+] e1" := (APlus e0 e1) (at level 50) : exp_scope.
Notation "e0 [*] e1" := (AMult e0 e1) (at level 50) : exp_scope.

Inductive cbexp := CEq (x:aexp) (y:aexp) | CLt (x:aexp) (y:aexp).

Definition rz_val : Set := nat.


(* Defining the instruction level syntax, by abstracting away the detailed implementations of the quantum arithmetic operations. *)

(*add mod multiplication here, compilation to OQASM*)
Inductive mu := Add (ps: list posi) (n:(nat)) (* we add nat to the bitstring represenation of ps *)
              | Less (ps : list posi) (n:(nat)) (p:posi) (* we compare ps with n (|ps| < n) store the boolean result in p. *)
              | Equal (ps : list posi) (n:(nat)) (p:posi) (* we compare ps with n (|ps| = n) store the boolean result in p. *)
              | ModMult (ps : list posi) (n:(nat)) (m: (nat))
              | Equal_posi_list (ps qs: list posi) (p:posi).

Inductive iota:= ISeq (k: iota) (m: iota) | ICU (x:posi) (y:iota)| Ora (e:mu) | Ry (p: posi) (r: rz_val).

Coercion Ora : mu >-> iota.
Notation "e0 ; e1" := (ISeq e0 e1) (at level 50) : exp_scope.


(* Defining the PQASM program level syntax. *)

Inductive exp := ESKIP | Next (p: iota) | Had (b:list posi) | New (b:list posi) 
| ESeq (k: exp) (m: exp) | Meas (x:var) (qs:list posi) (e1:exp) | IFa (k: cbexp) (op1: exp) (op2: exp).

Coercion Next : iota >-> exp.
Notation "e0 [;] e1" := (ESeq e0 e1) (at level 50) : exp_scope.





(*true -> 1, false -> 0, rz_val : nat -> bool, a bitstring represented as booleans *)
Inductive basis_val := Nval (b:bool) | Rval (n:nat).

Definition eta_state : Type := posi -> basis_val.
Fixpoint list_of_states (ps: list posi) (st: eta_state) : list basis_val :=
  match ps with 
  | [] => []
  | h::t => (st h)::(list_of_states t st)
  end.

Fixpoint position (p: posi) (l : list posi) : nat := 
  match l with 
  | [] => (0)
  | h::t => match (posi_eq h p) with 
            | true =>  1
            | false =>  1 + (position p t)
            end
  end.

Definition swap (f:nat -> bool) (x: nat) (y: nat): nat->bool :=
  fun k => if eqb k x then f y else if eqb k y then f x else f k.

Fixpoint permu (l : list posi) (f:nat -> bool) (G: list posi): nat->bool :=
  match G with 
  | [] => f
  | h::t => permu l (swap f (position h l) (position h G)) t
  end.

  Fixpoint push_to_st_helper (n: nat ) (G: list posi) (f' : nat -> bool) (st: eta_state): eta_state :=
    match G with 
    | [] => st
    | h::t => push_to_st_helper (n + 1) t f' (eupdate st h (Nval (f' n)))
    end.

Definition push_to_st (G: list posi) (f' : nat -> bool) (st: eta_state): eta_state :=
  match G with 
  | [] => st
  | h::t => push_to_st_helper 2 t f' (eupdate st h (Nval (f' 1)))
  end.

Definition pi32 (rmax:nat):= 2^(rmax-1) + 2^(rmax-2).

Definition angle_sum (f g:rz_val) (rmax:nat) := (f + g) mod 2^rmax.

Definition angle_sub (f g: rz_val) (rmax:nat) := if f <? g then 2^rmax - (g - f) else f - g.

Definition ry_rotate (st:eta_state) (p:posi) (r:rz_val) (rmax:nat): eta_state :=
   match st p with  Nval b2 => if b2 then st[ p |-> Rval (angle_sub (pi32 rmax) r rmax) ] else st[ p |-> Rval r]
                  |  Rval r1 => st[ p |-> Rval (angle_sum r1 r rmax)]
   end.

(*The following contains helper functions for records. *)
Definition qrecord : Type := (list posi * list posi * list posi).

Definition had (q:qrecord) := fst (fst q).

Definition nor (q:qrecord) := snd (fst q).

Definition rot (q:qrecord) := snd q.

Definition nor_sub (q:qrecord) (l:list posi) := (had q, l, rot q).

Definition had_sub (q:qrecord) (l:list posi) := (l, nor q, rot q).

Definition rec_union (q:qrecord) := (had q) ++ (nor q) ++ (rot q).

Definition flat_union (q:list qrecord) := fold_left (fun a b => a++rec_union b) q nil.

Definition set_inter_posi := set_inter posi_eq_dec.

Definition set_diff_posi := set_diff posi_eq_dec.

Definition qrecord_diff (q:qrecord) (l:list posi) := (set_diff_posi (had q) l, set_diff_posi (nor q) l, set_diff_posi (rot q) l).


(* Instruction level Semantic Functions. 
   The instruction level semantics is defined based on transitions over basis-kets. *)
Definition match_posi (a: posi) (b:posi): bool :=
  match a with
  | (w,x) => match b with 
      |(y,z) => match (eqb w y) with
          |false => false
          |true => match (eqb x z) with 
                |true => true
                |false => false
                end
          end
      end
    end.

Fixpoint disjoint_match (target: posi) (str: list posi): bool :=
  match str with 
  |[] => true
  | h::t => match match_posi h target with
      |true => disjoint_match target t 
      | false => false 
      end
    end.

Fixpoint disjoint_list (str: list posi): bool :=
    match str with
    | [] => true
    | h::t => match disjoint_match h t with
        | false => false
        | true => disjoint_list t
        end
     end.  

Fixpoint posi_list_to_bitstring_helper (ps: list posi) (st: eta_state) (n: nat): (nat-> bool) :=
  match ps with nil => allfalse
             | x::xs => 
      match st x with Rval r => fun k => if k =? n then false else posi_list_to_bitstring_helper xs st (n+1) k
                    | Nval b => fun k => if k =? n then b else posi_list_to_bitstring_helper xs st (n+1) k
      end
  end.
Definition posi_list_to_bitstring (ps: list posi) (st: eta_state): (nat-> bool) :=
    posi_list_to_bitstring_helper ps st 0.
    
Definition mu_addition (ps: list posi) (n:(nat)) (st: eta_state): (nat-> bool) :=
  sumfb false (posi_list_to_bitstring ps st) (nat2fb n).

(*
  Fixpoint mu_addition_reps (ps: list posi) (n:(nat)) (st: eta_state) (reps: nat): (nat-> bool):=
    match reps with 
    |0 => n
    | S m => mu_addition_reps ps (mu_addition ps n st) st m 
    end.
*)
  Definition rz_val_eq (rmax:nat) (x y : rz_val) := x mod 2^rmax =? y mod 2^rmax.
  Definition basis_val_eq (rmax:nat) (x y : basis_val) :=
      match (x,y) with (Nval b, Nval b') => Bool.eqb b b'
                   | (Rval bl1, Rval bl2) => rz_val_eq rmax bl1 bl2
                   | _ => false
      end.
Definition mu_less (ps: list posi) (n:(nat)) (st: eta_state) (q:posi) := 
  match st q with Nval j => st[q |-> Nval (j && (a_nat2fb (posi_list_to_bitstring ps st) (length ps) <? n))]
                | Rval f => st
  end.

Definition mu_eq (ps: list posi) (n:(nat)) (st: eta_state) (q:posi) := 
  match st q with Nval j => st[q |-> Nval (j && (a_nat2fb (posi_list_to_bitstring ps st) (length ps) =? n))]
                | Rval f => st
  end.

Definition mu_full_eq (ps qs: list posi) (st: eta_state) (q:posi) := 
  match st q with Nval j => st[q |-> Nval (j && 
                (a_nat2fb (posi_list_to_bitstring ps st) (length ps) =? a_nat2fb (posi_list_to_bitstring ps st) (length qs)))]
                | Rval f => st
  end.

Fixpoint bitstring_to_eta' (st:eta_state) (l:list posi) (f:nat -> bool) (n:nat): eta_state :=
  match l with nil => st
              | p::ps => (bitstring_to_eta' st ps f (n+1))[p |-> Nval (f n)]
  end.
Definition bitstring_to_eta st l f := bitstring_to_eta' st l f 0.

Definition modmult (st: eta_state) (ps:list posi) (c n:nat): eta_state :=
  bitstring_to_eta st ps (nat2fb ((c * a_nat2fb (posi_list_to_bitstring ps st) (length ps)) mod n)).

Definition mu_handling (rmax:nat) (m: mu) (st: eta_state) : eta_state :=
  match m with 
  | Add ps n => bitstring_to_eta st ps (mu_addition ps n st)
  | Less ps n p => mu_less ps n st p
  | Equal ps n p => mu_eq ps n st p
  | ModMult ps n m =>  modmult st ps n m
  | Equal_posi_list ps qs p => mu_full_eq ps qs st p
  end.
Fixpoint instr_sem (rmax:nat) (e:iota) (st: eta_state): eta_state :=
   match e with 
   | Ry p r => ry_rotate st p r rmax 
   | ISeq a b => instr_sem rmax b (instr_sem rmax a st)
   | Ora m => mu_handling rmax m st
  | ICU x y => match st x with 
      | Rval r =>  st 
      | Nval j => if j then instr_sem rmax y st else st
        end  
   end.

(* Program level semantics. *)
Definition state : Type := nat * (nat -> R * eta_state).
Definition config : Type := state * exp.
Definition bottom_state : nat -> R * eta_state := fun i => (R0, fun q => Nval false).

(* simp boolean expressions. *)
Fixpoint simp_aexp (e:aexp) :=
 match e with Num n => Some n
            | e1 [+] e2 => match simp_aexp e1
                                    with None => None
                                       | Some v1 => match simp_aexp e2 
                                               with None => None
                                                  | Some v2 => Some (v1 + v2)
                                                    end
                           end
            | e1 [*] e2 => match simp_aexp e1
                                    with None => None
                                       | Some v1 => match simp_aexp e2 
                                               with None => None
                                                  | Some v2 => Some (v1 * v2)
                                                    end
                           end
           | _ => None
 end.

Definition simp_bexp (e:cbexp) :=
  match e with CEq a b => match simp_aexp a with Some v1 =>
                                     match simp_aexp b with Some v2 => Some (v1 =? v2) | _ => None end 
                                                 | _ => None end
             | CLt a b => match simp_aexp a with Some v1 =>
                                     match simp_aexp b with Some v2 => Some (v1 <? v2) | _ => None end 
                                                 | _ => None end
  end.
(* Check simp_bexp. *)
(* add new qubits. *)
Definition add_new_eta (s:eta_state) (q:posi) := s[q |-> Nval false].

Fixpoint add_new_elem (n:nat) (s:nat -> R * eta_state) (q:posi) :=
   match n with 0 => s
              | S m => update (add_new_elem m s q) m (fst (s m), add_new_eta (snd (s m)) q)
   end.

Fixpoint add_new_list (n:nat) (s:nat -> R * eta_state) (q:list posi) :=
  match q with nil => s
             | x::xs => add_new_elem n (add_new_list n s xs) x
  end.
Definition add_new (s:state) (q:list posi) := (fst s, add_new_list (fst s) (snd s) q).

Fixpoint app_inst' (rmax:nat) (n:nat) (s:nat -> R * eta_state) (e:iota) :=
   match n with 0 => s
             | S m => update (app_inst' rmax m s e) m (fst (s m), instr_sem rmax e (snd (s m)))
   end.
Definition app_inst (rmax:nat) (s:state) (e:iota) := (fst s, app_inst' rmax (fst s) (snd s) e).

(* apply had operations. *)

Definition single_had (s:R * eta_state) (q:posi) (b:bool) :=
  match s with (phase,base) => 
    match (base q) with Rval v => (phase, base)
                      | Nval v =>
                if b then 
                  (if v then ((Rmult (Rdiv (Ropp 1) (sqrt(2))) phase):R, base[q |-> Nval b]) 
                        else ((Rmult (Rdiv 1 (sqrt(2))) phase):R, base[q |-> Nval b]))
                     else ((Rmult (Rdiv 1 (sqrt(2))) phase):R, base[q |-> Nval b])
    end
  end.

Fixpoint add_had' (n size:nat) (s:nat -> R * eta_state) (q:posi) :=
   match n with 0 => s
              | S m => update (update (add_had' m size s q) m (single_had (s m) q false)) (size + m) (single_had (s m) q true)
   end.
Definition add_had (s:state) (q:posi) := (2 * fst s, add_had' (fst s) (fst s) (snd s) q).

Fixpoint apply_hads (s:state) (qs : list posi) :=
  match qs with nil => s
              | x::xs => add_had (apply_hads s xs) x
  end.
  (* Check apply_hads. *)

Fixpoint turn_angle_r (rval :nat -> bool) (n:nat) (size:nat) : R :=
   match n with 0 => (0:R)
             | S m => (if (rval m) then (1/ (2^ (size - m))) else (0:R)) + turn_angle_r rval m size
   end.
Definition turn_angle (rval:nat) (n:nat) : R :=
      turn_angle_r (fbrev n (nat2fb rval)) n n.

(* apply computational basis measurement operations. *)
Fixpoint single_mea (rmax n:nat) (s:nat -> R * eta_state) (q:posi) (b:bool) :=
  match n with 0 => (0, R0, bottom_state)
             | S m => 
    match single_mea rmax m s q b with (num, prob, new_s) =>
       match (snd (s m)) q with Rval r => 
         if b then (S num,Rplus prob (Rmult (sin (turn_angle r rmax)) ((fst (s m))^2)), update new_s m (s m))
              else (S num,Rplus prob (Rmult (cos (turn_angle r rmax)) ((fst (s m))^2)), update new_s m (s m))
                            | Nval b1 => 
         if Bool.eqb b b1 then (S num, Rplus prob ((fst (s m))^2), update new_s m (s m))
                    else (num, prob, new_s)
       end
    end
  end.

Fixpoint amp_reduce (n:nat) (s: nat -> R * eta_state) (r:R) :=
   match n with 0 => s
             | S m => update (amp_reduce m s r) m (Rdiv (fst (s m)) (sqrt r), snd (s m))
   end.

Definition move_1 (f : nat -> bool) := fun i => f (i + 1).

Fixpoint apply_mea' (rmax:nat) (n:nat) (s:nat -> R * eta_state) (qs:list (posi * bool)) :=
   match qs with nil => ((n,s),R1)
               | (x,b)::xs => match apply_mea' rmax n s xs with ((new_n,new_s),re) =>
                             match single_mea rmax new_n new_s x b with (na,ra,sa) =>
                              ((na,amp_reduce na sa ra), Rmult re ra)
                             end
                          end
    end.

Fixpoint zip_b (qs:list posi) (bl: nat -> bool) :=
    match qs with nil => nil
                | x::xs => (x,bl 0)::(zip_b xs (move_1 bl))
    end.

Definition apply_mea (rmax:nat) (s:state) (qs:list posi) (bl:nat -> bool) : state * R :=
   apply_mea' rmax (fst s) (snd s) (zip_b qs bl).

Fixpoint aexp_subst_c (a:aexp) (x:var) (n:nat) :=
  match a with BA y => if x =? y then Num n else BA y
             | Num m => Num m
             | APlus e1 e2 => APlus (aexp_subst_c e1 x n) (aexp_subst_c e2 x n)
             | AMult e1 e2 => AMult (aexp_subst_c e1 x n) (aexp_subst_c e2 x n)
  end.


Definition bexp_subst_c (a:cbexp) (x:var) (n:nat) :=
  match a with CEq e1 e2 => CEq (aexp_subst_c e1 x n) (aexp_subst_c e2 x n)
             | CLt e1 e2 => CLt (aexp_subst_c e1 x n) (aexp_subst_c e2 x n)
  end.

Fixpoint exp_subst_c (a:exp) (x:var) (n:nat) :=
  match a with ESKIP => ESKIP
             | Next p => Next p
             | Had b => Had b
             | New b => New b
             | ESeq e1 e2 => ESeq (exp_subst_c e1 x n) (exp_subst_c e2 x n)
             | Meas y qs e => if x =? y then Meas y qs e else Meas y qs (exp_subst_c e x n)
             | IFa b e1 e2 => IFa (bexp_subst_c b x n) (exp_subst_c e1 x n) (exp_subst_c e2 x n)
  end.

(* The program level semantic rules. *)
Inductive prog_sem {rmax:nat}: state -> exp -> R -> state -> exp -> Prop :=
   seq_sem_1 : forall phi e,  prog_sem phi (ESKIP [;] e) (1:R) phi e
 | seq_sem_2: forall phi phi' r e1 e1' e2, prog_sem phi e1 r phi' e1' -> prog_sem phi (e1 [;] e2) r phi' (e1' [;] e2)
 | if_sem_3: forall phi b e1 e2, simp_bexp b = None -> prog_sem phi (IFa b e1 e2) 1 phi (IFa b e1 e2)
 | if_sem_1 : forall phi b e1 e2, simp_bexp b = Some true -> prog_sem phi (IFa b e1 e2) 1 phi e1
 | if_sem_2 : forall phi b e1 e2, simp_bexp b = Some false -> prog_sem phi (IFa b e1 e2) 1 phi e2
 | new_sem : forall phi bl, prog_sem phi (New bl) 1 (add_new phi bl) ESKIP
 | iota_sem : forall phi e, prog_sem phi (Next e) 1 (app_inst rmax phi e) ESKIP
 | had_sem : forall phi bl, prog_sem phi (Had bl) 1 (apply_hads phi bl) ESKIP
 | mea_sem : forall phi x qs e bl phi' rv, apply_mea rmax phi qs bl = (phi',rv) 
           -> prog_sem phi (Meas x qs e) rv phi' (exp_subst_c e x (a_nat2fb bl (length qs))).


