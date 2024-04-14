Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Lia.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Open Scope string_scope. Open Scope nat_scope.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[]" := nil.
Notation "[ x ]" := (cons x nil).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "| A |" := (length A) (at level 70).
Notation "x ++ y" := (app x y) (at level 60, right associativity).


Module Compiler.
(* Case study: Proving the correctness of a simple compiler *)


(* Source language *)


Notation var := string.
Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.

Infix "==v" := var_eq (no associativity, at level 50).


Inductive expr ( X : Type )  : Type :=
| Const : X -> expr X
| Var : var -> expr X
| Plus : expr X -> expr X -> expr X
| Bind : var -> expr X -> expr X -> expr X.

Arguments Const {X}.
Arguments Var {X}.
Arguments Plus {X}.
Arguments Bind {X}.

(* Properties about variables *)

(* Two variables are equal if they have the same string representation *)
Definition beq_id (x : var) (y : var) :=
  if (x ==v y)  then true else false.


(* Equality holds reflexivily for variables *)
Theorem beq_id_refl : forall var, true = beq_id var var.
Proof.
  intros. unfold beq_id. unfold var_eq.
  destruct (string_dec var var).
  - reflexivity.
  - destruct n. reflexivity.
Qed.

(* Conversely, if identiifer equality holds, then the variables 
   are semantically the same *)
Theorem beq_id_true_iff : forall x y : var,
  beq_id x y = true <-> x = y.
Proof.
   split.
   +  intros H. unfold beq_id in H. unfold var_eq in H.
      destruct (string_dec x y) in H.
      * assumption.
      * discriminate H.
   +  intros H. unfold beq_id. unfold var_eq. destruct (string_dec x y).
      * reflexivity.
      * unfold not in n. exfalso. apply n. assumption.
Qed.     

(* If syntactic equality fails, then variables are semantically distinct *)

Theorem beq_id_false_iff : forall x y : var,
  beq_id x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Theorem false_beq_id : forall x y : var,
   x <> y
   -> beq_id x y = false.
Proof.
  intros x y. rewrite beq_id_false_iff.
  intros H. assumption.
Qed.

(* Maps will be used to relate various kinds of objects (variables, registers, etc.) to values *)

Definition total_map (X A : Type) := X -> A.

Definition t_empty { X  A : Type } (v : A) : (total_map X A) :=
  (fun _ => v).

Definition t_update { X A : Type } (m : (total_map X A)) (eq: X -> X -> bool) (x : X) (v : A) :=
  fun x' => if (eq x x') then v else m x'.


(* A symbol table is a specific kind of map that relates variables to their values *)

Definition symt ( X : Type ) := total_map var X.

Definition empty_symt { X : Type } (init : X) := @t_empty var X init.

Definition symt_update { X : Type } (m : symt X) (x : var) (v : X) :=
  t_update m beq_id x v.

Definition symt_lookup { X : Type } (m : symt X) (x : var) : X :=  (m x).

Lemma symt_update_eq : forall { X : Type }  (m: symt X) x r,
  symt_update m x r x = r.
Proof.
  intros. unfold symt_update. unfold t_update. rewrite <- beq_id_refl. reflexivity.
Qed.  

Lemma symt_update_neq : forall {X : Type} v x1 x2 (m : symt X),
  x1 <> x2 ->
  (symt_update m x1 v) x2 = m x2.
Proof.
  intros.
  unfold symt_update.
  unfold t_update.
  rewrite false_beq_id.
  *  reflexivity.
  *  assumption.
Qed.

(* Source language interpreter *)

Fixpoint eval (s : symt nat) (e : expr nat) {struct e} :=
  match e with
  | Const n => n
  | Var x => symt_lookup s x
  | Bind x e1 e2 => match (eval s e1) with
                   | v => (eval (symt_update s x v) e2)
                   end
  | Plus e1 e2 => match (eval s e1) with
                 | v1 => match (eval s e2) with
                        | v2 => v1 + v2
                        end
                 end
  end.


(* ----------------------------------------- *)

(* Target *)
(* The target machine contains an accumulator and an infinite set
   of registers *)

Definition reg := nat.

(* memory cells *)
Inductive cell : Set := 
| Reg : reg -> cell
| Acc : cell.

(* Two memory cells are equal if they either (a) both denote an
   accumulator, or they are registers whose identity is the same *)
Definition cell_id x y :=
  match x,y with
    | Acc, Acc => true
    | (Reg r1), (Reg r2) => (r1 =? r2)
    | _,_ => false                                    
  end.

(* Similar properties hold for cells as they do for identifiers *)

(* 5 points *)
Theorem cell_refl : forall c, true = cell_id c c.
Proof.
intros.
unfold cell_id.
destruct c.
+ induction r. 
  ++ simpl. reflexivity.
  ++ simpl. apply IHr.
+ reflexivity.
Qed. 

(* 10 points *)
Theorem cell_true_iff : forall x y : cell,
  cell_id x y = true <-> x = y.
Proof.
intros.
split.
+ intros H. unfold cell_id in H. destruct x, y.
  ++ destruct r, r0.
     *  reflexivity.
     * discriminate.
     * discriminate.
     * simpl in H. apply Nat.eqb_eq in H. rewrite H. reflexivity.
  ++ destruct r.
     * discriminate.
     * discriminate.
  ++ discriminate.
  ++ reflexivity.
+ intros H. rewrite H. symmetry. apply cell_refl.
Qed.
     

(* 5 points *)
Theorem cell_false_iff : forall x y : cell,
  cell_id x y = false
  <-> x <> y.
Proof.
intros x y.
rewrite <- cell_true_iff. rewrite not_true_iff_false.
reflexivity.
Qed.

(* 5 points *)
Theorem false_beq_cell : forall x y : cell,
   x <> y
   -> cell_id x y = false.
Proof.
intros x y.
rewrite cell_false_iff. intros H. apply H. 
Qed.


(* The target machine's memory is a map that binds cells to the values they hold *)

Definition store := total_map cell nat.

Definition store_update (s : store) (c : cell) (v : nat) :=
  t_update s cell_id c v.
    
Definition empty_store := @t_empty cell nat 0.

Definition store_lookup (s : store) (c : cell) := (s c).

Lemma store_apply_empty:  forall A B x v, @t_empty A B v x = v.
Proof.
  reflexivity.
Qed.

(* 5 points *)
Lemma store_update_eq : forall (s: store) x v,
    (store_update s x v) x = v.
Proof.
 intros.
 unfold store_update, t_update.
 rewrite <- cell_refl.
 reflexivity.
Qed.
 
 

(* 5 points *)
Lemma store_update_neq : forall v x1 x2 (s : store),
  x1 <> x2 ->
  (store_update s x1 v) x2 = s x2.
Proof.
intros.
unfold store_update, t_update.
rewrite false_beq_cell.
- reflexivity.
- apply H.
Qed.




(* syntax of the target language *)

(* There are four instructions in the target machine:                     *)
(*   (1) LI n :     loads the accumulator with the constant n             *)
(*   (2) LOAD r :   loads the accumulator with the contents of register r *)
(*   (3) STO r  :   stores the contents of the accumulator to register r  *)
(*   (4) ADD r  :   adds the contents of register and the accumulator and *)
(*                    stores the result back into the accumulator         *)

Inductive instr : Set :=
|LI : nat -> instr
|LOAD : reg -> instr
|STO : reg -> instr
|ADD : reg -> instr.

(* Target machine interpreter for a single instruction *)

Definition Si (s : store) (i : instr) : store :=
match i with
|LI n => store_update s Acc n
|LOAD r => store_update s Acc (store_lookup s (Reg r))
|STO r => store_update s (Reg r) (store_lookup s Acc)
|ADD r => store_update s Acc ((store_lookup s Acc) + (store_lookup s (Reg r)))
end.

(* Interpreting a list of instructions *)
Fixpoint Sl (s : store) (l : list instr) {struct l} : store :=
match l with   
 |nil => s
 |(cons x l') => Sl (Si s x) l'
end.


(* a register table maps identifiers to the registers that hold their values *)

Definition regt := total_map var reg.

Definition empty_regt := @t_empty var reg 0.

Definition regt_update (m : regt) (x : var) (r : reg) :=
  t_update m beq_id x r.

Definition regt_lookup (m : regt) (x : var) :=  (m x).

(* 5 points *)
Lemma regt_update_eq : forall (m: regt) x r,
  regt_update m x r x = r.
Proof.
intros.
unfold regt_update, t_update.
rewrite <- beq_id_refl.
reflexivity.
Qed.


(* 5 points *)
Lemma regt_update_neq : forall v x1 x2 (m : regt),
  x1 <> x2 ->
  (regt_update m x1 v) x2 = m x2.
Proof.
intros.
unfold regt_update, t_update.
rewrite false_beq_id.
- reflexivity.
- apply H.
Qed.


(* ------------------------------------------------------------------- *)
(* The compiler is defined as an inductively defined proposition that  *)
(* relates source level expressions (e) with the compiled list of      *)
(* target instructions (l).  Specifically:                             *)
(*    c_const: compiles (Const n) to (LI n)                            *)
(*    c_deref: compiles (Var x) to (LOAD (m x)) where m is the         *)
(*             current register table                                  *)
(*    c_add:   compiles expression e1 and e2 found in (Plus e1 e2) to  *)
(*             a list of instructions l1 and l2, resp., and emits the  *)
(*             code sequence for add, consisting of l1 appended by     *)
(*             [STO r] that takes the contents of the accumulator and  *)
(*             stores it in register r (an argument to the relation),  *)
(*             then appends l2, and finally emits an (ADD r)           *)
(*             instruction that adds the contents of the accumulator   *)
(*             with the contents of r, and stores the contents back    *)
(*             into the accumulator.                                   *)
(*    c_bind:  Given an expression of the form (Bind x e1 e2),compiles *) 
(*             e1 to a list of instructions (l1),then compiles e2 to a *)
(*             list of instructions (l2) in the context of an updated  *)
(*             register table that maps x to register r, finally       *)
(*             emitting an instruction sequence consisting of l1,      *)
(*             a (STO r) instruction that stores the value of the      *)
(*             accumulator at the end of executing l1 to register      *)
(*             register r, followed by l2.                             *)
(***********************************************************************)
  

Inductive C : regt -> reg -> expr nat -> list instr -> Prop :=
|c_const (m : regt) (r : reg) (e : expr nat) (l : list instr) (n : nat) :
   (C m r (Const n) [LI n])
|c_deref (m: regt) (r : reg) (e : expr nat) (l : list instr) (x : var) :
   (C m r (Var x) [LOAD (m x)])
|c_add (m : regt) (r : reg) (e1 e2: expr nat) (l1 l2 : list instr) :
   (C m r e1 l1) ->
   (C m (r + 1) e2 l2) ->
   (C m r (Plus e1 e2) (l1 ++ [STO r] ++ l2 ++ [ADD r]))
|c_bind (m : regt) (r : reg) (x : var) (e1 e2: expr nat) (l1 l2 : list instr) :
   (C m r e1 l1) ->
   (C (regt_update m x r) (r+1) e2 l2) ->
   (C m r (Bind x e1 e2) (l1 ++ [STO r] ++ l2)).


(************************************************************************)
(* Properties                                                           *)
(************************************************************************)

(* Executing a list of instructions (l1 ++ l2) is the same as executing *)
(* l1 and then executing l2 in the context of the store produced by     *)
(* executing l1.                                                        *)

(* 5 points *)
Lemma Sl_append :
  forall (l1 l2 : list instr) (s : store), Sl s (l1 ++ l2) = Sl (Sl s l1) l2.
Proof.
intros l1.
induction l1 as [ | l1' l2'].
- simpl. reflexivity.
- simpl. intros l2 s. apply IHl2'.
Qed.  
 


(* Executing a list of instructions never modifies the contents of the  *)
(* store with respect to registers whose index is smaller than the      *)
(* current register used to hold the result of the compiled expression  *)
(* In other words, a register is only written to at most once.          *)

(* 20 points *)
Lemma Sl_invariant:
    forall (e : expr nat) (m : regt) (st : store) (r r' : reg) (l : list instr),
        r' < r  -> 
        (C m r e l) ->
        Sl st l (Reg r')  = st (Reg r').
Proof.
intros e.
induction e.
- simpl. intros. inversion H0. reflexivity.
- simpl. intros. inversion H0. reflexivity.
- intros. inversion H0. rewrite Sl_append. rewrite Sl_append. rewrite Sl_append.
simpl. rewrite store_update_neq. 
  + rewrite IHe2 with (m := m) (st:= store_update (Sl st l1) (Reg r) (store_lookup (Sl st l1) Acc)) (r:= r+1) (r':=r') (l:=l2).
    ++ rewrite store_update_neq. 
        +++ rewrite IHe1 with (l:=l1)(m := m)(r:=r). 
             ++++  reflexivity.
             ++++  apply H.
             ++++  apply H5.
        +++  injection. intros. lia.
    ++ lia.
    ++ apply H7.
  +  discriminate.
- intros. inversion H0. rewrite Sl_append. rewrite Sl_append. 
simpl. rewrite IHe2 with (m:=regt_update m s r) (st:= store_update (Sl st l1) (Reg r) (store_lookup (Sl st l1) Acc)) (r := r+1)(r' := r') (l:=l2).
  + rewrite store_update_neq. 
    ++ rewrite IHe1 with (m:=m)(r:=r)(l:=l1).
       +++ reflexivity.
       +++ apply H.
       +++ apply H7.
    ++ injection. intros. lia.
  + lia.
  + apply H8.
Qed. 


(* Executing the compilation of e produces the same result as interpreting e       *)
(* - the final result is always stored in the accumulator.  This property          *)
(* assumes that the register table maps every variable to a register smaller       *)
(* than the one used to evaluate the expression, and that the interpreter symbol   *)
(* table and the memory store agree on all values.                                 *)



Lemma HA : forall n : nat, 0 = S n + 0 -> False.
Proof.
  intros n H.
  discriminate.
Qed.

(* 30 points *)
Theorem correctness :
  forall (e : expr nat) (m : regt) (r : reg) (l : list instr) (st : store) (sym: symt nat),
    (C m r e l) ->
    (forall (v : var), (m v) < r) ->
    (forall (v : var), sym v = st (Reg (m v))) ->  Sl st l Acc = eval sym e.
Proof.
intros e.
induction e.
- simpl. intros. inversion H. reflexivity. 
- simpl. intros. inversion H. simpl. unfold store_update. unfold t_update. rewrite <- cell_refl.
unfold store_lookup. unfold symt_lookup. rewrite H1. reflexivity.
- intros. inversion H. rewrite Sl_append. rewrite Sl_append. rewrite Sl_append. simpl. rewrite store_update_eq.
unfold store_lookup.
rewrite IHe2 with (m:=m) (r:= r+1)(l:= l2)(st:= store_update (Sl st l1) (Reg r) (Sl st l1 Acc)) (sym:=sym).
  + rewrite Sl_invariant with (e := e2) (m := m) (st := (store_update (Sl st l1) (Reg r) (Sl st l1 Acc))) (r:= r+1)(l := l2) (r':=r).
    ++ rewrite store_update_eq. rewrite IHe1 with (m:= m) (r:=r) (sym:=sym)(l:=l1).
        +++ lia.
        +++ apply H6.
        +++ apply H0.
        +++ apply H1.
    ++ lia.
    ++ apply H8.
  + apply H8. 
  + intros. rewrite H0. lia.
  + intros. rewrite store_update_neq.
    ++ rewrite Sl_invariant with (e:=e1) (m := m) (st := st) (r:= r)(l := l1) (r':= m v). apply H1.
       +++ apply H0.
       +++ apply H6.
    ++ assert(Hmvr: forall v : var, m v < r -> Reg r <> Reg (m v)). { intros. injection. lia. }
       +++  apply Hmvr. apply H0.
- simpl. intros. inversion H. simpl. rewrite Sl_append. simpl. unfold store_update. unfold store_lookup. unfold symt_update.
rewrite IHe1 with (m:=m) (r:=r) (l:=l1) (st:=st) (sym:=sym).
rewrite IHe2 with (m:=t_update m beq_id s r) (r :=r+1) (l := l2) (st := t_update (Sl st l1) cell_id (Reg r) (eval sym e1)) (sym := (t_update sym beq_id s (eval sym e1))).
 + reflexivity.
 + apply H9.
 + unfold t_update. intros. destruct (beq_id s v).
   ++ lia.
   ++ rewrite H0. lia.
 + simpl. unfold t_update. intros. destruct (beq_id s v); simpl.
   ++ rewrite Nat.eqb_refl. reflexivity.
   ++ assert(Hlt_mvr: forall (m: regt) (r: reg) (v: var), m v < r -> r <> m v). { intros. lia. }
      assert ((r =? m v) = false). { apply Nat.eqb_neq. apply Hlt_mvr. apply H0. }
      rewrite H10. rewrite H1.
      rewrite Sl_invariant with  e1 m st r (m v) l1. reflexivity.
      apply H0. 
      apply H8.
 + apply H8.
 + apply H0.
 + apply H1.
Qed.
 
End Compiler.
