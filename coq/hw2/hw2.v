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


Module Review.
(* Review of exercises in Tactics.v, Poly.v, List.v *)

Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.


Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold (fun x => fun acc => (f x) :: acc) l [].


(* 5 points *)
Theorem fold_map_correct: forall X Y (f : X->Y) (l : list X),
    fold_map f l = map f l.
Proof.
intros X Y f l.
induction l as [ | l' ll' IHl'].
- simpl.
reflexivity.
- simpl.
rewrite <- IHl'.
reflexivity.
Qed.

(* You might find plus_n_Sm useful here *)
(* 10 points *)
Theorem plus_n_Sm: forall n m : nat, S (n + m) = n + S m.
Proof.
intros n m.
induction n as [|n'].
- simpl.
reflexivity.
- simpl.
rewrite -> IHn'.
+ simpl.
reflexivity.
Qed.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
intros n.
induction n as [|n' IHn'].
-simpl.
intros m eq.
destruct m as [|m'] eqn:E.
+ simpl.
reflexivity.
+ simpl.
discriminate.
- simpl.
intros m eq.
destruct m as [|m'] eqn:E.
+ simpl.
discriminate.
+ simpl in eq.
f_equal.
injection eq as goal.
rewrite<-plus_n_Sm in goal.
rewrite<-plus_n_Sm in goal.
injection goal as goal'.
apply IHn' in goal'.
apply goal'.
Qed.



Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

(** Prove that [split] and [combine] are inverses in the following
    sense: *)
(*10 points *)
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| l' ll' IHl'].
  - simpl. 
    intros l1 l2 eq. 
    injection eq as eq1 eq2. 
    rewrite <- eq1.
    rewrite <- eq2. 
    reflexivity.
  - simpl.
    destruct l' as [l1' l2']. 
    destruct (split ll'). 
    intros l1 l2 eq. 
    injection eq as eq1 eq2.
    rewrite <- eq1.
    rewrite <- eq2. 
    simpl.
    assert ( Hc : combine l l0 = ll'). 
    + apply IHl'.  
    reflexivity.
    + rewrite -> Hc.
    reflexivity.
Qed.


End Review.

Module ArithWithVariables.

  Notation var := string.
  Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.

  Infix "==v" := var_eq (no associativity, at level 50).

  (* We now consider a variant of the language discussed in hw1 to support variables *)
  Inductive exp  : Type :=
  | Const (n : nat)
  | Var (x : var) 
  | Plus (e1 e2 : exp).

(* An interpreter for arithmetic expressions *)

Inductive binding (X : Type) : Type :=
    | pair (x : var) (v : X).

Inductive lookupTable (X : Type) : Type :=
  | empty
  | cons (x : binding X) (l : (lookupTable X)).
  
Fixpoint lookup { X : Type } (l : (lookupTable X)) (x : var)  :=
    match l with
    | empty _  => None
    | cons _ (pair _ y v) l' => if (x ==v y)
                           then Some v
                           else lookup l' x
    end.
  
Fixpoint interp (e : exp) (l : lookupTable nat) :=
    match e with
    | Const n => n
    | Var x =>
        match (lookup l x) with
        | None => 0 
        | Some n => n
        end
    | Plus e1 e2 => interp e1 l + interp e2 l
    end.

(* Properties *)

Fixpoint swap (e : exp) : exp :=
    match e with
    | Const _ => e
    | Var _ => e
    | Plus e1 e2 => Plus (swap e2) (swap e1)
    end.

(* 5 points*)
Theorem swap_ok : forall l e, interp (swap e) l = interp e l.
Proof.
intros l e.
induction e.
- simpl.
reflexivity.
- simpl.
  lia.
- simpl.
  rewrite IHe1.
  rewrite IHe2.
  lia.
Qed.

(* changing the name of variables uniformily does not change the meaning of a program *)
Fixpoint alpha (e : exp) (x : var) (y : var) : exp :=
    match e with
    | Const _ => e
    | Var z  => if (z ==v x) then (Var y) else (Var z)
    | Plus e1 e2 => Plus (alpha e1 x y) (alpha e2 x y)
    end. 
  

(* 10 points *)
Theorem alpha_ok : forall x y l e, lookup l x = lookup l y ->
                              interp (alpha e x y) l = interp e l.
Proof.
  intros.
  induction e.
-simpl. reflexivity.
-simpl. destruct (x0 ==v x).
  + unfold interp. rewrite <- H. symmetry. rewrite e. reflexivity.
  + unfold interp. reflexivity.
- simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.


End ArithWithVariables.  

Module BindVariables.


Notation var := string.
Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.

Infix "==v" := var_eq (no associativity, at level 50).

  
(* Identifiers *)

(* Yet another variant of a language of arithmetic expressions.  This time, we introduce a binding
   scope - the expression (bind x e1 e2) introduces a new scope that binds x to the result of
   evaluating e1, and evaluates e2 in the context of that binding.  We extract that value bound to
   a variable using Var.                                
 *)

Inductive expr ( X : Type )  : Type :=
| Const : X -> expr X
| Var : var -> expr X
| Plus : expr X -> expr X -> expr X
| Bind : var -> expr X -> expr X -> expr X.

Arguments Const {X}.
Arguments Var {X}.
Arguments Plus {X}.
Arguments Bind {X}.

(* Two identifers are equal if they have the same string representation *)
Definition beq_id (x : var) (y : var) :=
  if (x ==v y)  then true else false.


(* Equality holds reflexivily for identifers *)
(* 5 points *)
Theorem beq_id_refl : forall id, true = beq_id id id.
Proof.
intros id.
unfold beq_id.
destruct (id ==v id).
- simpl.
reflexivity.
- destruct n.
reflexivity.
Qed.


(* Conversely, if identiifer equality holds, then the identifiers 
   are semantically the same *)
(* 10 points *)
Theorem beq_id_true_iff : forall x y : var,
  beq_id x y = true <-> x = y.
Proof.
intros x y.
unfold beq_id.
destruct (x ==v y).
- split.
+ intros H.
  rewrite e.
  reflexivity.
+ intros H.
  reflexivity.
- split.
+ intros H.
  discriminate.
+ intros H.
  destruct n.
  apply H.
Qed. 



(* If syntactic equality fails, then the identifiers are semantically distinct *)
(* 5 points *)
Theorem beq_id_false_iff : forall x y : var,
  beq_id x y = false
  <-> x <> y.
Proof.
intros x y.
unfold beq_id.
destruct (x ==v y).
- split.
+ intros H.
  discriminate.
+ intros H.
  destruct (H).
  apply e.
- split.
+ intros H.
  apply n.
+ intros H.
  reflexivity.
Qed.


(* 5 points *)
Theorem false_beq_id : forall x y : var,
   x <> y
   -> beq_id x y = false.
Proof.
intros x y H.
unfold beq_id.
destruct (x ==v y).
+ destruct (H).
apply e.
+ reflexivity.
Qed.
  
(* Maps are used to relate different kinds of objects, and are particularly useful
   to relate variables and the value to which they are bound *)

Definition total_map (X A : Type) := X -> A.

Definition t_empty { X  A : Type } (v : A) : (total_map X A) :=
  (fun _ => v).

Definition t_update { X A : Type } (m : (total_map X A)) (eq: X -> X -> bool) (x : X) (v : A) :=
  fun x' => if (eq x x') then v else m x'.

(* a symbol table is a specific kind of map that relates identifiers to their values *)

Definition symt ( X : Type ) := total_map var X.

Definition empty_symt { X : Type } (init : X) := @t_empty var X init.

Definition symt_update { X : Type } (m : symt X) (x : var) (v : X) :=
  t_update m beq_id x v.

Definition symt_lookup { X : Type } (m : symt X) (x : var) : X :=  (m x).

(* 5 points *)
Lemma symt_update_eq : forall { X : Type }  (m: symt X) x r,
  symt_update m x r x = r.
Proof.
intros.
unfold symt_update.
unfold t_update.
unfold beq_id.
destruct (x==v x).
- simpl. reflexivity.
- simpl. destruct n. reflexivity.
Qed.



(* 5 points *)
Lemma symt_update_neq : forall {X : Type} v x1 x2 (m : symt X),
  x1 <> x2 ->
  (symt_update m x1 v) x2 = m x2.
Proof.
intros.
unfold symt_update.
unfold t_update.
unfold beq_id.
destruct (x1==v x2).
- simpl. destruct (H). apply e. 
- simpl. reflexivity.
Qed.


(* The interpreter *)
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


(* A constant-folding optimization *)
Fixpoint foldConstants (e : expr nat) : expr nat :=
  match e with
  | Const _ => e
  | Var _ => e
  | Bind x e1 e2 => Bind x e1 (foldConstants e2)
  | Plus e1 e2 =>  match e1, e2 with
                 | Const  n1, Const n2 => Const  (n1 + n2)
                 | Const 0, e2 => e2
                 | e1, Const 0 => e1
                 | _ , _ => e
                 end
  end.


Fixpoint size (e : expr nat) : nat :=
  match e with
  | Const _ => 1
  | Var _ => 1
  | Bind _ e1 e2 => 1 + size e1 + size e2
  | Plus e1 e2 => 1 + size e1 + size e2
  end.

(* 10 points *)
Theorem size_foldConstants:
  forall e, size (foldConstants e) <= size e.
Proof.
intros.
induction e.
- simpl. lia.
- simpl. lia.
- simpl. destruct e1.
  + destruct n. 
      * destruct e2.
         ** simpl. lia.
         ** simpl. lia.
         ** simpl. lia.
         ** simpl. lia.
      * destruct e2.
         ** simpl. lia. 
         ** simpl. lia.
         ** simpl. lia.
         ** simpl. lia.
  + destruct e2.
      * destruct n.
         ** simpl. lia.
         ** simpl. lia.
      * simpl. lia.
      * simpl. lia.
      * simpl. lia.
  + destruct e2.
      * destruct n.
         ** simpl. lia.
         ** simpl. lia.
      * simpl. lia.
      * simpl. lia.
      * simpl. lia.
  + destruct e2.
      * destruct n.
         ** simpl. lia.
         ** simpl. lia.
      * simpl. lia.
      * simpl. lia.
      * simpl. lia.
- simpl. lia.
Qed.


(* 15 points *)
Lemma foldConstantsSafe : forall (e : expr nat) (s : symt nat),
    eval s e = eval s (foldConstants e).
Proof.

intros e. induction e.
- simpl. reflexivity.
- simpl. reflexivity.
- simpl. destruct e1.
  + destruct n, e2.
    ++ simpl. reflexivity.
    ++ simpl. reflexivity.
    ++ simpl. reflexivity.
    ++ simpl. reflexivity.
    ++ simpl. reflexivity.
    ++ simpl. reflexivity.
    ++ simpl. reflexivity.
    ++ simpl. reflexivity.
  + simpl. destruct e2.
    ++ destruct n.
      * simpl. intros H. apply Nat.add_0_r.
      * simpl. reflexivity.
    ++ simpl. reflexivity.
    ++ simpl. reflexivity.
    ++ simpl. reflexivity.
  + simpl. destruct e2.
    ++ destruct n.
      * simpl. intros H. apply Nat.add_0_r.
      * simpl. reflexivity.
    ++ simpl. reflexivity.
    ++ simpl. reflexivity.
    ++ simpl. reflexivity.
  + simpl. destruct e2.
    ++ destruct n.
      * simpl. intros H. apply Nat.add_0_r.
      * simpl. reflexivity.
    ++ simpl. reflexivity. 
    ++ simpl. reflexivity.
    ++ simpl. reflexivity.
- intros H. apply IHe2.
Qed.

End BindVariables.