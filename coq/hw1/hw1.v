Set Implicit Arguments.
Require Import Lia.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.
From LF Require Export Basics.

(* Homework 1 *)
(* Due date: January 29, 2024 *)

(* Part 1 - Exercises.  30 points *)
Module Review.

  (* 3 points *)
  Theorem zero_neqb_S : forall n:nat,
      0 =? (S n) = false.
  Proof.
  intros n.
  simpl.
  reflexivity.
  Qed.
  
  (* 5 points *)
  (* Hint: You will eventually need to destruct both booleans, as in
     the theorems above. But its best to delay introducing the
     hypothesis until after you have an opportunity to simplify it.

     Hint 2: When you reach a contradiction in the hypotheses, focus on
     how to [rewrite] with that contradiction. *)

  Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
  Proof.
  intros b c.
  destruct b eqn:Eb.
  - simpl.
  intros H.
  rewrite -> H.
  reflexivity.
  - simpl.
  destruct c eqn:Ec.
  + simpl.  (*Ignore the hypothesis*)
  intros H.
  reflexivity. 
  + simpl.
  intros H1. (*proving by contradiction*)
  rewrite -> H1.
  reflexivity.
  Qed.

  (* 3 points *)
  Theorem andb_false_r : forall b : bool,
      andb b false = false.
  Proof.
  intros b.
  destruct b eqn:Eb.
  - simpl.
  reflexivity.
  - simpl.
  reflexivity.
  Qed.
  
  (* 5 points *)
  Theorem leb_refl : forall n:nat,
      (n <=? n) = true. 
  Proof.
  intros n.
  induction n as [| n' IHn'].
  -simpl.
  reflexivity.
  -simpl.
  rewrite -> IHn'.
  reflexivity.
  Qed.

  (* 4 points *)
  Theorem all3_spec : forall b c : bool,
      orb
        (andb b c)
        (orb (negb b)
           (negb c))
      = true.
  Proof.
  intros b c.
  destruct b eqn:Eb.
  - simpl.
  destruct c eqn:Ec.
  + simpl.
  reflexivity.
  + simpl.
  reflexivity.
  - simpl.
  reflexivity.
  Qed.
  
  (* 5 points *)
  Theorem add_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
  Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
  Qed.

  Theorem mult_plus_distr_r : forall n m p : nat,
      (n + m) * p = (n * p) + (m * p).
  Proof.
  intros n m p.
  induction n as [| n' IH].
  - simpl.
  reflexivity.
  - simpl.
  rewrite -> IH.
  rewrite add_assoc.
  reflexivity.
  Qed.

  (* 5 points *)
  Theorem mult_assoc : forall n m p : nat,
      n * (m * p) = (n * m) * p.
  Proof.
  intros n m p.
  induction n as [| n' IHn].
  - simpl.
  reflexivity.
  - simpl.
  rewrite IHn.
  rewrite mult_plus_distr_r.
  reflexivity.
  Qed.
End Review.


(* Part 2: Case Study - A language of simple arithmetic expressions - 70 points *)

Module SimpleArithmetic.
  
  Inductive exp : Set :=
  | Const (v : nat)
  | Plus (e1 e2 : exp)
  | Minus (e1 e2 : exp)
  | Times (e1 e2 : exp).


  (* Examples. *)
  Example ex1 := Const 42.
  Example ex2 := Plus (Const 1) (Times (Const 2) (Const 3)).
   
  (* A function to compute the size of an arithmetic expression *)
  Fixpoint size (e : exp) : nat :=
    match e with
    | Const _ => 1
    | Plus e1 e2 => 1 + size e1 + size e2
    | Minus e1  e2 => 1 + size e1 + size e2                                      
    | Times e1 e2 => 1 + size e1 + size e2
    end.

  
  (* A function to compute the height of an expression *)
  Fixpoint height (e : exp) : nat :=
    match e with
    | Const _ => 1
    | Plus e1 e2 => 1 + max (height e1) (height e2)
    | Minus e1 e2 => 1 + max (height e1) (height e2)                           
    | Times e1 e2 => 1 + max (height e1) (height e2)
    end.


  (* 5 points *)
  Theorem height_to_size : forall e, height e <= size e.
    (* you may need to use the lia tactic in this proof as well others in this
       module. *)
  Proof.
    intros e.
    induction e.
    - simpl.
    lia.
    - simpl.
    lia.
    - simpl.
    lia.
    - simpl.
    lia.
  Qed.
  
  (* A simple transformation over expressions - arguments can be swapped in 
     commutative operations *)
  Fixpoint swap (e : exp) : exp :=
    match e with
    | Const _ => e
    | Plus e1 e2 => Plus (swap e2) (swap e1)
    | Minus e1 e2 => Minus (swap e1) (swap e2)                        
    | Times e1 e2 => Times (swap e2) (swap e1)
    end.

  (* 5 points *)
  Theorem swap_preserves_size : forall e, size (swap e) = size e.
  Proof.
    intros e.
    induction e.
    - simpl.
    reflexivity.
    - simpl.
    rewrite -> IHe1.
    rewrite -> IHe2.
    lia.
   - simpl.
    rewrite -> IHe1.
    rewrite -> IHe2.
    lia.
   - simpl.
    rewrite -> IHe1.
    rewrite -> IHe2.
    lia.
  Qed.
  
  (* 10 points *)
  Theorem swap_preserves_depth_ : forall e, height (swap e) = height e.
  Proof.
    intros e.
    induction e.
   - simpl.
    reflexivity.
   - simpl.
    rewrite -> IHe1.
    rewrite -> IHe2.
    lia.
   - simpl.
    rewrite -> IHe1.
    rewrite -> IHe2.
    lia.
   - simpl.
    rewrite -> IHe1.
    rewrite -> IHe2.
    lia.
  Qed.
  
  (* 10 points *)
  Theorem swap_involutive : forall e, swap (swap e) = e.
  Proof.
    intros e.
    induction e.
   - simpl.
    reflexivity.
   - simpl.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
   - simpl.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
   - simpl.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
  Qed.
End SimpleArithmetic.

Module ArithWithVariables.

  Notation var := string.
  Definition var_eq : forall x y : var, {x = y} + {x <> y} := string_dec.

  Infix "==v" := var_eq (no associativity, at level 50).

  (* We now extend the language to support variables *)
  Inductive exp : Set :=
  | Const (n : nat)
  | Var (x : var) 
  | Plus (e1 e2 : exp)
  | Minus (e1 e2 : exp)
  | Times (e1 e2 : exp).

 Fixpoint size (e : exp) : nat :=
   match e with
   | Const _ => 1
   | Var _ => 1
   | Plus e1 e2 => 1 + size e1 + size e2
   | Minus e1 e2 => 1 + size e1 + size e2                                      
   | Times e1 e2 => 1 + size e1 + size e2
   end.

 Fixpoint height (e : exp) : nat :=
    match e with
    | Const _ => 1
    | Var _ => 1
    | Plus e1 e2 => 1 + max (height e1) (height e2)
    | Minus e1 e2 => 1 + max (height e1) (height e2)                           
    | Times e1 e2 => 1 + max (height e1) (height e2)
    end.


  (* This operator replaces all variable occurrences with arithmetic expressions *)
  Fixpoint sub (org : exp) (subject : var) (target : exp) : exp :=
    match org with
    | Const _ => org
    | Var x => if x ==v subject then target else org
    | Plus e1 e2 => Plus (sub e1 subject target) (sub e2 subject target)
    | Minus e1 e2 => Minus (sub e1 subject target) (sub e2 subject target)
    | Times e1 e2 => Times (sub e1 subject target) (sub e2 subject target)
    end.

  (* This operator swaps the order of arguments in Plus and Times *)
  Fixpoint swap (e : exp) : exp :=
    match e with
    | Const _ => e
    | Var _ => e
    | Plus e1 e2 => Plus (swap e2) (swap e1)
    | Minus e1 e2 => Minus (swap e1) (swap e2)                        
    | Times e1 e2 => Times (swap e2) (swap e1)
    end.

  (* This operator replaces all occurrences of a variable x with variable y *)
  Fixpoint alpha (e : exp) (x : var) (y : var) : exp :=
    match e with
    | Const _ => e
    | Var z  => if (z ==v x) then (Var y) else (Var z)
    | Plus e1 e2 => Plus (alpha e1 x y) (alpha e2 x y)
    | Minus e1 e2 => Minus (alpha e1 x y) (alpha e2 x y)
    | Times e1 e2 => Times (alpha e1 x y) (alpha e2 x y)
    end. 

  (* 10 points *)
  Theorem swap_inverse : forall e, swap (swap e) = e.
  Proof.
    intros e.
    induction e.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
  - simpl.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
  - simpl.
    rewrite IHe1.
    rewrite IHe2.
    reflexivity.
  Qed.
  
  (* 15 points *)
  Theorem substitute_height : forall subject target org,
      height (sub org subject target) <= height org + height target.
  Proof.
    intros subject target org.
    induction org.
    - simpl.
    lia.
    - simpl.
    destruct (x ==v subject) eqn:H.
    + simpl.
    lia.
    + simpl.
    lia.
    - simpl.
    lia.
    - simpl.
    lia.
    - simpl.
    lia.
  Qed.

  (* 15 points *)
  Theorem substitute_swap : forall subject target org,
      swap (sub org subject target) =
      sub (swap org) subject (swap target).
  Proof.
    intros subject target org.
    induction org.
    - simpl.
    reflexivity.
    - simpl.
    destruct (x ==v subject) eqn:H.
    + simpl.
    reflexivity.
    + simpl.
    reflexivity.
    - simpl.
    rewrite -> IHorg1.
    rewrite -> IHorg2.
    * simpl.
    reflexivity.
    - simpl.
    rewrite -> IHorg1.
    rewrite -> IHorg2.
    reflexivity.
    - simpl.
    rewrite -> IHorg1.
    rewrite -> IHorg2.
    reflexivity.
  Qed.

End ArithWithVariables.