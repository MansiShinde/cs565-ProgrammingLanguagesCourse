Set Implicit Arguments.
Require Import Lia.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.EqNat.
Require Import Coq.Bool.Bool.

Check true.

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.


(* this new type is called day and its members are monday tuesday etc *)
(*writing the function which operates on day*)

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

(*command Compute to evaluate a compound expression involving next_weekday.*)

Compute (next_weekday friday).


Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.


Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).


Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Compute (monochrome white).


Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ =>false
  end.

Module Playground.
  Definition foo : rgb := blue.
End Playground.

Definition foo : bool := true.

Check Playground.foo : rgb.
Check foo : bool.


Module TuplePlayground.
Inductive bit : Type :=
  | B1
  | B0.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0)
  : nybble.

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).

Compute (all_zero (bits B0 B0 B0 B0)).


End TuplePlayground.


Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.


Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

End NatPlayground.


Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool :=
  negb (even n).
Example test_odd1: odd 1 = true.
Proof. 
simpl. 
reflexivity. 
Qed.


Theorem plus_O_n'' : forall n : nat, 0 + n = n.
Proof.
  intros m.
  simpl.
  reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n.
  simpl.
  reflexivity. Qed.


Theorem plus_id_example : forall n m:nat,
  n = m -> n + n = m + m.
  Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
  Qed.


Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
  Proof.
    intros n m o.
    intros H.
    intros H1.
    rewrite -> H.
    rewrite -> H1.
    reflexivity.
    Qed.
  
Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. 
  Qed.

Check mult_n_Sm.

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
intros p.
rewrite <- mult_n_Sm.
rewrite <- mult_n_O.
reflexivity.
Qed.


  Theorem zero_neqb_S : forall n:nat,
      0 =? (S n) = false.
  Proof.
  intros n.
  simpl.
  reflexivity.
  Qed.


Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
intros n.
destruct n as [| n'] eqn:E.
- reflexivity.
- reflexivity.
Qed.


Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. 
  destruct b eqn:E.
  - reflexivity.
  - reflexivity. 
  Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. 
  destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

  
Theorem andb_false_r : forall b : bool,
      andb b false = false.
Proof.
  intros b.
  destruct b eqn:Eb.
  - reflexivity.
  - reflexivity.
Qed.


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
+ simpl.
reflexivity.
+ simpl.
intros H1.
rewrite -> H1.
reflexivity.
Qed.


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

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
intros n m p.
induction n as [| n' IHn'].
- simpl.
reflexivity.
- simpl.
rewrite IHn'.
reflexivity.
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


Theorem mult_assoc : forall n m p : nat,
      n * (m * p) = (n * m) * p.
Proof.
intros n m p.
induction n as [| n' IHn'].
- simpl.
reflexivity.
- simpl.
rewrite IHn'.
rewrite mult_plus_distr_r.
reflexivity.
Qed.












