Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PLF Require Export Imp.
From PLF Require Export Hoare.


(* ================================================================= *)
(** ** Assert and Assume *)

(*  In this exercise, we will extend IMP with two commands, [assert]
    and [assume]. Both commands are ways to indicate that a certain
    statement should hold any time this part of the program is
    reached. However they differ as follows:

    - If an [assert] statement fails, it causes the program to go into
      an error state and exit.

    - If an [assume] statement fails, the program fails to evaluate at
      all. In other words, the program gets stuck and has no final
      state.

    The new set of commands is: *)

Module HoareAssertAssume.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CAssert : bexp -> com
  | CAssume : bexp -> com.

Notation "'assert' l" := (CAssert l)
                           (in custom com at level 8, l custom com at level 0).
Notation "'assume' l" := (CAssume l)
                          (in custom com at level 8, l custom com at level 0).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

(** To define the behavior of [assert] and [assume], we need to add
    notation for an error, which indicates that an assertion has
    failed. We modify the [ceval] relation, therefore, so that
    it relates a start state to either an end state or to [error].
    The [result] type indicates the end value of a program,
    either a state or an error: *)

Inductive result : Type :=
  | RNormal : state -> result
  | RError : result.

(** Now we are ready to give you the ceval relation for the new language. *)

Inductive ceval : com -> state -> result -> Prop :=
  (* Old rules, several modified *)
  | E_Skip : forall st,
      st =[ skip ]=> RNormal st
  | E_Asgn  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x := a1 ]=> RNormal (x !-> n ; st)
  | E_SeqNormal : forall c1 c2 st st' r,
      st  =[ c1 ]=> RNormal st' ->
      st' =[ c2 ]=> r ->
      st  =[ c1 ; c2 ]=> r
  | E_SeqError : forall c1 c2 st,
      st =[ c1 ]=> RError ->
      st =[ c1 ; c2 ]=> RError
  | E_IfTrue : forall st r b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_IfFalse : forall st r b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> r ->
      st =[ if b then c1 else c2 end ]=> r
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> RNormal st
  | E_WhileTrueNormal : forall st st' r b c,
      beval st b = true ->
      st  =[ c ]=> RNormal st' ->
      st' =[ while b do c end ]=> r ->
      st  =[ while b do c end ]=> r
  | E_WhileTrueError : forall st b c,
      beval st b = true ->
      st =[ c ]=> RError ->
      st =[ while b do c end ]=> RError
  (* Rules for Assert and Assume *)
  | E_AssertTrue : forall st b,
      beval st b = true ->
      st =[ assert b ]=> RNormal st
  | E_AssertFalse : forall st b,
      beval st b = false ->
      st =[ assert b ]=> RError
  | E_Assume : forall st b,
      beval st b = true ->
      st =[ assume b ]=> RNormal st

where "st '=[' c ']=>' r" := (ceval c st r).

(** We redefine hoare triples: Now, [{{P}} c {{Q}}] means that,
    whenever [c] is started in a state satisfying [P], and terminates
    with result [r], then [r] is not an error and the state of [r]
    satisfies [Q]. *)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st r,
     st =[ c ]=> r  -> P st  ->
     (exists st', r = RNormal st' /\ Q st').

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.

(** To test your understanding of this modification, give an example
    precondition and postcondition that are satisfied by the [assume]
    statement but not by the [assert] statement. *)


(* 10 points *)
Theorem assert_assume_differ : exists (P:Assertion) b (Q:Assertion),
       ({{P}} assume b {{Q}})
       /\ ~ ({{P}} assert b {{Q}}).
Proof.
exists (fun st => True).
exists (BFalse).
exists (fun st' => False).
split.
- unfold hoare_triple. 
  intros. 
  inversion H. subst. 
  inversion H2.
- unfold hoare_triple, not.
  intros. 
  specialize (H (t_empty 1)). 
  specialize (H (RError)).
  destruct H.
  + apply E_AssertFalse. 
    simpl. reflexivity.
  + reflexivity.
  + inversion H. apply H1.
Qed. 

(** Then prove that any triple for an [assert] also works when
    [assert] is replaced by [assume]. *)

(* 10 points *)
Theorem assert_implies_assume : forall P b Q,
     ({{P}} assert b {{Q}})
  -> ({{P}} assume b {{Q}}).
Proof.
unfold hoare_triple. 
intros. 
exists st. 
split.
- inversion H0. reflexivity.
- inversion H0. 
  subst.
  specialize (H(st)).
  specialize (H(RNormal st)).
  apply H in H1. destruct H1.
  + inversion H1. 
    inversion H2. 
    apply H4.
  + apply E_AssertTrue. 
    apply H3.
Qed.
    
  

(** Next, here are proofs for the old hoare rules adapted to the new
    semantics.  You don't need to do anything with these. **)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  exists (X !-> aeval st a ; st). split; try reflexivity.
  assumption. Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st r Hc HP.
  unfold hoare_triple in Hhoare.
  assert (exists st', r = RNormal st' /\ Q' st').
  { apply (Hhoare st); assumption. }
  destruct H as [st' [Hr HQ'] ].
  exists st'. split; try assumption.
  apply Himp. assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
  {{Q}} c2 {{R}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c1;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st r H12 Pre.
  inversion H12; subst.
  - eapply H1.
    + apply H6.
    + apply H2 in H3. apply H3 in Pre.
        destruct Pre as [st'0 [Heq HQ] ].
        inversion Heq; subst. assumption.
  - (* Find contradictory assumption *)
     apply H2 in H5. apply H5 in Pre.
     destruct Pre as [st' [C _] ].
     inversion C.
Qed.

Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  eexists. split. reflexivity. assumption.
Qed.

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b}} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *)
    apply (HTrue st st').
      assumption.
      split. assumption. assumption.
  - (* b is false *)
    apply (HFalse st st').
      assumption.
      split. assumption.
      apply bexp_eval_false. assumption. Qed.

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{ P /\ ~b}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember <{while b do c end}> as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *)
    eexists. split. reflexivity. split.
    assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrueNormal *)
    clear IHHe1.
    apply IHHe2. reflexivity.
    clear IHHe2 He2 r.
    unfold hoare_triple in Hhoare.
    apply Hhoare in He1.
    + destruct He1 as [st1 [Heq Hst1] ].
        inversion Heq; subst.
        assumption.
    + split; assumption.
  - (* E_WhileTrueError *)
     exfalso. clear IHHe.
     unfold hoare_triple in Hhoare.
     apply Hhoare in He.
     + destruct He as [st' [C _] ]. inversion C.
     + split; assumption.
Qed.

(** Finally, state Hoare rules for [assert] and [assume] and use them
    to prove a simple program correct.  Name your rules [hoare_assert]
    and [hoare_assume]. *)

(* 10 points *)
Theorem hoare_assert : forall Q (b:bexp),
    {{Q /\ b}} assert b {{Q}}.
Proof.
unfold hoare_triple. 
intros.
inversion H; subst.
- exists st. split.
  + reflexivity.
  + apply H0.
- exists st. split.
  + inversion H0.
    rewrite H3 in H2. 
    discriminate.
  +  apply H0.
Qed.

(* 10 points *)
Theorem hoare_assume : forall (Q: state -> Prop) (b:bexp),
    {{b -> Q}}  assume b {{Q}}.
Proof.
unfold hoare_triple.
intros.
inversion H; subst.
exists st.
split.
-  reflexivity.
- apply H0. apply H2.
Qed.

(* 10 points *)
Example assert_assume_example:
  {{True}}
    assume (X = 1);
    X := X + 1;
    assert (X = 2)
  {{True}}.
Proof.
eapply hoare_seq.
- eapply hoare_seq.
  + eapply hoare_assert.
  + eapply hoare_asgn.
- eapply hoare_consequence_pre.
  + eapply hoare_assume.
  + unfold "->>". 
    intros. split.
    ++ apply H.
    ++ simpl in *. 
       rewrite t_update_eq.
       apply eqb_eq.
       apply eqb_eq in H0. 
       inversion H0. 
       lia.
Qed.



End HoareAssertAssume.

From PLF Require Export Hoare2.

(* ================================================================= *)
(** ** Exercise: Slow Assignment 

    A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea.  Fill in decorations and prove the decorated
    program correct. (The proof should be very simple.) *)

Local Open Scope dcom_scope.

(* 20 points *)
Example slow_assignment_dec (m : nat) : decorated := 
    <{
{{ X = m }}
      Y := 0
                    {{  X=m /\ Y=0  }} ->>
                    {{  X+Y=m  }} ;
      while X <> 0 do
                    {{  X<>0 /\ X+Y=m  }} ->>
                    {{  X-1+Y+1=m  }}
         X := X - 1
                    {{  X+Y+1=m   }} ;
         Y := Y + 1
                    {{  X+Y=m   }}
      end
    {{  X+Y=m /\ ~(X<>0)  }} ->>
    {{ Y = m }}
  }>.

(* 5 points *)
Theorem slow_assignment : forall m,
    outer_triple_valid (slow_assignment_dec m).
Proof.
intros. 
verify.
Qed.

(** 

    Prove formally, using the definition of [hoare_triple], that [Y <= 4]
    is indeed a weakest precondition of [X := Y + 1] with respect to
    postcondition [X <= 5]. *)

(* 15 points *)
Theorem is_wp_example :
  is_wp (Y <= 4) <{X := Y + 1}> (X <= 5).
Proof.
unfold is_wp.
split.
- unfold Aexp_of_aexp.
  unfold Aexp_of_nat.
  eapply hoare_consequence_pre. 
  + apply hoare_asgn.
  + verify_assertion.
- intros.
  unfold "->>". 
  intros s H1.
  unfold Aexp_of_aexp in *. 
  unfold Aexp_of_nat in *.
  simpl in *.
  unfold valid_hoare_triple in H.
  apply H with (st' := X !-> (s Y + 1); s) in H1.
  + rewrite t_update_eq in H1. 
    lia.
  + apply E_Asgn. 
    reflexivity.
Qed. 



(* 10 points *)
Theorem hoare_asgn_weakest : forall Q X a,
    is_wp (Q [X |-> a]) <{ X := a }> Q.
Proof.
intros.
split.
- eapply hoare_asgn.
- intros.
  unfold "->>". 
  intros st. 
  apply H.
  apply E_Asgn.
  reflexivity.
Qed.



