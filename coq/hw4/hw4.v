Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Lia.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
From PLF Require Import Imp.
From PLF Require Import Stlc.
From PLF Require Import Smallstep.
From PLF Require Import Maps.
From PLF Require Import Equiv.
Require Import Coq.Logic.FunctionalExtensionality.

Open Scope string_scope.
Open Scope nat_scope.


(* Review Exercises *)

Module Review.


(* 5 points *)
Lemma aeval_weakening : forall x st a ni,
  var_not_used_in_aexp x a ->
  aeval (x !-> ni ; st) a = aeval st a.
Proof.
  intros.
  induction H. 
  - simpl. reflexivity.
  - simpl. rewrite t_update_neq.
    +  reflexivity.
    +  apply H.
  - simpl. rewrite IHvar_not_used_in_aexp1. rewrite IHvar_not_used_in_aexp2. reflexivity.
  - simpl. rewrite IHvar_not_used_in_aexp1. rewrite IHvar_not_used_in_aexp2. reflexivity.
  - simpl. rewrite IHvar_not_used_in_aexp1. rewrite IHvar_not_used_in_aexp2. reflexivity.
Qed. 


(* 5 points *)
Theorem inequiv_exercise:
  ~ cequiv <{ while true do skip end }> <{ skip }>.
Proof.
unfold not.
intros.
eapply loop_never_stops with empty_st empty_st.
unfold loop.
apply H.
apply E_Skip.
Qed.


(* 5 points *)
Theorem assign_aequiv : forall (X : string) (a : aexp),
  aequiv <{ X }> a ->
  cequiv <{ skip }> <{ X := a }>.
Proof.
unfold aequiv.
intros.
split.
- intros. inversion H0. subst.
  assert (st' = t_update st' X (st' X)).
  + apply functional_extensionality. intros. 
    rewrite t_update_same. reflexivity.
  + rewrite H1 at 2.  (* at 2 means it should replace 2nd occurance of st' with hypothesis*)
    apply E_Asgn.
    rewrite <- H. reflexivity.
- intros. inversion H0. subst.
  assert (st = t_update st X (st X)).
  + apply functional_extensionality. intros.
    rewrite t_update_same. reflexivity.
  + rewrite <- H. simpl. rewrite <- H1. 
    apply E_Skip.
Qed.


(* 5 points *)
Theorem while_true : forall b c,
  bequiv b <{true}>  ->
  cequiv
    <{ while b do c end }>
    <{ while true do skip end }>.
Proof.
unfold cequiv. intros. split.
- intros. exfalso. 
  apply (while_true_nonterm b c st st' H).
  apply H0.
- intros. exfalso.
  apply (while_true_nonterm BTrue CSkip st st').
  + apply refl_bequiv.
  + apply H0.
Qed.

End Review.


Module Types.

(* Source language *)

Inductive val :=
| unit
| bval (b : bool)
| nval (n : nat).

(* States  *)

Definition state := total_map val.

(* Types *)

Inductive ty : Type :=
| Unit : ty
| Bool : ty
| Nat : ty.

Inductive expr : Type :=
| const : val -> expr
| deref : string -> expr
| add : expr -> expr -> expr
| bind : string ->  expr -> expr -> expr
| bind1 : state -> string -> expr -> expr -> expr
| bind2 : state -> expr -> expr
| cnd:  expr -> expr -> expr -> expr.


(* Values *)

Inductive bvalue : expr -> Prop :=
  | bv :  forall b, bvalue (const (bval b)).

Inductive nvalue : expr -> Prop :=
  | nv : forall n, nvalue (const (nval n)).

Inductive uvalue : expr -> Prop :=
| uv : uvalue (const unit).

Definition value (e: expr) :  Prop :=
  bvalue e \/ nvalue e \/ uvalue e.


(* Smallstep semantics *)

Inductive progState : Type :=
  | st : expr -> state -> progState.

Notation "( x , y )" := (st x y).

Reserved Notation "(e,s)'-->' (e',s')" (at level 40).


Inductive step : progState -> progState -> Prop :=
| ST_AddConsts : forall s n1 n2,
    (add (const (nval n1)) (const (nval n2)), s) -->
      (const (nval (n1 + n2)), s)
| ST_AddOp1 : forall s s' e1 e1' e2,
      (e1, s) --> (e1', s') ->
      (add e1 e2, s) --> (add e1' e2, s')
| ST_AddOp2 : forall s s' n1 e2 e2',
      (e2, s) --> (e2', s') ->
      (add (const (nval n1)) e2, s)  --> (add (const (nval n1)) e2', s')
| ST_Deref : forall s id,
    (deref id, s) --> (const (s id), s)
| ST_Bind2End : forall s s'  v,
    (bind2 s (const v), s') --> (const v, s)
| ST_Bind2Eval : forall s s' s'' e e',
    (e,s') --> (e',s'') ->
    (bind2 s e, s') --> (bind2 s e', s'')
| ST_Bind1Body : forall s s' id v e,
    (bind1 s id (const v) e, s') --> (bind2 s e, t_update s' id v)
| ST_Bind1Arg : forall s s' s''  id e1 e1' e2,
    (e1, s')  --> (e1', s'') ->
    (bind1 s id e1 e2, s')  --> (bind1 s id e1' e2, s'')
| ST_Bind : forall s id e1 e2,
    (bind id e1 e2, s) --> (bind1 s id e1 e2, s)
| ST_CndGuardValTrue : forall s tb fb,
    (cnd (const (bval true)) tb fb, s) --> (tb, s)
| ST_CndGuardValFalse : forall s tb fb,
    (cnd (const (bval false)) tb fb, s) --> (fb, s)
| ST_CndGuard : forall s s' g g' tb fb,
    (g, s) --> (g', s') ->
    (cnd g tb fb, s)  --> (cnd g' tb fb, s')
           
where "s '-->' s' " := (step s s').


Inductive eval: state -> expr -> val -> Prop :=
  | E_single : forall e s v s', step (e, s) (const v, s') -> eval s e v
  | E_induct : forall e s e' s' v, step (e, s) (e', s') -> eval s' e' v -> eval s e v.

Definition program := (add (bind "x" (const (nval 2)) (deref "x")) (deref "x")).

Example step_program: eval (_ !-> nval 1) program (nval 3).
Proof.
  unfold program.
  eapply E_induct.  apply ST_AddOp1.  apply ST_Bind.
  eapply E_induct.  apply ST_AddOp1.  apply ST_Bind1Body.
  eapply E_induct.  apply ST_AddOp1.  apply ST_Bind2Eval. apply ST_Deref.
  eapply E_induct.  apply ST_AddOp1.  apply ST_Bind2End.
  eapply E_induct.  apply ST_AddOp2.  apply ST_Deref.
  eapply E_single.  apply ST_AddConsts.
Qed.

(* The language is deterministic *)

(* 10 points *)
Theorem step_deterministic : deterministic step.
Proof.
unfold deterministic. intros.
generalize dependent y2.
induction H; intros.
- inversion H0; subst.
  + reflexivity.
  + inversion H4.
  + inversion H4.
- inversion H0; subst.
  + inversion H.
  + apply IHstep in H5. injection H5. intros. rewrite H1. rewrite H2. reflexivity.
  + inversion H.
- inversion H0; subst.
  + inversion H.
  + inversion H5.
  + apply IHstep in H5. injection H5. intros. rewrite H1. rewrite H2. reflexivity.
- inversion H0; subst. reflexivity.
- inversion H0; subst. reflexivity. inversion H4.
- inversion H0; subst. inversion H. apply IHstep in H5. injection H5. intros. rewrite H1. 
  rewrite H2. reflexivity.
- inversion H0; subst. reflexivity. inversion H6.
- inversion H0; subst. inversion H. apply IHstep in H7. injection H7. intros. rewrite H1. 
  rewrite H2. reflexivity.
- inversion H0; subst. reflexivity.
- inversion H0; subst. reflexivity. inversion H5.
- inversion H0; subst. reflexivity. inversion H5.
- inversion H0; subst. 
  + inversion H.
  + inversion H.
  + apply IHstep in H6. injection H6. intros. rewrite H1. rewrite H2. reflexivity.
Qed.
 

(* Normal Forms *)

Notation step_normal_form := (normal_form step).

Definition stuck (p : progState) : Prop :=
  match p with
  | (st e s) =>  step_normal_form p /\ ~ value e
  end.

#[global]
Hint Unfold stuck : core.


(* 10 points *)
Example some_term_is_stuck :
  exists p, stuck p.
Proof.
unfold stuck. 
exists (add (const (bval true)) (const (bval true)), (fun x => (nval 5)) ). 
split.
- unfold step_normal_form. unfold not. intros. 
  inversion H. inversion H0. inversion H5.
- unfold not. intros. inversion H.
  + inversion H0.
  + inversion H0.
    ++ inversion H1.
    ++ inversion H1.
Qed.


(* 5 points *)
Lemma value_is_nf : forall e s,
  value e -> step_normal_form (st e s).
Proof.
intros. unfold step_normal_form. unfold not. 
inversion H.
- intros. inversion H1. inversion H0. rewrite <- H3 in H2. inversion H2.
- inversion H0.
  + intros. inversion H1. inversion H2. rewrite <- H3 in H4. inversion H4.
  + intros. inversion H1. inversion H2. rewrite <- H3 in H4. inversion H4.
Qed.
  


(* Types *)

Definition typeOf (v : val) :=
  match v with
  | unit => Unit
  | bval _ => Bool
  | nval _ => Nat
  end.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' e '\in' T" (at level 40).

Inductive has_type : context -> expr -> ty -> Prop :=
| T_Const : forall Gamma v T,
    typeOf(v) = T ->
    Gamma |- (const v) \in T
| T_Deref : forall Gamma id T,
    Gamma id = Some T ->
    Gamma |- (deref id) \in T
| T_Add : forall Gamma e1 e2,
    Gamma |- e1 \in Nat ->
    Gamma |- e2 \in Nat ->                  
    Gamma |- (add e1 e2) \in Nat
| T_Bind : forall Gamma  id e1 e2 T1 T2,
    Gamma |- e1 \in T1 ->
    (id |-> T1; Gamma)  |- e2 \in T2 ->
    Gamma |- (bind id e1 e2) \in T2
| T_Bind1 : forall Gamma s id e1 e2 T1 T2,
    Gamma |- e1 \in T1 ->
    (id |-> T1; Gamma) |- e2 \in T2 ->
    Gamma |- (bind1 s id e1 e2) \in T2
| T_Bind2 : forall Gamma s e T,
    Gamma |- e \in T ->
    Gamma |- (bind2 s e) \in T
| T_Cnd : forall Gamma e1 e2 e3 T,
    Gamma |- e1 \in Bool ->
    Gamma |- e2 \in T ->
    Gamma |- e3 \in T ->
    Gamma |- (cnd e1 e2 e3) \in T

where "Gamma '|-' e '\in' T" := (has_type Gamma e T).

#[global]
Hint Constructors has_type : core.

Example has_type_1 :
  empty |- (bind "x" (const (nval O)) (add (deref "x") (const (nval (S O))))) \in Nat.
Proof.
  eapply T_Bind.
  apply T_Const.
  unfold typeOf. reflexivity.
  unfold update. 
  apply T_Add.
  apply T_Deref.
  reflexivity.
  apply T_Const.  
  unfold typeOf.
  reflexivity.
Qed.

(* 5 points *)
Lemma bool_canonical : forall Gamma e ,
  Gamma |- e \in Bool -> value e -> bvalue e.
Proof.
intros.
inversion H0.
- apply H1.
- inversion H1.
  + inversion H2. rewrite <- H3 in H. inversion H. inversion H6.
  + inversion H2. rewrite <- H3 in H. inversion H. inversion H6.
Qed.



(* 5 points *)
Lemma nat_canonical : forall Gamma e ,
  Gamma |- e \in Nat -> value e -> nvalue e.
Proof.
intros. 
inversion H0.
- inversion H1. rewrite <- H2 in H. inversion H. inversion H5.
- inversion H1.
  + apply H2.
  +  inversion H2. rewrite <- H3 in H. inversion H. inversion H6.
Qed.



(* 15 points *)
Theorem unique_types : forall Gamma e T T',
  Gamma |- e \in T ->
  Gamma |- e \in T' ->
  T = T'.
Proof.
(*
intros.
induction H.
- inversion H0. rewrite <- H. rewrite <- H3. reflexivity.
- inversion H0. rewrite -> H in H3. inversion H3. reflexivity.
- inversion H0. reflexivity.
- 
*)
intros.
generalize dependent T'.
induction H.
- intros. inversion H0. rewrite H in H3.  apply H3.
- intros. inversion H0. rewrite H in H3. inversion H3. reflexivity.
- intros. inversion H1. reflexivity.
- intros. inversion H1. subst. assert (T1 = T0) as Heq. {
    intros. apply IHhas_type1. apply H7. } 
  apply IHhas_type2. rewrite Heq. apply H8.
- intros. inversion H1. subst. assert (T1 = T0) as Heq. {
    intros. apply IHhas_type1. apply H8. } 
  intros. apply IHhas_type2. rewrite Heq. apply H9.
- intros. inversion H0. eauto.
- intros. inversion H2. subst. eauto. 
Qed.



(* 30 points *)
Theorem progress : forall e c s T,
    c |- e \in T ->  
    value e \/ exists e' s', (st e s) --> (st e' s').
Proof with eauto.
intros. 
induction H; subst. 
  - destruct v; left; unfold value.
    + right. right. constructor. 
    + left. constructor.
    + right. left. constructor.
  - right. exists (const (s id)), s. apply ST_Deref.
  - destruct IHhas_type1. 
    + right. destruct IHhas_type2. 
      ++ apply nat_canonical with (Gamma:=Gamma) (e:= e1) in H1.
        +++ apply nat_canonical with (Gamma:=Gamma) (e:= e2) in H2. 
          ++++ inversion H1. inversion H2. 
               exists (const (nval (n + n0))). exists s. apply ST_AddConsts.
          ++++ apply H0. 
        +++ apply H.
      ++ apply nat_canonical with (Gamma:=Gamma) (e:= e1) in H1.
        +++ inversion H1. inversion H2. inversion H4. 
            exists (add (const (nval n)) x). exists x0. apply ST_AddOp2. apply H5. 
        +++ apply H.
    + inversion H1. inversion H2. right. 
      exists (add x e2). exists x0. apply ST_AddOp1. apply H3.
  - right. exists (bind1 s id e1 e2). exists s. apply ST_Bind.
  - right. inversion IHhas_type1. 
    + inversion H1; inversion H2. 
      ++ subst. exists (bind2 s0 e2). 
         exists (t_update s id ((bval b))). apply ST_Bind1Body.
      ++ inversion H3. subst. exists (bind2 s0 e2). 
         exists (t_update s id ((nval n))). apply ST_Bind1Body.
      ++ inversion H3. subst. exists (bind2 s0 e2). 
         exists (t_update s id ((unit))). apply ST_Bind1Body.
    + inversion H1. inversion H2. 
      exists (bind1 s0 id x e2). exists x0. apply ST_Bind1Arg. apply H3.
  - right. inversion IHhas_type. 
    + inversion H0; inversion H1. 
      ++ subst. exists (const(bval b)). exists s0. apply ST_Bind2End.
      ++ inversion H2. subst. exists (const(nval n)). exists s0. apply ST_Bind2End.
      ++ inversion H2. subst. exists (const(unit)). exists s0. apply ST_Bind2End.
    + inversion H0. inversion H1. 
      exists (bind2 s0 x). exists x0. apply ST_Bind2Eval. apply H2. 
  - subst. right. inversion IHhas_type1. 
    apply bool_canonical with (Gamma:=Gamma) (e:= e1) in H2. 
    ++ inversion H2. subst. destruct b. 
      +++  exists e2. exists s. apply ST_CndGuardValTrue.
      +++  exists e3. exists s. apply ST_CndGuardValFalse.
    ++ apply H.
    ++ inversion H2. inversion H3. 
       exists (cnd x e2 e3). exists x0. apply ST_CndGuard. apply H4.
  Qed.