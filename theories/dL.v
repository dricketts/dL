Require Import Coq.Strings.String.
Require Import Coq.Reals.Reals.
 Require Import FunctionalExtensionality.
Require Import ExtLib.Structures.Applicative.
Require Import ChargeCore.Logics.ILogic.
Require ChargeCore.Logics.ILInsts.
Transparent ILInsts.ILFun_Ops.

Definition var : Type := string.
Definition state : Type := var -> R.

Definition StateVal (T : Type) := state -> T.
Definition StateProp := StateVal Prop.
Instance ILogic_StateProp : ILogic StateProp := _.

Definition ActionVal (T : Type) := state -> state -> T.
Definition ActionProp := ActionVal Prop.
Instance ILogic_ActionProp : ILogic ActionProp := _.

Local Open Scope R.

Definition plus (a b : StateVal R) : StateVal R :=
  fun st => a st + b st.

Definition mult (a b : StateVal R) : StateVal R :=
  fun st => a st * b st.

Notation "x <$> y" := (ap x y) (at level 30).

Instance Applicative_StateVal : Applicative StateVal :=
  { pure := fun _ x _ => x;
    ap   := fun _ _ f x st => f st (x st) }.

Instance Applicative_ActionVal : Applicative ActionVal :=
  { pure := fun _ x _ _ => x;
    ap   := fun _ _ f x st st' => f st st' (x st st') }.

Definition get (x : var) : StateVal R :=
  fun st => st x.

Definition state_set (x : var) (e : R) (st : state) : state :=
  fun y => if string_dec y x then e else st y.

Definition assign (x : var) (e : StateVal R) : ActionProp :=
  fun st st' => st' = state_set x (e st) st.

Notation "x ::= e" := (assign x e) (at level 30).

Definition test (t : StateProp) : ActionProp :=
  fun st st' => st = st' /\ t st'.

Notation "? e" := (test e) (at level 30).

Definition choice (a b : ActionProp) : ActionProp :=
  fun st st' => a st st' \/ b st st'.

Notation "a '+++' b" := (choice a b) (at level 30).
  
Definition seq (a b : ActionProp) : ActionProp :=
  fun st st' => exists st'', a st st'' /\ b st'' st'.

Notation "a ;; b" := (seq a b) (at level 30).

Inductive star' (a : ActionProp) (st : state) : state -> Prop :=
| Done : star' a st st
| Continue : forall st' st'', a st st' -> star' a st' st'' -> star' a st st''.
Definition star : ActionProp -> ActionProp := star'.

Notation "a ^*" := (star a) (at level 30).

Definition geq (a b : StateVal R) : StateProp :=
  pure Rge <$> a <$> b.

Definition box (a : ActionProp) (s : StateProp) : StateProp :=
  fun st => forall st', a st st' -> s st'.

Notation "'[['  a ']]' p" := (box a p) (at level 30, p at next level, a at level 0).

Definition diamond (a : ActionProp) (s : StateProp) : StateProp :=
  fun st => exists st', a st st' /\ s st'.

Notation "'<<'  a '>>' p" := (diamond a p) (at level 30, p at next level, a at level 0).

Notation "! p" := (p -->> lfalse) (at level 30, p at level 30).

Require Import ClassicalFacts.
Theorem diamond_box :
  forall (a : ActionProp) (p : StateProp),
    <<a>> p -|- ![[a]] !p.
Proof.
  compute. intros.
  split; intros.
  { firstorder. }
  { eapply Classical_Prop.NNPP.
    intro. apply H. intros.
    eapply H0. eauto. }
Qed.

Definition Subst (x : var) (e : StateVal R) T (X : StateVal T) : StateVal T :=
  fun st => X (state_set x (e st) st).
Arguments Subst _ _ [_] _ _.
Notation "p [ x <- e ]" := (Subst x e p) (at level 30).

(* Discrete proof rules. *)

Theorem assign_rule :
  forall (x : var) (e : StateVal R) (p : StateProp),
    [[x ::= e]] p -|- p [x <- e].
Proof.
  cbv beta iota delta - [string_dec]. split; intros; eauto.
  subst; auto.
Qed.

Theorem test_rule :
  forall (q p : StateProp),
    [[? q]]p -|- q -->> p.
Proof.
  compute. split.
  { intuition. }
  { intros. destruct H0. subst. auto. }
Qed.

Theorem choice_rule :
  forall (a b : ActionProp) (p : StateProp),
    [[a +++ b]]p -|- [[a]]p //\\ [[b]]p.
Proof. compute; firstorder. Qed.

Theorem seq_rule :
  forall (a b : ActionProp) (p : StateProp),
    [[a ;; b]]p -|- [[a]][[b]]p.
Proof. compute; firstorder. Qed.

Theorem star_K :
  forall (a : ActionProp) (p : StateProp),
    [[a^*]]p -|- p //\\ [[a]][[a^*]]p.
Proof.
  compute. split; intros.
  { split.
    { apply H; constructor. }
    { intros. apply H. econstructor; eauto. } }
  { inversion H0.
    { subst; tauto. }
    { subst st'. destruct H. eapply H3; eauto. } }
Qed.

Theorem star_I :
  forall (a : ActionProp) (p : StateProp),
    |-- [[a^*]](p -->> [[a]]p) -->> (p -->> [[a^*]]p).
Proof.
  compute. intros. induction H2.
  { assumption. }
  { apply IHstar'. 
    { intros. eapply H0; eauto. econstructor; eauto. }
    { eapply H0; eauto. constructor. } }
Qed.

Theorem V_rule :
  forall (P : Prop) (a : ActionProp),
    (pure P) |-- [[a]](pure P).
Proof. compute; auto. Qed.

Theorem G_rule :
  forall (p : StateProp) (a : ActionProp),
    |-- p ->
    |-- [[a]]p.
Proof. compute; auto. Qed.

(* Substitution rules. *)

Lemma Subst_ap :
  forall T U (a : StateVal (T -> U)) (b : StateVal T)
         (x : var) (e : StateVal R),
    (a <$> b)[x <- e] = (a[x <- e]) <$> (b[x <- e]).
Proof. reflexivity. Qed.

Lemma Subst_pure :
  forall T (a : T) (x : var) (e : StateVal R),
    (pure a)[x <- e] = pure a.
Proof. reflexivity. Qed.

Lemma Subst_get :
  forall (x : var) (e : StateVal R),
    (get x)[x <- e] = e.
Proof.
  unfold Subst, state_set, get. simpl. intros.
  apply functional_extensionality. intros.
  destruct (string_dec x x); tauto.
Qed.

Lemma Subst_not_get :
  forall (x y : var) (e : StateVal R),
    x <> y ->
    (get x)[y <- e] = (get x).
Proof.
  unfold Subst, state_set, get. simpl. intros.
  apply functional_extensionality. intros.
  destruct (string_dec x y); congruence.
Qed.
