Require Import Coq.Strings.String.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Psatz.
Require Import Coq.Logic.FunctionalExtensionality.
(** Since dL's logic is classical, we include Coq's axiomatization of classical
 ** logic. In practice, we find that constructive encodings are generally
 ** sufficient and classical logic is not necessary with the exception of the
 ** dependence on Coq's real analysis library.
 **)
Require Import Coq.Logic.ClassicalFacts.
Require Import ExtLib.Structures.Applicative.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.ILogicIso.
Require Import ChargeCore.Tactics.Tactics.
Require ChargeCore.Logics.ILInsts.
Require Import dL.Logics.
Transparent ILInsts.ILFun_Ops.

Local Open Scope R.
Local Open Scope string_scope.

(** First, we define some notation to lift standard operators into
 ** the various logics.
 **)
Notation "a [+] b" := (pure Rplus <$> a <$> b) (at level 50, left associativity).
Notation "a [-] b" := (pure Rminus <$> a <$> b) (at level 50, left associativity).
Notation "a [*] b" := (pure Rmult <$> a <$> b) (at level 40, left associativity).
Notation "a [>=] b" := (pure Rge <$> a <$> b) (at level 70, right associativity).
Notation "a [<=] b" := (pure Rle <$> a <$> b) (at level 70, right associativity).
Notation "a [=] b" := (pure (@eq R) <$> a <$> b) (at level 70, right associativity).

(** We use the following to lift variables into
 ** [StateVal]s, which allows us to extract values
 ** from the state.
 **
 ** Writing [get "x"] is the equivalent of writing
 ** x in dL. A proper interface should hide this.
 **)
Definition get (x : var) : StateVal R :=
  mkStateVal (fun st => st x).

(** This begins the core definitions for the dL language.
 **)
Definition state_set (x : var) (e : R) (st : state) : state :=
  fun y => if string_dec y x then e else st y.

(** Assignment *)
Definition assign (x : var) (e : StateVal R) : ActionProp :=
  mkActionVal (fun st st' => st' = state_set x (e st) st).

Notation "x ::= e" := (assign x e) (at level 80, e at level 70).

(** Non-deterministic assignment *)
Definition nondet_assign (x : var) : ActionProp :=
  mkActionVal (fun st st' => exists (v : R), st' = state_set x v st).

Notation "x ::= ***" := (nondet_assign x) (at level 80).

(** Test *)
Definition test (t : StateProp) : ActionProp :=
  mkActionVal (fun st st' => st = st' /\ t st').

Notation "? e" := (test e) (at level 80, e at level 70).

(** Continuous transitions. *)
(** This gives the semantic definition of a continuous evolution
    subject to a flow [dF] and an evolution constraint [I]. *)
Definition evolve (dF : FlowProp) (I : StateProp) : ActionProp :=
  mkActionVal
    (fun st st' =>
       exists (r : R) (F : R -> state)
              (* derivable states that derivatives exists for all variables
                 at all times from 0 to r. *)
              (derivable : forall (x : var) (t : R), derivable_pt (fun t => F t x) t),
         0 <= r /\ F 0 = st /\ F r = st' /\
         forall t, 0 <= t <= r ->
                   dF (F t) (fun x => derive_pt (fun t => F t x) t (derivable x t)) /\
                   I (F t)).

Notation "d & I" := (evolve d I) (at level 80, I at level 79).
Print Grammar constr.
Notation "'d[' x ']'" := (mkFlowVal (fun _ st' => st' x)) (at level 30).
Notation "'#[' e ']'" := (mkFlowVal (fun st _ => e st)) (at level 30).

(** Choice *)
Definition choice (a b : ActionProp) : ActionProp :=
  mkActionVal (fun st st' => a st st' \/ b st st').

Notation "a '+++' b" := (choice a b) (at level 80).

(** Sequencing *)
Definition seq (a b : ActionProp) : ActionProp :=
  mkActionVal (fun st st' => exists st'', a st st'' /\ b st'' st').

Notation "a ;; b" := (seq a b) (at level 90, right associativity).

(** Star *)
Inductive star' (a : ActionProp) (st : state) : state -> Prop :=
| Done : star' a st st
| Continue : forall st' st'', a st st' -> star' a st' st'' -> star' a st st''.
Definition star : ActionProp -> ActionProp :=
  fun a => mkActionVal (star' a).

Notation "a ^*" := (star a) (at level 80).

(** Box *)
Definition box (a : ActionProp) (s : StateProp) : StateProp :=
  mkStateVal (fun st => forall st', a st st' -> s st').

Notation "'[['  a ']]' p" := (box a p) (at level 70, p at next level, a at level 0).

(** Diamond *)
Definition diamond (a : ActionProp) (s : StateProp) : StateProp :=
  mkStateVal (fun st => exists st', a st st' /\ s st').

Notation "'<<'  a '>>' p" := (diamond a p) (at level 70, p at next level, a at level 0).

(** Negation *)
Notation "! p" := (p -->> lfalse) (at level 30, p at level 30).
(** NOTE: In constructive logic (like Coq) negation is defined to be
 ** "implies false".
 **)

(** This ends the core definitions in the logic.
 ** Now we state and prove a range of proof rules.
 ** - The theorems roughly follow the presentation from the
 **   uniform substitution paper; however, they are reusing
 **   Coq's logic to do substitution rather than formalizing
 **   it separately.
 **)

(** This proof shows the connection between diamond and box. *)
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

(** When formalizing "updates" it is convenient to have an operation that means
 ** "update a variable with a value". In essence, this operation characterizes
 ** substitution in a semantic way using Coq's existing notions. Doing this
 ** allows us to avoid defining our own substitution and free-variable
 ** relations, and it allows us to re-use a substantial bit of Coq's theory.
 **)
(*Definition Subst (x : var) (e : StateVal R) T (X : StateVal T) : StateVal T :=
  mkStateVal (fun st => X (state_set x (e st) st)).
Arguments Subst _ _ [_] _. (* The [T] argument in [Subst] is implicit. *)*)
Definition Subst T (x : var) (e : StateVal R) (X : StateVal T) : StateVal T :=
  mkStateVal (fun st => X (state_set x (e st) st)).
Arguments Subst [_] _ _ _. (* The [T] argument in [Subst] is implicit. *)
Notation "p [ x <- e ]" := (Subst x e p) (at level 30).

(** Discrete proof rules *)

Theorem assign_rule :
  forall (x : var) (e : StateVal R) (p : StateProp),
    [[x ::= e]] p -|- p [x <- e].
Proof.
  destruct e. destruct p.
  cbv beta iota delta - [string_dec]. split; intros; eauto.
  subst; auto.
Qed.

Theorem nondet_assign_rule :
  forall (x : var) (P : StateProp),
    [[x ::= ***]]P -|- Forall v : R, P [x <- pure v].
Proof.
  destruct P. cbv beta iota delta - [string_dec].
  split; intros.
  { eapply H. eauto. }
  { destruct H0. subst. eauto. }
Qed.

Theorem test_rule :
  forall (q p : StateProp),
    [[? q]]p -|- q -->> p.
Proof.
  destruct q. destruct p.
  compute. split.
  { intuition. }
  { intros. destruct H0. subst. auto. }
Qed.

Theorem choice_rule :
  forall (a b : ActionProp) (p : StateProp),
    [[a +++ b]]p -|- [[a]]p //\\ [[b]]p.
Proof. compute; firstorder. Qed.

Theorem box_land :
  forall (a : ActionProp) (p q : StateProp),
    [[a]](p //\\ q) -|- [[a]]p //\\ [[a]]q.
Proof. compute; firstorder. Qed.

Theorem seq_rule :
  forall (a b : ActionProp) (p : StateProp),
    [[a ;; b]]p -|- [[a]][[b]]p.
Proof. compute; firstorder. Qed.

Theorem star_1 :
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

Theorem K_rule :
  forall (a : ActionProp) (p q : StateProp),
    [[a]](p -->> q) |-- [[a]]p -->> [[a]]q.
Proof. compute; firstorder. Qed.

Theorem star_I :
  forall (a : ActionProp) (p : StateProp),
    [[a^*]](p -->> [[a]]p) //\\ p |-- [[a^*]]p.
Proof.
  intros. do 2 charge_revert.
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
Proof. destruct p. compute; auto. Qed.

Theorem box_monotone :
  forall (a : ActionProp) (p q : StateProp),
    p |-- q ->
    [[a]]p |-- [[a]]q.
Proof. compute; firstorder. Qed.

(** Continuous proof rules *)

Theorem differential_weakening :
  forall (dF : FlowProp) (P : StateProp),
    |-- [[dF & P]]P.
Proof.
  cbv beta iota delta - [Rle derive_pt derivable_pt].
  intros. destruct H0 as [r [F [pf H0] ] ].
  destruct H0 as [Hr [HF0 [HFr HFt] ] ].
  specialize (HFt r). assert (0 <= r <= r) by psatzl R.
  intuition congruence.
Qed.

Theorem differential_weakening' :
  forall (dF : FlowProp) (P Q : StateProp),
     [[dF & Q]](Q -->> P) -|- [[dF & Q]]P.
Proof.
  split.
  { rewrite K_rule. pose proof (differential_weakening dF Q).
    charge_tauto. }
  { charge_revert. rewrite <- K_rule. apply G_rule. charge_tauto. }
Qed.

Theorem differential_cut :
  forall (dF : FlowProp) (Q C P : StateProp),
    [[dF & Q]]C //\\ [[dF & Q //\\ C]]P |-- [[dF & Q]]P.
Proof.
  destruct dF as [ dF ]. destruct Q as [Q]. destruct C as [C]. destruct P as [P].
  cbv beta iota delta - [Rle derive_pt derivable_pt].
  intros. destruct H as [HC HCP]. apply HCP.
  destruct H0 as [r [F [pf H0] ] ]. exists r. exists F.
  exists pf. repeat (split; [ tauto | ]).
  intros. rewrite <- and_assoc. split.
  { apply H0; auto. }
  { apply HC. exists t0. exists F. exists pf. repeat (split; [ tauto | ]).
    intros. apply H0. psatzl R. }
Qed.

(** [D_state_val e e'] states that [e'] is the derivative of [e]. *)
Definition D_state_val (e : StateVal R) (e' : FlowVal R) : Prop :=
  forall (f : R -> state)
         (derivable_f : forall (x : var), derivable (fun t => f t x)),
    exists derivable_e : derivable (fun t => e (f t)),
      forall (t : R),
        derive_pt (fun t => e (f t)) t (derivable_e t) =
        e' (f t) (fun x => derive_pt (fun t => f t x) t (derivable_f x t)).

(** Differential induction. We just prove one case for now. *)
Theorem differential_induction_leq :
  forall (dF : FlowProp) (I : StateProp)
         (e1 e2 : StateVal R) (e1' e2' : FlowVal R),
    (D_state_val e1 e1') ->
    (D_state_val e2 e2') ->
    dF //\\ #[I] |-- e1' [<=] e2' ->
    I -->> (e1 [<=] e2) |-- [[dF & I]](e1 [<=] e2).
Proof.
  destruct dF as [dF]. destruct I as [I]. destruct e1 as [e1].
  destruct e2 as [e2]. destruct e1' as [e1']. destruct e2' as [e2'].
  unfold D_state_val. simpl. intros.
  destruct H3 as [r [f [pf [Hr [Hf0 [Hfr HdF] ] ] ] ] ].
  specialize (H f (fun x => pf x)). specialize (H0 f (fun x => pf x)).
  destruct H. destruct H0. apply Rminus_le.
  assert (I (f 0)).
  { apply HdF; psatzl R. }
  assert (e2 (f 0) - e1 (f 0) <= e2 (f r) - e1 (f r)).
  { destruct Hr.
    { eapply derive_increasing_interv_var
      with (f:=fun t => e2 (f t) - e1 (f t)) (a:=0) (b:=r);
      try psatzl R. Unshelve. Focus 2. unfold derivable.
      intros. apply derivable_pt_minus; eauto.
      intros. simpl.
      rewrite derive_pt_minus
      with (f1:=fun t => e2 (f t)) (f2:=fun t => e1 (f t)).
      rewrite H. rewrite H0.
      assert (dF (f t0)
                 (fun x1 : var => derive_pt
                                    (fun t1 : R => f t1 x1) t0
                                    (pf x1 t0)) /\ I (f t0)).
      { apply HdF; psatzl R. }
      apply H1 in H6. psatzl R. }
    { subst. psatzl R. } }
  { subst. intuition; psatzl R. }
Qed.

Theorem D_state_val_var :
  forall (x : var),
    D_state_val (get x) (d[x]).
Proof.
  unfold D_state_val, get. simpl. intros.
  exists (derivable_f x). reflexivity.
Qed.

Theorem D_state_val_pure :
  forall (x : R),
    D_state_val (pure x) (pure 0).
Proof.
  unfold D_state_val, pure. simpl. intros.
  exists (derivable_pt_const x).
  intros. rewrite <- (derive_pt_const x t).
  reflexivity.
Qed.

Theorem D_state_val_plus :
  forall (e1 e2 : StateVal R) (e1' e2' : FlowVal R),
    D_state_val e1 e1' ->
    D_state_val e2 e2' ->
    D_state_val (e1 [+] e2) (e1' [+] e2').
Proof.
  unfold D_state_val, get. simpl. intros.
  specialize (H f derivable_f). specialize (H0 f derivable_f).
  destruct H. destruct H0. unfold derivable. eexists.
  intros. rewrite <- H. rewrite <- H0. apply derive_pt_plus.
Qed.

Theorem D_state_val_minus :
  forall (e1 e2 : StateVal R) (e1' e2' : FlowVal R),
    D_state_val e1 e1' ->
    D_state_val e2 e2' ->
    D_state_val (e1 [-] e2) (e1' [-] e2').
Proof.
  unfold D_state_val, get. simpl. intros.
  specialize (H f derivable_f). specialize (H0 f derivable_f).
  destruct H. destruct H0. unfold derivable. eexists.
  intros. rewrite <- H. rewrite <- H0. apply derive_pt_minus.
Qed.

Theorem D_state_val_mult :
  forall (e1 e2 : StateVal R) (e1' e2' : FlowVal R),
    D_state_val e1 e1' ->
    D_state_val e2 e2' ->
    D_state_val (e1 [*] e2) ((e1' [*] #[e2]) [+] (#[e1] [*] e2')).
Proof.
  unfold D_state_val, get. simpl. intros.
  specialize (H f derivable_f). specialize (H0 f derivable_f).
  destruct H. destruct H0. unfold derivable. eexists.
  intros. rewrite <- H. rewrite <- H0.
  apply derive_pt_mult with (f1:=fun t => e1 (f t)) (f2:=fun t => e2 (f t)).
Qed.

(** Some automation using Ltac (Coq's tactic language). *)

(* This tactic breaks the logic abstractions. This should be used
   when the goal has been reduced to a first-order formula over
   real arithmetic. After applying this tactic, the goal should
   be ready for arithmetic solvers. *)
Ltac breakAbstraction :=
  cbv beta iota delta - [Rle Rge].

(** Using Ltac we can build automation to
 ** automatically construct derivatives using these rules.
 **)
Ltac prove_derive :=
  repeat first [ simple eapply D_state_val_var
               | simple eapply D_state_val_plus
               | simple eapply D_state_val_minus
               | simple eapply D_state_val_mult
               | simple eapply D_state_val_pure
               ].

(* This tactic performs differential induction.
   Currently, we only have a lemma for <=, but it will
   be easy to add others.

   All arithmetic goals are passed to a simple foundational
   linear arithmetic solver. In the future, we will link
   in more powerful arithmetic decision procedures. *)
Ltac diff_ind :=
  rewrite <- differential_induction_leq;
  [ try solve [breakAbstraction; intros; psatzl R]
  | try prove_derive | try prove_derive
  | try solve [breakAbstraction; intros; psatzl R] ].

(** Substitution rules *)

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
  destruct e as [e].
  unfold Subst, state_set, get. simpl. intros.
  f_equal. apply functional_extensionality. intros.
  destruct (string_dec x x); tauto.
Qed.

Lemma Subst_not_get :
  forall (x y : var) (e : StateVal R),
    x <> y ->
    (get x)[y <- e] = (get x).
Proof.
  destruct e.
  unfold Subst, state_set, get. simpl. intros.
  f_equal. apply functional_extensionality. intros.
  destruct (string_dec x y); congruence.
Qed.

Lemma Subst_limpl :
  forall (x : var) (e : StateVal R) (p q : StateProp),
    (p -->> q)[x <- e] -|- p[x <- e] -->> q[x <- e].
Proof.
  unfold Subst, state_set. split; simpl; intros; auto.
Qed.

Lemma Subst_land :
  forall (x : var) (e : StateVal R) (p q : StateProp),
    (p //\\ q)[x <- e] -|- p[x <- e] //\\ q[x <- e].
Proof.
  unfold Subst, state_set. split; simpl; intros; auto.
Qed.

Lemma Subst_ltrue :
  forall (x : var) (e : StateVal R),
    ltrue[x <- e] -|- ltrue.
Proof.
  unfold Subst, state_set. split; simpl; intros; auto.
Qed.

Lemma Subst_lfalse :
  forall (x : var) (e : StateVal R),
    lfalse[x <- e] -|- lfalse.
Proof.
  unfold Subst, state_set. split; simpl; intros; auto.
Qed.

(**
 ** We use generalized rewriting to apply proof rules of the form
 ** P |-- Q within formulas. For example, if you have a goal
 ** |-- [[a]](Q //\\ R), you can rewrite the lemma P |-- Q to obtain
 ** a new goal |-- [[a]](P //\\ R). This is closely related to the
 ** contextual proof rules of dL.
 **
 ** The following instance declarations allow us to perform this
 ** rewriting.
 **)
Require Import Coq.Classes.Morphisms.
Instance Proper_box_lequiv :
  Proper (lequiv ==> lequiv ==> lequiv) box.
Proof.
  red. red. red. red. unfold lequiv. simpl. firstorder.
Qed.
Instance Proper_box_lentails :
  Proper (lentails --> lentails ==> lentails) box.
Proof.
  red. red. red. red. red. red. red. red. red. red. red. red.
  red. simpl. intros. apply H0. firstorder.
Qed.
Instance Proper_Subst_lequiv :
  Proper (eq ==> eq ==> lequiv ==> lequiv) (Subst (T:=Prop)).
Proof.
  repeat red. simpl. intros.
  split; intros; apply H1; intuition congruence.
Qed.
Instance Proper_Subst_lentails :
  Proper (eq ==> eq ==> lentails ==> lentails) (Subst (T:=Prop)).
Proof.
  repeat red. simpl. intros.
  apply H1; intuition congruence.
Qed.

(**
 ** Here's a simple example of using dL.
 ** The following system enforces an upper bound
 ** on velocity by controlling acceleration.
 **)
Section VelocityBound.

  (* The upper bound on velocity. *)
  Variable V : R.
  (* Upper bound on the time between executions of
     the discrete controller. *)
  Variable d : R.

  (* The safety property, i.e. the velocity is at most the
     upper bound. *)
  Definition safe : StateProp :=
    get "v" [<=] pure V.

  (* The discrete controller sets the acceleration to some
     value that will be safe until the next execution. It
     also sets the timer to zero. *)
  Definition ctrl : ActionProp :=
    "a" ::= ***;;
     ? get "v" [+] get "a"[*]pure d [<=] pure V;;
    "t" ::= pure 0.

  (* The physical dynamics of the system. This formulation
     differs slightly from dL in that we explicitly set
     derivatives to zero. *)
  Definition plant : ActionProp :=
    d["v"] [=] #[get "a"] //\\
    d["a"] [=] pure 0 //\\
    d["t"] [=] pure 1 & get "t" [<=] pure d.

  (* Theorem expressing that the system does enforce
     the upper bound on velocity. *)
  Theorem bound_correct :
    |-- safe -->> [[(ctrl;; plant)^*]]safe.
  Proof.
    intros. charge_intros. rewrite <- star_I.
    charge_split.
    { charge_clear. apply G_rule. charge_intro.
      unfold ctrl. repeat rewrite seq_rule.
      rewrite nondet_assign_rule. charge_intros.
      rewrite test_rule. rewrite assign_rule.
      rewrite Subst_limpl. charge_intro.
      assert (x <= 0 \/ 0 <= x) by psatzl R.
      destruct H; unfold plant.
      { rewrite <- differential_cut with (C:=get "a" [<=] pure 0).
        repeat rewrite Subst_land. charge_split.
        { diff_ind. }
        { unfold safe. diff_ind. } }
      { rewrite <- differential_cut with (C:=pure 0 [<=] get "a").
        repeat rewrite box_land. repeat rewrite Subst_land. charge_split.
        { diff_ind. }
        { rewrite <- differential_cut
          with (C:=get "v" [+] get "a"[*](pure d [-] get "t")
                       [<=] pure V).
          repeat rewrite Subst_land. charge_split.
          { diff_ind.
            (* This goal requires non-linear arithmetic,
               so we use a foundational non-linear decision
               procedure. In the future, we will call better
               decision procedures such as Z3. *)
            breakAbstraction. intros. psatz R. }
          { rewrite <- differential_weakening'. charge_clear.
            do 2 rewrite <- Subst_ltrue.
            apply Proper_Subst_lentails; [ reflexivity | reflexivity | ].
            apply Proper_Subst_lentails; [ reflexivity | reflexivity | ].
            apply G_rule. breakAbstraction. intros. psatz R. } } } }
    { reflexivity. }
  Qed.

End VelocityBound.