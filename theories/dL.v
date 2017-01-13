Require Import Coq.Strings.String.
Require Import Coq.Reals.Reals.
Require Import Coquelicot.Coquelicot.
Require Import Coq.micromega.Psatz.
Require Import Coq.Logic.FunctionalExtensionality.
(** Since dL's logic is classical, we include Coq's axiomatization of classical
 ** logic. In practice, we find that constructive encodings are generally
 ** sufficient and classical logic is not necessary with the exception of the
 ** dependence on Coq's real analysis library.
 **)
Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Classes.Morphisms.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Tactics.Tactics.
Require Import Records.Records.
Require Import dL.Logics.
Require Import dL.RecordsFacts.
Local Transparent ILInsts.ILFun_Ops.

Local Open Scope R.
Local Open Scope string_scope.

Set Implicit Arguments.
Set Universe Polymorphism.

(** This file formalizes dL using the logics defined in Logics.v *)

(** First, we define some notation to lift standard operators into
 ** the various logics. These define some operators for building
 ** terms in dL, but anything of type [StateVal T] is a term of
 ** type T.
 **)
Notation "a [+] b" := (pure Rplus <*> a <*> b) (at level 50, left associativity).
Notation "a [-] b" := (pure Rminus <*> a <*> b) (at level 50, left associativity).
Notation "a [*] b" := (pure Rmult <*> a <*> b) (at level 40, left associativity).
Notation "a [>=] b" := (pure Rge <*> a <*> b) (at level 70, right associativity).
Notation "a [<=] b" := (pure Rle <*> a <*> b) (at level 70, right associativity).
Notation "a [=] b" := (pure (@eq R) <*> a <*> b) (at level 70, right associativity).

Section dL.

  Definition var : Type := string.
  Variable vars : fields.
  Definition state : Type := record vars.

  (** We use the following to lift variables into
   ** [StateVal]s, which allows us to extract values
   ** from the state.
   **
   ** Writing [get "x"] is the equivalent of writing
   ** x in dL. A proper interface should hide this.
   **)
  Definition get (x : var) {T : Type} {pf : FieldOf vars x T} : StateVal state T :=
    mkStateVal (fun st => Rget st x pf.(_field_proof)).

  (** This begins the core definitions for hybrid programs.
   **)
  Definition state_set (x : var) {T : Type} (e : T) (st : state)
             {pf : FieldOf vars x T} : state :=
    record_set (get_member _ _ pf.(_field_proof)) e st.

  (** Assignment *)
  Definition assign (x : var) {T : Type} (e : StateVal state T)
             {pf : FieldOf vars x T} : ActionProp state :=
    mkActionVal (fun st st' => st' = state_set (pf:=pf) x (e st) st).

  Notation "x ::= e" := (@assign x _ e _) (at level 80, e at level 70).

  (** Non-deterministic assignment *)
  Definition nondet_assign (x : var) {T : Type}
             {pf : FieldOf vars x T} : ActionProp state :=
    mkActionVal (fun st st' => exists (v : T), st' = state_set (pf:=pf) x v st).

  Notation "x ::= ***" := (@nondet_assign x _ _) (at level 80).

  (** Test *)
  Definition test (t : StateProp state) : ActionProp state :=
    mkActionVal (fun st st' => st = st' /\ t st').

  Notation "? e" := (test e) (at level 80, e at level 70).

  Section Continuous.

    Variable cstate : NormedModule R_AbsRing.

    (** Continuous transitions. *)
    (** This gives the semantic definition of a continuous evolution
     ** subject to a flow [dF] and an evolution constraint [I]. *)
    Definition evolve' (dF : FlowProp cstate) (I : StateProp cstate)
      : ActionProp cstate :=
      mkActionVal
        (fun st st' =>
           exists (r : R) (F : R -> cstate),
             0 <= r /\ F 0 = st /\ F r = st' /\
             (forall t, 0 <= t <= r -> I (F t)) /\
             (exists (D : R -> cstate),
                 (forall t : R, is_derive F t (D t)) /\
                 forall t, 0 <= t <= r ->
                           is_derive F t (D t) /\
                           dF (F t) (D t))).

    Class ProjState :=
      { to_cstate : state -> cstate;
        from_cstate : state -> cstate -> state;
        Hinv : forall st cst, to_cstate (from_cstate st cst) = cst }.
    Context {PInst : ProjState}.

    Definition proj_StateProp (p : StateProp cstate) : StateProp state :=
      mkStateVal
        (fun st => p (to_cstate st)).
    Definition proj_ActionProp (a : ActionProp cstate) : ActionProp state :=
      mkActionVal
        (fun st st' => a (to_cstate st) (to_cstate st') /\
                       st' = from_cstate st (to_cstate st')).

    Definition evolve (dF : FlowProp cstate) (I : StateProp cstate)
      : ActionProp state :=
      proj_ActionProp (evolve' dF I).

  End Continuous.

  Notation "d & I" := (evolve d I) (at level 80, I at level 79).
  Notation "'d[' x ']'" := (mkFlowVal (fun _ st' => get x st')) (at level 30).
  Notation "'#[' e ']'" := (mkFlowVal (fun st _ => e st)) (at level 30).

  (** Choice *)
  Definition choice (a b : ActionProp state) : ActionProp state :=
    mkActionVal (fun st st' => a st st' \/ b st st').

  Notation "a '+++' b" := (choice a b) (at level 80).

  (** Sequencing *)
  Definition seq (a b : ActionProp state) : ActionProp state :=
    mkActionVal (fun st st' => exists st'', a st st'' /\ b st'' st').

  Notation "a ;; b" := (seq a b) (at level 90, right associativity).

  (** Star *)
  Inductive star' (a : ActionProp state) (st : state) : state -> Prop :=
  | Done : star' a st st
  | Continue : forall st' st'', a st st' -> star' a st' st'' -> star' a st st''.
  Definition star : ActionProp state -> ActionProp state :=
    fun a => mkActionVal (star' a).

  Notation "a ^*" := (star a) (at level 80).

  (** This begins the core definitions for dL. Note that logical
   ** connectives such as conjunction are not defined here
   ** because we get them for free from the definitions in
   ** Logics.v
   **)

  (** Box *)
  Definition box (a : ActionProp state) (s : StateProp state) : StateProp state :=
    mkStateVal (fun st => forall st', a st st' -> s st').

  Notation "'[[' a ']]' p" := (box a p) (at level 70, p at next level, a at level 0).

  (** Diamond *)
  Definition diamond (a : ActionProp state) (s : StateProp state) : StateProp state :=
    mkStateVal (fun st => exists st', a st st' /\ s st').

  Notation "'<<' a '>>' p" := (diamond a p) (at level 70, p at next level, a at level 0).
  Notation "! p" := (p -->> lfalse) (at level 30, p at level 30).
  (** NOTE: In constructive logic (like Coq) negation is defined to be
   ** "implies false".
   **)

  (** This ends the core definitions of dL.
   ** Now we state and prove a range of proof rules.
   ** - The theorems roughly follow the presentation from the
   **   uniform substitution paper; however, they are reusing
   **   Coq's logic to do substitution rather than formalizing
   **   it separately.
   **)

  (** This proof shows the connection between diamond and box. *)
  Theorem diamond_box :
    forall (a : ActionProp state) (p : StateProp state),
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
  Definition Subst (T U : Type) (x : var) (e : StateVal state U)
             (X : StateVal state T) (pf : FieldOf vars x U) : StateVal state T :=
    mkStateVal (fun st => X (state_set (pf:=pf) x (e st) st)).
  Arguments Subst [_ _] _ _ _ _. (* The [T] argument in [Subst] is implicit. *)
  Notation "p {{ x <- e }}" := (@Subst _ _ x e p _)
                                 (at level 30).

  (** Discrete proof rules *)
  Theorem assign_rule :
    forall (T : Type) (x : var) (e : StateVal state T) (p : StateProp state)
           (pf : FieldOf vars x T),
      [[x ::= e]] p -|- p {{x <- e}}.
  Proof.
    destruct e. destruct p.
    cbv beta iota delta - [string_dec]. split; intros; eauto.
    subst; auto.
  Qed.

  Theorem nondet_assign_rule
  : forall (T : Type) (x : var) (P : StateProp state)
      (pf : FieldOf vars x T),
      [[x ::= ***]]P -|- Forall v : T, P {{x <- pure v}}.
  Proof.
    destruct P. cbv beta iota delta - [string_dec].
    split; intros.
    { eapply H. eauto. }
    { destruct H0. subst. eauto. }
  Qed.

  Theorem test_rule :
    forall (q p : StateProp state),
      [[? q]]p -|- q -->> p.
  Proof.
    destruct q. destruct p.
    compute. split.
    { intuition. }
    { intros. destruct H0. subst. auto. }
  Qed.

  Theorem choice_rule :
    forall (a b : ActionProp state) (p : StateProp state),
      [[a +++ b]]p -|- [[a]]p //\\ [[b]]p.
  Proof. compute; firstorder. Qed.

  Theorem box_land :
    forall (a : ActionProp state) (p q : StateProp state),
      [[a]](p //\\ q) -|- [[a]]p //\\ [[a]]q.
  Proof. compute; firstorder. Qed.

  Theorem seq_rule :
    forall (a b : ActionProp state) (p : StateProp state),
      [[a ;; b]]p -|- [[a]][[b]]p.
  Proof. compute; firstorder. Qed.

  Theorem star_1 :
    forall (a : ActionProp state) (p : StateProp state),
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
    forall (a : ActionProp state) (p q : StateProp state),
      [[a]](p -->> q) |-- [[a]]p -->> [[a]]q.
  Proof. compute; firstorder. Qed.

  Theorem star_I :
    forall (a : ActionProp state) (p : StateProp state),
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
    forall (P : Prop) (a : ActionProp state),
      (pure P) |-- [[a]](pure P).
  Proof. compute; auto. Qed.

  Theorem G_rule :
    forall (p : StateProp state) (a : ActionProp state),
      |-- p ->
      |-- [[a]]p.
  Proof. destruct p. compute; auto. Qed.

  Theorem box_monotone :
    forall (a : ActionProp state) (p q : StateProp state),
      p |-- q ->
      [[a]]p |-- [[a]]q.
  Proof. compute; firstorder. Qed.

  (** Continuous proof rules *)

  Section ContinuousRules.

    Variable cstate : NormedModule R_AbsRing.
    Context { PInst : @ProjState cstate }.

    Theorem differential_weakening :
      forall (dF : FlowProp cstate) (P : StateProp cstate),
        |-- [[dF & P]] proj_StateProp P.
    Proof.
      destruct P as [P].
      cbv beta iota delta - [Rle is_derive].
      intros. destruct H0 as [ [r [F H0] ] ?].
      destruct H0 as [Hr [HF0 [HFr [HFI ?] ] ] ].
      specialize (HFI r). assert (0 <= r <= r) by psatzl R.
      intuition congruence.
    Qed.

    Theorem differential_weakening' :
      forall (dF : FlowProp cstate) (Q : StateProp cstate) (P : StateProp state),
        [[dF & Q]](proj_StateProp Q -->> P) -|- [[dF & Q]]P.
    Proof.
      split.
      { rewrite K_rule. pose proof (differential_weakening). specialize (H dF Q).
        charge_tauto. }
      { charge_revert. rewrite <- K_rule. apply G_rule. charge_tauto. }
    Qed.

    Theorem differential_cut :
      forall (dF : FlowProp cstate) (P : StateProp state) (Q C : StateProp cstate) ,
            [[dF & Q]] proj_StateProp C //\\ [[dF & Q //\\ C]] P
        |-- [[dF & Q]] P.
    Proof.
      destruct dF as [ dF ]. destruct Q as [Q]. destruct C as [C]. destruct P as [P].
      cbv beta iota delta - [Rle is_derive].
      intros. destruct H as [HC HCP]. apply HCP.
      destruct H0 as [ [r [F [Hr [HF0 [HFr [HFI [D [HFD1 HFD2] ] ] ] ] ] ] ] ? ].
      split.
      { exists r. exists F. repeat (split; [ assumption | ]).
        split.
        { intros. split; auto.
          specialize (HC (from_cstate t (F t0))). simpl in *.
          rewrite <- Hinv with (ProjState:=PInst) (st:=t). apply HC. split.
          { exists t0. exists F. repeat (split; [ tauto | ]).
              split.
              { rewrite <- Hinv with (ProjState:=PInst) at 1. reflexivity. }
              { split.
                { intros; apply HFI; psatzl R. }
                { exists D. intros. split; intros; [ apply HFD1 | apply HFD2 ]. psatzl R. } } }
          { rewrite <- Hinv with (ProjState:=PInst) at 1. reflexivity. } }
        { exists D. intros. split; intros; [ apply HFD1 | apply HFD2 ]. psatzl R. } }
      { assumption. }
    Qed.

    (** [D_state_val e e'] states that [e'] is the derivative of [e]. *)
    Definition D_state_val (e : StateVal cstate R) (e' : FlowVal cstate R) : Prop :=
      forall (F : R -> cstate) (D : R -> cstate) (t : R),
              is_derive F t (D t) ->
              is_derive (fun t => e (F t)) t (e' (F t) (D t)).

    (** Differential induction. We just prove one case for now. *)
    Theorem differential_induction_leq :
      forall (dF : FlowProp cstate) (I : StateProp cstate)
             (e1 e2 : StateVal cstate R) (e1' e2' : FlowVal cstate R),
        (D_state_val e1 e1') ->
        (D_state_val e2 e2') ->
        dF //\\ #[I] |-- e1' [<=] e2' ->
        proj_StateProp I -->> proj_StateProp (e1 [<=] e2) |-- [[dF & I]]proj_StateProp (e1 [<=] e2).
    Proof.
      destruct dF as [dF]. destruct I as [I]. destruct e1 as [e1].
      destruct e2 as [e2]. destruct e1' as [e1']. destruct e2' as [e2'].
      unfold D_state_val. simpl. intros.
      destruct H3 as [ [ r [f [Hr [Hf0 [Hfr [HI [D [HFD1 HFD2] ] ] ] ] ] ] ] ?].
      apply Rminus_le. assert (I (f 0)).
      { apply HI; psatzl R. }
      assert (e2 (f 0) - e1 (f 0) <= e2 (f r) - e1 (f r)).
      { destruct Hr.
        { specialize (H f D). specialize (H0 f D).
          eapply derive_increasing_interv_var
          with (f:=fun t => e2 (f t) - e1 (f t)) (a:=0) (b:=r);
          try psatzl R. intros. assert (0 <= t0 <= r) by psatzl R.
          Unshelve.
          2: (unfold derivable; intros; apply ex_derive_Reals_0;
              eapply ex_derive_minus
              with (f0:=fun t => e2 (f t)) (g:=fun t => e1 (f t));
              eexists; [ apply H0 | apply H ]; apply HFD1).
          rewrite Derive_Reals. rewrite Derive_minus; [ | eexists; eauto | eexists; eauto ].
          assert (is_derive f t0 (D t0)) as Hderivf by (apply HFD1; assumption).
          specialize (H t0 Hderivf). specialize (H0 t0 Hderivf).
          apply is_derive_unique in H. apply is_derive_unique in H0.
          rewrite H. rewrite H0. specialize (H1 (f t0) (D t0)).
          assert (dF (f t0) (D t0) /\ I (f t0)).
          { split; [ apply HFD2 | apply HI ]; psatzl R. }
          intuition psatzl R. }
        { subst r. psatzl R. } }
      { rewrite <- Hfr. rewrite <- Hf0 in *. intuition psatzl R. }
    Qed.

    Theorem D_state_val_pure :
      forall (x : R),
        D_state_val (pure x) (pure 0).
    Proof.
      unfold D_state_val, pure. simpl. intros.
      auto_derive; intuition psatzl R.
    Qed.

    Theorem D_state_val_plus :
      forall (e1 e2 : StateVal cstate R) (e1' e2' : FlowVal cstate R),
        D_state_val e1 e1' ->
        D_state_val e2 e2' ->
        D_state_val (e1 [+] e2) (e1' [+] e2').
    Proof.
      unfold D_state_val, get. simpl. intros.
      specialize (H F D t H1). specialize (H0 F D t H1).
      apply (is_derive_plus _ _ _ _ _ H H0).
    Qed.

    Theorem D_state_val_minus :
      forall (e1 e2 : StateVal cstate R) (e1' e2' : FlowVal cstate R),
        D_state_val e1 e1' ->
        D_state_val e2 e2' ->
        D_state_val (e1 [-] e2) (e1' [-] e2').
    Proof.
      unfold D_state_val, get. simpl. intros.
      specialize (H F D t H1). specialize (H0 F D t H1).
      apply (is_derive_minus _ _ _ _ _ H H0).
    Qed.

    Theorem D_state_val_mult :
      forall (e1 e2 : StateVal cstate R) (e1' e2' : FlowVal cstate R),
        D_state_val e1 e1' ->
        D_state_val e2 e2' ->
        D_state_val (e1 [*] e2) ((e1' [*] #[e2]) [+] (#[e1] [*] e2')).
    Proof.
      unfold D_state_val, get. simpl. intros.
      specialize (H F D t H1). specialize (H0 F D t H1).
      apply (is_derive_mult _ _ _ _ _ H H0).
      compute. intros. apply Rmult_comm.
    Qed.

  End ContinuousRules.

(** Substitution rules *)

Lemma Subst_ap :
  forall T U (a : StateVal state (T -> U)) (b : StateVal state T)
         (x : var) (e : StateVal state R) {FO : FieldOf vars x R},
    (a <*> b){{x <- e}} = (a{{x <- e}}) <*> (b{{x <- e}}).
Proof. reflexivity. Qed.

Lemma Subst_pure :
  forall T (a : T) (x : var) (e : StateVal state R) {FO : FieldOf vars x R},
    (pure a){{x <- e}} = pure a.
Proof. reflexivity. Qed.

Lemma Subst_get :
  forall (x : var) (e : StateVal state R) {FO : FieldOf vars x R},
    (get x){{x <- e}} = e.
Proof.
  destruct e as [e].
  unfold Subst, state_set, get.
  simpl.
  intros.
  f_equal.
  apply functional_extensionality.
  intros.
  destruct FO as [pf].
  simpl.
  apply record_get_record_set_same.
Qed.

Lemma Subst_not_get :
  forall (x y : var) (e : StateVal state R)
    {X : FieldOf vars x R}
    {Y : FieldOf vars y R}
  ,
    x <> y ->
    (get x){{y <- e}} = (get x).
Proof.
  destruct e as [e].
  unfold Subst, state_set, get.
  simpl.
  intros.
  f_equal.
  apply functional_extensionality.
  intros.
  apply record_get_record_set_different.
  apply different_var_different_member.
  intro.
  apply H.
  apply string_to_p_injective.
  assumption.
Qed.

Lemma Subst_limpl :
  forall (x : var) (e : StateVal state R) (p q : StateProp state)
    {X : FieldOf vars x R},
    (p -->> q){{x <- e}} -|- p{{x <- e}} -->> q{{x <- e}}.
Proof.
  unfold Subst, state_set.
  split; simpl; intros; auto.
Qed.

Lemma Subst_land :
  forall (x : var) (e : StateVal state R) (p q : StateProp state)
    {X : FieldOf vars x R},
    (p //\\ q){{x <- e}} -|- p{{x <- e}} //\\ q{{x <- e}}.
Proof.
  unfold Subst, state_set.
  split; simpl; intros; auto.
Qed.

Lemma Subst_ltrue :
  forall (x : var) (e : StateVal state R) {X : FieldOf vars x R},
    ltrue{{x <- e}} -|- ltrue.
Proof.
  unfold Subst, state_set.
  split; simpl; intros; auto.
Qed.

Lemma Subst_lfalse :
  forall (x : var) (e : StateVal state R) {X : FieldOf vars x R},
    lfalse{{x <- e}} -|- lfalse.
Proof.
  unfold Subst, state_set.
  split; simpl; intros; auto.
Qed.

(**
 ** We use generalized rewriting to apply proof rules of the form
 ** P |-- Q within formulas. For example, if you have a goal
 ** |-- [[a]](Q //\\ R), you can rewrite the lemma P |-- Q to obtain
 ** a new goal |-- [[a]](P //\\ R). This is closely related to the
 ** contextual proof rules of dL.
 **
 ** The following instance declarations allow us to perform this
 ** rewriting in particular contexts. Many more are possible, but
 ** this collection of definitions are the only ones necessary to
 ** the example below.
 **)
Global Instance Proper_box_lequiv :
  Proper (lequiv ==> lequiv ==> lequiv) box.
Proof.
  repeat red. unfold lequiv. simpl. firstorder.
Qed.

Global Instance Proper_box_lentails :
  Proper (lentails --> lentails ==> lentails) box.
Proof.
  repeat red. simpl. intros. apply H0. firstorder.
Qed.

Global Instance Proper_Subst_lequiv (X : Type) (x : var) :
  Proper (eq ==> lequiv ==> eq ==> lequiv) (Subst (T:=Prop) (U:=X) x).
Proof.
  repeat red. simpl. intros.
  split; intros; apply H0; intuition congruence.
Qed.

Global Instance Proper_Subst_lentails (X : Type) (x : var) :
  Proper (eq ==> lentails ==> eq ==> lentails) (Subst (T:=Prop) (U:=X) x).
Proof.
  repeat red. simpl. intros.
  apply H0. congruence.
Qed.

End dL.

(* Redefining notations since they did not survive the section. *)

Notation "x ::= e" := (@assign _ x _ e _) (at level 80, e at level 70).
Notation "x ::= ***" := (@nondet_assign _ x _ _) (at level 80).
Notation "? e" := (test e) (at level 80, e at level 70).

Notation "d & I" := (evolve d I) (at level 80, I at level 79).
Notation "'d[' x ']'" := (mkFlowVal (fun _ st' => get x st')) (at level 30).
Notation "'#[' e ']'" := (mkFlowVal (fun st _ => e st)) (at level 30).

Notation "a '+++' b" := (choice a b) (at level 80).
Notation "a ;; b" := (seq a b) (at level 90, right associativity).
Notation "a ^*" := (star a) (at level 80).

Notation "'[[' a ']]' p" := (box a p) (at level 70, p at next level, a at level 0).
Notation "'<<' a '>>' p" := (diamond a p) (at level 70, p at next level, a at level 0).
Notation "! p" := (p -->> lfalse) (at level 30, p at level 30).
(** NOTE: In constructive logic (like Coq) negation is defined to be
 ** "implies false".
 **)

Notation "p {{ x <- e }}" := (@Subst _ _ _ x e p _) (at level 30).

(* Tactics must be defined outside of sections to be globally everywhere *)

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
  repeat first [ (*simple eapply D_state_val_var
               |*) simple eapply D_state_val_plus
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
