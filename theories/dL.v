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
Require ChargeCore.Logics.ILInsts.
Transparent ILInsts.ILFun_Ops.

(* TODO: move to Charge Core. *)
Section from_iso.
Context {T U : Type} (f : T -> U) (g : U -> T) (ilo : ILogicOps T).
Local Instance ILogicOps_iso : ILogicOps U :=
{| lentails := fun l r => lentails (g l) (g r)
 ; ltrue := f ltrue
 ; lfalse := f lfalse
 ; land := fun l r => f (land (g l) (g r))
 ; lor := fun l r => f (lor (g l) (g r))
 ; limpl := fun l r => f (limpl (g l) (g r))
 ; lforall := fun T P => f (lforall (fun x => g (P x)))
 ; lexists := fun T P => f (lexists (fun x => g (P x)))
 |}.

Context {il : ILogic T}.
Hypothesis gf : forall x, g (f x) -|- x.
Require Import ChargeCore.Tactics.Tactics.
Instance ILogic_iso : ILogic U.
constructor; simpl; intros; repeat rewrite gf in *.
{ constructor.
  { red; simpl; intros; reflexivity. }
  { red; simpl; intros. etransitivity; eassumption. } }
all: try charge_tauto.
apply lfalseL.
eapply lforallL; eauto.
eapply lforallR; eauto.
eapply lexistsL; eauto.
eapply lexistsR; eauto.
apply lorL; eauto.
Defined.
End from_iso.
Arguments ILogic_iso {_ _} [_ _ _] {_} _.

Hint Extern 10 (@ILogic _ _) => (eapply ILogic_iso ; [ eauto with typeclass_instances | intro; reflexivity ]) : typeclass_instances.

(** Notation for applicative functors *)
Notation "x <$> y" := (ap x y) (at level 30).


(** Represent variables as strings *)
Definition var : Type := string.

(** States are functions from variables to real numbers.
 ** By changing these definitions, we can support other
 ** types, e.g. floating point numbers, integers, etc.
 **
 ** NOTE: There are two reasonable ways to do this:
 ** 1/ Users declare a Coq type specifying the state that
 **    they want, e.g. using a record.
 ** 2/ Use the extensible records library which constructs
 **    canonical extensible records for arbitrary sets of
 **    fields identified by strings.
 **
 ** Both of these solutions are much better than the [var -> R]
 ** solution because they allow multiple types and they support
 ** "small states", i.e. states without extraneous variables.
 **)
Definition state : Type := var -> R.

(** [StateVal T] represents a value of type [T] which might
 ** depend on the current state.
 **)
Record StateVal (T : Type) : Type := mkStateVal
{ unStateVal : state -> T }.
Arguments mkStateVal [_] _.
Arguments unStateVal [_] _ _.
Coercion unStateVal : StateVal >-> Funclass.
(** [StateProp] is the type of predicates over a single state.
 **)
Definition StateProp := StateVal Prop.
(** The following two instances state that
 ** [StateProp] forms an intuitionistic logic. This declaration
 ** provides operations such as:
 ** - ltrue (True), lfalse (False)
 ** - a //\\ b (conjunction), a \\// b (disjunction), a -->> b (implication)
 ** - lforall (fun x => P x) (universal quantification)
 ** - lexists (fun x => P x) (existential quantification)
 **)
Instance ILogicOps_StateProp : ILogicOps StateProp :=
  ILogicOps_iso (@mkStateVal _) (@unStateVal _) _.
Instance ILogic_StateProp : ILogic StateProp := _.

(** StateVal forms an applicative functor, which basically means that
 ** we can lift pure operations to operations over StateVals.
 **)
Instance Applicative_StateVal : Applicative StateVal :=
{ pure := fun _ x => mkStateVal (fun _ => x)
; ap   := fun _ _ f x => mkStateVal (fun st => f st (x st)) }.

(** For example, we can lift addition and multiplication using the following
 ** definitions.
 **)
Notation "a [+] b" := (pure Rplus <$> a <$> b) (at level 30).
Notation "a [*] b" := (pure Rmult <$> a <$> b) (at level 30).
Notation "a [>=] b" := (pure Rge <$> a <$> b) (at level 30).
Notation "a [<=] b" := (pure Rle <$> a <$> b) (at level 30).

(** In addition to combining values, we can also extract values from the state.
 **)

Definition get (x : var) : StateVal R :=
  mkStateVal (fun st => st x).

(** [ActionVal T] represents a value of type [T] which might
 ** depend on either the pre-state or the post-state. Normally,
 ** this is used for stating predicates between two related states.
 **)
Record ActionVal (T : Type) : Type := mkActionVal
  { unActionVal : state -> state -> T }.
Arguments mkActionVal [_] _.
Arguments unActionVal [_] _ _ _.
Coercion unActionVal : ActionVal >-> Funclass.
(** [ActionProp] represents a predicate over two states, e.g. a transition
 ** relation.
 **)
Definition ActionProp := ActionVal Prop.
(** We derive a logic in the same way as above. *)
Instance ILogicOps_ActionProp : ILogicOps ActionProp :=
  ILogicOps_iso (@mkActionVal _) (@unActionVal _) _.
Instance ILogic_ActionProp : ILogic ActionProp := _.

Instance Applicative_ActionVal : Applicative ActionVal :=
{ pure := fun _ x => mkActionVal (fun _ _ => x)
; ap   := fun _ _ f x => mkActionVal (fun st st' => f st st' (x st st')) }.

Local Open Scope R.

(** This begins the core definitions for the dL language.
 **)

Definition state_set (x : var) (e : R) (st : state) : state :=
  fun y => if string_dec y x then e else st y.

(** Assignment *)
Definition assign (x : var) (e : StateVal R) : ActionProp :=
  mkActionVal (fun st st' => st' = state_set x (e st) st).

Notation "x ::= e" := (assign x e) (at level 80).

(** Test *)
Definition test (t : StateProp) : ActionProp :=
  mkActionVal (fun st st' => st = st' /\ t st').

Notation "? e" := (test e) (at level 80).

(** Continuous transitions. *)
(** We encode flows using arbitrary predicates [dF] over the values of variables
    and their derivatives. *)
Record FlowVal (T : Type) : Type := mkFlowVal
{ unFlowVal : state -> state -> T }.
Arguments mkFlowVal [_] _.
Arguments unFlowVal [_] _ _ _.
Coercion unFlowVal : FlowVal >-> Funclass.
Definition Flow : Type := FlowVal Prop.
(** Flows also form a logic, which allows us to, e.g. conjoint them. *)
Instance ILogicOps_Flow : ILogicOps Flow :=
  ILogicOps_iso (@mkFlowVal _) (@unFlowVal _) _.
Instance ILogic_Flow : ILogic Flow := _.

Instance Applicative_FlowVal : Applicative FlowVal :=
{ pure := fun _ x => mkFlowVal (fun _ _ => x)
; ap   := fun _ _ f x => mkFlowVal (fun st st' => f st st' (x st st')) }.

(** This gives the semantic definition of a continuous evolution
    subject to a flow. *)
Definition evolve (dF : Flow) (I : StateProp) : ActionProp :=
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

Notation "d & I" := (evolve d I) (at level 80).

Notation "'d[' x ']'" := (mkFlowVal (fun _ st' => st' x)) (at level 30).
Notation "'#[' e ']'" := (mkFlowVal (fun st _ => e st)) (at level 30).

(** Choice *)
Definition choice (a b : ActionProp) : ActionProp :=
  mkActionVal (fun st st' => a st st' \/ b st st').

Notation "a '+++' b" := (choice a b) (at level 80).

(** Sequencing *)
Definition seq (a b : ActionProp) : ActionProp :=
  mkActionVal (fun st st' => exists st'', a st st'' /\ b st'' st').

Notation "a ;; b" := (seq a b) (at level 80).

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
Definition Subst (x : var) (e : StateVal R) T (X : StateVal T) : StateVal T :=
  mkStateVal (fun st => X (state_set x (e st) st)).
Arguments Subst _ _ [_] _. (* The [T] argument in [Subst] is implicit. *)
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
Proof. destruct p. compute; auto. Qed.

(** Continuous proof rules *)

Theorem differential_weakening :
  forall (dF : Flow) (P : StateProp),
    |-- [[dF & P]]P.
Proof.
  cbv beta iota delta - [Rle derive_pt derivable_pt].
  intros. destruct H0 as [r [F [pf H0] ] ].
  destruct H0 as [Hr [HF0 [HFr HFt] ] ].
  specialize (HFt r). assert (0 <= r <= r) by psatzl R.
  intuition congruence.
Qed.

Theorem differential_cut :
  forall (dF : Flow) (Q C P : StateProp),
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

Definition D_state_val (e : StateVal R) (e' : FlowVal R) : Prop :=
  forall (f : R -> state)
         (derivable_f : forall (x : var), derivable (fun t => f t x)),
    exists derivable_e : derivable (fun t => e (f t)),
      forall (t : R),
        derive_pt (fun t => e (f t)) t (derivable_e t) =
        e' (f t) (fun x => derive_pt (fun t => f t x) t (derivable_f x t)).

(** Differential induction. *)
Theorem differential_induction_leq :
  forall (dF : Flow) (I : StateProp)
         (e1 e2 : StateVal R) (e1' e2' : FlowVal R),
    (D_state_val e1 e1') ->
    (D_state_val e2 e2') ->
    dF |-- e1' [<=] e2' ->
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
      assert (dF (f t0) (fun x1 : var => derive_pt (fun t1 : R => f t1 x1) t0 (pf x1 t0))).
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
