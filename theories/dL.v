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
Definition StateVal (T : Type) := state -> T.
(** [StateProp] is the type of predicates over a single state.
 **)
Definition StateProp := StateVal Prop.
(** [StateProp] forms an intuitionistic logic. This declaration
 ** provides operations such as:
 ** - ltrue (True), lfalse (False)
 ** - a //\\ b (conjunction), a \\// b (disjunction), a -->> b (implication)
 ** - lforall (fun x => P x) (universal quantification)
 ** - lexists (fun x => P x) (existential quantification)
 **)
Instance ILogic_StateProp : ILogic StateProp := _.

(** StateVal forms an applicative functor, which basically means that
 ** we can lift pure operations to operations over StateVals.
 **)
Instance Applicative_StateVal : Applicative StateVal :=
{ pure := fun _ x _ => x
; ap   := fun _ _ f x st => f st (x st) }.

(** For example, we can lift addition and multiplication using the following
 ** definitions.
 **)
Definition plus (a b : StateVal R) : StateVal R :=
  pure Rplus <$> a <$> b.

Notation "a [+] b" := (plus a b) (at level 30).

Definition mult (a b : StateVal R) : StateVal R :=
  pure Rmult <$> a <$> b.

Definition geq (a b : StateVal R) : StateProp :=
  pure Rge <$> a <$> b.

Definition leq (a b : StateVal R) : StateProp :=
  pure Rge <$> a <$> b.

Notation "a [<=] b" := (leq a b) (at level 30).

(** In addition to combining values, we can also extract values from the state.
 **)
Definition get (x : var) : StateVal R :=
  fun st => st x.


(** [ActionVal T] represents a value of type [T] which might
 ** depend on either the pre-state or the post-state. Normally,
 ** this is used for stating predicates between two related states.
 **)
Definition ActionVal (T : Type) := state -> state -> T.
(** [ActionProp] represents a predicate over two states, e.g. a transition
 ** relation.
 **)
Definition ActionProp := ActionVal Prop.
(** We derive a logic in the same way as above. *)
Instance ILogic_ActionProp : ILogic ActionProp := _.

Instance Applicative_ActionVal : Applicative ActionVal :=
{ pure := fun _ x _ _ => x
; ap   := fun _ _ f x st st' => f st st' (x st st') }.


Local Open Scope R.

(** This begins the core definitions for the dL language.
 **)

Definition state_set (x : var) (e : R) (st : state) : state :=
  fun y => if string_dec y x then e else st y.

(** Assignment *)
Definition assign (x : var) (e : StateVal R) : ActionProp :=
  fun st st' => st' = state_set x (e st) st.

Notation "x ::= e" := (assign x e) (at level 30).

(** Test *)
Definition test (t : StateProp) : ActionProp :=
  fun st st' => st = st' /\ t st'.

Notation "? e" := (test e) (at level 30).

(** Continuous transitions. *)
(** We encode flows using arbitrary predicates [dF] over the values of variables
    and their derivatives. *)
Definition Flow : Type := state -> state -> Prop.
(** Flows also form a logic, which allows us to, e.g. conjoint them. *)
Instance ILogic_Flow : ILogic Flow := _.

(** This gives the semantic definition of a continuous evolution
    subject to a flow. *)
Definition evolve (dF : Flow) : ActionProp :=
  fun st st' =>
    exists (r : R) (F : R -> state)
           (* derivable states that derivatives exists for all variables
              at all times from 0 to r. *)
           (derivable : forall (x : var) (t : R), derivable_pt (fun t => F t x) t),
      0 <= r /\ F 0 = st /\ F r = st' /\
      forall t, 0 <= t <= r ->
                dF (F t) (fun x => derive_pt (fun t => F t x) t (derivable x t)).

(** Choice *)
Definition choice (a b : ActionProp) : ActionProp :=
  fun st st' => a st st' \/ b st st'.

Notation "a '+++' b" := (choice a b) (at level 30).

(** Sequencing *)
Definition seq (a b : ActionProp) : ActionProp :=
  fun st st' => exists st'', a st st'' /\ b st'' st'.

Notation "a ;; b" := (seq a b) (at level 30).

(** Star *)
Inductive star' (a : ActionProp) (st : state) : state -> Prop :=
| Done : star' a st st
| Continue : forall st' st'', a st st' -> star' a st' st'' -> star' a st st''.
Definition star : ActionProp -> ActionProp := star'.

Notation "a ^*" := (star a) (at level 30).

(** Box *)
Definition box (a : ActionProp) (s : StateProp) : StateProp :=
  fun st => forall st', a st st' -> s st'.

Notation "'[['  a ']]' p" := (box a p) (at level 30, p at next level, a at level 0).

(** Diamond *)
Definition diamond (a : ActionProp) (s : StateProp) : StateProp :=
  fun st => exists st', a st st' /\ s st'.

Notation "'<<'  a '>>' p" := (diamond a p) (at level 30, p at next level, a at level 0).

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
  fun st => X (state_set x (e st) st).
Arguments Subst _ _ [_] _ _. (* The [T] argument in [Subst] is implicit. *)
Notation "p [ x <- e ]" := (Subst x e p) (at level 30).

(** Discrete proof rules *)

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

(** Continuous proof rules *)

Theorem differential_weakening :
  forall (dF : Flow) (P : StateProp),
    |-- [[evolve (dF //\\ (fun st _ => P st))]]P.
Proof.
  cbv beta iota delta - [Rle derive_pt derivable_pt].
  intros. destruct H0 as [r [F [pf H0] ] ].
  destruct H0 as [Hr [HF0 [HFr HFt] ] ].
  specialize (HFt r). assert (0 <= r <= r) by psatzl R.
  intuition congruence.
Qed.

Theorem differential_cut :
  forall (dF : Flow) (R P : StateProp),
    [[evolve dF]]R //\\ [[evolve (dF //\\ (fun st _ => R st))]]P |-- [[evolve dF]]P.
Proof.
  cbv beta iota delta - [Rle derive_pt derivable_pt].
  intros. destruct H as [HR HRP]. apply HRP.
  destruct H0 as [r [F [pf H0] ] ]. exists r. exists F.
  exists pf. repeat split; try tauto.
  { intuition. }
  { apply HR. exists t0. exists F. exists pf. repeat split; try tauto.
    intros. apply H0. split; try tauto. destruct H. eapply Rle_trans; eauto.
    tauto. }
Qed.

(** Need to figure out how to phrase differential induction. *)
(*
Theorem differential_induction_leq :
  forall (dF : Flow) (e1 e2 : StateVal R),
        Forall st' : state, (fun st => dF st st') -->> (e1 [<=] e2) //\\
        
    |-- [[evolve dF]](e1 [<=] e2).
*)

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
