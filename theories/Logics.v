Require Import Coq.Strings.String.
Require Import Coq.Reals.Rdefinitions.

(** This file defines the three logics in dL.
 ** - [StateProp] represents predicates over states
 **   (it is morally equal to dL).
 ** - [ActionProp] represents transitions between
 **   states (morally hybrid programs).
 ** - [FlowProp] represents predicates over variable
 **   values and their derivatives (these are used
 **   to describe continuous transitions in hybrid
 **   programs).
 **
 ** NOTE: The separation of [ActionProp] and [FlowProp]
 ** allows us to avoid the need to talk about derivatives
 ** in hybrid programs (except for during continuous
 ** evolution).
 **)

(** For simplicity we will represents variables as strings *)
Definition var : Type := string.

(** States are functions from variables to real numbers.
 ** By changing these definitions, we can support other
 ** types, e.g. floating point numbers, integers, etc.
 **
 ** There are two reasonable ways to do this:
 ** 1/ Users declare a Coq type specifying the state that
 **    they want, e.g. using a record.
 ** 2/ Use the extensible records library which constructs
 **    canonical extensible records for arbitrary sets of
 **    fields identified by strings.
 **
 ** NOTE: Both of these solutions are much better than the [var -> R]
 ** solution because they allow multiple types and they support
 ** "small states", i.e. states without extraneous variables.
 ** This choice is made strictly for simplicity at this point.
 **)
Definition state : Type := var -> R.

(** [StateVal T] represents a value of type [T] which might
 ** depend on the current state.
 **)
Record StateVal (T : Type) : Type := mkStateVal
{ unStateVal : state -> T }.

(** [StateProp] is the type of predicates over a single state.
 **)
Definition StateProp := StateVal Prop.

(** [ActionVal T] represents a value of type [T] which might
 ** depend on either the pre-state or the post-state. Normally,
 ** this is used for stating predicates between two related states.
 **)
Record ActionVal (T : Type) : Type := mkActionVal
  { unActionVal : state -> state -> T }.
(** [ActionProp] represents a predicate over two states, e.g. a transition
 ** relation.
 **)
Definition ActionProp := ActionVal Prop.

(** Continuous transitions. *)
(** We encode flows using arbitrary predicates [dF] over the values of variables
    and their derivatives. *)
Record FlowVal (T : Type) : Type := mkFlowVal
{ unFlowVal : state -> state -> T }.
Definition FlowProp : Type := FlowVal Prop.

(** The rest of the file defines "natural" structures that these types have.
 ** 
 ** Applictive Functor:
 **   Each XxxVal is an applicative functor which allows us to
 **   lift pure operations, such as addition, to operations over the XxxVal.
 **   For example, there is a canonical way to lift addition to addition over
 **   [StateVal]s.
 **
 **     [x + y] is a [StateVal R] if x and y are both [StateVal R]
 **
 ** Logic
 **   Each XxxProp is a logic (called an ILogic) which provides logical
 **   operators including the following:
 **   - ltrue (True) , lfalse (False)
 **   - a //\\ b (conjunction) , a \\// b (disjunction) , a -->> b (implication)
 **   - Forall x : T , P x (universal quantification over a value of type T)
 **   - Exists x : T , P x (existential quantification over a value of type T)
 **   - P |-- Q (entailment) , P -|- Q (bi-entailment, i.e. P |-- Q and Q |-- P)
 **     Entailment is morally the same as implication but it is a Coq proposition
 **     allowing us to prove it using Coq tools. For example, we can write a
 **     theorem:
 **
 **        Theorem my_lemma : forall P Q : StateProp,
 **           P //\\ Q |-- P.
 **
 **     in this definition, the [forall] is Coq's universal quantifier, and the entailment
 **     is between for the State logic. If we break the abstractions (defined subsequently)
 **     this theorem means exactly:
 **
 **        Theorem my_lemma_no_abs : forall P Q : StateProp,
 **           forall st : state, P st -> Q st.
 **
 **   In addition to the logical operators, logics also provide the core proof rules
 **   (and many derived proof rules and tactics) which allow us to prove the above theorems. 
 **   For example, [my_lemma] can be proved by the [charge_tauto] tactic.
 **
 **        Theorem my_lemma : forall P Q : StateProp,
 **           P //\\ Q |-- P.
 **        Proof.
 **          intros. (* to introduce Coq's foralls *)
 **          charge_tauto. (* prove the entailment *)
 **        Qed.
 **)
Require Import ExtLib.Structures.Applicative.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.ILogicIso.
Require ChargeCore.Logics.ILInsts.
Transparent ILInsts.ILFun_Ops.

(** Notation for applicative functors *)
Notation "x <$> y" := (ap x y) (at level 30).

Arguments mkStateVal [_] _.
Arguments unStateVal [_] _ _.
Coercion unStateVal : StateVal >-> Funclass.

(* StateProp is an ILogic *)
Instance ILogicOps_StateProp : ILogicOps StateProp :=
  ILogicOps_iso (@mkStateVal _) (@unStateVal _).
Instance ILogic_StateProp : ILogic StateProp := _.

(* StateVal forms an applicative functor *)
Instance Applicative_StateVal : Applicative StateVal :=
{ pure := fun _ x => mkStateVal (fun _ => x)
; ap   := fun _ _ f x => mkStateVal (fun st => f st (x st)) }.

Arguments mkActionVal [_] _.
Arguments unActionVal [_] _ _ _.
Coercion unActionVal : ActionVal >-> Funclass.

(** ActionProp is an ILogic. *)
Instance ILogicOps_ActionProp : ILogicOps ActionProp :=
  ILogicOps_iso (@mkActionVal _) (@unActionVal _).
Instance ILogic_ActionProp : ILogic ActionProp := _.

(** ActionVal forms an applicative functor. *)
Instance Applicative_ActionVal : Applicative ActionVal :=
{ pure := fun _ x => mkActionVal (fun _ _ => x)
; ap   := fun _ _ f x => mkActionVal (fun st st' => f st st' (x st st')) }.

Arguments mkFlowVal [_] _.
Arguments unFlowVal [_] _ _ _.
Coercion unFlowVal : FlowVal >-> Funclass.

(** FlowProp forms an ILogic. *)
Instance ILogicOps_FlowProp : ILogicOps FlowProp :=
  ILogicOps_iso (@mkFlowVal _) (@unFlowVal _).
Instance ILogic_FlowProp : ILogic FlowProp := _.

Instance Applicative_FlowVal : Applicative FlowVal :=
{ pure := fun _ x => mkFlowVal (fun _ _ => x)
; ap   := fun _ _ f x => mkFlowVal (fun st st' => f st st' (x st st')) }.
