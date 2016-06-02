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
Notation "a [*] b" := (pure Rmult <$> a <$> b) (at level 40, left associativity).
Notation "a [>=] b" := (pure Rge <$> a <$> b) (at level 70, right associativity).
Notation "a [<=] b" := (pure Rle <$> a <$> b) (at level 70, right associativity).
Notation "a [=] b" := (pure (@eq R) <$> a <$> b) (at level 70, right associativity).

(** We can also extract values from the state.
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

(** Differential induction. *)
Theorem differential_induction_leq :
  forall (dF : FlowProp) (I : StateProp)
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

(** Using Ltac (Coq's tactic language) we can build automation to
 ** automatically construct derivatives using these rules.
 **)
Ltac prove_derive :=
  repeat first [ simple eapply D_state_val_var
               | simple eapply D_state_val_plus
               | simple eapply D_state_val_mult
               | simple eapply D_state_val_pure
               ].

Ltac differential_induction :=
  etransitivity; [ | eapply differential_induction_leq; [ try prove_derive | try prove_derive | ] ].

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

Definition Subst_ActionVal (x : var) (e : StateVal R) T (X : ActionVal T) : ActionVal T :=
  mkActionVal (fun st st' => X (state_set x (e st) st) st').
Arguments Subst_ActionVal _ _ [_] _. (* The [T] argument in [Subst] is implicit. *)
Notation "p [ x <-- e ]" := (Subst_ActionVal x e p) (at level 30).

(*
Lemma Subst_box :
  forall (a : ActionProp) (P G : StateProp) (x : var) (e : StateVal R),
    G |-- get x [=] e -->> [[a]] P ->
    G[x <- e] |-- ([[a]]P)[x <- e].
Proof.
  destruct a as [a]. destruct P as [P]. destruct e as [e].
  destruct G as [G].
  unfold box, Subst. simpl; intros. eapply H in H0; eauto.
  unfold state_set. dest
  { admit. }
  { 


Lemma Subst_box :
  forall (a : ActionProp) (P : StateProp) (x : var) (e : StateVal R),
    ([[a]]P)[x <- e] -|- [[?(get x) [=] e;; a]] P.
Proof.
  destruct a as [a]. destruct P as [P]. destruct e as [e].
  unfold box, test, seq, Subst. split; simpl; intros.
  { apply H. destruct H0. destruct H0. destruct H0. subst t.
    assert (x0 = state_set x (e x0) x0).
    { apply functional_extensionality; intro. unfold state_set.
      destruct (string_dec x1 x).
      { subst. assumption. }
      { reflexivity. } }
    rewrite <- H0. assumption. }
  { apply H. exists ((state_set x (e t) t)).

*)

Lemma Subst_box :
  forall (a : ActionProp) (P : StateProp) (x : var) (e : StateVal R),
    ([[a]]P)[x <- e] = [[a[x <-- e] ]]P.
Proof. reflexivity. Qed.

Lemma Subst_assign :
  forall (x y : var) (e1 e2 : StateVal R),
    (x ::= e1)[y <-- e2] = (x ::= (e1[y <- e2])).
Proof.
  destruct e1 as [e1]. destruct e2 as [e2].
  unfold Subst, Subst_ActionVal, assign.
  simpl. f_equal. apply functional_extensionality.
  intro. apply functional_extensionality. intro.
  unfold state_set. f_equal. apply functional_extensionality.
  intro. destruct (string_dec x2 x).
  { reflexivity. }
  { destruct (string_dec x2 y).
    {  subst
  


(** Here's a *very* simple example of using dL
 **)
Section Simple.

  Variable V : R.
  Variable d : R.

  Definition safe : StateProp :=
    get "v" [<=] pure V.

  Definition ctrl : ActionProp :=
    "a" ::= ***;;
     ? get "v" [+] get "a"[*]pure d [<=] pure V;;
    "t" ::= pure 0.

  Definition plant : ActionProp :=
    d["v"] [=] #[get "a"] //\\ d["t"] [=] pure 1 & get "t" [<=] pure d.

  Theorem example :
    |-- safe -->> [[(ctrl;; plant)^*]]safe.
  Proof.
    intros. charge_intros. rewrite <- star_I.
    charge_split.
    { charge_clear. apply G_rule. charge_intro.
      unfold ctrl. repeat rewrite seq_rule.
      rewrite nondet_assign_rule. charge_intro.
Check seq_rule.
      rewrite seq_rule.
      { admit. }
      { 
        { reflexivity. }

End Simple.