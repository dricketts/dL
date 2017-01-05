Require Import Coq.Reals.Rdefinitions.
Require Import Coq.micromega.Psatz.
Require Import Coquelicot.Coquelicot.
Require Import ChargeCore.Tactics.Tactics.
Require Import Records.Records.
Require Import dL.Logics.
Require Import dL.dL.
Require Import dL.RecordsFacts.
Local Transparent ILInsts.ILFun_Ops.

Local Open Scope R.
Local Open Scope string_scope.

(**
 ** Here's a simple example of using dL.
 ** The following system enforces an upper bound
 ** on velocity by controlling acceleration.
 **)
Section VelocityBound.

  (* The upper bound on velocity. This is a symbolic constant. *)
  Variable V : R.
  (* Upper bound on the time between executions of
     the discrete controller. This is also a symbolic constant. *)
  Variable d : R.

  Notation "{@@ x , .. , y @@}" :=
    (Fields (FScons x%field_decl ..
                    (FScons y%field_decl FSnil) .. ))
    : type_scope.

  Definition state :=
    dL.state
      {@@ ("a" %e R)
       ,  ("v" %e R)
       ,  ("t" %e R)
       ,  ("y" %e R)
       @@}.

  Definition state_AbelianGroup_mixin : AbelianGroup.mixin_of state.
    refine (AbelianGroup.Mixin state _ _ _ _ _ _ _).
    reflexivity.
      try reflexivity.

    apply Leaf_unit.
  Defined.
  Canonical Leaf_AbelianGroup := AbelianGroup.Pack _ Leaf_AbelianGroup_mixin (record pm_Leaf).

  Definition Leaf_Ring_mixin : Ring.mixin_of Leaf_AbelianGroup.
    refine (Ring.Mixin _ (fun _ _ => pr_Leaf) pr_Leaf _ _ _ _ _); try reflexivity; apply Leaf_unit.
  Defined.
  Canonical Leaf_Ring :=
    Ring.Pack (record pm_Leaf) (Ring.Class _ _ Leaf_Ring_mixin) (record pm_Leaf).

  Definition state_UniformSpace_mixin : UniformSpace.mixin_of state.
    refine (UniformSpace.Mixin _ (fun _ _ _ => True) _ _ _); intros; exact I.
  Defined.
  Canonical state_UniformSpace :=
    UniformSpace.Pack state state_UniformSpace_mixin state.

  Definition state_ModuleSpace_mixin (K : Ring)
    : ModuleSpace.mixin_of K state_AbelianGroup.
    refine (ModuleSpace.Mixin _ _ (fun _ _ => pr_Leaf) _ _ _ _); try reflexivity; apply Leaf_unit.
Defined.
Definition Leaf_ModuleSpace_class_of (K : Ring) : ModuleSpace.class_of K (record pm_Leaf) :=
  ModuleSpace.Class _ _ Leaf_AbelianGroup_mixin (Leaf_ModuleSpace_mixin _).
Canonical Leaf_ModuleSpace (K : Ring) :=
  ModuleSpace.Pack K (record pm_Leaf) (Leaf_ModuleSpace_class_of _) (record pm_Leaf).

Definition Leaf_NormedModuleAux_class_of (K : AbsRing)
  : NormedModuleAux.class_of K (record pm_Leaf) :=
  NormedModuleAux.Class _ _ (Leaf_ModuleSpace_class_of _) Leaf_UniformSpace_mixin.
Canonical Leaf_NormedModuleAux (K : AbsRing) :=
  NormedModuleAux.Pack K (record pm_Leaf) (Leaf_NormedModuleAux_class_of _) (record pm_Leaf).

  Definition Leaf_NormedModuleAux_class_of (K : AbsRing)
    : NormedModuleAux.class_of K (record pm_Leaf) :=
    NormedModuleAux.Class _ _ (Leaf_ModuleSpace_class_of _) Leaf_UniformSpace_mixin.
  Canonical Leaf_NormedModuleAux (K : AbsRing) :=
    NormedModuleAux.Pack K (record pm_Leaf) (Leaf_NormedModuleAux_class_of _) (record pm_Leaf).

  Definition Leaf_NormedModule_mixin (K : AbsRing)
    : NormedModule.mixin_of K (Leaf_NormedModuleAux _).
    refine (NormedModule.Mixin _ _ (fun _ => R0) R1 _ _ _ _ _).
    { intros. psatzl R. }
    { intros. psatz R. }
    { intros. unfold ball. simpl. exact I. }
    { intros. destruct eps. simpl. psatz R. }
    { intros. symmetry. apply Leaf_unit. }
  Defined.
  Definition Leaf_NormedModule_class_of (K : AbsRing)
    : NormedModule.class_of K (record pm_Leaf) :=
    NormedModule.Class _ _ (Leaf_NormedModuleAux_class_of _) (Leaf_NormedModule_mixin _).
  Canonical Leaf_NormedModule_class_of.
  Canonical Leaf_NormedModule (K : AbsRing) :=
    NormedModule.Pack K (record pm_Leaf) (Leaf_NormedModule_class_of _) (record pm_Leaf).


  (* The safety property, i.e. the velocity is at most the
     upper bound. You have to write [get "v"] to access
     the current value of the velocity variable v. You also
     have to write [pure V] to express a constant. These are
     some of the many examples of how the syntax is very
     verbose in our embedding, but we hope to improve this
     in the future. *)
  Definition safe : StateProp state :=
    get "v" [<=] pure V.

  (* The discrete controller sets the acceleration to some
     value that will be safe until the next execution. It
     also sets the timer to zero. *)
  Definition ctrl : ActionProp state :=
    "a" ::= ***;;
     ? get "v" [+] get "a"[*]pure d [<=] pure V;;
    "t" ::= pure 0.

  (* The physical dynamics of the system. This formulation
     differs slightly from dL in that we explicitly set
     derivatives to zero. You write d["v"] [=] #[get "a"]
     to write that the derivative of the variable v is
     equal to the variable a. This syntax is pretty brutal
     and we would definitely like to improve it. The evolution
     invariant follows the [&] symbol. *)

  Definition plant : FlowProp state :=
    d["v"] [=] #[get "a"] //\\
     d["a"] [=] pure 0.

  (* The next two should actually be about some NormedModule of state *)

  Definition evolveL : FlowProp state :=
    d["t"] [=] pure 1.

  Definition evolveR : StateProp state :=
    get "t" [<=] pure d.

  Definition plant2 : ActionProp state :=
    evolveL & evolveR.

  (* Theorem expressing that the system does enforce
     the upper bound on velocity. The proof is fairly simple
     and can probably be mostly or completely automated, but
     for the moment, we manually apply proof rules. Proof
     rules are applied contextually by [rewrite] or directly
     by [apply]. *)
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