Set Universe Polymorphism.

Require Import Coq.Reals.Reals.
Require Import Coquelicot.Coquelicot.
Require Import Coq.micromega.Psatz.
Require Import Equality.
Require Import Records.Records.

Section Leaf.

  Local Notation T := (record pm_Leaf) (only parsing).

  Lemma Leaf_unit : forall x : T, pr_Leaf = x.
  Proof.
    dependent destruction x. reflexivity.
  Qed.

  Definition Leaf_plus : T -> T -> T.
    intros _ _. exact pr_Leaf.
  Defined.

  Definition Leaf_opp : T -> T.
    intros _. exact pr_Leaf.
  Defined.

  Definition Leaf_zero : T.
    exact pr_Leaf.
  Defined.

  Definition Leaf_AbelianGroup_mixin : AbelianGroup.mixin_of T.
    apply AbelianGroup.Mixin with
      (plus := Leaf_plus)
      (opp := Leaf_opp)
      (zero := Leaf_zero).
    { reflexivity. }
    { reflexivity. }
    { apply Leaf_unit. }
    { reflexivity. }
  Defined.
  Canonical Leaf_AbelianGroup :=
    AbelianGroup.Pack _ Leaf_AbelianGroup_mixin T.

  Definition Leaf_mult : T -> T -> T.
    intros _ _. exact pr_Leaf.
  Defined.

  Definition Leaf_one : T.
    exact pr_Leaf.
  Defined.

  (*
  Definition Leaf_Ring_mixin : Ring.mixin_of Leaf_AbelianGroup.
    apply Ring.Mixin with
      (mult := Leaf_mult)
      (one  := Leaf_one).
    { reflexivity. }
    { apply Leaf_unit. }
    { apply Leaf_unit. }
    { reflexivity. }
    { reflexivity. }
  Defined.
  Canonical Leaf_Ring :=
    Ring.Pack T (Ring.Class _ _ Leaf_Ring_mixin) T.
   *)

  Definition Leaf_ball : T -> R -> T -> Prop.
    intros _ _ _. exact True.
  Defined.

  Definition Leaf_UniformSpace_mixin : UniformSpace.mixin_of T.
    apply UniformSpace.Mixin with
      (ball := Leaf_ball).
    { intros. exact I. }
    { intros. exact I. }
    { intros. exact I. }
  Defined.
  Canonical Leaf_UniformSpace :=
    UniformSpace.Pack T Leaf_UniformSpace_mixin T.

  Section Leaf_Ring.

    Variable K : Ring.

    Definition Leaf_scal : K -> T -> T.
      intros _ _. exact pr_Leaf.
    Defined.

    Definition Leaf_ModuleSpace_mixin
      : ModuleSpace.mixin_of K Leaf_AbelianGroup.
      apply ModuleSpace.Mixin with
      (scal := Leaf_scal).
      { reflexivity. }
      { apply Leaf_unit. }
      { reflexivity. }
      { reflexivity. }
    Defined.
    Definition Leaf_ModuleSpace_class_of : ModuleSpace.class_of K T :=
      ModuleSpace.Class _ _ Leaf_AbelianGroup_mixin Leaf_ModuleSpace_mixin.
    Canonical Leaf_ModuleSpace :=
      ModuleSpace.Pack
        K T Leaf_ModuleSpace_class_of T.

  End Leaf_Ring.

  Section Leaf_AbsRing.

    Variable K : AbsRing.

    Definition Leaf_NormedModuleAux_class_of : NormedModuleAux.class_of K T :=
      NormedModuleAux.Class
        _ _ (Leaf_ModuleSpace_class_of _) Leaf_UniformSpace_mixin.
    Canonical Leaf_NormedModuleAux :=
      NormedModuleAux.Pack
        K T Leaf_NormedModuleAux_class_of T.

    Definition Leaf_norm : Leaf_NormedModuleAux -> R.
      intros _. exact R0.
    Defined.

    Definition Leaf_norm_factor : R.
      exact R1.
    Defined.

    Definition Leaf_NormedModule_mixin
      : NormedModule.mixin_of K Leaf_NormedModuleAux.
      apply NormedModule.Mixin with
        (norm        := Leaf_norm)
        (norm_factor := Leaf_norm_factor).
      { intros. unfold Leaf_norm. psatzl R. }
      { intros. unfold Leaf_norm. psatz R. }
      { intros. exact I. }
      {
        intros.
        destruct eps.
        unfold Leaf_norm, Leaf_norm_factor.
        simpl.
        psatz R.
      }
      { intros. symmetry. apply Leaf_unit. }
    Defined.
    Definition Leaf_NormedModule_class_of : NormedModule.class_of K T :=
      NormedModule.Class
        _ _ Leaf_NormedModuleAux_class_of Leaf_NormedModule_mixin.
    Canonical Leaf_NormedModule_class_of.
    Canonical Leaf_NormedModule :=
      NormedModule.Pack
        K T Leaf_NormedModule_class_of T.

  End Leaf_AbsRing.

End Leaf.

Section Branch_None_NormedModule.

  Variable AR : AbsRing.

  Variable l r : fields.

  Hypothesis L_NormedModule_class_of : NormedModule.class_of AR (record l).
  Hypothesis R_NormedModule_class_of : NormedModule.class_of AR (record r).

  Local Notation T := (record (pm_Branch l None r)) (only parsing).

  Definition Branch_None_plus : T -> T -> T.
    intros a b.
    dependent destruction a; dependent destruction b.
    constructor.
    { exact (AbelianGroup.plus _ L_NormedModule_class_of a1 b1). }
    { exact tt. }
    { exact (AbelianGroup.plus _ R_NormedModule_class_of a2 b2). }
  Defined.

  Lemma simplify_plus_Branch_None:
    forall (l1 l2 : record l) (v1 v2 : unit) (r1 r2 : record r),
      Branch_None_plus
        (pr_Branch None l1 v1 r1)
        (pr_Branch None l2 v2 r2) =
      pr_Branch
        None
        (AbelianGroup.plus _ L_NormedModule_class_of l1 l2)
        tt
        (AbelianGroup.plus _ R_NormedModule_class_of r1 r2).
  Proof.
    reflexivity.
  Qed.

  Definition Branch_None_opp : T -> T.
    intros x.
    dependent destruction x.
    constructor.
    { exact (AbelianGroup.opp _ L_NormedModule_class_of x1). }
    { exact tt. }
    { exact (AbelianGroup.opp _ R_NormedModule_class_of x2). }
  Defined.

  Lemma simplify_opp_Branch_None :
    forall a b v,
      Branch_None_opp (pr_Branch None a v b)
      = pr_Branch
          None
          (AbelianGroup.opp _ L_NormedModule_class_of a)
          tt
          (AbelianGroup.opp _ R_NormedModule_class_of b).
  Proof.
    destruct v.
    reflexivity.
  Qed.

  Definition Branch_None_zero : T.
    constructor.
    { exact (AbelianGroup.zero _ L_NormedModule_class_of). }
    { exact tt. }
    { exact (AbelianGroup.zero _ R_NormedModule_class_of). }
  Defined.

  Lemma simplify_zero_Branch_None :
    Branch_None_zero =
    pr_Branch
      None
      (AbelianGroup.zero _ L_NormedModule_class_of)
      tt
      (AbelianGroup.zero _ R_NormedModule_class_of).
  Proof. reflexivity. Qed.

  Definition Branch_None_AbelianGroup_mixin : AbelianGroup.mixin_of T.
    apply AbelianGroup.Mixin with
      (plus := Branch_None_plus)
      (opp  := Branch_None_opp)
      (zero := Branch_None_zero).
    {
      intros a b.
      dependent destruction a; dependent destruction b.
      do 2 rewrite simplify_plus_Branch_None.
      f_equal; apply AbelianGroup.ax1.
    }
    {
      intros a b c.
      dependent destruction a; dependent destruction b; dependent destruction c.
      do 4 rewrite simplify_plus_Branch_None.
      f_equal; apply AbelianGroup.ax2.
    }
    {
      intro x.
      dependent destruction x.
      rewrite simplify_zero_Branch_None.
      rewrite simplify_plus_Branch_None.
      f_equal.
      { apply AbelianGroup.ax3. }
      { now destruct y. }
      { apply AbelianGroup.ax3. }
    }
    {
      intro x.
      dependent destruction x.
      rewrite simplify_opp_Branch_None.
      rewrite simplify_plus_Branch_None.
      rewrite simplify_zero_Branch_None.
      f_equal.
      { apply AbelianGroup.ax4. }
      { apply AbelianGroup.ax4. }
    }
  Defined.
  Canonical Branch_None_AbelianGroup :=
    AbelianGroup.Pack _ Branch_None_AbelianGroup_mixin T.

  Definition Branch_None_ball : T -> R -> T -> Prop.
    intros a eps b.
    dependent destruction a; dependent destruction b.
    pose proof (UniformSpace.ball _ L_NormedModule_class_of a1 eps b1) as P1.
    pose proof (UniformSpace.ball _ R_NormedModule_class_of a2 eps b2) as P2.
    exact (P1 /\ P2).
  Defined.

  Lemma simplify_ball_Branch_None:
    forall (l1 l2 : record l) (v1 v2 : unit) (r1 r2 : record r) eps,
      Branch_None_ball
        (pr_Branch None l1 v1 r1)
        eps
        (pr_Branch None l2 v2 r2)
      =
      (
        UniformSpace.ball _ L_NormedModule_class_of l1 eps l2
        /\
        UniformSpace.ball _ R_NormedModule_class_of r1 eps r2
      ).
  Proof.
    reflexivity.
  Qed.

  Definition Branch_None_UniformSpace_mixin : UniformSpace.mixin_of T.
    apply UniformSpace.Mixin with
      (ball := Branch_None_ball).
    {
      intros x eps.
      dependent destruction x.
      rewrite simplify_ball_Branch_None.
      split.
      { apply UniformSpace.ax1. }
      { apply UniformSpace.ax1. }
    }
    {
      intros a b eps.
      dependent destruction a; dependent destruction b.
      do 2 rewrite simplify_ball_Branch_None.
      TODO.
      split.
      { apply UniformSpace.ax1. }
      { apply UniformSpace.ax1. }
    }

      unfold Branch_None_ball.

    }
    { intros. exact I. }
    { intros. exact I. }
  Defined.
  Canonical Branch_None_UniformSpace :=
    UniformSpace.Pack T Branch_None_UniformSpace_mixin T.

  Definition Branch_None_scal : AR -> T -> T.
    intros k b.
    dependent destruction b.
    apply pr_Branch.
    {
      apply (ModuleSpace.scal _ _ L_NormedModule_class_of k).
      auto.
    }
    { exact tt. }
    {
      apply (ModuleSpace.scal _ _ R_NormedModule_class_of k).
      auto.
    }
  Defined.

  Lemma simplify_scal_Branch_None:
    forall (k : AR) (l1 : record l) (v : unit) (r1 : record r),
      Branch_None_scal k (pr_Branch None l1 v r1)
      = pr_Branch
          None
          (ModuleSpace.scal _ _ L_NormedModule_class_of k l1 : record l)
          tt
          (ModuleSpace.scal _ _ R_NormedModule_class_of k r1 : record r).
  Proof.
    reflexivity.
  Qed.

  Definition Branch_None_ModuleSpace_mixin
    : ModuleSpace.mixin_of AR Branch_None_AbelianGroup.
    unfold Branch_None_AbelianGroup.
    apply ModuleSpace.Mixin with
    (scal := Branch_None_scal).
    {
      intros x y u.
      simpl in u.
      dependent destruction u.
      do 3 rewrite simplify_scal_Branch_None.
      f_equal.
      { apply ModuleSpace.ax1. }
      { apply ModuleSpace.ax1. }
    }
    {
      intros u.
      simpl in u.
      dependent destruction u.
      rewrite simplify_scal_Branch_None.
      f_equal.
      { apply ModuleSpace.ax2. }
      { now destruct y. }
      { apply ModuleSpace.ax2. }
    }
    {
      intros x u v.
      simpl in *.
      dependent destruction u; dependent destruction v.
      rewrite simplify_plus_Branch_None.
      do 3 rewrite simplify_scal_Branch_None.
      rewrite simplify_plus_Branch_None.
      f_equal.
      { apply ModuleSpace.ax3. }
      { apply ModuleSpace.ax3. }
    }
    {
      intros x y u.
      simpl in u.
      dependent destruction u.
      do 3 rewrite simplify_scal_Branch_None.
      rewrite simplify_plus_Branch_None.
      f_equal.
      { apply ModuleSpace.ax4. }
      { apply ModuleSpace.ax4. }
    }
  Defined.
  Definition Branch_None_ModuleSpace_class_of : ModuleSpace.class_of AR T :=
    ModuleSpace.Class
      _ _ Branch_None_AbelianGroup_mixin Branch_None_ModuleSpace_mixin.
  Canonical Branch_None_ModuleSpace :=
    ModuleSpace.Pack
      AR T Branch_None_ModuleSpace_class_of T.

  Definition Branch_None_NormedModuleAux_class_of
    : NormedModuleAux.class_of AR T :=
    NormedModuleAux.Class
      _ _ Branch_None_ModuleSpace_class_of Branch_None_UniformSpace_mixin.
  Canonical Branch_None_NormedModuleAux :=
    NormedModuleAux.Pack
      AR T Branch_None_NormedModuleAux_class_of T.

  Definition Branch_None_norm : Branch_None_NormedModuleAux -> R.
    intros b.
    unfold Branch_None_NormedModuleAux in b.
    simpl in b.
    dependent destruction b.
    exact R0.
  Defined.

  Definition Branch_None_norm_factor : R.
    exact R1.
  Defined.

    Definition Branch_None_NormedModule_mixin
      : NormedModule.mixin_of K Branch_None_NormedModuleAux.
      apply NormedModule.Mixin with
        (norm        := Branch_None_norm)
        (norm_factor := Branch_None_norm_factor).
      { intros. unfold Branch_None_norm. psatzl R. }
      { intros. unfold Branch_None_norm. psatz R. }
      { intros. exact I. }
      {
        intros.
        destruct eps.
        unfold Branch_None_norm, Branch_None_norm_factor.
        simpl.
        psatz R.
      }
      { intros. symmetry. apply Branch_None_unit. }
    Defined.
    Definition Branch_None_NormedModule_class_of : NormedModule.class_of K T :=
      NormedModule.Class
        _ _ Branch_None_NormedModuleAux_class_of Branch_None_NormedModule_mixin.
    Canonical Branch_None_NormedModule_class_of.
    Canonical Branch_None_NormedModule :=
      NormedModule.Pack
        K T Branch_None_NormedModule_class_of T.

  End Branch_None_AbsRing.

End Branch_None_NormedModule.

Section Branch_Some_NormedModule.

  Variable AR : AbsRing.

  Variable L R : fields.
  Variable S : Type.
  Hypothesis L_NormedModule_class_of : NormedModule.class_of AR (record L).
  Hypothesis R_NormedModule_class_of : NormedModule.class_of AR (record R).
  Hypothesis S_NormedModule_class_of : NormedModule.class_of AR S.

  Local Notation T := (record (pm_Branch L (Some S) R)) (only parsing).

  Definition Branch_Some_plus : T -> T -> T.
    intros a b.
    dependent destruction a; dependent destruction b.
    constructor.
    { exact (AbelianGroup.plus _ L_NormedModule_class_of a1 b1). }
    { exact (AbelianGroup.plus _ S_NormedModule_class_of y y0). }
    { exact (AbelianGroup.plus _ R_NormedModule_class_of a2 b2). }
  Defined.

  Definition Branch_Some_opp : T -> T.
    intros x.
    dependent destruction x.
    constructor.
    { exact (AbelianGroup.opp _ L_NormedModule_class_of x1). }
    { exact (AbelianGroup.opp _ S_NormedModule_class_of y). }
    { exact (AbelianGroup.opp _ R_NormedModule_class_of x2). }
  Defined.

  Definition Branch_Some_zero : T.
    constructor.
    { exact (AbelianGroup.zero _ L_NormedModule_class_of). }
    { exact (AbelianGroup.zero _ S_NormedModule_class_of). }
    { exact (AbelianGroup.zero _ R_NormedModule_class_of). }
  Defined.

  Definition Branch_Some_AbelianGroup_mixin : AbelianGroup.mixin_of T.
    apply AbelianGroup.Mixin with
      (plus := Branch_Some_plus)
      (opp  := Branch_Some_opp)
      (zero := Branch_Some_zero).
    admit.
    admit.
    admit.
    admit.
  Admitted.
  Canonical Branch_Some_AbelianGroup :=
    AbelianGroup.Pack _ Branch_Some_AbelianGroup_mixin T.

End Branch_Some_NormedModule.



  Definition Branch_None_ModuleSpace_mixin (K : Ring)
    : ModuleSpace.mixin_of K Branch_None_AbelianGroup.
    apply ModuleSpace.Mixin with
    (scal := fun _ _ => pr_Leaf).
    { reflexivity. }
    { apply Leaf_unit. }
    { reflexivity. }
    { reflexivity. }
  Defined.
  Definition Leaf_ModuleSpace_class_of (K : Ring)
    : ModuleSpace.class_of K (record pm_Leaf) :=
    ModuleSpace.Class _ _ Leaf_AbelianGroup_mixin (Leaf_ModuleSpace_mixin _).
  Canonical Leaf_ModuleSpace (K : Ring) :=
    ModuleSpace.Pack
      K (record pm_Leaf) (Leaf_ModuleSpace_class_of _) (record pm_Leaf).

  Definition Leaf_NormedModuleAux_class_of (K : AbsRing)
    : NormedModuleAux.class_of K branchRecord :=
    NormedModuleAux.Class
      _ _ (Leaf_ModuleSpace_class_of _) Leaf_UniformSpace_mixin.
  Canonical Leaf_NormedModuleAux (K : AbsRing) :=
    NormedModuleAux.Pack
      K (record pm_Leaf) (Leaf_NormedModuleAux_class_of _) (record pm_Leaf).

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
    NormedModule.Class
      _ _ (Leaf_NormedModuleAux_class_of _) (Leaf_NormedModule_mixin _).
  Canonical Leaf_NormedModule_class_of.
  Canonical Leaf_NormedModule (K : AbsRing) :=
    NormedModule.Pack
      K (record pm_Leaf) (Leaf_NormedModule_class_of _) (record pm_Leaf).

  Definition Branch_None_NormedModule_class_of
    : NormedModule.class_of K (record (pm_Branch L None R)) :=
    NormedModule.Class
      _ _ (Leaf_NormedModuleAux_class_of _) (Leaf_NormedModule_mixin _).
  Canonical Leaf_NormedModule_class_of.
  Canonical Leaf_NormedModule (K : AbsRing) :=
    NormedModule.Pack
      K (record pm_Leaf) (Leaf_NormedModule_class_of _) (record pm_Leaf).

End Branch_NormedModule.
