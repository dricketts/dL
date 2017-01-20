Set Universe Polymorphism.

Require Import Coq.Reals.Reals.
Require Import Coquelicot.Coquelicot.
Require Import Coq.micromega.Psatz.
Require Import Equality.
Require Import Records.Records.

Lemma sqrt_plus : forall a b, sqrt (a^2 + b^2) <= sqrt 2 * Rmax (Rabs a) (Rabs b).
Proof.
  intros a b.
  apply sqrt_plus_sqr.
Qed.

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

    Variable K : Ring. (* for generality, but in practice it'll have to be AbsRing *)

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

  Variable K : AbsRing.

  Variable l r : fields.

  Hypothesis L_NormedModule_class_of : NormedModule.class_of K (record l).
  Hypothesis R_NormedModule_class_of : NormedModule.class_of K (record r).

  Definition L_NormedModule := NormedModule.Pack _ _ L_NormedModule_class_of K.
  Definition R_NormedModule := NormedModule.Pack _ _ R_NormedModule_class_of K.

  Local Notation T := (record (pm_Branch l None r)) (only parsing).

  Definition Branch_None_plus : T -> T -> T.
    intros a b.
    dependent destruction a; dependent destruction b.
    constructor.
    { exact (@plus L_NormedModule a1 b1). }
    { exact tt. }
    { exact (@plus R_NormedModule a2 b2). }
  Defined.

  Lemma simplify_plus_Branch_None:
    forall (l1 l2 : record l) (v1 v2 : unit) (r1 r2 : record r),
      Branch_None_plus
        (pr_Branch None l1 v1 r1)
        (pr_Branch None l2 v2 r2) =
      pr_Branch
        None
        (@plus L_NormedModule l1 l2 : record l)
        tt
        (@plus R_NormedModule r1 r2 : record r).
  Proof.
    reflexivity.
  Qed.

  Definition Branch_None_opp : T -> T.
    intros x.
    dependent destruction x.
    constructor.
    { exact (@opp L_NormedModule x1). }
    { exact tt. }
    { exact (@opp R_NormedModule x2). }
  Defined.

  Lemma simplify_opp_Branch_None :
    forall a b v,
      Branch_None_opp (pr_Branch None a v b)
      = pr_Branch
          None
          (@opp L_NormedModule a : record l)
          tt
          (@opp R_NormedModule b : record r).
  Proof.
    reflexivity.
  Qed.

  Definition Branch_None_zero : T.
    constructor.
    { exact (@zero L_NormedModule). }
    { exact tt. }
    { exact (@zero R_NormedModule). }
  Defined.

  Lemma simplify_zero_Branch_None :
    Branch_None_zero =
    pr_Branch
      None
      (@zero L_NormedModule : record l)
      tt
      (@zero R_NormedModule : record r).
  Proof.
    reflexivity.
  Qed.

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
    pose proof (@ball L_NormedModule a1 eps b1) as P1.
    pose proof (@ball R_NormedModule a2 eps b2) as P2.
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
        @ball L_NormedModule l1 eps l2
        /\
        @ball R_NormedModule r1 eps r2
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
      split.
      { now apply UniformSpace.ax2. }
      { now apply UniformSpace.ax2. }
    }
    {
      intros a b c eps1 eps2.
      dependent destruction a; dependent destruction b; dependent destruction c.
      do 3 rewrite simplify_ball_Branch_None.
      intuition.
      { eapply UniformSpace.ax3; eauto. }
      { eapply UniformSpace.ax3; eauto. }
    }
  Defined.
  Canonical Branch_None_UniformSpace :=
    UniformSpace.Pack T Branch_None_UniformSpace_mixin T.

  Definition Branch_None_scal : K -> T -> T.
    intros k b.
    dependent destruction b.
    apply pr_Branch.
    { exact (@scal _ L_NormedModule k b1). }
    { exact tt. }
    { exact (@scal _ R_NormedModule k b2). }
  Defined.

  Lemma simplify_scal_Branch_None:
    forall (k : K) (l1 : record l) (v : unit) (r1 : record r),
      Branch_None_scal k (pr_Branch None l1 v r1)
      = pr_Branch
          None
          (@scal _ L_NormedModule k l1 : record l)
          tt
          (@scal _ R_NormedModule k r1 : record r).
  Proof.
    reflexivity.
  Qed.

  Definition Branch_None_ModuleSpace_mixin
    : ModuleSpace.mixin_of K Branch_None_AbelianGroup.
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
  Definition Branch_None_ModuleSpace_class_of : ModuleSpace.class_of K T :=
    ModuleSpace.Class
      _ _ Branch_None_AbelianGroup_mixin Branch_None_ModuleSpace_mixin.
  Canonical Branch_None_ModuleSpace :=
    ModuleSpace.Pack
      K T Branch_None_ModuleSpace_class_of T.

  Definition Branch_None_NormedModuleAux_class_of
    : NormedModuleAux.class_of K T :=
    NormedModuleAux.Class
      _ _ Branch_None_ModuleSpace_class_of Branch_None_UniformSpace_mixin.
  Canonical Branch_None_NormedModuleAux :=
    NormedModuleAux.Pack
      K T Branch_None_NormedModuleAux_class_of T.

  Definition Branch_None_norm : Branch_None_NormedModuleAux -> R.
    intros b.
    unfold Branch_None_NormedModuleAux in b.
    simpl in b.
    dependent destruction b.
    pose proof (@norm _ L_NormedModule b1) as n1.
    pose proof (@norm _ R_NormedModule b2) as n2.
    exact (sqrt (n1 ^ 2 + n2 ^ 2)).
  Defined.

  Lemma simplify_norm_Branch_None:
    forall (l1 : record l) (v : unit) (r1 : record r),
      Branch_None_norm (pr_Branch None l1 v r1)
      =
      sqrt (
          ((@norm _ L_NormedModule l1) ^ 2)
          +
          ((@norm _ R_NormedModule r1) ^ 2)
        ).
  Proof.
    reflexivity.
  Qed.

  Definition Branch_None_norm_factor : R.
    pose proof (@norm_factor _ L_NormedModule) as nfl.
    pose proof (@norm_factor _ R_NormedModule) as nfr.
    exact (sqrt 2 * Rmax nfl nfr).
  Defined.

  Definition Branch_None_NormedModule_mixin
    : NormedModule.mixin_of K Branch_None_NormedModuleAux.
    apply NormedModule.Mixin with
      (norm        := Branch_None_norm)
      (norm_factor := Branch_None_norm_factor).
    {
      simpl.
      intros a b.
      dependent destruction a; dependent destruction b.
      rewrite simplify_plus_Branch_None.
      do 3 rewrite simplify_norm_Branch_None.

      apply Rle_trans with
      (
        sqrt (
            ((plus (@norm _ L_NormedModule a1) (@norm _ L_NormedModule b1)) ^ 2)
            +
            ((plus (@norm _ R_NormedModule a2) (@norm _ R_NormedModule b2)) ^ 2)
          )
      ).

      {
        apply sqrt_le_1_alt.
        apply Rplus_le_compat.
        {
          apply Rmult_le_compat.
          { apply norm_ge_0. }
          {
            apply Rmult_le_pos.
            { apply norm_ge_0. }
            { psatzl R. }
          }
          { apply NormedModule.ax1. }
          {
            do 2 rewrite Rmult_1_r.
            apply NormedModule.ax1.
          }
        }
        {
          apply Rmult_le_compat.
          { apply norm_ge_0. }
          {
            apply Rmult_le_pos.
            { apply norm_ge_0. }
            { psatzl R. }
          }
          { apply NormedModule.ax1. }
          {
            do 2 rewrite Rmult_1_r.
            apply NormedModule.ax1.
          }
        }
      }

      {
        apply Rsqr_incr_0_var.
        {
          apply Rminus_le_0.
          unfold pow.
          repeat rewrite Rmult_1_r.

          admit.

(*
  unfold Rsqr ; simpl ; ring_simplify.
  rewrite /pow ?Rmult_1_r.
  rewrite ?sqrt_sqrt ; ring_simplify.
  replace (-2 * norm xu * norm yu - 2 * norm xv * norm yv)
    with (-(2 * (norm xu * norm yu + norm xv * norm yv))) by ring.
  rewrite Rmult_assoc -sqrt_mult.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rmult_le_compat_l.
  apply Rlt_le, Rlt_0_2.
  apply Rsqr_incr_0_var.
  apply Rminus_le_0.
  rewrite /Rsqr ?sqrt_sqrt ; ring_simplify.
  replace (norm xu ^ 2 * norm yv ^ 2 - 2 * norm xu * norm xv * norm yu * norm yv + norm xv ^ 2 * norm yu ^ 2)
    with ((norm xu * norm yv - norm xv * norm yu) ^ 2) by ring.
  apply pow2_ge_0.
  repeat apply Rplus_le_le_0_compat ; apply Rmult_le_pos ; apply pow2_ge_0.
  apply sqrt_pos.
  apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
  apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
  replace (norm xu ^ 2 + 2 * norm xu * norm yu + norm yu ^ 2 + norm xv ^ 2 + 2 * norm xv * norm yv + norm yv ^ 2)
    with ((norm xu + norm yu) ^ 2 + (norm xv + norm yv) ^ 2) by ring.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply sqrt_pos.
 *)
        }
        {
          admit.
        }
      }
    }
    {
      simpl.
      intros k b.
      dependent destruction b.
      rewrite simplify_scal_Branch_None.
      rewrite simplify_norm_Branch_None.
      pose proof (@NormedModule.ax2 _ L_NormedModule L_NormedModule_class_of k b1) as L.
      pose proof (@NormedModule.ax2 _ R_NormedModule R_NormedModule_class_of k b2) as R.
      admit.
    }
    {
      simpl.
      intros a b eps.
      dependent destruction a; dependent destruction b.
      unfold minus.
      rewrite simplify_opp_Branch_None.
      rewrite simplify_plus_Branch_None.
      rewrite simplify_norm_Branch_None.
      pose proof (@NormedModule.ax3 _ L_NormedModule L_NormedModule_class_of a1 b1 eps) as L.
      pose proof (@NormedModule.ax3 _ R_NormedModule R_NormedModule_class_of a2 b2 eps) as R.
      admit.
    }
    {
      simpl.
      intros a b eps.
      dependent destruction a; dependent destruction b.
      rewrite simplify_ball_Branch_None.
      intros [BL BR].
      unfold minus.
      rewrite simplify_opp_Branch_None.
      rewrite simplify_plus_Branch_None.
      rewrite simplify_norm_Branch_None.
      pose proof (
             @NormedModule.ax4 _ L_NormedModule L_NormedModule_class_of a1 b1 eps BL
           ) as L.
      pose proof (
             @NormedModule.ax4 _ R_NormedModule R_NormedModule_class_of a2 b2 eps BR
           ) as R.
      unfold minus in *.
      admit.
    }
    {
      simpl.
      intros b.
      dependent destruction b.
      rewrite simplify_norm_Branch_None.
      intros H.
      assert (@norm _ L_NormedModule b1 = 0) by admit.
      assert (@norm _ R_NormedModule b2 = 0) by admit.
      unfold zero.
      simpl.
      rewrite simplify_zero_Branch_None.
      pose proof (@NormedModule.ax5 _ L_NormedModule L_NormedModule_class_of b1) as L.
      pose proof (@NormedModule.ax5 _ R_NormedModule R_NormedModule_class_of b2) as R.
      f_equal.
      { now apply L. }
      { now destruct y. }
      { now apply R. }
    }
  Admitted.
  Definition Branch_None_NormedModule_class_of : NormedModule.class_of K T :=
    NormedModule.Class
      _ _ Branch_None_NormedModuleAux_class_of Branch_None_NormedModule_mixin.
  Canonical Branch_None_NormedModule_class_of.
  Canonical Branch_None_NormedModule :=
    NormedModule.Pack
      K T Branch_None_NormedModule_class_of T.

End Branch_None_NormedModule.

Section Branch_Some_NormedModule.

  Variable K : AbsRing.

  Variable l r : fields.
  Variable S : Type.

  Hypothesis L_NormedModule_class_of : NormedModule.class_of K (record l).
  Hypothesis R_NormedModule_class_of : NormedModule.class_of K (record r).
  Hypothesis S_NormedModule_class_of : NormedModule.class_of K S.

  Let L_NormedModule := NormedModule.Pack _ _ L_NormedModule_class_of K.
  Let R_NormedModule := NormedModule.Pack _ _ R_NormedModule_class_of K.
  Let S_NormedModule := NormedModule.Pack _ _ S_NormedModule_class_of K.

  Local Notation T := (record (pm_Branch l (Some S) r)) (only parsing).

  Definition Branch_Some_plus : T -> T -> T.
    intros a b.
    dependent destruction a; dependent destruction b.
    constructor.
    { exact (@plus L_NormedModule a1 b1). }
    { exact (@plus S_NormedModule y y0). }
    { exact (@plus R_NormedModule a2 b2). }
  Defined.

  Lemma simplify_plus_Branch_Some:
    forall (l1 l2 : record l) (v1 v2 : S) (r1 r2 : record r),
      Branch_Some_plus
        (pr_Branch (Some S) l1 v1 r1)
        (pr_Branch (Some S) l2 v2 r2) =
      pr_Branch
        (Some S)
        (@plus L_NormedModule l1 l2 : record l)
        (@plus S_NormedModule v1 v2)
        (@plus R_NormedModule r1 r2 : record r).
  Proof.
    reflexivity.
  Qed.

  Definition Branch_Some_opp : T -> T.
    intros x.
    dependent destruction x.
    constructor.
    { exact (@opp L_NormedModule x1). }
    { exact (@opp S_NormedModule y). }
    { exact (@opp R_NormedModule x2). }
  Defined.

  Lemma simplify_opp_Branch_Some :
    forall a b v,
      Branch_Some_opp (pr_Branch (Some S) a v b)
      = pr_Branch
          (Some S)
          (@opp L_NormedModule a : record l)
          (@opp S_NormedModule v)
          (@opp R_NormedModule b : record r).
  Proof.
    reflexivity.
  Qed.

  Definition Branch_Some_zero : T.
    constructor.
    { exact (@zero L_NormedModule). }
    { exact (@zero S_NormedModule). }
    { exact (@zero R_NormedModule). }
  Defined.

  Lemma simplify_zero_Branch_Some :
    Branch_Some_zero =
    pr_Branch
      (Some S)
      (@zero L_NormedModule : record l)
      (@zero S_NormedModule)
      (@zero R_NormedModule : record r).
  Proof.
    reflexivity.
  Qed.

  Definition Branch_Some_AbelianGroup_mixin : AbelianGroup.mixin_of T.
    apply AbelianGroup.Mixin with
      (plus := Branch_Some_plus)
      (opp  := Branch_Some_opp)
      (zero := Branch_Some_zero).
    {
      intros a b.
      dependent destruction a; dependent destruction b.
      do 2 rewrite simplify_plus_Branch_Some.
      f_equal; apply AbelianGroup.ax1.
    }
    {
      intros a b c.
      dependent destruction a; dependent destruction b; dependent destruction c.
      do 4 rewrite simplify_plus_Branch_Some.
      f_equal; apply AbelianGroup.ax2.
    }
    {
      intro x.
      dependent destruction x.
      rewrite simplify_zero_Branch_Some.
      rewrite simplify_plus_Branch_Some.
      f_equal.
      { apply AbelianGroup.ax3. }
      { apply AbelianGroup.ax3. }
      { apply AbelianGroup.ax3. }
    }
    {
      intro x.
      dependent destruction x.
      rewrite simplify_opp_Branch_Some.
      rewrite simplify_plus_Branch_Some.
      rewrite simplify_zero_Branch_Some.
      f_equal.
      { apply AbelianGroup.ax4. }
      { apply AbelianGroup.ax4. }
      { apply AbelianGroup.ax4. }
    }
  Defined.
  Canonical Branch_Some_AbelianGroup :=
    AbelianGroup.Pack _ Branch_Some_AbelianGroup_mixin T.

  Definition Branch_Some_ball : T -> R -> T -> Prop.
    intros a eps b.
    dependent destruction a; dependent destruction b.
    pose proof (@ball L_NormedModule a1 eps b1) as PL.
    pose proof (@ball S_NormedModule y  eps y0) as PS.
    pose proof (@ball R_NormedModule a2 eps b2) as PR.
    exact (PL /\ PS /\ PR).
  Defined.

  Lemma simplify_ball_Branch_Some:
    forall (l1 l2 : record l) (v1 v2 : S) (r1 r2 : record r) eps,
      Branch_Some_ball
        (pr_Branch (Some S) l1 v1 r1)
        eps
        (pr_Branch (Some S) l2 v2 r2)
      =
      (
        @ball L_NormedModule l1 eps l2
        /\
        @ball S_NormedModule v1 eps v2
        /\
        @ball R_NormedModule r1 eps r2
      ).
  Proof.
    reflexivity.
  Qed.

  Definition Branch_Some_UniformSpace_mixin : UniformSpace.mixin_of T.
    apply UniformSpace.Mixin with
      (ball := Branch_Some_ball).
    {
      intros x eps.
      dependent destruction x.
      rewrite simplify_ball_Branch_Some.
      repeat split.
      { apply UniformSpace.ax1. }
      { apply UniformSpace.ax1. }
      { apply UniformSpace.ax1. }
    }
    {
      intros a b eps.
      dependent destruction a; dependent destruction b.
      do 2 rewrite simplify_ball_Branch_Some.
      repeat split.
      { now apply UniformSpace.ax2. }
      { now apply UniformSpace.ax2. }
      { now apply UniformSpace.ax2. }
    }
    {
      intros a b c eps1 eps2.
      dependent destruction a; dependent destruction b; dependent destruction c.
      do 3 rewrite simplify_ball_Branch_Some.
      intuition.
      { eapply UniformSpace.ax3; eauto. }
      { eapply UniformSpace.ax3; eauto. }
      { eapply UniformSpace.ax3; eauto. }
    }
  Defined.
  Canonical Branch_Some_UniformSpace :=
    UniformSpace.Pack T Branch_Some_UniformSpace_mixin T.

  Definition Branch_Some_scal : K -> T -> T.
    intros k b.
    dependent destruction b.
    apply pr_Branch.
    { exact (@scal _ L_NormedModule k b1). }
    { exact (@scal _ S_NormedModule k y). }
    { exact (@scal _ R_NormedModule k b2). }
  Defined.

  Lemma simplify_scal_Branch_Some:
    forall (k : K) (l1 : record l) (v : S) (r1 : record r),
      Branch_Some_scal k (pr_Branch (Some S) l1 v r1)
      = pr_Branch
          (Some S)
          (@scal _ L_NormedModule k l1 : record l)
          (@scal _ S_NormedModule k v)
          (@scal _ R_NormedModule k r1 : record r).
  Proof.
    reflexivity.
  Qed.

  Definition Branch_Some_ModuleSpace_mixin
    : ModuleSpace.mixin_of K Branch_Some_AbelianGroup.
    unfold Branch_Some_AbelianGroup.
    apply ModuleSpace.Mixin with
    (scal := Branch_Some_scal).
    {
      intros x y u.
      simpl in u.
      dependent destruction u.
      do 3 rewrite simplify_scal_Branch_Some.
      f_equal.
      { apply ModuleSpace.ax1. }
      { apply ModuleSpace.ax1. }
      { apply ModuleSpace.ax1. }
    }
    {
      intros u.
      simpl in u.
      dependent destruction u.
      rewrite simplify_scal_Branch_Some.
      f_equal.
      { apply ModuleSpace.ax2. }
      { apply ModuleSpace.ax2. }
      { apply ModuleSpace.ax2. }
    }
    {
      intros x u v.
      simpl in *.
      dependent destruction u; dependent destruction v.
      rewrite simplify_plus_Branch_Some.
      do 3 rewrite simplify_scal_Branch_Some.
      rewrite simplify_plus_Branch_Some.
      f_equal.
      { apply ModuleSpace.ax3. }
      { apply ModuleSpace.ax3. }
      { apply ModuleSpace.ax3. }
    }
    {
      intros x y u.
      simpl in u.
      dependent destruction u.
      do 3 rewrite simplify_scal_Branch_Some.
      rewrite simplify_plus_Branch_Some.
      f_equal.
      { apply ModuleSpace.ax4. }
      { apply ModuleSpace.ax4. }
      { apply ModuleSpace.ax4. }
    }
  Defined.
  Definition Branch_Some_ModuleSpace_class_of : ModuleSpace.class_of K T :=
    ModuleSpace.Class
      _ _ Branch_Some_AbelianGroup_mixin Branch_Some_ModuleSpace_mixin.
  Canonical Branch_Some_ModuleSpace :=
    ModuleSpace.Pack
      K T Branch_Some_ModuleSpace_class_of T.

  Definition Branch_Some_NormedModuleAux_class_of
    : NormedModuleAux.class_of K T :=
    NormedModuleAux.Class
      _ _ Branch_Some_ModuleSpace_class_of Branch_Some_UniformSpace_mixin.
  Canonical Branch_Some_NormedModuleAux :=
    NormedModuleAux.Pack
      K T Branch_Some_NormedModuleAux_class_of T.

  Definition Branch_Some_norm : Branch_Some_NormedModuleAux -> R.
    intros b.
    unfold Branch_Some_NormedModuleAux in b.
    simpl in b.
    dependent destruction b.
    pose proof (@norm _ L_NormedModule b1) as nl.
    pose proof (@norm _ S_NormedModule y) as ns.
    pose proof (@norm _ R_NormedModule b2) as nr.
    exact (sqrt (nl ^ 2 + ns ^ 2 + nr ^ 2)).
  Defined.

  Lemma simplify_norm_Branch_Some:
    forall (l1 : record l) (v : S) (r1 : record r),
      Branch_Some_norm (pr_Branch (Some S) l1 v r1)
      =
      sqrt (
          ((@norm _ L_NormedModule l1) ^ 2)
          +
          ((@norm _ S_NormedModule v) ^ 2)
          +
          ((@norm _ R_NormedModule r1) ^ 2)
        ).
  Proof.
    reflexivity.
  Qed.

  Definition Branch_Some_norm_factor : R.
    pose proof (@norm_factor _ L_NormedModule) as nfl.
    pose proof (@norm_factor _ S_NormedModule) as nfs.
    pose proof (@norm_factor _ R_NormedModule) as nfr.
    exact (sqrt 2 * Rmax nfs (Rmax nfl nfr)). (* not sure about this *)
  Defined.

  Definition Branch_Some_NormedModule_mixin
    : NormedModule.mixin_of K Branch_Some_NormedModuleAux.
    apply NormedModule.Mixin with
      (norm        := Branch_Some_norm)
      (norm_factor := Branch_Some_norm_factor).
    {
      simpl.
      intros a b.
      dependent destruction a; dependent destruction b.
      rewrite simplify_plus_Branch_Some.
      do 3 rewrite simplify_norm_Branch_Some.
      pose proof (@NormedModule.ax1 _ L_NormedModule L_NormedModule_class_of a1 b1) as L.
      pose proof (@NormedModule.ax1 _ S_NormedModule S_NormedModule_class_of y y0) as NS.
      pose proof (@NormedModule.ax1 _ R_NormedModule R_NormedModule_class_of a2 b2) as R.
      admit.
    }
    {
      simpl.
      intros k b.
      dependent destruction b.
      rewrite simplify_scal_Branch_Some.
      rewrite simplify_norm_Branch_Some.
      pose proof (@NormedModule.ax2 _ L_NormedModule L_NormedModule_class_of k b1) as L.
      pose proof (@NormedModule.ax2 _ S_NormedModule S_NormedModule_class_of k y) as NS.
      pose proof (@NormedModule.ax2 _ R_NormedModule R_NormedModule_class_of k b2) as R.
      admit.
    }
    {
      simpl.
      intros a b eps.
      dependent destruction a; dependent destruction b.
      unfold minus.
      rewrite simplify_opp_Branch_Some.
      rewrite simplify_plus_Branch_Some.
      rewrite simplify_norm_Branch_Some.
      pose proof (@NormedModule.ax3 _ L_NormedModule L_NormedModule_class_of a1 b1 eps) as L.
      pose proof (@NormedModule.ax3 _ S_NormedModule S_NormedModule_class_of y y0 eps) as NS.
      pose proof (@NormedModule.ax3 _ R_NormedModule R_NormedModule_class_of a2 b2 eps) as R.
      admit.
    }
    {
      simpl.
      intros a b eps.
      dependent destruction a; dependent destruction b.
      rewrite simplify_ball_Branch_Some.
      intros [BL [BS BR]].
      unfold minus.
      rewrite simplify_opp_Branch_Some.
      rewrite simplify_plus_Branch_Some.
      rewrite simplify_norm_Branch_Some.
      pose proof (
             @NormedModule.ax4 _ L_NormedModule L_NormedModule_class_of a1 b1 eps BL
           ) as L.
      pose proof (
             @NormedModule.ax4 _ S_NormedModule S_NormedModule_class_of y y0 eps BS
           ) as NS.
      pose proof (
             @NormedModule.ax4 _ R_NormedModule R_NormedModule_class_of a2 b2 eps BR
           ) as R.
      unfold minus in *.
      admit.
    }
    {
      simpl.
      intros b.
      dependent destruction b.
      rewrite simplify_norm_Branch_Some.
      intros H.
      assert (@norm _ L_NormedModule b1 = 0) by admit.
      assert (@norm _ S_NormedModule y = 0) by admit.
      assert (@norm _ R_NormedModule b2 = 0) by admit.
      unfold zero.
      simpl.
      rewrite simplify_zero_Branch_Some.
      pose proof (@NormedModule.ax5 _ L_NormedModule L_NormedModule_class_of b1) as L.
      pose proof (@NormedModule.ax5 _ S_NormedModule S_NormedModule_class_of y) as NS.
      pose proof (@NormedModule.ax5 _ R_NormedModule R_NormedModule_class_of b2) as R.
      f_equal.
      { now apply L. }
      { now apply NS. }
      { now apply R. }
    }
  Admitted.
  Definition Branch_Some_NormedModule_class_of : NormedModule.class_of K T :=
    NormedModule.Class
      _ _ Branch_Some_NormedModuleAux_class_of Branch_Some_NormedModule_mixin.
  Canonical Branch_Some_NormedModule_class_of.
  Canonical Branch_Some_NormedModule :=
    NormedModule.Pack
      K T Branch_Some_NormedModule_class_of T.

End Branch_Some_NormedModule.
