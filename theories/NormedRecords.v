Require Import Records.Records.
Require Import Coq.Reals.Reals.
Require Import Coquelicot.Coquelicot.
Require Import Coq.micromega.Psatz.

Lemma Leaf_unit : forall x : record pm_Leaf, pr_Leaf = x.
Proof.
  Require Import Equality. dependent destruction x. reflexivity.
Qed.

Definition Leaf_AbelianGroup_mixin : AbelianGroup.mixin_of (record pm_Leaf).
  refine (AbelianGroup.Mixin _ (fun _ _ => pr_Leaf) (fun _ => pr_Leaf) pr_Leaf _ _ _ _);
    try reflexivity. apply Leaf_unit.
Defined.
Canonical Leaf_AbelianGroup := AbelianGroup.Pack _ Leaf_AbelianGroup_mixin (record pm_Leaf).

Definition Leaf_Ring_mixin : Ring.mixin_of Leaf_AbelianGroup.
  refine (Ring.Mixin _ (fun _ _ => pr_Leaf) pr_Leaf _ _ _ _ _); try reflexivity; apply Leaf_unit.
Defined.
Canonical Leaf_Ring :=
  Ring.Pack (record pm_Leaf) (Ring.Class _ _ Leaf_Ring_mixin) (record pm_Leaf).

Definition Leaf_UniformSpace_mixin : UniformSpace.mixin_of (record pm_Leaf).
  refine (UniformSpace.Mixin _ (fun _ _ _ => True) _ _ _); intros; exact I.
Defined.
Canonical Leaf_UniformSpace :=
  UniformSpace.Pack (record pm_Leaf) Leaf_UniformSpace_mixin (record pm_Leaf).

Definition Leaf_ModuleSpace_mixin (K : Ring) : ModuleSpace.mixin_of K Leaf_AbelianGroup.
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

Definition Leaf_NormedModule_mixin (K : AbsRing) : NormedModule.mixin_of K (Leaf_NormedModuleAux _).
  refine (NormedModule.Mixin _ _ (fun _ => R0) R1 _ _ _ _ _).
  { intros. psatzl R. }
  { intros. psatz R. }
  { intros. unfold ball. simpl. exact I. }
  { intros. destruct eps. simpl. psatz R. }
  { intros. symmetry. apply Leaf_unit. }
Defined.
Definition Leaf_NormedModule_class_of (K : AbsRing) : NormedModule.class_of K (record pm_Leaf) :=
  NormedModule.Class _ _ (Leaf_NormedModuleAux_class_of _) (Leaf_NormedModule_mixin _).
Canonical Leaf_NormedModule_class_of.
Canonical Leaf_NormedModule (K : AbsRing) :=
  NormedModule.Pack K (record pm_Leaf) (Leaf_NormedModule_class_of _) (record pm_Leaf).

Section Branch_NormedModule.

  Variable K : AbsRing.

  Variable L R : fields.
  Hypothesis L_NormedModule_class_of : NormedModule.class_of K (record L).
  Hypothesis R_NormedModule_class_of : NormedModule.class_of K (record R).

  Definition Branch_None_NormedModule_class_of (T : NormedModule K)
    : Type.
    refine (NormedModule.class_of K (record (pm_Branch L (@Some Type T) R))).
