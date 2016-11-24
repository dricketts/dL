Require Import BinPos.
Require Import Coq.Logic.FinFun.
Require Import Program.
Require Import Records.Records.

(** TODO: This should be moved to the extensible records repository *)
Class FieldOf vars x T : Prop :=
  mkFieldOf
    { _field_proof : fields_get x vars = Some T }.
Arguments _field_proof [_ _ _] _.

Hint Extern 0 (FieldOf _ _ _) => constructor; reflexivity : typeclass_instances.

Ltac apply_obvious :=
  match goal with
  | [ H: _ |- _ ] => apply H
  end.

Lemma record_get_record_set_same:
  forall (T: Type) (vars: fields)
    (pm: member T vars)
    (r: record vars) (val: T),
    record_get pm (record_set pm val r) = val.
Proof.
  intros.
  induction pm; simpl.
  { reflexivity. }
  { apply_obvious. }
  { apply_obvious. }
Qed.

Fixpoint
  member_to_positive
  {T: Type} {vars: fields} (m: member T vars): positive :=
  match m with
  | pmm_H _ _ _ => xH
  | pmm_L V R mL => xO (member_to_positive mL)
  | pmm_R V L mR => xI (member_to_positive mR)
  end.

Ltac break_member :=
  (* This should use is_contructor in 8.6 *)
  match goal with
  | [ m: member _ pm_Leaf |- _ ] => dependent destruction m
  | [ m: member _ (pm_Branch _ _ _) |- _ ] => dependent destruction m
  | [ r: record pm_Leaf |- _ ] => dependent destruction r
  | [ m: record (pm_Branch _ _ _) |- _ ] => dependent destruction r
  end.

Lemma record_get_record_set_different:
  forall (T: Type) (vars: fields)
    (pmr pmw: member T vars)
    (diff: member_to_positive pmr <> member_to_positive pmw)
    (r: record vars) (val: T),
    record_get pmr (record_set pmw val r) = record_get pmr r.
Proof.
  intros.
  induction vars.
  { break_member. }
  { repeat break_member; simpl in *; try congruence.
    { apply_obvious. congruence. }
    { apply_obvious. congruence. }
  }
Qed.

Lemma fields_get_Leaf_None:
  forall (x: field),
    fields_get x pm_Leaf = None.
Proof.
  induction x; simpl; congruence.
Qed.

Lemma different_var_different_member:
  forall (x y : field) (vars: fields) vx vy
    (X: fields_get x vars = Some vx)
    (Y: fields_get y vars = Some vy)
  ,
    x <> y ->
    member_to_positive (get_member x vars X) <>
    member_to_positive (get_member y vars Y).
Proof.
  intros.
  (* kinda want to do the destruct vars here, but want to keep the IH general *)
  dependent induction x; intros;
    (destruct vars as [|L ? R];
     [ exfalso; rewrite fields_get_Leaf_None in X; discriminate | simpl in * ]).

  {
    destruct y; simpl in *.
    { intro.
      apply IHx with (X := X) (Y := Y).
      { congruence. }
      { congruence. }
    }
    { congruence. }
    {
      dependent destruction o.
      {
        dependent destruction Y.
        simpl.
        congruence.
      }
      { congruence. }
    }
  }

  {
    destruct y; simpl in *.
    { congruence. }
    { intro.
      apply IHx with (X := X) (Y := Y).
      { congruence. }
      { congruence. }
    }
    {
      dependent destruction o.
      {
        dependent destruction Y.
        simpl.
        congruence.
      }
      { congruence. }
    }
  }

  {
    dependent destruction o.
    {
      dependent destruction X.
      simpl.
      destruct y; simpl in *.
      { congruence. }
      { congruence. }
      { congruence. }
    }
    { congruence. }
  }

Qed.

Theorem ascii_to_p_injection:
  forall a b s t, ascii_to_p a s = ascii_to_p b t -> a = b /\ s = t.
Proof.
  intros.
  repeat (
      match goal with
      | [ a: Ascii.ascii |- _ ] => destruct a
      | [ H: bool_to_p ?b1 _ = bool_to_p ?b2 _ |- _ ] =>
        destruct b1; destruct b2; simpl in H; try congruence; inversion H; clear H
      | _ => simpl in *
      end
    ); split; reflexivity.
Qed.

Theorem string_to_p_injective: Injective string_to_p.
Proof.

  intro x.
  induction x; intros y XY; destruct y; simpl in *.

  { reflexivity. }

  {
    destruct a.
    destruct b.
    {
      simpl in XY.
      congruence.
    }
    {
      simpl in XY.
      congruence.
    }
  }

  {
    destruct a.
    destruct b.
    {
      simpl in XY.
      congruence.
    }
    {
      simpl in XY.
      congruence.
    }
  }

  {
    apply ascii_to_p_injection in XY.
    f_equal; firstorder.
  }

Qed.
