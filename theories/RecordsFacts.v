Require Import BinPos.
Require Import Records.Records.

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

Require Import Program.

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

(*
Lemma different_var_different_member:
  forall (T: Type) (vars: fields) (x y : field) vx vy
    (X: fields_get x vars = Some vx)
    (Y: fields_get y vars = Some vy)
  ,
    x <> y ->
    member_to_positive (get_member x vars X) <>
    member_to_positive (get_member y vars Y).
Proof.

Qed.
 *)
