
Set Universe Polymorphism.

Require Import Records.Records.
Require Import Equality.

Ltac infer_instance := constructor; auto with typeclass_instances.

(*** Plus ***)

Class Commutative {T : Type} (op : T -> T -> T) :=
  { commutativity : forall a b, op a b = op b a; }.

Class Associative {T : Type} (op : T -> T -> T) :=
  { associativity : forall a b c, op a (op b c) = op (op a b) c; }.

Class PlusOp (T : Type) := plus_op : T -> T -> T.
Infix "+" := (plus_op).

Class Plus T {Plus_PlusOp : PlusOp T} :=
  {
    Plus_Commutative :> Commutative plus_op;
    Plus_Associative :> Associative plus_op;
  }.

(*** Plus Leaf ***)

Global Instance PlusOp_Leaf : PlusOp (record pm_Leaf).
Proof.
  unfold PlusOp. intros _ _. exact pr_Leaf.
Defined.

Global Instance Plus_Leaf : Plus (record pm_Leaf).
Proof.
  constructor.
  { constructor. intros. reflexivity. }
  { constructor. intros. reflexivity. }
Qed.

(*** Plus Branch None ***)

Section Branch_None.

  Variables (l r : fields).

  Section With_PlusOp.

    Context `{PlusOp (record l)} `{PlusOp (record r)}.

    Global Instance PlusOp_Branch_None :
      PlusOp (record (pm_Branch l None r)).
    Proof.
      intros a b.
      dependent destruction a; dependent destruction b.
      constructor.
      { exact (a1 + b1). }
      { exact tt. }
      { exact (a2 + b2). }
    Defined.

    Lemma simplify_plus_Branch_None:
      forall (l1 l2 : record l) (v1 v2: unit) (r1 r2 : record r),
        pr_Branch None l1 v1 r1 + pr_Branch None l2 v2 r2 =
        pr_Branch None (l1 + l2) tt (r1 + r2).
    Proof.
      intros.
      reflexivity.
    Qed.

  End With_PlusOp.

  Section With_Plus.

    Context `{Plus (record l)} `{Plus (record r)}.

    Global Instance Plus_Branch_None : Plus (record (pm_Branch l None r)).
    Proof.
      constructor.
      {
        constructor.
        intros a b.
        dependent destruction a; dependent destruction b.
        do 2 rewrite simplify_plus_Branch_None.
        f_equal; apply commutativity.
      }
      {
        constructor.
        intros a b c.
        dependent destruction a; dependent destruction b; dependent destruction c.
        do 4 rewrite simplify_plus_Branch_None.
        f_equal; apply associativity.
      }
    Qed.

  End With_Plus.

End Branch_None.

(*** Plus Branch Some ***)

Section Branch_Some.

  Variables (l r : fields).
  Context `{T : Type}.

  Section With_PlusOp.

    Context `{PlusOp (record l)} `{PlusOp T} `{PlusOp (record r)}.

    Global Instance PlusOp_Branch_Some :
      PlusOp (record (pm_Branch l (Some T) r)).
    Proof.
      intros a b.
      dependent destruction a; dependent destruction b.
      constructor.
      { exact (a1 + b1). }
      { exact (y + y0). }
      { exact (a2 + b2). }
    Defined.

    Lemma simplify_plus_Branch_Some:
      forall (l1 l2 : record l) (v1 v2 : T) (r1 r2 : record r),
        pr_Branch (Some T) l1 v1 r1 + pr_Branch (Some T) l2 v2 r2 =
        pr_Branch (Some T) (l1 + l2) (v1 + v2) (r1 + r2).
    Proof.
      intros.
      reflexivity.
    Qed.

  End With_PlusOp.

  Section With_Plus.

    Context `{Plus (record l)} `{Plus T} `{Plus (record r)}.

    Global Instance Plus_Branch_Some : Plus (record (pm_Branch l (Some T) r)).
    Proof.
      constructor.
      {
        constructor.
        intros a b.
        dependent destruction a; dependent destruction b.
        do 2 rewrite simplify_plus_Branch_Some.
        f_equal; apply commutativity.
      }
      {
        constructor.
        intros a b c.
        dependent destruction a; dependent destruction b; dependent destruction c.
        do 4 rewrite simplify_plus_Branch_Some.
        f_equal; apply associativity.
      }
    Qed.

  End With_Plus.

End Branch_Some.

(*** Testing Plus ***)

Global Polymorphic Instance PlusOp_nat: PlusOp nat.
Proof. exact Nat.add. Defined.

Global Polymorphic Instance Plus_nat: Plus nat.
Proof.
  constructor.
  { constructor. exact PeanoNat.Nat.add_comm. }
  { constructor. exact PeanoNat.Nat.add_assoc. }
Qed.

Goal Plus (record pm_Leaf).
  auto with typeclass_instances.
Qed.

Goal Plus (record (pm_Branch pm_Leaf None pm_Leaf)).
  auto with typeclass_instances.
Qed.

Goal Plus (record (pm_Branch pm_Leaf (Some nat) pm_Leaf)).
  auto with typeclass_instances.
Qed.

Definition example :=
  record
    (fields_join
       (fields_singleton
          (String.String "x" String.EmptyString)
          nat)
       pm_Leaf).

Global Instance PlusOp_example : PlusOp example.
Proof.
  unfold example.
  simpl.
  auto 10 with typeclass_instances.
Defined.

Global Instance Plus_example : Plus example.
Proof.
  unfold example.
  simpl.
  (*
    For some reason this does not work:
  auto 100 with typeclass_instances.
   *)
  apply Plus_Branch_None.
  auto 10 with typeclass_instances.
  auto 10 with typeclass_instances.
Defined.

(*** Zero ***)

Delimit Scope zero with zero.
Open Scope zero.

Class RightNeutral {T : Type} (op : T -> T -> T) (n : T) :=
  { right_neutral: forall x, op x n = x; }.

Class ZeroOp (T : Type) := zero_op : T.
Notation "0" := (zero_op) : zero.

Class Zero (T : Type) `{Plus T} {Zero_ZeroOp : ZeroOp T} :=
  {
    Zero_RightNeutral :> RightNeutral plus_op 0;
  }.

(*** Zero Leaf ***)

Global Polymorphic Instance ZeroOp_Leaf : ZeroOp (record pm_Leaf).
Proof.
  unfold ZeroOp. exact pr_Leaf.
Defined.

Global Polymorphic Instance RightNeutral_Leaf : RightNeutral plus_op zero_op.
Proof.
  constructor.
  intro x.
  dependent destruction x.
  reflexivity.
Qed.

Global Polymorphic Instance Zero_Leaf : Zero (record pm_Leaf).
Proof. infer_instance. Qed.

Section Zero_Branch.

  Variables (l r : fields).

  Section ZeroOp_Branch_None.

    Context `{ZeroOp (record l)} `{ZeroOp (record r)}.

    Global Instance ZeroOp_Branch_None : ZeroOp (record (pm_Branch l None r)).
    Proof.
      unfold ZeroOp.
      constructor.
      exact zero_op.
      exact tt.
      exact zero_op.
    Defined.

    Lemma simplify_zero_Branch_None: 0 = pr_Branch None 0 tt 0.
    Proof. reflexivity. Qed.

  End ZeroOp_Branch_None.

  Section Zero_Branch_None.

    Context `{ZeroOp (record l)} `{ZeroOp (record r)}.
    Context `{Zero (record l)} `{Zero (record r)}.

    Global Instance Zero_Branch_None : Zero (record (pm_Branch l None r)).
    Proof.
      constructor.
      constructor.
      intro x.
      dependent destruction x.
      rewrite simplify_zero_Branch_None.
      rewrite simplify_plus_Branch_None.
      f_equal.
      apply right_neutral.
      now destruct y.
      apply right_neutral.
    Qed.

  End Zero_Branch_None.

  Section Some.

    Context `{T : Type}.

    Section ZeroOp_Branch_Some.

      Context `{ZeroOp (record l)} `{ZeroOp T} `{ZeroOp (record r)}.

      Global Instance ZeroOp_Branch_Some : ZeroOp (record (pm_Branch l (Some T) r)).
      Proof.
        unfold ZeroOp.
        constructor.
        exact zero_op.
        exact 0.
        exact zero_op.
      Defined.

      Lemma simplify_zero_Branch_Some : 0 = pr_Branch (Some T) 0 0 0.
      Proof. reflexivity. Qed.

    End ZeroOp_Branch_Some.

    Section Zero_Branch_Some.

      Context `{Zero (record l)} `{Zero T} `{Zero (record r)}.

      Global Instance Zero_Branch_Some : Zero (record (pm_Branch l (Some T) r)).
      Proof.
        constructor.
        constructor.
        intro x.
        dependent destruction x.
        rewrite simplify_zero_Branch_Some.
        rewrite simplify_plus_Branch_Some.
        f_equal.
        apply right_neutral.
        apply right_neutral.
        apply right_neutral.
      Qed.

    End Zero_Branch_Some.

  End Some.

End Zero_Branch.

(*** Opp ***)

Class OppOp (T : Type) := opp_op : T -> T.
Notation "- x" := (opp_op x).
Notation "a - b" := (a + (- b)).

Class Opp (T : Type) `{Zero T} {Opp_OppOp : OppOp T} :=
  {
    opp_spec : forall (x : T), x - x = 0;
  }.

(*** Opp Leaf ***)

Global Polymorphic Instance OppOp_Leaf : OppOp (record pm_Leaf).
Proof.
  unfold OppOp. intros _. exact pr_Leaf.
Defined.

Global Polymorphic Instance Opp_Leaf : Opp (record pm_Leaf).
Proof.
  constructor. intros x. reflexivity.
Qed.

Section Opp_Branch.

  Variables (l r : fields).

  Section OppOp_Branch_None.

    Context `{OppOp (record l)} `{OppOp (record r)}.

    Global Instance OppOp_Branch_None : OppOp (record (pm_Branch l None r)).
    Proof.
      intros x.
      dependent destruction x.
      constructor.
      exact (- x1).
      exact tt.
      exact (- x2).
    Defined.

    Lemma simplify_opp_Branch_None: forall a b v,
        - (pr_Branch None a v b) = pr_Branch None (- a) tt (- b).
    Proof.
      destruct v.
      reflexivity.
    Qed.

  End OppOp_Branch_None.

  Section Opp_Branch_None.

    Context `{OppOp (record l)} `{OppOp (record r)}.
    Context `{Opp (record l)} `{Opp (record r)}.

    Global Instance Opp_Branch_None : Opp (record (pm_Branch l None r)).
    Proof.
      constructor.
      intro x.
      dependent destruction x.
      rewrite simplify_opp_Branch_None.
      rewrite simplify_plus_Branch_None.
      rewrite simplify_zero_Branch_None.
      f_equal.
      apply opp_spec.
      apply opp_spec.
    Qed.

  End Opp_Branch_None.

  Section Some.

    Context `{T : Type}.

    Section OppOp_Branch_Some.

      Context `{OppOp (record l)} `{OppOp T} `{OppOp (record r)}.

      Global Instance OppOp_Branch_Some : OppOp (record (pm_Branch l (Some T) r)).
      Proof.
        unfold OppOp.
        intros x.
        dependent destruction x.
        constructor.
        exact (- x1).
        exact (- y).
        exact (- x2).
      Defined.

      Lemma simplify_opp_Branch_Some: forall a b v,
          - (pr_Branch (Some T) a v b) = pr_Branch (Some T) (- a) (- v) (- b).
      Proof.
        reflexivity.
      Qed.

    End OppOp_Branch_Some.

    Section Opp_Branch_Some.

      Context `{Opp (record l)} `{Opp T} `{Opp (record r)}.

      Global Instance Opp_Branch_Some : Opp (record (pm_Branch l (Some T) r)).
      Proof.
        constructor.
        intro x.
        dependent destruction x.
        rewrite simplify_opp_Branch_Some.
        rewrite simplify_plus_Branch_Some.
        rewrite simplify_zero_Branch_Some.
        f_equal.
        apply opp_spec.
        apply opp_spec.
        apply opp_spec.
      Qed.

    End Opp_Branch_Some.

  End Some.

End Opp_Branch.

Class AbelianGroup T :=
  {
    AbelianGroup_mixin :> AbelianGroup.mixin_of T
  }.

Global Instance AbelianGroupFromOpp T `{Opp T} : AbelianGroup T.
Proof.
  constructor.
  apply AbelianGroup.Mixin with
    (plus := plus_op)
    (opp := opp_op)
    (zero := 0%zero).
  { apply commutativity. }
  { apply associativity. }
  { apply right_neutral. }
  { apply opp_spec. }
Defined.
