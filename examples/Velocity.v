Require Import Coq.Reals.Rdefinitions.
Require Import Coq.micromega.Psatz.
Require Import Coquelicot.Coquelicot.
Require Import ChargeCore.Tactics.Tactics.
Require Import Records.Records.
Require Import dL.Logics.
Require Import dL.dL.
Require Import dL.RecordsFacts.
Require Import Morphisms.
Require Import Program.
Local Transparent ILInsts.ILFun_Ops.

Local Open Scope R.
Local Open Scope string_scope.

(*Set Printing Universes.*)
Set Universe Polymorphism.

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

  Definition fields : fields@{Set} :=
    {@@ ("a" %e R)
     ,  ("v" %e R)
     ,  ("t" %e R)
     ,  ("y" %e R)
     @@}.

  Definition full_state := dL.state fields.

  Axiom cstate_class_of : NormedModule.class_of R_AbsRing full_state.
  Canonical continuous_state : NormedModule R_AbsRing :=
    NormedModule.Pack R_AbsRing full_state cstate_class_of full_state.
  Instance PInst : ProjState fields continuous_state.
    apply Build_ProjState with
      (to_cstate := fun s => s)
      (from_cstate := fun fs cs => cs).
    reflexivity.
  Defined.

  (* The safety property, i.e. the velocity is at most the
     upper bound. You have to write [get "v"] to access
     the current value of the velocity variable v. You also
     have to write [pure V] to express a constant. These are
     some of the many examples of how the syntax is very
     verbose in our embedding, but we hope to improve this
     in the future. *)
  Definition continuous_safe : StateProp continuous_state :=
    get "v" [<=] pure V.
  Definition safe : StateProp full_state :=
    proj_StateProp continuous_safe.

  (* The discrete controller sets the acceleration to some
     value that will be safe until the next execution. It
     also sets the timer to zero. *)
  Definition ctrl : ActionProp full_state :=
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

  Definition evolveL : FlowProp continuous_state :=
    d["v"] [=] #[get "a"] //\\
    d["a"] [=] pure 0 //\\
    d["t"] [=] pure 1.

  Definition evolveR : StateProp continuous_state :=
    get "t" [<=] pure d.

  Definition plant : ActionProp continuous_state :=
    evolveL & evolveR.

  Ltac break_record :=
    (* First, break all instances of record and remove unit types *)
    repeat
      match goal with
      | [ v : () |- _ ] => destruct v
      | [ r : record _ |- _ ] => dependent destruction r
      end;
    (* Then, clean all the record values that are not used in the goal *)
    repeat
      match goal with
      | [ r : R |- _ ] => try clear r
      end
  .

  (* Theorem expressing that the system does enforce
     the upper bound on velocity. The proof is fairly simple
     and can probably be mostly or completely automated, but
     for the moment, we manually apply proof rules. Proof
     rules are applied contextually by [rewrite] or directly
     by [apply]. *)
  Theorem bound_correct :
    |-- safe -->> [[(ctrl;; plant)^*]] safe.
  Proof.
    charge_intros.
    (* induction rule for the Kleene star *)
    rewrite <- star_I.
    charge_split.
    { charge_clear.
      apply G_rule.
      charge_intro.
      (* Cut-point: we need to prove that safe is preserved by one step *)
      unfold ctrl.
      repeat rewrite seq_rule.
      (* 1: non-deterministic assignment *)
      rewrite nondet_assign_rule.
      charge_intros.
      (* 2: test *)
      rewrite test_rule.
      rewrite assign_rule.
      rewrite Subst_limpl.
      charge_intro.
      set (EQ1 := get "v" [+] get "a" [*] pure d [<=] pure V).
      unfold plant, evolveL, evolveR.
      set (DV := d["v"] [=] #[get "a"]).
      set (DA := d["a"] [=] pure 0).
      set (DT := d["t"] [=] pure 1).
      set (dF := DV //\\ DA //\\ DT).
      set (I := get "t" [<=] pure d).
      assert (x <= 0 \/ 0 <= x) by psatzl R.
      destruct H.
      {
        (* ⟦dF & Q⟧ C ∧ ⟦dF & Q ∧ C⟧ P ⊢ ⟦dF & Q⟧ P *)
        rewrite <- differential_cut
        with (C := (get "a" [<=] pure 0) : StateProp continuous_state).
        repeat rewrite Subst_land.
        charge_split.
        {
          unfold I.
          rewrite <- differential_induction_leq
          with (e1' := d["a"] : FlowVal continuous_state R).
          {
            simpl.
            intros t.
            compute.
            unfold state in t.
            break_record.
            intuition.
          }
          {
            unfold D_state_val.
            unfold get.
            simpl.
            intros.
            unfold is_derive.
            simpl.
            unfold filterdiff.
            set (r := D t !! 353%positive).
            split.
            {
              constructor.
              {
                intros.
                unfold scal.
                simpl.
                apply mult_distr_r.
              }
              {
                intros.
                unfold scal.
                simpl.
                now rewrite -> mult_assoc.
              }
              {
                unfold scal.
                simpl.
                destruct H0 as [ [? ? [delta [? ?] ] ] ?].
                exists delta.
                split.
                { intuition. }
                {
                  unfold scal in H1. simpl in H1.
                  intros epsilon. specialize (H1 epsilon).
                  unfold norm in H1. simpl in H1.
                  unfold norm. simpl.
                  unfold NormedModule.norm in H1.
                  unfold NormedModule.mixin in H1.
                  admit. (* need to actually specify cstate_class_of... *)
                }
              }
            }
            {
              admit.
            }
          }
          { prove_derive. }
          {
            simpl.
            intros t0 t1.
            compute.
            unfold full_state, state in t0, t1.
            break_record. (* This takes forever... *)
            psatzl R.
          }
        }
        {
          unfold safe, continuous_safe.
          rewrite <- differential_induction_leq
          with (e1' := d["v"] : FlowVal continuous_state R).
          {
            admit.
          }
          { admit. }
          { prove_derive. }
          {
            simpl.
            intros t0 t1.
            compute.
            unfold full_state, state in t0, t1.
            break_record. (* This takes forever... *)
            psatzl R.
          }
        }
      }
      {
        rewrite <- differential_cut
        with (C := pure 0 [<=] get "a" : StateProp continuous_state).
        repeat rewrite box_land.
        repeat rewrite Subst_land.
        charge_split.
        {
          rewrite <- differential_induction_leq
          with (e2' := d["a"] : FlowVal continuous_state R).
          {
            breakAbstraction; intros; psatzl R.
          }
          { prove_derive. }
          { admit. }
          {
            breakAbstraction; intros; psatzl R.
          }
        }
        {
          rewrite <- differential_cut
          with (C := get "v" [+] get "a"[*] (pure d [-] get "t") [<=] pure V).
          repeat rewrite Subst_land.
          charge_split.
          { diff_ind.
            (* This goal requires non-linear arithmetic,
               so we use a foundational non-linear decision
               procedure. In the future, we will call better
               decision procedures such as Z3. *)
            breakAbstraction.
            intros.
            psatz R. }
          { rewrite <- differential_weakening'.
            charge_clear.
            do 2 rewrite <- Subst_ltrue.
            apply Proper_Subst_lentails; [ reflexivity | reflexivity | ].
            apply Proper_Subst_lentails; [ reflexivity | reflexivity | ].
            apply G_rule.
            breakAbstraction.
            intros.
            psatz R. } } } }
    { reflexivity. }
  Qed.



End VelocityBound.
