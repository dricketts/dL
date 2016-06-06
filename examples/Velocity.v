Require Import Coq.Reals.Rdefinitions.
Require Import Coq.micromega.Psatz.
Require Import ChargeCore.Tactics.Tactics.
Require Import dL.Logics.
Require Import dL.dL.
Local Transparent ILInsts.ILFun_Ops.

Local Open Scope R.
Local Open Scope string_scope.

(**
 ** Here's a simple example of using dL.
 ** The following system enforces an upper bound
 ** on velocity by controlling acceleration.
 **)
Section VelocityBound.

  (* The upper bound on velocity. *)
  Variable V : R.
  (* Upper bound on the time between executions of
     the discrete controller. *)
  Variable d : R.

  (* The safety property, i.e. the velocity is at most the
     upper bound. *)
  Definition safe : StateProp :=
    get "v" [<=] pure V.

  (* The discrete controller sets the acceleration to some
     value that will be safe until the next execution. It
     also sets the timer to zero. *)
  Definition ctrl : ActionProp :=
    "a" ::= ***;;
     ? get "v" [+] get "a"[*]pure d [<=] pure V;;
    "t" ::= pure 0.

  (* The physical dynamics of the system. This formulation
     differs slightly from dL in that we explicitly set
     derivatives to zero. *)
  Definition plant : ActionProp :=
    d["v"] [=] #[get "a"] //\\
    d["a"] [=] pure 0 //\\
    d["t"] [=] pure 1 & get "t" [<=] pure d.

  (* Theorem expressing that the system does enforce
     the upper bound on velocity. *)
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