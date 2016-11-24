Require Import Coq.Reals.Rdefinitions.
Require Import Coq.micromega.Psatz.
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

  (* Debug attempt:
     Definition plant : ActionProp state :=
       (@mkFlowVal state R (fun _ st' => get "v" st')) [=] pure 0.
   *)

  Definition plant : ActionProp state :=
    d["v"] [=] #[get "a"] //\\
    d["a"] [=] pure 0 //\\
    d["t"] [=] pure 1 & get "t" [<=] pure d.

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