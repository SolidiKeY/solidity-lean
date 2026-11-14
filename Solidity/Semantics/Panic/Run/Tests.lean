import Solidity.Semantics.Panic.Run.Control

namespace Solidity.Semantics.Panic.Tests

/-- A countdown terminates after three condition checks. -/
example : Loop.run (fun n : Nat => .ok (n - 1)) (fun n => .ok (n != 0)) 2 = .ok 0 :=
  Loop.run_of_iterN (n := 3) rfl

/-- A failing requirement inside an entered loop halts the entire loop. -/
example {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    Run.loop (.simple (.bool true)) .refl (Run.require (.simple (.bool false))) σ =
      .error .revert :=
  Loop.run_body_error _ _ _ .revert rfl rfl

/-- Assertion failure skips the following block and retains the assertion origin. -/
example {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    Run.seq (Run.assert (.simple (.bool false))) (Run.block .refl Run.nil) σ =
      .error (.intrinsic .assert (Raised.ofOrigin (.assertion false) .assertion rfl)) :=
  Run.seq_error _ _ σ _ (Run.assert_false _ σ rfl)

/-- A false condition never executes its failing branch. -/
example {C : Contract} {Γ : Ctx} (σ : State C Γ) :
    Run.ite (.simple (.bool false)) .refl (Run.assert (.simple (.bool false)))
      .refl Run.nil σ = .ok ⟨σ.drop .refl, List.prefix_refl _⟩ := rfl

/- External panic bytes select code 17 without being relabelled intrinsic. -/
#guard (match Run.catchHalt (.externalRevert (Semantics.encodePanic 17))
    (fun _ => .ok 99) (fun code => .ok code.val.toNat) (fun _ => .ok 88) with
  | .ok n => n == 17
  | .error _ => false)

/- Resource halts are not catchable and never expose revert bytes. -/
#guard (match Run.haltBytes .exhausted, Run.haltBytes .diverge with
  | .error .exhausted, .error .diverge => true
  | _, _ => false)

/- Exported proof contracts used by the remaining Run and binding checkpoints. -/
#check Loop.iterN_done_le
#check Loop.iterN_done_unique
#check Loop.run_induct
#check Loop.run_diverge
#check Loop.run_condition_error
#check args_erase
#check decode_erase
#check Run.call_error
#check Run.tryCall_self_failure
#check Run.catchBytes
#check Run.catchHalt_intrinsic
#check Run.catchHalt_exhausted
#check Run.catchHalt_diverge
#check Run.assert_eval_error
#check Run.producer_actual_code
#check Run.catch_assert_false

end Solidity.Semantics.Panic.Tests
