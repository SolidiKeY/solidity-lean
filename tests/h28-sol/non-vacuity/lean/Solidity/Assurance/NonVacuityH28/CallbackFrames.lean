import Solidity.Assurance.NonVacuityH28.Callbacks

/-! Every callback-frame constructor on actual typed states.
Sequence cases execute the nonempty payment program; pop/drop discard actual
primitive locals before it. A violated frame is never a true postcondition. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics
variable (C : Contract)

theorem callback_nil_frame :
    ExecF (openPolicy C true) (funded C) .nil
      (.ok ⟨funded C, List.prefix_refl _⟩) := .nil

theorem callback_seq_frame :
    ExecF (openPolicy C true) (funded C) (.seq (callbackProgram C) .nil)
      (.ok ⟨resumed C, List.prefix_refl _⟩) :=
  .seq (callback_program_resume C) .nil

theorem callback_halt_frame :
    ExecF (openPolicy C true) (State.init C) (.seq (callbackProgram C) .nil) (.halt .revert) :=
  .seqHalt (callback_program_revert C)

theorem callback_violated_frame :
    (paymentInvariant C).at (funded C) ∧
    ExecF (paymentInvariant C) (funded C) (.seq (callbackProgram C) .nil) .violated :=
  ⟨(callback_program_violation C).1, .seqViolated (callback_program_violation C).2⟩

theorem callback_pop_frame :
    ExecF (openPolicy C true) ((funded C).push (t := .val .bool) true)
      (.pop .block (.push .refl) (.seq (callbackProgram C) .nil))
      (.ok ⟨resumed C, List.prefix_refl _⟩) :=
  .pop (callback_seq_frame C)

theorem callback_drop_frame :
    ExecF (openPolicy C true)
      (((funded C).push (t := .val .uint) (⟨7, rfl⟩ : PrimTy.uint.Denote)).push (t := .val .bool) true)
      (.drop (.drop .refl) (.pop .capture (.push .refl) (.seq (callbackProgram C) .nil)))
      (.ok ⟨resumed C, List.prefix_refl _⟩) :=
  .drop (.pop (callback_seq_frame C))

/-- The frame sequence really admits a changed callback ledger. -/
theorem callback_frame_observation :
    ExecF (openPolicy C true) (funded C) (.seq (callbackProgram C) .nil)
      (.ok ⟨resumed C, List.prefix_refl _⟩) ∧
      (lookupBy (⟨9, rfl⟩ : PrimTy.uint.Denote) (resumed C).net).getD 0 = -7 :=
  ⟨callback_seq_frame C, rfl⟩

end Solidity.Assurance.NonVacuityH28
