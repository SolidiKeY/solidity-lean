import Solidity.Backend.TryCall.PanicEmitter
import Solidity.Evm.Correct

/-! Represented positive and negative entries for the SAME checked emitter.
These are core-model nonvacuity witnesses, not an original deployment profile,
account installation fact or a compiled-solc execution. -/
namespace Solidity.Backend.TryCall.PanicControls
open Evm Evm.Memory
open PanicEmitter

def C : Contract := contract!{}
abbrev F := Frag.init Γ

def initial (self : Fin W) : State C Γ :=
  (freshT C 0 W_pos self).withEnv (uintT 0 W_pos, ())
def machine (self : Fin W) : Machine :=
  { Machine.init (fun _ => 0) self with mem := fun a => if a = 2 then w[4] else w[0] }
def bases (_ : Nat) : Fin W := ⟨0,W_pos⟩

private theorem noRef {R : RefTy} (r : HRef [] R) : False := by
  rcases r with ⟨id,bound⟩
  cases id <;> cases bound

theorem represented (self : Fin W) :
    StateRepr 1 0 8 F (initial self) bases (machine self) := by
  have fresh := Sim.init C 0 W_pos (fun _ => 0) self rfl
  constructor
  · refine ⟨fresh.store, ?_, ?_, fresh.net, fresh.netSelf, fresh.bound, ?_,
      fresh.env, fresh.funds, fresh.oracle⟩
    · intro p i
      cases i with
      | here => exact ⟨⟨0,W_pos⟩,rfl,rfl⟩
      | there i => nomatch i
    · intro R i
      cases i with | there i => nomatch i
    · intro R i
      cases i with | there i => nomatch i
  · exact ⟨fun r => (noRef r).elim,fun r => (noRef r).elim,fun r => (noRef r).elim⟩
  · intro R i
    cases i with | there i => nomatch i
  · decide
  · exact ⟨fun r => (noRef r).elim,fun r => (noRef r).elim,fun r => (noRef r).elim⟩
  · exact fun a r => (noRef a).elim
  · exact RefFieldsRepr.withoutStructs _ _ _ noRef

theorem entry (self : Fin W) :
    RF.Entry (plan 0 2 2 F) 1 0 8 F (initial self) bases (machine self) 4 where
  represented := represented self
  callerBound := by decide
  resultBound := by decide
  workspace := by decide
  pointerAbove := by decide
  pointerBelow := by decide
  payloadAbove := by decide
  reserve := by change 4 + 2 ≤ 8; decide
  controlSpace := by change 2 ≤ 2; decide
  separate := by change 2 < 4 ∨ 4 + 2 ≤ 2; decide
  noWrap := by change 4 + 2 < W; decide
  cursor := rfl
  capacity := .inl ((checked 0 F).checked.zeroCost rfl (initial self))

theorem successful : InternalFlow.RuntimeFrame.InterfaceV2.SuccessfulEntry
    0 F site.statement (plan (C := C) 0 2 2 F) := by
  refine ⟨1,8,initial ⟨1,by decide⟩,bases,machine ⟨1,by decide⟩,4,
    ⟨(initial ⟨1,by decide⟩).setLocal .here Evm.TryPanicProducer.codeWord,List.prefix_refl _⟩,
    entry _,?_⟩
  exact PanicNormalization.nonzero _
    ⟨0,0,.legacy,105,⟨1,rfl⟩,⟨0,rfl⟩,⟨0,rfl⟩⟩ (by decide)

theorem reverting : InternalFlow.RuntimeFrame.InterfaceV2.RevertingEntry
    0 F site.statement (plan (C := C) 0 2 2 F) := by
  refine ⟨1,8,initial ⟨0,W_pos⟩,bases,machine ⟨0,W_pos⟩,4,entry _,?_⟩
  exact PanicNormalization.zero _ rfl

/-- A fully inhabited checked producer, with two real represented outcomes. -/
def producer : Producer 0 F (site (C := C)) where
  plan := plan 0 2 2 F
  returns := returns 0 2 2 F
  reverts := reverts 0 2 2 F
  successful := successful
  reverting := reverting

/-- The positive entry executes the actual emitted code and preserves its frame. -/
theorem positive_target : RF.Returned (plan 0 2 2 F) 1 0 8
    (initial ⟨1,by decide⟩) bases (machine ⟨1,by decide⟩) 4
    ⟨(initial ⟨1,by decide⟩).setLocal .here Evm.TryPanicProducer.codeWord,List.prefix_refl _⟩ := by
  apply returns 0 2 2 F 1 8 _ bases _ 4 (entry _)
  exact PanicNormalization.nonzero _
    ⟨0,0,.legacy,105,⟨1,rfl⟩,⟨0,rfl⟩,⟨0,rfl⟩⟩ (by decide)

/-- Zero-receiver bare revert is transported to a real target REVERT. -/
theorem negative_target : Evm.run (plan (C := C) 0 2 2 F).code
    (machine ⟨0,W_pos⟩) = .revert :=
  reverts 0 2 2 F 1 8 _ bases _ 4 (entry _) (PanicNormalization.zero _ rfl)

/-- A source-success entry cannot be relabelled a target revert. -/
theorem positive_not_revert : Evm.run (plan (C := C) 0 2 2 F).code
    (machine ⟨1,by decide⟩) ≠ .revert := by
  obtain ⟨target,addresses,actual,rest⟩ := positive_target
  intro wrong
  rw [wrong] at actual
  cases actual

end Solidity.Backend.TryCall.PanicControls
