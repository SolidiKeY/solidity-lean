import Solidity.Backend.Passes.TripleAllocation

/-! Inhabitation of the generic third-stage reached allocation budget:
allocation, nonallocating capture effect, then a real second allocation. -/
namespace Solidity.Backend.Passes.TripleSuffix
open Solidity.Evm Solidity.Evm.Compiler Solidity.Evm.Memory
open Solidity.Backend.Passes.Controls.Fixture
open Solidity.Backend.Passes.AllocatingControls
open Solidity.Backend.Passes.TripleControls
private abbrev A : RefTy := .array (.prim .uint)
def lastStage : CompiledProg 1 captureStage.frag allocateMore :=
  (compileProg 1 captureStage.frag allocateMore).get (by decide +kernel)
def finalSource : Solidity.Out C CaptureControls.afterCapture.H (.mem A :: Γ) :=
  ⟨CaptureControls.afterCapture.allocPush (defaultArray .uint ⟨1, by decide⟩), ⟨[A], rfl⟩⟩
theorem last_source : allocateMore.run CaptureControls.afterCapture = .ok finalSource := by
  with_unfolding_all rfl

/-- Derived through the reusable3stage budget helper, not an assumed Input
at a guessed intermediate map. Both source successes identify reached costs. -/
theorem last_link : ReachedMappedLink (.memory allocationStage) (.memory captureStage)
    (.memory lastStage) 1 7 initialBase (State.init C) initialMachine := by
  apply memory_third_budgeted_link
  · decide +kernel
  · intro o u hs hu
    have ho : o = ⟨σ, ⟨σ.H, rfl⟩⟩ :=
      Except.ok.inj (hs.symm.trans ReachabilityControls.fresh_state_reaches_fixture)
    cases ho
    have hu' : u = ⟨CaptureControls.afterCapture, List.prefix_refl _⟩ :=
      Except.ok.inj (hu.symm.trans capture_source)
    cases hu'
    exact .inr ⟨by decide, ⟨16, by decide⟩, initial_repr7.2, by decide +kernel⟩

/-- Actual triple resource theorem with a positive-cost suffix. -/
theorem resources : ∃ (mb nb ob : Nat → Fin W) (mid next final : Machine),
    run (allocationStage.code ++ captureStage.code ++ lastStage.code) initialMachine = .ok final 0 ∧
    MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C) initialMachine σ mid mb ∧
    MappedOutput (.memory captureStage) 1 7 mb σ mid CaptureControls.afterCapture next nb ∧
    MappedOutput (.memory lastStage) 1 7 nb CaptureControls.afterCapture next finalSource.st final ob ∧
    BaseExtends σ.H mb ob ∧
    GrowsAllocator 1 7 7 (State.init C) initialBase initialMachine finalSource.st ob final := by
  obtain ⟨mb, nb, ob, mid, next, final, _, ht, _, ma, md, me, _, hb, hg⟩ :=
    memory_triple_resources allocationStage captureStage lastStage prefix_input7 first_link last_link
      ReachabilityControls.fresh_state_reaches_fixture capture_source last_source
  have hc : captureStage.cert.cost σ = 0 := by decide +kernel
  have hz : lastStage.cert.cost CaptureControls.afterCapture = 2 := by decide +kernel
  refine ⟨mb, nb, ob, mid, next, final, ht, ?_, ?_, ?_, hb, ?_⟩
  · simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using ma
  · simpa only [allocationStage.cert.pushes_zero, captureStage.cert.pushes_zero, Nat.add_zero] using md
  · simpa only [allocationStage.cert.pushes_zero, captureStage.cert.pushes_zero,
      lastStage.cert.pushes_zero, Nat.add_zero] using me
  · simpa only [reached_cost, hc, hz, Nat.zero_add, Nat.reduceAdd] using hg

def shared := compilation_triple_shared (.memory allocationStage) (.memory captureStage)
  (.memory lastStage) prefix_input7 rfl first_link last_link rfl rfl rfl
  ReachabilityControls.fresh_state_reaches_fixture capture_source last_source

private def code := allocationStage.code ++ captureStage.code ++ lastStage.code
private def cell (n : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem n with | .val w => some w.val | _ => none
  | _ => none
private theorem saved : cell 4 (run code initialMachine) = some 7 := by decide +kernel
private theorem newRef : cell 5 (run code initialMachine) = some 21 := by decide +kernel
private theorem newValue : cell 22 (run code initialMachine) = some 0 := by decide +kernel
private theorem oldValue : cell 17 (run code initialMachine) = some 8 := by decide +kernel
private theorem alias1 : cell 2 (run code initialMachine) = some 16 := by decide +kernel
private theorem alias2 : cell 3 (run code initialMachine) = some 16 := by decide +kernel
private theorem other : cell 1 (run code initialMachine) = some 19 := by decide +kernel
private theorem otherValue : cell 20 (run code initialMachine) = some 4 := by decide +kernel
private theorem cursor : cell 0 (run code initialMachine) = some 23 := by decide +kernel

theorem ordered_results : [4, 5, 22, 17, 2, 3, 1, 20, 0].mapM
    (fun n => cell n (run code initialMachine)) = some [7, 21, 0, 8, 16, 16, 19, 4, 23] := by
  simp only [List.mapM_cons, List.mapM_nil, saved, newRef, newValue, oldValue,
    alias1, alias2, other, otherValue, cursor]
  rfl
end Solidity.Backend.Passes.TripleSuffix
