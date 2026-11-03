import Solidity.Backend.Passes.TripleControls

/-! A genuinely allocating middle stage consumes reached capacity above a
populated heap. The final capture reads the NEW object's selected address. -/
namespace Solidity.Backend.Passes.TripleAllocation
open Solidity.Evm Solidity.Evm.Compiler Solidity.Evm.Memory
open Solidity.Backend.Passes.Controls.Fixture
open Solidity.Backend.Passes.AllocatingControls
open Solidity.Backend.Passes.TripleControls
private abbrev A : RefTy := .array (.prim .uint)
private abbrev Ξ : Ctx := .mem A :: Γ
private def loc : OpLoc C Ξ .uint := .mindex .dyn (.var .here rfl) (.lit 0 rfl)
def captureNew : Prog C Ξ Ξ :=
  .cons (.assignIncDec (.there .here) .postInc rfl loc rfl) .nil
private def readNew : Val C Ξ .uint :=
  .readMem (.index .dyn (.var .here rfl) (.simple (.lit 0 rfl)))
def lastStage : CompiledProg 1 moreStage.frag captureNew :=
  (compileProg 1 moreStage.frag captureNew).get (by decide +kernel)

def sourceOutput : Solidity.Out C moreOutput.st.H Ξ :=
  match captureNew.run moreOutput.st with
  | .ok o => o
  | .error _ => ⟨moreOutput.st, List.prefix_refl _⟩

theorem source_success : captureNew.run moreOutput.st = .ok sourceOutput := by
  have h : (captureNew.run moreOutput.st).halt? = none := by decide +kernel
  unfold sourceOutput
  generalize he : captureNew.run moreOutput.st = res at *
  cases res with
  | ok o => rfl
  | error e => cases h

/-- Actual intrinsic observation through the new reference after its capture.
The captured old zero and observed new one are distinct. -/
theorem source_observation : readNew.evalT sourceOutput.st = .ok ⟨1, rfl⟩ ∧
    TEnv.get (.there .here) sourceOutput.st.env = ⟨0, rfl⟩ := by
  constructor <;> with_unfolding_all rfl

/-- The combined entry capacity is7cells:5for the real builder and2for
the reached one-element allocation. It is transported by nextInput. -/
theorem allocating_link : MappedBoundaryLink (.memory allocationStage) (.memory moreStage)
    1 7 initialBase (State.init C) initialMachine := by
  apply memory_budgeted_mapped_link
  · decide +kernel
  · intro o hs
    have ho : o = ⟨σ, ⟨σ.H, rfl⟩⟩ :=
      Except.ok.inj (hs.symm.trans ReachabilityControls.fresh_state_reaches_fixture)
    cases ho
    exact .inr ⟨by decide, ⟨16, by decide⟩, initial_repr7.2, by decide +kernel⟩

theorem capture_link : ReachedMappedLink (.memory allocationStage) (.memory moreStage)
    (.memory lastStage) 1 7 initialBase (State.init C) initialMachine := by
  intro o mid mb _ _ _
  exact memory_nonallocating_mapped_link _ _ (by decide +kernel) (by decide +kernel)

/-- Old identities across BOTH boundaries and total reached7cell growth.
The map at the allocating middle output, not the initial map, represents
and is consumed by the capture of the new array. -/
theorem resources :
    ∃ (mb nb ob : Nat → Fin W) (mid next final : Machine),
      run (allocationStage.code ++ moreStage.code ++ lastStage.code) initialMachine = .ok final 0 ∧
      MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
        initialMachine σ mid mb ∧
      MappedOutput (.memory moreStage) 1 7 mb σ mid moreOutput.st next nb ∧
      MappedOutput (.memory lastStage) 1 7 nb moreOutput.st next sourceOutput.st final ob ∧
      nb CompileExamples.r0.id = mb CompileExamples.r0.id ∧
      nb CompileExamples.r1.id = mb CompileExamples.r1.id ∧
      BaseExtends moreOutput.st.H nb ob ∧
      BaseExtends σ.H mb ob ∧
      GrowsAllocator 1 7 7 (State.init C) initialBase initialMachine sourceOutput.st ob final := by
  obtain ⟨mb, nb, ob, mid, next, final, _, ht, _, ma, md, me, _, hb, hg⟩ :=
    memory_triple_resources allocationStage moreStage lastStage prefix_input7
      allocating_link capture_link ReachabilityControls.fresh_state_reaches_fixture more_source source_success
  have ma' : MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
      initialMachine σ mid mb := by
    simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using ma
  have md' : MappedOutput (.memory moreStage) 1 7 mb σ mid moreOutput.st next nb := by
    simpa only [allocationStage.cert.pushes_zero, moreStage.cert.pushes_zero, Nat.add_zero] using md
  have me' : MappedOutput (.memory lastStage) 1 7 nb moreOutput.st next sourceOutput.st final ob := by
    simpa only [allocationStage.cert.pushes_zero, moreStage.cert.pushes_zero,
      lastStage.cert.pushes_zero, Nat.add_zero] using me
  have hc : moreStage.cert.cost σ = 2 := by decide +kernel
  have hz : lastStage.cert.cost moreOutput.st = 0 := by decide +kernel
  exact ⟨mb, nb, ob, mid, next, final, ht, ma', md', me',
    md'.2.1 CompileExamples.r0, md'.2.1 CompileExamples.r1, me'.2.1, hb,
    by simpa only [reached_cost, hc, hz, Nat.add_zero, Nat.reduceAdd] using hg⟩

/-- All three machines/maps precede forall tail even when the middle allocates. -/
def shared := compilation_triple_shared (.memory allocationStage) (.memory moreStage)
  (.memory lastStage) prefix_input7 rfl allocating_link capture_link rfl rfl rfl
  ReachabilityControls.fresh_state_reaches_fixture more_source source_success

private def code := allocationStage.code ++ moreStage.code ++ lastStage.code
private def cell (n : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem n with | .val w => some w.val | _ => none
  | _ => none
private theorem saved : cell 4 (run code initialMachine) = some 0 := by decide +kernel
private theorem freshRef : cell 5 (run code initialMachine) = some 21 := by decide +kernel
private theorem freshValue : cell 22 (run code initialMachine) = some 1 := by decide +kernel
private theorem old1 : cell 2 (run code initialMachine) = some 16 := by decide +kernel
private theorem old2 : cell 3 (run code initialMachine) = some 16 := by decide +kernel
private theorem other : cell 1 (run code initialMachine) = some 19 := by decide +kernel
private theorem oldValue : cell 17 (run code initialMachine) = some 7 := by decide +kernel
private theorem otherValue : cell 20 (run code initialMachine) = some 4 := by decide +kernel
private theorem cursor : cell 0 (run code initialMachine) = some 23 := by decide +kernel

theorem ordered_results : [4, 5, 22, 2, 3, 1, 17, 20, 0].mapM
    (fun n => cell n (run code initialMachine)) = some [0, 21, 1, 16, 16, 19, 7, 4, 23] := by
  simp only [List.mapM_cons, List.mapM_nil, saved, freshRef, freshValue, old1, old2,
    other, oldValue, otherValue, cursor]
  rfl

/-- A stale prefix map may happen to guess an unused address correctly;
no universal impossibility is claimed. A map with its fresh id still at zero
cannot represent the new object, even though its old ids can remain valid. -/
theorem stale_new (oldBase : Nat → Fin W) (hz : oldBase 2 = ⟨0, W_pos⟩)
    (m : Machine) : ¬ StateRepr 1 1 7 moreStage.frag moreOutput.st oldBase m := by
  intro h
  have bad := h.heap.above (p := .uint) ⟨2, by decide +kernel⟩
  change 7 ≤ (oldBase 2).val at bad
  rw [hz] at bad
  contradiction

/-- The newly allocated object cannot be consumed using the stale entry map:
its heap would violate frame separation, independently of target contents. -/
theorem stale_initial (m : Machine) :
    ¬ StateRepr 1 1 7 moreStage.frag moreOutput.st initialBase m := by
  intro h
  have bad := h.heap.above (CompileExamples.r0.wk moreOutput.ext)
  change 7 ≤ 0 at bad
  omega

end Solidity.Backend.Passes.TripleAllocation
