import Solidity.Backend.Passes.MappedSequence
import Solidity.Backend.Passes.ReachabilityControls

/-! An allocating allocationStage reaches the populated fixture; its selected map is
consumed by a nonallocating read/write suffix. Both source and target are
existing intrinsic objects. This does not claim independent Source lowering. -/
namespace Solidity.Backend.Passes.AllocatingControls
open Solidity.Evm Solidity.Evm.Compiler Solidity.Evm.Memory
open Solidity.Backend.Passes.Controls
open Solidity.Backend.Passes.Controls.Fixture

def initialBase : Nat → Fin W := fun _ => ⟨0, W_pos⟩
def initialMachine : Machine :=
  { Machine.init with mem := fun a => if a = 0 then w[16] else w[0] }

theorem initial_repr :
    StateRepr 1 1 6 (Frag.init []) (State.init C) initialBase initialMachine ∧
    StructAllocatorRepr (State.init C).heap initialBase 6 ⟨16, by decide⟩ initialMachine := by
  have hn {R : RefTy} (r : HRef [] R) : False := by
    simpa only [List.getElem?_nil, reduceCtorEq] using r.get?
  have hh : HeapRepr (State.init C).heap initialBase 6 initialMachine :=
    ⟨fun r => (hn r).elim, fun r => (hn r).elim, fun r _ _ => (hn r).elim⟩
  constructor
  · refine ⟨?_, hh, (fun i => nomatch i), by decide,
      ⟨fun r => (hn r).elim, fun r => (hn r).elim, fun r => (hn r).elim⟩,
      (fun _ r => (hn r).elim), RefFieldsRepr.withoutStructs _ _ _ (fun r => hn r)⟩
    have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0, W_pos⟩ rfl
    exact ⟨hc.store, (fun i => nomatch i), (fun i _ => nomatch i),
      hc.net, hc.netSelf, hc.bound, (fun i _ => nomatch i), hc.env, hc.funds, hc.oracle⟩
  · refine AllocatorRepr.withoutStructs ?_ (fun r => hn r)
    refine ⟨hh, ⟨by decide, by decide, rfl, ?_⟩, fun r => (hn r).elim⟩
    intro addr ha
    change 16 ≤ addr at ha
    simp only [initialMachine]
    split <;> rename_i he
    · omega
    · rfl

def allocationStage : CompiledProg 1 (Frag.init []) ReachabilityControls.populatedBuilder :=
  (compileProg 1 (Frag.init []) ReachabilityControls.populatedBuilder).get (by decide +kernel)
def suffix : CompiledProg 1 allocationStage.frag writeAndRead :=
  (compileProg 1 allocationStage.frag writeAndRead).get (by decide +kernel)

theorem reached_cost : allocationStage.cert.cost (State.init C) = 5 := by decide +kernel

theorem prefix_input : (Compilation.memory allocationStage).Input 1 6 initialBase
    (State.init C) initialMachine := by
  refine ⟨initial_repr.1, by decide +kernel, .inr ⟨by decide, ⟨16, by decide⟩, initial_repr.2, ?_⟩⟩
  rw [reached_cost]
  decide

theorem actual_link : MappedBoundaryLink (.memory allocationStage) (.memory suffix)
    1 6 initialBase (State.init C) initialMachine :=
  memory_nonallocating_mapped_link allocationStage suffix (by decide +kernel) (by decide +kernel)

/-- An inhabited allocating composition with the same selected intermediate
map, exact five-cell growth, both full representations, and preserved tail. -/
theorem allocating_composition :
    ∃ midBase outBase mid final,
      run (allocationStage.code ++ suffix.code) initialMachine = .ok final 0 ∧
      final.stack = initialMachine.stack ∧
      MappedOutput (.memory allocationStage) 1 6 initialBase (State.init C)
        initialMachine σ mid midBase ∧
      MappedOutput (.memory suffix) 1 6 midBase σ mid sourceOutput.st final outBase ∧
      BaseExtends (State.init C).H initialBase outBase ∧
      GrowsAllocator 1 6 5 (State.init C) initialBase initialMachine
        sourceOutput.st outBase final := by
  obtain ⟨mb, ob, mid, final, _, ht, hstack, hleft, hright, he, hg⟩ :=
    memory_sequence_resources allocationStage suffix prefix_input actual_link
      ReachabilityControls.fresh_state_reaches_fixture source_success
  refine ⟨mb, ob, mid, final, ht, hstack, ?_, ?_, he, ?_⟩
  · simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using hleft
  · simpa only [allocationStage.cert.pushes_zero, suffix.cert.pushes_zero, Nat.add_zero] using hright
  · have hz : suffix.cert.cost σ = 0 := by decide +kernel
    simpa only [reached_cost, hz, Nat.add_zero] using hg

/-- The original all-zero map cannot represent the newly allocated heap;
forgetting map correlation would lose an essential premise. -/
theorem stale_map_impossible (m : Machine) :
    ¬ StateRepr 1 1 6 allocationStage.frag σ initialBase m := by
  intro h
  have bad := h.heap.above CompileExamples.r0
  change 6 ≤ 0 at bad
  omega

/-- A real target bootstrap, with no assumed preallocated source object. -/
theorem target_bootstrap :
    run [.push w[16], .mstore 0] Machine.init = .ok initialMachine 0 := by rfl

private def cellValue (a : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem a with | .val w => some w.val | _ => none
  | _ => none

theorem actual_result :
    cellValue 0 (run (allocationStage.code ++ suffix.code) initialMachine) = some 21 ∧
    cellValue 4 (run (allocationStage.code ++ suffix.code) initialMachine) = some 5 := by
  constructor <;> decide +kernel

def badSuffix : CompiledProg 1 allocationStage.frag CompileExamples.badRhsRead :=
  (compileProg 1 allocationStage.frag CompileExamples.badRhsRead).get (by decide +kernel)

theorem reached_failure :
    run (allocationStage.code ++ badSuffix.code) initialMachine = .revert := by
  obtain ⟨mb, mid, ht, _, hr⟩ :=
    memory_mapped_success allocationStage prefix_input ReachabilityControls.fresh_state_reaches_fixture
  have hi := memory_nonallocating_mapped_link allocationStage badSuffix
    (L := 1) (frame := 6) (base := initialBase) (σ := State.init C) (m := initialMachine)
    (by decide +kernel) (by decide +kernel)
    _ _ _ ReachabilityControls.fresh_state_reaches_fixture ht hr
  rw [run_append_ok ht]
  rcases badSuffix.cert.correct hi.1 hi.2.1 hi.2.2 with
    ⟨o, _, _, hs, _, _, _, _, _⟩ | ⟨_, ht'⟩
  · rw [LinkedControls.right_stage_source_revert] at hs
    cases hs
  · exact ht'


private abbrev A : RefTy := .array (.prim .uint)
def allocateMore : Prog C Γ (.mem A :: Γ) :=
  .cons (.declMem A (.user "more") (some (.newArr (.lit 1 rfl) rfl)) rfl rfl) .nil
def moreOutput : Solidity.Out C σ.H (.mem A :: Γ) :=
  ⟨σ.allocPush (defaultArray .uint ⟨1, by decide⟩), ⟨[A], rfl⟩⟩
theorem more_source : allocateMore.run σ = .ok moreOutput := by
  with_unfolding_all rfl
def moreStage : CompiledProg 1 allocationStage.frag allocateMore :=
  (compileProg 1 allocationStage.frag allocateMore).get (by decide +kernel)

theorem more_link : MappedBoundaryLink (.memory allocationStage) (.memory moreStage)
    1 6 initialBase (State.init C) initialMachine := by
  apply memory_budgeted_mapped_link
  · decide +kernel
  · intro o hs
    have ho : o = ⟨σ, ⟨σ.H, rfl⟩⟩ :=
      Except.ok.inj (hs.symm.trans ReachabilityControls.fresh_state_reaches_fixture)
    cases ho
    exact .inr ⟨by decide, ⟨16, by decide⟩, initial_repr.2, by decide +kernel⟩

/-- The second stage allocates above a genuinely populated heap. Its
old-reference identity clause now ranges over both existing arrays. -/
theorem populated_allocation :
    ∃ midBase outBase mid final,
      run (allocationStage.code ++ moreStage.code) initialMachine = .ok final 0 ∧
      MappedOutput (.memory allocationStage) 1 6 initialBase (State.init C)
        initialMachine σ mid midBase ∧
      MappedOutput (.memory moreStage) 1 6 midBase σ mid moreOutput.st final outBase ∧
      outBase CompileExamples.r0.id = midBase CompileExamples.r0.id ∧
      outBase CompileExamples.r1.id = midBase CompileExamples.r1.id := by
  obtain ⟨mb, ob, mid, final, _, ht, _, hl, hr, _, _⟩ :=
    memory_sequence_resources allocationStage moreStage prefix_input more_link
      ReachabilityControls.fresh_state_reaches_fixture more_source
  have hr' : MappedOutput (.memory moreStage) 1 6 mb σ mid moreOutput.st final ob := by
    simpa only [allocationStage.cert.pushes_zero, moreStage.cert.pushes_zero, Nat.add_zero] using hr
  exact ⟨mb, ob, mid, final, ht,
    by simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using hl,
    hr', hr'.2.1 CompileExamples.r0, hr'.2.1 CompileExamples.r1⟩

theorem populated_allocation_cursor :
    cellValue 0 (run (allocationStage.code ++ moreStage.code) initialMachine) = some 23 := by
  decide +kernel

end Solidity.Backend.Passes.AllocatingControls
