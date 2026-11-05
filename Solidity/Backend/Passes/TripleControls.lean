import Solidity.Backend.Passes.TripleSequence
import Solidity.Backend.Passes.AllocatingCapture

/-! Three real compiler stages: allocate a populated heap, capture an old
primitive while mutating through an alias, then create/read a reference local.
Every physical boundary is independently inhabited. -/
namespace Solidity.Backend.Passes.TripleControls
open Solidity.Evm Solidity.Evm.Compiler Solidity.Evm.Memory
open Solidity.Backend.Passes.Controls.Fixture
open Solidity.Backend.Passes.AllocatingControls

theorem initial_repr7 :
    StateRepr 1 1 7 (Frag.init []) (State.init C) initialBase initialMachine ∧
    StructAllocatorRepr (State.init C).heap initialBase 7 ⟨16, by decide⟩ initialMachine := by
  have hn {R : RefTy} (r : HRef [] R) : False := by
    simpa only [List.getElem?_nil, reduceCtorEq] using r.get?
  have hh : HeapRepr (State.init C).heap initialBase 7 initialMachine :=
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

theorem prefix_input7 : (Compilation.memory allocationStage).Input 1 7 initialBase
    (State.init C) initialMachine := by
  refine ⟨initial_repr7.1, by decide +kernel, .inr ⟨by decide, ⟨16, by decide⟩, initial_repr7.2, ?_⟩⟩
  rw [reached_cost]
  decide

def captureProg : Prog C Γ Γ := .cons CaptureControls.capture .nil
def observeProg : Prog C Γ (.val .uint :: .mem (.array (.prim .uint)) :: Γ) :=
  .cons CaptureControls.aliasStmt (.cons CaptureControls.valueStmt .nil)
def captureStage : CompiledProg 1 allocationStage.frag captureProg :=
  (compileProg 1 allocationStage.frag captureProg).get (by decide +kernel)
def observeStage : CompiledProg 1 captureStage.frag observeProg :=
  (compileProg 1 captureStage.frag observeProg).get (by decide +kernel)

theorem capture_source : captureProg.run σ =
    .ok ⟨CaptureControls.afterCapture, List.prefix_refl _⟩ := by
  rw [captureProg, Prog.run_cons_ok CaptureControls.source_capture, Prog.run_nil]
  rfl

theorem observe_source : observeProg.run CaptureControls.afterCapture =
    .ok ⟨CaptureControls.afterValue, List.prefix_refl _⟩ := by
  with_unfolding_all rfl

theorem first_link : MappedBoundaryLink (.memory allocationStage) (.memory captureStage)
    1 7 initialBase (State.init C) initialMachine :=
  memory_nonallocating_mapped_link allocationStage captureStage (by decide +kernel) (by decide +kernel)

theorem second_link : ReachedMappedLink (.memory allocationStage) (.memory captureStage)
    (.memory observeStage) 1 7 initialBase (State.init C) initialMachine := by
  intro o mid mb _ _ _
  exact memory_nonallocating_mapped_link captureStage observeStage
    (by decide +kernel) (by decide +kernel)

/-- Fresh source success under both associations, independently evaluated
at each actual intrinsic state. -/
theorem fresh_source :
    ((ReachabilityControls.populatedBuilder.join captureProg).join observeProg).run (State.init C) =
      .ok ⟨CaptureControls.afterValue, ⟨σ.H, rfl⟩⟩ :=
  (triple_source_success (State.init C)
    ReachabilityControls.fresh_state_reaches_fixture capture_source observe_source).1

/-- Three fixed maps, three actual outputs, both associations and complete
relations for arbitrary saved tails. Growth and old-reference identities are
derived from those very same selected maps, not stale initial addresses. -/
theorem shared_resources :
    ∃ (mb nb ob : Nat → Fin W) (mid next final : Machine),
      ∀ tail,
      run allocationStage.code {initialMachine with stack := tail} = .ok {mid with stack := tail} 0 ∧
      run captureStage.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
      run observeStage.code {next with stack := tail} = .ok {final with stack := tail} 0 ∧
      run ((allocationStage.code ++ captureStage.code) ++ observeStage.code)
        {initialMachine with stack := tail} = .ok {final with stack := tail} 0 ∧
      run (allocationStage.code ++ (captureStage.code ++ observeStage.code))
        {initialMachine with stack := tail} = .ok {final with stack := tail} 0 ∧
      MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
        {initialMachine with stack := tail} σ {mid with stack := tail} mb ∧
      MappedOutput (.memory captureStage) 1 7 mb σ {mid with stack := tail}
        CaptureControls.afterCapture {next with stack := tail} nb ∧
      MappedOutput (.memory observeStage) 1 7 nb CaptureControls.afterCapture
        {next with stack := tail} CaptureControls.afterValue {final with stack := tail} ob ∧
      ob CompileExamples.r0.id = nb CompileExamples.r0.id ∧
      nb CompileExamples.r0.id = mb CompileExamples.r0.id ∧
      ob CompileExamples.r1.id = mb CompileExamples.r1.id ∧
      BaseExtends σ.H mb ob ∧
      GrowsAllocator 1 7 5 (State.init C) initialBase {initialMachine with stack := tail}
        CaptureControls.afterValue ob {final with stack := tail} := by
  obtain ⟨mb, nb, ob, mid, next, final, _, _, _, hall⟩ :=
    compilation_triple_shared (.memory allocationStage) (.memory captureStage) (.memory observeStage)
      prefix_input7 rfl first_link second_link rfl rfl rfl
      ReachabilityControls.fresh_state_reaches_fixture capture_source observe_source
  refine ⟨mb, nb, ob, mid, next, final, ?_⟩
  intro tail
  obtain ⟨ha, hd, he, hl, hr, ma, md, me⟩ := hall tail
  have ma' : MappedOutput (.memory allocationStage) 1 7 initialBase (State.init C)
      {initialMachine with stack := tail} σ {mid with stack := tail} mb := by
    simpa only [allocationStage.cert.pushes_zero, Nat.add_zero] using ma
  have md' : MappedOutput (.memory captureStage) 1 7 mb σ {mid with stack := tail}
      CaptureControls.afterCapture {next with stack := tail} nb := by
    simpa only [allocationStage.cert.pushes_zero, captureStage.cert.pushes_zero, Nat.add_zero] using md
  have me' : MappedOutput (.memory observeStage) 1 7 nb CaptureControls.afterCapture
      {next with stack := tail} CaptureControls.afterValue {final with stack := tail} ob := by
    simpa only [allocationStage.cert.pushes_zero, captureStage.cert.pushes_zero,
      observeStage.cert.pushes_zero, Nat.add_zero] using me
  have hb : BaseExtends σ.H mb ob :=
    BaseExtends.trans (List.prefix_refl _) md'.2.1 me'.2.1
  have hg := GrowsAllocator.comp ma'.2.2 (GrowsAllocator.comp md'.2.2 me'.2.2)
  have hc : captureStage.cert.cost σ = 0 := by decide +kernel
  have ho : observeStage.cert.cost CaptureControls.afterCapture = 0 := by decide +kernel
  exact ⟨ha, hd, he, hl, hr, ma', md', me', me'.2.1 CompileExamples.r0,
    md'.2.1 CompileExamples.r0, hb CompileExamples.r1, hb,
    by simpa only [reached_cost, hc, ho, Nat.add_zero] using hg⟩

def code : List Instr := allocationStage.code ++ (captureStage.code ++ observeStage.code)
private def cell (n : Nat) : Evm.Out → Option Nat
  | .ok m _ => match m.mem n with | .val w => some w.val | _ => none
  | _ => none

private theorem cell4 : cell 4 (run code initialMachine) = some 7 := by decide +kernel
private theorem cell5 : cell 5 (run code initialMachine) = some 16 := by decide +kernel
private theorem cell6 : cell 6 (run code initialMachine) = some 8 := by decide +kernel
private theorem cell17 : cell 17 (run code initialMachine) = some 8 := by decide +kernel
private theorem cell2 : cell 2 (run code initialMachine) = some 16 := by decide +kernel
private theorem cell3 : cell 3 (run code initialMachine) = some 16 := by decide +kernel
private theorem cell1 : cell 1 (run code initialMachine) = some 19 := by decide +kernel
private theorem cell20 : cell 20 (run code initialMachine) = some 4 := by decide +kernel
private theorem cell0 : cell 0 (run code initialMachine) = some 21 := by decide +kernel

/-- Complete ordered vector: saved primitive, fresh reference, fresh read,
mutated element, both original aliases, independent array/value and cursor. -/
theorem ordered_results :
    [4, 5, 6, 17, 2, 3, 1, 20, 0].mapM (fun n => cell n (run code initialMachine)) =
      some [7, 16, 8, 8, 16, 16, 19, 4, 21] := by
  simp only [List.mapM_cons, List.mapM_nil, cell4, cell5, cell6, cell17,
    cell2, cell3, cell1, cell20, cell0]
  rfl

theorem stale_map (m : Machine) :
    ¬ StateRepr 1 1 7 allocationStage.frag σ initialBase m :=
by
  intro h
  have bad := h.heap.above CompileExamples.r0
  change 7 ≤ 0 at bad
  omega

theorem corruption : ∃ canonical : Machine,
    run code {initialMachine with stack := [w[41], w[19]]} =
      .ok {canonical with stack := [w[41], w[19]]} 0 ∧
    run (code ++ [.pop]) {initialMachine with stack := [w[41], w[19]]} =
      .ok {canonical with stack := [w[19]]} 0 := by
  obtain ⟨_, _, _, _, _, final, h⟩ := shared_resources
  refine ⟨final, (h _).2.2.2.2.1, ?_⟩
  change run ((allocationStage.code ++ (captureStage.code ++ observeStage.code)) ++ _) _ = _
  rw [run_append_ok (h _).2.2.2.2.1]
  rfl

end Solidity.Backend.Passes.TripleControls
