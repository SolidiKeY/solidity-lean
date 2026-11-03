import Solidity.Backend.Passes.MemoryCallScopeControls
import Solidity.Backend.Passes.ReindexedMemory

/-! A concrete public compiler result is used directly. Complete certificate
record equality is not a premise of its typed physical composition. -/
namespace Solidity.Backend.Passes.CompilerCallScopeRecognition
open Evm Evm.Memory Evm.Compiler MemoryCallControls
open MemoryCallScopeBoundary.Controls (scopeProgram scopeProducer post suffix)

theorem accepted_some : (Compiler.compile 1 allocation.frag scopeProgram).isSome = true := by
  decide +kernel

@[irreducible] def actual : Compilation 1 allocation.frag scopeProgram :=
  (Compiler.compile 1 allocation.frag scopeProgram).get accepted_some

theorem accepted : Compiler.compile 1 allocation.frag scopeProgram = some actual := by
  unfold actual
  exact (Option.some_get _).symm

theorem branch : actual.isMemoryCalls = true := by
  with_unfolding_all decide +kernel

theorem frame : actual.requiredFrame = scopeProducer.need := by
  with_unfolding_all decide +kernel

theorem fragment : actual.frag = scopeProducer.frag := by
  with_unfolding_all decide +kernel

theorem allocation_cost : actual.allocationCost first.st = 6 := by
  with_unfolding_all decide +kernel

theorem memory_calls_mapped_iff {C : Contract} {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} (result : Compilation b F P) (kind : result.isMemoryCalls = true)
    (base selected : Nat → Fin W) (entry : State C Γ) (initial : Machine)
    (state : State C Δ) (middle : Machine) :
    MappedOutput result L frame base entry initial state middle selected ↔
      StateRepr L b frame result.frag state selected middle ∧
      BaseExtends entry.H base selected ∧
      GrowsAllocator b frame (result.allocationCost entry) entry base initial state selected middle := by
  cases result with
  | core out cert => cases kind
  | memory out => cases kind
  | referenceArrays out => cases kind
  | objects out => cases kind
  | construction out => cases kind
  | memoryLoops out => cases kind
  | memoryLoopScopes out => cases kind
  | memoryCalls out free => rfl
  | memoryCopy out => cases kind
  | fixedMemory out => cases kind
  | copyConstruction out => cases kind

theorem input {L frame : Nat} {selected : Nat → Fin W} {m : Machine}
    (h : checked.Input L frame selected first.st m) : actual.Input L frame selected first.st m := by
  have scopedInput := MemoryCallScopeBoundary.input producer push_free h
  apply (actual.memoryCalls_input branch L frame selected first.st m).mpr
  refine ⟨scopedInput.1, ?_, ?_⟩
  · rw [CompilerCallScopeRecognition.frame]
    exact scopedInput.2.1
  · rw [allocation_cost]
    have hc : (MemoryCallScopeBoundary.compiled producer).cost first.st = 6 :=
      (MemoryCallScopeBoundary.cost producer first.st).trans MemoryCallControls.costs.2.1
    simpa only [hc] using scopedInput.2.2

theorem input_back {L frame : Nat} {selected : Nat → Fin W} {m : Machine}
    (h : actual.Input L frame selected first.st m) : checked.Input L frame selected first.st m := by
  have opened := (actual.memoryCalls_input branch L frame selected first.st m).mp h
  have room : 1 + scopeProducer.need ≤ frame := by
    simpa only [CompilerCallScopeRecognition.frame] using opened.2.1
  have budget : AllocationInput 1 frame 6 first.st selected m := by
    simpa only [allocation_cost] using opened.2.2
  have scopedInput : MemoryCallScopeBoundary.Controls.scopeChecked.Input L frame selected first.st m :=
    ⟨opened.1,room,MemoryCallScopeBoundary.Controls.reached_cost.symm ▸ budget⟩
  exact MemoryCallScopeBoundary.input_back producer push_free scopedInput

theorem input_iff (L frame : Nat) (selected : Nat → Fin W) (m : Machine) :
    actual.Input L frame selected first.st m ↔ checked.Input L frame selected first.st m :=
  ⟨input_back,input⟩

theorem private_frame_strict : frameNeedProg call < actual.requiredFrame := by
  with_unfolding_all decide +kernel

theorem private_frame_refused {selected : Nat → Fin W} {state : State C Before} {m : Machine} :
    ¬ actual.Input 1 (1 + frameNeedProg call) selected state m := by
  intro h
  have cap := ((actual.memoryCalls_input branch 1 (1+frameNeedProg call) selected state m).mp h).2.1
  have strict := private_frame_strict
  omega

def consumer : CompiledProg 1 actual.frag suffix :=
  memory_reindex fragment MemoryCallScopeBoundary.Controls.right

theorem consumer_code : consumer.code = MemoryCallScopeBoundary.Controls.right.code :=
  memory_reindex_code fragment _

theorem into_actual : MappedBoundaryLink (.memory allocation) actual 1 128 base initial machine := by
  intro o mid selected source run output
  have same : first = o := Except.ok.inj (first_source.symm.trans source)
  subst o
  exact input (MemoryCallApplication.into_call first mid selected first_source run output)

theorem next_link (entry : State C Before) (incoming : Nat → Fin W) (m : Machine) :
    MappedBoundaryLink actual (.memory consumer) 1 128 incoming entry m := by
  intro o next selected _ _ output
  have free : Evm.Prog.pushes scopeProgram = 0 := MemoryCallScopeBoundary.scope_free push_free
  simp only [free,Nat.add_zero] at output ⊢
  have represented := (memory_calls_mapped_iff actual branch incoming selected entry m o.st next).mp output
  exact ⟨represented.1,by decide +kernel,.inl (allocationCostProg_zero suffix rfl o.st)⟩

theorem after_actual : ReachedMappedLink (.memory allocation) actual (.memory consumer) 1 128 base initial machine := by
  intro o mid selected _ _ _
  simpa only [MemoryCallApplication.allocation_free,Nat.add_zero] using next_link o.st selected mid

theorem shared : ∃ (mb nb ob : Nat → Fin W) (mid next out : Machine),
    mid.stack = [] ∧ next.stack = [] ∧ out.stack = [] ∧ ∀ tail,
    run allocation.code {machine with stack := tail} = .ok {mid with stack := tail} 0 ∧
    run actual.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
    run consumer.code {next with stack := tail} = .ok {out with stack := tail} 0 ∧
    run ((allocation.code ++ actual.code) ++ consumer.code) {machine with stack := tail} = .ok {out with stack := tail} 0 ∧
    run (allocation.code ++ (actual.code ++ consumer.code)) {machine with stack := tail} = .ok {out with stack := tail} 0 ∧
    MappedOutput (.memory allocation) 1 128 base initial {machine with stack := tail} first.st {mid with stack := tail} mb ∧
    MappedOutput actual 1 128 mb first.st {mid with stack := tail} post {next with stack := tail} nb ∧
    MappedOutput (.memory consumer) 1 128 nb post {next with stack := tail}
      MemoryCallScopeBoundary.Controls.final.st {out with stack := tail} ob := by
  have free : Evm.Prog.pushes scopeProgram = 0 := MemoryCallScopeBoundary.scope_free push_free
  simpa only [MemoryCallApplication.allocation_free,free,consumer.cert.pushes_zero,Nat.add_zero] using
    compilation_triple_shared (.memory allocation) actual (.memory consumer) MemoryCallControls.input rfl
      into_actual after_actual (by decide +kernel) (by decide +kernel) (by decide +kernel)
      first_source MemoryCallScopeBoundary.Controls.scope_source MemoryCallScopeBoundary.Controls.suffix_source

end Solidity.Backend.Passes.CompilerCallScopeRecognition
