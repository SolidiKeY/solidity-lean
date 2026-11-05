import Solidity.Assurance.NonVacuityH28.CheckedObjects

/-! Additional existing Compilation constructors on a live allocated heap.
These are contract non-vacuity witnesses, not producer-operation audits. -/
namespace Solidity.Assurance.NonVacuityH28
open Solidity Semantics

abbrev MemCtx : Ctx := [.mem (.array (.prim .uint))]
variable (C : Contract)

def liveLayout : Evm.Frag MemCtx := (constructionResult C).frag

def scalarMemoryProgram : Prog C MemCtx MemCtx := .cons (.require (.simple (.bool true))) .nil

def declareMemoryProgram : Prog C MemCtx (.val .uint :: MemCtx) :=
  .cons (.declLocal .uint (.user "v") (some (.simple (.lit 7 rfl)))) .nil

def selfRebindProgram : Prog C MemCtx MemCtx :=
  .cons (.rebindMem .here (.alias (.var .here rfl))) .nil

theorem scalar_memory_source (σ : State C MemCtx) :
    Prog.run σ (scalarMemoryProgram C) = .ok ⟨σ, List.prefix_refl _⟩ := rfl

theorem declare_memory_source (σ : State C MemCtx) :
    Prog.run σ (declareMemoryProgram C) =
      .ok ⟨σ.push (⟨7, rfl⟩ : PrimTy.uint.Denote), List.prefix_refl _⟩ := rfl

theorem self_rebind_source (σ : State C MemCtx) (r : HRef σ.H (.array (.prim .uint)))
    (hr : TEnv.get .here σ.env = some r) :
    Prog.run σ (selfRebindProgram C) = .ok ⟨σ.setLocal .here (some r), List.prefix_refl _⟩ := by
  have hp : (MPath.var .here rfl : MPath C MemCtx (.ref (.array (.prim .uint)))).mvalT σ = .ok r := by
    simp only [MPath.mvalT, hr]
  change TRun.seq (TRun.rebindMem .here (.alias (.var .here rfl))) TRun.nil σ = _
  simp only [TRun.seq, TRun.rebindMem, MRhs.evalT, hp, bind, Except.bind, pure, Except.pure, TRun.nil, Except.map]

/-- Existing complete object ownership entails the unchanged fixed-array input. -/
theorem objects_supply_fixed {Γ : Ctx} {L b frame : Nat} {F : Evm.Frag Γ}
    {σ : State C Γ} {base : Nat → Fin Evm.W} {mc : Evm.Machine}
    (h : Evm.Memory.Objects.StateRepr L b frame F σ base mc) :
    Evm.Memory.FixedStateRepr L b frame F σ base mc := by
  refine ⟨h.legacy, ⟨?_, ?_⟩⟩
  · intro p n r
    refine ⟨?_, ?_⟩
    · have hs : (base r.id).val + max 1 n ≤ Evm.W := (h.heap.arrays .fixed r).space
      exact Nat.le_trans (Nat.add_le_add_left (Nat.le_max_right 1 n) _) hs
    · intro i v hv
      simpa only [Evm.Memory.Objects.ValueRepr, Evm.Memory.Objects.header, Nat.add_zero]
        using (h.heap.arrays .fixed r).elements i v (by simpa only [MObj.elems_fixed] using hv)
  · intro p n r
    exact h.heap.owner.above r

def referenceArrayResult : Evm.Memory.ReferenceArrays.CompiledProg 1 (liveLayout C) (selfRebindProgram C) :=
  (Evm.Memory.ReferenceArrays.compileProg 1 (liveLayout C) (selfRebindProgram C)).get (by rfl)
def referenceArrayCompiled : Evm.Compiler.Compilation 1 (liveLayout C) (selfRebindProgram C) :=
  .referenceArrays (referenceArrayResult C)

def objectResult : Evm.Memory.Objects.CompiledProg 1 (liveLayout C) (declareMemoryProgram C) :=
  (Evm.Memory.Objects.compileProg 1 (liveLayout C) (declareMemoryProgram C)).get (by rfl)
def objectCompiled : Evm.Compiler.Compilation 1 (liveLayout C) (declareMemoryProgram C) :=
  .objects (objectResult C)

def loopResult : Evm.Memory.Loops.CompiledProg 1 (liveLayout C) (scalarMemoryProgram C) :=
  (Evm.Memory.Loops.compileProg 1 (liveLayout C) (scalarMemoryProgram C)).get (by rfl)
def loopCompiled : Evm.Compiler.Compilation 1 (liveLayout C) (scalarMemoryProgram C) :=
  .memoryLoops (loopResult C)

def scopeResult : Evm.Memory.LoopScopes.CompiledProg 1 (liveLayout C) (scalarMemoryProgram C) :=
  (Evm.Memory.LoopScopes.compileProg 1 (scalarMemoryProgram C) (liveLayout C)).get (by rfl)
def scopeCompiled : Evm.Compiler.Compilation 1 (liveLayout C) (scalarMemoryProgram C) :=
  .memoryLoopScopes (scopeResult C)

def callsResult : Evm.Memory.Calls.Program 1 (liveLayout C) (scalarMemoryProgram C) :=
  (Evm.Memory.Calls.compile 1 (liveLayout C) (scalarMemoryProgram C)).get (by rfl)
def callsCompiled : Evm.Compiler.Compilation 1 (liveLayout C) (scalarMemoryProgram C) :=
  .memoryCalls (callsResult C) rfl

def copyResult : Evm.Memory.StorageCopy.CompiledProg 1 (liveLayout C) (scalarMemoryProgram C) :=
  (Evm.Memory.StorageCopy.compileProg 1 (liveLayout C) (scalarMemoryProgram C)).get (by rfl)
def copyCompiled : Evm.Compiler.Compilation 1 (liveLayout C) (scalarMemoryProgram C) :=
  .memoryCopy (copyResult C)

def fixedResult : Evm.Memory.Fixed.CompiledProg 1 (liveLayout C) (scalarMemoryProgram C) :=
  (Evm.Memory.Fixed.compileProg 1 (liveLayout C) (scalarMemoryProgram C)).get (by rfl)
def fixedCompiled : Evm.Compiler.Compilation 1 (liveLayout C) (scalarMemoryProgram C) :=
  .fixedMemory (fixedResult C)

def copyConstructionResult : Evm.Memory.CopyConstruction.CompiledProg 1 (liveLayout C) (scalarMemoryProgram C) :=
  (Evm.Memory.CopyConstruction.compileProg 1 (liveLayout C) (scalarMemoryProgram C)).get (by rfl)
def copyConstructionCompiled : Evm.Compiler.Compilation 1 (liveLayout C) (scalarMemoryProgram C) :=
  .copyConstruction (copyConstructionResult C)

variable {base : Nat → Fin Evm.W} {σ : State C MemCtx} {mc : Evm.Machine}

theorem reference_array_input (h : Evm.Memory.Objects.StateRepr 1 1 128 (liveLayout C) σ base mc) :
    (referenceArrayCompiled C).Input 1 128 base σ mc := h.reference

theorem object_input (h : Evm.Memory.Objects.StateRepr 1 1 128 (liveLayout C) σ base mc) :
    (objectCompiled C).Input 1 128 base σ mc := by
  exact ⟨h, by change 3 ≤ 128; decide⟩

theorem loop_input (h : Evm.Memory.Objects.StateRepr 1 1 128 (liveLayout C) σ base mc) :
    (loopCompiled C).Input 1 128 base σ mc := by
  exact ⟨h.legacy, by change 2 ≤ 128; decide,
    Evm.Memory.Loops.room_nonallocating (loopResult C).cert rfl σ base mc⟩

theorem scope_input (h : Evm.Memory.Objects.StateRepr 1 1 128 (liveLayout C) σ base mc) :
    (scopeCompiled C).Input 1 128 base σ mc := by
  exact ⟨h.legacy, by change 2 ≤ 128; decide,
    Evm.Memory.LoopScopes.room_nonallocating (scopeResult C).cert rfl σ base mc⟩

theorem calls_input (h : Evm.Memory.Objects.StateRepr 1 1 128 (liveLayout C) σ base mc) :
    (callsCompiled C).Input 1 128 base σ mc := by
  exact ⟨h.legacy, by change 2 ≤ 128; decide, .inl rfl⟩

theorem copy_input (h : Evm.Memory.Objects.StateRepr 1 1 128 (liveLayout C) σ base mc) :
    (copyCompiled C).Input 1 128 base σ mc := by
  exact ⟨h.legacy, by change 2 ≤ 128; decide, .inl rfl, by change 0 ≤ 1; decide⟩

theorem fixed_input (h : Evm.Memory.Objects.StateRepr 1 1 128 (liveLayout C) σ base mc) :
    (fixedCompiled C).Input 1 128 base σ mc :=
  ⟨objects_supply_fixed C h, by change 0 ≤ 1; decide⟩

theorem copy_construction_input (h : Evm.Memory.Objects.StateRepr 1 1 128 (liveLayout C) σ base mc) :
    (copyConstructionCompiled C).Input 1 128 base σ mc := by
  exact ⟨h, by change 2 ≤ 128; decide, .inl rfl, by change 0 ≤ 1; decide⟩

/-- Actual source and target executions retaining the selected output relation. -/
def SuccessfulChecked {Γ Δ : Ctx} {F : Evm.Frag Γ} {P : Prog C Γ Δ}
    (result : Evm.Compiler.Compilation 1 F P) (σ : State C Γ)
    (base : Nat → Fin Evm.W) (mc : Evm.Machine) : Prop :=
  result.Input 1 128 base σ mc ∧
  ∃ o mc', Prog.run σ P = .ok o ∧ Evm.run result.code mc = .ok mc' 0 ∧
    mc'.stack = mc.stack ∧ result.Rep (1 + Evm.Prog.pushes P) 128 base σ mc o.st mc'

private theorem successful_checked {Γ Δ : Ctx} {F : Evm.Frag Γ} {P : Prog C Γ Δ}
    (result : Evm.Compiler.Compilation 1 F P) {σ : State C Γ}
    {base : Nat → Fin Evm.W} {mc : Evm.Machine} {o : Out C σ.H Δ}
    (input : result.Input 1 128 base σ mc) (hpay : Evm.Prog.pays P = false)
    (hs : Prog.run σ P = .ok o) : SuccessfulChecked C result σ base mc := by
  obtain ⟨mc', ht, hstack, hr⟩ := checked_success_after_source result input hpay hs
  exact ⟨input, o, mc', hs, ht, hstack, hr⟩

/-- All eight additional constructors share an actual allocated source heap.
The scalar cases inhabit their public contracts; they do not audit backend
loop, call or copy operations. -/
theorem checked_families_joint :
    ∃ mc : Evm.Machine, ∃ base : Nat → Fin Evm.W,
      Evm.Memory.Objects.StateRepr 1 1 128 (liveLayout C) (primitiveOutcome C).st base mc ∧
      SuccessfulChecked C (referenceArrayCompiled C) (primitiveOutcome C).st base mc ∧
      SuccessfulChecked C (objectCompiled C) (primitiveOutcome C).st base mc ∧
      SuccessfulChecked C (loopCompiled C) (primitiveOutcome C).st base mc ∧
      SuccessfulChecked C (scopeCompiled C) (primitiveOutcome C).st base mc ∧
      SuccessfulChecked C (callsCompiled C) (primitiveOutcome C).st base mc ∧
      SuccessfulChecked C (copyCompiled C) (primitiveOutcome C).st base mc ∧
      SuccessfulChecked C (fixedCompiled C) (primitiveOutcome C).st base mc ∧
      SuccessfulChecked C (copyConstructionCompiled C) (primitiveOutcome C).st base mc := by
  obtain ⟨mc, base, _, _, h⟩ := construction_joint C
  obtain ⟨r, hr, _⟩ := h.pointers (.here : Idx MemCtx (.mem (.array (.prim .uint))))
  refine ⟨mc, base, h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact successful_checked C _ (reference_array_input C h) rfl (self_rebind_source C _ r hr)
  · exact successful_checked C _ (object_input C h) rfl (declare_memory_source C _)
  · exact successful_checked C _ (loop_input C h) rfl (scalar_memory_source C _)
  · exact successful_checked C _ (scope_input C h) rfl (scalar_memory_source C _)
  · exact successful_checked C _ (calls_input C h) rfl (scalar_memory_source C _)
  · exact successful_checked C _ (copy_input C h) rfl (scalar_memory_source C _)
  · exact successful_checked C _ (fixed_input C h) rfl (scalar_memory_source C _)
  · exact successful_checked C _ (copy_construction_input C h) rfl (scalar_memory_source C _)

end Solidity.Assurance.NonVacuityH28
