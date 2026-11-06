import Solidity.Evm.Compiler
import Solidity.Roadmap.V16.Specifications

/-!
Scoped consumers of the published ordinary-memory-call compiler certificate.
The actual Input retains state/frame/reached allocation obligations. Program.sound
has only represented success or exact empty revert; the public Agrees union is
not narrowed by assuming a desired target run. No byte-EVM/source-profile claim.
-/
namespace Solidity.Roadmap.V16
open Solidity.Evm

/-- The actual memory-call constructor supplies the stronger published relation. -/
theorem memory_call_result {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemoryCalls = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} (input : compiled.Input L frame base σ m) :
    Memory.GrowingResult L b frame (compiled.allocationCost σ) compiled.frag σ base m
      (P.run σ) (run compiled.code m) := by
  cases compiled with
  | memoryCopy _ => cases path
  | fixedMemory _ => cases path
  | copyConstruction _ => cases path
  | core _ _ => cases path
  | memory _ => cases path
  | referenceArrays _ => cases path
  | objects _ => cases path
  | construction _ => cases path
  | memoryLoops _ => cases path
  | memoryLoopScopes _ => cases path
  | memoryCalls out _ => exact out.sound input.1 input.2.1 input.2.2

/-- Unpack the successful public representation without losing base extension
or the exact reached allocator cost. -/
theorem memory_call_rep_iff {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemoryCalls = true) {σ : State C Γ} {τ : State C Δ}
    {base : Nat → Fin W} {m m' : Machine} :
    compiled.Rep L frame base σ m τ m' ↔
      ∃ base', Memory.StateRepr L b frame compiled.frag τ base' m' ∧
        Memory.BaseExtends σ.H base base' ∧
        Memory.GrowsAllocator b frame (compiled.allocationCost σ) σ base m τ base' m' := by
  cases compiled with
  | memoryCopy _ => cases path
  | fixedMemory _ => cases path
  | copyConstruction _ => cases path
  | core _ _ => cases path
  | memory _ => cases path
  | referenceArrays _ => cases path
  | objects _ => cases path
  | construction _ => cases path
  | memoryLoops _ => cases path
  | memoryLoopScopes _ => cases path
  | memoryCalls _ _ => rfl

/-- Actual source success selects represented target success using soundness,
not the broader public Agrees payment/panic/divergence alternatives. -/
theorem memory_call_success {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemoryCalls = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {o : Solidity.Out C σ.H Δ}
    (input : compiled.Input L frame base σ m) (source : P.run σ = .ok o) :
    ∃ m' base', run compiled.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
      Memory.StateRepr L b frame compiled.frag o.st base' m' ∧
      Memory.BaseExtends σ.H base base' ∧
      Memory.GrowsAllocator b frame (compiled.allocationCost σ) σ base m o.st base' m' := by
  rcases memory_call_result compiled path input with
    ⟨u, m', base', hs, ht, repr, stack, baseExtension, grows⟩ | ⟨hs, _⟩
  · have eq : u = o := Except.ok.inj (hs.symm.trans source)
    subst u
    exact ⟨m', base', ht, stack, repr, baseExtension, grows⟩
  · rw [source] at hs
    cases hs

/-- A source box at a real successful compiled memory call gives a machine-side
represented specification witness, retaining its entire evaluation-stack tail. -/
theorem memory_call_spec {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemoryCalls = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {o : Solidity.Out C σ.H Δ} {φ : Spec C Δ}
    (input : compiled.Input L frame base σ m) (source : P.run σ = .ok o)
    (box : Spec.sat σ (.box P φ)) :
    ∃ m', run compiled.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
      compiled.Rep L frame base σ m o.st m' ∧ Spec.sat o.st φ := by
  obtain ⟨m', base', ht, stack, repr, baseExtension, grows⟩ :=
    memory_call_success compiled path input source
  exact ⟨m', ht, stack, (memory_call_rep_iff compiled path).2
    ⟨base', repr, baseExtension, grows⟩, spec_box_post box source⟩

/-- On this actual certificate path, a source failure is precisely empty revert.
No panic, payload-bearing revert or divergence is silently collapsed into it. -/
theorem memory_call_failure {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemoryCalls = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {e : THalt} (input : compiled.Input L frame base σ m)
    (source : P.run σ = .error e) : e = .revert ∧ run compiled.code m = .revert := by
  rcases memory_call_result compiled path input with
    ⟨_, _, _, hs, _⟩ | ⟨hs, ht⟩
  · rw [source] at hs
    cases hs
  · rw [source] at hs
    exact ⟨Except.error.inj hs, ht⟩

/-- Source alias identity yields equality of actual represented pointer cells. -/
theorem memory_call_alias {C : Contract} {L b frame : Nat} {Γ : Ctx}
    {F : Frag Γ} {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : Memory.StateRepr L b frame F σ base m) {R : RefTy}
    (i j : Idx Γ (.mem R)) (r : HRef σ.H R)
    (left : TEnv.get i σ.env = some r) (right : TEnv.get j σ.env = some r) :
    m.mem (cellOf b i) = m.mem (cellOf b j) := by
  obtain ⟨ri, hi, mi⟩ := repr.pointers i
  obtain ⟨rj, hj, mj⟩ := repr.pointers j
  have ei : ri = r := Option.some.inj (hi.symm.trans left)
  have ej : rj = r := Option.some.inj (hj.symm.trans right)
  subst ri
  subst rj
  exact mi.trans mj.symm

/-- Required private frame size remains an actual admission obligation. -/
theorem memory_call_small_frame {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemoryCalls = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} (small : frame < b + compiled.requiredFrame) :
    ¬ compiled.Input L frame base σ m := by
  intro input
  have bound := ((compiled.memoryCalls_input path L frame base σ m).1 input).2.1
  exact Nat.not_lt_of_ge bound small

/-- Actual reached allocator capacity yields its exact post-run cursor cell. -/
theorem memory_call_cursor {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemoryCalls = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {o : Solidity.Out C σ.H Δ}
    (input : compiled.Input L frame base σ m) (source : P.run σ = .ok o)
    (cursor : Fin W) (positive : 0 < b)
    (allocator : Memory.StructAllocatorRepr σ.heap base frame cursor m)
    (space : cursor.val + compiled.allocationCost σ < W) :
    ∃ m' base', run compiled.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
      Memory.StateRepr L b frame compiled.frag o.st base' m' ∧
      Memory.BaseExtends σ.H base base' ∧
      Memory.StructAllocatorRepr o.st.heap base' frame
        ⟨cursor.val + compiled.allocationCost σ, space⟩ m' ∧
      m'.mem 0 = .val ⟨cursor.val + compiled.allocationCost σ, space⟩ := by
  obtain ⟨m', base', ht, stack, repr, baseExtension, grows⟩ :=
    memory_call_success compiled path input source
  have next := grows cursor positive allocator space
  exact ⟨m', base', ht, stack, repr, baseExtension, next, next.arrays.free.cell⟩

/-- The actual checked memory-call certificate excludes the existing exhausted
outcome. This is not an assumption about all source executions or diamonds. -/
theorem memory_call_not_exhausted {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemoryCalls = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} (input : compiled.Input L frame base σ m) :
    P.run σ ≠ .error .exhausted := by
  intro exhausted
  have impossible := (memory_call_failure compiled path input exhausted).1
  cases impossible

/-- Reached AllocationInput supplies capacity at any actual represented entry
cursor. Cursor equality is obtained from its machine cell, not assumed. -/
theorem memory_call_capacity {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemoryCalls = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} (input : compiled.Input L frame base σ m) (cursor : Fin W)
    (allocator : Memory.StructAllocatorRepr σ.heap base frame cursor m) :
    cursor.val + compiled.allocationCost σ < W := by
  have capacity := ((compiled.memoryCalls_input path L frame base σ m).1 input).2.2
  rcases capacity with zero | ⟨_, other, represented, space⟩
  · rw [zero, Nat.add_zero]
    exact cursor.isLt
  · have eq : cursor = other := Evm.Word.val.inj
      (allocator.arrays.free.cell.symm.trans represented.arrays.free.cell)
    subst other
    exact space

/-- The unchanged approved diamond becomes genuine source AND target success on
this actual finite certificate path. No source-success/notExhausted/target-run
premise is supplied; the certificate discharges exhaustion. -/
theorem memory_call_diamond {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemoryCalls = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {φ : Spec C Δ} (input : compiled.Input L frame base σ m)
    (diamond : Spec.sat σ (.diamond P φ)) :
    ∃ o m' base', P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧ Memory.StateRepr L b frame compiled.frag o.st base' m' ∧
      Memory.BaseExtends σ.H base base' ∧
      Memory.GrowsAllocator b frame (compiled.allocationCost σ) σ base m o.st base' m' ∧
      Spec.sat o.st φ := by
  obtain ⟨o, source, post⟩ := spec_diamond_success diamond
    (memory_call_not_exhausted compiled path input)
  obtain ⟨m', base', target, stack, repr, baseExtension, grows⟩ :=
    memory_call_success compiled path input source
  exact ⟨o, m', base', source, target, stack, repr, baseExtension, grows, post⟩

/-- Scoped equivalence with the full actual source/target/post witness. The
reverse direction uses only the existing successful diamond reading. -/
theorem memory_call_diamond_iff {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemoryCalls = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {φ : Spec C Δ} (input : compiled.Input L frame base σ m) :
    Spec.sat σ (.diamond P φ) ↔
    ∃ o m' base', P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧ Memory.StateRepr L b frame compiled.frag o.st base' m' ∧
      Memory.BaseExtends σ.H base base' ∧
      Memory.GrowsAllocator b frame (compiled.allocationCost σ) σ base m o.st base' m' ∧
      Spec.sat o.st φ := by
  constructor
  · exact memory_call_diamond compiled path input
  · rintro ⟨o, _, _, source, _, _, _, _, _, post⟩
    simpa only [Spec.sat, source] using post

/-- Diamond transport also retains exact reached allocator observations. Capacity
is DERIVED from Input; only the actual entry allocator and positive frame base
are requested, with no desired source/target run premise. -/
theorem memory_call_diamond_cursor {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemoryCalls = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {φ : Spec C Δ} (input : compiled.Input L frame base σ m)
    (diamond : Spec.sat σ (.diamond P φ)) (cursor : Fin W) (positive : 0 < b)
    (allocator : Memory.StructAllocatorRepr σ.heap base frame cursor m) :
    ∃ o m' base', ∃ space : cursor.val + compiled.allocationCost σ < W,
      P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧ m'.stack = m.stack ∧
      Memory.StateRepr L b frame compiled.frag o.st base' m' ∧
      Memory.BaseExtends σ.H base base' ∧
      Memory.GrowsAllocator b frame (compiled.allocationCost σ) σ base m o.st base' m' ∧
      Spec.sat o.st φ ∧ Memory.StructAllocatorRepr o.st.heap base' frame
        ⟨cursor.val + compiled.allocationCost σ, space⟩ m' ∧
      m'.mem 0 = .val ⟨cursor.val + compiled.allocationCost σ, space⟩ := by
  obtain ⟨o, m', base', source, target, stack, repr, baseExtension, grows, post⟩ :=
    memory_call_diamond compiled path input diamond
  have space := memory_call_capacity compiled path input cursor allocator
  have next := grows cursor positive allocator space
  exact ⟨o, m', base', space, source, target, stack, repr, baseExtension, grows,
    post, next, next.arrays.free.cell⟩

/-- A box on this actual checked path supplies successful represented output
with its postcondition OR the exact genuine empty-revert alternative. Source
success is not a premise, and a reverting box does not supply a false post. -/
theorem memory_call_box {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemoryCalls = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {φ : Spec C Δ} (input : compiled.Input L frame base σ m)
    (box : Spec.sat σ (.box P φ)) :
    (∃ o m' base', P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧ Memory.StateRepr L b frame compiled.frag o.st base' m' ∧
      Memory.BaseExtends σ.H base base' ∧
      Memory.GrowsAllocator b frame (compiled.allocationCost σ) σ base m o.st base' m' ∧
      Spec.sat o.st φ) ∨ (P.run σ = .error .revert ∧ run compiled.code m = .revert) := by
  rcases memory_call_result compiled path input with
    ⟨o, m', base', source, target, repr, stack, baseExtension, grows⟩ | ⟨source, target⟩
  · exact .inl ⟨o, m', base', source, target, stack, repr, baseExtension, grows,
      spec_box_post box source⟩
  · exact .inr ⟨source, target⟩

/-- Exact scoped box equivalence preserves both success/post and failure; it is
not a total-success assertion or a change to the approved box reading. -/
theorem memory_call_box_iff {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemoryCalls = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {φ : Spec C Δ} (input : compiled.Input L frame base σ m) :
    Spec.sat σ (.box P φ) ↔
    (∃ o m' base', P.run σ = .ok o ∧ run compiled.code m = .ok m' 0 ∧
      m'.stack = m.stack ∧ Memory.StateRepr L b frame compiled.frag o.st base' m' ∧
      Memory.BaseExtends σ.H base base' ∧
      Memory.GrowsAllocator b frame (compiled.allocationCost σ) σ base m o.st base' m' ∧
      Spec.sat o.st φ) ∨ (P.run σ = .error .revert ∧ run compiled.code m = .revert) := by
  constructor
  · exact memory_call_box compiled path input
  · rintro (⟨o, _, _, source, _, _, _, _, _, post⟩ | ⟨source, _⟩)
    · simpa only [Spec.sat, source] using post
    · simp only [Spec.sat, source, ne_eq, reduceCtorEq, not_false_eq_true]

/-- Box/diamond duality is valid on this actual two-outcome certificate path.
It is deliberately not asserted for arbitrary source execution (exhaustion and
panic in the approved general semantics would invalidate that inference). -/
theorem memory_call_box_diamond_dual {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
    {F : Frag Γ} {P : Prog C Γ Δ} (compiled : Compiler.Compilation b F P)
    (path : compiled.isMemoryCalls = true) {σ : State C Γ} {base : Nat → Fin W}
    {m : Machine} {φ : Spec C Δ} (input : compiled.Input L frame base σ m) :
    Spec.sat σ (.box P φ) ↔ ¬ Spec.sat σ (.diamond P (.not φ)) := by
  classical
  rcases memory_call_result compiled path input with ⟨o, _, _, source, _⟩ | ⟨source, _⟩
  · simpa only [Spec.sat, source] using (Classical.not_not : ¬ ¬ Spec.sat o.st φ ↔ Spec.sat o.st φ).symm
  · simp only [Spec.sat, source, ne_eq, reduceCtorEq, not_false_eq_true, iff_self]

end Solidity.Roadmap.V16
