import Solidity.Backend.InternalFlow.RuntimeFrameV3CountdownWitness

/-! Zero-cost allocator transport for the existing recursive return image.
The initial allocator remains a real ownership premise. Reached representation,
cursor-cell equality and free-tail equality supply the output allocator;
no full memory equality or arbitrary-callee heap preservation is assumed. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.AllocatorReturn
open Evm Evm.Memory

/-- Reuse reached heap representation while transporting the existing free
arena and its exact cursor. Live source object intervals are unchanged. -/
theorem allocator {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
 {σ : State C Γ} {base : Nat → Fin W} {before after : Machine}
 (reached : StateRepr L b frame F σ base after)
 (cursorCell : after.mem 0=before.mem 0)
 (exterior : ∀ x, frame≤x → after.mem x=before.mem x)
 (cursor : Fin W) (initial : StructAllocatorRepr σ.heap base frame cursor before) :
 StructAllocatorRepr σ.heap base frame cursor after := by
 refine ⟨⟨reached.heap,?_,initial.arrays.live⟩,reached.structs,reached.separated,initial.live⟩
 refine ⟨initial.arrays.free.reserved,initial.arrays.free.above,
   cursorCell.trans initial.arrays.free.cell,?_⟩
 intro x bound
 exact (exterior x (Nat.le_trans initial.arrays.free.above bound)).trans
   (initial.arrays.free.zero x bound)

/-- The exact public allocator implication, with zero SOURCE allocation cost.
Runtime private frame words are below `frame`, not heap allocations. -/
theorem growth {C : Contract} {Γ : Ctx} {L b frame : Nat} {F : Frag Γ}
 {σ : State C Γ} {base : Nat → Fin W} {before after : Machine}
 (reached : StateRepr L b frame F σ base after)
 (cursorCell : after.mem 0=before.mem 0)
 (exterior : ∀ x, frame≤x → after.mem x=before.mem x) :
 GrowsAllocator b frame 0 σ base before σ base after := by
 intro cursor positive initial space
 simpa only [Nat.add_zero] using allocator reached cursorCell exterior cursor initial

/-- The actual populated countdown endpoint now exports the same allocator
implication at the nonzero callee offset. Initial ownership is not claimed by
this legacy fixture, whose caller cell zero is a reference rather than a heap
allocator cursor. This is a conditional component, not a producer instance. -/
theorem countdown_growth :
 GrowsAllocator 2 16 0 CountdownWitness.callee CountdownWitness.P.base
   CountdownWitness.machine CountdownWitness.callee CountdownWitness.P.base CountdownWitness.returned := by
 apply growth CountdownWitness.specification.2.2.1
 · exact CountdownWitness.specification.2.2.2.2.2.1 0 (by decide) (by decide)
 · exact CountdownWitness.specification.2.2.2.2.2.2.1

namespace Checks
open CountdownWitness RecursiveSource RecursiveActivation RecursiveReturn

/-- A NEW callee-only input: word zero is a genuine allocator cursor. The old
whole-caller fixture and all of its observations remain unchanged. -/
def input : Machine := writeMachine CountdownWitness.machine 0 w[22]

theorem represented : StateRepr 1 2 16 F callee P.base input := by
 apply Restored.memory_transport callee_repr input.mem
 · intro t index observed
   cases index with
   | here => rfl
   | there index => cases index with
     | here => rfl
     | there index => cases index
 · intro x above
   exact upd_other _ _ (by omega)

theorem ownership : StructAllocatorRepr callee.heap P.base 16 ⟨22,by decide⟩ input := by
 refine ⟨⟨represented.heap,⟨by decide,by decide,rfl,?_⟩,?_⟩,
   represented.structs,represented.separated,?_⟩
 · intro x bound
   change 22≤x at bound
   simp only [input,CountdownWitness.machine,writeMachine,upd]
   simp only [if_neg (show x≠0 from by omega),if_neg (show x≠9 from by omega),
     if_neg (show x≠8 from by omega),if_neg (show x≠3 from by omega)]
   change P.machine.mem x=w[0]
   simp only [P.machine,Evm.Memory.CompileExamples.machine]
   simp only [if_neg (show x≠0 from by omega),if_neg (show x≠1 from by omega),
     if_neg (show x≠2 from by omega),if_neg (show x≠16 from by omega),
     if_neg (show x≠17 from by omega),if_neg (show x≠18 from by omega),
     if_neg (show x≠20 from by omega),if_neg (show x≠21 from by omega)]
 · intro p r
   rcases r with ⟨i,hi⟩
   cases i with
   | zero => cases hi; with_unfolding_all decide
   | succ i => cases i with
     | zero => cases hi; with_unfolding_all decide
     | succ i => cases hi
 · intro name r
   rcases r with ⟨i,hi⟩
   cases i with
   | zero => cases hi
   | succ i => cases i with
     | zero => cases hi
     | succ i => cases hi

/-- Actual two-level descent/unwind, starting with inhabited allocator
ownership and ending with the SAME cursor and complete represented heap. -/
theorem endpoint : ∃ last,
 run (entryCode (C:=P.C) 2 F 8 7) input=.ok last 0 ∧
 StateRepr 1 2 16 F callee P.base last ∧
 StructAllocatorRepr callee.heap P.base 16 ⟨22,by decide⟩ last ∧
 GrowsAllocator 2 16 0 callee P.base input callee P.base last ∧
 last.stack=[w[77]] ∧ last.mem 0=w[22] ∧ last.mem 8=w[10] ∧
 (∀ x,16≤x → last.mem x=input.mem x) := by
 obtain ⟨last,source,executed,reached,stack,cursor,low,high,history,bottom⟩ :=
   initialized_endpoint rfl 2 (by decide) callee P.r0 rfl rfl P.base input represented
     8 8 7 10 (by decide) (by decide) (by decide) (by decide)
     (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl
 have cell : last.mem 0=input.mem 0 := low 0 (by decide) (by decide)
 exact ⟨last,executed,reached,allocator reached cell high _ ownership,
   growth reached cell high,stack,cell,cursor,high⟩

/-- Wrong allocator cursor is rejected by its actual cell equality. -/
theorem wrong_cursor : ¬ StructAllocatorRepr callee.heap P.base 16 ⟨23,by decide⟩ input := by
 intro bad
 have cell := bad.arrays.free.cell
 change w[22]=w[23] at cell
 have different : w[22]≠w[23] := by decide
 exact different cell

/-- A real nonzero write in the free tail invalidates ownership even when
all older objects and the cursor cell remain unchanged. -/
theorem wrong_tail : ¬ StructAllocatorRepr callee.heap P.base 16 ⟨22,by decide⟩
 (writeMachine input 22 w[1]) := by
 intro bad
 have zero := bad.arrays.free.zero 22 (Nat.le_refl _)
 change w[1]=w[0] at zero
 have different : w[1]≠w[0] := by decide
 exact different zero

end Checks
end Solidity.Backend.InternalFlow.RuntimeFrame.AllocatorReturn

/-- info: 'Solidity.Backend.InternalFlow.RuntimeFrame.AllocatorReturn.Checks.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Solidity.Backend.InternalFlow.RuntimeFrame.AllocatorReturn.Checks.endpoint
