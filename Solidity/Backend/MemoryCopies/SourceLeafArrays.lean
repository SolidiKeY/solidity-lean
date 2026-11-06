import Solidity.Backend.MemoryCopies.SourceLeafInterface

/-! Arbitrary-length Source reference-element defaults, using the existing fold. -/
namespace Solidity.Backend.MemoryCopies

def bytesLeaf (E : Source.Env) : SourceLeafDefault E (.bytes .memory) rfl :=
  ⟨.bytes [],fun _ _ => rfl⟩
def stringLeaf (E : Source.Env) : SourceLeafDefault E (.string .memory) rfl :=
  ⟨.string [],fun _ _ => rfl⟩
def dynamicLeaf (E : Source.Env) (element : Source.STy) :
    SourceLeafDefault E (.array .memory element none) rfl :=
  ⟨.array 0 (fun _ impossible => nomatch impossible) Fin.elim0,fun _ _ => rfl⟩

/-- Actual Source element traversal succeeds with enough explicit horizon;
every element is a fresh reference at its own exact address. -/
theorem SourceLeafDefault.elements {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    {memory : τ.loc? = some .memory} (leaf : SourceLeafDefault E τ memory)
    (count slack : Nat) (before : Source.EMState E Γ) :
    SourceLeafElementsResult memory before count slack := by
  induction count generalizing before with
  | zero =>
    refine ⟨Fin.elim0,before,?_,Nat.add_zero _ |>.symm,AllocationExtension.refl before,?_⟩
    · have budget : 0 + 2 + slack = (slack + 1) + 1 := by omega
      rw [budget,Source.zeroElems]
      · rfl
      · omega
    · intro index
      exact Fin.elim0 index
  | succ count previous =>
    let one : Source.EMState E Γ := allocatedState leaf.data before
    obtain ⟨values,after,execution,frontier,preserved,indices⟩ := previous one
    have firstRun : (Source.zeroVal (E := E) (Γ := Γ) (count + 2 + slack) τ).run before =
        (.ok (.memRef memory before.2.heap.next),one) := by
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using leaf.execution before (count + slack)
    have firstFrame : AllocationExtension before one := AllocatesOnly.alloc leaf.data before
    refine ⟨Source.finCons (.val (.memRef memory before.2.heap.next)) values,after,?_,?_,
      firstFrame.trans preserved,?_⟩
    · have budget : count + 1 + 2 + slack = (count + 2 + slack) + 1 := by omega
      rw [budget,Source.zeroElems,Source.Hoare.run_bind,firstRun]
      dsimp only
      rw [Source.Hoare.run_bind,execution]
      rfl
    · change after.2.heap.next = before.2.heap.next + (count + 1)
      change after.2.heap.next = before.2.heap.next + 1 + count at frontier
      omega
    · intro index
      rcases index with ⟨index,bound⟩
      cases index with
      | zero => rfl
      | succ index =>
        change values ⟨index,by omega⟩ =
          Source.Data.val (Source.Val.memRef memory (before.2.heap.next + (index + 1)))
        rw [indices]
        congr 2
        change before.2.heap.next + 1 + index = before.2.heap.next + (index + 1)
        omega

/-- Allocate the fixed parent only after all reference children have actually
been constructed. The existing Source certificate includes old/nonheap state. -/
theorem SourceLeafDefault.fixed {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    {memory : τ.loc? = some .memory} (leaf : SourceLeafDefault E τ memory)
    (count slack : Nat) (before : Source.EMState E Γ) :
    ∃ (values : Fin count → Source.Data E.layout τ) (after : Source.EMState E Γ),
      let data : Source.Data E.layout (.array .memory τ (some count)) :=
        .array count (fun _ equality => by cases equality; rfl) values
      SourceDefaultCertificate (count + 4 + slack) (.array .memory τ (some count)) rfl
        before (allocatedState data after) after.2.heap.next data ∧
      after.2.heap.next = before.2.heap.next + count ∧
      (∀ i, values i = .val (.memRef memory (before.2.heap.next + i.val))) := by
  obtain ⟨values,after,execution,frontier,preserved,indices⟩ := leaf.elements count slack before
  let data : Source.Data E.layout (.array .memory τ (some count)) :=
    .array count (fun _ equality => by cases equality; rfl) values
  have constructed :
      (Source.zeroVal (E := E) (Γ := Γ) (count + 4 + slack) (.array .memory τ (some count))).run before =
        (.ok (.memRef rfl after.2.heap.next),allocatedState data after) := by
    have budget : count + 4 + slack = (count + 2 + slack) + 1 + 1 := by omega
    rw [budget]
    rw [Source.zeroVal]
    simp only [Source.Val.default,Source.Val.defaultElem,Source.STy.loc?,if_true]
    rw [Source.Hoare.run_bind]
    rw [Source.zeroData,Source.Hoare.run_bind,execution]
    dsimp only
    exact allocRef_run data rfl after
  have frame : AllocationExtension before (allocatedState data after) := by
    have derived : AllocationExtension before
        ((Source.zeroVal (E := E) (Γ := Γ) (count + 4 + slack) (.array .memory τ (some count))).run before).2 :=
      zeroVal_allocates (count + 4 + slack) (.array .memory τ (some count)) before
    rw [constructed] at derived
    exact derived
  exact ⟨values,after,⟨constructed,frame.frame,frame.growth,preserved.growth,
    Source.Heap.alloc_get _ _,frame.old⟩,frontier,indices⟩

#print axioms bytesLeaf
#print axioms stringLeaf
#print axioms dynamicLeaf
#print axioms SourceLeafDefault.elements
#print axioms SourceLeafDefault.fixed
end Solidity.Backend.MemoryCopies
