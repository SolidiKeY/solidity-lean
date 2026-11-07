import Solidity.Backend.MemoryCopies.SourceConstructionInterface
import Solidity.Backend.MemoryCopies.SourceLeafArrays

/-! Closure of existing Source default certificates under fixed-array nesting. -/
namespace Solidity.Backend.MemoryCopies

def SourceLeafDefault.construction {E : Source.Env} {τ : Source.STy}
    {memory : τ.loc? = some .memory} (leaf : SourceLeafDefault E τ memory) :
    SourceConstructionCertificate E τ memory where
  horizon := 2
  objects := 1
  horizon_positive := by decide
  objects_positive := by decide
  execution := by
    intro Γ before slack
    have execution : (Source.zeroVal (E := E) (Γ := Γ) (2 + slack) τ).run before =
        (.ok (.memRef memory before.2.heap.next),allocatedState leaf.data before) := by
      simpa only [Nat.add_comm] using leaf.execution before slack
    refine ⟨allocatedState leaf.data before,before.2.heap.next,leaf.data,
      ⟨execution,rfl,?_,Nat.le_refl _,Source.Heap.alloc_get _ _,?_⟩,rfl,rfl⟩
    · change before.2.heap.next ≤ before.2.heap.next + 1
      omega
    · intro address older
      exact Source.Heap.alloc_other _ _ (Nat.ne_of_lt older)

theorem SourceConstructionCertificate.elements {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    {memory : τ.loc? = some .memory} (child : SourceConstructionCertificate E τ memory)
    (count slack : Nat) (before : Source.EMState E Γ) :
    SourceConstructionElements child count slack before := by
  induction count generalizing before with
  | zero =>
    refine ⟨Fin.elim0,before,?_,?_,AllocationExtension.refl before⟩
    · have positive : 0 < child.horizon + slack := by
        have childPositive : 0 < child.horizon := child.horizon_positive
        omega
      have budget : 0 + child.horizon + slack = (child.horizon + slack - 1) + 1 := by omega
      rw [budget,Source.zeroElems]
      · rfl
      · omega
    · simp only [Nat.zero_mul,Nat.add_zero]
  | succ count previous =>
    obtain ⟨one,root,data,certificate,firstCount,_⟩ := child.execution before (count + slack)
    obtain ⟨values,after,execution,frontier,preserved⟩ := previous one
    have firstRun : (Source.zeroVal (E := E) (Γ := Γ) (count + child.horizon + slack) τ).run before =
        (.ok (.memRef memory root),one) := by
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using certificate.execution
    have firstFrame : AllocationExtension before one := ⟨certificate.frame,certificate.growth,certificate.old⟩
    refine ⟨Source.finCons (.val (.memRef memory root)) values,after,?_,?_,firstFrame.trans preserved⟩
    · have budget : count + 1 + child.horizon + slack = (count + child.horizon + slack) + 1 := by omega
      rw [budget,Source.zeroElems,Source.Hoare.run_bind,firstRun]
      dsimp only
      rw [Source.Hoare.run_bind,execution]
      rfl
    · rw [frontier,firstCount,Nat.succ_mul]
      omega

/-- A proved child constructor supplies every nested allocation. No source
shape or desired child outcome is silently assumed by the fixed constructor. -/
def SourceConstructionCertificate.fixed {E : Source.Env} {τ : Source.STy}
    {memory : τ.loc? = some .memory} (child : SourceConstructionCertificate E τ memory)
    (count : Nat) : SourceConstructionCertificate E (.array .memory τ (some count)) rfl where
  horizon := count + child.horizon + 2
  objects := count * child.objects + 1
  horizon_positive := by omega
  objects_positive := by omega
  execution := by
    intro Γ before slack
    obtain ⟨values,middle,children,counted,preserved⟩ := child.elements count slack before
    let data : Source.Data E.layout (.array .memory τ (some count)) :=
      .array count (fun _ equality => by cases equality; rfl) values
    have execution :
        (Source.zeroVal (E := E) (Γ := Γ) (count + child.horizon + 2 + slack)
          (.array .memory τ (some count))).run before =
        (.ok (.memRef rfl middle.2.heap.next),allocatedState data middle) := by
      have budget : count + child.horizon + 2 + slack = (count + child.horizon + slack) + 1 + 1 := by omega
      rw [budget,Source.zeroVal]
      simp only [Source.Val.default,Source.Val.defaultElem,Source.STy.loc?,if_true]
      rw [Source.Hoare.run_bind,Source.zeroData,Source.Hoare.run_bind,children]
      dsimp only
      exact allocRef_run data rfl middle
    have frame : AllocationExtension before (allocatedState data middle) := by
      have derived : AllocationExtension before
          ((Source.zeroVal (E := E) (Γ := Γ) (count + child.horizon + 2 + slack)
            (.array .memory τ (some count))).run before).2 :=
        zeroVal_allocates _ _ before
      rw [execution] at derived
      exact derived
    refine ⟨allocatedState data middle,middle.2.heap.next,data,
      ⟨execution,frame.frame,frame.growth,preserved.growth,Source.Heap.alloc_get _ _,frame.old⟩,?_,rfl⟩
    change middle.2.heap.next + 1 = before.2.heap.next + (count * child.objects + 1)
    rw [counted]
    omega

#print axioms SourceLeafDefault.construction
#print axioms SourceConstructionCertificate.elements
#print axioms SourceConstructionCertificate.fixed
end Solidity.Backend.MemoryCopies
