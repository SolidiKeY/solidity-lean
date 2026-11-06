import Solidity.Backend.StorageOps.NumericRetainedCycle

/-! Exact intrinsic retained aggregate slot identity through actual operations.
These are graph operation laws, separate from numeric/target/Source/world bridges.
Primitive reuse needs defaulted observations rather than unrestricted raw identity. -/
namespace Solidity.Backend.StorageOps.GraphRetainedCycle
open TypeGraph

def execute {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
 (old : Value G (.array E)) : Option (Value G (.array E)) := do
 let popped ← recursivePop old
 let grown ← operationPush popped
 recursivePop grown

private theorem array_ext {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
 (left right : Value G (.array E))
 (extentEq : left.extent.val = right.extent.val)
 (lengthEq : left.length = right.length)
 (slotsEq : ∀ (i : Fin left.extent.val) (j : Fin right.extent.val),
   i.val=j.val → left.slots i = right.slots j) : left=right := by
 cases left with
 | array le ll lb ls =>
  cases right with
  | array re rl rb rs =>
   have extent : le=re := Fin.ext extentEq
   cases extent
   cases lengthEq
   have slots : ls=rs := funext (fun i => slotsEq i i rfl)
   cases slots
   rfl

/-- Actual nonprimitive push preserves the exact retained absent/present slot,
not only its defaulted getD observation. No retention cap or liveness inference. -/
theorem push_slots {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
 (old result : Value G (.array E)) (pushed : operationPush old=some result)
 (nonprimitive : E.isPrimitive=false)
 (i : Fin old.extent.val) (j : Fin result.extent.val) (same : i.val=j.val) :
 result.slots j=old.slots i := by
 cases old with
 | array extent length bound slots =>
  simp only [operationPush,Value.extent,Value.length,Value.slots] at pushed
  split at pushed
  · cases pushed
    have inside : j.val < extent.val := by have within : i.val < extent.val := i.isLt; omega
    simp only [Value.slots,nonprimitive,Bool.false_eq_true,false_and,if_false,dif_pos inside]
    apply congrArg slots
    exact Fin.ext same.symm
  · cases pushed

/-- Actual pop's exact raw slot update, including absent slots and retained tails. -/
theorem pop_slots {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
 (old result : Value G (.array E)) (popped : recursivePop old=some result)
 (i : Fin old.extent.val) (j : Fin result.extent.val) (same : i.val=j.val) :
 result.slots j = if j.val=old.length.val-1 then recursiveClearSlot (old.slots i) else old.slots i := by
 cases old with
 | array extent length bound slots =>
  simp only [recursivePop,Value.extent,Value.length,Value.slots] at popped
  split at popped
  · cases popped
    have indices : i=j := Fin.ext same
    cases indices
    rfl
  · cases popped

/-- Aggregate pop/regrowth/pop restores the exact FIRST popped value,
including mapping barriers, absent slots and retained histories at every depth. -/
theorem cycle {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
 (old middle grown : Value G (.array E))
 (popped : recursivePop old=some middle) (pushed : operationPush middle=some grown)
 (nonprimitive : E.isPrimitive=false) : recursivePop grown=some middle := by
 have popHeader := recursivePop_header old middle popped
 have grownHeader := PopPush.headers old middle grown popped pushed
 have live : 0 < grown.length.val := by omega
 cases second : recursivePop grown with
 | none =>
   have empty := (recursivePop_failure grown).mp second
   omega
 | some result =>
   have resultHeader := recursivePop_header grown result second
   have extents : result.extent.val=middle.extent.val := by rw [resultHeader.2,grownHeader.2,popHeader.2]
   have lengths : result.length=middle.length := Fin.ext (by omega)
   apply congrArg some
   apply array_ext result middle extents lengths
   intro i j same
   let k : Fin grown.extent.val := ⟨i.val,by rw [← resultHeader.2]; exact i.isLt⟩
   rw [pop_slots grown result second k i rfl,
     push_slots middle grown pushed nonprimitive j k same.symm]
   by_cases selected : i.val=grown.length.val-1
   · rw [if_pos selected]
     let original : Fin old.extent.val := ⟨j.val,by rw [← popHeader.2]; exact j.isLt⟩
     have was := pop_slots old middle popped original j rfl
     have last : j.val=old.length.val-1 := by omega
     rw [if_pos last] at was
     rw [was]
     simp only [recursiveClearSlot_eq_clear,Slot.clear_idem]
   · rw [if_neg selected]

/-- Both complete Option outcomes match the first actual pop for aggregate
reuse. Capacity is derived from the first pop, never an extra source premise. -/
theorem outcome {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
 (old : Value G (.array E)) (nonprimitive : E.isPrimitive=false) :
 execute old=recursivePop old := by
 cases popped : recursivePop old with
 | none =>
   unfold execute
   rw [popped]
   rfl
 | some middle =>
   obtain ⟨grown,pushed⟩ := NestedPopRegrow.push_exists old middle popped
   unfold execute
   rw [popped]
   change (do let grown ← operationPush middle; recursivePop grown) = some middle
   rw [pushed]
   exact cycle old middle grown popped pushed nonprimitive

/-- info: 'Solidity.Backend.StorageOps.GraphRetainedCycle.push_slots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms push_slots
/-- info: 'Solidity.Backend.StorageOps.GraphRetainedCycle.pop_slots' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pop_slots
/-- info: 'Solidity.Backend.StorageOps.GraphRetainedCycle.cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cycle
/-- info: 'Solidity.Backend.StorageOps.GraphRetainedCycle.outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms outcome
end Solidity.Backend.StorageOps.GraphRetainedCycle
