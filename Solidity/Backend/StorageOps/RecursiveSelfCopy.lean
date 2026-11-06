import Solidity.Backend.StorageOps.RecursiveProgress
import Solidity.Backend.StorageOps.PrefixLaws

/-! Uncapped graph self-copy laws for the existing recursive operation.
These do not assert raw ROOT identity through defaulted prefixes, Source
admission for mapping-containing types, or eager/emitted/world execution. -/
namespace Solidity.Backend.StorageOps.RecursiveSelfCopy
open TypeGraph

/-- Dependent array-domain transport used only in the recursive proof. -/
private theorem array_ext {n : Nat} {G : Schema n} {E : TypeGraph.Ty n}
 (left right : Extent) (length : Index) (lb : length.val ≤ left.val) (rb : length.val ≤ right.val)
 (ls : Fin left.val → Slot G E) (rs : Fin right.val → Slot G E)
 (equal : left.val=right.val)
 (pointwise : ∀ (i : Fin left.val) (j : Fin right.val), i.val=j.val → ls i=rs j) :
 Value.array left length lb ls=Value.array right length rb rs := by
 have sizes : left=right := Fin.ext equal
 cases sizes
 have slots : ls=rs := funext (fun i => pointwise i i rfl)
 cases slots
 rfl

mutual
/-- All recursive constructors, including runtime arrays and mapping barriers. -/
theorem value_self {n : Nat} {G : Schema n} :
 {T : TypeGraph.Ty n} → (value : Value G T) → recursiveCopy value value=value
 | _, .prim _ => by rfl
 | _, .node fields => by
   apply congrArg Value.node
   funext U p
   exact value_self (fields p)
 | _, .array extent length bound slots => by
   rw [recursiveCopy_eq_overlay]
   simp only [Value.overlay]
   apply array_ext
   · exact Nat.max_eq_left bound
   · intro i j equal
     have inside : i.val < extent.val := by rw [equal]; exact j.isLt
     have same : (⟨i.val,inside⟩ : Fin extent.val)=j := Fin.ext equal
     simp only [dif_pos inside]
     by_cases live : i.val < length.val
     · simp only [dif_pos live]
       rw [same]
       exact (recursiveSlot_eq_overlay _ _).symm.trans (slot_self (slots j))
     · simp only [dif_neg live,if_neg live,same]
 | _, .fixed slots => by
   apply congrArg Value.fixed
   funext i
   exact slot_self (slots i)
 | _, .mapping _ => by rfl

/-- Absence stays absent; present data recursively retains its exact value. -/
theorem slot_self {n : Nat} {G : Schema n} :
 {T : TypeGraph.Ty n} → (slot : Slot G T) → recursiveSlot slot slot=slot
 | _, .absent => by rfl
 | _, .present value => by
   change Slot.present (recursiveCopy value value)=Slot.present value
   exact congrArg Slot.present (value_self value)
end

/-- info: 'Solidity.Backend.StorageOps.RecursiveSelfCopy.value_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms value_self
/-- info: 'Solidity.Backend.StorageOps.RecursiveSelfCopy.slot_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms slot_self
end Solidity.Backend.StorageOps.RecursiveSelfCopy
