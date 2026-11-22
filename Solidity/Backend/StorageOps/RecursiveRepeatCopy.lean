import Solidity.Backend.StorageOps.RecursiveCopy

/-! Reapplying the SAME captured source snapshot to the recursive graph copy.
No re-read of a possibly overlapping source, new admission/depth bound,
representation relation, eager target execution or world rollback is implied. -/
namespace Solidity.Backend.StorageOps.RecursiveRepeatCopy
open TypeGraph

mutual
/-- Recursive operation idempotence in the destination, with source fixed. -/
theorem value_repeat {n : Nat} {G : Schema n} :
 {T : TypeGraph.Ty n} → (old src : Value G T) →
 recursiveCopy (recursiveCopy old src) src=recursiveCopy old src
 | _, old, .prim _ => by cases old; rfl
 | _, .node old, .node src => by
   apply congrArg Value.node
   funext U p
   exact value_repeat (old p) (src p)
 | _, .array oe ol oh os, .array ne nl nh ns => by
   simp only [recursiveCopy_eq_overlay,Value.overlay]
   apply array_value_ext
   · change max (max oe.val nl.val) nl.val=max oe.val nl.val
     omega
   · intro i j equal
     have inside : i.val < max oe.val nl.val := by rw [equal]; exact j.isLt
     simp only [dif_pos inside]
     by_cases live : j.val < nl.val
     · simp only [equal,dif_pos live]
       exact (show
        ((if h : j.val < oe.val then os ⟨j.val,h⟩ else Slot.absent).overlay
         (ns ⟨j.val,Nat.lt_of_lt_of_le live nh⟩)).overlay
         (ns ⟨j.val,Nat.lt_of_lt_of_le live nh⟩)=
        (if h : j.val < oe.val then os ⟨j.val,h⟩ else Slot.absent).overlay
         (ns ⟨j.val,Nat.lt_of_lt_of_le live nh⟩) from by
          simpa only [recursiveSlot_eq_overlay] using slot_repeat
           (if h : j.val < oe.val then os ⟨j.val,h⟩ else Slot.absent)
           (ns ⟨j.val,Nat.lt_of_lt_of_le live nh⟩))
     · simp only [equal,dif_neg live,if_neg live]
 | _, .fixed old, .fixed src => by
   apply congrArg Value.fixed
   funext i
   exact slot_repeat (old i) (src i)
 | _, old, .mapping _ => by cases old; rfl

/-- An absent captured slot repeats clear; a present slot recurses. -/
theorem slot_repeat {n : Nat} {G : Schema n} :
 {T : TypeGraph.Ty n} → (old src : Slot G T) →
 recursiveSlot (recursiveSlot old src) src=recursiveSlot old src
 | _, old, .absent => by
   simp only [recursiveSlot_eq_overlay,Slot.overlay,Slot.clear_idem]
 | _, old, .present src => by
   change Slot.present (recursiveCopy (recursiveCopy (old.getD (Value.dflt _)) src) src)=
    Slot.present (recursiveCopy (old.getD (Value.dflt _)) src)
   exact congrArg Slot.present (value_repeat _ src)
end

/-- info: 'Solidity.Backend.StorageOps.RecursiveRepeatCopy.value_repeat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms value_repeat
/-- info: 'Solidity.Backend.StorageOps.RecursiveRepeatCopy.slot_repeat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms slot_repeat
end Solidity.Backend.StorageOps.RecursiveRepeatCopy
