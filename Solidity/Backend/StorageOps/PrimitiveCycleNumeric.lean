import Solidity.Backend.StorageOps.PrimitiveCycleMachine

/-! Whole-store algebra of the ACTUAL existing numeric primitive cycle.
Both numeric operations reset child BEFORE writing header; this order matters
when physical addresses collide. No representation or hash premise is hidden. -/
namespace Solidity.Backend.StorageOps.PrimitiveCycleNumeric
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph

private theorem header_bound (N : Nat) (hash : Solidity.Storage.Pre → Nat)
 (base : Solidity.Storage.Loc) (numeric : WordStore) :
 LifecycleNumeric.headerLength N hash base numeric < 2^256 := by
 have bound := (numeric (base.word N hash)).property
 simp only [PrimTy.inRange,decide_eq_true_eq] at bound
 unfold LifecycleNumeric.headerLength
 omega

def afterPop (N : Nat) (hash : Solidity.Storage.Pre → Nat)
 (base : Solidity.Storage.Loc) (numeric : WordStore) : WordStore :=
 let h := LifecycleNumeric.headerLength N hash base numeric
 writeWord (writeWord numeric ((Solidity.Storage.Loc.data base (h-1)).word N hash) ClearDemands.zero)
  (base.word N hash) (lengthWord (h-1) (by have bound:=header_bound N hash base numeric; omega))

/-- Exact actual numeric pop outcome; no world rollback is inferred. -/
theorem pop_outcome (N : Nat) (hash : Solidity.Storage.Pre → Nat)
 (base : Solidity.Storage.Loc) (numeric : WordStore) :
 PrimitivePop.execute N hash base numeric =
 if 0<LifecycleNumeric.headerLength N hash base numeric then some (afterPop N hash base numeric) else none := by
 unfold PrimitivePop.execute
 dsimp only
 by_cases live : 0<LifecycleNumeric.headerLength N hash base numeric
 · rw [dif_pos live,if_pos live]
   rfl
 · rw [dif_neg live,if_neg live]

/-- Header is written LAST, so this fact needs no child/root separation. -/
theorem pop_header (N : Nat) (hash : Solidity.Storage.Pre → Nat)
 (base : Solidity.Storage.Loc) (numeric : WordStore) :
 LifecycleNumeric.headerLength N hash base (afterPop N hash base numeric)=
 LifecycleNumeric.headerLength N hash base numeric-1 := by
 apply LifecycleNumeric.headerLength_known hash base _ ⟨_,by have b:=header_bound N hash base numeric; omega⟩
 simp only [afterPop,writeWord,if_true]

/-- Entire numeric WordStore/Option equality for the actual primitive triple.
No finite observations, graph metadata, intermediate zero/room/equality, or
hash premise is assumed. It follows from actual reset-before-header order. -/
theorem cycle (N : Nat) (hash : Solidity.Storage.Pre → Nat)
 (base : Solidity.Storage.Loc) (numeric : WordStore) :
 PrimitiveCycleProgram.execute N hash base numeric=PrimitivePop.execute N hash base numeric := by
 let h := LifecycleNumeric.headerLength N hash base numeric
 have bounded : h<2^256 := header_bound N hash base numeric
 by_cases positive : 0<h
 · let first := afterPop N hash base numeric
   have firstHeader : LifecycleNumeric.headerLength N hash base first=h-1 := pop_header N hash base numeric
   have room : h-1+1<2^256 := by omega
   let grown := writeWord (writeWord first ((Solidity.Storage.Loc.data base (h-1)).word N hash) ClearDemands.zero)
     (base.word N hash) (lengthWord (h-1+1) room)
   have grownHeader : LifecycleNumeric.headerLength N hash base grown=h := by
    have known : LifecycleNumeric.headerLength N hash base grown=h-1+1 := by
     apply LifecycleNumeric.headerLength_known hash base grown ⟨_,room⟩
     simp only [grown,writeWord,if_true]
    omega
   have pushed : LifecycleNumeric.pushPrimitive N hash base first=some grown := by
    unfold LifecycleNumeric.pushPrimitive
    rw [firstHeader,dif_pos room]
   have returned : afterPop N hash base grown=first := by
    simp only [afterPop,grownHeader]
    funext observer
    by_cases root : observer=base.word N hash
    · simp only [writeWord,if_pos root,first,afterPop,h]
    · by_cases child : observer=(Solidity.Storage.Loc.data base (h-1)).word N hash
      · simp only [writeWord,if_neg root,if_pos child,first,afterPop,h]
      · simp only [writeWord,if_neg root,if_neg child,grown,first,afterPop,h]
   unfold PrimitiveCycleProgram.execute TargetPrimitivePopPush.execute
   rw [pop_outcome,if_pos positive]
   change (LifecycleNumeric.pushPrimitive N hash base first).bind (PrimitivePop.execute N hash base)=some first
   rw [pushed]
   change PrimitivePop.execute N hash base grown=some first
   rw [pop_outcome,if_pos (by rw [grownHeader]; exact positive),returned]
 · unfold PrimitiveCycleProgram.execute TargetPrimitivePopPush.execute
   rw [pop_outcome,if_neg positive]
   rfl

/-- Per-run separation is still necessary for the selected-clear observation:
that conclusion is not inferred from the premise-free whole-cycle identity. -/
theorem selected_zero {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {preimages : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash preimages locations)
 (base : Solidity.Storage.Loc) (numeric : WordStore)
 (rootCovered : base ∈ locations)
 (childCovered : Solidity.Storage.Loc.data base (LifecycleNumeric.headerLength N hash base numeric-1) ∈ locations) :
 afterPop N hash base numeric ((Solidity.Storage.Loc.data base (LifecycleNumeric.headerLength N hash base numeric-1)).word N hash)=ClearDemands.zero := by
 have different : (Solidity.Storage.Loc.data base (LifecycleNumeric.headerLength N hash base numeric-1)).word N hash ≠ base.word N hash := by
  intro same
  have equality := run.word_inj childCovered rootCovered same
  have depth := congrArg Solidity.Storage.Loc.depth equality
  change base.depth+1=base.depth at depth
  omega
 simp only [afterPop,writeWord,if_neg different,if_true]

/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleNumeric.pop_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_outcome
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleNumeric.pop_header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms pop_header
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleNumeric.cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cycle
/-- info: 'Solidity.Backend.StorageOps.PrimitiveCycleNumeric.selected_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms selected_zero
end Solidity.Backend.StorageOps.PrimitiveCycleNumeric
