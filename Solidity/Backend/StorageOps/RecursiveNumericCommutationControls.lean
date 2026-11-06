import Solidity.Backend.StorageOps.RecursiveNumericCommutation
import Solidity.Backend.StorageOps.CopyDemandControls

/-! Heterogeneous nested/primitive actual copies with shared read-only source,
GOOD finite regions, complete changed/shadow/context observations and source
interference counterexample. Fixed graph captures are explicit. -/
namespace Solidity.Backend.StorageOps.RecursiveNumericCommutationControls
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph
open RecursiveNumericCommutation
private def ix (i : Fin 4) : Index := ⟨i.val,by have h := i.isLt; omega⟩
private def zero : Semantics.Word := ClearDemands.zero
private def one : Semantics.Word := PrimTy.toWord (p := .bool) true
private def two : Semantics.Word := lengthWord 2 (by decide)
private def seven : Semantics.Word := ⟨7,by decide⟩
private abbrev B : TypeGraph.Ty 0 := .array (.prim .bool)
private def oldB : Value CopyDemandControls.graph B :=
  .array ⟨3,by decide⟩ ⟨2,by decide⟩ (by decide) (fun _ => .present (.prim true))
private def srcB : Value CopyDemandControls.graph B :=
  .array ⟨3,by decide⟩ ⟨1,by decide⟩ (by decide) (fun i => .present (.prim (i.val != 0)))
private def altB : Value CopyDemandControls.graph B :=
  .array ⟨3,by decide⟩ ⟨1,by decide⟩ (by decide) (fun _ => .present (.prim true))
private def dstA : Solidity.Storage.Loc := .root 0
private def sourceA : Solidity.Storage.Loc := .root 1
private def dstB : Solidity.Storage.Loc := .root 2
private def sourceB : Solidity.Storage.Loc := .data sourceA 0
private def hash (p : Solidity.Storage.Pre) : Nat := if p = .data 0 then 8 else if p = .data 1 then 24 else if p = .data 2 then 16 else if p = .data 3 then 32 else if p = .data 8 then 40 else if p = .data 9 then 48 else if p = .data 10 then 56 else if p = .data 11 then 64 else if p = .data 24 then 104 else 0
private def preimages : List Solidity.Storage.Pre := [.data 0,.data 1,.data 2,.data 3,
  .data 8,.data 9,.data 10,.data 11,.data 24]
private def machine : WordStore := fun a =>
  if a = 0 ∨ a = 2 ∨ a = 8 ∨ a = 9 ∨ a = 10 then two else
  if a = 1 ∨ a = 3 ∨ a = 16 ∨ a = 17 ∨ a = 18 ∨ a = 24 ∨ a = 25 ∨ a = 32 ∨ a = 33 ∨ a = 34 ∨
    a = 40 ∨ a = 41 ∨ a = 42 ∨ a = 48 ∨ a = 49 ∨ a = 50 ∨ a = 56 ∨ a = 57 ∨ a = 58 then one else
  if a = 104 then zero else seven
private noncomputable def wa := writeSet CopyDemandControls.old CopyDemandControls.src dstA
private noncomputable def wb := writeSet oldB srcB dstB
private noncomputable def ra := readSet CopyDemandControls.src sourceA
private noncomputable def rb := readSet srcB sourceB
private noncomputable def locations := wa ++ wb ++ ra ++ rb ++ [.data (.data dstA 3) 0,.data dstB 2,.root 3,.data (.root 3) 0]
private def writeLocations : List Solidity.Storage.Loc :=
  [.data (.data dstA 0) 0,.data (.data dstA 0) 1,.data dstA 0,
   .data (.data dstA 1) 0,.data (.data dstA 1) 1,.data dstA 1,dstA,
   .data dstB 0,.data dstB 1,dstB]
private def readLocations : List Solidity.Storage.Loc := [.data sourceB 0,sourceB,sourceA,.data sourceB 0,sourceB]
private theorem run : FiniteRun 256 4 4 hash preimages locations := by
  constructor
  · intro p; simp only [hash]; split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (split <;> (first | decide | (decide))))))))))))))))))
  · decide
  · decide
  · decide
  · intro l member
    change l ∈ writeLocations ++ readLocations ++ [.data (.data dstA 3) 0,.data dstB 2,.root 3,.data (.root 3) 0] at member
    simp only [writeLocations,readLocations,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [dstA,dstB,sourceA,sourceB,Solidity.Storage.Loc.Bounded] <;> decide
  · intro l member
    change l ∈ writeLocations ++ readLocations ++ [.data (.data dstA 3) 0,.data dstB 2,.root 3,.data (.root 3) 0] at member
    simp only [writeLocations,readLocations,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
private theorem waCovered : ∀ a ∈ wa, a ∈ locations := by
  intro a member
  simp only [locations,List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl member)))
private theorem wbCovered : ∀ a ∈ wb, a ∈ locations := by
  intro a member
  simp only [locations,List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr member)))
private theorem raCovered : ∀ a ∈ ra, a ∈ locations := by
  intro a member
  simp only [locations,List.mem_append]
  exact Or.inl (Or.inl (Or.inr member))
private theorem rbCovered : ∀ a ∈ rb, a ∈ locations := by
  intro a member
  simp only [locations,List.mem_append]
  exact Or.inl (Or.inr member)
private theorem disjointWrites : ∀ a ∈ wa, ∀ b ∈ wb, a ≠ b := by
  intro a member b inside
  change a ∈ [.data (.data dstA 0) 0,.data (.data dstA 0) 1,.data dstA 0,
    .data (.data dstA 1) 0,.data (.data dstA 1) 1,.data dstA 1,dstA] at member
  change b ∈ [.data dstB 0,.data dstB 1,dstB] at inside
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member inside
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases inside with rfl | rfl | rfl <;> decide
private theorem wbRa : ∀ b ∈ wb, ∀ a ∈ ra, b ≠ a := by
  intro b member a inside
  change b ∈ [.data dstB 0,.data dstB 1,dstB] at member
  change a ∈ [.data sourceB 0,sourceB,sourceA] at inside
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member inside
  rcases member with rfl | rfl | rfl <;> rcases inside with rfl | rfl | rfl <;> decide
private theorem waRb : ∀ a ∈ wa, ∀ b ∈ rb, a ≠ b := by
  intro a member b inside
  change a ∈ [.data (.data dstA 0) 0,.data (.data dstA 0) 1,.data dstA 0,
    .data (.data dstA 1) 0,.data (.data dstA 1) 1,.data dstA 1,dstA] at member
  change b ∈ [.data sourceB 0,sourceB] at inside
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member inside
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases inside with rfl | rfl <;> decide
private noncomputable def copyA (m : WordStore) := CopyWrites.numericCopy (N := 256)
  CopyDemandControls.old CopyDemandControls.src dstA sourceA hash m
private noncomputable def copyB (m : WordStore) := CopyWrites.numericCopy (N := 256) oldB srcB dstB sourceB hash m
private def view (m : WordStore) := (m 0,m 8,m 9,m 10,m 40,m 41,m 42,m 48,m 49,m 50,m 56,
  m 2,m 16,m 17,m 18,m 1,m 24,m 104,m 64,m 255)

/-- Different aggregate endpoint types share actual read-only source cells.
The entire actual WordStore result commutes, not merely its projection. -/
theorem heterogeneous_commutation : copyB (copyA machine) = copyA (copyB machine) :=
  copy_copy CopyDemandControls.old CopyDemandControls.src oldB srcB dstA sourceA dstB sourceB machine run
    waCovered wbCovered raCovered rbCovered disjointWrites wbRa waRb

/-- ALL20 ordered observations distinguish BOTH changed targets, clear tails,
older shadows, shared source, failed-query garbage and outside sentinel. -/
theorem complete_numeric_observations :
    (view machine,view (copyB (copyA machine)),view (copyA (copyB machine))) =
    ((two,two,two,two,one,one,one,one,one,one,one,two,one,one,one,one,one,zero,seven,seven),
     (one,one,zero,two,zero,zero,one,zero,zero,one,one,one,zero,zero,one,one,one,zero,seven,seven),
     (one,one,zero,two,zero,zero,one,zero,zero,one,one,one,zero,zero,one,one,one,zero,seven,seven)) := by rfl

/-- Shared source reads are genuinely present, not removed by the premises. -/
theorem shared_source : sourceB ∈ ra ∧ sourceB ∈ rb ∧ .data sourceB 0 ∈ ra ∧ .data sourceB 0 ∈ rb := by
  exact ⟨List.mem_cons_of_mem _ List.mem_cons_self,List.mem_cons_of_mem _ List.mem_cons_self,
    List.mem_cons_self,List.mem_cons_self⟩

private noncomputable def interfere (m : WordStore) :=
  CopyWrites.numericCopy (N := 256) srcB altB sourceB (.root 3) hash m
private def interferenceView (m : WordStore) := (m 2,m 16,m 17,m 18,m 24,m 104,m 3,m 32,m 255)

/-- Removing first-write/second-read separation changes live payloads even with
disjoint destination writes. Fixed graph shape captures remain explicit. -/
theorem wrong_source_interference :
    (interferenceView machine,interferenceView (copyB (interfere machine)),interferenceView (interfere (copyB machine))) =
    ((two,one,one,one,one,zero,one,one,seven),
     (one,one,zero,one,one,one,one,one,seven),
     (one,zero,zero,one,one,one,one,one,seven)) := by rfl

/-- Concrete ordered execution applies public symbolic/numeric Transport to
BOTH actual generated logs; no post graph representation is assumed. -/
theorem ordered_transport :
    let aLog := CopyWrites.updates (N := 256) CopyDemandControls.old CopyDemandControls.src dstA sourceA hash machine
    let bLog := CopyWrites.updates (N := 256) oldB srcB dstB sourceB hash (copyA machine)
    Transport 256 hash locations
      (bLog.foldl (fun w op => write w op.1 op.2)
        (aLog.foldl (fun w op => write w op.1 op.2) (fun l => machine (l.word 256 hash))))
      (copyB (copyA machine)) :=
  sequence_transport CopyDemandControls.old CopyDemandControls.src oldB srcB dstA sourceA dstB sourceB
    (fun l => machine (l.word 256 hash)) machine run (by intro l _; rfl)
    waCovered wbCovered rbCovered waRb

/-- info: 'Solidity.Backend.StorageOps.RecursiveNumericCommutationControls.ordered_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ordered_transport

/-- info: 'Solidity.Backend.StorageOps.RecursiveNumericCommutationControls.heterogeneous_commutation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms heterogeneous_commutation
/-- info: 'Solidity.Backend.StorageOps.RecursiveNumericCommutationControls.complete_numeric_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms complete_numeric_observations
/-- info: 'Solidity.Backend.StorageOps.RecursiveNumericCommutationControls.shared_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shared_source
/-- info: 'Solidity.Backend.StorageOps.RecursiveNumericCommutationControls.wrong_source_interference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_source_interference

end Solidity.Backend.StorageOps.RecursiveNumericCommutationControls
