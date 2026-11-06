import Solidity.Backend.StorageOps.RuntimeCopyRepeat

/-! Actual current-header symbolic/numeric copy composition. OLD transport and
original generated accesses derive both subsequent relations and whole-store
repetition. Independent Source evaluation and emitted loops are not supplied. -/
namespace Solidity.Backend.StorageOps.RuntimeCopyComposition
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph NumericCopyCommutation

/-- BOTH actual runtime-copy transports and whole-store repetition follow from
OLD evidence. No intermediate owner/transport/header stability/coverage oracle.
All symbolic locations and all numeric words are covered by the equalities. -/
theorem complete {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (dst src : Solidity.Storage.Loc)
 (captured : Store) (initial : WordStore)
 (before : Transport N hash locations captured initial)
 (covered : ∀ l ∈ writeSet N hash dst src initial ++ (readSet N hash dst src initial).tail,l ∈ locations)
 (safe : dst=src ∨ ∀ w ∈ writeSet N hash dst src initial,∀ r ∈ (readSet N hash dst src initial).tail,w≠r) :
 let sym1 := CopyTransport.symbolicCopy dst src captured
 let num1 := NumericTraversal.copy N hash dst src initial
 let sym2 := CopyTransport.symbolicCopy dst src sym1
 let num2 := NumericTraversal.copy N hash dst src num1
 Transport N hash locations sym1 num1 ∧ Transport N hash locations sym2 num2 ∧
 sym2=sym1 ∧ num2=num1 := by
 dsimp only
 let sym1 := CopyTransport.symbolicCopy dst src captured
 let num1 := NumericTraversal.copy N hash dst src initial
 have dstHeader : dst ∈ locations := covered dst (List.mem_append.mpr (Or.inl List.mem_cons_self))
 have srcHeader : src ∈ locations := by
  apply covered
  apply List.mem_append.mpr
  right
  change src ∈ src :: _
  exact List.mem_cons_self
 have sourceCovered : ∀ i<LifecycleNumeric.headerLength N hash src initial,Solidity.Storage.Loc.data src i ∈ locations := by
  intro i inside
  apply covered
  apply List.mem_append.mpr
  right
  change Solidity.Storage.Loc.data src i ∈ src :: (List.range _).map (Solidity.Storage.Loc.data src)
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,List.mem_range.mpr inside,rfl⟩)
 have visitedCovered : ∀ i<max (LifecycleNumeric.headerLength N hash dst initial) (LifecycleNumeric.headerLength N hash src initial),Solidity.Storage.Loc.data dst i ∈ locations := by
  intro i inside
  apply covered
  apply List.mem_append.mpr
  left
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,List.mem_range.mpr inside,rfl⟩)
 have oldDst : LifecycleNumeric.headerLength N hash dst initial=(captured dst).val.toNat := by
  simp only [LifecycleNumeric.headerLength,before dst dstHeader]
 have oldSrc : LifecycleNumeric.headerLength N hash src initial=(captured src).val.toNat := by
  simp only [LifecycleNumeric.headerLength,before src srcHeader]
 have first : Transport N hash locations sym1 num1 := CopyTransport.transported run dst src captured initial before dstHeader srcHeader
  (by simpa only [oldSrc] using sourceCovered) (by simpa only [oldDst,oldSrc] using visitedCovered)
 have currentLengths : LifecycleNumeric.headerLength N hash dst num1=LifecycleNumeric.headerLength N hash src initial ∧
  LifecycleNumeric.headerLength N hash src num1=LifecycleNumeric.headerLength N hash src initial := by
  rcases safe with same | separate
  · subst dst
    simp only [num1,NumericCopyCommutation.copy_self,and_self]
  · have facts := RuntimeCopyRepeat.headers_and_footprint run dst src initial covered separate
    exact ⟨facts.1,facts.2.1⟩
 have currentDst : (sym1 dst).val.toNat=LifecycleNumeric.headerLength N hash src initial := by
  have relation : LifecycleNumeric.headerLength N hash dst num1=(sym1 dst).val.toNat := by
   simp only [LifecycleNumeric.headerLength,first dst dstHeader]
  exact relation.symm.trans currentLengths.1
 have currentSrc : (sym1 src).val.toNat=LifecycleNumeric.headerLength N hash src initial := by
  have relation : LifecycleNumeric.headerLength N hash src num1=(sym1 src).val.toNat := by
   simp only [LifecycleNumeric.headerLength,first src srcHeader]
  exact relation.symm.trans currentLengths.2
 have nextSource : ∀ i<(sym1 src).val.toNat,Solidity.Storage.Loc.data src i ∈ locations := by
  simpa only [currentSrc] using sourceCovered
 have nextVisited : ∀ i<max (sym1 dst).val.toNat (sym1 src).val.toNat,Solidity.Storage.Loc.data dst i ∈ locations := by
  intro i inside
  rw [currentDst,currentSrc,Nat.max_self] at inside
  exact visitedCovered i (Nat.lt_of_lt_of_le inside (Nat.le_max_right _ _))
 have second := CopyTransport.transported run dst src sym1 num1 first dstHeader srcHeader nextSource nextVisited
 have numericEq := RuntimeCopyRepeat.copy_repeat run dst src initial covered safe
 have symbolicEq : CopyTransport.symbolicCopy dst src sym1=sym1 := by
  funext observer
  by_cases member : observer ∈ locations
  · exact (second observer member).symm.trans ((congrFun numericEq _).trans (first observer member))
  · have foldFrame : ∀ (ops : List (Solidity.Storage.Loc × Semantics.Word)) (seed : Store),
     (∀ op ∈ ops,op.1 ∈ locations) →
     (ops.foldl (fun w op => Representation.write w op.1 op.2) seed) observer=seed observer := by
     intro ops
     induction ops with
     | nil => intro seed _; rfl
     | cons op rest ih =>
       intro seed opsCovered
       simp only [List.foldl_cons]
       rw [ih _ (fun next inside => opsCovered next (List.mem_cons_of_mem _ inside))]
       apply Representation.write_other
       intro same
       apply member
       rw [same]
       exact opsCovered op List.mem_cons_self
    apply foldFrame
    intro op inside
    simp only [CopyTransport.updates,List.mem_append,List.mem_singleton] at inside
    rcases inside with bodyMember | rfl
    · obtain ⟨i,visited,rfl⟩:=List.mem_map.mp bodyMember
      exact nextVisited i (List.mem_range.mp visited)
    · exact dstHeader
 exact ⟨first,second,symbolicEq,numericEq⟩

/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyComposition.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms complete
end Solidity.Backend.StorageOps.RuntimeCopyComposition
