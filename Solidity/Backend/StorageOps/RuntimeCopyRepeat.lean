import Solidity.Backend.StorageOps.NumericCopyCommutation

/-! Actual runtime-header copy: the destination header is intentionally changed.
Only SOURCE reads must be framed. Original finite regions derive that frame,
then the second write footprint shrinks inside the first, without a count cap.
This is not Source lowering, an eager aggregate emitter or world rollback. -/
namespace Solidity.Backend.StorageOps.RuntimeCopyRepeat
open TypeGraph Solidity.Storage Solidity.Storage.Representation Solidity.Storage.Representation.Graph NumericCopyCommutation

/-- Both current headers and the next actual access footprint are derived from
initial generated coverage. The destination header is not assumed unchanged. -/
theorem headers_and_footprint {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (dst src : Solidity.Storage.Loc) (initial : WordStore)
 (covered : ∀ l ∈ writeSet N hash dst src initial ++ (readSet N hash dst src initial).tail,l ∈ locations)
 (separate : ∀ w ∈ writeSet N hash dst src initial,∀ r ∈ (readSet N hash dst src initial).tail,w≠r) :
 let after := NumericTraversal.copy N hash dst src initial
 LifecycleNumeric.headerLength N hash dst after=LifecycleNumeric.headerLength N hash src initial ∧
 LifecycleNumeric.headerLength N hash src after=LifecycleNumeric.headerLength N hash src initial ∧
 (readSet N hash dst src after).tail=(readSet N hash dst src initial).tail ∧
 (∀ l ∈ writeSet N hash dst src after,l ∈ writeSet N hash dst src initial) := by
 dsimp only
 have frame := copy_frames run dst src initial (readSet N hash dst src initial).tail covered separate
 have sourceMember : src ∈ (readSet N hash dst src initial).tail := by
  change src ∈ src :: (List.range (LifecycleNumeric.headerLength N hash src initial)).map (Solidity.Storage.Loc.data src)
  exact List.mem_cons_self
 have sourceWord := frame src sourceMember
 have dstLength : LifecycleNumeric.headerLength N hash dst (NumericTraversal.copy N hash dst src initial)=LifecycleNumeric.headerLength N hash src initial := by
  simp only [LifecycleNumeric.headerLength,NumericTraversal.copy_header]
 have srcLength : LifecycleNumeric.headerLength N hash src (NumericTraversal.copy N hash dst src initial)=LifecycleNumeric.headerLength N hash src initial := by
  simp only [LifecycleNumeric.headerLength,sourceWord]
 refine ⟨dstLength,srcLength,?_,?_⟩
 · simp only [readSet,srcLength]
 · intro l member
   simp only [writeSet,dstLength,srcLength,Nat.max_self,List.mem_cons,List.mem_map,List.mem_range] at member
   rcases member with rfl | ⟨i,inside,rfl⟩
   · exact List.mem_cons_self
   · apply List.mem_cons_of_mem
     apply List.mem_map.mpr
     exact ⟨i,List.mem_range.mpr (Nat.lt_of_lt_of_le inside (Nat.le_max_right _ _)),rfl⟩

/-- Whole numeric-store repetition of the UNCHANGED actual dynamic copy.
The first source length determines the smaller second loop; stale tails stay
cleared, older words stay exact, and exact aliases use the checked self law. -/
theorem copy_repeat {N L R : Nat} {hash : Solidity.Storage.Pre → Nat}
 {P : List Solidity.Storage.Pre} {locations : List Solidity.Storage.Loc}
 (run : FiniteRun N L R hash P locations) (dst src : Solidity.Storage.Loc) (initial : WordStore)
 (covered : ∀ l ∈ writeSet N hash dst src initial ++ (readSet N hash dst src initial).tail,l ∈ locations)
 (safe : dst=src ∨ ∀ w ∈ writeSet N hash dst src initial,∀ r ∈ (readSet N hash dst src initial).tail,w≠r) :
 NumericTraversal.copy N hash dst src (NumericTraversal.copy N hash dst src initial)=
 NumericTraversal.copy N hash dst src initial := by
 rcases safe with same | separate
 · subst dst
   simp only [NumericCopyCommutation.copy_self]
 · let after := NumericTraversal.copy N hash dst src initial
   let live := LifecycleNumeric.headerLength N hash src initial
   let count := max (LifecycleNumeric.headerLength N hash dst initial) live
   have facts := headers_and_footprint run dst src initial covered separate
   have frame := copy_frames run dst src initial (readSet N hash dst src initial).tail covered separate
   have dstCovered : dst ∈ locations := covered dst (List.mem_append.mpr (Or.inl List.mem_cons_self))
   have sourceMember : src ∈ (readSet N hash dst src initial).tail := by
    change src ∈ src :: (List.range live).map (Solidity.Storage.Loc.data src)
    exact List.mem_cons_self
   have sourceElement : ∀ i<live,Solidity.Storage.Loc.data src i ∈ (readSet N hash dst src initial).tail := by
    intro i inside
    change Solidity.Storage.Loc.data src i ∈ src :: (List.range live).map (Solidity.Storage.Loc.data src)
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,List.mem_range.mpr inside,rfl⟩)
   have oldVisited : ∀ i<count,Solidity.Storage.Loc.data dst i ∈ locations := by
    intro i inside
    apply covered
    apply List.mem_append.mpr
    left
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,List.mem_range.mpr inside,rfl⟩)
   have newVisited : ∀ i<max (LifecycleNumeric.headerLength N hash dst after) (LifecycleNumeric.headerLength N hash src after),Solidity.Storage.Loc.data dst i ∈ locations := by
    intro i inside
    rw [facts.1,facts.2.1,Nat.max_self] at inside
    exact oldVisited i (Nat.lt_of_lt_of_le inside (Nat.le_max_right _ _))
   funext a
   by_cases header : a=dst.word N hash
   · subst a
     simpa only [NumericTraversal.copy_header] using frame src sourceMember
   · by_cases touched : ∃ i,i<count ∧ a=(Solidity.Storage.Loc.data dst i).word N hash
     · obtain ⟨i,inside,rfl⟩:=touched
       have second := NumericTraversal.copy_element run dst src after i dstCovered (oldVisited i inside) newVisited
       dsimp only at second
       rw [facts.1,facts.2.1,Nat.max_self] at second
       change NumericTraversal.copy N hash dst src after ((Solidity.Storage.Loc.data dst i).word N hash)=
        (if i<live then (if i<live then after ((Solidity.Storage.Loc.data src i).word N hash) else ClearDemands.zero)
         else after ((Solidity.Storage.Loc.data dst i).word N hash)) at second
       by_cases copied : i<live
       · simp only [if_pos copied] at second
         rw [second]
         have first := NumericTraversal.copy_element run dst src initial i dstCovered (oldVisited i inside) oldVisited
         dsimp only at first
         change after ((Solidity.Storage.Loc.data dst i).word N hash)=
          (if i<count then (if i<live then initial ((Solidity.Storage.Loc.data src i).word N hash) else ClearDemands.zero)
           else initial ((Solidity.Storage.Loc.data dst i).word N hash)) at first
         simp only [if_pos inside,if_pos copied] at first
         exact (frame _ (sourceElement i copied)).trans first.symm
       · simp only [if_neg copied] at second
         exact second
     · apply NumericTraversal.copy_outside N hash dst src after a header
       intro i inside equal
       rw [facts.1,facts.2.1,Nat.max_self] at inside
       exact touched ⟨i,Nat.lt_of_lt_of_le inside (Nat.le_max_right _ _),equal⟩

/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyRepeat.headers_and_footprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms headers_and_footprint
/-- info: 'Solidity.Backend.StorageOps.RuntimeCopyRepeat.copy_repeat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copy_repeat
end Solidity.Backend.StorageOps.RuntimeCopyRepeat
