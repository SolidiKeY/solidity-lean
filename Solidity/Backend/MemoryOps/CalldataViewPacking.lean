import Solidity.Backend.AbiEntry.Premises.CalldataViews
import Solidity.Source.Value

/-! Finite structural packing of supplied coherent typed views into the EXISTING
Source.Calldata. Equality uses the published Source.STy.same decider;
this is structural view packing, not an ABI decoder or path compiler.
No payload is decoded or validated here; G40 supplies demanded-view coherence. -/
namespace Solidity.Backend.MemoryOps
open Solidity.Backend.AbiEntry.Premises

/-- The exact typed raw identity from the published view contract. -/
def calldataViewIdentity {D : Source.Layout} (v : CalldataView D) : Source.STy × Nat × Nat :=
  (v.type,v.rawOffset,v.rawLength)

theorem calldataViewIdentity_eq {D : Source.Layout} (v w : CalldataView D) :
    calldataViewIdentity v=calldataViewIdentity w ↔
      v.type=w.type ∧ v.rawOffset=w.rawOffset ∧ v.rawLength=w.rawLength := by
  simp only [calldataViewIdentity,Prod.mk.injEq]

/-- First representative of the exact identity class. There is no view-count
or canonical-layout cutoff; keys are logical, not physical raw offsets. -/
def calldataViewKey {D : Source.Layout} (views : List (CalldataView D))
    (i : Fin views.length) : Nat :=
  views.findIdx (fun v => decide (calldataViewIdentity v=calldataViewIdentity views[i.val]))

theorem calldataViewKey_bound {D : Source.Layout} (views : List (CalldataView D))
    (i : Fin views.length) : calldataViewKey views i<views.length := by
  unfold calldataViewKey
  apply List.findIdx_lt_length_of_exists
  exact ⟨views[i.val],List.getElem_mem i.isLt,decide_eq_true rfl⟩

theorem calldataViewKey_identity {D : Source.Layout} (views : List (CalldataView D))
    (i : Fin views.length) :
    calldataViewIdentity (views[calldataViewKey views i]'(calldataViewKey_bound views i))=
      calldataViewIdentity views[i.val] := by
  unfold calldataViewKey
  apply of_decide_eq_true
  exact List.findIdx_getElem (w := calldataViewKey_bound views i)

theorem calldataViewKey_aliases {D : Source.Layout} (views : List (CalldataView D))
    (i j : Fin views.length) : calldataViewKey views i=calldataViewKey views j ↔
      views[i.val].type=views[j.val].type ∧ views[i.val].rawOffset=views[j.val].rawOffset ∧
        views[i.val].rawLength=views[j.val].rawLength := by
  rw [←calldataViewIdentity_eq]
  constructor
  · intro same
    have first := calldataViewKey_identity views i
    have second := calldataViewKey_identity views j
    have representatives : calldataViewIdentity (views[calldataViewKey views i]'(calldataViewKey_bound views i))=
        calldataViewIdentity (views[calldataViewKey views j]'(calldataViewKey_bound views j)) := by
      simp only [same]
    exact first.symm.trans (representatives.trans second)
  · intro same
    unfold calldataViewKey
    simp only [same]

/-- Finite position table. Uncaptured positions may contain redundant entries;
only captured logical keys have the alias/lookup contract. Outside is None. -/
def calldataViewTable {D : Source.Layout} (input : List UInt8) (views : List (CalldataView D)) :
    Source.Calldata D :=
  { input := input
    objects := fun key => if h : key<views.length then some ⟨views[key].type,views[key].contents⟩ else none }

theorem calldataViewTable_lookup {D : Source.Layout} (input : List UInt8) (views : List (CalldataView D))
    (coherent : V11G34_ViewCoherence views) (i : Fin views.length) :
    (calldataViewTable input views).objects (calldataViewKey views i)=some ⟨views[i.val].type,views[i.val].contents⟩ := by
  unfold calldataViewTable
  dsimp only
  rw [dif_pos (calldataViewKey_bound views i)]
  apply congrArg some
  obtain ⟨typeEq,offsetEq,lengthEq⟩ := (calldataViewIdentity_eq _ _).mp (calldataViewKey_identity views i)
  exact Sigma.ext typeEq (coherent.coherent ⟨calldataViewKey views i,calldataViewKey_bound views i⟩ i typeEq offsetEq lengthEq)

/-- Actual universally quantified V1 structural producer. It neither assumes a
packed result nor supplies ABI bytes, runtime execution or a decoder instance. -/
def packCalldataViews {D : Source.Layout} (input : List UInt8)
    (views : List (CalldataView D)) (coherent : V11G34_ViewCoherence views) : V11G34_PackedViews input views :=
  { calldata := calldataViewTable input views
    key := calldataViewKey views
    rawReference := fun i => .cdRef views[i.val].location views[i.val].rawOffset views[i.val].rawLength
    input_exact := rfl
    raw_exact := fun _ => rfl
    lookup := calldataViewTable_lookup input views coherent
    aliases := calldataViewKey_aliases views }

def overlappingCalldataViews (D : Source.Layout) : V11G34_OverlappingCalldataViews D :=
  ⟨packCalldataViews⟩

/-- info: 'Solidity.Backend.MemoryOps.calldataViewIdentity_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms calldataViewIdentity_eq
/-- info: 'Solidity.Backend.MemoryOps.calldataViewKey_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms calldataViewKey_bound
/-- info: 'Solidity.Backend.MemoryOps.calldataViewKey_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms calldataViewKey_identity
/-- info: 'Solidity.Backend.MemoryOps.calldataViewKey_aliases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms calldataViewKey_aliases
/-- info: 'Solidity.Backend.MemoryOps.calldataViewTable_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms calldataViewTable_lookup
/-- info: 'Solidity.Backend.MemoryOps.overlappingCalldataViews' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms overlappingCalldataViews
end Solidity.Backend.MemoryOps
