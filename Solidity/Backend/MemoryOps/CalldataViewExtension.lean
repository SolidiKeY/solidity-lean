import Solidity.Backend.MemoryOps.CalldataViewPacking
import Solidity.Backend.AbiEntry.Premises.CalldataViewExtensions
import Init.Data.List.Nat.Basic

/-! Structural extension of supplied typed views. Existing captured logical
keys are retained even when the prior packing uses arbitrary sparse keys.
This is not a decoder, native access theorem or emitted copy program. -/
namespace Solidity.Backend.MemoryOps
open Solidity.Backend.AbiEntry.Premises

def calldataViewFreshBase {D : Source.Layout} {bytes : List UInt8}
    {views : List (CalldataView D)} (prior : V11G34_PackedViews bytes views) : Nat :=
  (List.ofFn prior.key).max?.getD 0+1

theorem calldataViewFreshBase_bound {D : Source.Layout} {bytes : List UInt8}
    {views : List (CalldataView D)} (prior : V11G34_PackedViews bytes views)
    (i : Fin views.length) : prior.key i<calldataViewFreshBase prior := by
  have member : prior.key i ∈ List.ofFn prior.key := List.mem_ofFn.mpr ⟨i,rfl⟩
  have bound := List.le_max?_getD_of_mem (k := 0) member
  unfold calldataViewFreshBase
  omega

def calldataViewExtendedKey {D : Source.Layout} {bytes : List UInt8}
    {views : List (CalldataView D)} (prior : V11G34_PackedViews bytes views)
    (additional : List (CalldataView D)) (i : Fin (views++additional).length) : Nat :=
  let k := calldataViewKey (views++additional) i
  if h : k<views.length then prior.key ⟨k,h⟩ else calldataViewFreshBase prior+k

theorem calldataViewExtendedKey_aliases {D : Source.Layout} {bytes : List UInt8}
    {views : List (CalldataView D)} (prior : V11G34_PackedViews bytes views)
    (additional : List (CalldataView D)) (i j : Fin (views++additional).length) :
    calldataViewExtendedKey prior additional i=calldataViewExtendedKey prior additional j ↔
      (views++additional)[i.val].type=(views++additional)[j.val].type ∧
      (views++additional)[i.val].rawOffset=(views++additional)[j.val].rawOffset ∧
      (views++additional)[i.val].rawLength=(views++additional)[j.val].rawLength := by
  rw [←calldataViewIdentity_eq]
  constructor
  · intro same
    have left := calldataViewKey_identity (views++additional) i
    have right := calldataViewKey_identity (views++additional) j
    unfold calldataViewExtendedKey at same
    dsimp only at same
    split at same <;> split at same
    · have oldSame := (prior.aliases _ _).mp same
      have identities := (calldataViewIdentity_eq _ _).mpr oldSame
      rw [←left,←right]
      rw [List.getElem_append_left (by assumption),List.getElem_append_left (by assumption)]
      exact identities
    · have bound := calldataViewFreshBase_bound prior
        ⟨calldataViewKey (views++additional) i,by assumption⟩
      omega
    · have bound := calldataViewFreshBase_bound prior
        ⟨calldataViewKey (views++additional) j,by assumption⟩
      omega
    · have eqKeys : calldataViewKey (views++additional) i=calldataViewKey (views++additional) j := by omega
      exact (calldataViewIdentity_eq _ _).mpr
        ((calldataViewKey_aliases (views++additional) i j).mp eqKeys)
  · intro identities
    have eqKeys := (calldataViewKey_aliases (views++additional) i j).mpr
      ((calldataViewIdentity_eq _ _).mp identities)
    unfold calldataViewExtendedKey
    simp only [eqKeys]

theorem calldataViewExtendedKey_prefix {D : Source.Layout} {bytes : List UInt8}
    {views : List (CalldataView D)} (prior : V11G34_PackedViews bytes views)
    (additional : List (CalldataView D)) (old : Fin views.length)
    (new : Fin (views++additional).length) (same : old.val=new.val) :
    prior.key old=calldataViewExtendedKey prior additional new := by
  have element : (views++additional)[new.val]=views[old.val] := by
    simp only [←same]
    exact List.getElem_append_left old.isLt
  have canonical : calldataViewKey (views++additional) new=calldataViewKey views old := by
    unfold calldataViewKey
    rw [element,List.findIdx_append]
    exact if_pos (calldataViewKey_bound views old)
  unfold calldataViewExtendedKey
  dsimp only
  rw [canonical,dif_pos (calldataViewKey_bound views old)]
  apply (prior.aliases old _).mpr
  exact (calldataViewIdentity_eq _ _).mp (calldataViewKey_identity views old).symm

def keyedCalldataViews {D : Source.Layout} (bytes : List UInt8)
    (views : List (CalldataView D)) (key : Fin views.length → Nat) : Source.Calldata D :=
  { input := bytes
    objects := fun k => ((List.finRange views.length).find? (fun i => decide (key i=k))).map
      (fun i => ⟨views[i.val].type,views[i.val].contents⟩) }

theorem keyedCalldataViews_lookup {D : Source.Layout} (bytes : List UInt8)
    (views : List (CalldataView D)) (key : Fin views.length → Nat)
    (aliases : ∀ i j,key i=key j ↔ calldataViewIdentity views[i.val]=calldataViewIdentity views[j.val])
    (coherent : V11G34_ViewCoherence views) (i : Fin views.length) :
    (keyedCalldataViews bytes views key).objects (key i)=some ⟨views[i.val].type,views[i.val].contents⟩ := by
  unfold keyedCalldataViews
  dsimp only
  cases found : (List.finRange views.length).find? (fun j => decide (key j=key i)) with
  | none =>
    have absent := List.find?_eq_none.mp found i
      (show i ∈ List.finRange views.length from List.mem_ofFn.mpr ⟨i,rfl⟩)
    exact False.elim (absent (decide_eq_true rfl))
  | some j =>
    have keyEq : key j=key i := of_decide_eq_true (List.find?_some (p := fun j => decide (key j=key i)) found)
    obtain ⟨typeEq,offsetEq,lengthEq⟩ := (calldataViewIdentity_eq _ _).mp ((aliases j i).mp keyEq)
    apply congrArg some
    exact Sigma.ext typeEq (coherent.coherent j i typeEq offsetEq lengthEq)

/-- Extend an arbitrary valid prior packing, preserving its captured keys. -/
def extendCalldataViews {D : Source.Layout} (bytes : List UInt8)
    (views additional : List (CalldataView D)) (prior : V11G34_PackedViews bytes views)
    (coherent : V11G34_ViewCoherence (views++additional)) : V11G34_ViewExtension prior additional :=
  { grown :=
      { calldata := keyedCalldataViews bytes (views++additional) (calldataViewExtendedKey prior additional)
        key := calldataViewExtendedKey prior additional
        rawReference := fun i => .cdRef (views++additional)[i.val].location
          (views++additional)[i.val].rawOffset (views++additional)[i.val].rawLength
        input_exact := rfl
        raw_exact := fun _ => rfl
        lookup := keyedCalldataViews_lookup bytes (views++additional) _
          (fun i j => (calldataViewExtendedKey_aliases prior additional i j).trans
            (calldataViewIdentity_eq _ _).symm) coherent
        aliases := calldataViewExtendedKey_aliases prior additional }
    prefix_keys := calldataViewExtendedKey_prefix prior additional }

def overlappingCalldataViewsV2 (D : Source.Layout) : V11G34_OverlappingCalldataViewsV2 D :=
  { toV11G34_OverlappingCalldataViews := overlappingCalldataViews D
    extend := extendCalldataViews }
/-- info: 'Solidity.Backend.MemoryOps.calldataViewFreshBase_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms calldataViewFreshBase_bound
/-- info: 'Solidity.Backend.MemoryOps.calldataViewExtendedKey_aliases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms calldataViewExtendedKey_aliases
/-- info: 'Solidity.Backend.MemoryOps.calldataViewExtendedKey_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms calldataViewExtendedKey_prefix
/-- info: 'Solidity.Backend.MemoryOps.keyedCalldataViews_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms keyedCalldataViews_lookup
/-- info: 'Solidity.Backend.MemoryOps.overlappingCalldataViewsV2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms overlappingCalldataViewsV2
end Solidity.Backend.MemoryOps
