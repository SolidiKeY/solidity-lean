import Solidity.Yul.Views.RetainedIndices

namespace Solidity.Yul.Views

/-- Single actual inherited persistent root, with computed ACTIVE origin. This
is a placement certificate, not a final view/inverse/coverage assumption. -/
structure RetainedArrayLayout {E : Source.Env} {τ : Source.STy} {b : Bool}
    (child : RecursiveStorageDeclaration E τ b) (active : String) (a : Roadmap.Address) where
  origin : ActiveLayoutOrigin E active
  root : Source.DeclName
  ordered : inheritedRootNames E origin.hierarchy.order false = [root]
  sourceDistinct : ∀ scope ∈ origin.hierarchy.order, (allScopeRootNames E (some scope)).Nodup
  declared : E.rootTy root = some (.array .storage τ none)
  aggregate : τ.isValue = false

def prepareRetainedArrayLayout? {E τ b} (child : RecursiveStorageDeclaration E τ b)
    (active : String) (a : Roadmap.Address) (root : Source.DeclName) : Option (RetainedArrayLayout child active a) := do
  let origin ← (prepareActiveOrigin E active).toOption
  if sourceDistinct : ∀ scope ∈ origin.hierarchy.order, (allScopeRootNames E (some scope)).Nodup then
    if ordered : inheritedRootNames E origin.hierarchy.order false = [root] then
      if declared : E.rootTy root = some (.array .storage τ none) then
        if aggregate : τ.isValue = false then some ⟨origin,root,ordered,sourceDistinct,declared,aggregate⟩ else none
      else none
    else none
  else none

def RetainedArrayLayout.path {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a) : Source.SPath := ⟨r.root,[]⟩
def RetainedArrayLayout.cursor {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a) := r.origin.persistent.val*32

theorem RetainedArrayLayout.typed {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a) :
    E.pathTy r.path = some (.array .storage τ none) := r.declared

theorem RetainedArrayLayout.bank {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a) : E.transientRoot r.path = false := by
  have member : r.root ∈ inheritedRootNames E r.origin.hierarchy.order false := by rw [r.ordered]; exact List.mem_singleton_self _
  obtain ⟨scope,inside,selected⟩ := List.mem_flatMap.mp member
  exact ordinaryRootNames_bank (r.sourceDistinct scope inside) r.root selected

theorem RetainedArrayLayout.header_bound {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a) :
    ((dynamicHeaderSeed E).position (roundSlot r.cursor)).start/32<2^256 := by
  rw [dynamic_header_start]
  have aligned : r.cursor%32=0 := by unfold cursor; omega
  rw [roundSlot_aligned _ aligned]
  change r.origin.persistent.val*32/32<2^256
  rw [Nat.mul_div_cancel _ (by decide)]
  exact r.origin.persistent.isLt

def RetainedArrayLayout.header {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a) :
    ScalarPath E.layout (E.lay a) :=
  ((dynamicHeaderSeed E).position (roundSlot r.cursor)).registration r.path (aggregate_array_cell r.typed) a r.header_bound

theorem RetainedArrayLayout.header_path {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a) : r.header.path=r.path := rfl

def RetainedArrayLayout.childCursor {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a)
    (fixed : Roadmap.Evm.Fixed) (i : Nat) : Nat :=
  (fixedLayoutHash fixed (.data r.header.slot.val)+i*(AggregateStorageDeclaration.ordinary child).stride)*32

/-- Finite witnessed index formation. The index is recorded, never a desired
child coordinate/trace. Formation means an ACTUAL source indexLoc execution;
no assertion that every intrinsically constructible storRef has this history. -/
structure RetainedIndexEvent {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a) where
  index : Nat
  formed : ∃ (Γ : Source.RCtx) (F : Source.Fr) (s : Source.EMState E Γ), F.this=a ∧
    (Source.indexLoc (E := E) F (Source.Val.storRef (τ := .array .storage τ none) (by rfl) r.path) index).run s =
      (.ok (.stor (r.path.go (.index index))),s)

def recordRetainedIndex {E τ b child active a Γ} (r : @RetainedArrayLayout E τ b child active a)
    (F : Source.Fr) (s : Source.EMState E Γ) (i : Nat) (account : F.this=a)
    (formed : (Source.indexLoc (E := E) F (Source.Val.storRef (τ := .array .storage τ none) (by rfl) r.path) i).run s =
      (.ok (.stor (r.path.go (.index i))),s)) : RetainedIndexEvent r := ⟨i,Γ,F,s,account,formed⟩

/-- Histories have no imposed count/depth bound. Same-path aliases record real
separate events; their indices are deduplicated BEFORE codec construction. -/
abbrev RetainedIndexHistory {E τ b child active a} (r : @RetainedArrayLayout E τ b child active a) := List (RetainedIndexEvent r)

def retainedVisitIndices {E τ b child active a} {r : @RetainedArrayLayout E τ b child active a}
    (history : RetainedIndexHistory r) (length : Nat) : List Nat := uniqueVisitIndices [] (List.range length ++ history.map RetainedIndexEvent.index)

theorem retainedVisitIndices_mem {E τ b child active a} {r : @RetainedArrayLayout E τ b child active a}
    (history : RetainedIndexHistory r) (length i : Nat) :
    i ∈ retainedVisitIndices history length ↔ i<length ∨ ∃ event ∈ history, event.index=i := by
  simp only [retainedVisitIndices,uniqueVisitIndices_mem,List.not_mem_nil,not_false_eq_true,and_true,List.mem_append,List.mem_range,List.mem_map]

theorem retainedVisitIndices_unique {E τ b child active a} {r : @RetainedArrayLayout E τ b child active a}
    (history : RetainedIndexHistory r) (length : Nat) : (retainedVisitIndices history length).Nodup := uniqueVisitIndices_nodup _ _

end Solidity.Yul.Views
