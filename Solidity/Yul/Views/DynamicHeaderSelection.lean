import Solidity.Yul.Views.DynamicSource

namespace Solidity.Yul.Views

theorem DynamicHeader.proof_irrel {E root cursor} (h g : DynamicHeader E root cursor) : h = g := by
  cases h
  cases g
  rfl

/-- Executable extraction from the actual computed dynamic-head trace. No
source values, final slots or readback laws are supplied by the caller. -/
def ComputedStorage.header? {E ds d active a} (r : @ComputedStorage E ds d active a) (root : Source.DeclName) :
    Option {cursor : Nat // DynamicHeader E root cursor} := do
  let (_,cursor) ← r.headerTrace.find? (fun entry => entry.1 == root)
  if declared : E.rootTy root = some (.array .storage (.int .u256) none) then
    if bounded : ((dynamicHeaderSeed E).position (roundSlot cursor)).start/32 < 2^256 then
      some ⟨cursor,⟨declared,bounded⟩⟩
    else none
  else none

theorem ComputedStorage.header_selected {E ds d active a} (r : @ComputedStorage E ds d active a)
    (root : Source.DeclName) (cursor : Nat) (h : DynamicHeader E root cursor)
    (selected : r.header? root = some ⟨cursor,h⟩) :
    (root,cursor) ∈ r.headerTrace ∧ h.registration a ∈ r.registrations := by
  unfold header? at selected
  obtain ⟨entry,found,result⟩ := Option.bind_eq_some_iff.mp selected
  rcases entry with ⟨name,incoming⟩
  have flag := List.find?_some found
  change (name == root) = true at flag
  have sameName : name = root := beq_iff_eq.mp flag
  subst name
  dsimp only at result
  split at result
  · split at result
    · have same : incoming = cursor := congrArg Subtype.val (Option.some.inj result)
      subst cursor
      have member := List.mem_of_find?_eq_some found
      obtain ⟨g,gm⟩ := r.header_present root incoming member
      rw [g.proof_irrel h] at gm
      exact ⟨member,gm⟩
    · cases result
  · cases result

theorem StorageDeclarations.header_roots {E ds} (d : StorageDeclarations E ds) (cursor : Nat) :
    List.Sublist ((d.headers cursor).map Prod.fst) (ds.map Prod.fst) := by
  induction d generalizing cursor with
  | nil => exact .slnil
  | @cons root τ rest head tail ih =>
    cases head with
    | fixed fixed => exact List.Sublist.cons root (ih (fixed.endByte cursor))
    | uintArray => exact List.Sublist.cons₂ root (ih ((StorageDeclaration.uintArray (E := E)).endByte cursor))

theorem ComputedStorage.headers_unique {E ds d active a} (r : @ComputedStorage E ds d active a) :
    (r.headerTrace.map Prod.fst).Nodup := (d.header_roots _).nodup r.distinct

end Solidity.Yul.Views
