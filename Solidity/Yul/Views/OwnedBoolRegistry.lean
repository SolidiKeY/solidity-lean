import Solidity.Yul.Views.OwnedBoolJournal
import Solidity.Yul.Views.InheritedDeclarationLaws

namespace Solidity.Yul.Views

def ownedByteKey {D L} (transient : Bool) (account : Roadmap.Address) (c : ScalarPath D L) : OwnedByteKey :=
  ⟨transient,account,c.slot,⟨c.field.offset,by have p:=c.field.positive; have f:=c.field.fits; omega⟩⟩

theorem ScalarPath.bool_width {D L} (c : ScalarPath D L) (typed : L c.path=.bool) : c.field.width=1 := by
  have width := c.width
  rw [typed] at width
  have only : ∀ n, StorageWidth D .bool n → n=1 := by
    intro n witness
    cases witness
    rfl
  exact only _ width

/-- Preserve actual path/slot/width and registration. Only the represented
physical bool encoder changes. Other actual source types reuse their codec. -/
def representedPath {D L} (c : ScalarPath D L) (code : BoolTrueByte) : ScalarPath D L :=
  if typed : L c.path=.bool then
    {c with codec:=typed.symm ▸ representedBoolCodec D c.field (c.bool_width typed) code}
  else c

theorem representedPath_path {D L} (c : ScalarPath D L) (code) : (representedPath c code).path=c.path := by
  unfold representedPath; split <;> rfl

theorem representedPath_slot {D L} (c : ScalarPath D L) (code) : (representedPath c code).slot=c.slot := by
  unfold representedPath; split <;> rfl

theorem representedPath_field {D L} (c : ScalarPath D L) (code) : (representedPath c code).field=c.field := by
  unfold representedPath; split <;> rfl

def representedRegistry {D L} (cs : List (ScalarPath D L)) (transient : Bool) (account : Roadmap.Address)
    (encoding : BoolEncodingJournal) : List (ScalarPath D L) :=
  cs.map fun c => representedPath c (encoding.cells (ownedByteKey transient account c))

theorem representedRegistry_paths {D L} (cs : List (ScalarPath D L)) (tr) (a) (encoding) :
    (representedRegistry cs tr a encoding).map ScalarPath.path=cs.map ScalarPath.path := by
  simp only [representedRegistry,List.map_map,Function.comp_def,representedPath_path]

theorem representedRegistry_separated {D L} (cs : List (ScalarPath D L)) (tr) (a) (encoding)
    (separated : finiteSeparated cs) : finiteSeparated (representedRegistry cs tr a encoding) := by
  apply List.pairwise_map.mpr
  apply separated.imp
  intro c d apart
  simp only [representedPath_path,pathsApart,representedPath_slot,representedPath_field] at apart ⊢
  exact apart

theorem ownedByteKey_distinct {D L} (c d : ScalarPath D L) (tr) (a) (apart : pathsApart c d) :
    ownedByteKey tr a c ≠ ownedByteKey tr a d := by
  intro same
  have slot := congrArg OwnedByteKey.slot same
  have offset := congrArg (fun key : OwnedByteKey => key.offset.val) same
  change c.slot=d.slot at slot
  change c.field.offset=d.field.offset at offset
  rcases apart with different | above | below
  · exact different slot
  · have positive:=c.field.positive; omega
  · have positive:=d.field.positive; omega

/-- Actual inherited declaration computation is the provenance of locations.
No caller-supplied slot adequacy law or replacement planner. -/
def CheckedInheritedDeclarations.represented {E ds d active tr a origin}
    (r : @CheckedInheritedDeclarations E ds d active tr a origin) (encoding : BoolEncodingJournal) :=
  representedRegistry r.registrations tr a encoding

theorem CheckedInheritedDeclarations.represented_separated {E ds d active tr a origin}
    (r : @CheckedInheritedDeclarations E ds d active tr a origin) (encoding : BoolEncodingJournal) :
    finiteSeparated (r.represented encoding) := representedRegistry_separated _ _ _ _ r.separated

theorem CheckedInheritedDeclarations.represented_paths {E ds d active tr a origin}
    (r : @CheckedInheritedDeclarations E ds d active tr a origin) (encoding : BoolEncodingJournal) :
    (r.represented encoding).map ScalarPath.path=d.paths := by
  unfold CheckedInheritedDeclarations.represented
  rw [representedRegistry_paths,r.coverage]

end Solidity.Yul.Views
