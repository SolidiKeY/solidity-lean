import Solidity.Frontend.SolcJson.YulMetadataWords
import Solidity.Frontend.SolcJson.YulReferenceAttachment

/-! Actual original-ID selection to the declaration namespace used by existing
scoped typing. This is not a Source declaration-provider or JSON typed-use
alignment theorem. Explicit function visibility is retained where needed. -/
namespace Solidity.Frontend.YulJson.Names
open Solidity.Yul

private theorem original_member {α} {entries : List (String × α)} {name value}
    (binding : Resolves entries name value) : (name,value) ∈ entries := by
  induction binding with
  | head => exact List.mem_cons_self
  | tail _ _ ih => exact List.mem_cons_of_mem _ ih

private theorem resolve_consistent {α} (entries : List (String × α))
    (name : String) (value : α) (present : (name,value) ∈ entries)
    (consistent : ∀ other, (name,other) ∈ entries → other = value) :
    resolve entries name = some value := by
  induction entries with
  | nil => cases present
  | cons binding rest ih =>
      rcases binding with ⟨head,previous⟩
      by_cases same : name = head
      · subst head
        have equal := consistent previous List.mem_cons_self
        simp only [resolve,if_true,equal]
      · rw [resolve,if_neg same]
        apply ih
        · rcases List.mem_cons.mp present with first | later
          · exact False.elim (same (congrArg Prod.fst first))
          · exact later
        · exact fun other member => consistent other (List.mem_cons_of_mem _ member)

/-- The selected ORIGINAL identity really occurs in the namespace consumed by
ScopedExpressions; duplicate original spellings cannot expose an older ID. -/
theorem BindingD.declarations_binding {X table original name declaration}
    (binding : @BindingD X table original name declaration) :
    Resolves (declarations table original) name ⟨declaration.ty,declaration.index⟩ := by
  apply resolve_sound
  apply resolve_consistent
  · cases binding with
    | intro named identified =>
        let entry : Entry table original := ⟨name,declaration,.intro named identified⟩
        have present : entry ∈ entries table original := by
          apply List.mem_filterMap.mpr
          refine ⟨(name,_),original_member named,?_⟩
          unfold entry?
          rw [BindingD.complete (.intro named identified)]
          rfl
        exact List.mem_map.mpr ⟨entry,present,rfl⟩
  · intro other present
    obtain ⟨entry,_,equal⟩ := List.mem_map.mp present
    have nameEq : entry.visible = name := congrArg Prod.fst equal
    have valueEq := congrArg Prod.snd equal
    have selected : BindingD table original name entry.declaration := nameEq ▸ entry.selected
    have declarationEq : entry.declaration = declaration := selected.unique binding
    exact valueEq.symm.trans
      (congrArg (fun d : Declaration X => (⟨d.ty,d.index⟩ : ExternalDeclRef X)) declarationEq)

/-- A namespace hit comes from a genuinely selected original identity. -/
theorem declarations_lookup_sound {X table original name reference}
    (found : resolve (@declarations X table original) name = some reference) :
    ∃ declaration, BindingD table original name declaration ∧
      reference = (⟨declaration.ty,declaration.index⟩ : ExternalDeclRef X) := by
  have member := original_member (resolve_sound found)
  obtain ⟨entry,_,same⟩ := List.mem_map.mp member
  have nameEq : entry.visible = name := congrArg Prod.fst same
  have valueEq := congrArg Prod.snd same
  exact ⟨entry.declaration,nameEq ▸ entry.selected,valueEq.symm⟩

/-- Exact hit AND refusal correspondence to actual original-name selection.
Unknown/blocked first bindings cannot expose any older same-named declaration. -/
theorem declarations_lookup {X} (table : DeclarationTable X) (original : Original)
    (name : String) :
    resolve (declarations table original) name =
      (select table original name).map
        (fun selected => (⟨selected.val.ty,selected.val.index⟩ : ExternalDeclRef X)) := by
  cases chosen : select table original name with
  | none =>
      cases found : resolve (declarations table original) name with
      | none => rfl
      | some reference =>
          obtain ⟨declaration,binding,_⟩ := declarations_lookup_sound found
          have contradiction := binding.complete
          rw [chosen] at contradiction
          cases contradiction
  | some selected =>
      rw [resolve_complete selected.property.declarations_binding]
      rfl

end Solidity.Frontend.YulJson.Names

namespace Solidity.Frontend.YulJson.ReferenceAttachment
open Solidity.Yul

/-- Concrete root declaration lookup, suffix and access proof, all supplied by
the actual attachment certificate and existing original-namespace producer. -/
def Attached.external {X table original write node reference}
    (attached : @Attached X table original write node reference) :
    ExternalD (Names.declarations table original) write attached.visible attached.suffix attached.term :=
  .intro reference.declaration.index attached.original_binding.declarations_binding
    attached.spelling attached.access

/-- Function projection keeps its REAL scope visibility premise. No unavailable
local is promoted to a global and no older declaration is substituted. -/
def Attached.scoped {X current table original write node reference}
    (attached : @Attached X table original write node reference)
    (scope : ExternalScope X current) (index : Member current reference.declaration.ty)
    (visibility : ScopeIndexD scope reference.declaration.index index) :
    ScopedExternalD (Names.declarations table original) scope write attached.visible attached.suffix
      ⟨index,reference.attr,attached.access⟩ :=
  .intro attached.external visibility

/-- Final concrete root lookup discharges both canonical-name and visibility
premises using the ACTUAL input namespace and root index producer. -/
theorem Attached.root_lookup {X table original write node reference}
    (input : @MetadataWords.Input X table original)
    (attached : Attached table original write node reference) :
    resolve (ScopedNames.names (Names.declarations table original) .root write)
      (externalKey attached.visible attached.suffix) = some attached.term :=
  ScopedNames.lookup_complete input.names.canonical
    (attached.scoped .root reference.declaration.index (.root _))

/-- Concrete one-function projection for genuinely global declaration types. -/
theorem Attached.function_lookup {X table original write node reference}
    (input : @MetadataWords.Input X table original)
    (attached : Attached table original write node reference)
    (global : reference.declaration.ty.isGlobal = true) :
    resolve (ScopedNames.names (Names.declarations table original) (.function .root) write)
      (externalKey attached.visible attached.suffix) =
      some ⟨reference.declaration.index.intoGlobals global,reference.attr,attached.access⟩ :=
  ScopedNames.lookup_complete input.names.canonical
    (attached.scoped (.function .root) (reference.declaration.index.intoGlobals global)
      (.function (.root _) global))

/-- Actual non-global refusal uses the original binding before projection.
No older same-named global declaration is considered as a replacement. -/
theorem Attached.function_refused {X table original write node reference}
    (input : @MetadataWords.Input X table original)
    (attached : Attached table original write node reference)
    (nonglobal : reference.declaration.ty.isGlobal = false) :
    resolve (ScopedNames.names (Names.declarations table original) (.function .root) write)
      (externalKey attached.visible attached.suffix) = none := by
  have canonical := input.names.canonical attached.visible
    (ScopedNames.external_name_mem attached.external)
  rw [ScopedNames.lookup_agrees _ _ _ input.names.canonical _ _ canonical]
  have unavailable :
      (ExternalScope.function (.root : ExternalScope X X)).index
        reference.declaration.index = none := by
    simp only [ExternalScope.index,nonglobal,Bool.false_eq_true,reduceDIte]
  unfold checkScopedExternal
  rw [attached.external.complete]
  simp only [Attached.term,bind,Option.bind,unavailable,Option.map_none]

end Solidity.Frontend.YulJson.ReferenceAttachment
