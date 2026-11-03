import Solidity.Yul.BlockHeaders
import Solidity.Yul.ReservedNames
import Solidity.Frontend.Checked.Lexer

/-! Declaration-name checks use G08's existing whole-lexeme Yul classifier,
not another lexer. They strengthen direct source-header preparation; complete
block/body environment construction and provenance remain separate. -/
namespace Solidity.Yul
open Solidity.Frontend.Checked

def nameBytes (name : String) : Solidity.Frontend.Checked.Bytes := name.toUTF8.data.toList

/-- Inline-only reservations from pinned ReferencesResolver, separate from
Osaka EVMDialect reservations. -/
def inlineReservedNames : List String := ["this", "super", "_"]

/-- Existing lexical classification, independent builtin absence, and absence
from the distinct pinned strict-inline reservation table. -/
structure NameD (name : String) : Prop where
  lexical : yulTok (nameBytes name) = some (.ident name)
  noBuiltin : NoBuiltin name
  noReserved : name ∉ reservedNames
  noInlineReserved : name ∉ inlineReservedNames

def checkName (name : String) : Bool :=
  if name ∈ reservedNames then false else
  if name ∈ inlineReservedNames then false else
  match yulTok (nameBytes name) with
  | some (.ident actual) => actual == name && (lookupBuiltin name).isNone
  | _ => false

theorem checkName_iff (name : String) : checkName name = true ↔ NameD name := by
  constructor
  · intro h
    unfold checkName at h
    split at h
    · cases h
    · next hn =>
      split at h
      · cases h
      · next hi =>
        split at h
        · next actual ht =>
          have hp := Bool.and_eq_true_iff.mp h
          have he : actual = name := beq_iff_eq.mp hp.1
          subst actual
          exact ⟨ht, lookup_none_sound (Option.isNone_iff_eq_none.mp hp.2), hn, hi⟩
        · cases h
  · intro d
    unfold checkName
    rw [if_neg d.noReserved, if_neg d.noInlineReserved, d.lexical]
    change (name == name && (lookupBuiltin name).isNone) = true
    rw [lookup_none_complete d.noBuiltin]
    exact Bool.and_eq_true_iff.mpr ⟨beq_self_eq_true name, rfl⟩

theorem checkName_reserved {name : String} (h : name ∈ reservedNames) : checkName name = false := by
  unfold checkName
  rw [if_pos h]

/-- Names are fresh against ALL supplied visible names, including unavailable
outer locals inside function bodies, and are individually legal declarations. -/
structure NamesD (visible names : List String) : Prop where
  fresh : Fresh visible names
  legal : ∀ name ∈ names, NameD name

def checkNames (visible names : List String) : Bool :=
  fresh visible names && names.all checkName

theorem checkNames_iff (visible names : List String) :
    checkNames visible names = true ↔ NamesD visible names := by
  unfold checkNames
  rw [Bool.and_eq_true, fresh_iff, List.all_eq_true]
  constructor
  · intro h; exact ⟨h.1, fun name hm => (checkName_iff name).mp (h.2 name hm)⟩
  · intro h; exact ⟨h.fresh, fun name hm => (checkName_iff name).mpr (h.legal name hm)⟩

/-- Independent legal direct-header relation over ORIGINAL source syntax. -/
structure LegalHeadersD (visible : List String) (body : Solidity.Source.Syn (.list .yulStmt))
    (headers : List (String × Sig)) : Prop where
  collected : HeadersD body headers
  names : NamesD visible (headers.map Prod.fst)

def checkLegalHeaders (visible : List String) (body : Solidity.Source.Syn (.list .yulStmt)) :
    Option (List (String × Sig)) :=
  let headers := collectHeaders body
  if checkNames visible (headers.map Prod.fst) then some headers else none

theorem checkLegalHeaders_sound {visible body headers}
    (h : checkLegalHeaders visible body = some headers) : LegalHeadersD visible body headers := by
  unfold checkLegalHeaders at h
  dsimp only at h
  split at h
  · next hn =>
    cases h
    exact ⟨collectHeaders_sound body, (checkNames_iff _ _).mp hn⟩
  · cases h

theorem LegalHeadersD.complete {visible body headers}
    (d : LegalHeadersD visible body headers) : checkLegalHeaders visible body = some headers := by
  unfold checkLegalHeaders
  dsimp only
  rw [d.collected.complete]
  rw [if_pos ((checkNames_iff _ _).mpr d.names)]

theorem checkLegalHeaders_iff (visible : List String) (body : Solidity.Source.Syn (.list .yulStmt))
    (headers : List (String × Sig)) :
    checkLegalHeaders visible body = some headers ↔ LegalHeadersD visible body headers :=
  ⟨checkLegalHeaders_sound, LegalHeadersD.complete⟩

def LegalHeadersD.checked {visible body headers} (d : LegalHeadersD visible body headers) :
    CheckedHeaders visible body := ⟨headers, d.collected, d.names.fresh⟩

theorem LegalHeadersD.callable {visible body headers F sig i name}
    (d : LegalHeadersD visible body headers) (older : FunctionNames F)
    (named : NamedFunction headers (s := sig) i name) :
    NoBuiltin name ∧
      resolve (d.checked.hoist older) name = some ⟨sig, i.append F⟩ :=
  ⟨(d.names.legal name named.mem).noBuiltin, d.checked.hoist_new older named⟩

end Solidity.Yul
