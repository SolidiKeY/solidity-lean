import Solidity.Frontend.SolcJson.YulNames

/-! Per-occurrence attachment to actual JSON YulIdentifier metadata. The role
is an explicit index, not inferred from caller intent. A later whole-AST walk
must supply the actual read/assignment role and account for every reference.
This module proves exactly span/name/ID/suffix/capability attachment for the
given node, original namespace and typed reference, not Source provenance,
whole-block completeness, function visibility or admission. -/
namespace Solidity.Frontend.YulJson.ReferenceAttachment
open Lean (Json)
open Solidity.Yul

inductive Error where
  | json (reason : YulJson.Error)
  | span
  | suffix
  | identity
  | capability
  deriving Repr

/-- Independent real metadata/namespace equations and intrinsically indexed
read/write access. Stored declaration spelling may differ from a visible alias. -/
structure Attached {X} (table : DeclarationTable X) (original : Names.Original)
    (write : Bool) (node : Json) (reference : Reference table) where
  visible : String
  suffix : List String
  identifier_eq : identifierPath node = .ok (visible,suffix)
  rawSpan : String
  rawSpan_eq : string node "src" = .ok rawSpan
  span_eq : sourceSpan rawSpan = .ok reference.source
  suffix_eq : suffix = reference.suffix
  named : Names.ReferenceD table original visible reference
  access : Access reference.declaration.ty reference.attr write

private def witnessed {α : Type} (result : Except YulJson.Error α) :
    Except Error {value : α // result = .ok value} :=
  match result with
  | .error reason => .error (.json reason)
  | .ok value => .ok ⟨value,rfl⟩

def check {X} (table : DeclarationTable X) (original : Names.Original)
    (write : Bool) (node : Json) (reference : Reference table) :
    Except Error (Attached table original write node reference) := do
  let ⟨(visible,suffix),identifier_eq⟩ ← witnessed (identifierPath node)
  let ⟨rawSpan,rawSpan_eq⟩ ← witnessed (string node "src")
  let ⟨source,source_eq⟩ ← witnessed (sourceSpan rawSpan)
  if same : source = reference.source then
    if suffix_eq : suffix = reference.suffix then
      match Names.checkReference table original visible reference with
      | none => .error .identity
      | some named =>
          match checkAccess reference.declaration.ty reference.attr write with
          | none => .error .capability
          | some access => .ok ⟨visible,suffix,identifier_eq,rawSpan,rawSpan_eq,
              source_eq.trans (congrArg Except.ok same),suffix_eq,named,access⟩
    else .error .suffix
  else .error .span

private theorem witnessed_complete {α : Type} (result : Except YulJson.Error α)
    (value : α) (actual : result = .ok value) :
    witnessed result = .ok ⟨value,actual⟩ := by subst result; rfl

/-- Completeness against the independent attachment fields, preserving the
actual role/access index and first original-name lookup. -/
theorem Attached.complete {X table original write node reference}
    (attached : @Attached X table original write node reference) :
    check table original write node reference = .ok attached := by
  cases attached with
  | mk visible suffix identifier_eq rawSpan rawSpan_eq span_eq suffix_eq named access =>
      simp only [check,witnessed_complete _ _ identifier_eq,
        witnessed_complete _ _ rawSpan_eq,witnessed_complete _ _ span_eq,
        bind,Except.bind,dif_pos True.intro,
        dif_pos suffix_eq,named.complete,access.complete]

theorem check_iff {X} (table : DeclarationTable X) (original : Names.Original)
    (write : Bool) (node : Json) (reference : Reference table) :
    (check table original write node reference).isOk = true ↔
      Nonempty (Attached table original write node reference) := by
  constructor
  · intro valid
    cases actual : check table original write node reference with
    | error reason => rw [actual] at valid; cases valid
    | ok attached => exact ⟨attached⟩
  · rintro ⟨attached⟩
    rw [attached.complete]
    rfl

/-- Actual root-context intrinsic reference with the checked access direction. -/
def Attached.term {X table original write node reference}
    (attached : @Attached X table original write node reference) : ExternalRef X write :=
  ⟨reference.declaration.index,reference.attr,attached.access⟩

theorem Attached.declaration_identity {X table original write node reference}
    (_attached : @Attached X table original write node reference) :
    reference.declarationId = reference.declaration.id :=
  reference.identified.id_eq

theorem Attached.original_binding {X table original write node reference}
    (attached : @Attached X table original write node reference) :
    Names.BindingD table original attached.visible reference.declaration :=
  attached.named.binding

theorem Attached.spelling {X table original write node reference}
    (attached : @Attached X table original write node reference) :
    SuffixD attached.suffix reference.attr := by
  rw [attached.suffix_eq]
  exact reference.spelled

end Solidity.Frontend.YulJson.ReferenceAttachment
