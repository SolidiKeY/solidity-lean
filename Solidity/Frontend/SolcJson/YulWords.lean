import Solidity.Frontend.SolcJson.YulSafety
import Solidity.Yul.WordSyntax

/-!
# Closed JSON word preparation

This composes existing decoders with intrinsic static/policy checking. It does
not install frontend admission. Decoder equalities are real premises, not an
independent JSON specification. Supplied empty references do not establish
source occurrence attachment; outside names remain a caller input. Spans are
syntactic only. Metadata safety is neither MemOK nor source-comment provenance.
The canonical rethrow continues through its existing, separate Body path.
-/
namespace Solidity.Frontend.YulJson.Words
open Lean (Json)
open Solidity.Yul

def emptyDeclarations : DeclarationTable [] := ⟨[], by decide⟩

theorem declaration_impossible (d : Declaration []) : False := by
  have index := d.index
  cases index

theorem reference_impossible (r : Reference emptyDeclarations) : False :=
  declaration_impossible r.declaration

theorem references_empty (r : References emptyDeclarations) : r.entries = [] := by
  cases h : r.entries with
  | nil => rfl
  | cons first rest => exact False.elim (reference_impossible first)

inductive Error where
  | json (reason : YulJson.Error)
  | safety (reason : Refusal)
  | words (reason : WordSyntax.Error)
  deriving Repr

/-- A successful value retains the exact input decoder equations alongside
independent safety, syntax and policy certificates. None supplies Source IDs. -/
structure Checked (outside : List String) (bound : Nat) (node : Json) where
  imported : Metadata emptyDeclarations
  imported_eq : metadata emptyDeclarations node = .ok imported
  rawSpan : String
  rawSpan_eq : string node "src" = .ok rawSpan
  span : SourceSpan
  span_eq : sourceSpan rawSpan = .ok span
  ast : Json
  ast_eq : field node "AST" = .ok ast
  shaped : ShapedBlock bound ast
  safe : SafetyCertificate imported.flags imported.documentation
  prepared : WordSyntax.Prepared outside shaped.tree

private def witnessed {α : Type} (result : Except YulJson.Error α) :
    Except Error {value : α // result = .ok value} :=
  match result with
  | .error reason => .error (.json reason)
  | .ok value => .ok ⟨value, rfl⟩

def check (outside : List String) (bound : Nat) (node : Json) :
    Except Error (Checked outside bound node) := do
  let ⟨imported, imported_eq⟩ ← witnessed (metadata emptyDeclarations node)
  let ⟨rawSpan, rawSpan_eq⟩ ← witnessed (string node "src")
  let ⟨span, span_eq⟩ ← witnessed (sourceSpan rawSpan)
  let ⟨ast, ast_eq⟩ ← witnessed (field node "AST")
  let shaped ← (checkBlockShape bound ast).mapError Error.json
  let safe ← (checkMetadataSafety imported.flags imported.documentation).mapError Error.safety
  let prepared ← (WordSyntax.prepare outside shaped.tree).mapError Error.words
  pure ⟨imported, imported_eq, rawSpan, rawSpan_eq, span, span_eq, ast, ast_eq,
    shaped, safe, prepared⟩

/-- Actual emitted program, not a promised future compiler/Source adapter. -/
def Checked.program {outside bound node} (c : Checked outside bound node) :=
  c.prepared.program

def Checked.run {outside bound node} (c : Checked outside bound node) (fuel : Nat) :=
  c.prepared.run fuel

theorem Checked.contract {outside bound node} (c : Checked outside bound node) :
    c.imported.references.entries = [] ∧
    blockAux bound c.ast = .ok c.shaped.tree ∧
    c.shaped.tree.prec = true ∧
    MetadataSafetyD c.imported.flags c.imported.documentation :=
  ⟨references_empty _, c.shaped.parsed, c.shaped.shaped, c.safe.derivation⟩

/-- The existing raw-byte-derived decoder bound is retained unchanged.
Its sufficiency, actual source attachment and admission remain unproved here. -/
def checkText (outside : List String) (raw : String) :
    Except Error ((node : Json) × Checked outside (raw.toUTF8.size + 1) node) := do
  let node ← (Json.parse raw).mapError (fun reason => Error.json (.json reason))
  pure ⟨node, ← check outside (raw.toUTF8.size + 1) node⟩


/-- Exact reconstruction relative to the existing decoder equations. This
does not assert completeness against an independent JSON/Source relation. -/
private theorem witnessed_complete {α : Type} (result : Except YulJson.Error α)
    (value : α) (h : result = .ok value) :
    witnessed result = .ok ⟨value, h⟩ := by
  subst result
  rfl

theorem parsed_complete {bound node} (p : ParsedBlock bound node) :
    parseBlock bound node = .ok p := by
  unfold parseBlock
  split
  · next reason failed => cases (failed.symm.trans p.parsed)
  · next tree found =>
      have same : tree = p.tree := Except.ok.inj (found.symm.trans p.parsed)
      cases p
      cases same
      rfl

theorem shaped_complete {bound node} (s : ShapedBlock bound node) :
    checkBlockShape bound node = .ok s := by
  cases s with
  | mk parsed shaped =>
      simp only [checkBlockShape, parsed_complete parsed, bind, Except.bind]
      exact dif_pos shaped

theorem safety_complete {flags doc} (s : SafetyCertificate flags doc) :
    checkMetadataSafety flags doc = .ok s := by
  obtain ⟨other, h⟩ := s.derivation.complete
  have same : other = s := by cases other; cases s; rfl
  exact h.trans (congrArg Except.ok same)

theorem Checked.complete {outside bound node} (c : Checked outside bound node) :
    check outside bound node = .ok c := by
  cases c with
  | mk imported imported_eq rawSpan rawSpan_eq span span_eq ast ast_eq shaped safe prepared =>
      simp only [check, witnessed_complete _ _ imported_eq,
        witnessed_complete _ _ rawSpan_eq, witnessed_complete _ _ span_eq,
        witnessed_complete _ _ ast_eq, shaped_complete shaped, safety_complete safe,
        prepared.complete, bind, Except.bind, Except.mapError, pure, Except.pure]

theorem check_iff (outside : List String) (bound : Nat) (node : Json) :
    (check outside bound node).toOption.isSome = true ↔
      Nonempty (Checked outside bound node) := by
  constructor
  · intro h
    cases hc : check outside bound node with
    | error reason => simp only [hc, Except.toOption, Option.isSome] at h; cases h
    | ok c => exact ⟨c⟩
  · rintro ⟨c⟩
    rw [c.complete]
    rfl

end Solidity.Frontend.YulJson.Words
