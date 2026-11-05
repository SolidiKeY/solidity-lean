import Solidity.Frontend.SolcJson.YulNamespaceBinding
import Solidity.Yul.ScopedExpressions

/-! A supplied actual JSON occurrence/metadata attachment is admitted at a
specific intrinsic expression/target environment only after REAL current-scope
visibility and local-priority checks. This is a leaf bridge; deriving the
enclosing AST occurrence's actual environment remains a separate obligation. -/
namespace Solidity.Frontend.YulJson.ReferenceAttachment
open Lean (Json)
open Solidity.Yul

theorem Attached.node_kind {X table original write node reference}
    (attached : @Attached X table original write node reference) :
    string node "nodeType" = .ok "YulIdentifier" := by
  have parsed := attached.identifier_eq
  unfold identifierPath requireNode at parsed
  cases actual : string node "nodeType" with
  | error reason => simp only [actual,bind,Except.bind] at parsed; cases parsed
  | ok kind =>
      simp only [actual,bind,Except.bind] at parsed
      by_cases same : kind = "YulIdentifier"
      · exact congrArg Except.ok same
      · simp only [same,if_false,throw] at parsed
        cases parsed

theorem Attached.parsed {X table original write node reference}
    (attached : @Attached X table original write node reference) (fuel : Nat) :
    expression (fuel+1) node = .ok (.yulPath attached.visible attached.suffix) := by
  simp only [expression,expressionAux,attached.node_kind,bind,Except.bind,
    String.reduceEq,if_false,if_true,attached.identifier_eq,pure,Except.pure]

/-- The current index is tied to the original declaration occurrence, not just
to a type/attribute. Local priority is checked at this EXACT supplied context. -/
structure Use {root current table original write node reference}
    (attached : @Attached root table original write node reference)
    (scope : ExternalScope root current) {n : Nat} (locals : List (String × Fin n)) where
  index : Member current reference.declaration.ty
  visible : ScopeIndexD scope reference.declaration.index index
  priority : attached.suffix ≠ [] ∨ NoBinding locals attached.visible

def checkUse {root current table original write node reference}
    (attached : @Attached root table original write node reference)
    (scope : ExternalScope root current) {n : Nat} (locals : List (String × Fin n)) :
    Option (Use attached scope locals) := do
  let ⟨index,visible⟩ ← scope.index reference.declaration.index
  if different : attached.suffix ≠ [] then
    pure ⟨index,visible,.inl different⟩
  else
    match found : resolve locals attached.visible with
    | some _ => none
    | none => pure ⟨index,visible,.inr (resolve_none_sound found)⟩

theorem Use.complete {root current table original write node reference attached scope n locals}
    (use : @Use root current table original write node reference attached scope n locals) :
    checkUse attached scope locals = some use := by
  cases use with
  | mk index visible priority =>
      unfold checkUse
      rw [visible.complete]
      simp only [bind,Option.bind]
      split
      · rfl
      · next same =>
          have absent : NoBinding locals attached.visible := by
            cases priority with
            | inl different => exact False.elim (same different)
            | inr absent => exact absent
          split
          · next position found =>
              have impossible := resolve_none_complete absent
              rw [found] at impossible
              cases impossible
          · rfl

theorem checkUse_iff {root current table original write node reference}
    (attached : @Attached root table original write node reference)
    (scope : ExternalScope root current) {n : Nat} (locals : List (String × Fin n)) :
    (checkUse attached scope locals).isSome = true ↔ Nonempty (Use attached scope locals) := by
  constructor
  · intro yes
    cases result : checkUse attached scope locals with
    | none => rw [result] at yes; cases yes
    | some use => exact ⟨use⟩
  · rintro ⟨use⟩
    rw [use.complete]
    rfl

def Use.term {root current table original write node reference attached scope n locals}
    (use : @Use root current table original write node reference attached scope n locals) :
    ExternalRef current write := ⟨use.index,reference.attr,attached.access⟩

def Use.scoped {root current table original write node reference attached scope n locals}
    (use : @Use root current table original write node reference attached scope n locals) :
    ScopedExternalD (Names.declarations table original) scope write attached.visible attached.suffix
      use.term :=
  attached.scoped scope use.index use.visible

def Use.readDerivation {root current table original node reference attached scope n locals F}
    (input : @MetadataWords.Input root table original)
    (use : @Use root current table original false node reference attached scope n locals)
    (functions : FunctionNames F) :
    ExprD (input.names.readEnv scope locals functions)
      (.yulPath attached.visible attached.suffix) 1 :=
  input.names.externalExpr scope locals functions use.scoped use.priority

theorem Use.read_term {root current table original node reference attached scope n locals F}
    (input : @MetadataWords.Input root table original)
    (use : @Use root current table original false node reference attached scope n locals)
    (functions : FunctionNames F) :
    (use.readDerivation input functions).term = .external use.term := rfl

/-- The certificate consumed by the EXISTING scoped block expression checker,
including its supplemental independent external-scope property. -/
def Use.readScoped {root current table original node reference attached scope n locals F}
    (input : @MetadataWords.Input root table original)
    (use : @Use root current table original false node reference attached scope n locals)
    (functions : FunctionNames F) :
    ScopedExpressions.Checked input.names scope locals functions
      (.yulPath attached.visible attached.suffix) :=
  ⟨1,use.readDerivation input functions,⟨use.scoped⟩⟩

theorem Use.readScoped_complete {root current table original node reference attached scope n locals F}
    (input : @MetadataWords.Input root table original)
    (use : @Use root current table original false node reference attached scope n locals)
    (functions : FunctionNames F) :
    ScopedExpressions.check input.names scope locals functions
      (.yulPath attached.visible attached.suffix) = some (use.readScoped input functions) :=
  (use.readScoped input functions).complete

/-- The actual JSON leaf is parsed, not replaced by a caller-supplied tree. -/
def Use.readJson {root current table original node reference attached scope n locals F}
    (input : @MetadataWords.Input root table original)
    (use : @Use root current table original false node reference attached scope n locals)
    (functions : FunctionNames F) (fuel : Nat) :
    CheckedExpression (input.names.readEnv scope locals functions) (fuel+1) node :=
  ⟨_,1,attached.parsed fuel,use.readDerivation input functions⟩

/-- Concrete reconstruction through the EXISTING JSON and intrinsic expression
checkers, with no parser/lookup agreement premise. -/
theorem Use.readJson_complete {root current table original node reference attached scope n locals F}
    (input : @MetadataWords.Input root table original)
    (use : @Use root current table original false node reference attached scope n locals)
    (functions : FunctionNames F) (fuel : Nat) :
    checkExpression (input.names.readEnv scope locals functions) (fuel+1) node =
      .ok (use.readJson input functions fuel) := by
  unfold checkExpression
  split
  · next reason failed =>
      have impossible := attached.parsed fuel
      rw [failed] at impossible
      cases impossible
  · next tree parsed =>
      have same := Except.ok.inj (parsed.symm.trans (attached.parsed fuel))
      subst tree
      rw [(use.readDerivation input functions).complete]
      rfl

theorem Use.write_checked {root current table original node reference attached scope n locals}
    (use : @Use root current table original true node reference attached scope n locals) :
    (checkTarget (ScopedNames.targetEnv (Names.declarations table original) scope locals)
      attached.visible attached.suffix).map Sigma.fst = some (.external use.term) :=
  ScopedNames.checkTarget_external_complete locals use.scoped use.priority

end Solidity.Frontend.YulJson.ReferenceAttachment
