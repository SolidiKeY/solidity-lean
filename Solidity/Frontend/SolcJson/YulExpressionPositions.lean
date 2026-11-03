import Solidity.Frontend.SolcJson.YulObjectLookup
import Solidity.Yul.TypingLeafScope

/-! Forward expression-decoder to actual JSON occurrence existence.
No reverse enumeration/uniqueness, whole-block alignment, metadata adequacy
or Source provenance claim is made. -/
namespace Solidity.Frontend.YulJson.ExpressionPositions
open Lean (Json)
open Solidity.Yul

def ReadAt {F X n E} (node : Json) (leaf : @TypingLeaves.ReadLeaf F X n E) : Prop :=
  ∃ path found, Occurrences.OccurrenceD node false path false found ∧
    identifierPath found = .ok (leaf.name,leaf.parts)

private theorem call_lift {F X n E parent values child}
    (kind : string parent "nodeType" = .ok "YulFunctionCall")
    (arguments : array parent "arguments" = .ok values)
    (member : child ∈ values.toList) (leaf : @TypingLeaves.ReadLeaf F X n E)
    (inside : ReadAt child leaf) : ReadAt parent leaf := by
  obtain ⟨path,node,occurrence,spelled⟩ := inside
  obtain ⟨arrayIndex,inArray⟩ := ObjectLookup.array_occurrence member occurrence
  have kindEq := ObjectLookup.kind_of_string kind
  have notIdentifier : Occurrences.isIdentifier parent = false := by
    simp only [Occurrences.isIdentifier,kindEq]
    decide +kernel
  have selected : Occurrences.includeField parent "arguments" = true := by
    simp only [Occurrences.includeField,kindEq,Occurrences.childKeys]
    decide +kernel
  have role : Occurrences.fieldRole parent "arguments" = false := by
    simp only [Occurrences.fieldRole,kindEq]
    decide +kernel
  obtain ⟨ordinal,lifted⟩ := ObjectLookup.field_occurrence
    (start := false) (ObjectLookup.array_field arguments) notIdentifier selected
    (by simpa only [role] using inArray)
  exact ⟨.field "arguments" ordinal::.array arrayIndex::path,node,lifted,spelled⟩

/-- Internal list transport with its REAL child decoder premise. The final
expression theorem below supplies that premise by induction on decoder fuel. -/
private theorem arguments_reads {F X n E} (fuel : Nat)
    (known : ∀ {node term arity}, expressionAux fuel node = .ok term →
      (typed : @ExprD F X n E term arity) → (path : TypingLeaves.Path) →
        TypingLeaves.All (fun _ leaf => ReadAt node leaf) (TypingLeaves.reads typed path))
    (nodes : List Json) {trees : List (Solidity.Source.Syn .yulExpr)} {arity : Nat}
    (parsed : nodes.mapM (expressionAux fuel) = .ok trees)
    (typed : ArgsD E (Solidity.Frontend.Checked.toSynList trees) arity)
    (path : TypingLeaves.Path) :
    TypingLeaves.All (fun _ leaf => ∃ child ∈ nodes, ReadAt child leaf)
      (TypingLeaves.arguments typed path) := by
  induction nodes generalizing trees arity path with
  | nil =>
      change (Except.ok [] : Except Error (List (Solidity.Source.Syn .yulExpr))) = .ok trees at parsed
      cases parsed
      cases typed
      intro entry impossible
      cases impossible
  | cons node rest ih =>
      cases headEq : expressionAux fuel node with
      | error reason =>
          simp only [List.mapM_cons,headEq,bind,Except.bind] at parsed
          cases parsed
      | ok headTree =>
          cases tailEq : rest.mapM (expressionAux fuel) with
          | error reason =>
              simp only [List.mapM_cons,headEq,tailEq,bind,Except.bind] at parsed
              cases parsed
          | ok tailTrees =>
              have same : headTree::tailTrees = trees := Except.ok.inj (by
                simpa only [List.mapM_cons,headEq,tailEq,bind,Except.bind,pure,Except.pure] using parsed)
              cases same
              cases typed with
              | cons head tail =>
                  intro entry present
                  change entry ∈ TypingLeaves.reads head (path++[.first]) ++
                    TypingLeaves.arguments tail (path++[.rest]) at present
                  rcases List.mem_append.mp present with first | later
                  · exact ⟨node,List.mem_cons_self,known headEq head (path++[.first]) entry first⟩
                  · obtain ⟨child,member,read⟩ := ih tailEq tail (path++[.rest]) entry later
                    exact ⟨child,List.mem_cons_of_mem _ member,read⟩

private theorem identifier_reads {F X n E node name parts arity}
    (identified : Occurrences.isIdentifier node = true)
    (parsed : identifierPath node = .ok (name,parts))
    (typed : @ExprD F X n E (.yulPath name parts) arity) (path : TypingLeaves.Path) :
    TypingLeaves.All (fun _ leaf => ReadAt node leaf) (TypingLeaves.reads typed path) := by
  cases typed <;> intro entry present <;>
    rcases List.mem_cons.mp present with same | impossible
  · cases same
    exact ⟨[],node,.identifier identified,parsed⟩
  · cases impossible
  · cases same
    exact ⟨[],node,.identifier identified,parsed⟩
  · cases impossible

private theorem call_reads {F X n E node name values trees arity} (fuel : Nat)
    (known : ∀ {node term arity}, expressionAux fuel node = .ok term →
      (typed : @ExprD F X n E term arity) → (path : TypingLeaves.Path) →
        TypingLeaves.All (fun _ leaf => ReadAt node leaf) (TypingLeaves.reads typed path))
    (kind : string node "nodeType" = .ok "YulFunctionCall")
    (valuesEq : array node "arguments" = .ok values)
    (decoded : values.toList.mapM (expressionAux fuel) = .ok trees)
    (typed : ExprD E (.yulCall name (Solidity.Frontend.Checked.toSynList trees)) arity)
    (path : TypingLeaves.Path) :
    TypingLeaves.All (fun _ leaf => ReadAt node leaf) (TypingLeaves.reads typed path) := by
  cases typed with
  | builtin builtin spelling arguments =>
      have children := arguments_reads fuel known values.toList decoded arguments (path++[.arguments])
      intro entry present
      obtain ⟨child,member,read⟩ := children entry present
      exact call_lift kind valuesEq member entry.2 read
  | call function noBuiltin resolved arguments =>
      have children := arguments_reads fuel known values.toList decoded arguments (path++[.arguments])
      intro entry present
      obtain ⟨child,member,read⟩ := children entry present
      exact call_lift kind valuesEq member entry.2 read

/-- Concrete forward composition of the ACTUAL decoder and ACTUAL intrinsic
derivation. Every typed variable read reaches an actual JSON occurrence with
the exact decoded spelling/suffix. No child/provider/alignment law is assumed.
This is existence, not reverse coverage or positional injectivity. -/
theorem decoded_reads {F X n E} (fuel : Nat) {node term arity}
    (parsed : expressionAux fuel node = .ok term) (typed : @ExprD F X n E term arity)
    (path : TypingLeaves.Path) :
    TypingLeaves.All (fun _ leaf => ReadAt node leaf) (TypingLeaves.reads typed path) := by
  induction fuel generalizing node term arity path with
  | zero => cases parsed
  | succ fuel ih =>
      rw [expressionAux] at parsed
      cases kindEq : string node "nodeType" with
      | error reason =>
          simp only [kindEq,bind,Except.bind] at parsed
          cases parsed
      | ok kind =>
          simp only [kindEq,bind,Except.bind] at parsed
          by_cases literalKind : kind = "YulLiteral"
          · rw [if_pos literalKind] at parsed
            cases literalEq : literal node with
            | error reason =>
                simp only [literalEq] at parsed
                cases parsed
            | ok description =>
                simp only [literalEq,pure,Except.pure] at parsed
                cases parsed
                cases typed
                intro entry impossible
                cases impossible
          · rw [if_neg literalKind] at parsed
            by_cases identifierKind : kind = "YulIdentifier"
            · rw [if_pos identifierKind] at parsed
              cases identifierEq : identifierPath node with
              | error reason =>
                  simp only [identifierEq] at parsed
                  cases parsed
              | ok pair =>
                  rcases pair with ⟨name,parts⟩
                  simp only [identifierEq,pure,Except.pure] at parsed
                  cases parsed
                  have identified : Occurrences.isIdentifier node = true := by
                    unfold Occurrences.isIdentifier
                    rw [ObjectLookup.kind_of_string
                      (kindEq.trans (congrArg Except.ok identifierKind))]
                    decide +kernel
                  exact identifier_reads identified identifierEq typed path
            · rw [if_neg identifierKind] at parsed
              by_cases callKind : kind = "YulFunctionCall"
              · rw [if_pos callKind] at parsed
                cases functionField : field node "functionName" with
                | error reason =>
                    simp only [functionField] at parsed
                    cases parsed
                | ok functionNode =>
                    simp only [functionField] at parsed
                    cases functionEq : functionName functionNode with
                    | error reason =>
                        simp only [functionEq] at parsed
                        cases parsed
                    | ok name =>
                        simp only [functionEq] at parsed
                        cases valuesEq : array node "arguments" with
                        | error reason =>
                            simp only [valuesEq] at parsed
                            cases parsed
                        | ok values =>
                            simp only [valuesEq] at parsed
                            cases treesEq : values.toList.mapM (expressionAux fuel) with
                            | error reason =>
                                simp only [treesEq] at parsed
                                cases parsed
                            | ok trees =>
                                simp only [treesEq,pure,Except.pure] at parsed
                                cases parsed
                                exact call_reads fuel (fun decoded child relativePath =>
                                  ih decoded child relativePath)
                                  (kindEq.trans (congrArg Except.ok callKind))
                                  valuesEq treesEq typed path
              · rw [if_neg callKind] at parsed
                cases parsed

end Solidity.Frontend.YulJson.ExpressionPositions
namespace Solidity.Frontend.YulJson
open Solidity.Yul

def CheckedExpression.readTrace {F X n E bound node}
    (checked : @CheckedExpression F X n E bound node) :
    TypingLeaves.ReadTrace E :=
  TypingLeaves.reads checked.derivation []

/-- Final ACTUAL checked-expression composition. Only forward occurrence
existence is claimed; relative grammar/JSON path injectivity is separate. -/
theorem CheckedExpression.read_occurrences_exist {F X n E bound node}
    (checked : @CheckedExpression F X n E bound node) :
    TypingLeaves.All (fun _ leaf => ExpressionPositions.ReadAt node leaf) checked.readTrace :=
  ExpressionPositions.decoded_reads bound checked.parsed checked.derivation []

end Solidity.Frontend.YulJson
