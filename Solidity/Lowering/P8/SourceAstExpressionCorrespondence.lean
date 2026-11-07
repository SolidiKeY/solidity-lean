import Solidity.Lowering.P8.SourceAstCorrespondence

/-! Structural child correspondence for existing compiler expression readers.
Regression purpose: preserve the receiver/storage alias syntax, assignment
operand order and every positional argument. Exact JSON field hypotheses
identify the input shape; no Source admission, meaning or origin is claimed. -/
namespace Solidity.Lowering.P8.SourceAstExpressionCorrespondence
open Lean Solidity.Source
open SourceAstParameters SourceAstCorrespondence

theorem ok_bind {α β ε : Type} (value : α) (next : α → Except ε β) :
    (Except.ok value >>= next) = next value := rfl

/-- Identifier spelling is retained exactly. -/
theorem identifier_exact (fuel : Nat) (node : Json) (name : String)
    (kind : node.getObjValAs? String "nodeType" = .ok "Identifier")
    (field : node.getObjValAs? String "name" = .ok name) :
    SourceAstExpressions.expression (fuel + 1) node = .ok (.ident name) := by
  rw [SourceAstExpressions.expression]
  simp only [kind, field, ok_bind]
  rfl

/-- Member success retains the exact recursively converted receiver. -/
theorem member_ok_iff (fuel : Nat) (node receiver : Json) (name : String)
    (out : Syn .expr)
    (kind : node.getObjValAs? String "nodeType" = .ok "MemberAccess")
    (base : node.getObjVal? "expression" = .ok receiver)
    (field : node.getObjValAs? String "memberName" = .ok name) :
    SourceAstExpressions.expression (fuel + 1) node = .ok out ↔
      ∃ value, SourceAstExpressions.expression fuel receiver = .ok value ∧
        out = .member value name := by
  rw [SourceAstExpressions.expression]
  simp only [kind, base, field, ok_bind]
  cases h : SourceAstExpressions.expression fuel receiver with
  | error message =>
    constructor
    · intro bad
      cases bad
    · intro ⟨value, bad, _⟩
      cases bad
  | ok value =>
    constructor
    · intro eq
      change Except.ok (.member value name) = Except.ok out at eq
      cases eq
      exact ⟨value, rfl, rfl⟩
    · intro ⟨other, same, eq⟩
      cases same
      cases eq
      rfl

/-- Both assignment operands retain their original side and child conversion. -/
theorem assignment_ok_iff (fuel : Nat) (node left right : Json) (out : Syn .expr)
    (kind : node.getObjValAs? String "nodeType" = .ok "Assignment")
    (op : node.getObjValAs? String "operator" = .ok "=")
    (lhs : node.getObjVal? "leftHandSide" = .ok left)
    (rhs : node.getObjVal? "rightHandSide" = .ok right) :
    SourceAstExpressions.expression (fuel + 1) node = .ok out ↔
      ∃ l r, SourceAstExpressions.expression fuel left = .ok l ∧
        SourceAstExpressions.expression fuel right = .ok r ∧ out = .assign .assign l r := by
  rw [SourceAstExpressions.expression]
  simp only [kind, op, lhs, rhs, ok_bind, beq_self_eq_true]
  cases hl : SourceAstExpressions.expression fuel left with
  | error message =>
    constructor
    · intro bad
      cases bad
    · intro ⟨l, r, bad, _⟩
      cases bad
  | ok l =>
    cases hr : SourceAstExpressions.expression fuel right with
    | error message =>
      constructor
      · intro bad
        cases bad
      · intro ⟨l', r, _, bad, _⟩
        cases bad
    | ok r =>
      constructor
      · intro eq
        change Except.ok (.assign .assign l r) = Except.ok out at eq
        cases eq
        exact ⟨l, r, rfl, rfl, rfl⟩
      · intro ⟨l', r', leftEq, rightEq, eq⟩
        cases leftEq
        cases rightEq
        cases eq
        rfl

/-- A positional call retains its target and every argument in order. -/
theorem call_ok_iff (fuel : Nat) (node target : Json) (args : Array Json)
    (out : Syn .expr)
    (kind : node.getObjValAs? String "nodeType" = .ok "FunctionCall")
    (callKind : node.getObjValAs? String "kind" = .ok "functionCall")
    (names : node.getObjValAs? (Array String) "names" = .ok #[])
    (fn : node.getObjVal? "expression" = .ok target)
    (fields : node.getObjValAs? (Array Json) "arguments" = .ok args) :
    SourceAstExpressions.expression (fuel + 1) node = .ok out ↔
      ∃ value, SourceAstExpressions.expression fuel target = .ok value ∧
        ∃ values, Each (fun child arg => SourceAstExpressions.expression fuel child = .ok arg)
          args.toList values ∧ out = .call value (.positional (syntaxList values)) := by
  rw [SourceAstExpressions.expression]
  simp only [kind, callKind, names, fn, fields, ok_bind, beq_self_eq_true,
    Array.isEmpty_empty, ite_true, pure_bind]
  cases h : SourceAstExpressions.expression fuel target with
  | error message =>
    constructor
    · intro bad
      cases bad
    · intro ⟨value, bad, _⟩
      cases bad
  | ok value =>
    constructor
    · intro success
      exact ⟨value, rfl, (build_ok_iff_each (SourceAstExpressions.expression fuel)
        (fun (values : List (Syn .expr)) => (Syn.call value (.positional (syntaxList values)) : Syn .expr)) args.toList out).mp success⟩
    · intro ⟨other, same, values⟩
      cases same
      exact (build_ok_iff_each (SourceAstExpressions.expression fuel)
        (fun (values : List (Syn .expr)) => (Syn.call value (.positional (syntaxList values)) : Syn .expr)) args.toList out).mpr values

/-- Receiver failure wins before member-name lookup, preserving its exact diagnostic. -/
theorem member_receiver_failure (fuel : Nat) (node receiver : Json) (message : String)
    (kind : node.getObjValAs? String "nodeType" = .ok "MemberAccess")
    (base : node.getObjVal? "expression" = .ok receiver)
    (failed : SourceAstExpressions.expression fuel receiver = .error message) :
    SourceAstExpressions.expression (fuel + 1) node = .error message := by
  rw [SourceAstExpressions.expression]
  simp only [kind, base, failed, ok_bind]
  rfl

/-- Left conversion failure wins before right-field lookup; operand errors are not reordered. -/
theorem assignment_left_failure (fuel : Nat) (node left : Json) (message : String)
    (kind : node.getObjValAs? String "nodeType" = .ok "Assignment")
    (op : node.getObjValAs? String "operator" = .ok "=")
    (lhs : node.getObjVal? "leftHandSide" = .ok left)
    (failed : SourceAstExpressions.expression fuel left = .error message) :
    SourceAstExpressions.expression (fuel + 1) node = .error message := by
  rw [SourceAstExpressions.expression]
  simp only [kind, op, lhs, failed, ok_bind, beq_self_eq_true]
  rfl

/-- Named calls retain their existing refusal before target or argument conversion. -/
theorem named_call_refused (fuel : Nat) (node : Json) (names : Array String)
    (kind : node.getObjValAs? String "nodeType" = .ok "FunctionCall")
    (callKind : node.getObjValAs? String "kind" = .ok "functionCall")
    (namesField : node.getObjValAs? (Array String) "names" = .ok names)
    (nonempty : names.isEmpty = false) :
    SourceAstExpressions.expression (fuel + 1) node =
      .error "named call conversion not implemented" := by
  rw [SourceAstExpressions.expression]
  simp only [kind, callKind, namesField, nonempty, ok_bind, beq_self_eq_true]
  rfl

/-- info: 'Solidity.Lowering.P8.SourceAstExpressionCorrespondence.ok_bind' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms ok_bind
/-- info: 'Solidity.Lowering.P8.SourceAstExpressionCorrespondence.identifier_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms identifier_exact
/-- info: 'Solidity.Lowering.P8.SourceAstExpressionCorrespondence.member_ok_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms member_ok_iff
/-- info: 'Solidity.Lowering.P8.SourceAstExpressionCorrespondence.assignment_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assignment_ok_iff
/-- info: 'Solidity.Lowering.P8.SourceAstExpressionCorrespondence.call_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms call_ok_iff
/-- info: 'Solidity.Lowering.P8.SourceAstExpressionCorrespondence.member_receiver_failure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms member_receiver_failure
/-- info: 'Solidity.Lowering.P8.SourceAstExpressionCorrespondence.assignment_left_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assignment_left_failure
/-- info: 'Solidity.Lowering.P8.SourceAstExpressionCorrespondence.named_call_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_call_refused
end Solidity.Lowering.P8.SourceAstExpressionCorrespondence
