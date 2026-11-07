import Solidity.Lowering.P8.SourceAstExpressionCorrespondence

/-! Tuple and string-byte correspondence for existing Source syntax readers.
Regression purpose: retain tuple holes/order, reject an empty tuple explicitly,
and keep decoded string bytes. These are structural conversion laws, not
source-byte/artifact binding, Source meaning, admission or lifecycle proofs. -/
namespace Solidity.Lowering.P8.SourceAstTupleCorrespondence
open Lean Solidity.Source
open SourceAstParameters SourceAstCorrespondence SourceAstExpressionCorrespondence

/-- The tuple reader's existing anonymous child adapter agrees with the
existing shared optional-expression reader; no new decoder is introduced. -/
theorem optional_reader_agrees (fuel : Nat) (node : Json) :
    (do match node with
      | .null => pure (Syn.none : Syn (.opt .expr))
      | _ => return Syn.some (← SourceAstExpressions.expression fuel node)) =
    SourceAstStatements.optionalExpression fuel node := by
  unfold SourceAstStatements.optionalExpression
  cases node with
  | null => rfl
  | bool b => cases SourceAstExpressions.expression fuel (.bool b) <;> rfl
  | num n => cases SourceAstExpressions.expression fuel (.num n) <;> rfl
  | str s => cases SourceAstExpressions.expression fuel (.str s) <;> rfl
  | arr xs => cases SourceAstExpressions.expression fuel (.arr xs) <;> rfl
  | obj fields => cases SourceAstExpressions.expression fuel (.obj fields) <;> rfl

theorem optional_hole (fuel : Nat) :
    SourceAstStatements.optionalExpression fuel .null = .ok Syn.none := rfl

/-- Every successful tuple has at least one component, and every original
component has exactly its ordered optional conversion result. -/
theorem tuple_ok_iff_each (fuel : Nat) (node : Json) (children : Array Json)
    (out : Syn .expr)
    (kind : node.getObjValAs? String "nodeType" = .ok "TupleExpression")
    (inlineArray : node.getObjValAs? Bool "isInlineArray" = .ok false)
    (fields : node.getObjValAs? (Array Json) "components" = .ok children) :
    SourceAstExpressions.expression (fuel + 1) node = .ok out ↔
      ∃ head tail, Each (fun child value =>
        SourceAstStatements.optionalExpression fuel child = .ok value)
        children.toList (head :: tail) ∧ out = .tuple head (syntaxList tail) := by
  have adapter : (fun child : Json => do
      match child with
      | .null => pure (Syn.none : Syn (.opt .expr))
      | _ => return Syn.some (← SourceAstExpressions.expression fuel child)) =
      SourceAstStatements.optionalExpression fuel := funext (optional_reader_agrees fuel)
  rw [SourceAstExpressions.expression]
  simp only [kind, inlineArray, fields, ok_bind, Bool.not_false, ite_true, pure_bind]
  change ((do
    let values ← children.toList.mapM (fun child : Json => do
      match child with
      | .null => pure (Syn.none : Syn (.opt .expr))
      | _ => return Syn.some (← SourceAstExpressions.expression fuel child))
    match values with
    | [] => throw "empty tuple conversion not implemented"
    | head :: tail => pure (Syn.tuple head (syntaxList tail))) : Except String (Syn .expr)) =
      .ok out ↔ _
  rw [adapter]
  cases h : children.toList.mapM (SourceAstStatements.optionalExpression fuel) with
  | error message =>
    constructor
    · intro bad
      cases bad
    · intro ⟨head, tail, each, _⟩
      have bad := each.mapM_ok
      rw [h] at bad
      cases bad
  | ok values =>
    cases values with
    | nil =>
      constructor
      · intro bad
        cases bad
      · intro ⟨head, tail, each, _⟩
        have bad := each.mapM_ok
        rw [h] at bad
        cases bad
    | cons head tail =>
      constructor
      · intro same
        change Except.ok (.tuple head (syntaxList tail)) = Except.ok out at same
        cases same
        exact ⟨head, tail, each_of_mapM_ok h, rfl⟩
      · intro ⟨other, rest, each, same⟩
        have eq := each.mapM_ok
        rw [h] at eq
        cases eq
        cases same
        rfl

/-- An empty tuple cannot silently become a successful expression. -/
theorem empty_tuple_rejected (fuel : Nat) (node : Json)
    (kind : node.getObjValAs? String "nodeType" = .ok "TupleExpression")
    (inlineArray : node.getObjValAs? Bool "isInlineArray" = .ok false)
    (fields : node.getObjValAs? (Array Json) "components" = .ok #[]) :
    SourceAstExpressions.expression (fuel + 1) node =
      .error "empty tuple conversion not implemented" := by
  rw [SourceAstExpressions.expression]
  simp only [kind, inlineArray, fields, ok_bind, Bool.not_false, ite_true, pure_bind]
  rfl

/-- The ordinary string kind preserves the exact decoded compiler hex bytes.
This says nothing about source provenance or an independent compiler run. -/
theorem string_bytes_exact (node : Json) (raw : String) (bytes : List UInt8)
    (kind : node.getObjValAs? String "kind" = .ok "string")
    (field : node.getObjValAs? String "hexValue" = .ok raw)
    (digits : raw.toUTF8.toList.all Solidity.Frontend.Checked.isHexDigit = true)
    (decoded : Solidity.Frontend.Checked.hexBody raw.toUTF8.toList = some bytes) :
    SourceAstExpressions.literal node = .ok (.str bytes) := by
  unfold SourceAstExpressions.literal
  simp only [kind, field, ok_bind, digits, decoded, ite_true, pure_bind]
  rfl

/-- info: 'Solidity.Lowering.P8.SourceAstTupleCorrespondence.optional_reader_agrees' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms optional_reader_agrees
/-- info: 'Solidity.Lowering.P8.SourceAstTupleCorrespondence.optional_hole' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms optional_hole
/-- info: 'Solidity.Lowering.P8.SourceAstTupleCorrespondence.tuple_ok_iff_each' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tuple_ok_iff_each
/-- info: 'Solidity.Lowering.P8.SourceAstTupleCorrespondence.empty_tuple_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_tuple_rejected
/-- info: 'Solidity.Lowering.P8.SourceAstTupleCorrespondence.string_bytes_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms string_bytes_exact
end Solidity.Lowering.P8.SourceAstTupleCorrespondence
