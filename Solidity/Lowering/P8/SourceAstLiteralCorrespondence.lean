import Solidity.Lowering.P8.SourceAstTupleCorrespondence

/-! Remaining supported literal-reader correspondence.
Regression purpose: preserve decoded string-kind distinctions, canonical
integer values and Boolean values before Source resolution. These are syntax
laws about existing readers, not compiler/source provenance or execution. -/
namespace Solidity.Lowering.P8.SourceAstLiteralCorrespondence
open Lean Solidity.Source
open SourceAstExpressionCorrespondence

/-- All supported string kinds retain their decoded bytes and constructor. -/
theorem string_kind_exact (node : Json) (label raw : String) (bytes : List UInt8)
    (supported : label = "string" ∨ label = "unicodeString" ∨ label = "hexString")
    (kind : node.getObjValAs? String "kind" = .ok label)
    (field : node.getObjValAs? String "hexValue" = .ok raw)
    (digits : raw.toUTF8.toList.all Solidity.Frontend.Checked.isHexDigit = true)
    (decoded : Solidity.Frontend.Checked.hexBody raw.toUTF8.toList = some bytes) :
    SourceAstExpressions.literal node = .ok (match label with
      | "unicodeString" => Lit.unicodeStr bytes
      | "hexString" => Lit.hexStr bytes
      | _ => Lit.str bytes) := by
  rcases supported with same | same | same <;> subst label
  all_goals
    unfold SourceAstExpressions.literal
    simp only [kind, field, ok_bind, digits, decoded, ite_true, pure_bind]
    rfl

/-- Every existing no-unit spelling keeps exactly the canonical integer value.
The field hypotheses expose the converter's input, not a Source success filter. -/
theorem integer_exact (node : Json) (raw : String) (value : Nat)
    (kind : node.getObjValAs? String "kind" = .ok "number")
    (field : node.getObjValAs? String "value" = .ok raw)
    (units : (∃ message, node.getObjVal? "subdenomination" = .error message) ∨
      node.getObjVal? "subdenomination" = .ok .null ∨
      node.getObjVal? "subdenomination" = .ok (.str ""))
    (canonical : Solidity.Frontend.Checked.canonNat raw.toUTF8.toList = some value) :
    SourceAstExpressions.literal node = .ok (.num (.dec value 0 0)) := by
  rcases units with ⟨message, units⟩ | units | units
  all_goals
    unfold SourceAstExpressions.literal
    simp only [kind, field, units, canonical, ok_bind, pure_bind]
    rfl

/-- Both Boolean spellings retain their value without a success-only branch. -/
theorem boolean_exact (node : Json) (value : Bool)
    (kind : node.getObjValAs? String "kind" = .ok "bool")
    (field : node.getObjValAs? String "value" = .ok (if value then "true" else "false")) :
    SourceAstExpressions.literal node = .ok (.bool value) := by
  cases value <;> unfold SourceAstExpressions.literal
  all_goals
    simp only [kind, field, ok_bind]
    rfl

/-- The expression wrapper retains the exact successfully converted literal. -/
theorem literal_expression_exact (fuel : Nat) (node : Json) (value : Lit)
    (kind : node.getObjValAs? String "nodeType" = .ok "Literal")
    (converted : SourceAstExpressions.literal node = .ok value) :
    SourceAstExpressions.expression (fuel + 1) node = .ok (.lit value) := by
  rw [SourceAstExpressions.expression]
  simp only [kind, converted, ok_bind]
  rfl

/-- info: 'Solidity.Lowering.P8.SourceAstLiteralCorrespondence.string_kind_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms string_kind_exact
/-- info: 'Solidity.Lowering.P8.SourceAstLiteralCorrespondence.integer_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms integer_exact
/-- info: 'Solidity.Lowering.P8.SourceAstLiteralCorrespondence.boolean_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boolean_exact
/-- info: 'Solidity.Lowering.P8.SourceAstLiteralCorrespondence.literal_expression_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms literal_expression_exact
end Solidity.Lowering.P8.SourceAstLiteralCorrespondence
