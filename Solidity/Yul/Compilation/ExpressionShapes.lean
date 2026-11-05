import Solidity.Yul.Compilation.ShapeCapacity
import Solidity.Yul.Compilation.ProducerExpressions

/-! Operand-shape certificates for the EXISTING literal/local/binary lowering.
No source syntax, compiler output or executor is replaced. Binary metadata is
an explicit real arity row, discharged by concrete operator consumers. These
are operand heights; all-prefix capacity and native/G24 remain separate. -/
namespace Solidity.Yul.Compilation.ExpressionShapes
open Backend Scalar LabelExec

theorem append {a b : Program} {n m k : Nat} (first : CodeShape a n m)
    (second : CodeShape b m k) : CodeShape (a++b) n k := by
  induction first with
  | nil n => exact second
  | cons head rest ih => exact .cons head (ih second)

theorem literal {n : Nat} (value : Scalar.Word) (depth : Nat) (p : Program)
    (emitted : (lowerLiteral (n := n) value).code depth = some p) :
    CodeShape p (n+depth) (n+depth+1) := by
  cases emitted
  exact .cons (.mk 0 1 (n+depth) rfl (by omega) (by omega)) (.nil (n+depth+1))

theorem local_shape {n : Nat} (i : Fin n) (depth : Nat) (p : Program)
    (emitted : (lowerLocal i).code depth = some p) :
    CodeShape p (n+depth) (n+depth+1) := by
  change (if h : depth+i.val < 16 then some [readSlot ⟨depth+i.val,h⟩] else none) = some p at emitted
  split at emitted
  next accessible =>
    cases emitted
    have bounded := i.isLt
    exact .cons (.mk (depth+i.val+1) (depth+i.val+2) (n-(i.val+1))
      rfl (by omega) (by omega)) (.nil (n+depth+1))
  next inaccessible => cases emitted

/-- Right runs at depth; left runs one word deeper. A physical arity row is
required in addition to the primitive's word semantics, never inferred from
an abstract chosen run result. Child metadata is for actual emitted code. -/
theorem binary {n : Nat} {left right : Vector Scalar.Word n → Scalar.Word}
    (op : BinarySelection) (a : LoweredExpr n left) (b : LoweredExpr n right)
    (row : arity (.op op.opcode) = some (2,1))
    (leftShape : ∀ depth p, a.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (rightShape : ∀ depth p, b.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (depth : Nat) (p : Program) (emitted : (lowerBinary op a b).code depth = some p) :
    CodeShape p (n+depth) (n+depth+1) := by
  change (b.code depth).bind (fun rb => (a.code (1+depth)).map
    (fun la => rb++la++[.op op.opcode])) = some p at emitted
  cases hr : b.code depth with
  | none => simp only [hr,Option.bind_none] at emitted; cases emitted
  | some rb =>
    cases hl : a.code (1+depth) with
    | none => simp only [hr,hl,Option.bind_some,Option.map_none] at emitted; cases emitted
    | some la =>
      simp only [hr,hl,Option.bind_some,Option.map_some] at emitted
      cases emitted
      have first := rightShape depth rb hr
      have second := leftShape (1+depth) la hl
      rw [show n+(1+depth) = n+depth+1 by omega] at second
      exact append (append first second)
        (.cons (.mk 2 1 (n+depth) row (by omega) (by omega)) (.nil (n+depth+1)))
/-- info: 'Solidity.Yul.Compilation.ExpressionShapes.append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms append
/-- info: 'Solidity.Yul.Compilation.ExpressionShapes.literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literal
/-- info: 'Solidity.Yul.Compilation.ExpressionShapes.local_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms local_shape
/-- info: 'Solidity.Yul.Compilation.ExpressionShapes.binary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms binary
end Solidity.Yul.Compilation.ExpressionShapes
