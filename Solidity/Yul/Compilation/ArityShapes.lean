import Solidity.Yul.Compilation.ExpressionShapes
import Solidity.Yul.Compilation.OpcodeLowering

/-! Operand metadata for existing arity-indexed argument and inline lowering.
These are copied operands, not function frames. Actual child/body shapes are
explicit; native validity and every-prefix1024 capacity remain separate. -/
namespace Solidity.Yul.Compilation.ArityShapes
open Backend Scalar LabelExec

theorem no_args (n depth : Nat) (p : Program)
    (emitted : (lowerNoArgs n).code depth = some p) :
    CodeShape p (n+depth) (n+depth+0) := by
  cases emitted
  exact .nil (n+depth)

theorem cons {n arity : Nat} {head : Vector Scalar.Word n → Scalar.Word}
    {rest : Vector Scalar.Word n → Vector Scalar.Word arity}
    (first : LoweredExpr n head) (suffix : LoweredArgs n arity rest)
    (firstShape : ∀ depth p, first.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (suffixShape : ∀ depth p, suffix.code depth = some p → CodeShape p (n+depth) (n+depth+arity))
    (depth : Nat) (p : Program) (emitted : (lowerArgCons first suffix).code depth = some p) :
    CodeShape p (n+depth) (n+depth+(1+arity)) := by
  obtain ⟨right,rightEmitted,rest⟩ := Option.bind_eq_some_iff.mp emitted
  obtain ⟨left,leftEmitted,same⟩ := Option.map_eq_some_iff.mp rest
  subst p
  have leftShape := firstShape (arity+depth) left leftEmitted
  rw [show n+(arity+depth) = n+depth+arity by omega,
    show n+depth+arity+1 = n+depth+(1+arity) by omega] at leftShape
  exact ExpressionShapes.append (suffixShape depth right rightEmitted) leftShape

theorem inline {n args results : Nat} {input : Vector Scalar.Word n → Vector Scalar.Word args}
    {output : Vector Scalar.Word args → Vector Scalar.Word results}
    (arguments : LoweredArgs n args input) (body : AritySlice args results output)
    (argumentShape : ∀ depth p, arguments.code depth = some p → CodeShape p (n+depth) (n+depth+args))
    (bodyShape : ∀ h, CodeShape body.code (h+args) (h+results))
    (depth : Nat) (p : Program) (emitted : (lowerInline arguments body).code depth = some p) :
    CodeShape p (n+depth) (n+depth+results) := by
  obtain ⟨code,argEmitted,same⟩ := Option.map_eq_some_iff.mp emitted
  subst p
  exact ExpressionShapes.append (argumentShape depth code argEmitted) (bodyShape (n+depth))

theorem unary {n : Nat} {value : Vector Scalar.Word n → Scalar.Word}
    (op : UnarySelection) (argument : LoweredExpr n value)
    (row : arity (.op op.opcode) = some (1,1))
    (argumentShape : ∀ depth p, argument.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (depth : Nat) (p : Program) (emitted : (lowerUnary op argument).code depth = some p) :
    CodeShape p (n+depth) (n+depth+1) := by
  obtain ⟨code,argEmitted,same⟩ := Option.map_eq_some_iff.mp emitted
  subst p
  exact ExpressionShapes.append (argumentShape depth code argEmitted)
    (.cons (.mk 1 1 (n+depth) row (by omega) (by omega)) (.nil (n+depth+1)))

theorem ternary {n : Nat} {a b c : Vector Scalar.Word n → Scalar.Word}
    (op : TernarySelection) (left : LoweredExpr n a) (right : LoweredExpr n b) (modulus : LoweredExpr n c)
    (row : arity (.op op.opcode) = some (3,1))
    (leftShape : ∀ depth p, left.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (rightShape : ∀ depth p, right.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (modulusShape : ∀ depth p, modulus.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (depth : Nat) (p : Program) (emitted : (lowerTernary op left right modulus).code depth = some p) :
    CodeShape p (n+depth) (n+depth+1) :=
  inline _ _ (cons left _ leftShape (cons right _ rightShape
      (cons modulus _ modulusShape (no_args n))))
    (fun h => .cons (.mk 3 1 h row (by omega) (by omega)) (.nil (h+1))) depth p emitted

/-- info: 'Solidity.Yul.Compilation.ArityShapes.no_args' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms no_args
/-- info: 'Solidity.Yul.Compilation.ArityShapes.cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms cons
/-- info: 'Solidity.Yul.Compilation.ArityShapes.inline' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms inline
/-- info: 'Solidity.Yul.Compilation.ArityShapes.unary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms unary
/-- info: 'Solidity.Yul.Compilation.ArityShapes.ternary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ternary

end Solidity.Yul.Compilation.ArityShapes
