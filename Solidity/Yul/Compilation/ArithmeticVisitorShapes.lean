import Solidity.Yul.Compilation.ExpressionShapes

/-! Actual ProducerExpressions.compile success closes recursive operand-shape
obligations for its arithmetic domain. No supplied child metadata or arity row
remains in the public theorem. Other visitors, capacity, logical Source/G24
and native execution are not covered by this result. -/
namespace Solidity.Yul.Compilation.ArithmeticVisitorShapes
open Backend Scalar LabelExec ProducerExpressions

private theorem binary_visit {fuel n : Nat} {args : Fin 2 → Solidity.Yul.Expr [] [] n 1}
    {op : Solidity.Yul.Pure 2} (bridge : BinaryBridge op)
    (row : arity (.op bridge.selection.opcode) = some (2,1))
    (leftLaws : ∀ (child : Compiled fuel (args 0)), compile fuel (args 0) = some child →
      ∀ depth p, child.lowered.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (rightLaws : ∀ (child : Compiled fuel (args 1)), compile fuel (args 1) = some child →
      ∀ depth p, child.lowered.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (compiled : Compiled (fuel+1) (.builtin (.pure op) args))
    (visited : (compile fuel (args 0)).bind (fun left =>
      (compile fuel (args 1)).bind (fun right => some (ProducerExpressions.binary bridge left right))) = some compiled)
    (depth : Nat) (p : Program) (emitted : compiled.lowered.code depth = some p) :
    CodeShape p (n+depth) (n+depth+1) := by
  obtain ⟨left,leftVisit,rest⟩ := Option.bind_eq_some_iff.mp visited
  obtain ⟨right,rightVisit,same⟩ := Option.bind_eq_some_iff.mp rest
  have equal : ProducerExpressions.binary bridge left right = compiled := Option.some.inj same
  subst compiled
  exact ExpressionShapes.binary bridge.selection left.lowered right.lowered row
    (leftLaws left leftVisit) (rightLaws right rightVisit) depth p emitted

/-- A genuine successful visit and target emission derive operand metadata.
No blanket simulation theorem, child certificate or chosen run is a premise. -/
theorem visit_shape (fuel : Nat) : ∀ {n r : Nat} (expr : Solidity.Yul.Expr [] [] n r)
    (compiled : Compiled fuel expr), compile fuel expr = some compiled →
    ∀ depth p, compiled.lowered.code depth = some p → CodeShape p (n+depth) (n+depth+1) := by
  induction fuel with
  | zero =>
    intro n r expr compiled visited
    cases visited
  | succ fuel ih =>
    intro n r expr compiled visited depth p emitted
    cases expr with
    | literal w =>
      have same : ProducerExpressions.literal fuel w = compiled := Option.some.inj visited
      subst compiled
      exact ExpressionShapes.literal (BitVec.ofFin w) depth p emitted
    | «local» i =>
      have same : localExpr fuel i = compiled := Option.some.inj visited
      subst compiled
      exact ExpressionShapes.local_shape i depth p emitted
    | external ref => cases ref.index
    | call f args => cases f
    | builtin builtin args =>
      cases builtin <;> try (change none = some compiled at visited; cases visited)
      case pure op =>
        cases op <;> try (change none = some compiled at visited; cases visited)
        case add =>
          exact binary_visit addBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case sub =>
          exact binary_visit subBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case mul =>
          exact binary_visit mulBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
/-- info: 'Solidity.Yul.Compilation.ArithmeticVisitorShapes.visit_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms visit_shape
end Solidity.Yul.Compilation.ArithmeticVisitorShapes
