import Solidity.Yul.Compilation.ExpressionShapes
import Solidity.Yul.Compilation.WordExpressions

/-! Operand metadata derived from actual WordExpressions.compile success.
Arithmetic, unsigned quotients, comparisons and unary word operations use the
unchanged original AST/compiler. No public child metadata or primitive row is
assumed; capacity, wider visitors and native/Source-G24 stay separate. -/
namespace Solidity.Yul.Compilation.WordVisitorShapes
open Backend Scalar LabelExec ProducerExpressions

private theorem binary_visit {fuel n : Nat} {args : Fin 2 → Solidity.Yul.Expr [] [] n 1}
    {op : Solidity.Yul.Pure 2} (bridge : BinaryBridge op)
    (row : arity (.op bridge.selection.opcode) = some (2,1))
    (leftLaws : ∀ (child : Compiled fuel (args 0)), WordExpressions.compile fuel (args 0) = some child →
      ∀ depth p, child.lowered.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (rightLaws : ∀ (child : Compiled fuel (args 1)), WordExpressions.compile fuel (args 1) = some child →
      ∀ depth p, child.lowered.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (compiled : Compiled (fuel+1) (.builtin (.pure op) args))
    (visited : (WordExpressions.compile fuel (args 0)).bind (fun left =>
      (WordExpressions.compile fuel (args 1)).bind (fun right => some (ProducerExpressions.binary bridge left right))) = some compiled)
    (depth : Nat) (p : Program) (emitted : compiled.lowered.code depth = some p) :
    CodeShape p (n+depth) (n+depth+1) := by
  obtain ⟨left,leftVisit,rest⟩ := Option.bind_eq_some_iff.mp visited
  obtain ⟨right,rightVisit,same⟩ := Option.bind_eq_some_iff.mp rest
  have equal : ProducerExpressions.binary bridge left right = compiled := Option.some.inj same
  subst compiled
  exact ExpressionShapes.binary bridge.selection left.lowered right.lowered row
    (leftLaws left leftVisit) (rightLaws right rightVisit) depth p emitted

private theorem unary_visit {fuel n : Nat} {args : Fin 1 → Solidity.Yul.Expr [] [] n 1}
    {op : Solidity.Yul.Pure 1} (bridge : WordExpressions.UnaryBridge op)
    (row : arity (.op bridge.selection.opcode) = some (1,1))
    (argLaws : ∀ (child : Compiled fuel (args 0)), WordExpressions.compile fuel (args 0) = some child →
      ∀ depth p, child.lowered.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (compiled : Compiled (fuel+1) (.builtin (.pure op) args))
    (visited : (WordExpressions.compile fuel (args 0)).bind
      (fun arg => some (WordExpressions.unary bridge arg)) = some compiled)
    (depth : Nat) (p : Program) (emitted : compiled.lowered.code depth = some p) :
    CodeShape p (n+depth) (n+depth+1) := by
  obtain ⟨arg,argVisit,same⟩ := Option.bind_eq_some_iff.mp visited
  have equal : WordExpressions.unary bridge arg = compiled := Option.some.inj same
  subst compiled
  change (arg.lowered.code depth).map (fun code => code++[.op bridge.selection.opcode]) = some p at emitted
  obtain ⟨code,argEmitted,codeSame⟩ := Option.map_eq_some_iff.mp emitted
  subst p
  exact ExpressionShapes.append (argLaws arg argVisit depth code argEmitted)
    (.cons (.mk 1 1 (n+depth) row (by omega) (by omega)) (.nil (n+depth+1)))

/-- A genuine successful visit and target emission derive operand metadata.
No blanket simulation theorem, child certificate or chosen run is a premise. -/
theorem visit_shape (fuel : Nat) : ∀ {n r : Nat} (expr : Solidity.Yul.Expr [] [] n r)
    (compiled : Compiled fuel expr), WordExpressions.compile fuel expr = some compiled →
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
        case «div» =>
          exact binary_visit QuotientExpressions.divBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case «mod» =>
          exact binary_visit QuotientExpressions.modBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case «lt» =>
          exact binary_visit WordExpressions.ltBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case «gt» =>
          exact binary_visit WordExpressions.gtBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case «eq» =>
          exact binary_visit WordExpressions.eqBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case «iszero» =>
          exact unary_visit WordExpressions.iszeroBridge rfl (ih (args 0)) compiled visited depth p emitted
        case «not» =>
          exact unary_visit WordExpressions.notBridge rfl (ih (args 0)) compiled visited depth p emitted
/-- info: 'Solidity.Yul.Compilation.WordVisitorShapes.visit_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms visit_shape
end Solidity.Yul.Compilation.WordVisitorShapes
