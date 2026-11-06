import Solidity.Yul.Compilation.PureVisitorShapes
import Solidity.Yul.Compilation.StatementVisitorShapes

/-! Balanced operand and original closed-source transport for the existing
full-pure assignment entry. Real RHS metadata is derived from compile success;
no function-frame, native, logical Source/G24 or capacity claim is inferred. -/
namespace Solidity.Yul.Compilation.PureAssignmentShapes
open Backend Scalar LabelExec Closed

/-- Actual assignment visit and emission discharge the RHS and scoped-slot
metadata. The original singleton target function remains the AST index. -/
theorem assignment_shape {fuel n : Nat} {c : Solidity.Yul.Control}
    (targets : Fin 1 → Solidity.Yul.Target [] n) (expr : Solidity.Yul.Expr [] [] n 1)
    (compiled : ProducerStatements.Compiled (fuel+1) (Solidity.Yul.Stmt.assign (c := c) targets expr))
    (visited : PureExpressions.assignment targets expr = some compiled)
    (depth : Nat) (p : Program) (emitted : compiled.lowered.code depth = some p) :
    CodeShape p (n+depth) (n+depth) := by
  obtain ⟨rhs,rhsVisit,same⟩ := Option.map_eq_some_iff.mp visited
  subst compiled
  exact StatementVisitorShapes.lowerAssign_shape (ProducerStatements.localTarget (targets 0)) rhs.lowered
    (PureVisitorShapes.visit_shape fuel expr rhs rhsVisit) depth p emitted

/-- Existing normal sequence builder for two actual same-horizon full-pure
assignment visits. This is not a replacement general statement visitor. -/
theorem sequence_shape {fuel n : Nat} {c : Solidity.Yul.Control}
    (targetsA targetsB : Fin 1 → Solidity.Yul.Target [] n)
    (exprA exprB : Solidity.Yul.Expr [] [] n 1)
    (first : ProducerStatements.Compiled (fuel+1) (Solidity.Yul.Stmt.assign (c := c) targetsA exprA))
    (second : ProducerStatements.Compiled (fuel+1) (Solidity.Yul.Stmt.assign (c := c) targetsB exprB))
    (firstVisit : PureExpressions.assignment targetsA exprA = some first)
    (secondVisit : PureExpressions.assignment targetsB exprB = some second)
    (depth : Nat) (p : Program) (emitted : (ProducerStatements.seq first second).lowered.code depth = some p) :
    CodeShape p (n+depth) (n+depth) := by
  change (first.lowered.code depth).bind (fun a =>
    (second.lowered.code depth).map (fun b => a++b)) = some p at emitted
  obtain ⟨a,firstEmission,rest⟩ := Option.bind_eq_some_iff.mp emitted
  obtain ⟨b,secondEmission,same⟩ := Option.map_eq_some_iff.mp rest
  subst p
  exact ExpressionShapes.append (assignment_shape targetsA exprA first firstVisit depth a firstEmission)
    (assignment_shape targetsB exprB second secondVisit depth b secondEmission)

/-- Same-horizon actual closed-Yul update and scalar execution preserve newer
locals and arbitrary caller contents; logical Solidity Source is separate. -/
theorem source_target {fuel n : Nat} {c : Solidity.Yul.Control}
    (targets : Fin 1 → Solidity.Yul.Target [] n) (expr : Solidity.Yul.Expr [] [] n 1)
    (compiled : ProducerStatements.Compiled (fuel+1) (Solidity.Yul.Stmt.assign (c := c) targets expr))
    (visited : PureExpressions.assignment targets expr = some compiled)
    (depth : Nat) (p : Program) (emitted : compiled.lowered.code depth = some p)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth) (caller : Stack) :
    (evalStmt (fuel+1) .nil True.intro (Solidity.Yul.Stmt.assign (c := c) targets expr)
      compiled.profile (ProducerExpressions.sourceLocals locals) =
      some ⟨ProducerExpressions.sourceLocals (compiled.update locals),.normal⟩) ∧
    CodeShape p (n+depth) (n+depth) ∧
    run p (newer.toList++(locals.toList++caller)) =
      some (newer.toList++((compiled.update locals).toList++caller)) :=
  ⟨compiled.source locals,assignment_shape targets expr compiled visited depth p emitted,
    compiled.lowered.correct depth p emitted locals newer caller⟩

/-- Balanced intrinsic packet; the actual complete-height all-prefix check
remains a separate obligation and is never inferred from scalar success. -/
def packet {fuel n : Nat} {c : Solidity.Yul.Control}
    (targets : Fin 1 → Solidity.Yul.Target [] n) (expr : Solidity.Yul.Expr [] [] n 1)
    (compiled : ProducerStatements.Compiled (fuel+1) (Solidity.Yul.Stmt.assign (c := c) targets expr))
    (visited : PureExpressions.assignment targets expr = some compiled)
    (depth extra : Nat) (p : Program) (emitted : compiled.lowered.code depth = some p)
    (room : stackBound p (n+depth+extra) = true) : Code (n+depth+extra) (n+depth+extra) where
  instructions := p
  shape := ShapeCapacity.code_lift (assignment_shape targets expr compiled visited depth p emitted) extra
  capacity := room

/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.assignment_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms assignment_shape
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.sequence_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms sequence_shape
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.source_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_target
/-- info: 'Solidity.Yul.Compilation.PureAssignmentShapes.packet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms packet

end Solidity.Yul.Compilation.PureAssignmentShapes
