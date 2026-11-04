import Solidity.Yul.Compilation.ArithmeticVisitorShapes
import Solidity.Yul.Compilation.ProducerStatements

/-! Actual normal statement-visitor operand metadata. Successful skip,
singleton assignment and sequence visits discharge recursive shape facts;
slot accessibility comes from actual emission. Values may change. Source/G24,
other visitors, full control and all-prefix/native capacity remain separate. -/
namespace Solidity.Yul.Compilation.StatementVisitorShapes
open Backend Scalar LabelExec

private theorem assign_shape {n : Nat} (i : Fin n) {value : Vector Scalar.Word n → Scalar.Word}
    (rhs : LoweredExpr n value)
    (rhsShape : ∀ depth p, rhs.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (depth : Nat) (p : Program) (emitted : (lowerAssign i rhs).code depth = some p) :
    CodeShape p (n+depth) (n+depth) := by
  change (if h : depth+i.val < 16 then (rhs.code depth).map
    (fun expr => expr++writeSlot ⟨depth+i.val,h⟩) else none) = some p at emitted
  split at emitted
  next accessible =>
    cases hr : rhs.code depth with
    | none => simp only [hr,Option.map_none] at emitted; cases emitted
    | some expr =>
      simp only [hr,Option.map_some] at emitted
      cases emitted
      have bounded := i.isLt
      exact ExpressionShapes.append (rhsShape depth expr hr)
        (.cons (m := n+depth+1) (.mk (depth+i.val+2) (depth+i.val+2) (n-(i.val+1))
          rfl (by omega) (by omega))
          (.cons (.mk 1 0 (n+depth) rfl (by omega) (by omega)) (.nil (n+depth))))
  next inaccessible => cases emitted

private theorem seq_shape {n : Nat} {first second : Vector Scalar.Word n → Vector Scalar.Word n}
    (a : LoweredStmt n first) (b : LoweredStmt n second)
    (leftLaws : ∀ depth p, a.code depth = some p → CodeShape p (n+depth) (n+depth))
    (rightLaws : ∀ depth p, b.code depth = some p → CodeShape p (n+depth) (n+depth))
    (depth : Nat) (p : Program) (emitted : (lowerSeq a b).code depth = some p) :
    CodeShape p (n+depth) (n+depth) := by
  change (a.code depth).bind (fun left => (b.code depth).map (fun right => left++right)) = some p at emitted
  cases ha : a.code depth with
  | none => simp only [ha,Option.bind_none] at emitted; cases emitted
  | some left =>
    cases hb : b.code depth with
    | none => simp only [ha,hb,Option.bind_some,Option.map_none] at emitted; cases emitted
    | some right =>
      simp only [ha,hb,Option.bind_some,Option.map_some] at emitted
      cases emitted
      exact ExpressionShapes.append (leftLaws depth left ha) (rightLaws depth right hb)

/-- Actual successful statement visit/emission gives balanced operand shapes.
No public child metadata, target-slot range or chosen run is assumed. -/
theorem visit_shape (fuel : Nat) : ∀ {c : Solidity.Yul.Control} {n : Nat}
    (stmt : Solidity.Yul.Stmt [] [] c n) (compiled : ProducerStatements.Compiled fuel stmt),
    ProducerStatements.compile fuel stmt = some compiled →
    ∀ depth p, compiled.lowered.code depth = some p → CodeShape p (n+depth) (n+depth) := by
  induction fuel with
  | zero =>
    intro c n stmt compiled visited
    cases visited
  | succ fuel ih =>
    intro c n stmt compiled visited depth p emitted
    cases stmt <;> try (change none = some compiled at visited; cases visited)
    case skip =>
      have same : ProducerStatements.skip fuel n = compiled := Option.some.inj visited
      subst compiled
      cases emitted
      exact .nil (n+depth)
    case seq a b =>
      change (ProducerStatements.compile fuel a).bind (fun first =>
        (ProducerStatements.compile fuel b).bind (fun second => some (ProducerStatements.seq first second))) = some compiled at visited
      obtain ⟨first,ha,rest⟩ := Option.bind_eq_some_iff.mp visited
      obtain ⟨second,hb,same⟩ := Option.bind_eq_some_iff.mp rest
      have equal : ProducerStatements.seq first second = compiled := Option.some.inj same
      subst compiled
      exact seq_shape first.lowered second.lowered (ih a first ha) (ih b second hb) depth p emitted
    case assign r targets expr =>
      cases r with
      | zero => cases visited
      | succ r =>
        cases r with
        | succ r => cases visited
        | zero =>
          change (ProducerExpressions.compile fuel expr).map (ProducerStatements.assignTargets targets) = some compiled at visited
          obtain ⟨rhs,rhsVisit,same⟩ := Option.map_eq_some_iff.mp visited
          subst compiled
          exact assign_shape (ProducerStatements.localTarget (targets 0)) rhs.lowered
            (ArithmeticVisitorShapes.visit_shape fuel expr rhs rhsVisit) depth p emitted
/-- info: 'Solidity.Yul.Compilation.StatementVisitorShapes.visit_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms visit_shape
end Solidity.Yul.Compilation.StatementVisitorShapes
