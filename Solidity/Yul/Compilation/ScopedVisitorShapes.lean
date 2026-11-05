import Solidity.Yul.Compilation.PureAssignmentShapes
import Solidity.Yul.Compilation.ScopedStatements

/-! Operand shapes from the actual let/zero/sequence/full-pure assignment
visitor. Scope selection still requires empty newer depth; capacity and
logical Source/G24/native/function/physical correctness remain separate. -/
namespace Solidity.Yul.Compilation.ScopedVisitorShapes
open Backend Scalar LabelExec ProducerExpressions ProducerStatements

theorem push_shape (xs : Stack) (h : Nat) : CodeShape (pushPrefix xs) h (h+xs.length) := by
  induction xs with
  | nil => exact .nil h
  | cons x xs ih =>
    change CodeShape (pushPrefix xs++[pushWord x]) h (h+(xs.length+1))
    exact ExpressionShapes.append ih
      (.cons (.mk 0 1 (h+xs.length) rfl (by omega) (by omega)) (.nil (h+(xs.length+1))))

theorem pop_shape (count h : Nat) : CodeShape (popPrefix count) (h+count) h := by
  induction count with
  | zero => exact .nil h
  | succ count ih =>
    exact .cons (.mk 1 0 (h+count) rfl (by omega) (by omega)) ih

/-- Actual scope emission forces depthzero. The fresh prefix is removed after
its real extended-context body, without changing that body's context indices. -/
theorem scope_shape {n fresh : Nat} {values : Vector Scalar.Word n → Vector Scalar.Word fresh}
    {update : Vector Scalar.Word (fresh+n) → Vector Scalar.Word (fresh+n)}
    (initializers : LoweredArgs n fresh values) (body : LoweredStmt (fresh+n) update)
    (initialShape : ∀ depth p, initializers.code depth = some p → CodeShape p (n+depth) (n+depth+fresh))
    (bodyShape : ∀ depth p, body.code depth = some p → CodeShape p (fresh+n+depth) (fresh+n+depth))
    (depth : Nat) (p : Program) (emitted : (lowerLocalScope initializers body).code depth = some p) :
    CodeShape p (n+depth) (n+depth) := by
  by_cases zero : depth = 0
  · subst depth
    change (initializers.code 0).bind (fun a => (body.code 0).map
      (fun b => a++b++popPrefix fresh)) = some p at emitted
    obtain ⟨a,ha,rest⟩ := Option.bind_eq_some_iff.mp emitted
    obtain ⟨b,hb,same⟩ := Option.map_eq_some_iff.mp rest
    subst p
    have entry := initialShape 0 a ha
    have inside := bodyShape 0 b hb
    simp only [Nat.add_zero] at entry inside ⊢
    rw [show n+fresh = fresh+n by omega] at entry
    have exit := pop_shape fresh n
    rw [show n+fresh = fresh+n by omega] at exit
    exact ExpressionShapes.append (ExpressionShapes.append entry inside) exit
  · change (if depth = 0 then _ else none) = some p at emitted
    simp only [zero,ite_false] at emitted
    cases emitted

private theorem zero_shape (n fresh depth : Nat) (p : Program)
    (emitted : (ScopedStatements.zeroArguments n fresh).code depth = some p) :
    CodeShape p (n+depth) (n+depth+fresh) := by
  cases emitted
  have shape := push_shape (Vector.replicate fresh (0 : Scalar.Word)).toList (n+depth)
  simpa only [Vector.length_toList] using shape

/-- Actual original-AST visit/emission derives all recursive operand facts.
The successful domain remains the existing scoped visitor's domain. -/
theorem visit_shape (fuel : Nat) : ∀ {c : Solidity.Yul.Control} {n : Nat}
    (stmt : Solidity.Yul.Stmt [] [] c n) (compiled : ProducerStatements.Compiled fuel stmt),
    ScopedStatements.compile fuel stmt = some compiled →
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
      change (ScopedStatements.compile fuel a).bind (fun first =>
        (ScopedStatements.compile fuel b).bind (fun second => some (ProducerStatements.seq first second))) = some compiled at visited
      obtain ⟨first,ha,rest⟩ := Option.bind_eq_some_iff.mp visited
      obtain ⟨second,hb,same⟩ := Option.bind_eq_some_iff.mp rest
      have equal : ProducerStatements.seq first second = compiled := Option.some.inj same
      subst compiled
      exact StatementVisitorShapes.lowerSeq_shape first.lowered second.lowered
        (ih a first ha) (ih b second hb) depth p emitted
    case assign r targets expr =>
      cases r with
      | zero => cases visited
      | succ r =>
        cases r with
        | succ r => cases visited
        | zero =>
          change (PureExpressions.compile fuel expr).map (ProducerStatements.assignTargets targets) = some compiled at visited
          exact PureAssignmentShapes.assignment_shape targets expr compiled visited depth p emitted
    case let_ r rhs body =>
      cases r with
      | zero => cases visited
      | succ r =>
        cases r with
        | succ r => cases visited
        | zero =>
          change (PureExpressions.compile fuel rhs).bind (fun initializer =>
            (ScopedStatements.compile fuel body).bind (fun scope =>
              some (ScopedStatements.letOne initializer scope))) = some compiled at visited
          obtain ⟨initializer,hi,rest⟩ := Option.bind_eq_some_iff.mp visited
          obtain ⟨scope,hb,same⟩ := Option.bind_eq_some_iff.mp rest
          have equal : ScopedStatements.letOne initializer scope = compiled := Option.some.inj same
          subst compiled
          exact scope_shape _ _ (PureVisitorShapes.visit_shape fuel rhs initializer hi)
            (ih body scope hb) depth p emitted
    case zero fresh body =>
      change (ScopedStatements.compile fuel body).map ScopedStatements.zero = some compiled at visited
      obtain ⟨scope,hb,same⟩ := Option.map_eq_some_iff.mp visited
      subst compiled
      exact scope_shape _ _ (zero_shape n fresh) (ih body scope hb) depth p emitted

/-- Original closed-source normal update and actual scalar run, with derived
balanced operand metadata. Logical Solidity Source/G24 remains separate. -/
theorem source_target {fuel n : Nat} {c : Solidity.Yul.Control}
    (stmt : Solidity.Yul.Stmt [] [] c n) (compiled : ProducerStatements.Compiled fuel stmt)
    (visited : ScopedStatements.compile fuel stmt = some compiled)
    (depth : Nat) (p : Program) (emitted : compiled.lowered.code depth = some p)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth) (caller : Stack) :
    (Solidity.Yul.Closed.evalStmt fuel .nil True.intro stmt compiled.profile (sourceLocals locals) =
      some ⟨sourceLocals (compiled.update locals),.normal⟩) ∧
    CodeShape p (n+depth) (n+depth) ∧
    run p (newer.toList++(locals.toList++caller)) =
      some (newer.toList++((compiled.update locals).toList++caller)) :=
  ⟨compiled.source locals,visit_shape fuel stmt compiled visited depth p emitted,
    compiled.lowered.correct depth p emitted locals newer caller⟩

/-- Extra caller words lift operand shape; their actual all-prefix capacity
is a separate required check, never inferred from the source/scalar result. -/
def packet {fuel n : Nat} {c : Solidity.Yul.Control}
    (stmt : Solidity.Yul.Stmt [] [] c n) (compiled : ProducerStatements.Compiled fuel stmt)
    (visited : ScopedStatements.compile fuel stmt = some compiled)
    (depth extra : Nat) (p : Program) (emitted : compiled.lowered.code depth = some p)
    (room : stackBound p (n+depth+extra) = true) : Code (n+depth+extra) (n+depth+extra) where
  instructions := p
  shape := ShapeCapacity.code_lift (visit_shape fuel stmt compiled visited depth p emitted) extra
  capacity := room

/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.push_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms push_shape
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.pop_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms pop_shape
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.scope_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms scope_shape
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.visit_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms visit_shape
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.source_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_target
/-- info: 'Solidity.Yul.Compilation.ScopedVisitorShapes.packet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms packet

end Solidity.Yul.Compilation.ScopedVisitorShapes
