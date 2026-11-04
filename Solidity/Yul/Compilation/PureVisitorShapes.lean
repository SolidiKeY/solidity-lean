import Solidity.Yul.Compilation.ArityShapes
import Solidity.Yul.Compilation.ClzShapes
import Solidity.Yul.Compilation.PureExpressions

/-! Operand certificates derived from the actual full pure-expression visitor.
All recursive child shapes and primitive arity rows are discharged, including
software BYTE/CLZ. This supplies no native/G24 or every-prefix capacity proof. -/
namespace Solidity.Yul.Compilation.PureVisitorShapes
open Backend Scalar LabelExec ProducerExpressions
open WordExpressions BitExpressions SignedExpressions ModularExpressions RemainingWordBridges

private theorem binary_visit {fuel n : Nat} {args : Fin 2 → Solidity.Yul.Expr [] [] n 1}
    {op : Solidity.Yul.Pure 2} (bridge : BinaryBridge op)
    (row : arity (.op bridge.selection.opcode) = some (2,1))
    (leftLaws : ∀ (child : Compiled fuel (args 0)), PureExpressions.compile fuel (args 0) = some child →
      ∀ depth p, child.lowered.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (rightLaws : ∀ (child : Compiled fuel (args 1)), PureExpressions.compile fuel (args 1) = some child →
      ∀ depth p, child.lowered.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (compiled : Compiled (fuel+1) (.builtin (.pure op) args))
    (visited : (PureExpressions.compile fuel (args 0)).bind (fun left =>
      (PureExpressions.compile fuel (args 1)).bind (fun right => some (ProducerExpressions.binary bridge left right))) = some compiled)
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
    (argLaws : ∀ (child : Compiled fuel (args 0)), PureExpressions.compile fuel (args 0) = some child →
      ∀ depth p, child.lowered.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (compiled : Compiled (fuel+1) (.builtin (.pure op) args))
    (visited : (PureExpressions.compile fuel (args 0)).bind
      (fun arg => some (WordExpressions.unary bridge arg)) = some compiled)
    (depth : Nat) (p : Program) (emitted : compiled.lowered.code depth = some p) :
    CodeShape p (n+depth) (n+depth+1) := by
  obtain ⟨arg,argVisit,same⟩ := Option.bind_eq_some_iff.mp visited
  have equal : WordExpressions.unary bridge arg = compiled := Option.some.inj same
  subst compiled
  exact ArityShapes.unary bridge.selection arg.lowered row (argLaws arg argVisit) depth p emitted

private theorem ternary_visit {fuel n : Nat} {args : Fin 3 → Solidity.Yul.Expr [] [] n 1}
    {op : Solidity.Yul.Pure 3} (bridge : TernaryBridge op)
    (row : arity (.op bridge.selection.opcode) = some (3,1))
    (laws : ∀ i (child : Compiled fuel (args i)), PureExpressions.compile fuel (args i) = some child →
      ∀ depth p, child.lowered.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (compiled : Compiled (fuel+1) (.builtin (.pure op) args))
    (visited : (PureExpressions.compile fuel (args 0)).bind (fun left =>
      (PureExpressions.compile fuel (args 1)).bind (fun right =>
        (PureExpressions.compile fuel (args 2)).bind (fun modulus =>
          some (ModularExpressions.ternary bridge left right modulus)))) = some compiled)
    (depth : Nat) (p : Program) (emitted : compiled.lowered.code depth = some p) :
    CodeShape p (n+depth) (n+depth+1) := by
  obtain ⟨left,leftVisit,rest⟩ := Option.bind_eq_some_iff.mp visited
  obtain ⟨right,rightVisit,rest⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨modulus,modulusVisit,same⟩ := Option.bind_eq_some_iff.mp rest
  have equal : ModularExpressions.ternary bridge left right modulus = compiled := Option.some.inj same
  subst compiled
  exact ArityShapes.ternary bridge.selection left.lowered right.lowered modulus.lowered row
    (laws 0 left leftVisit) (laws 1 right rightVisit) (laws 2 modulus modulusVisit) depth p emitted

/-- The actual software BYTE body consumes two copies and returns one.
The two original locals and arbitrary caller are supplied by the lowerer. -/
theorem byte_expansion (h : Nat) : CodeShape byteExpansion (h+2) (h+1) := by
  refine .cons (m := h+3) (.mk 0 1 (h+2) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+4) (.mk 3 4 (h+0) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+5) (.mk 3 4 (h+1) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+6) (.mk 0 1 (h+5) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+5) (.mk 2 1 (h+4) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+6) (.mk 0 1 (h+5) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+5) (.mk 2 1 (h+4) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+4) (.mk 2 1 (h+3) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+3) (.mk 2 1 (h+2) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+4) (.mk 0 1 (h+3) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+5) (.mk 3 4 (h+1) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+4) (.mk 2 1 (h+3) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+3) (.mk 2 1 (h+2) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+3) (.mk 3 3 (h+0) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+2) (.mk 1 0 (h+2) rfl (by omega) (by omega)) ?_
  refine .cons (m := h+1) (.mk 1 0 (h+1) rfl (by omega) (by omega)) ?_
  exact .nil (h+1)

private theorem byte_visit {fuel n : Nat} {args : Fin 2 → Solidity.Yul.Expr [] [] n 1}
    (laws : ∀ i (child : Compiled fuel (args i)), PureExpressions.compile fuel (args i) = some child →
      ∀ depth p, child.lowered.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (compiled : Compiled (fuel+1) (.builtin (.pure .byte) args))
    (visited : (PureExpressions.compile fuel (args 0)).bind (fun left =>
      (PureExpressions.compile fuel (args 1)).bind (fun right =>
        some (PureExpressions.byte left right))) = some compiled)
    (depth : Nat) (p : Program) (emitted : compiled.lowered.code depth = some p) :
    CodeShape p (n+depth) (n+depth+1) := by
  obtain ⟨left,leftVisit,rest⟩ := Option.bind_eq_some_iff.mp visited
  obtain ⟨right,rightVisit,same⟩ := Option.bind_eq_some_iff.mp rest
  have equal : PureExpressions.byte left right = compiled := Option.some.inj same
  subst compiled
  exact ArityShapes.inline _ _ (ArityShapes.cons left.lowered _ (laws 0 left leftVisit)
    (ArityShapes.cons right.lowered _ (laws 1 right rightVisit) (ArityShapes.no_args n)))
    byte_expansion depth p emitted

private theorem clz_visit {fuel n : Nat} {args : Fin 1 → Solidity.Yul.Expr [] [] n 1}
    (laws : ∀ (child : Compiled fuel (args 0)), PureExpressions.compile fuel (args 0) = some child →
      ∀ depth p, child.lowered.code depth = some p → CodeShape p (n+depth) (n+depth+1))
    (compiled : Compiled (fuel+1) (.builtin (.pure .clz) args))
    (visited : (PureExpressions.compile fuel (args 0)).bind
      (fun argument => some (PureExpressions.clz argument)) = some compiled)
    (depth : Nat) (p : Program) (emitted : compiled.lowered.code depth = some p) :
    CodeShape p (n+depth) (n+depth+1) := by
  obtain ⟨argument,argVisit,same⟩ := Option.bind_eq_some_iff.mp visited
  have equal : PureExpressions.clz argument = compiled := Option.some.inj same
  subst compiled
  exact ClzShapes.lowering_shape argument.lowered (laws argument argVisit) depth p emitted

/-- Actual successful original-AST visit and emission derive all operand
metadata. No recursive child shape, primitive row or chosen run is assumed. -/
theorem visit_shape (fuel : Nat) : ∀ {n r : Nat} (expr : Solidity.Yul.Expr [] [] n r)
    (compiled : Compiled fuel expr), PureExpressions.compile fuel expr = some compiled →
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
        cases op
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
        case lt =>
          exact binary_visit ltBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case gt =>
          exact binary_visit gtBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case eq =>
          exact binary_visit eqBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case iszero =>
          exact unary_visit iszeroBridge rfl (ih (args 0)) compiled visited depth p emitted
        case «not» =>
          exact unary_visit notBridge rfl (ih (args 0)) compiled visited depth p emitted
        case «and» =>
          exact binary_visit andBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case «or» =>
          exact binary_visit orBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case «xor» =>
          exact binary_visit xorBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case «shl» =>
          exact binary_visit shlBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case «shr» =>
          exact binary_visit shrBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case sdiv =>
          exact binary_visit sdivBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case smod =>
          exact binary_visit smodBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case slt =>
          exact binary_visit sltBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case sgt =>
          exact binary_visit sgtBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case sar =>
          exact binary_visit sarBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case addmod =>
          exact ternary_visit addmodBridge rfl (fun i => ih (args i)) compiled visited depth p emitted
        case mulmod =>
          exact ternary_visit mulmodBridge rfl (fun i => ih (args i)) compiled visited depth p emitted
        case exp =>
          exact binary_visit expBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case signextend =>
          exact binary_visit signextendBridge rfl (ih (args 0)) (ih (args 1)) compiled visited depth p emitted
        case byte =>
          exact byte_visit (fun i => ih (args i)) compiled visited depth p emitted
        case clz =>
          exact clz_visit (ih (args 0)) compiled visited depth p emitted

/-- Source is the original closed Yul evaluator, at the actual source horizon.
The native machine, logical Source state and G24 relation are not substituted. -/
theorem source_target {fuel n r : Nat} (expr : Solidity.Yul.Expr [] [] n r)
    (compiled : Compiled fuel expr) (visited : PureExpressions.compile fuel expr = some compiled)
    (depth : Nat) (p : Program) (emitted : compiled.lowered.code depth = some p)
    (locals : Vector Scalar.Word n) (newer : Vector Scalar.Word depth) (caller : Stack) :
    (Solidity.Yul.Closed.evalExpr fuel .nil True.intro expr compiled.profile (sourceLocals locals) =
      some (fun _ => (compiled.value locals).toFin)) ∧
    CodeShape p (n+depth) (n+depth+1) ∧
    run p (newer.toList++(locals.toList++caller)) =
      some (compiled.value locals::(newer.toList++(locals.toList++caller))) :=
  ⟨compiled.source locals,visit_shape fuel expr compiled visited depth p emitted,
    compiled.lowered.correct depth p emitted locals newer caller⟩

/-- An actual caller-height packet additionally needs its real all-prefix
capacity check; successful scalar execution does not provide that check. -/
def packet {fuel n r : Nat} (expr : Solidity.Yul.Expr [] [] n r)
    (compiled : Compiled fuel expr) (visited : PureExpressions.compile fuel expr = some compiled)
    (depth extra : Nat) (p : Program) (emitted : compiled.lowered.code depth = some p)
    (room : stackBound p (n+depth+extra) = true) :
    Code (n+depth+extra) (n+depth+1+extra) where
  instructions := p
  shape := ShapeCapacity.code_lift (visit_shape fuel expr compiled visited depth p emitted) extra
  capacity := room

/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.byte_expansion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms byte_expansion
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.visit_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms visit_shape
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.source_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_target
/-- info: 'Solidity.Yul.Compilation.PureVisitorShapes.packet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms packet

end Solidity.Yul.Compilation.PureVisitorShapes
