import Solidity.Backend.FailurePaths.Interface
import Solidity.Lowering.V08.LiteralFailureLowering
import Solidity.Lowering.V08.BoolErrorStatement

/-!
# Completed failure statements

The compiler reuses G21's literal recognizer and Boolean custom-error selector.
The new statement bridge accounts for the actual source statement boundary and
its reached state. This remains checked instruction-slice compilation: no full
EVM representation, gas adequacy or arbitrary runtime ABI encoder is inferred.
-/
namespace Solidity.Backend.FailurePaths
open Source

/-- Lifting an actual expression failure through the source statement evaluator
retains its reached state, including any effects made before the halt. -/
theorem expression_statement {E : Source.Env} {Γ : RCtx} {τ : STy}
    (global : Glob E) (frame : Fr) (fuel : Nat) (expr : RExpr E Γ τ)
    (locals next : Locals E.layout Γ) (initial reached : St E) (payload : Roadmap.Bytes)
    (evaluated : (evalE global frame fuel expr).run (locals, initial) =
      (.error (.revert payload), (next, reached))) :
    StatementReverts global frame (fuel + 1) (.expr expr) locals initial reached payload := by
  simp only [ExceptT.run] at evaluated
  simp only [StatementReverts, execS, EM.sub, evaluated, bind, pure,
    ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.mk, StateT.bind, StateT.pure]

/-- No expression is evaluated during this partial compilation decision. -/
def compileExpression {E : Source.Env} {Γ : RCtx} {τ : STy}
    (offset : Nat) (expr : RExpr E Γ τ) : Option Backend.Program :=
  Lowering.V08.LiteralFailureLowering.emitLiteral offset expr

/-- Partial compilation over the existing indexed statement, with no new IR.
Expressions use the literal failure selector; other statements use the existing
Boolean custom-error selector. Unsupported statements retain named refusal. -/
def compileStatement {E : Source.Env} {Γ Δ : RCtx} (global : Glob E) (offset : Nat)
    (stmt : RStmt E [] false .body Γ Δ) : Option Backend.Program :=
  match stmt with
  | .expr expr => compileExpression offset expr
  | _ => Lowering.V08.BoolErrorStatement.emitStatement global offset stmt

/-- A successful indexed custom-error decision selects the same public code. -/
theorem compile_custom_selected {E : Source.Env} {Γ Δ : RCtx}
    (global : Glob E) (offset : Nat) (stmt : RStmt E [] false .body Γ Δ)
    (code : Backend.Program)
    (selected : Lowering.V08.BoolErrorStatement.emitStatement global offset stmt = some code) :
    compileStatement global offset stmt = some code := by
  obtain ⟨view, _⟩ := Lowering.V08.BoolErrorStatement.selected_witness global offset stmt code selected
  cases view.contexts
  have syntaxEq : stmt = Lowering.V08.BoolErrorLowering.statement view.error view.bits view.typed :=
    eq_of_heq view.same
  rw [syntaxEq] at selected ⊢
  exact selected

/-- Actual successful recognition supplies both the source statement failure
and execution of its emitted bytes. The input observation is proved to be a
revert, so a return emitter cannot enter this theorem. -/
theorem literal_statement {E : Source.Env} {Γ : RCtx} {τ : STy}
    (global : Glob E) (frame : Fr) (extra offset : Nat) (expr : RExpr E Γ τ)
    (input : Failure.Input) (selected : Lowering.V08.LiteralFailureLowering.literalInput expr = some input)
    (locals : Locals E.layout Γ) (state : St E) :
    compileStatement global offset (.expr expr) = some (Failure.emit offset input) ∧
    StatementReverts global frame (extra + 7) (.expr expr) locals state state input.bytes ∧
    input.observation = .revert input.bytes ∧
    Emits (Failure.emit offset input) offset input := by
  obtain ⟨source, outcome⟩ := Lowering.V08.LiteralFailureLowering.literalInput_sound global frame extra locals state expr input selected
  refine ⟨?_, ?_, outcome, ?_⟩
  · simp only [compileStatement, compileExpression, Lowering.V08.LiteralFailureLowering.emitLiteral, selected, Option.map_some]
  · exact expression_statement global frame (extra + 6) expr locals locals state state input.bytes source
  · exact Failure.checkedRun_emit_suffix offset input

/-- This consumes the existing indexed custom-error selector rather than
introducing a second custom-error argument elaborator or ABI encoder. -/
theorem custom_statement {E : Source.Env} {Γ Δ : RCtx}
    (global : Glob E) (frame : Fr) (extra offset : Nat)
    (stmt : RStmt E [] false .body Γ Δ) (code : Backend.Program)
    (selected : Lowering.V08.BoolErrorStatement.emitStatement global offset stmt = some code)
    (locals : Locals E.layout Γ) (state : St E) :
    ∃ view : Lowering.V08.BoolErrorStatement.StatementView stmt,
      compileStatement global offset stmt = some code ∧
      StatementReverts global frame (view.bits.length + extra + 4) stmt locals state state
        (Lowering.V08.BoolErrorLowering.payload global view.error view.bits) ∧
      Emits code offset (.custom (Lowering.V08.BoolErrorLowering.payload global view.error view.bits)) := by
  obtain ⟨view, _, source, target⟩ :=
    Lowering.V08.BoolErrorStatement.selected_correct global frame extra offset stmt code selected locals state
  exact ⟨view, compile_custom_selected global offset stmt code selected, source, target⟩

/-- Every successful decision of the public partial statement compiler has an
actual completed source run and matching checked target bytes. The fuel is an
explicit finite witness, never a replacement for a timed-out source execution. -/
theorem compiled_statement {E : Source.Env} {Γ Δ : RCtx}
    (global : Glob E) (frame : Fr) (extra offset : Nat)
    (stmt : RStmt E [] false .body Γ Δ) (code : Backend.Program)
    (compiled : compileStatement global offset stmt = some code)
    (locals : Locals E.layout Γ) (state : St E) :
    ∃ fuel payload, StatementReverts global frame fuel stmt locals state state payload ∧
      Emits code offset (.custom payload) := by
  have custom {Δ : RCtx} (s : RStmt E [] false .body Γ Δ)
      (selected : Lowering.V08.BoolErrorStatement.emitStatement global offset s = some code) :
      ∃ fuel payload, StatementReverts global frame fuel s locals state state payload ∧
        Emits code offset (.custom payload) := by
    obtain ⟨view, _, source, target⟩ := custom_statement global frame extra offset s code selected locals state
    exact ⟨view.bits.length + extra + 4, _, source, target⟩
  cases stmt <;> try exact custom _ compiled
  case expr τ expr =>
    simp only [compileStatement, compileExpression, Lowering.V08.LiteralFailureLowering.emitLiteral] at compiled
    cases selected : Lowering.V08.LiteralFailureLowering.literalInput expr with
    | none => simp only [selected, Option.map_none, reduceCtorEq] at compiled
    | some input =>
      simp only [selected, Option.map_some, Option.some.injEq] at compiled
      subst code
      obtain ⟨_, source, outcome, target⟩ :=
        literal_statement global frame extra offset expr input selected locals state
      refine ⟨extra + 7, input.bytes, source, ?_⟩
      intro suffix machine fits stack
      have result := target suffix machine fits stack
      rw [outcome] at result
      exact result

#print axioms expression_statement
#print axioms literal_statement
#print axioms custom_statement
#print axioms compiled_statement
end Solidity.Backend.FailurePaths
