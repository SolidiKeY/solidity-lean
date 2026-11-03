import Solidity.Backend.FailurePaths.Statements

/-!
# Failure statements independent of the function return signature

The existing typed expression/error constructors are retagged only at their
phantom return signature. Actual execS equality proves this specialization;
no general AST erasure, untyped IR, return convention or new evaluator is used.
Literal and Boolean-custom recognition remains the published G21 decision.
-/
namespace Solidity.Backend.FailurePaths.Parametric
open Source

def Reverts {E : Source.Env} {R : List STy} {Γ Δ : RCtx}
    (global : Glob E) (frame : Fr) (fuel parameters : Nat)
    (stmt : RStmt E R false .body Γ Δ) (locals : Locals E.layout Γ)
    (state : St E) (payload : Roadmap.Bytes) : Prop :=
  (execS global frame fuel parameters none stmt locals).run (Source.L0 E, state) =
    (.error (.revert payload), (Source.L0 E, state))

def compile {E : Source.Env} {R : List STy} {Γ Δ : RCtx}
    (global : Glob E) (offset : Nat) (stmt : RStmt E R false .body Γ Δ) : Option Backend.Program :=
  match stmt with
  | .expr expr => compileExpression offset expr
  | .revertError error typed args =>
      Lowering.V08.BoolErrorStatement.emitStatement global offset
        (.revertError error typed args : RStmt E [] false .body Γ Γ)
  | _ => none

/-- Both actual source executions retain the same result/state at EVERY
horizon, including timeout. No return-slot or parameter convention is erased. -/
theorem expression_tag {E : Source.Env} {R : List STy} {Γ : RCtx} {τ : STy}
    (global : Glob E) (frame : Fr) (fuel parameters : Nat) (expr : RExpr E Γ τ)
    (locals : Locals E.layout Γ) (state : St E) :
    (execS global frame fuel parameters none (.expr expr : RStmt E R false .body Γ Γ) locals).run
      (Source.L0 E, state) =
    (execS global frame fuel 0 none (.expr expr : RStmt E [] false .body Γ Γ) locals).run
      (Source.L0 E, state) := by
  cases fuel <;> rfl

theorem error_tag {E : Source.Env} {R : List STy} {Γ : RCtx} {types : List STy}
    (global : Glob E) (frame : Fr) (fuel parameters : Nat) (error : Decl)
    (typed : error.paramTys E = some types) (args : RConvArgs E Γ types)
    (locals : Locals E.layout Γ) (state : St E) :
    (execS global frame fuel parameters none
      (.revertError error typed args : RStmt E R false .body Γ Γ) locals).run (Source.L0 E, state) =
    (execS global frame fuel 0 none
      (.revertError error typed args : RStmt E [] false .body Γ Γ) locals).run (Source.L0 E, state) := by
  cases fuel <;> rfl

/-- Every successful generic-return-signature decision has actual source and
checked target execution. Other body statements retain helper refusal. -/
theorem selected_correct {E : Source.Env} {R : List STy} {Γ Δ : RCtx}
    (global : Glob E) (frame : Fr) (extra parameters offset : Nat)
    (stmt : RStmt E R false .body Γ Δ) (code : Backend.Program)
    (selected : compile global offset stmt = some code)
    (locals : Locals E.layout Γ) (state : St E) :
    ∃ fuel payload, Reverts global frame fuel parameters stmt locals state payload ∧
      Emits code offset (.custom payload) := by
  cases stmt <;> simp only [compile] at selected
  all_goals first | cases selected | skip
  case expr τ expr =>
    obtain ⟨fuel, payload, source, target⟩ :=
      compiled_statement global frame extra offset (.expr expr) code selected locals state
    exact ⟨fuel, payload, (expression_tag global frame fuel parameters expr locals state).trans source, target⟩
  case revertError types error typed args =>
    obtain ⟨view, _, source, target⟩ := custom_statement global frame extra offset
      (.revertError error typed args) code selected locals state
    exact ⟨view.bits.length + extra + 4, _,
      (error_tag global frame _ parameters error typed args locals state).trans source, target⟩

#print axioms expression_tag
#print axioms error_tag
#print axioms selected_correct
end Solidity.Backend.FailurePaths.Parametric
