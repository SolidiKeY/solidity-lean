import Solidity.Yul.Compilation.OpenExpressions
import Solidity.Yul.Compilation.ProducerStatements
import Solidity.Yul.DirectBindings
/-! Actual raw external-cell writes and sequence compilation. Producer support
is derived by an actual-AST visitor, not assumed execution. Source/session/
pipeline typing and broader control/function/physical adequacy remain open. -/
namespace Solidity.Yul.Compilation.OpenStatements
open Backend Scalar
open Solidity.Yul.Closed

/-- Evidence traversal uses the SAME supplied source horizon as the compiler;
there is no independent cutoff or extra proof/execution budget. -/
def supported {X c n} (fuel : Nat) (stmt : Stmt [] X c n) :
    Option (DirectBindings.Supported X stmt) :=
  match fuel with
  | 0 => none
  | fuel+1 => by
      apply Stmt.casesOn (motive_1 := fun F X c n stmt =>
        match F with
        | [] => Option (DirectBindings.Supported X stmt)
        | _::_ => Unit) stmt
      case skip =>
        intro F X c n
        cases F
        · exact some (.base .skip)
        · exact ()
      case seq =>
        intro F X c n a b
        cases F
        · exact do
            let first ← supported fuel a
            let second ← supported fuel b
            pure (.seq first second)
        · exact ()
      case assign =>
        intro F X c n r targets rhs
        cases F
        · exact some (.base (.assign targets rhs))
        · exact ()
      all_goals intro F; cases F <;> intros <;> first | exact none | exact ()
termination_by structural fuel

structure Compiled {X c n} (fuel : Nat) (stmt : Stmt [] X c n) (policy : Policy.StmtP .A stmt) where
  support : DirectBindings.Supported X stmt
  packed : ProducerStatements.Compiled fuel (WordAdapter.program stmt policy).code

def compile {X c n} (fuel : Nat) (stmt : Stmt [] X c n) (policy : Policy.StmtP .A stmt) :
    Option (Compiled fuel stmt policy) := do
  let support ← supported fuel stmt
  let packed ← ProducerStatements.compile fuel (WordAdapter.program stmt policy).code
  pure ⟨support,packed⟩

def updated {X c n fuel} {stmt : Stmt [] X c n} {policy : Policy.StmtP .A stmt}
    (compiled : Compiled fuel stmt policy) (state : WordState X n) : WordState X n :=
  WordState.unpack (ProducerExpressions.sourceLocals (compiled.packed.update (OpenExpressions.encoded state)))

theorem source {X c n fuel} {stmt : Stmt [] X c n} {policy : Policy.StmtP .A stmt}
    (compiled : Compiled fuel stmt policy) (state : WordState X n) :
    DirectBindings.eval fuel compiled.support policy state = some ⟨updated compiled state,.normal⟩ := by
  rw [DirectBindings.run_agrees]
  have done := compiled.packed.source (OpenExpressions.encoded state)
  rw [OpenExpressions.encoded_locals] at done
  change (evalStmt fuel .nil True.intro (WordAdapter.program stmt policy).code
    (WordAdapter.program stmt policy).words state.pack).map _ = _
  rw [done]
  rfl

theorem executes {X c n fuel} {stmt : Stmt [] X c n} {policy : Policy.StmtP .A stmt}
    (compiled : Compiled fuel stmt policy) (state : WordState X n)
    (depth : Nat) (code : Program) (emitted : compiled.packed.lowered.code depth = some code)
    (newer : Vector Scalar.Word depth) (caller : Stack) :
    DirectBindings.eval fuel compiled.support policy state = some ⟨updated compiled state,.normal⟩ ∧
    run code (newer.toList ++ ((OpenExpressions.encoded state).toList ++ caller)) =
      some (newer.toList ++ ((compiled.packed.update (OpenExpressions.encoded state)).toList ++ caller)) :=
  ⟨source compiled state,compiled.packed.lowered.correct depth code emitted
    (OpenExpressions.encoded state) newer caller⟩
#print axioms supported
#print axioms compile
#print axioms source
#print axioms executes
end Solidity.Yul.Compilation.OpenStatements
