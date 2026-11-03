import Solidity.Yul.Compilation.ScopedStatements
import Solidity.Yul.Compilation.OpenStatements
/-! Existing producer raw binding evidence/program packing/certificate are reused.
Actual packed context placement is supplied by WordAdapter, never reconstructed. -/
namespace Solidity.Yul.Compilation.ScopedRawStatements
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
      case let_ =>
        intro F X c n r rhs body
        cases F
        · exact (supported fuel body).map (DirectBindings.Supported.let_ rhs)
        · exact ()
      case zero =>
        intro F X c n r body
        cases F
        · exact (supported fuel body).map (DirectBindings.Supported.zero r)
        · exact ()
      all_goals intro F; cases F <;> intros <;> first | exact none | exact ()
termination_by structural fuel

def compile {X c n} (fuel : Nat) (stmt : Stmt [] X c n) (policy : Policy.StmtP .A stmt) :
    Option (OpenStatements.Compiled fuel stmt policy) := do
  let support ← supported fuel stmt
  let packed ← ScopedStatements.compile fuel (WordAdapter.program stmt policy).code
  pure ⟨support,packed⟩
/-- Depth-zero scope execution, proved once for an actual packed certificate.
This avoids repeatedly normalizing its concrete producer context transports. -/
theorem executes {X c n fuel} {stmt : Stmt [] X c n} {policy : Policy.StmtP .A stmt}
    (compiled : OpenStatements.Compiled fuel stmt policy) (state : WordState X n)
    (code : Backend.Program) (emitted : compiled.packed.lowered.code 0 = some code) (tail : Backend.Scalar.Stack) :
    DirectBindings.eval fuel compiled.support policy state = some ⟨OpenStatements.updated compiled state,.normal⟩ ∧
    Backend.Scalar.run code ((OpenExpressions.encoded state).toList ++ tail) =
      some ((compiled.packed.update (OpenExpressions.encoded state)).toList ++ tail) :=
  ⟨OpenStatements.source compiled state,
   compiled.packed.lowered.correct 0 code emitted (OpenExpressions.encoded state) #v[] tail⟩
#print axioms executes
#print axioms supported
#print axioms compile
end Solidity.Yul.Compilation.ScopedRawStatements
