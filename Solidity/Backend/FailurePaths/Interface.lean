import Solidity.Source.Eval
import Solidity.Backend.Failure.Unwind

/-!
# G38 statement-path interfaces

These predicates mention the existing indexed source statement and its actual
execution. Target execution is the published checked terminal instruction slice;
this interface does not identify it with the complete EVM evaluator. No producer
or general compiler correctness theorem is postulated here.
-/
namespace Solidity.Backend.FailurePaths
open Source

/-- Exact completed source failure, including the reached (possibly dirty) state.
The source evaluator does not itself restore a caller on revert. -/
def StatementReverts {E : Source.Env} {Γ Δ : RCtx}
    (global : Glob E) (frame : Fr) (fuel : Nat)
    (stmt : RStmt E [] false .body Γ Δ) (locals : Locals E.layout Γ)
    (initial reached : St E) (payload : Roadmap.Bytes) : Prop :=
  (execS global frame fuel 0 none stmt locals).run (Source.L0 E, initial) =
    (.error (.revert payload), (Source.L0 E, reached))

/-- Real checked execution, exact byte order, and terminal suffix absorption.
The existing nonwrapping allocation and stack premises are unchanged. -/
def Emits (code : Backend.Program) (offset : Nat) (input : Failure.Input) : Prop :=
  ∀ (suffix : Backend.Program) (machine : Failure.Slice.Machine),
    Failure.Fits offset input.bytes → machine.stack.length + 2 ≤ 1024 →
    Failure.Slice.checkedRun (code ++ suffix) machine =
      some ({machine with memory := Failure.Slice.putBytes machine.memory offset input.bytes},
        some input.observation)

/-- The immutable outcome is obtained before restoring the local checkpoint.
A producer of this predicate still owes its source/physical representation link. -/
def Unwinds {P T : Type} (checkpoint : Failure.Local.Checkpoint P T)
    (live : Failure.Local.Journal P T) (offset : Nat) (payload : Roadmap.Bytes) : Prop :=
  Failure.Local.execute checkpoint offset (.custom payload) live =
    some (Failure.Local.restore checkpoint, .revert payload)

end Solidity.Backend.FailurePaths
