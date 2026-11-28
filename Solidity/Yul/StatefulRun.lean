import Solidity.Yul.OpenComposition

/-! Machine-state boundary for the retained word evaluators. The compatibility
entry points execute only their existing profiles: they do not interpret EVM
stateful builtins, consume gas, or establish external EVM agreement. -/
namespace Solidity.Yul.StatefulRun
open Closed

/-- Byte-addressed memory and word-addressed storage. Calldata is immutable input;
return data and revert status describe the current execution, not a call oracle. -/
structure Machine where
  storage : Word → Word
  memory : Nat → UInt8
  calldata : ByteArray
  returnData : ByteArray
  reverted : Bool

/-- A fresh invocation with empty storage, memory and output. -/
def Machine.empty (calldata : ByteArray := ByteArray.empty) : Machine :=
  ⟨fun _ => word 0, fun _ => 0, calldata, ByteArray.empty, false⟩

structure Result (α : Type) where
  value : α
  machine : Machine

/-- Fuel and erased word-profile evidence are passed unchanged to ClosedRun.
`none` means fuel exhaustion, never a revert or an unsupported operation. -/
def runClosed (fuel : Nat) {F c n} (environment : FunctionEnv F)
    (he : EnvWordP environment) (code : Stmt F [] c n) (hc : StmtWordP code)
    (vars : Values n) (machine : Machine) : Option (Result (Outcome c n)) :=
  (evalStmt fuel environment he code hc vars).map (fun value => ⟨value, machine⟩)

/-- Open Solidity cells keep OpenRun's original tier-A policy and lexical
function environment. The EVM machine is separate from those external cells. -/
def runOpen (fuel : Nat) {F X c n} (environment : OpenFunctions.PureEnvironment F)
    (code : Stmt F X c n) (policy : Policy.StmtP .A code)
    (state : WordState X n) (machine : Machine) :
    Option (Result (WordAdapter.Outcome X c n)) :=
  (OpenRun.statement fuel environment code policy state).map (fun value => ⟨value, machine⟩)

/-- Exact agreement includes exhaustion and the complete control-flow result. -/
theorem runClosed_agrees (fuel : Nat) {F c n} (environment : FunctionEnv F)
    (he : EnvWordP environment) (code : Stmt F [] c n) (hc : StmtWordP code)
    (vars : Values n) (machine : Machine) :
    (runClosed fuel environment he code hc vars machine).map Result.value =
      evalStmt fuel environment he code hc vars := by
  unfold runClosed
  cases evalStmt fuel environment he code hc vars <;> rfl

/-- Pure execution preserves all five machine components, on every completed run. -/
theorem runClosed_machine (fuel : Nat) {F c n} (environment : FunctionEnv F)
    (he : EnvWordP environment) (code : Stmt F [] c n) (hc : StmtWordP code)
    (vars : Values n) (machine : Machine) (result : Result (Outcome c n))
    (done : runClosed fuel environment he code hc vars machine = some result) :
    result.machine = machine := by
  unfold runClosed at done
  cases h : evalStmt fuel environment he code hc vars with
  | none => simp only [h, Option.map_none] at done; cases done
  | some value =>
    simp only [h, Option.map_some, Option.some.injEq] at done
    cases done
    rfl

/-- Reuse the established OpenRun correspondence, including its coordinate map;
no new simulation assumption is introduced. -/
theorem runOpen_agrees (fuel : Nat) {F X c n m} (coordinates : Coordinates X n m)
    (environment : OpenFunctions.PureEnvironment F) (code : Stmt F X c n)
    (policy : Policy.StmtP .A code) (state : WordState X n) (machine : Machine) :
    (runOpen fuel environment code policy state machine).map
        (fun result => Coordinates.encodeOutcome coordinates result.value) =
      evalStmt fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
        (WordAdapter.statement code policy coordinates.locals coordinates.cells).code
        (WordAdapter.statement code policy coordinates.locals coordinates.cells).words
        (coordinates.pack state) := by
  simp only [runOpen, Option.map_map, Function.comp_def]
  exact OpenRun.statement_agrees fuel coordinates environment code policy state

end Solidity.Yul.StatefulRun
