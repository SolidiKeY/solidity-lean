import Solidity.Examples.DecisionQuantLedger

/-! Runtime controls for the ledger/quantifier closer. Run with
`lake env lean -j1 --tstack=131072 --run tests/quant-ledger/Run.lean`.
Optional fixture names select a subset; no arguments runs every fixture.
The driver checks both public pipelines and retains every storage root
(including retained array slots), the complete ledger, and transaction fields.
-/

open Solidity Solidity.Decide Solidity.Examples.Decision Solidity.Examples.DecisionKInt
open Solidity.Examples.DecisionQuantLedger

private def fixtures : List (String × Fml Gaps [] × String) :=
  [("original", gapQuantLedger, "proved"), ("bad", bad, "refuted"),
   ("aliasOk", aliasOk, "proved"), ("aliasBad", aliasBad, "refuted"),
   ("distinctBad", distinctBad, "refuted"), ("paymentOk", paymentOk, "proved"),
   ("paymentBad", paymentBad, "refuted"), ("highOk", highOk, "proved"),
   ("highBad", highBad, "refuted"), ("negativeBad", negativeBad, "refuted"),
   ("paramOk", paramOk, "proved"), ("paramBad", paramBad, "refuted")]

private def label : LeafVerdict Gaps → String
  | .proved => "proved"
  | .refuted _ => "refuted"
  | .unknown => "unknown"

private def observations (σ : State Gaps []) : String :=
  s!"storage={Solidity.Tools.fmtStorageLine Gaps σ.storage true}; ledger={reprStr σ.net.entries}; self={σ.tx.selfAddress.1}; balance={σ.selfBalance.1}; sender={σ.tx.msgSender.1}; value={σ.tx.msgValue.1}; timestamp={σ.tx.timestamp.1}; heapObjects={σ.H.length}; externalResponses={σ.tx.ext.length}"

def main (args : List String) : IO UInt32 := do
  if args.any (fun a => !fixtures.any (fun f => f.1 == a)) then
    IO.eprintln "unknown fixture name"
    return 2
  let selected := fixtures.filter (fun f => args.isEmpty || args.contains f.1)
  let pipelines : List (String × (Fml Gaps [] → LeafVerdict Gaps)) :=
    [("decideLeaf", decideLeaf), ("decideGoal", decideGoal)]
  let out ← IO.getStdout
  for (name, φ, expected) in selected do
    for (pipeline, decider) in pipelines do
      out.putStrLn s!"BEGIN {name} {pipeline}"
      out.flush
      let start ← IO.monoMsNow
      let result := decider φ
      out.putStrLn s!"VERDICT {name} {pipeline}: {label result}"
      match result with
      | .refuted σ =>
        out.putStrLn s!"OBSERVATIONS {name} {pipeline}: {observations σ}"
        if name == "highBad" && !(Decidable.decide (ledgerAt σ.net (uintOfNat 0) > (2^256 : Int) - 1)) then
          throw (IO.userError "upper-bound countercontrol did not exhibit an unbounded entry")
        if name == "negativeBad" && !(Decidable.decide (ledgerAt σ.net (uintOfNat 0) < 0)) then
          throw (IO.userError "negative countercontrol did not exhibit a negative entry")
      | _ => pure ()
      if label result != expected then
        throw (IO.userError s!"{name} {pipeline}: expected {expected}, got {label result}")
      let finish ← IO.monoMsNow
      out.putStrLn s!"MILLISECONDS {name} {pipeline}: {finish - start}"
      out.flush
  out.putStrLn s!"PASS {selected.length} fixtures, {2 * selected.length} pipeline results"
  return 0
