import Solidity.Lowering.V08.SourceFailures
import Solidity.Lowering.V08.SourceEnvironmentControls

/-! Actual independent source reason execution and paid intrinsic rollback.
The source literal has no argument effects. No compiler/body selection, source
payment or general source/target storage relation is asserted. -/
namespace Solidity.Lowering.V08.SourceFailureControls
open Solidity
open SourceEnvironmentControls
open SourceFailures

-- Keep the full existing TRes value, using ordinary constructor equality.
private instance : DecidableEq (TRes Unit) := fun a b => by
  cases a with
  | error e =>
    cases b with
    | error f => exact decidable_of_iff (e = f) ⟨congrArg Except.error, Except.error.inj⟩
    | ok v => exact isFalse (fun h => Except.noConfusion h)
  | ok v =>
    cases b with
    | error e => exact isFalse (fun h => Except.noConfusion h)
    | ok u => exact decidable_of_iff (v = u) ⟨congrArg Except.ok, Except.ok.inj⟩

def binary : Roadmap.Bytes := [0, 0xff, 0x80]

theorem source_binary (pipeline : Roadmap.Pipeline) (horizon : Nat) :
    (Source.evalE (global pipeline) frame (horizon + 5) (reason binary)).run (locals, populated) =
      (.error (.revert (Semantics.encodeError binary)), (locals, populated)) :=
  eval_reason_transport (global pipeline) frame horizon binary locals populated

theorem source_binary_body (pipeline : Roadmap.Pipeline) (horizon : Nat) :
    (Source.execS (global pipeline) frame (horizon + 6) 0 none
      (.expr (reason binary) : Source.RStmt E [] false .body [.bool] [.bool]) locals).run
        (Source.L0 E, populated) =
      (.error (.revert (Source.errorData binary)), (Source.L0 E, populated)) :=
  exec_reason (global pipeline) frame horizon binary locals populated

theorem wrong_binary (pipeline : Roadmap.Pipeline) :
    ((Source.evalE (global pipeline) frame 5 (reason binary)).run (locals, populated)).1 ≠
      .error (.revert (Semantics.encodeError [0, 0xff, 0x7f])) := by
  rw [source_binary pipeline 0]
  intro same
  have bytes := Source.Halt.revert.inj (Except.error.inj same)
  exact (by decide +kernel : Semantics.encodeError binary ≠ Semantics.encodeError [0, 0xff, 0x7f]) bytes

theorem empty_reason_not_plain (pipeline : Roadmap.Pipeline) :
    ((Source.evalE (global pipeline) frame 5 (reason [])).run (locals, populated)).1 ≠
      .error (.revert []) := by
  rw [eval_reason_transport (global pipeline) frame 0 [] locals populated]
  intro same
  have bytes := Source.Halt.revert.inj (Except.error.inj same)
  exact (by decide +kernel : Semantics.encodeError [] ≠ []) bytes

theorem insufficient_horizon (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) frame 2 (reason binary)).run (locals, populated) =
      (.error .timeout, (locals, populated)) :=
  reason_low_horizon (global pipeline) frame binary locals populated

def entry : ContractWorld.Entry Controls.Cell Unit :=
  { locals := [], body := .cons (reasonStatement binary) .nil,
    result := fun _ => .ok (), payable := true }

def rollbackObservation : TRes (Option (Int × Int × Int × Int) × TRes Unit) := do
  let before ← Controls.setup
  let (after, result) := before.transact (fun world =>
    world.call (⟨Controls.self⟩ : ContractWorld.Handle ()) entry Controls.paidCtx)
  pure (Controls.observe after, result)

theorem paid_rollback : rollbackObservation.toOption =
    some (some (100, 0, 0, 0), .error (.revertWith (Semantics.encodeError binary))) := by decide +kernel

theorem wrong_paid_snapshot : rollbackObservation.toOption ≠
    some (some (93, 7, 0, 0), .error (.revertWith (Semantics.encodeError binary))) := by
  rw [paid_rollback]
  decide +kernel

theorem wrong_rollback_payload : rollbackObservation.toOption ≠
    some (some (100, 0, 0, 0), .error .revert) := by
  rw [paid_rollback]
  decide +kernel

def unaligned : Roadmap.Bytes := List.replicate 33 0xff

theorem source_unaligned (pipeline : Roadmap.Pipeline) :
    (Source.evalE (global pipeline) frame 5 (reason unaligned)).run (locals, populated) =
      (.error (.revert (Semantics.encodeError unaligned)), (locals, populated)) :=
  eval_reason_transport (global pipeline) frame 0 unaligned locals populated

#print axioms source_binary
#print axioms source_binary_body
#print axioms wrong_binary
#print axioms empty_reason_not_plain
#print axioms insufficient_horizon
#print axioms paid_rollback
#print axioms wrong_paid_snapshot
#print axioms wrong_rollback_payload
#print axioms source_unaligned
end Solidity.Lowering.V08.SourceFailureControls
