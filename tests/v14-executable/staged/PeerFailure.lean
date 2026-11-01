import Solidity.Backend.AbiWorld.ErrorEmission
import Solidity.Backend.Executable.CreationFrame

/-! Exact peer error-emission terminal consumed by an existing typed catch.
Private staged client: no fetched EVM/world/gas or source-lowering claim. -/
namespace Solidity.Backend.Executable.PeerFailure
open ContractWorld Semantics
open CreationFrame (C Γ caller reason caughtOut resumed)
open Failure

/-- Only an actual REVERT terminal enters the intrinsic Error handler.
An actual successful return is refused by this catch-only adapter. -/
def catchTerminal : Roadmap.Outcome → TRes (Out C caller.H Γ)
  | .revert bytes => TRun.block (Ext.push .refl)
      (CreationFrame.handler (.revertWith bytes)) caller
  | .success _ => .error .revert

def consume (run : Option (Slice.Machine × Option Roadmap.Outcome)) :
    Option (TRes (Out C caller.H Γ)) :=
  run.bind fun pair => pair.2.map catchTerminal

/-- The real producer executes through its terminal before the actual catch
handler sees those exact bytes. Fits/headroom remain architectural conditions. -/
theorem emitted_catch (a : Nat) (suffix : Program) (s : Slice.Machine)
    (fits : Fits a CreationFrame.payload) (room : s.stack.length + 2 ≤ 1024) :
    consume (Slice.checkedRun (AbiWorld.emitError a reason ++ suffix) s) =
      some CreationFrame.branch := by
  rw [AbiWorld.execute_error a reason suffix s fits room]
  rfl

/-- A nonempty protected stack and nonzero existing byte memory. The unsupported
ADD suffix must be ignored because REVERT already terminated the slice. -/
def machine : Slice.Machine :=
  ⟨[⟨17,by decide⟩,⟨29,by decide⟩], fun _ => 0x55⟩
def suffix : Program := [.op .ADD]
theorem fits_payload : Fits 32 CreationFrame.payload := by
  unfold Fits
  decide +kernel

theorem actual_slice :
    Slice.checkedRun (AbiWorld.emitError 32 reason ++ suffix) machine =
      some ({machine with memory := Slice.putBytes machine.memory 32 CreationFrame.payload},
        some (.revert CreationFrame.payload)) :=
  AbiWorld.execute_error 32 reason suffix machine fits_payload (by decide)

/-- Same exact failure packet enters the real creation caller catch, including
its old aliases and branch-local allocation/drop. No machine world is invented. -/
theorem constructor_catch :
    consume (Slice.checkedRun (AbiWorld.emitError 32 reason ++ suffix) machine) =
      some ((CreationFrame.attempt (.ok ()) CreationFrame.failing).map Prod.snd) := by
  rw [emitted_catch 32 suffix machine fits_payload (by decide),
    CreationFrame.branch_allocates, CreationFrame.caught_run]
  rfl

/-- The concrete catch result is exact, so the existing heap-dependent tail
runs on caughtOut rather than on the pre-catch heap. -/
theorem caught_result :
    consume (Slice.checkedRun (AbiWorld.emitError 32 reason ++ suffix) machine) =
      some (.ok caughtOut) := by
  rw [emitted_catch 32 suffix machine fits_payload (by decide), CreationFrame.branch_allocates]

/-- The independent fixed paidOne fixture stays distinct from the numeric slice.
Only the actual caught frame is passed to the existing world/typed tail. -/
def resumeTerminal (run : Option (Slice.Machine × Option Roadmap.Outcome)) :
    Option (TRes (World PaymentCheckpointChecks.contracts × Out C caller.H (.val .uint :: Γ))) :=
  (consume run).map fun selected => CreationTryFrame.tail caller
    (selected.map (WorldPrefixChecks.paidOne, ·)) CreationFrame.resume

theorem emitted_resume :
    resumeTerminal (Slice.checkedRun (AbiWorld.emitError 32 reason ++ suffix) machine) =
      some (.ok (WorldPrefixChecks.paidOne,
        ⟨resumed.st, caughtOut.ext.trans resumed.ext⟩)) := by
  unfold resumeTerminal
  rw [constructor_catch]
  change some (CreationTryFrame.tail caller
    (((CreationFrame.attempt (.ok ()) CreationFrame.failing).map Prod.snd).map
      (WorldPrefixChecks.paidOne, ·)) CreationFrame.resume) = _
  rw [CreationFrame.caught_run]
  exact congrArg some (CreationTryFrame.tail_success WorldPrefixChecks.paidOne caller _
    caughtOut CreationFrame.resume resumed rfl CreationFrame.tail_runs)

private theorem empty {α : Type} (r : Option α) (h : r.isNone = true) : r = none := by
  cases r with | none => rfl | some x => cases h

def crowded : Slice.Machine := {machine with stack := List.replicate 1023 ⟨17,by decide⟩}
theorem capacity_refused :
    Slice.checkedRun (AbiWorld.emitError 32 reason ++ suffix) crowded = none :=
  empty _ (by decide +kernel)

/-- The emitted packet also decodes to the actual reason through the supplied
peer decoder theorem; it is not raw ca/fe treated as Error(string). -/
theorem actual_reason : CatchKind.reason.decode CreationFrame.payload = some reason :=
  AbiWorld.catch_error reason (by decide +kernel)

theorem success_is_not_caught (bytes : List UInt8) :
    catchTerminal (.success bytes) = .error .revert := rfl

theorem raw_bytes_refused : catchTerminal (.revert [0xca,0xfe]) =
    .error (.revertWith [0xca,0xfe]) := by
  change TRun.block (Ext.push .refl)
    (CreationTryFrame.errorData (.revertWith [0xca,0xfe]) TRun.nil) caller = _
  unfold TRun.block
  rw [CreationTryFrame.errorData_refused _ _ caller (by decide +kernel)]
  rfl

/-- Actual emitted RETURN of exactly the same payload cannot enter a catch. -/
theorem returned_packet_refused :
    consume (Slice.checkedRun (emit 32 (.returned CreationFrame.payload) ++ suffix) machine) =
      some (.error .revert) := by
  rw [checkedRun_emit_suffix 32 (.returned CreationFrame.payload) suffix machine
    fits_payload (by decide)]
  rfl

theorem absent_result : consume none = none := rfl
theorem missing_terminal : consume (Slice.checkedRun [] machine) = none := rfl
theorem unsupported_slice : consume (Slice.checkedRun [.op .ADD] machine) = none := rfl

/-- info: 'Solidity.Backend.Executable.PeerFailure.actual_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_slice
/-- info: 'Solidity.Backend.Executable.PeerFailure.emitted_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms emitted_resume
/-- info: 'Solidity.Backend.Executable.PeerFailure.capacity_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms capacity_refused
/-- info: 'Solidity.Backend.Executable.PeerFailure.constructor_catch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms constructor_catch
/-- info: 'Solidity.Backend.Executable.PeerFailure.caught_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms caught_result
/-- info: 'Solidity.Backend.Executable.PeerFailure.actual_reason' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_reason
/-- info: 'Solidity.Backend.Executable.PeerFailure.raw_bytes_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_bytes_refused
/-- info: 'Solidity.Backend.Executable.PeerFailure.returned_packet_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms returned_packet_refused
/-- info: 'Solidity.Backend.Executable.PeerFailure.absent_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms absent_result
/-- info: 'Solidity.Backend.Executable.PeerFailure.missing_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms missing_terminal
/-- info: 'Solidity.Backend.Executable.PeerFailure.unsupported_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unsupported_slice
end Solidity.Backend.Executable.PeerFailure
