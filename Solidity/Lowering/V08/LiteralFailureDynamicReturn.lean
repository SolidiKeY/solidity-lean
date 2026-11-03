import Solidity.Lowering.V08.LiteralFailureDynamicListError
import Solidity.Backend.FailurePaths.Returns

/-! G41 discharges the published G38 actual-encoding premise for arbitrary
ordered byte-reference lists. The terminal and checkpoint are component-local,
not an unknown-memory encoder or full Source return-statement compiler. -/
namespace Solidity.Lowering.V08.LiteralFailureDynamicReturn
open Solidity Source Backend

def payload (packets : List Roadmap.Bytes) : Roadmap.Bytes :=
 AbiEntry.encodeArgs (LiteralFailureDynamicListError.abiValues packets)

/-- Only intrinsic local/heap equations are required, not a desired encoder run. -/
theorem encodingAt {E : Env} {Γ : RCtx} (F : Fr) (fuel : Nat)
 (refs : List (Source.Idx Γ (.bytes .memory))) (packets : List Roadmap.Bytes)
 (locals : Locals E.layout Γ) (state : St E)
 (memory : LiteralFailureDynamicListError.all_represented locals state refs packets) :
 FailurePaths.Premises.EncodingAt F fuel (LiteralFailureDynamicListError.values locals refs).toR state state (payload packets) := by
 simpa only [payload,LiteralFailureDynamicListError.abi_agreement] using
  LiteralFailureDynamicListError.encoding_run F fuel refs packets locals (Source.L0 E) state memory

/-- Actual G38 consumer application: its encoding premise is discharged.
The saved caller and encoded live stores remain distinct explicit states. -/
theorem return_transport {E : Env} {Γ : RCtx} (F : Fr) (fuel address : Nat)
 (refs : List (Source.Idx Γ (.bytes .memory))) (packets : List Roadmap.Bytes)
 (locals : Locals E.layout Γ) (state savedSource : St E)
 (memory : LiteralFailureDynamicListError.all_represented locals state refs packets)
 (saved live : Failure.Slice.Machine)
 (fits : Failure.Fits address (payload packets)) (stack : live.stack.length+2≤1024) :
 FailurePaths.Premises.EncodingAt F fuel (LiteralFailureDynamicListError.values locals refs).toR state state (payload packets) ∧
 FailurePaths.Emits (Failure.emit address (.returned (payload packets))) address (.returned (payload packets)) ∧
 Failure.Local.execute (Failure.Local.save (MemoryOps.Physical.worldJournal savedSource.ex saved))
 address (.returned (payload packets)) (MemoryOps.Physical.worldJournal state.ex live)=
 some (MemoryOps.Physical.worldJournal state.ex
  {live with memory:=Failure.Slice.putBytes live.memory address (payload packets)},.success (payload packets)) :=
 FailurePaths.encoded_return F fuel address (LiteralFailureDynamicListError.values locals refs).toR state state savedSource
  (payload packets) (encodingAt F fuel refs packets locals state memory) saved live fits stack
end Solidity.Lowering.V08.LiteralFailureDynamicReturn
