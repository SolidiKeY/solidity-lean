import Solidity.Lowering.V08.LiteralFailureLowering
import Solidity.Lowering.V08.SourceAbi
import Solidity.Semantics.AbiEntry
import Solidity.Backend.AbiWorld.ErrorRoundtrip

/-! G21 actual Source Error packets, intrinsic ABI encoding and the existing
constant-value terminal emitter. Generic AbiEntry entry/body composition remains open:
the older readback closure is incompatible with current compiler/binder APIs.
No decoder, runtime memory-reading encoder, caller catch phase or world relation
is introduced. Source state and Failure.Slice memory remain distinct machines. -/
namespace Solidity.Lowering.V08.LiteralFailureBytesReadback
open Solidity Source Backend

/-- Actual indexed ABI value, not an alternate codec. -/
def values (bs : List UInt8) : AbiEntry.Vals [.bytes] := .cons (.bytes bs) .nil

theorem source_encoding (bs : List UInt8) :
 Source.abiLayout [(true,bs)] = AbiEntry.encodeArgs (values bs) := by
 have padding : AbiEntry.roundUp bs.length-bs.length=(32-bs.length%32)%32 := by
  unfold AbiEntry.roundUp
  omega
 have byte_mod (n : Nat) : UInt8.ofNat (n%256)=UInt8.ofNat n := UInt8.ofNat_mod_size
 rw [SourceAbi.single_dynamic_bytes]
 simp only [values,AbiEntry.encodeArgs,AbiEntry.Vals.parts,AbiEntry.Shape.dynamic,
  AbiEntry.Val.enc,AbiEntry.assemble,List.foldl_cons,List.foldl_nil,ite_true,Nat.zero_add,
  AbiEntry.assemble.go,List.append_nil,List.append_assoc,padding,
  AbiEntry.wordBytes,Semantics.wordBytes,Semantics.pad32,Nat.toUInt8,byte_mod]

theorem source_error (bs : List UInt8) :
 Source.errorData bs = Source.errorSelector ++ AbiEntry.encodeArgs (values bs) := by
 rw [errorData_transport_total,← SourceAbi.error_payload_projection bs,source_encoding]
 rfl

/-- The already emitted exact packet is read from the real reached slice
memory. The returned ABI data and ordered bytes are observations only; this
proves no fetched native execution or unknown-memory encoder. -/
theorem lowered_packet {E : Env} {Γ : RCtx} (G : Glob E) (F : Fr) (n : Nat)
 (locals : Locals E.layout Γ) (state : St E) (bs : List UInt8)
 (address : Nat) (machine : Failure.Slice.Machine)
 (fits : Failure.Fits address (errorData bs)) (stack : machine.stack.length+2≤1024) :
 ∃ code,
  LiteralFailureLowering.emitLiteral address (LiteralFailureLowering.revertReason (E:=E) (Γ:=Γ) bs)=some code ∧
  (evalE G F (n+6) (LiteralFailureLowering.revertReason bs)).run (locals,state)=
   (.error (.revert (Source.errorSelector ++ AbiEntry.encodeArgs (values bs))),(locals,state)) ∧
  Failure.Slice.checkedRun code machine=
   some ({machine with memory:=Failure.Slice.putBytes machine.memory address (errorData bs)},
    some (revertOutcome (Source.errorSelector ++ AbiEntry.encodeArgs (values bs)))) ∧
  Failure.Slice.getBytes (Failure.Slice.putBytes machine.memory address (errorData bs)) address (errorData bs).length=
   Source.errorSelector ++ AbiEntry.encodeArgs (values bs) ∧
  Semantics.decodeError
   (Failure.Slice.getBytes (Failure.Slice.putBytes machine.memory address (errorData bs))
    address (errorData bs).length)=some bs := by
 obtain ⟨code,selected,source,emitted⟩ :=
  LiteralFailureLowering.reason_lowered G F n locals state bs address machine fits stack
 refine ⟨code,selected,?_,?_,?_,?_⟩
 · simpa only [source_error] using source
 · simpa only [source_error] using emitted
 · rw [Failure.Slice.getBytes_putBytes,source_error]
 · rw [Failure.Slice.getBytes_putBytes,errorData_transport_total]
   exact Backend.AbiWorld.error_roundtrip bs (LiteralFailureLowering.reason_bound address bs fits)

end Solidity.Lowering.V08.LiteralFailureBytesReadback

#print axioms Solidity.Lowering.V08.LiteralFailureBytesReadback.source_encoding
#print axioms Solidity.Lowering.V08.LiteralFailureBytesReadback.source_error
#print axioms Solidity.Lowering.V08.LiteralFailureBytesReadback.lowered_packet
#check Solidity.Lowering.V08.LiteralFailureBytesReadback.lowered_packet
