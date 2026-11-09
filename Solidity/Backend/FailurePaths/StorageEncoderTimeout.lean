import Solidity.Backend.FailurePaths.Premises
import Solidity.Source.Preservation.Encoding

/-! Actual storage reads preserve complete state through encoder/local ABI timeout; ordinary error parameters use memory, so this proves no admitted custom-error call. -/
namespace Solidity.Backend.FailurePaths.StorageEncoderTimeout
open Source
variable {E : Source.Env} {Γ : RCtx}

/-- Actual primitive reads discharge timeout in the same Env/state, without an encoder-outcome premise. -/
theorem incomplete (frame : Fr) (path : Source.SPath) (packed : Bool)
    (before : EMState E Γ) (byte : UInt8)
    (lengthRead : (readLen frame path : EM E Γ Nat).run before = (.ok 2,before))
    (firstRead : (readAt frame (path.go (.index 0)) (.fixedBytes 1 (by decide)) :
      EM E Γ _).run before = (.ok (.fixedBytes [byte] rfl),before)) :
    Premises.IncompleteAt
      (encodeVals frame 2 packed
        (.cons (.val (.storRef rfl path) : RVal E.layout (.bytes .storage)) .nil) :
        EM E Γ Roadmap.Bytes) before before :=
  Preservation.encode_storage_bytes_timeout_two frame path packed before byte lengthRead firstRead

/-- Local ABI evaluation times out before allocation/revert, preserving complete caller state. -/
theorem local_abi_timeout (global : Glob E) (frame : Fr)
    (i : Source.Idx Γ (.bytes .storage)) (locals : Locals E.layout Γ)
    (initial : St E) (path : Source.SPath) (byte : UInt8)
    (value : locals.get i = .storRef rfl path)
    (lengthRead : (readLen frame path : EM E Γ Nat).run (locals,initial) =
      (.ok 2,(locals,initial)))
    (firstRead : (readAt frame (path.go (.index 0)) (.fixedBytes 1 (by decide)) :
      EM E Γ _).run (locals,initial) = (.ok (.fixedBytes [byte] rfl),(locals,initial))) :
    (evalE global frame 3
      (.abiEncode .encode (.cons (.local i) .nil))).run (locals,initial) =
      (.error .timeout,(locals,initial)) := by
  have args : (evalArgs global frame 2
      (.cons (.local i) .nil : RArgs E Γ [.bytes .storage])).run (locals,initial) =
      (.ok (.cons (.val (.storRef rfl path)) .nil),(locals,initial)) := by
    simp only [evalArgs,evalE]
    change ((Except.ok (.cons (.val (locals.get i)) .nil) :
      Except Source.Halt (RVals E.layout [.bytes .storage])),(locals,initial)) = _
    rw [value]
  have encoded := incomplete frame path false (locals,initial) byte lengthRead firstRead
  change ((do
    let vs ← evalArgs global frame 2 (.cons (.local i) .nil)
    let data ← encodeVals frame 2 false vs
    return .val (← allocRef (Data.bytes (l := .memory) data))) :
      EM E Γ (RVal E.layout (.bytes .memory))).run (locals,initial) = _
  rw [Hoare.run_bind,args]
  change ((do
    let data ← encodeVals frame 2 false
      (.cons (.val (.storRef rfl path)) .nil)
    return .val (← allocRef (Data.bytes (l := .memory) data))) :
      EM E Γ (RVal E.layout (.bytes .memory))).run (locals,initial) = _
  rw [Hoare.run_bind,encoded]
/-- info: 'Solidity.Backend.FailurePaths.StorageEncoderTimeout.incomplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms incomplete
/-- info: 'Solidity.Backend.FailurePaths.StorageEncoderTimeout.local_abi_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_abi_timeout
end Solidity.Backend.FailurePaths.StorageEncoderTimeout
