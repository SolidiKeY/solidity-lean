import SolidityBridge.RoadmapV15.P10.DecoderAgreement
import SolidityBridge.ExternalEvm.MemoryBytes

namespace SolidityBridge.RoadmapV15.P10.DecoderAgreement
open Solidity Solidity.Backend EvmYul

/-- Existing reference PUSH family, indexed by actual Backend immediate width. -/
def pushOp : Fin 33 → Operation .EVM :=
  ![.PUSH0,.PUSH1,.PUSH2,.PUSH3,.PUSH4,.PUSH5,.PUSH6,.PUSH7,.PUSH8,.PUSH9,.PUSH10,.PUSH11,.PUSH12,.PUSH13,.PUSH14,.PUSH15,.PUSH16,.PUSH17,.PUSH18,.PUSH19,.PUSH20,.PUSH21,.PUSH22,.PUSH23,.PUSH24,.PUSH25,.PUSH26,.PUSH27,.PUSH28,.PUSH29,.PUSH30,.PUSH31,.PUSH32]

theorem push_parser (n : Fin 33) : EVM.parseInstr (Backend.pushCode n) = some (pushOp n) := by
  fin_cases n <;> rfl

theorem push_width (n : Fin 33) : EVM.argOnNBytesOfInstr (pushOp n) = n.val := by
  fin_cases n <;> rfl

/-- Pure extraction from both actual extract' branches, no allocator premise. -/
theorem exact_payload (pre payload post : List UInt8) :
    ByteArray.extract' ⟨(pre ++ payload ++ post).toArray⟩ pre.length
      (pre.length+payload.length) = ⟨payload.toArray⟩ := by
  have slice : ((pre ++ payload ++ post).drop pre.length).take payload.length = payload := by
    rw [List.append_assoc,List.drop_left,List.take_left]
  unfold ByteArray.extract'
  split
  · apply ByteArray.ext
    simp only [ByteArray.data_extract,List.extract_toArray,List.extract_eq_drop_take,
      Nat.add_sub_cancel_left]
    rw [slice]
  · simp only [Solidity.Evm.External.Memory.bytes_list,
      Nat.add_sub_cancel_left]
    rw [slice]

/-- Valid intrinsic length excludes reference truncation; arbitrary prefix/suffix. -/
theorem decode_push (before after : Backend.Program) (n : Fin 33)
    (payload : Vector UInt8 n.val)
    (pcFits : (Backend.encode before).length < UInt256.size) :
    EVM.decode ⟨(Backend.encode (before ++ .push n payload :: after)).toArray⟩
      (.ofNat (Backend.encode before).length) =
    some (pushOp n,if n.val = 0 then none else
      some (EvmYul.uInt256OfByteArray ⟨payload.toArray⟩,n.val)) := by
  have pc : (UInt256.ofNat (Backend.encode before).length).toNat =
      (Backend.encode before).length := Nat.mod_eq_of_lt pcFits
  have byte : (⟨(Backend.encode (before ++ .push n payload :: after)).toArray⟩ : ByteArray).get?
      (Backend.encode before).length = some (Backend.pushCode n) := by
    change (Backend.encode (before ++ .push n payload :: after)).toArray[(Backend.encode before).length]? = _
    rw [List.getElem?_toArray]
    simp only [Backend.encode_append,Backend.encode_cons,Instr.encode,List.cons_append]
    rw [List.getElem?_append_right (Nat.le_refl _)]
    simp only [Nat.sub_self,List.getElem?_cons_zero]
  have extracted : ByteArray.extract'
      ⟨(Backend.encode (before ++ .push n payload :: after)).toArray⟩
      ((Backend.encode before).length+1) ((Backend.encode before).length+1+n.val) =
      ⟨payload.toArray⟩ := by
    have h := exact_payload (Backend.encode before ++ [Backend.pushCode n])
      payload.toList (Backend.encode after)
    simpa only [Backend.encode_append,Backend.encode_cons,Instr.encode,List.cons_append,
      List.length_append,List.length_singleton,Vector.length_toList,List.append_assoc,
      List.singleton_append] using h
  simp only [EVM.decode,pc,byte,bind,Option.bind,push_parser,push_width]
  rw [show (Backend.encode before).length.succ = (Backend.encode before).length+1 from rfl,extracted]
  by_cases zero : n.val = 0
  · simp only [zero,beq_self_eq_true,ite_true]
  · simp only [zero,beq_iff_eq,ite_false]

/-- The actual reader's byte order and modulo, not an assumed PUSH value. -/
theorem payload_word (payload : List UInt8) :
    (EvmYul.uInt256OfByteArray ⟨payload.toArray⟩).toNat =
      EvmYul.fromBytesBigEndian payload % UInt256.size := by
  change EvmYul.fromBytes' payload.toArray.toList.reverse % UInt256.size = _
  rw [List.toList_toArray]
  rfl

/-- Actual fetched PUSH dispatch preserves arbitrary seed state and native fuel. -/
theorem fetched_push (seed : EVM.State) (before after : Backend.Program)
    (n : Fin 33) (payload : Vector UInt8 n.val)
    (pcFits : (Backend.encode before).length < UInt256.size) (fuel cost : Nat) :
    let input : EVM.State := {seed with
      pc := .ofNat (Backend.encode before).length
      executionEnv := {seed.executionEnv with
        code := ⟨(Backend.encode (before ++ .push n payload :: after)).toArray⟩}}
    EVM.step (fuel+1) cost none input =
      EVM.step (fuel+1) cost (some (pushOp n,if n.val = 0 then none else
        some (EvmYul.uInt256OfByteArray ⟨payload.toArray⟩,n.val))) input := by
  dsimp only
  have decoded := decode_push before after n payload pcFits
  simp only [EVM.step,EVM.fetchInstr,decoded,Option.option,bind,Except.bind]
  rfl

#print axioms push_parser
#print axioms push_width
#print axioms exact_payload
#print axioms decode_push
#print axioms payload_word
#print axioms fetched_push
end SolidityBridge.RoadmapV15.P10.DecoderAgreement
