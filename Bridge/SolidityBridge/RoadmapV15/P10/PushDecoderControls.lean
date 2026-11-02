import SolidityBridge.RoadmapV15.P10.PushDecoderAgreement
namespace SolidityBridge.RoadmapV15.P10.PushDecoderControls
open Solidity Solidity.Backend EvmYul DecoderAgreement
private def preCode : Backend.Program := [.push ⟨1,by decide⟩ #v[0x1e],.op .POP]
private def suffix : Backend.Program := [.op .JUMPDEST,.op .STOP]
private def payload (n : Fin 33) : Vector UInt8 n.val :=
  Vector.ofFn (fun i => UInt8.ofNat (i.val+1))
private def code (n : Fin 33) : ByteArray :=
  ⟨(Backend.encode (preCode ++ .push n (payload n) :: suffix)).toArray⟩

theorem all_widths (n : Fin 33) :
    EVM.decode (code n) (.ofNat 3) =
      some (pushOp n,if n.val = 0 then none else
        some (uInt256OfByteArray ⟨(payload n).toArray⟩,n.val)) :=
  decode_push preCode suffix n (payload n) (by decide)

theorem ordered_two_bytes : (code ⟨2,by decide⟩).data.toList =
    [0x60,0x1e,0x50,0x61,0x01,0x02,0x5b,0x00] := rfl

theorem zero_width : EVM.decode (code ⟨0,by decide⟩) (.ofNat 3) =
    some (.PUSH0,none) := all_widths _

theorem nonzero_two_bytes : EVM.decode (code ⟨2,by decide⟩) (.ofNat 3) =
    some (.PUSH2,some (.ofNat 258,2)) := all_widths _

theorem wrong_endian : EVM.decode (code ⟨2,by decide⟩) (.ofNat 3) ≠
    some (.PUSH2,some (.ofNat 513,2)) := by decide +kernel

theorem reverse_distinct : EVM.decode ⟨#[0x61,0x02,0x01,0x5b]⟩ (.ofNat 0) =
    some (.PUSH2,some (.ofNat 513,2)) := by decide +kernel

theorem suffix_not_payload : EVM.decode ⟨#[0x61,0x01,0x02,0xff]⟩ (.ofNat 0) =
    some (.PUSH2,some (.ofNat 258,2)) := by decide +kernel

theorem maximum_width : EVM.decode
    ⟨(Backend.encode [.push ⟨32,by decide⟩ (Vector.replicate 32 0xff),.op .STOP]).toArray⟩
    (.ofNat 0) = some (.PUSH32,some (.ofNat (2^256-1),32)) := by decide +kernel

/-- The pin accepts a short raw immediate; intrinsic Backend data cannot be short. -/
theorem raw_truncated_reference : EVM.decode ⟨#[0x61,0x01]⟩ (.ofNat 0) =
    some (.PUSH2,some (.ofNat 1,2)) := by decide +kernel

theorem raw_truncated_backend : Backend.decode [0x61,0x01] = none := by
  rw [Backend.decode]
  rfl

theorem wrong_width : EVM.decode (code ⟨2,by decide⟩) (.ofNat 3) ≠
    some (.PUSH1,some (.ofNat 258,1)) := by decide +kernel

theorem wrong_payload_length : EVM.decode (code ⟨2,by decide⟩) (.ofNat 3) ≠
    some (.PUSH2,some (.ofNat 1,2)) := by decide +kernel

theorem all_payload_lengths (n : Fin 33) :
    (ByteArray.extract' (code n) 4 (4+n.val)).data.toList = (payload n).toList := by
  have extracted := exact_payload (Backend.encode preCode ++ [Backend.pushCode n])
    (payload n).toList (Backend.encode suffix)
  have length : (Backend.encode preCode ++ [Backend.pushCode n]).length = 4 := rfl
  have shape : ByteArray.extract' (code n) 4 (4+n.val) = ⟨(payload n).toArray⟩ := by
    simpa only [length,Vector.length_toList,code,Backend.encode_append,
      Backend.encode_cons,Instr.encode,List.cons_append,List.append_assoc,List.singleton_append]
      using extracted
  rw [shape]
  rfl

theorem payload_modulo (n : Fin 33) :
    (uInt256OfByteArray ⟨(payload n).toArray⟩).toNat =
      fromBytesBigEndian (payload n).toList % UInt256.size :=
  payload_word (payload n).toList

private def prepared (seed : EVM.State) (tail : List UInt256) : EVM.State :=
  {seed with
    pc := .ofNat 3
    gasAvailable := .ofNat 9
    execLength := 41
    stack := tail
    executionEnv := {seed.executionEnv with code := code ⟨2,by decide⟩}}

/-- Whole native state, with every seed field outside the listed updates retained.
Cost3 is supplied to step; no charged-driver adequacy is claimed here. -/
theorem arbitrary_seed_step (seed : EVM.State) (tail : List UInt256) :
    EVM.step 1 3 none (prepared seed tail) =
      .ok {(prepared seed tail) with
        pc := .ofNat 6
        gasAvailable := .ofNat 6
        execLength := 42
        stack := .ofNat 258 :: tail} := by
  have dispatched := fetched_push
    {seed with gasAvailable := .ofNat 9,execLength := 41,stack := tail}
    preCode suffix ⟨2,by decide⟩ (payload ⟨2,by decide⟩) (by decide) 0 3
  change EVM.step 1 3 none (prepared seed tail) =
    EVM.step 1 3 (some (.PUSH2,some (.ofNat 258,2))) (prepared seed tail) at dispatched
  rw [dispatched]
  change Except.ok (({prepared seed tail with
    execLength := 42,gasAvailable := UInt256.ofNat 9 - UInt256.ofNat 3}).replaceStackAndIncrPC
      (.ofNat 258 :: tail) (pcΔ := 3)) = _
  rw [show UInt256.ofNat 9 - UInt256.ofNat 3 = UInt256.ofNat 6 from by decide +kernel]
  change Except.ok ({prepared seed tail with
    execLength := 42,gasAvailable := UInt256.ofNat 6,
    stack := .ofNat 258 :: tail,pc := UInt256.ofNat 3 + UInt256.ofNat 3}) = _
  rw [show UInt256.ofNat 3 + UInt256.ofNat 3 = UInt256.ofNat 6 from by decide +kernel]

private def populated : EVM.State :=
  {(default : EVM.State) with
    memory := ⟨#[0xaa,0xbb]⟩,returnData := ⟨#[0xcc,0xdd]⟩,H_return := ⟨#[0xee,0xff]⟩
    executionEnv := {(default : EVM.State).executionEnv with
      codeOwner := .ofNat 7,source := .ofNat 11,perm := false
      calldata := ⟨#[0x11,0x22,0x33]⟩}}

theorem populated_step :
    EVM.step 1 3 none (prepared populated [.ofNat 513,.ofNat 1025]) =
      .ok {(prepared populated [.ofNat 513,.ofNat 1025]) with
        pc := .ofNat 6,gasAvailable := .ofNat 6,execLength := 42,
        stack := [.ofNat 258,.ofNat 513,.ofNat 1025]} := arbitrary_seed_step _ _

theorem fuel_zero : EVM.step 0 3 none (prepared populated [.ofNat 513,.ofNat 1025]) =
    .error .OutOfFuel := rfl


#print axioms all_widths
#print axioms ordered_two_bytes
#print axioms zero_width
#print axioms nonzero_two_bytes
#print axioms wrong_endian
#print axioms reverse_distinct
#print axioms suffix_not_payload
#print axioms maximum_width
#print axioms raw_truncated_reference
#print axioms raw_truncated_backend
#print axioms wrong_width
#print axioms wrong_payload_length
#print axioms all_payload_lengths
#print axioms payload_modulo
#print axioms arbitrary_seed_step
#print axioms populated_step
#print axioms fuel_zero
end SolidityBridge.RoadmapV15.P10.PushDecoderControls
