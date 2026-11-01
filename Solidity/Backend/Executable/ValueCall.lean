import Solidity.Backend.Executable.LocalFrame
import Solidity.Semantics.ContractWorld

/-! Actual empty-data value CALL bytes with literal or typed-local amounts.
Operand prefixes execute in the published numeric slice; CALL is outside it.
Gas is an explicit typed input, not a proved stipend policy. This does not
specialize local/environment reads by evaluating a source state. The two-cell
frameTail is a constructed representation; its general runtime producer remains open. -/
namespace Solidity.Backend.Executable.ValueCall
open Semantics ContractWorld

/-- One selected PUSH1 followed by actual DUP1 instructions makes the four
empty input/output buffer operands without duplicating a protected caller word. -/
def emptyBuffers : Program :=
  [Scalar.pushByte 0, .op (.DUP ⟨0,by decide⟩), .op (.DUP ⟨0,by decide⟩), .op (.DUP ⟨0,by decide⟩)]

/-- Typed literal arguments, in reverse push order for top-first CALL input.
The caller must separately justify its gas operand and runtime argument lowering. -/
def operandCode (gas : PrimTy.uint.Denote) (recipient : Address) (amount : PrimTy.uint.Denote) : Program :=
  emptyBuffers ++ Scalar.literal .uint amount ++ Scalar.literal .uint recipient.1 ++ Scalar.literal .uint gas

def code (gas : PrimTy.uint.Denote) (recipient : Address) (amount : PrimTy.uint.Denote) : Program :=
  operandCode gas recipient amount ++ [.op .CALL]

def bytes (gas : PrimTy.uint.Denote) (recipient : Address) (amount : PrimTy.uint.Denote) : List UInt8 :=
  Backend.encode (code gas recipient amount)

theorem empty_buffers (tail : Scalar.Stack) :
    Scalar.run emptyBuffers tail = some ([0,0,0,0] ++ tail) := by
  simp only [emptyBuffers, Scalar.run, Scalar.step_pushByte, Option.bind_some]
  rfl

theorem amount_stage (amount : PrimTy.uint.Denote) (tail : Scalar.Stack) :
    Scalar.run (emptyBuffers ++ Scalar.literal .uint amount) tail =
      some (Scalar.encodeValue .uint amount :: [0,0,0,0] ++ tail) :=
  Scalar.run_comp (empty_buffers tail) (Scalar.literal_correct .uint amount _)

theorem recipient_stage (recipient : Address) (amount : PrimTy.uint.Denote) (tail : Scalar.Stack) :
    Scalar.run (emptyBuffers ++ Scalar.literal .uint amount ++ Scalar.literal .uint recipient.1) tail =
      some (Scalar.encodeValue .uint recipient.1 :: Scalar.encodeValue .uint amount :: [0,0,0,0] ++ tail) :=
  Scalar.run_comp (amount_stage amount tail) (Scalar.literal_correct .uint recipient.1 _)

/-- Exact staged stack frame, with all caller words retained in order. -/
theorem prefix_correct (gas : PrimTy.uint.Denote) (recipient : Address)
    (amount : PrimTy.uint.Denote) (tail : Scalar.Stack) :
    Scalar.run (operandCode gas recipient amount) tail = some
      ([Scalar.encodeValue .uint gas, Scalar.encodeValue .uint recipient.1,
        Scalar.encodeValue .uint amount,0,0,0,0] ++ tail) :=
  Scalar.run_comp (recipient_stage recipient amount tail) (Scalar.literal_correct .uint gas _)

/-- Actual capacity at every prefix boundary, including the three DUP peaks.
No assumed capacity certificate or desired simulation is an input. -/
theorem capacity_iff (gas : PrimTy.uint.Denote) (recipient : Address)
    (amount : PrimTy.uint.Denote) (h : Int) :
    Scalar.stackBound (operandCode gas recipient amount) h = true ↔ 0 ≤ h ∧ h + 7 ≤ 1024 := by
  simp only [operandCode, emptyBuffers, Scalar.literal, Scalar.pushByte, Scalar.pushWord,
    List.cons_append, List.nil_append, Scalar.stackBound, Scalar.heightTrace, Scalar.stackDelta,
    List.all_cons, List.all_nil, Scalar.safeHeight, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨lo,_⟩,_,_,_,_,_,_,⟨_,hi⟩,_⟩
    exact ⟨lo,by omega⟩
  · rintro ⟨lo,hi⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,True.intro⟩ <;> constructor <;> omega

theorem prefix_safe (gas : PrimTy.uint.Denote) (recipient : Address)
    (amount : PrimTy.uint.Denote) (tail : Scalar.Stack) (room : tail.length ≤ 1017)
    (before after : Program) (split : before ++ after = operandCode gas recipient amount)
    {out : Scalar.Stack} (ran : Scalar.run before tail = some out) : out.length ≤ 1024 := by
  apply Scalar.prefix_capacity before after ran
  rw [split, capacity_iff]
  constructor <;> omega

/-- The existing literal selector supplies uniform source arguments. These
are actual intrinsic literals, not arbitrary source expressions or frame loads. -/
theorem source_arguments {C : Contract} {Γ : Ctx} (σ : State C Γ)
    (recipient : Address) (amount : PrimTy.uint.Denote) :
    ((.simple (.lit recipient.1.1 recipient.1.2) : Val C Γ .uint).evalT σ = .ok recipient.1) ∧
    ((.simple (.lit amount.1 amount.2) : Val C Γ .uint).evalT σ = .ok amount) :=
  ⟨(Scalar.numericLiteral .uint recipient.1.1 recipient.1.2).source σ,
    (Scalar.numericLiteral .uint amount.1 amount.2).source σ⟩

theorem recipient_word (recipient : Address) :
    (Scalar.encodeValue .uint recipient.1).toNat = recipient.1.1.toNat := Scalar.encode_uint_toNat recipient.1

theorem prefix_byte_length (gas : PrimTy.uint.Denote) (recipient : Address)
    (amount : PrimTy.uint.Denote) : (Backend.encode (operandCode gas recipient amount)).length = 104 := by
  rw [Backend.length_encode]
  rfl

theorem byte_observation (gas : PrimTy.uint.Denote) (recipient : Address)
    (amount : PrimTy.uint.Denote) :
    bytes gas recipient amount = Backend.encode (operandCode gas recipient amount) ++ [0xf1] := by
  rw [bytes, code, Backend.encode_append]
  rfl

theorem byte_length (gas : PrimTy.uint.Denote) (recipient : Address)
    (amount : PrimTy.uint.Denote) : (bytes gas recipient amount).length = 105 := by
  rw [byte_observation, List.length_append, prefix_byte_length]
  rfl

/-- This consumes the published encoder roundtrip, not pinned decoder agreement. -/
theorem decode_bytes (gas : PrimTy.uint.Denote) (recipient : Address)
    (amount : PrimTy.uint.Denote) : Backend.decode (bytes gas recipient amount) = some (code gas recipient amount) :=
  Backend.decode_encode _

/-- Unsupported numeric-slice CALL is not an EVM revert or failed send. -/
theorem numeric_boundary (gas : PrimTy.uint.Denote) (recipient : Address)
    (amount : PrimTy.uint.Denote) (tail : Scalar.Stack) :
    Scalar.run (code gas recipient amount) tail = none := by
  rw [code, Scalar.run_append, prefix_correct]
  rfl

/-- Four new buffer words shift the actual uint local at index1 to index5.
This is DUP6, not an evaluated source value embedded as an immediate. -/
def localAmount : Program := [.op (.DUP ⟨5,by decide⟩)]
def localOperands (gas : PrimTy.uint.Denote) (recipient : Address) : Program :=
  emptyBuffers ++ localAmount ++ Scalar.literal .uint recipient.1 ++ Scalar.literal .uint gas
def localCode (gas : PrimTy.uint.Denote) (recipient : Address) : Program :=
  localOperands gas recipient ++ [.op .CALL]

/-- Source amount lookup is the already-published actual typed local read. -/
theorem local_source {C : Contract} (σ : State C [.val .int,.val .uint]) :
    (LocalFrame.uintRead (C := C)).evalT σ = .ok (TEnv.get (.there .here) σ.env) :=
  LocalFrame.uint_source σ

theorem local_amount_stage {C : Contract} (σ : State C [.val .int,.val .uint]) (spill : Scalar.Stack) :
    Scalar.run (emptyBuffers ++ localAmount) (ScalarSequence.frameTail σ spill) =
      some (Scalar.encodeValue .uint (TEnv.get (.there .here) σ.env) ::
        [0,0,0,0] ++ ScalarSequence.frameTail σ spill) :=
  Scalar.run_comp (empty_buffers _) rfl

theorem local_recipient_stage {C : Contract} (σ : State C [.val .int,.val .uint])
    (spill : Scalar.Stack) (recipient : Address) :
    Scalar.run (emptyBuffers ++ localAmount ++ Scalar.literal .uint recipient.1)
      (ScalarSequence.frameTail σ spill) = some
      (Scalar.encodeValue .uint recipient.1 :: Scalar.encodeValue .uint (TEnv.get (.there .here) σ.env) ::
        [0,0,0,0] ++ ScalarSequence.frameTail σ spill) :=
  Scalar.run_comp (local_amount_stage σ spill) (Scalar.literal_correct .uint recipient.1 _)

/-- Real DUP6/selected PUSH instructions preserve both actual typed caller cells
and every protected spill word, uniformly in the caller state. -/
theorem local_correct {C : Contract} (σ : State C [.val .int,.val .uint])
    (spill : Scalar.Stack) (gas : PrimTy.uint.Denote) (recipient : Address) :
    Scalar.run (localOperands gas recipient) (ScalarSequence.frameTail σ spill) = some
      ([Scalar.encodeValue .uint gas, Scalar.encodeValue .uint recipient.1,
        Scalar.encodeValue .uint (TEnv.get (.there .here) σ.env),0,0,0,0] ++ ScalarSequence.frameTail σ spill) :=
  Scalar.run_comp (local_recipient_stage σ spill recipient) (Scalar.literal_correct .uint gas _)

/-- Same +7 peak as the concrete literal emitter, derived from actual opcode
choices; successful local_correct additionally witnesses DUP6's operand. -/
theorem local_heights (gas : PrimTy.uint.Denote) (recipient : Address) (h : Int) :
    Scalar.heightTrace (localOperands gas recipient) h =
      Scalar.heightTrace (operandCode gas recipient ⟨0,by decide⟩) h := rfl

theorem local_capacity {C : Contract} (σ : State C [.val .int,.val .uint])
    (spill : Scalar.Stack) (gas : PrimTy.uint.Denote) (recipient : Address) :
    Scalar.stackBound (localOperands gas recipient) ((ScalarSequence.frameTail σ spill).length : Int) = true ↔
      spill.length ≤ 1015 := by
  unfold Scalar.stackBound
  rw [local_heights]
  change Scalar.stackBound (operandCode gas recipient ⟨0,by decide⟩)
    ((ScalarSequence.frameTail σ spill).length : Int) = true ↔ _
  rw [capacity_iff, ScalarSequence.frame_length]
  constructor
  · intro h; omega
  · intro h; constructor <;> omega

theorem local_prefix_safe {C : Contract} (σ : State C [.val .int,.val .uint])
    (spill : Scalar.Stack) (gas : PrimTy.uint.Denote) (recipient : Address) (room : spill.length ≤ 1015)
    (first rest : Program) (split : first ++ rest = localOperands gas recipient)
    {out : Scalar.Stack} (ran : Scalar.run first (ScalarSequence.frameTail σ spill) = some out) :
    out.length ≤ 1024 := by
  apply Scalar.prefix_capacity first rest ran
  rw [split]
  exact (local_capacity σ spill gas recipient).mpr room

theorem local_byte_observation (gas : PrimTy.uint.Denote) (recipient : Address) :
    Backend.encode (localCode gas recipient) = Backend.encode (localOperands gas recipient) ++ [0xf1] := by
  rw [localCode, Backend.encode_append]
  rfl

theorem local_byte_length (gas : PrimTy.uint.Denote) (recipient : Address) :
    (Backend.encode (localCode gas recipient)).length = 73 := by
  rw [Backend.length_encode]
  rfl

theorem local_decode (gas : PrimTy.uint.Denote) (recipient : Address) :
    Backend.decode (Backend.encode (localCode gas recipient)) = some (localCode gas recipient) := Backend.decode_encode _

/-- The actual CALL opcode is deliberately not interpreted by this numeric
relation; none here must not be promoted into a payment failure observation. -/
theorem local_numeric_boundary {C : Contract} (σ : State C [.val .int,.val .uint])
    (spill : Scalar.Stack) (gas : PrimTy.uint.Denote) (recipient : Address) :
    Scalar.run (localCode gas recipient) (ScalarSequence.frameTail σ spill) = none := by
  rw [localCode, Scalar.run_append, local_correct]
  rfl

/-- Reuse the actual encoder's32-byte source-word payload; no new ABI codec. -/
def uintPayload (v : PrimTy.uint.Denote) : List UInt8 := (Backend.toBytesBE 32 v.1.toNat).toList

/-- Complete emitted PUSH payload order, including buffer DUPs and real CALL. -/
theorem complete_bytes (gas : PrimTy.uint.Denote) (recipient : Address) (amount : PrimTy.uint.Denote) :
    bytes gas recipient amount = [0x60,0,0x80,0x80,0x80] ++
      (0x7f :: uintPayload amount) ++ (0x7f :: uintPayload recipient.1) ++
      (0x7f :: uintPayload gas) ++ [0xf1] := by
  simp only [bytes, code, operandCode, Backend.encode_append, Scalar.literal,
    Backend.encode_cons, Backend.encode_nil, List.append_nil, Scalar.encode_pushWord,
    Scalar.encode_uint_toNat, uintPayload]
  rfl

/-- Runtime local copying has its own actual DUP6 byte, not a literal amount
specialized from a caller. Recipient then gas are the only PUSH32 payloads. -/
theorem complete_local_bytes (gas : PrimTy.uint.Denote) (recipient : Address) :
    Backend.encode (localCode gas recipient) = [0x60,0,0x80,0x80,0x80,0x85] ++
      (0x7f :: uintPayload recipient.1) ++ (0x7f :: uintPayload gas) ++ [0xf1] := by
  simp only [localCode, localOperands, Backend.encode_append, Scalar.literal,
    Backend.encode_cons, Backend.encode_nil, List.append_nil, Scalar.encode_pushWord,
    Scalar.encode_uint_toNat, uintPayload]
  rfl

/-- info: 'Solidity.Backend.Executable.ValueCall.empty_buffers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_buffers
/-- info: 'Solidity.Backend.Executable.ValueCall.amount_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms amount_stage
/-- info: 'Solidity.Backend.Executable.ValueCall.recipient_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recipient_stage
/-- info: 'Solidity.Backend.Executable.ValueCall.prefix_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_correct
/-- info: 'Solidity.Backend.Executable.ValueCall.capacity_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capacity_iff
/-- info: 'Solidity.Backend.Executable.ValueCall.prefix_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_safe
/-- info: 'Solidity.Backend.Executable.ValueCall.source_arguments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_arguments
/-- info: 'Solidity.Backend.Executable.ValueCall.recipient_word' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms recipient_word
/-- info: 'Solidity.Backend.Executable.ValueCall.prefix_byte_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_byte_length
/-- info: 'Solidity.Backend.Executable.ValueCall.byte_observation' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms byte_observation
/-- info: 'Solidity.Backend.Executable.ValueCall.byte_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms byte_length
/-- info: 'Solidity.Backend.Executable.ValueCall.decode_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decode_bytes
/-- info: 'Solidity.Backend.Executable.ValueCall.numeric_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms numeric_boundary
/-- info: 'Solidity.Backend.Executable.ValueCall.local_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_source
/-- info: 'Solidity.Backend.Executable.ValueCall.local_amount_stage' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_amount_stage
/-- info: 'Solidity.Backend.Executable.ValueCall.local_recipient_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_recipient_stage
/-- info: 'Solidity.Backend.Executable.ValueCall.local_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_correct
/-- info: 'Solidity.Backend.Executable.ValueCall.local_heights' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_heights
/-- info: 'Solidity.Backend.Executable.ValueCall.local_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_capacity
/-- info: 'Solidity.Backend.Executable.ValueCall.local_prefix_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_prefix_safe
/-- info: 'Solidity.Backend.Executable.ValueCall.local_byte_observation' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms local_byte_observation
/-- info: 'Solidity.Backend.Executable.ValueCall.local_byte_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms local_byte_length
/-- info: 'Solidity.Backend.Executable.ValueCall.local_decode' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_decode
/-- info: 'Solidity.Backend.Executable.ValueCall.local_numeric_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_numeric_boundary
/-- info: 'Solidity.Backend.Executable.ValueCall.complete_bytes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms complete_bytes
/-- info: 'Solidity.Backend.Executable.ValueCall.complete_local_bytes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms complete_local_bytes
end Solidity.Backend.Executable.ValueCall
