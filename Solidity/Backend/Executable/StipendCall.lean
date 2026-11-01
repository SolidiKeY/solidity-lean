import Solidity.Backend.Executable.ValueCall
import Solidity.Stipend.Rule

/-! Ordinary-payment requested-gas selection using actual runtime words.
This proves the emitted requested operand, not a universal EVM forwarded-gas
rule or callee Fitted/Enforced. Existing typed frame producer remains open. -/
namespace Solidity.Backend.Executable.StipendCall
open Semantics ContractWorld

def zero : PrimTy.uint.Denote := ⟨0,by decide⟩
def stipend : PrimTy.uint.Denote := ⟨(Roadmap.Evm.pinned.stipend : Int),by decide +kernel⟩

/-- Compiler-internal request: nonzero value relies on CALL's value stipend;
zero value must request the stipend. No source gas observation is introduced. -/
def requested (amount : PrimTy.uint.Denote) : PrimTy.uint.Denote :=
  if amount.1 = 0 then stipend else zero

private theorem zero_encoding : Scalar.encodeValue .uint zero = 0 := rfl

theorem zero_test (amount : PrimTy.uint.Denote) :
    (Scalar.encodeValue .uint amount == 0) = decide (amount.1 = 0) := by
  have eq := Scalar.encode_uint_beq amount zero
  simpa only [zero_encoding, zero] using eq

theorem scaled_flag (amount : PrimTy.uint.Denote) :
    Scalar.encodeValue .uint stipend * Scalar.flag (Scalar.encodeValue .uint amount == 0) =
      Scalar.encodeValue .uint (requested amount) := by
  rw [zero_test]
  by_cases h : amount.1 = 0
  · simp only [requested, h, ↓reduceIte, decide_true]
    change Scalar.encodeValue .uint stipend * (1 : Scalar.Word) = _
    exact BitVec.mul_one _
  · simp only [requested, h, ↓reduceIte, decide_false]
    change Scalar.encodeValue .uint stipend * (0 : Scalar.Word) = 0
    exact BitVec.mul_zero

/-- On recipient::amount::tail, preserve both inputs and put the computed gas
on top. The amount is copied from the actual stack, never specialized in code. -/
def gasCode : Program :=
  [.op (.DUP ⟨1,by decide⟩), .op .ISZERO] ++ Scalar.literal .uint stipend ++ [.op .MUL]

theorem gas_correct (recipient : Scalar.Word) (amount : PrimTy.uint.Denote) (tail : Scalar.Stack) :
    Scalar.run gasCode (recipient :: Scalar.encodeValue .uint amount :: tail) =
      some (Scalar.encodeValue .uint (requested amount) :: recipient :: Scalar.encodeValue .uint amount :: tail) := by
  have tested : Scalar.run [.op (.DUP ⟨1,by decide⟩),.op .ISZERO]
      (recipient :: Scalar.encodeValue .uint amount :: tail) =
      some (Scalar.flag (Scalar.encodeValue .uint amount == 0) :: recipient :: Scalar.encodeValue .uint amount :: tail) := rfl
  have pushed := Scalar.literal_correct .uint stipend
    (Scalar.flag (Scalar.encodeValue .uint amount == 0) :: recipient :: Scalar.encodeValue .uint amount :: tail)
  have multiplied : Scalar.run [.op .MUL]
      (Scalar.encodeValue .uint stipend :: Scalar.flag (Scalar.encodeValue .uint amount == 0) ::
        recipient :: Scalar.encodeValue .uint amount :: tail) =
      some (Scalar.encodeValue .uint (requested amount) :: recipient :: Scalar.encodeValue .uint amount :: tail) := by
    change some ((Scalar.encodeValue .uint stipend * Scalar.flag (Scalar.encodeValue .uint amount == 0)) :: _) = _
    rw [scaled_flag]
  exact Scalar.run_comp (Scalar.run_comp tested pushed) multiplied

/-- Dynamic uint amount from the existing two-local constructed frame. -/
def operands (recipient : Address) : Program :=
  ValueCall.emptyBuffers ++ ValueCall.localAmount ++ Scalar.literal .uint recipient.1 ++ gasCode

def code (recipient : Address) : Program := operands recipient ++ [.op .CALL]

theorem operands_correct {C : Contract} (σ : State C [.val .int,.val .uint])
    (spill : Scalar.Stack) (recipient : Address) :
    Scalar.run (operands recipient) (ScalarSequence.frameTail σ spill) = some
      ([Scalar.encodeValue .uint (requested (TEnv.get (.there .here) σ.env)),
        Scalar.encodeValue .uint recipient.1,Scalar.encodeValue .uint (TEnv.get (.there .here) σ.env),0,0,0,0] ++
        ScalarSequence.frameTail σ spill) :=
  Scalar.run_comp (ValueCall.local_recipient_stage σ spill recipient)
    (gas_correct (Scalar.encodeValue .uint recipient.1) (TEnv.get (.there .here) σ.env) _)

/-- The extra test/PUSH peak is eight cells, even though final input has seven.
This is derived from actual DUP2/ISZERO/PUSH32/MUL instruction selection. -/
theorem heights (recipient : Address) (h : Int) :
    Scalar.heightTrace (operands recipient) h =
      [h,h+1,h+2,h+3,h+4,h+5,h+6,h+7,h+7,h+8,h+7] := by
  simp only [operands, ValueCall.emptyBuffers, ValueCall.localAmount, gasCode, Scalar.literal,
    Scalar.pushByte, Scalar.pushWord, List.cons_append, List.nil_append, Scalar.heightTrace,
    Scalar.stackDelta, Scalar.numericDelta, Scalar.unary, Scalar.binary,
    Option.isSome_some, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  simp only [Int.add_assoc, Int.reduceAdd]

theorem capacity_iff (recipient : Address) (h : Int) :
    Scalar.stackBound (operands recipient) h = true ↔ 0 ≤ h ∧ h+8 ≤ 1024 := by
  simp only [Scalar.stackBound, heights, List.all_cons, List.all_nil, Scalar.safeHeight,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨lo,_⟩,_,_,_,_,_,_,_,_,⟨_,hi⟩,_,_⟩
    exact ⟨lo,by omega⟩
  · rintro ⟨lo,hi⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,True.intro⟩ <;> constructor <;> omega

theorem local_capacity {C : Contract} (σ : State C [.val .int,.val .uint])
    (spill : Scalar.Stack) (recipient : Address) :
    Scalar.stackBound (operands recipient) ((ScalarSequence.frameTail σ spill).length : Int) = true ↔
      spill.length ≤ 1014 := by
  rw [capacity_iff, ScalarSequence.frame_length]
  constructor
  · intro h; omega
  · intro h; constructor <;> omega

theorem prefix_safe {C : Contract} (σ : State C [.val .int,.val .uint])
    (spill : Scalar.Stack) (recipient : Address) (room : spill.length ≤ 1014)
    (first rest : Program) (split : first ++ rest = operands recipient)
    {out : Scalar.Stack} (ran : Scalar.run first (ScalarSequence.frameTail σ spill) = some out) : out.length ≤ 1024 := by
  apply Scalar.prefix_capacity first rest ran
  rw [split]
  exact (local_capacity σ spill recipient).mpr room

private theorem encode_operands (recipient : Address) (gas : PrimTy.uint.Denote) :
    Backend.encode (ValueCall.emptyBuffers ++ ValueCall.localAmount ++ Scalar.literal .uint recipient.1 ++
      ([.op (.DUP ⟨1,by decide⟩), .op .ISZERO] ++ Scalar.literal .uint gas ++ [.op .MUL]) ++ [.op .CALL]) =
    [0x60,0,0x80,0x80,0x80,0x85] ++ (0x7f :: ValueCall.uintPayload recipient.1) ++
      [0x81,0x15] ++ (0x7f :: ValueCall.uintPayload gas) ++ [0x02,0xf1] := by
  have encoded (v : PrimTy.uint.Denote) : Backend.encode (Scalar.literal .uint v) =
      0x7f :: ValueCall.uintPayload v := by
    simp only [Scalar.literal, Backend.encode_cons, Backend.encode_nil, List.append_nil,
      Scalar.encode_pushWord, Scalar.encode_uint_toNat, ValueCall.uintPayload]
  have buffers : Backend.encode ValueCall.emptyBuffers = [0x60,0,0x80,0x80,0x80] := rfl
  have copied : Backend.encode ValueCall.localAmount = [0x85] := rfl
  have test : Backend.encode [.op (.DUP ⟨1,by decide⟩), .op .ISZERO] = [0x81,0x15] := rfl
  have mul : Backend.encode [.op .MUL] = [0x02] := rfl
  have call : Backend.encode [.op .CALL] = [0xf1] := rfl
  simp only [Backend.encode_append, encoded, buffers, copied, test, mul, call]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem complete_bytes (recipient : Address) : Backend.encode (code recipient) =
    [0x60,0,0x80,0x80,0x80,0x85] ++ (0x7f :: ValueCall.uintPayload recipient.1) ++
      [0x81,0x15] ++ (0x7f :: ValueCall.uintPayload stipend) ++ [0x02,0xf1] :=
  encode_operands recipient stipend

theorem byte_length (recipient : Address) : (Backend.encode (code recipient)).length = 76 := by
  rw [Backend.length_encode]
  rfl

theorem decode_bytes (recipient : Address) : Backend.decode (Backend.encode (code recipient)) = some (code recipient) :=
  Backend.decode_encode _

theorem numeric_boundary {C : Contract} (σ : State C [.val .int,.val .uint])
    (spill : Scalar.Stack) (recipient : Address) : Scalar.run (code recipient) (ScalarSequence.frameTail σ spill) = none := by
  rw [code, Scalar.run_append, operands_correct]
  rfl

/-- info: 'Solidity.Backend.Executable.StipendCall.zero_test' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_test

/-- info: 'Solidity.Backend.Executable.StipendCall.scaled_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scaled_flag

/-- info: 'Solidity.Backend.Executable.StipendCall.gas_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gas_correct

/-- info: 'Solidity.Backend.Executable.StipendCall.operands_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms operands_correct

/-- info: 'Solidity.Backend.Executable.StipendCall.heights' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms heights

/-- info: 'Solidity.Backend.Executable.StipendCall.capacity_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capacity_iff

/-- info: 'Solidity.Backend.Executable.StipendCall.local_capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_capacity

/-- info: 'Solidity.Backend.Executable.StipendCall.prefix_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prefix_safe

/-- info: 'Solidity.Backend.Executable.StipendCall.complete_bytes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms complete_bytes

/-- info: 'Solidity.Backend.Executable.StipendCall.byte_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms byte_length

/-- info: 'Solidity.Backend.Executable.StipendCall.decode_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decode_bytes

/-- info: 'Solidity.Backend.Executable.StipendCall.numeric_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms numeric_boundary

end Solidity.Backend.Executable.StipendCall
