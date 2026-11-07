import Solidity.Backend.Opcode

/-! Joint input domains for every authored Opcode theorem, and a total encoder
stage contract with observable byte-level failures. This is fixed Osaka syntax;
it does not claim an execution gas model or historical-fork admission. -/
namespace Solidity.H62.EvmCompilerAudit.Opcode
open Backend

def width : Fin 33 := ⟨1, by decide⟩
def push : Instr := .push width #v[0x2a]
def packet : Program := [push, .op .STOP]

theorem width_domain : ∃ _n : Fin 33, True := ⟨width, True.intro⟩
theorem byte_domain : ∃ _b : UInt8, True := ⟨0x60, True.intro⟩
theorem op_domain : ∃ _op : Op, True := ⟨.ADD, True.intro⟩
theorem push_data_joint : ∃ (n : Fin 33) (_ : Vector UInt8 n), True :=
  ⟨width, #v[0x2a], True.intro⟩
theorem instruction_domain : ∃ _i : Instr, True := ⟨push, True.intro⟩
theorem cons_data_joint : ∃ (_ : Instr) (_ : Program), True :=
  ⟨push, [.op .STOP], True.intro⟩
theorem program_pair_domain : ∃ (_ _ : Program), True := ⟨packet, packet, True.intro⟩
theorem program_domain : ∃ _p : Program, True := ⟨packet, True.intro⟩

theorem push_code_joint : ∃ (b : UInt8) (n : Fin 33), pushWidth b = some n :=
  ⟨pushCode width, width, pushWidth_pushCode width⟩
theorem op_of_push_joint : ∃ (b : UInt8) (n : Fin 33), pushWidth b = some n :=
  push_code_joint
theorem op_code_joint : ∃ (b : UInt8) (op : Op), Op.ofCode b = some op :=
  ⟨Op.ADD.code, .ADD, Op.ofCode_code .ADD⟩
theorem op_injective_joint : ∃ op op' : Op, op.code = op'.code := ⟨.ADD, .ADD, rfl⟩
theorem encode_injective_joint : ∃ p q : Program, encode p = encode q :=
  ⟨packet, packet, rfl⟩
theorem decode_joint : ∃ (bytes : List UInt8) (p : Program), decode bytes = some p :=
  ⟨encode packet, packet, decode_encode packet⟩

/-- Every intrinsically represented instruction program receives exact bytes. -/
def TotalEncoding (compiler : Program → Option (List UInt8)) : Prop :=
  ∀ p, ∃ bytes, compiler p = some bytes ∧ decode bytes = some p

theorem encoder_total : TotalEncoding (fun p => some (encode p)) :=
  fun p => ⟨encode p, rfl, decode_encode p⟩

theorem packet_bytes : encode packet = [0x60, 0x2a, 0x00] := rfl

theorem reject_all_encoder_fails : ¬ TotalEncoding (fun _ => none) := by
  intro h
  obtain ⟨bytes, emitted, _⟩ := h packet
  cases emitted

theorem empty_encoder_fails : ¬ TotalEncoding (fun _ => some []) := by
  intro h
  obtain ⟨bytes, emitted, decoded⟩ := h packet
  cases Option.some.inj emitted
  simp only [decode] at decoded
  have different : ([] : Program) = packet := Option.some.inj decoded
  cases different

theorem reverting_encoder_fails : ¬ TotalEncoding (fun _ => some (encode [.op .REVERT])) := by
  intro h
  obtain ⟨bytes, emitted, decoded⟩ := h packet
  cases Option.some.inj emitted
  rw [decode_encode] at decoded
  have different : ([.op .REVERT] : Program) = packet := Option.some.inj decoded
  cases different

theorem undefined_byte_failure : decode [0x0c] = none := by
  have hp : pushWidth (0x0c : UInt8) = none := by decide +kernel
  have ho : Op.ofCode (0x0c : UInt8) = none := by decide +kernel
  rw [decode, hp, ho]
theorem truncated_push_failure : decode [0x60] = none := by
  change decode [pushCode width] = none
  have short : ¬ width.val ≤ ([] : List UInt8).length := by decide
  rw [decode, pushWidth_pushCode]
  simp only [dif_neg short]
/-- CLZ belongs to the fixed Osaka opcode alphabet used by this interface. -/
theorem osaka_clz : decode [0x1e] = some [.op .CLZ] := decode_encode [.op .CLZ]

#print axioms width_domain
#print axioms byte_domain
#print axioms op_domain
#print axioms push_data_joint
#print axioms instruction_domain
#print axioms cons_data_joint
#print axioms program_pair_domain
#print axioms program_domain
#print axioms push_code_joint
#print axioms op_of_push_joint
#print axioms op_code_joint
#print axioms op_injective_joint
#print axioms encode_injective_joint
#print axioms decode_joint
#print axioms encoder_total
#print axioms packet_bytes
#print axioms reject_all_encoder_fails
#print axioms empty_encoder_fails
#print axioms reverting_encoder_fails
#print axioms undefined_byte_failure
#print axioms truncated_push_failure
#print axioms osaka_clz
end Solidity.H62.EvmCompilerAudit.Opcode
