import Solidity.Backend.LabelExec.Fetch

/-! Runtime jump packets, with the whole actual byte code and arbitrary
physical stack tails. Invalid targets remain a computed branch. -/
namespace Solidity.Backend.LabelExec

/-- An actual encoded PUSH followed by an actual branch instruction. -/
def branchCode (pre : List UInt8) (n : Fin 33) (imm : Vector UInt8 n)
    (branch : Op) (post : List UInt8) : List UInt8 :=
  pre ++ ((Instr.push n imm).encode ++ ((Instr.op branch).encode ++ post))

/-- Two real fetched byte instructions execute the resolved jump, or reject
its actual scanned destination. No successful step premise is supplied. -/
theorem jump_packet (pre : List UInt8) (n : Fin 33) (imm : Vector UInt8 n)
    (post : List UInt8) (tail : Scalar.Stack) :
    advance 2 (branchCode pre n imm .JUMP post) ⟨pre.length,tail⟩ =
      if validJumpdest (branchCode pre n imm .JUMP post)
          (Scalar.immediate imm.toList).toNat then
        some ⟨(Scalar.immediate imm.toList).toNat,tail⟩ else none := by
  simp only [advance, branchCode, push_prefix, Option.bind_some, Option.bind_fun_some]
  have h : step ((pre ++ (Instr.push n imm).encode) ++ ((Instr.op .JUMP).encode ++ post))
      ⟨(pre ++ (Instr.push n imm).encode).length, Scalar.immediate imm.toList :: tail⟩ =
      effect ((pre ++ (Instr.push n imm).encode) ++ ((Instr.op .JUMP).encode ++ post))
        (.op .JUMP) ⟨(pre ++ (Instr.push n imm).encode).length, Scalar.immediate imm.toList :: tail⟩ :=
    step_prefix (pre ++ (Instr.push n imm).encode) (.op .JUMP) post
    (Scalar.immediate imm.toList :: tail)
  simpa only [List.append_assoc, List.length_append, Instr.length_encode, effect] using h

/-- Conditional transfer consumes both operands. An untaken jump does not
validate the destination; a taken invalid destination has no slice step. -/
theorem jumpi_packet (pre : List UInt8) (n : Fin 33) (imm : Vector UInt8 n)
    (post : List UInt8) (condition : Scalar.Word) (tail : Scalar.Stack) :
    advance 2 (branchCode pre n imm .JUMPI post) ⟨pre.length,condition :: tail⟩ =
      if condition == 0 then some ⟨pre.length + (Instr.push n imm).size + 1,tail⟩
      else if validJumpdest (branchCode pre n imm .JUMPI post)
          (Scalar.immediate imm.toList).toNat then
        some ⟨(Scalar.immediate imm.toList).toNat,tail⟩ else none := by
  simp only [advance, branchCode, push_prefix, Option.bind_some, Option.bind_fun_some]
  simpa only [List.append_assoc, List.length_append, Instr.length_encode, effect] using
    (step_prefix (pre ++ (Instr.push n imm).encode) (.op .JUMPI) post
      (Scalar.immediate imm.toList :: condition :: tail))

/-- The exact control test emitted before an if/loop conditional jump. -/
def testCode (pre : List UInt8) (n : Fin 33) (imm : Vector UInt8 n)
    (post : List UInt8) : List UInt8 :=
  pre ++ ((Instr.op .ISZERO).encode ++
    ((Instr.push n imm).encode ++ ((Instr.op .JUMPI).encode ++ post)))

/-- Actual ISZERO/PUSH/JUMPI execution selects the false/exit branch exactly
when the original condition is zero; no supplied Boolean reply chooses it. -/
theorem test_packet (pre : List UInt8) (n : Fin 33) (imm : Vector UInt8 n)
    (post : List UInt8) (condition : Scalar.Word) (tail : Scalar.Stack) :
    advance 3 (testCode pre n imm post) ⟨pre.length,condition :: tail⟩ =
      if condition == 0 then
        if validJumpdest (testCode pre n imm post) (Scalar.immediate imm.toList).toNat then
          some ⟨(Scalar.immediate imm.toList).toNat,tail⟩ else none
      else some ⟨pre.length + 1 + (Instr.push n imm).size + 1,tail⟩ := by
  rw [testCode, advance, step_prefix]
  simp only [effect, Scalar.step, Scalar.numericStep, Scalar.unary, Scalar.applyUnary,
    Option.map_some, Option.bind_some, Instr.size]
  have hj : advance 2 (branchCode (pre ++ (Instr.op .ISZERO).encode) n imm .JUMPI post)
      ⟨(pre ++ (Instr.op .ISZERO).encode).length, Scalar.flag (condition == 0) :: tail⟩ =
      if Scalar.flag (condition == 0) == 0 then
        some ⟨(pre ++ (Instr.op .ISZERO).encode).length + (Instr.push n imm).size + 1,tail⟩
      else if validJumpdest (branchCode (pre ++ (Instr.op .ISZERO).encode) n imm .JUMPI post)
          (Scalar.immediate imm.toList).toNat then some ⟨(Scalar.immediate imm.toList).toNat,tail⟩
      else none := jumpi_packet _ _ _ _ _ _
  have hz : ((0 : Scalar.Word) == 0) = true := rfl
  have ho : ((1 : Scalar.Word) == 0) = false := rfl
  cases hw : condition == 0 <;>
    simpa only [branchCode, List.append_assoc, List.length_append, Instr.length_encode,
      Instr.size, hw, Scalar.flag, Bool.false_eq_true, if_false, if_pos rfl, hz, ho] using hj

end Solidity.Backend.LabelExec
