import Solidity.Backend.LabelExec.Placement

/-! Actual entry-to-test execution for literal-condition loops. This consumes
emitted JUMPDEST and PUSH bytes, deriving the condition rather than accepting a
reached test state. Counted gasless cuts do not assert source termination. -/
namespace Solidity.Backend.LabelExec

/-- The two real instructions preceding the generated literal-loop test. -/
theorem literal_entry_prefix (pre post : List UInt8) (w : Fin 33)
    (imm : Vector UInt8 w) (tail : Scalar.Stack) (n : Nat) :
    advance (n+2) (pre ++ ((Instr.op .JUMPDEST).encode ++
      ((Instr.push w imm).encode ++ post))) ⟨pre.length,tail⟩ =
    advance n (pre ++ ((Instr.op .JUMPDEST).encode ++
      ((Instr.push w imm).encode ++ post)))
      ⟨pre.length+1+(Instr.push w imm).size,Scalar.immediate imm.toList :: tail⟩ := by
  have hs : step (pre ++ ((Instr.op .JUMPDEST).encode ++
      ((Instr.push w imm).encode ++ post))) ⟨pre.length,tail⟩ =
      some ⟨pre.length+1,tail⟩ := by
    rw [step_prefix]
    rfl
  have hp : step (pre ++ ((Instr.op .JUMPDEST).encode ++
      ((Instr.push w imm).encode ++ post))) ⟨pre.length+1,tail⟩ =
      some ⟨pre.length+1+(Instr.push w imm).size,Scalar.immediate imm.toList :: tail⟩ := by
    simpa only [List.append_assoc, List.length_append, Instr.length_encode,
      Instr.size] using push_prefix (pre ++ (Instr.op .JUMPDEST).encode) w imm post tail
  rw [advance, hs, Option.bind_some, advance, hp, Option.bind_some]

/-- Consume the actual emitted head and literal condition before the checked
loop test. Both computed branches retain the original physical tail. No
reached-test/condition/step or favourable destination premise is supplied. -/
theorem literal_loop_header_at (before after : List (Item Nat Empty))
    (w : Fin 33) (imm : Vector UInt8 w) (body : Block) (n : Nat)
    (out : Assembled Empty)
    (h : assemble 0 emptyLink (placedItems before after [.push w imm] body n) = some out)
    (tail : Scalar.Stack) :
    advance 5 (encode out.code)
      ⟨size (emitPrefix (placedItems before after [.push w imm] body n) before),tail⟩ =
      if Scalar.immediate imm.toList == 0 then
        some ⟨offset out.code
          (before.length + ((Block.loop [.push w imm] body).expand n).1.length-1),tail⟩
      else some ⟨size (emitPrefix (placedItems before after [.push w imm] body n)
          (before ++ checkPrefix [.push w imm] n)) + 1 +
        (Instr.push (asmWidths 0 (placedItems before after [.push w imm] body n) (n+1))
          (labelImm (placedItems before after [.push w imm] body n) (n+1))).size + 1,tail⟩ := by
  let items := placedItems before after [.push w imm] body n
  let rest : List (Item Nat Empty) :=
    [.instr (.op .ISZERO), .pushTag (n+1), .instr (.op .JUMPI)] ++
      (body.expand (n+2)).1 ++ [.pushTag n, .instr (.op .JUMP), .tag (n+1)] ++ after
  have hcode : encode out.code = encode (emitPrefix items before) ++
      ((Instr.op .JUMPDEST).encode ++ ((Instr.push w imm).encode ++
        encode (emitPrefix items rest))) := by
    have hc : out.code = items.map (Item.emit (asmWidths 0 items)
        (tagOffset (asmWidths 0 items) items) 0 emptyLink) := (assemble_eq h).2.1
    rw [hc]
    simp only [items, rest, placedItems, Block.expand, emitPrefix, List.map_append,
      List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
      List.nil_append, encode_append, encode_cons, Item.emit]
  have hp : advance 5 (encode out.code)
      ⟨size (emitPrefix items before),tail⟩ =
      advance 3 (encode out.code)
        ⟨size (emitPrefix items before)+1+(Instr.push w imm).size,
          Scalar.immediate imm.toList :: tail⟩ := by
    rw [hcode]
    simpa only [length_encode] using literal_entry_prefix
      (encode (emitPrefix items before)) (encode (emitPrefix items rest)) w imm tail 3
  have ht : size (emitPrefix items (before ++ checkPrefix [.push w imm] n)) =
      size (emitPrefix items before)+1+(Instr.push w imm).size := by
    simp only [checkPrefix, emitPrefix, List.map_append, List.map_cons, List.map_nil,
      Item.emit, size, List.sum_append_nat, List.sum_cons, List.sum_nil, Instr.size,
      Nat.add_zero, Nat.add_assoc]
  rw [hp, ← ht]
  exact loop_header_at before after [.push w imm] body n out h
    (Scalar.immediate imm.toList) tail

end Solidity.Backend.LabelExec
