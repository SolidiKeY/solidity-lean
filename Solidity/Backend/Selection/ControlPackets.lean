import Solidity.Backend.Selection.ExecutionTrace

/-! Capacity clients of the existing assembled jump packets. -/
namespace Solidity.Backend.Selection.ExecutionTrace

/-- Fetch an actual placed instruction using the assembler's emitted program. -/
theorem placed_step (before after : List (Item Nat Empty)) (instruction : Instr)
    (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink
      (before ++ .instr instruction :: after) = some out) (stack : Scalar.Stack) :
    LabelExec.step (encode out.code)
      ⟨size (LabelExec.emitPrefix (before ++ .instr instruction :: after) before),stack⟩ =
    LabelExec.effect (encode out.code) instruction
      ⟨size (LabelExec.emitPrefix (before ++ .instr instruction :: after) before),stack⟩ := by
  let items : List (Item Nat Empty) := before ++ .instr instruction :: after
  have emitted : out.code = LabelExec.emitPrefix items before ++
      instruction :: LabelExec.emitPrefix items after := by
    rw [(assemble_eq assembly).2.1]
    simp only [items, LabelExec.emitPrefix, List.map_append, List.map_cons, Item.emit]
  rw [emitted, encode_append, encode_cons]
  simpa only [length_encode] using LabelExec.step_prefix
    (encode (LabelExec.emitPrefix items before)) instruction
    (encode (LabelExec.emitPrefix items after)) stack

/-- Split a real two-step packet at its independently fetched first step. -/
theorem two {bytes : List UInt8} {start middle finish : LabelExec.State}
    (actual : LabelExec.advance 2 bytes start = some finish)
    (first : LabelExec.step bytes start = some middle)
    (entry : start.stack.length ≤ 1024) (peak : middle.stack.length ≤ 1024)
    (exit : finish.stack.length ≤ 1024) : Safe bytes 2 start finish := by
  have second : LabelExec.step bytes middle = some finish := by
    simpa only [LabelExec.advance, first, Option.bind_some, Option.bind_fun_some] using actual
  exact append (single bytes start middle first entry peak)
    (single bytes middle finish second peak exit)

/-- The first PUSH of any assembled branch packet is actually fetched. -/
theorem branch_push (before after : List (Item Nat Empty)) (label : Nat) (branch : Op)
    (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink
      (before ++ .pushTag label :: .instr (.op branch) :: after) = some out)
    (stack : Scalar.Stack) :
    LabelExec.step (encode out.code)
      ⟨size (LabelExec.emitPrefix (before ++ .pushTag label :: .instr (.op branch) :: after) before),stack⟩ =
    some ⟨size (LabelExec.emitPrefix (before ++ .pushTag label :: .instr (.op branch) :: after) before) +
      (Instr.push (asmWidths 0 (before ++ .pushTag label :: .instr (.op branch) :: after) label)
        (LabelExec.labelImm (before ++ .pushTag label :: .instr (.op branch) :: after) label)).size,
      Scalar.immediate (LabelExec.labelImm
        (before ++ .pushTag label :: .instr (.op branch) :: after) label).toList :: stack⟩ := by
  let items : List (Item Nat Empty) := before ++ .pushTag label :: .instr (.op branch) :: after
  let instruction : Instr := .push (asmWidths 0 items label) (LabelExec.labelImm items label)
  have emitted : out.code = LabelExec.emitPrefix items before ++
      instruction :: .op branch :: LabelExec.emitPrefix items after := by
    rw [(assemble_eq assembly).2.1]
    simp only [items, instruction, LabelExec.labelImm, LabelExec.emitPrefix,
      List.map_append, List.map_cons, Item.emit, Nat.zero_add]
  rw [emitted, encode_append, encode_cons]
  rw [← length_encode (LabelExec.emitPrefix items before), LabelExec.step_prefix]
  rfl

/-- Actual target resolution and one temporary operand give a bounded JUMP. -/
theorem jump (before after : List (Item Nat Empty)) (label : Nat) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink
      (before ++ .pushTag label :: .instr (.op .JUMP) :: after) = some out)
    (stack : Scalar.Stack) (room : stack.length + 1 ≤ 1024) :
    ∃ target : Nat,
      tagIndex (before ++ .pushTag label :: .instr (.op .JUMP) :: after) label = some target ∧
      Safe (encode out.code) 2
        ⟨size (LabelExec.emitPrefix (before ++ .pushTag label :: .instr (.op .JUMP) :: after) before),stack⟩
        ⟨offset out.code target,stack⟩ := by
  obtain ⟨target,found,actual⟩ := LabelExec.assembled_jump before after label out assembly stack
  refine ⟨target,found,?_⟩
  apply two actual (branch_push before after label .JUMP out assembly stack)
  · change stack.length ≤ 1024; omega
  · exact room
  · change stack.length ≤ 1024; omega

/-- Both conditional arms consume the real condition and fit their PUSH peak. -/
theorem jumpi (before after : List (Item Nat Empty)) (label : Nat) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink
      (before ++ .pushTag label :: .instr (.op .JUMPI) :: after) = some out)
    (condition : Scalar.Word) (stack : Scalar.Stack) (room : stack.length + 2 ≤ 1024) :
    ∃ target : Nat,
      tagIndex (before ++ .pushTag label :: .instr (.op .JUMPI) :: after) label = some target ∧
      Safe (encode out.code) 2
        ⟨size (LabelExec.emitPrefix (before ++ .pushTag label :: .instr (.op .JUMPI) :: after) before),condition :: stack⟩
        ⟨if condition == 0 then
          size (LabelExec.emitPrefix (before ++ .pushTag label :: .instr (.op .JUMPI) :: after) before) +
            (Instr.push (asmWidths 0 (before ++ .pushTag label :: .instr (.op .JUMPI) :: after) label)
              (LabelExec.labelImm (before ++ .pushTag label :: .instr (.op .JUMPI) :: after) label)).size + 1
          else offset out.code target,stack⟩ := by
  obtain ⟨target,found,actual⟩ := LabelExec.assembled_jumpi before after label out assembly condition stack
  have actual_at : LabelExec.advance 2 (encode out.code)
      ⟨size (LabelExec.emitPrefix (before ++ .pushTag label :: .instr (.op .JUMPI) :: after) before),condition :: stack⟩ =
      some ⟨if condition == 0 then
        size (LabelExec.emitPrefix (before ++ .pushTag label :: .instr (.op .JUMPI) :: after) before) +
          (Instr.push (asmWidths 0 (before ++ .pushTag label :: .instr (.op .JUMPI) :: after) label)
            (LabelExec.labelImm (before ++ .pushTag label :: .instr (.op .JUMPI) :: after) label)).size + 1
        else offset out.code target,stack⟩ := by
    cases zero : condition == 0 <;>
      simpa only [zero, Bool.false_eq_true, if_false, if_true] using actual
  refine ⟨target,found,?_⟩
  apply two actual_at (branch_push before after label .JUMPI out assembly (condition :: stack))
  · change stack.length + 1 ≤ 1024; omega
  · change stack.length + 1 + 1 ≤ 1024; omega
  · change stack.length ≤ 1024; omega

/-- Item-index offsets are converted using actual assembled byte sizes. -/
theorem offset_before (before after : List (Item Nat Empty)) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink (before ++ after) = some out) :
    offset out.code before.length = size (LabelExec.emitPrefix (before ++ after) before) := by
  rw [(assemble_eq assembly).2.1]
  simp only [offset, ← List.map_take, List.take_left, LabelExec.emitPrefix]

/-- The generated ISZERO/PUSH/JUMPI test retains all intermediate bounds. -/
theorem test (before after : List (Item Nat Empty)) (label : Nat) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink (LabelExec.testItems before after label) = some out)
    (condition : Scalar.Word) (stack : Scalar.Stack) (room : stack.length + 2 ≤ 1024) :
    ∃ target : Nat, tagIndex (LabelExec.testItems before after label) label = some target ∧
      Safe (encode out.code) 3
        ⟨size (LabelExec.emitPrefix (LabelExec.testItems before after label) before),condition :: stack⟩
        ⟨if condition == 0 then offset out.code target
          else size (LabelExec.emitPrefix (LabelExec.testItems before after label)
            (before ++ [.instr (.op .ISZERO), .pushTag label, .instr (.op .JUMPI)])),stack⟩ := by
  let items : List (Item Nat Empty) := LabelExec.testItems before after label
  let flag : Scalar.Word := if condition == 0 then 1 else 0
  have pushAssembly : assemble 0 LabelExec.emptyLink
      ((before ++ [.instr (.op .ISZERO)]) ++ .pushTag label :: .instr (.op .JUMPI) :: after) =
      some out := by
    simpa only [LabelExec.testItems, List.append_assoc, List.cons_append, List.nil_append] using assembly
  obtain ⟨target,found,rest⟩ := jumpi (before ++ [.instr (.op .ISZERO)]) after label out
    pushAssembly flag stack room
  have first_step : LabelExec.step (encode out.code)
      ⟨size (LabelExec.emitPrefix items before),condition :: stack⟩ =
      some ⟨size (LabelExec.emitPrefix items before) + 1,flag :: stack⟩ := by
    dsimp only [items, LabelExec.testItems]
    rw [placed_step before (.pushTag label :: .instr (.op .JUMPI) :: after)
      (.op .ISZERO) out assembly (condition :: stack)]
    rfl
  have entry : (condition :: stack).length ≤ 1024 := by
    simp only [List.length_cons]; omega
  have peak : (flag :: stack).length ≤ 1024 := by
    simp only [List.length_cons]; omega
  have first_safe : Safe (encode out.code) 1
      ⟨size (LabelExec.emitPrefix items before),condition :: stack⟩
      ⟨size (LabelExec.emitPrefix items before) + 1,flag :: stack⟩ :=
    single _ _ _ first_step entry peak
  have pc_after_iszero : size (LabelExec.emitPrefix items (before ++ [.instr (.op .ISZERO)])) =
      size (LabelExec.emitPrefix items before) + 1 := by
    rw [emit_append, size_append]
    rfl
  have pc_after_test : size (LabelExec.emitPrefix items
      (before ++ [.instr (.op .ISZERO), .pushTag label, .instr (.op .JUMPI)])) =
      size (LabelExec.emitPrefix items before) + 1 +
        (Instr.push (asmWidths 0 items label) (LabelExec.labelImm items label)).size + 1 := by
    rw [emit_append, size_append]
    simp only [LabelExec.emitPrefix, List.map_cons, List.map_nil, Item.emit,
      Nat.zero_add, size, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero, Instr.size]
    omega
  have same_items : ((before ++ [.instr (.op .ISZERO)]) ++
      .pushTag label :: .instr (.op .JUMPI) :: after) = items := by
    simp only [items, LabelExec.testItems, List.append_assoc, List.cons_append, List.nil_append]
  rw [same_items] at found rest
  rw [pc_after_iszero] at rest
  have flag_zero : (flag == 0) = !(condition == 0) := by
    cases zero : condition == 0 <;> simp only [flag, zero, Bool.false_eq_true, if_false, if_true] <;> rfl
  rw [flag_zero] at rest
  refine ⟨target,found,?_⟩
  have rest_at : Safe (encode out.code) 2
      ⟨size (LabelExec.emitPrefix items before) + 1,flag :: stack⟩
      ⟨if condition == 0 then offset out.code target else
        size (LabelExec.emitPrefix items
          (before ++ [.instr (.op .ISZERO), .pushTag label, .instr (.op .JUMPI)])),stack⟩ := by
    rw [pc_after_test]
    cases zero : condition == 0 <;>
      simpa only [zero, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true] using rest
  exact append first_safe rest_at

/-- Successful assembly identifies a tag at its genuine item position. -/
theorem tag_before (before after : List (Item Nat Empty)) (label : Nat) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink (before ++ .tag label :: after) = some out) :
    tagIndex (before ++ .tag label :: after) label = some before.length := by
  have checked : layoutOk 0 (before ++ .tag label :: after)
      (asmWidths 0 (before ++ .tag label :: after)) = true := (assemble_eq assembly).1
  simp only [layoutOk, Bool.and_eq_true, decide_eq_true_eq] at checked
  apply tagIndex_unique checked.1.1
  simp only [List.getElem?_append_right (Nat.le_refl before.length), Nat.sub_self,
    List.getElem?_cons_zero]

/-- JUMPDEST itself is executed, including its final one-byte PC advance. -/
theorem tag (before after : List (Item Nat Empty)) (label : Nat) (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink (before ++ .tag label :: after) = some out)
    (stack : Scalar.Stack) (room : stack.length ≤ 1024) :
    Safe (encode out.code) 1
      ⟨size (LabelExec.emitPrefix (before ++ .tag label :: after) before),stack⟩
      ⟨size (LabelExec.emitPrefix (before ++ .tag label :: after) (before ++ [.tag label])),stack⟩ := by
  let items : List (Item Nat Empty) := before ++ .tag label :: after
  have emitted : out.code = LabelExec.emitPrefix items before ++
      .op .JUMPDEST :: LabelExec.emitPrefix items after := by
    rw [(assemble_eq assembly).2.1]
    simp only [items, LabelExec.emitPrefix, List.map_append, List.map_cons, Item.emit]
  have actual : LabelExec.step (encode out.code)
      ⟨size (LabelExec.emitPrefix items before),stack⟩ =
      some ⟨size (LabelExec.emitPrefix items before) + 1,stack⟩ := by
    rw [emitted, encode_append, encode_cons]
    rw [← length_encode (LabelExec.emitPrefix items before), LabelExec.step_prefix]
    rfl
  have end_pc : size (LabelExec.emitPrefix items (before ++ [.tag label])) =
      size (LabelExec.emitPrefix items before) + 1 := by
    rw [emit_append, size_append]
    rfl
  change Safe _ 1 ⟨size (LabelExec.emitPrefix items before),stack⟩
    ⟨size (LabelExec.emitPrefix items (before ++ [.tag label])),stack⟩
  rw [end_pc]
  exact single _ _ _ actual room room

#print axioms tag_before
#print axioms tag

#print axioms offset_before
#print axioms test

#print axioms placed_step
#print axioms two
#print axioms branch_push
#print axioms jump
#print axioms jumpi

end Solidity.Backend.Selection.ExecutionTrace
