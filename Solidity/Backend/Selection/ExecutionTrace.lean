import Solidity.Backend.Selection.StackSelection

/-! Capacity-bounded traces of the existing byte-PC machine. This is a
certificate predicate over LabelExec.advance, not another execution semantics. -/
namespace Solidity.Backend.Selection
namespace ExecutionTrace

/-- The exact execution and every reached instruction boundary are retained. -/
def Safe (bytes : List UInt8) (count : Nat) (start finish : LabelExec.State) : Prop :=
  LabelExec.advance count bytes start = some finish ∧
    ∀ k : Nat, k ≤ count → ∃ reached : LabelExec.State,
      LabelExec.advance k bytes start = some reached ∧ reached.stack.length ≤ 1024

theorem advance_add (left right : Nat) (bytes : List UInt8) (start : LabelExec.State) :
    LabelExec.advance (left + right) bytes start =
      (LabelExec.advance left bytes start).bind (LabelExec.advance right bytes) := by
  induction left generalizing start with
  | zero => simp only [Nat.zero_add, LabelExec.advance, Option.bind_some]
  | succ left ih =>
    simp only [Nat.succ_add, LabelExec.advance, Option.bind_assoc]
    congr 1
    funext middle
    exact ih middle

theorem prefix_reached (bytes : List UInt8) (count : Nat) (start finish : LabelExec.State)
    (actual : LabelExec.advance count bytes start = some finish)
    (k : Nat) (within : k ≤ count) :
    ∃ reached, LabelExec.advance k bytes start = some reached ∧
      LabelExec.advance (count - k) bytes reached = some finish := by
  have split : count = k + (count - k) := by omega
  rw [split, advance_add] at actual
  cases found : LabelExec.advance k bytes start with
  | none => simp only [found, Option.bind_none, reduceCtorEq] at actual
  | some reached =>
    exact ⟨reached, rfl, by simpa only [found, Option.bind_some] using actual⟩

theorem zero (bytes : List UInt8) (state : LabelExec.State)
    (bound : state.stack.length ≤ 1024) : Safe bytes 0 state state := by
  refine ⟨rfl, ?_⟩
  intro k within
  have same : k = 0 := by omega
  subst k
  exact ⟨state, rfl, bound⟩

theorem single (bytes : List UInt8) (start finish : LabelExec.State)
    (actual : LabelExec.step bytes start = some finish)
    (entry : start.stack.length ≤ 1024) (exit : finish.stack.length ≤ 1024) :
    Safe bytes 1 start finish := by
  refine ⟨?_, ?_⟩
  · simp only [LabelExec.advance, actual, Option.bind_some]
  · intro k within
    have cases_k : k = 0 ∨ k = 1 := by omega
    rcases cases_k with rfl | rfl
    · exact ⟨start, rfl, entry⟩
    · exact ⟨finish, by simp only [LabelExec.advance, actual, Option.bind_some], exit⟩

theorem append {bytes : List UInt8} {left right : Nat} {start middle finish : LabelExec.State}
    (first : Safe bytes left start middle) (second : Safe bytes right middle finish) :
    Safe bytes (left + right) start finish := by
  refine ⟨?_, ?_⟩
  · rw [advance_add, first.1, Option.bind_some]
    exact second.1
  · intro k within
    by_cases early : k ≤ left
    · exact first.2 k early
    · have late : k - left ≤ right := by omega
      obtain ⟨reached, actual, bound⟩ := second.2 (k - left) late
      refine ⟨reached, ?_, bound⟩
      have split : k = left + (k - left) := by omega
      rw [split, advance_add, first.1, Option.bind_some]
      exact actual

theorem size_append (first second : Program) : size (first ++ second) = size first + size second := by
  simp only [size, List.map_append, List.sum_append_nat]

/-- Actual scalar evaluation executes exactly its instructions at encoded PCs,
retaining arbitrary surrounding bytes and deriving every prefix bound. -/
theorem scalar_bytes (code : Program) (before after : List UInt8) (input output : Scalar.Stack)
    (actual : Scalar.run code input = some output)
    (capacity : Scalar.stackBound code (input.length : Int) = true) :
    Safe (before ++ (encode code ++ after)) code.length
      ⟨before.length, input⟩ ⟨before.length + size code, output⟩ := by
  induction code generalizing before input with
  | nil =>
    cases actual
    have entry : output.length ≤ 1024 := Scalar.run_capacity rfl capacity
    simpa only [encode_nil, size, List.map_nil, List.sum_nil, Nat.add_zero,
      List.nil_append] using zero (before ++ after) ⟨before.length, output⟩ entry
  | cons instruction rest ih =>
    cases step : Scalar.step instruction input with
    | none => simp only [Scalar.run, step, Option.bind_none, reduceCtorEq] at actual
    | some reached =>
      simp only [Scalar.run, step, Option.bind_some] at actual
      have height : (reached.length : Int) = (input.length : Int) + Scalar.stackDelta instruction :=
        Scalar.step_height step
      have entry : input.length ≤ 1024 := Scalar.prefix_capacity [] (instruction :: rest) rfl capacity
      have after_head : reached.length ≤ 1024 :=
        Scalar.prefix_capacity [instruction] rest (by simp only [Scalar.run, step, Option.bind_some]) capacity
      have remainder : Scalar.stackBound rest (reached.length : Int) = true := by
        rw [height]
        simp only [Scalar.stackBound, Scalar.heightTrace, List.all_cons, Bool.and_eq_true] at capacity
        exact capacity.2
      have first : Safe (before ++ (encode (instruction :: rest) ++ after)) 1
          ⟨before.length, input⟩ ⟨before.length + instruction.size, reached⟩ := by
        apply single _ _ _ ?_ entry after_head
        simp only [encode_cons, List.append_assoc]
        rw [LabelExec.step_prefix]
        exact LabelExec.effect_of_scalar _ _ _ _ _ step
      have rest_trace : Safe ((before ++ instruction.encode) ++ (encode rest ++ after)) rest.length
          ⟨(before ++ instruction.encode).length, reached⟩
          ⟨(before ++ instruction.encode).length + size rest, output⟩ :=
        ih (before ++ instruction.encode) reached actual remainder
      have rest_trace_at : Safe (before ++ (encode (instruction :: rest) ++ after)) rest.length
          ⟨before.length + instruction.size, reached⟩
          ⟨before.length + size (instruction :: rest), output⟩ := by
        simpa only [encode_cons, List.append_assoc, List.length_append, Instr.length_encode,
          size, List.map_cons, List.sum_cons, Nat.add_assoc] using rest_trace
      simpa only [List.length_cons, Nat.add_comm] using append first rest_trace_at

/-- Static shape determines the height of the actual scalar result. -/
theorem code_length {code : Program} {inputHeight outputHeight : Nat}
    (shape : LabelExec.CodeShape code inputHeight outputHeight)
    (input output : Scalar.Stack) (actual : Scalar.run code input = some output)
    (height : input.length = inputHeight) : output.length = outputHeight := by
  induction shape generalizing input with
  | nil n => cases actual; exact height
  | @cons instruction rest n m k head tail ih =>
    cases step : Scalar.step instruction input with
    | none => simp only [Scalar.run, step, Option.bind_none, reduceCtorEq] at actual
    | some reached =>
      simp only [Scalar.run, step, Option.bind_some] at actual
      rcases head with ⟨consumed, produced, suffix, row, hin, hout⟩
      obtain ⟨derived, computed, length⟩ :=
        LabelExec.arity_domain instruction consumed produced suffix input row (height.trans hin)
      have same : derived = reached := Option.some.inj (computed.symm.trans step)
      have reached_length : reached.length = m := by
        rw [← same]
        exact length.trans hout.symm
      exact ih reached actual reached_length

/-- Height preservation is derived from actual structured execution, not a
value-frame assumption about condition code. -/
theorem structured_length {block : Block} {n m : Nat}
    (shape : LabelExec.BlockShape block n m) {input output : Scalar.Stack}
    (actual : StructuredExec block input output) (height : input.length = n) :
    output.length = m := by
  induction actual generalizing n m with
  | code run =>
    cases shape with
    | code code => exact code_length code.shape _ _ run height
  | seq left right ihLeft ihRight =>
    cases shape with
    | seq leftShape rightShape => exact ihRight rightShape (ihLeft leftShape height)
  | @iteTrue cond left right input middle output word condition nonzero body ih =>
    cases shape with
    | @ite n m c a b leftShape rightShape cap =>
      have result : (word :: middle).length = n + 1 := code_length c.shape _ _ condition height
      have middle_length : middle.length = n := by simp only [List.length_cons] at result; omega
      exact ih leftShape middle_length
  | @iteFalse cond left right input middle output condition body ih =>
    cases shape with
    | @ite n m c a b leftShape rightShape cap =>
      have result : ((0 : Scalar.Word) :: middle).length = n + 1 := code_length c.shape _ _ condition height
      have middle_length : middle.length = n := by simp only [List.length_cons] at result; omega
      exact ih rightShape middle_length
  | @loopDone cond body input output condition =>
    cases shape with
    | @loop n c body bodyShape cap =>
      have result : ((0 : Scalar.Word) :: output).length = n + 1 :=
        code_length c.shape _ _ condition height
      simp only [List.length_cons] at result
      omega
  | @loopMore cond body input first second output word condition nonzero bodyRun rest ihBody ihRest =>
    cases shape with
    | @loop n c b bodyShape cap =>
      have result : (word :: first).length = n + 1 := code_length c.shape _ _ condition height
      have first_length : first.length = n := by simp only [List.length_cons] at result; omega
      have second_length : second.length = n := ihBody bodyShape first_length
      exact ihRest (.loop bodyShape cap) second_length

theorem emit_append (items first second : List (Item Nat Empty)) :
    LabelExec.emitPrefix items (first ++ second) =
      LabelExec.emitPrefix items first ++ LabelExec.emitPrefix items second := by
  simp only [LabelExec.emitPrefix, List.map_append]

theorem emit_instructions (items : List (Item Nat Empty)) (code : Program) :
    LabelExec.emitPrefix items (code.map Item.instr) = code := by
  induction code with
  | nil => rfl
  | cons instruction rest ih =>
    change instruction :: LabelExec.emitPrefix items (rest.map Item.instr) = instruction :: rest
    rw [ih]

/-- Consume actual assembled code equality at any byte prefix/suffix placement. -/
theorem placed_scalar (before after : List (Item Nat Empty)) (code : Program)
    (out : Assembled Empty)
    (assembly : assemble 0 LabelExec.emptyLink (before ++ code.map Item.instr ++ after) = some out)
    (input output : Scalar.Stack) (actual : Scalar.run code input = some output)
    (capacity : Scalar.stackBound code (input.length : Int) = true) :
    Safe (encode out.code) code.length
      ⟨size (LabelExec.emitPrefix (before ++ code.map Item.instr ++ after) before), input⟩
      ⟨size (LabelExec.emitPrefix (before ++ code.map Item.instr ++ after)
        (before ++ code.map Item.instr)), output⟩ := by
  let items : List (Item Nat Empty) := before ++ code.map Item.instr ++ after
  have emitted : out.code = LabelExec.emitPrefix items before ++
      code ++ LabelExec.emitPrefix items after := by
    calc
      out.code = LabelExec.emitPrefix items items := (assemble_eq assembly).2.1
      _ = _ := by
        change LabelExec.emitPrefix items (before ++ code.map Item.instr ++ after) = _
        rw [emit_append, emit_append, emit_instructions]
  have end_pc : size (LabelExec.emitPrefix items (before ++ code.map Item.instr)) =
      size (LabelExec.emitPrefix items before) + size code := by
    rw [emit_append, emit_instructions, size_append]
  have transported : Safe (encode out.code) code.length
      ⟨size (LabelExec.emitPrefix items before), input⟩
      ⟨size (LabelExec.emitPrefix items before) + size code, output⟩ := by
    rw [emitted, encode_append, encode_append]
    simpa only [List.append_assoc, length_encode] using
      scalar_bytes code (encode (LabelExec.emitPrefix items before))
        (encode (LabelExec.emitPrefix items after)) input output actual capacity
  change Safe (encode out.code) code.length
    ⟨size (LabelExec.emitPrefix items before), input⟩
    ⟨size (LabelExec.emitPrefix items (before ++ code.map Item.instr)), output⟩
  rw [end_pc]
  exact transported

/-- The frozen control certificate is inhabited for every shaped code block. -/
def codeCertificate {n m : Nat} (code : LabelExec.Code n m) :
    ControlCertificate (.code code.instructions) n m where
  shape := .code code
  room := True.intro
  realize := by
    intro before after label out assembly input output height execution
    have actual : Scalar.run code.instructions input = some output := by
      cases execution with
      | code run => exact run
    have capacity : Scalar.stackBound code.instructions (input.length : Int) = true := by
      rw [height]
      exact code.capacity
    exact ⟨code.instructions.length, placed_scalar before after code.instructions out
      assembly input output actual capacity⟩

/-- Whole adjacent blocks compose at their actual reached intermediate stack. -/
def seqCertificate {left right : Block} {n middleHeight m : Nat}
    (first : ControlCertificate left n middleHeight)
    (second : ControlCertificate right middleHeight m) :
    ControlCertificate (.seq left right) n m where
  shape := .seq first.shape second.shape
  room := ⟨middleHeight, first.shape, second.shape, first.room, second.room⟩
  realize := by
    intro before after label out assembly input output height execution
    cases execution with
    | @seq a b s middle t leftRun rightRun =>
      let items : List (Item Nat Empty) := before ++ ((Block.seq left right).expand label).1 ++ after
      have left_assembly : assemble 0 LabelExec.emptyLink
          (before ++ (left.expand label).1 ++ ((right.expand (left.expand label).2).1 ++ after)) =
          some out := by
        simpa only [Block.expand, List.append_assoc] using assembly
      have right_assembly : assemble 0 LabelExec.emptyLink
          ((before ++ (left.expand label).1) ++ (right.expand (left.expand label).2).1 ++ after) =
          some out := by
        simpa only [Block.expand, List.append_assoc] using assembly
      have middle_length : middle.length = middleHeight := structured_length first.shape leftRun height
      obtain ⟨leftCount, leftActual, leftBound⟩ := first.realize before
        ((right.expand (left.expand label).2).1 ++ after) label out left_assembly
        input middle height leftRun
      obtain ⟨rightCount, rightActual, rightBound⟩ := second.realize
        (before ++ (left.expand label).1) after (left.expand label).2 out right_assembly
        middle output middle_length rightRun
      have left_safe : Safe (encode out.code) leftCount
          ⟨size (LabelExec.emitPrefix items before), input⟩
          ⟨size (LabelExec.emitPrefix items (before ++ (left.expand label).1)), middle⟩ := by
        simpa only [Safe, items, Block.expand, List.append_assoc] using And.intro leftActual leftBound
      have right_safe : Safe (encode out.code) rightCount
          ⟨size (LabelExec.emitPrefix items (before ++ (left.expand label).1)), middle⟩
          ⟨size (LabelExec.emitPrefix items (before ++ ((Block.seq left right).expand label).1)), output⟩ := by
        simpa only [Safe, items, Block.expand, List.append_assoc] using And.intro rightActual rightBound
      exact ⟨leftCount + rightCount, append left_safe right_safe⟩

#print axioms seqCertificate
#print axioms code_length
#print axioms structured_length
#print axioms placed_scalar
#print axioms codeCertificate
#print axioms advance_add
#print axioms prefix_reached
#print axioms append
#print axioms scalar_bytes

end ExecutionTrace
end Solidity.Backend.Selection
