import Solidity.Backend.Selection.NumericSequence
import Solidity.Backend.Selection.FrameCapacityV2

/-! Native stack-family selection and physical frame capacity. The existing IR
uses one-based DUP/SWAP indices; physical opcode indices are zero-based Fin16.
Runner equations use the existing numeric irStack representation. -/
namespace Solidity.Backend.Selection

/-- Relate the existing physical exchange to the IR's lookup/set operations. -/
theorem exchange_get_set (word : Scalar.Word) (index : Nat) (input : Scalar.Stack) :
    Scalar.exchange word index input =
      (input[index]?).map (fun old => (old, input.set index word)) := by
  induction index generalizing input with
  | zero => cases input <;> rfl
  | succ index ih =>
    cases input with
    | nil => rfl
    | cons head rest =>
      simp only [Scalar.exchange, ih, List.getElem?_cons_succ,
        List.set_cons_succ, Option.map_map]
      cases actual : rest[index]? <;> rfl

/-- Actual IR POP, with exact operand-shortage refusal. -/
def popCertificate : InstructionCertificate .pop :=
  certificateOfStep .pop [.op .POP] (by
    intro input m stack
    cases input <;> simp only [Evm.Instr.step, stack, irStack, List.map_nil,
      List.map_cons, Evm.Machine.next, Scalar.run, Scalar.step, Scalar.pop,
      Option.bind_none, Option.bind_some])

/-- All native DUP1 through DUP16, with explicit one-based IR translation. -/
def dupCertificate (index : Fin 16) : InstructionCertificate (.dup (index.val + 1)) :=
  certificateOfStep (.dup (index.val + 1)) [.op (.DUP index)] (by
    intro input m stack
    cases actual : input[index.val]? with
    | none =>
      simp only [Evm.Instr.step, stack, irStack, Nat.add_sub_cancel,
        List.getElem?_map, actual, Option.map_none, Scalar.run, Scalar.step,
        Scalar.duplicate, Option.bind_none]
    | some word =>
      simp only [Evm.Instr.step, stack, irStack, Nat.add_sub_cancel,
        List.getElem?_map, actual, Option.map_some, List.map_cons,
        Evm.Machine.next, Scalar.run, Scalar.step, Scalar.duplicate,
        Option.bind_some])

/-- All native SWAP1 through SWAP16; SWAP16 reaches the seventeenth word. -/
def swapCertificate (index : Fin 16) : InstructionCertificate (.swap (index.val + 1)) :=
  certificateOfStep (.swap (index.val + 1)) [.op (.SWAP index)] (by
    intro input m stack
    cases input with
    | nil =>
      simp only [Evm.Instr.step, stack, irStack, List.map_nil, Scalar.run,
        Scalar.step, Scalar.swap, Option.bind_none]
    | cons head rest =>
      cases actual : rest[index.val]? with
      | none =>
        simp only [Evm.Instr.step, stack, irStack, List.map_cons,
          List.getElem?_map, actual, Option.map_none, Scalar.run, Scalar.step,
          Scalar.swap, exchange_get_set, Option.bind_none]
      | some word =>
        simp only [Evm.Instr.step, stack, irStack, List.map_cons,
          List.getElem?_map, actual, Option.map_some, Scalar.run, Scalar.step,
          Scalar.swap, exchange_get_set, Option.bind_some, Evm.Machine.next,
          List.map_set])

/-- Native-family component selection; larger IR indices need another lowering. -/
def selectStack : (instruction : Evm.Instr) → Option (InstructionCertificate instruction)
  | .pop => some popCertificate
  | .dup (index + 1) => if valid : index < 16 then some (dupCertificate ⟨index, valid⟩) else none
  | .swap (index + 1) => if valid : index < 16 then some (swapCertificate ⟨index, valid⟩) else none
  | _ => none

namespace V2

/-- DUP preserves every external suffix; one actual extra word must fit. -/
def duplicateFrame (index : Fin 16) (input : Scalar.Stack) (word : Scalar.Word)
    (found : input[index.val]? = some word) (room : input.length + 1 ≤ 1024) :
    FrameCertificate input (word :: input) where
  code := [.op (.DUP index)]
  peak := 1
  inputRoom := room
  frame := by
    intro tail
    have actual : Scalar.run [.op (.DUP index)] input = some (word :: input) := by
      simp only [Scalar.run, Scalar.step, Scalar.duplicate, found,
        Option.map_some, Option.bind_some]
    exact Scalar.run_frame actual tail
  capacity := by
    intro tail admitted
    simp only [Scalar.stackBound, Scalar.heightTrace, Scalar.stackDelta,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      Scalar.safeHeight, decide_eq_true_eq]
    omega

/-- SWAP preserves the frame and has no additional height peak. -/
def exchangeFrame (index : Fin 16) (head : Scalar.Word) (rest : Scalar.Stack)
    (word : Scalar.Word) (found : rest[index.val]? = some word)
    (room : (head :: rest).length ≤ 1024) :
    FrameCertificate (head :: rest) (word :: rest.set index.val head) where
  code := [.op (.SWAP index)]
  peak := 0
  inputRoom := by simpa only [Nat.add_zero] using room
  frame := by
    intro tail
    have actual : Scalar.run [.op (.SWAP index)] (head :: rest) =
        some (word :: rest.set index.val head) := by
      simp only [Scalar.run, Scalar.step, Scalar.swap, exchange_get_set,
        found, Option.map_some, Option.bind_some]
    exact Scalar.run_frame actual tail
  capacity := by
    intro tail admitted
    simp only [Scalar.stackBound, Scalar.heightTrace, Scalar.stackDelta,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      Scalar.safeHeight, decide_eq_true_eq]
    omega

/-- POP consumes only its admitted operand, including at the 1024 boundary. -/
def popFrame (head : Scalar.Word) (rest : Scalar.Stack)
    (room : (head :: rest).length ≤ 1024) : FrameCertificate (head :: rest) rest where
  code := [.op .POP]
  peak := 0
  inputRoom := by simpa only [Nat.add_zero] using room
  frame := by
    intro tail
    have actual : Scalar.run [.op .POP] (head :: rest) = some rest := rfl
    exact Scalar.run_frame actual tail
  capacity := by
    intro tail admitted
    simp only [Scalar.stackBound, Scalar.heightTrace, Scalar.stackDelta,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      Scalar.safeHeight, decide_eq_true_eq, List.length_append, List.length_cons]
    simp only [List.length_append, List.length_cons, Nat.add_zero] at admitted
    omega

/-- Capacity composes at the actual intermediate stack, not just net height. -/
theorem bound_append_of_run (first second : Program) (input middle : Scalar.Stack)
    (actual : Scalar.run first input = some middle)
    (left : Scalar.stackBound first (input.length : Int) = true)
    (right : Scalar.stackBound second (middle.length : Int) = true) :
    Scalar.stackBound (first ++ second) (input.length : Int) = true := by
  induction first generalizing input with
  | nil => cases actual; exact right
  | cons instruction rest ih =>
    cases step : Scalar.step instruction input with
    | none => simp only [Scalar.run, step, Option.bind_none, reduceCtorEq] at actual
    | some reached =>
      simp only [Scalar.run, step, Option.bind_some] at actual
      have height : (reached.length : Int) =
          (input.length : Int) + Scalar.stackDelta instruction := Scalar.step_height step
      simp only [List.cons_append, Scalar.stackBound, Scalar.heightTrace, List.all_cons,
        Bool.and_eq_true] at left ⊢
      refine ⟨left.1, ?_⟩
      rw [← height]
      exact ih reached actual (by rw [height]; exact left.2)

/-- Precise composition of the two declared peaks at the real intermediate height. -/
def compose {input middle output : Scalar.Stack}
    (first : FrameCertificate input middle) (second : FrameCertificate middle output)
    (room : input.length + max first.peak (middle.length + second.peak - input.length) ≤ 1024) :
    FrameCertificate input output where
  code := first.code ++ second.code
  peak := max first.peak (middle.length + second.peak - input.length)
  inputRoom := room
  frame := fun tail => Scalar.run_comp (first.frame tail) (second.frame tail)
  capacity := by
    intro tail admitted
    have first_peak : first.peak ≤
        max first.peak (middle.length + second.peak - input.length) := Nat.le_max_left _ _
    have next_peak : middle.length + second.peak - input.length ≤
        max first.peak (middle.length + second.peak - input.length) := Nat.le_max_right _ _
    have first_room : (input ++ tail).length + first.peak ≤ 1024 := by
      simp only [List.length_append] at admitted ⊢
      omega
    have second_room : (middle ++ tail).length + second.peak ≤ 1024 := by
      simp only [List.length_append] at admitted ⊢
      omega
    exact bound_append_of_run first.code second.code _ _ (first.frame tail)
      (first.capacity tail first_room) (second.capacity tail second_room)

/-- Every supported physical instruction grows by at most one word. -/
theorem delta_le_one (instruction : Instr) : Scalar.stackDelta instruction ≤ 1 := by
  cases instruction with
  | push n bytes => exact Int.le_refl 1
  | op opcode =>
    cases opcode <;> simp only [Scalar.stackDelta, Scalar.numericDelta,
      Scalar.unary, Scalar.binary, Scalar.ternary, Option.isSome_some,
      Option.isSome_none, Bool.false_eq_true, if_true, if_false] <;> omega

/-- A successful program has a conservative extra-word peak of its length. -/
theorem bound_of_run_length (code : Program) (input output : Scalar.Stack)
    (actual : Scalar.run code input = some output)
    (room : input.length + code.length ≤ 1024) :
    Scalar.stackBound code (input.length : Int) = true := by
  induction code generalizing input with
  | nil =>
    simp only [Scalar.stackBound, Scalar.heightTrace, List.all_cons, List.all_nil,
      Bool.and_true, Scalar.safeHeight, decide_eq_true_eq]
    simp only [List.length_nil, Nat.add_zero] at room
    omega
  | cons instruction rest ih =>
    cases step : Scalar.step instruction input with
    | none => simp only [Scalar.run, step, Option.bind_none, reduceCtorEq] at actual
    | some reached =>
      simp only [Scalar.run, step, Option.bind_some] at actual
      have height : (reached.length : Int) =
          (input.length : Int) + Scalar.stackDelta instruction := Scalar.step_height step
      have delta : Scalar.stackDelta instruction ≤ 1 := delta_le_one instruction
      have reached_room : reached.length + rest.length ≤ 1024 := by
        simp only [List.length_cons] at room
        omega
      have bounded : Scalar.stackBound rest (reached.length : Int) = true :=
        ih reached actual reached_room
      simp only [Scalar.stackBound, Scalar.heightTrace, List.all_cons, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · simp only [Scalar.safeHeight, decide_eq_true_eq]
        simp only [List.length_cons] at room
        omega
      · rw [← height]
        exact bounded

/-- Generic successful-slice consumer with an explicit conservative room domain. -/
def ofRun (code : Program) (input output : Scalar.Stack)
    (actual : Scalar.run code input = some output)
    (room : input.length + code.length ≤ 1024) : FrameCertificate input output where
  code := code
  peak := code.length
  inputRoom := room
  frame := Scalar.run_frame actual
  capacity := fun tail admitted =>
    bound_of_run_length code (input ++ tail) (output ++ tail) (Scalar.run_frame actual tail) admitted

end V2

namespace StackControls

def indexed : Scalar.Stack := (List.range 16).map (fun n => BitVec.ofNat 256 (n + 1))

def dup16 : V2.FrameCertificate indexed (16 :: indexed) :=
  V2.duplicateFrame ⟨15, by decide⟩ indexed 16 (by decide) (by decide)

def swap16 : V2.FrameCertificate (0 :: indexed) (16 :: indexed.set 15 0) :=
  V2.exchangeFrame ⟨15, by decide⟩ 0 indexed 16 (by decide) (by decide)

def pop : V2.FrameCertificate [7, 11] [11] := V2.popFrame 7 [11] (by decide)

theorem dup16_tail :
    Scalar.run dup16.code (indexed ++ [23, 41]) = some ((16 :: indexed) ++ [23, 41]) ∧
    Scalar.stackBound dup16.code ((indexed ++ [23, 41]).length : Int) = true := by
  exact ⟨dup16.frame [23, 41], dup16.capacity [23, 41] (by decide)⟩

theorem swap16_tail :
    Scalar.run swap16.code ((0 :: indexed) ++ [23, 41]) =
      some ((16 :: indexed.set 15 0) ++ [23, 41]) ∧
    Scalar.stackBound swap16.code (((0 :: indexed) ++ [23, 41]).length : Int) = true := by
  exact ⟨swap16.frame [23, 41], swap16.capacity [23, 41] (by decide)⟩

theorem pop_tail : Scalar.run pop.code [7, 11, 23, 41] = some [11, 23, 41] ∧
    Scalar.stackBound pop.code 4 = true := by
  exact ⟨pop.frame [23, 41], pop.capacity [23, 41] (by decide)⟩

theorem dup16_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    (Evm.Instr.dup 16).step { m with stack := irStack (indexed ++ tail) } =
      .ok { m with stack := irStack ((16 :: indexed) ++ tail) } 0 := by
  exact ((dupCertificate ⟨15, by decide⟩).success _ _ _ rfl).mpr (dup16.frame tail)

theorem swap16_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    (Evm.Instr.swap 16).step { m with stack := irStack ((0 :: indexed) ++ tail) } =
      .ok { m with stack := irStack ((16 :: indexed.set 15 0) ++ tail) } 0 := by
  exact ((swapCertificate ⟨15, by decide⟩).success _ _ _ rfl).mpr (swap16.frame tail)

theorem pop_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.Instr.pop.step { m with stack := irStack ([7, 11] ++ tail) } =
      .ok { m with stack := irStack ([11] ++ tail) } 0 := by
  exact (popCertificate.success _ _ _ rfl).mpr (pop.frame tail)

theorem empty_refusals (index : Fin 16) :
    Scalar.run (dupCertificate index).code [] = none ∧
    Scalar.run (swapCertificate index).code [] = none ∧
    Scalar.run popCertificate.code [] = none := by exact ⟨rfl, rfl, rfl⟩

theorem deep_shortages (m : Evm.Machine) :
    (Evm.Instr.dup 16).step { m with stack := irStack (List.replicate 15 7) } = .fault ∧
    (Evm.Instr.swap 16).step { m with stack := irStack (List.replicate 16 7) } = .fault := by
  have duplicate : Scalar.run (dupCertificate ⟨15, by decide⟩).code
      (List.replicate 15 7) = none := by decide
  have exchange : Scalar.run (swapCertificate ⟨15, by decide⟩).code
      (List.replicate 16 7) = none := by decide
  exact ⟨((dupCertificate ⟨15, by decide⟩).refusal _ _ rfl).mpr duplicate,
    ((swapCertificate ⟨15, by decide⟩).refusal _ _ rfl).mpr exchange⟩

theorem wrong_duplicate_index :
    Scalar.run dup16.code indexed ≠ some (15 :: indexed) := by decide
theorem wrong_swap_index :
    Scalar.run swap16.code (0 :: indexed) ≠ some (15 :: indexed.set 15 0) := by decide
theorem corrupt_tail :
    Scalar.run dup16.code (indexed ++ [23, 41]) ≠
      some ((16 :: indexed) ++ [23, 42]) := by decide

/-- Index-zero IR refusal is real; it is not the physical zero-based index. -/
theorem zero_indices (m : Evm.Machine) : selectStack (.dup 0) = none ∧
    selectStack (.swap 0) = none ∧ (Evm.Instr.dup 0).step m = .fault ∧
    (Evm.Instr.swap 0).step m = .fault := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · cases stack : m.stack <;> simp only [Evm.Instr.step, stack]
  · cases stack : m.stack <;> simp only [Evm.Instr.step, stack]

/-- A larger IR index can succeed even though this native component refuses it. -/
theorem outside_native (m : Evm.Machine) : selectStack (.dup 17) = none ∧
    (Evm.Instr.dup 17).step { m with stack := irStack (List.replicate 17 7) } =
      .ok { m with stack := irStack (List.replicate 18 7) } 0 := by exact ⟨rfl, rfl⟩

def nearFullDup : V2.FrameCertificate (List.replicate 1023 7)
    (7 :: List.replicate 1023 7) :=
  V2.duplicateFrame 0 _ 7 rfl (by simp only [List.length_replicate]; decide)

def fullPop : V2.FrameCertificate (7 :: List.replicate 1023 7) (List.replicate 1023 7) :=
  V2.popFrame 7 _ (by simp only [List.length_cons, List.length_replicate]; decide)

def fullSwap : V2.FrameCertificate (7 :: List.replicate 1023 7)
    (7 :: (List.replicate 1023 7).set 0 7) :=
  V2.exchangeFrame 0 7 _ 7 rfl (by simp only [List.length_cons, List.length_replicate]; decide)

theorem admitted_boundaries : Scalar.stackBound nearFullDup.code 1023 = true ∧
    Scalar.stackBound fullPop.code 1024 = true ∧ Scalar.stackBound fullSwap.code 1024 = true := by
  constructor
  · simpa only [List.length_replicate] using nearFullDup.capacity_empty
  · constructor
    · simpa only [List.length_cons, List.length_replicate] using fullPop.capacity_empty
    · simpa only [List.length_cons, List.length_replicate] using fullSwap.capacity_empty

theorem no_overfull_duplicate :
    ¬ Nonempty (V2.FrameCertificate (List.replicate 1024 7) (7 :: List.replicate 1024 7)) := by
  apply V2.no_overfull_output
  simp only [List.length_cons, List.length_replicate]
  decide

def duplicateThenPop : V2.FrameCertificate indexed indexed :=
  V2.compose dup16 (V2.popFrame 16 indexed (by decide)) (by decide)

theorem composed_nonempty_tail : duplicateThenPop.peak = 1 ∧
    Scalar.run duplicateThenPop.code (indexed ++ [23, 41]) = some (indexed ++ [23, 41]) ∧
    Scalar.stackBound duplicateThenPop.code ((indexed ++ [23, 41]).length : Int) = true := by
  exact ⟨rfl, duplicateThenPop.frame [23, 41], duplicateThenPop.capacity [23, 41] (by decide)⟩

theorem all_composed_prefixes (before after : Program) (reached : Scalar.Stack)
    (split : before ++ after = duplicateThenPop.code)
    (actual : Scalar.run before (indexed ++ [23, 41]) = some reached) : reached.length ≤ 1024 :=
  duplicateThenPop.prefixes [23, 41] (by decide) before after reached split actual

/-- Final height1024 does not excuse an intermediate height1025. -/
theorem intermediate_overflow : Scalar.stackBound [.op (.DUP 0), .op .POP] 1024 = false := by decide

theorem no_full_duplicate_pop : ¬ ∃ certificate :
    V2.FrameCertificate (List.replicate 1024 7) (List.replicate 1024 7),
    certificate.code = [.op (.DUP 0), .op .POP] := by
  rintro ⟨certificate, code⟩
  have bounded : Scalar.stackBound [.op (.DUP 0), .op .POP] 1024 = true := by
    have bound : Scalar.stackBound certificate.code
        ((List.replicate 1024 (7 : Scalar.Word)).length : Int) = true :=
      certificate.capacity_empty
    rw [code] at bound
    simpa only [List.length_replicate] using bound
  rw [intermediate_overflow] at bounded
  cases bounded

/-- The conservative constructor also consumes the proved numeric compiler result. -/
def numericFrame : V2.FrameCertificate [] [6] :=
  V2.ofRun NumericSequenceControls.sampleCode [] [6]
    (NumericSequenceControls.sample_run []) (by decide)

theorem numeric_nonempty_tail : numericFrame.peak = 5 ∧
    Scalar.run numericFrame.code [23, 41] = some [6, 23, 41] ∧
    Scalar.stackBound numericFrame.code 2 = true := by
  exact ⟨rfl, numericFrame.frame [23, 41], numericFrame.capacity [23, 41] (by decide)⟩

theorem emitted_opcodes : encode (dupCertificate 0).code = [0x80] ∧
    encode (dupCertificate ⟨15, by decide⟩).code = [0x8f] ∧
    encode (swapCertificate 0).code = [0x90] ∧
    encode (swapCertificate ⟨15, by decide⟩).code = [0x9f] ∧
    encode popCertificate.code = [0x50] := by decide

end StackControls

#print axioms StackControls.dup16
#print axioms StackControls.swap16
#print axioms StackControls.pop
#print axioms StackControls.dup16_tail
#print axioms StackControls.swap16_tail
#print axioms StackControls.pop_tail
#print axioms StackControls.dup16_complete_frame
#print axioms StackControls.swap16_complete_frame
#print axioms StackControls.pop_complete_frame
#print axioms StackControls.empty_refusals
#print axioms StackControls.deep_shortages
#print axioms StackControls.wrong_duplicate_index
#print axioms StackControls.wrong_swap_index
#print axioms StackControls.corrupt_tail
#print axioms StackControls.zero_indices
#print axioms StackControls.outside_native
#print axioms StackControls.admitted_boundaries
#print axioms StackControls.no_overfull_duplicate
#print axioms StackControls.duplicateThenPop
#print axioms StackControls.composed_nonempty_tail
#print axioms StackControls.all_composed_prefixes
#print axioms StackControls.intermediate_overflow
#print axioms StackControls.no_full_duplicate_pop
#print axioms StackControls.numericFrame
#print axioms StackControls.numeric_nonempty_tail
#print axioms StackControls.emitted_opcodes
#print axioms V2.bound_append_of_run
#print axioms V2.compose
#print axioms V2.delta_le_one
#print axioms V2.bound_of_run_length
#print axioms V2.ofRun
#print axioms exchange_get_set
#print axioms popCertificate
#print axioms dupCertificate
#print axioms swapCertificate
#print axioms V2.duplicateFrame
#print axioms V2.exchangeFrame
#print axioms V2.popFrame

end Solidity.Backend.Selection
