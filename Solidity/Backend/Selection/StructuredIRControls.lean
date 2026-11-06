import Solidity.Backend.Selection.StructuredIRComposition
import Solidity.Backend.Selection.LoopControls

/-! Concrete closed IR-to-byte compositions, including recursive loops and both
relative-branch arms. Raw finite IR witnesses independently check the producers. -/
namespace Solidity.Backend.Selection.StructuredIRControls

open LabelExec

abbrev conditionCode : Code 2 3 := ExecutionTrace.LoopControls.condition

def conditionIR : List Evm.Instr := [.dup 1]
def decrementIR : List Evm.Instr := [.push (.val (Evm.wmod 1)), .swap 1, .sub]
def elseIR : List Evm.Instr := [.pop, .push (.val (Evm.wmod 99))]

def decrementCode : Code 2 2 where
  instructions := [Scalar.pushWord 1, .op (.SWAP 0), .op .SUB]
  shape := .cons (.mk 0 1 2 rfl rfl rfl)
    (.cons (.mk 2 2 1 rfl rfl rfl) (.cons (.mk 2 1 1 rfl rfl rfl) (.nil 2)))
  capacity := by decide

def elseCode : Code 2 2 where
  instructions := [.op .POP, Scalar.pushWord 99]
  shape := .cons (.mk 1 0 1 rfl rfl rfl) (.cons (.mk 0 1 1 rfl rfl rfl) (.nil 2))
  capacity := by decide

def condition : FramedLoweringCertificate conditionIR (.code conditionCode.instructions) :=
  .scalar conditionIR conditionCode.instructions rfl

def decrement : FramedLoweringCertificate decrementIR (.code decrementCode.instructions) :=
  .scalar decrementIR decrementCode.instructions rfl

def alternative : FramedLoweringCertificate elseIR (.code elseCode.instructions) :=
  .scalar elseIR elseCode.instructions rfl

def bodyIR : List Evm.Instr := IRBranch.emit conditionIR decrementIR elseIR
def bodyBlock : Block := .ite conditionCode.instructions (.code decrementCode.instructions) (.code elseCode.instructions)
def body : FramedLoweringCertificate bodyIR bodyBlock := .branch condition decrement alternative

def innerIR : List Evm.Instr := [.loop conditionIR bodyIR]
def innerBlock : Block := .loop conditionCode.instructions bodyBlock
def inner : FramedLoweringCertificate innerIR innerBlock := .loop condition body

def nestedIR : List Evm.Instr := [.loop conditionIR innerIR]
def nestedBlock : Block := .loop conditionCode.instructions innerBlock
def nested : FramedLoweringCertificate nestedIR nestedBlock := .loop condition inner

def bodyControl : ControlCertificate bodyBlock 2 2 :=
  ExecutionTrace.iteCertificate conditionCode (ExecutionTrace.codeCertificate decrementCode)
    (ExecutionTrace.codeCertificate elseCode) (by decide) (by decide)
def innerControl : ControlCertificate innerBlock 2 2 :=
  ExecutionTrace.loopCertificate conditionCode bodyControl (by decide)
def nestedControl : ControlCertificate nestedBlock 2 2 :=
  ExecutionTrace.loopCertificate conditionCode innerControl (by decide)

theorem condition_two (initial : Evm.Machine) :
    Evm.run conditionIR { initial with stack := irStack [2,23] } =
      .ok { initial with stack := irStack [2,2,23] } 0 :=
  (condition.success [2,23] [2,2,23] { initial with stack := irStack [2,23] } rfl).mpr (.code rfl)

theorem condition_one (initial : Evm.Machine) :
    Evm.run conditionIR { initial with stack := irStack [1,23] } =
      .ok { initial with stack := irStack [1,1,23] } 0 :=
  (condition.success [1,23] [1,1,23] { initial with stack := irStack [1,23] } rfl).mpr (.code rfl)

theorem condition_zero (initial : Evm.Machine) :
    Evm.run conditionIR { initial with stack := irStack [0,23] } =
      .ok { initial with stack := irStack [0,0,23] } 0 :=
  (condition.success [0,23] [0,0,23] { initial with stack := irStack [0,23] } rfl).mpr (.code rfl)

theorem decrement_two (initial : Evm.Machine) :
    Evm.run decrementIR { initial with stack := irStack [2,23] } =
      .ok { initial with stack := irStack [1,23] } 0 :=
  (decrement.success [2,23] [1,23] { initial with stack := irStack [2,23] } rfl).mpr (.code (by decide))

theorem decrement_one (initial : Evm.Machine) :
    Evm.run decrementIR { initial with stack := irStack [1,23] } =
      .ok { initial with stack := irStack [0,23] } 0 :=
  (decrement.success [1,23] [0,23] { initial with stack := irStack [1,23] } rfl).mpr (.code (by decide))

theorem body_actual_two (initial : Evm.Machine) :
    Evm.run bodyIR { initial with stack := irStack [2,23] } =
      .ok { initial with stack := irStack [1,23] } 0 := by
  change Evm.run (IRBranch.emit conditionIR decrementIR elseIR) _ = _
  rw [IRBranch.run (condition_two initial)]
  simp only [show ((2 : Scalar.Word) == 0) = false from rfl, Bool.false_eq_true,
    if_false, decrement_two initial, Evm.Out.ok_bind, IRBranch.join_normal]

theorem body_actual_one (initial : Evm.Machine) :
    Evm.run bodyIR { initial with stack := irStack [1,23] } =
      .ok { initial with stack := irStack [0,23] } 0 := by
  change Evm.run (IRBranch.emit conditionIR decrementIR elseIR) _ = _
  rw [IRBranch.run (condition_one initial)]
  simp only [show ((1 : Scalar.Word) == 0) = false from rfl, Bool.false_eq_true,
    if_false, decrement_one initial, Evm.Out.ok_bind, IRBranch.join_normal]

/-- Compose actual IR turn equations while keeping the interpreter functions
abstract in the finite-iterator proof. No whole-loop lowering is used here. -/
theorem inner_turns (initial : Evm.Machine) :
    Evm.loopIterN (Evm.run conditionIR) (Evm.run bodyIR) 3
      { initial with stack := irStack [2,23] } = .inr (.ok { initial with stack := irStack [0,23] } 0) := by
  exact IRLoop.iter_three (Evm.run conditionIR) (Evm.run bodyIR)
    { initial with stack := irStack [2,23] } { initial with stack := irStack [1,23] }
    { initial with stack := irStack [0,23] } (.ok { initial with stack := irStack [0,23] } 0)
    (IRLoop.turn_continue (Evm.run conditionIR) (Evm.run bodyIR)
      { initial with stack := irStack [2,23] } { initial with stack := irStack [1,23] }
      2 [2,23] (by decide) (condition_two initial) (body_actual_two initial))
    (IRLoop.turn_continue (Evm.run conditionIR) (Evm.run bodyIR)
      { initial with stack := irStack [1,23] } { initial with stack := irStack [0,23] }
      1 [1,23] (by decide) (condition_one initial) (body_actual_one initial))
    (IRLoop.turn_done (Evm.run conditionIR) (Evm.run bodyIR)
      { initial with stack := irStack [0,23] } [0,23] (condition_zero initial))

theorem inner_actual (initial : Evm.Machine) :
    Evm.run innerIR { initial with stack := irStack [2,23] } =
      .ok { initial with stack := irStack [0,23] } 0 := by
  exact (IRLoop.single_run conditionIR bodyIR { initial with stack := irStack [2,23] }).trans
    (Evm.loopRun_of_iterN (inner_turns initial))

/-- The outer body is itself an actual recursive IR loop, not a flat surrogate. -/
theorem outer_turns (initial : Evm.Machine) :
    Evm.loopIterN (Evm.run conditionIR) (Evm.run innerIR) 2
      { initial with stack := irStack [2,23] } = .inr (.ok { initial with stack := irStack [0,23] } 0) := by
  exact IRLoop.iter_two (Evm.run conditionIR) (Evm.run innerIR)
    { initial with stack := irStack [2,23] } { initial with stack := irStack [0,23] }
    (.ok { initial with stack := irStack [0,23] } 0)
    (IRLoop.turn_continue (Evm.run conditionIR) (Evm.run innerIR)
      { initial with stack := irStack [2,23] } { initial with stack := irStack [0,23] }
      2 [2,23] (by decide) (condition_two initial) (inner_actual initial))
    (IRLoop.turn_done (Evm.run conditionIR) (Evm.run innerIR)
      { initial with stack := irStack [0,23] } [0,23] (condition_zero initial))

theorem nested_actual (initial : Evm.Machine) :
    Evm.run nestedIR { initial with stack := irStack [2,23] } =
      .ok { initial with stack := irStack [0,23] } 0 := by
  exact (IRLoop.single_run conditionIR innerIR { initial with stack := irStack [2,23] }).trans
    (Evm.loopRun_of_iterN (outer_turns initial))

theorem body_two_one : StructuredExec bodyBlock [2,23] [1,23] :=
  .iteTrue (show Scalar.run conditionCode.instructions [2,23] = some [2,2,23] from rfl)
    (by decide) (.code (by decide))
theorem body_one_zero : StructuredExec bodyBlock [1,23] [0,23] :=
  .iteTrue (show Scalar.run conditionCode.instructions [1,23] = some [1,1,23] from rfl)
    (by decide) (.code (by decide))
theorem inner_reference : StructuredExec innerBlock [2,23] [0,23] :=
  .loopMore (show Scalar.run conditionCode.instructions [2,23] = some [2,2,23] from rfl)
    (by decide) body_two_one
    (.loopMore (show Scalar.run conditionCode.instructions [1,23] = some [1,1,23] from rfl)
      (by decide) body_one_zero (.loopDone rfl))
theorem nested_reference : StructuredExec nestedBlock [2,23] [0,23] :=
  .loopMore (show Scalar.run conditionCode.instructions [2,23] = some [2,2,23] from rfl)
    (by decide) inner_reference (.loopDone rfl)

theorem nested_forward (initial : Evm.Machine) :
    Evm.run nestedIR { initial with stack := irStack [2,23] } =
      .ok { initial with stack := irStack [0,23] } 0 :=
  (nested.success [2,23] [0,23] { initial with stack := irStack [2,23] } rfl).mpr nested_reference

theorem nested_fits : ∀ label ∈ refs (nestedBlock.expand 0).1,
    0 + tagOffset (fun _ => (32 : Fin 33)) (nestedBlock.expand 0).1 label < 256 ^ 32 := by
  intro label member
  have onlyRef : label = 1 ∨ label = 3 ∨ label = 4 ∨ label = 5 ∨ label = 2 ∨ label = 0 := by
    simpa only [show refs (nestedBlock.expand 0).1 = [1,3,4,5,2,0] from rfl,
      List.mem_cons, List.not_mem_nil, or_false] using member
  rcases onlyRef with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def artifact : Option (CompositionCertificate nestedIR nestedBlock 2 2) :=
  assembleComposition nested nestedControl.shape nestedControl.room

theorem artifact_exists : ∃ composition, artifact = some composition :=
  Option.isSome_iff_exists.mp (assembleComposition_isSome nested nestedControl.shape nestedControl.room nested_fits)

/-- Closed recursive IR lowering is composed with actual assembly and byte
execution; no whole-IR correspondence is supplied as a premise. -/
theorem nested_bytes (initial : Evm.Machine) :
    ∃ composition, artifact = some composition ∧
      ∃ count, ExecutionTrace.Safe (encode composition.assembled.code) count ⟨0,[2,23]⟩
        ⟨size composition.assembled.code,[0,23]⟩ := by
  obtain ⟨composition,selected⟩ := artifact_exists
  obtain ⟨count,trace⟩ := composition.execute [2,23] [0,23]
    { initial with stack := irStack [2,23] } rfl rfl (nested_actual initial)
  exact ⟨composition,selected,count,trace⟩

/-- Both wrong output and damaged protected tail disagree with the same actual run. -/
theorem nested_negatives : ∃ composition, artifact = some composition ∧
    ∃ count, advance count (encode composition.assembled.code) ⟨0,[2,23]⟩ =
        some ⟨size composition.assembled.code,[0,23]⟩ ∧
      advance count (encode composition.assembled.code) ⟨0,[2,23]⟩ ≠
        some ⟨size composition.assembled.code,[1,23]⟩ ∧
      advance count (encode composition.assembled.code) ⟨0,[2,23]⟩ ≠
        some ⟨size composition.assembled.code,[0,24]⟩ := by
  obtain ⟨composition,selected,count,trace⟩ := nested_bytes Evm.Machine.init
  refine ⟨composition,selected,count,trace.1,?_,?_⟩
  · rw [trace.1]
    intro equal
    have stacks : ([0,23] : Scalar.Stack) = [1,23] := congrArg LabelExec.State.stack (Option.some.inj equal)
    exact (by decide : ([0,23] : Scalar.Stack) ≠ [1,23]) stacks
  · rw [trace.1]
    intro equal
    have stacks : ([0,23] : Scalar.Stack) = [0,24] := congrArg LabelExec.State.stack (Option.some.inj equal)
    exact (by decide : ([0,23] : Scalar.Stack) ≠ [0,24]) stacks

theorem branch_false_actual (initial : Evm.Machine) :
    Evm.run bodyIR { initial with stack := irStack [0,23] } =
      .ok { initial with stack := irStack [99,23] } 0 := by
  have tested : Evm.run conditionIR { initial with stack := irStack [0,23] } =
      .ok (({ initial with stack := irStack [0,23] } : Evm.Machine).push (.val (Evm.bword false))) 0 :=
    condition_zero initial
  change Evm.run (StructuredFlow.Branch.emit conditionIR decrementIR elseIR) _ = _
  rw [StructuredFlow.Branch.false_run tested]
  exact (alternative.success [0,23] [99,23] { initial with stack := irStack [0,23] } rfl).mpr (.code (by decide))

def wrongDistanceIR : List Evm.Instr :=
  conditionIR ++ ([.iszero, .jumpi 3] ++ (decrementIR ++ ([.jump 2] ++ elseIR)))

theorem wrong_distance_actual (initial : Evm.Machine) :
    Evm.run wrongDistanceIR { initial with stack := irStack [0,23] } =
      .ok { initial with stack := irStack [0,23] } 0 := by
  change Evm.run (conditionIR ++ ([.iszero, .jumpi 3] ++ (decrementIR ++ ([.jump 2] ++ elseIR)))) _ = _
  rw [Evm.run_append_ok (condition_zero initial),
    Evm.run_append_skip (IRBranch.test_run 3 0 [0,23] initial)]
  change Evm.exec (decrementIR ++ ([.jump 2] ++ elseIR)) (decrementIR.length + 0)
    { initial with stack := irStack [0,23] } = .ok { initial with stack := irStack [0,23] } 0
  calc
    Evm.exec (decrementIR ++ ([.jump 2] ++ elseIR)) (decrementIR.length + 0)
        { initial with stack := irStack [0,23] } =
      Evm.exec ([.jump 2] ++ elseIR) 0 { initial with stack := irStack [0,23] } :=
        Evm.exec_skip_append decrementIR ([.jump 2] ++ elseIR) 0 _
    _ = .ok { initial with stack := irStack [0,23] } 0 := IRBranch.join_normal elseIR _

theorem relative_distance_discriminates (initial : Evm.Machine) :
    Evm.run bodyIR { initial with stack := irStack [0,23] } ≠
      Evm.run wrongDistanceIR { initial with stack := irStack [0,23] } := by
  rw [branch_false_actual,wrong_distance_actual]
  intro equal
  have frames : { initial with stack := irStack [99,23] } = { initial with stack := irStack [0,23] } :=
    (Evm.Out.ok.inj equal).1
  have values : ([99,23] : Scalar.Stack) = [0,23] := (stack_update_eq _ _ _).mp frames
  exact (by decide : ([99,23] : Scalar.Stack) ≠ [0,23]) values

theorem body_fits : ∀ label ∈ refs (bodyBlock.expand 0).1,
    0 + tagOffset (fun _ => (32 : Fin 33)) (bodyBlock.expand 0).1 label < 256 ^ 32 := by
  intro label member
  have onlyRef : label = 0 ∨ label = 1 := by
    simpa only [show refs (bodyBlock.expand 0).1 = [0,1] from rfl,
      List.mem_cons, List.not_mem_nil, or_false] using member
  rcases onlyRef with rfl | rfl <;> decide

theorem branch_false_bytes (initial : Evm.Machine) :
    ∃ composition, assembleComposition body bodyControl.shape bodyControl.room = some composition ∧
      ∃ count, ExecutionTrace.Safe (encode composition.assembled.code) count ⟨0,[0,23]⟩
        ⟨size composition.assembled.code,[99,23]⟩ := by
  obtain ⟨composition,selected⟩ := Option.isSome_iff_exists.mp
    (assembleComposition_isSome body bodyControl.shape bodyControl.room body_fits)
  obtain ⟨count,trace⟩ := composition.execute [0,23] [99,23]
    { initial with stack := irStack [0,23] } rfl rfl (branch_false_actual initial)
  exact ⟨composition,selected,count,trace⟩

def sequence : FramedLoweringCertificate
    ([.push (.val (Evm.wmod 5))] ++ [.pop])
    (.seq (.code [Scalar.pushWord 5]) (.code [.op .POP])) :=
  .seq (.scalar [.push (.val (Evm.wmod 5))] [Scalar.pushWord 5] rfl)
    (.scalar [.pop] [.op .POP] rfl)

/-- The sequence producer reflects an independent old scalar-runner result
through its actual temporary stack and restores the caller's protected word. -/
theorem sequence_reflection (initial : Evm.Machine) :
    StructuredExec (.seq (.code [Scalar.pushWord 5]) (.code [.op .POP])) [23] [23] := by
  have actual : Evm.run ([.push (.val (Evm.wmod 5))] ++ [.pop])
      { initial with stack := irStack [23] } = .ok { initial with stack := irStack [23] } 0 :=
    (scalarLowering [.push (.val (Evm.wmod 5)), .pop] [Scalar.pushWord 5, .op .POP] rfl).success
      [23] [23] { initial with stack := irStack [23] } rfl |>.mpr (.code (by decide))
  exact (sequence.success [23] [23] { initial with stack := irStack [23] } rfl).mp actual

#print axioms sequence
#print axioms sequence_reflection

/-- The stronger contract refuses a genuinely escaping successful skip. -/
theorem escaping_skip_rejected (block : Block) :
    ¬ FramedLoweringCertificate [.jump 17] block := by
  intro certificate
  have actual : Evm.run [.jump 17] Evm.Machine.init = .ok Evm.Machine.init 17 := rfl
  obtain ⟨output,zero,frame,structured⟩ := certificate.reflect [] Evm.Machine.init Evm.Machine.init 17 rfl actual
  omega

/-- A selected leaf still faults on missing operands; it is not called a return. -/
theorem underflow_preserved : Evm.run [.pop] Evm.Machine.init = .fault ∧
    ∀ output : Scalar.Stack, ¬ StructuredExec (.code [.op .POP]) [] output := by
  constructor
  · rfl
  · intro output actual
    cases actual with
    | code run => cases run

#print axioms condition
#print axioms body
#print axioms inner
#print axioms nested
#print axioms inner_turns
#print axioms outer_turns
#print axioms nested_actual
#print axioms nested_forward
#print axioms artifact_exists
#print axioms nested_bytes
#print axioms nested_negatives
#print axioms branch_false_actual
#print axioms wrong_distance_actual
#print axioms relative_distance_discriminates
#print axioms branch_false_bytes
#print axioms escaping_skip_rejected
#print axioms underflow_preserved

end Solidity.Backend.Selection.StructuredIRControls
