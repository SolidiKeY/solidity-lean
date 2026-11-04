import Solidity.Backend.Selection.SignedSelection

/-! Numeric compiler-IR selection and straight-line composition use the existing
instruction and lowering certificates. No source evaluator is introduced. -/
namespace Solidity.Backend.Selection

/-- Unified numeric component over the existing intrinsic IR constructors. -/
def selectNumeric : (instruction : Evm.Instr) → Option (InstructionCertificate instruction)
  | .push (.val value) => some (literalCertificate value)
  | .add => some addCertificate
  | .sub => some subCertificate
  | .mul => some mulCertificate
  | .div => some divCertificate
  | .mod => some modCertificate
  | .lt => some ltCertificate
  | .gt => some gtCertificate
  | .eq => some eqCertificate
  | .iszero => some iszeroCertificate
  | .or => some orCertificate
  | .and => some andCertificate
  | .slt => some sltCertificate
  | .sgt => some sgtCertificate
  | .sdiv => some sdivCertificate
  | .smod => some smodCertificate
  | .xor => some xorCertificate
  | .not => some notCertificate
  | .shl => some shlCertificate
  | .shr => some shrCertificate
  | .exp => some expCertificate
  | _ => none

/-- Exactly this component's supported IR cases, not a source refusal predicate. -/
def numericSupported : Evm.Instr → Bool
  | .push (.val _) => true
  | .add | .sub | .mul | .div | .mod | .lt | .gt | .eq | .iszero | .or | .and
  | .slt | .sgt | .sdiv | .smod | .xor | .not | .shl | .shr | .exp => true
  | _ => false

theorem selectNumeric_complete (instruction : Evm.Instr) :
    (selectNumeric instruction).isSome = numericSupported instruction := by
  cases instruction <;> try rfl
  case push word => cases word <;> rfl

/-- The existing two-sided certificate implies a total equation of actual steps. -/
theorem instruction_equation (instruction : Evm.Instr)
    (certificate : InstructionCertificate instruction) (input : Scalar.Stack)
    (m : Evm.Machine) (stack : m.stack = irStack input) :
    instruction.step m = match Scalar.run certificate.code input with
      | none => .fault
      | some output => .ok { m with stack := irStack output } 0 := by
  cases actual : Scalar.run certificate.code input with
  | none => exact (certificate.refusal input m stack).mpr actual
  | some output => exact (certificate.success input output m stack).mpr actual

/-- Flatten actual selected expansions in IR order. None means outside this
numeric component, independently of whether the IR itself faults or reverts. -/
def compileNumeric : List Evm.Instr → Option Program
  | [] => some []
  | instruction :: rest => (selectNumeric instruction).bind (fun certificate =>
      (compileNumeric rest).map (fun code => certificate.code ++ code))

/-- Whole actual IR execution, including early and late operand faults. -/
theorem compileNumeric_equation (ir : List Evm.Instr) (code : Program)
    (selected : compileNumeric ir = some code) (input : Scalar.Stack)
    (m : Evm.Machine) (stack : m.stack = irStack input) :
    Evm.run ir m = match Scalar.run code input with
      | none => .fault
      | some output => .ok { m with stack := irStack output } 0 := by
  induction ir generalizing code input m with
  | nil =>
    simp only [compileNumeric, Option.some.injEq] at selected
    subst code
    simp only [Evm.run, Evm.exec_nil, Scalar.run, ← stack]
  | cons instruction rest ih =>
    cases first : selectNumeric instruction with
    | none => simp only [compileNumeric, first, Option.bind_none, reduceCtorEq] at selected
    | some certificate =>
      cases next : compileNumeric rest with
      | none =>
        simp only [compileNumeric, first, next, Option.bind_some,
          Option.map_none, reduceCtorEq] at selected
      | some tailCode =>
        have codes : certificate.code ++ tailCode = code := by
          simpa only [compileNumeric, first, next, Option.bind_some,
            Option.map_some, Option.some.injEq] using selected
        subst code
        rw [Scalar.run_append]
        simp only [Evm.run, Evm.exec_cons_zero]
        rw [instruction_equation instruction certificate input m stack]
        cases actual : Scalar.run certificate.code input with
        | none => rfl
        | some middle =>
          simpa only [Evm.run, Evm.Out.bind, Option.bind_some] using
            ih tailCode next middle { m with stack := irStack middle } rfl

/-- The existing code-case execution specification is exactly Scalar.run. -/
theorem structured_code_iff (code : Program) (input output : Scalar.Stack) :
    StructuredExec (.code code) input output ↔ Scalar.run code input = some output := by
  constructor
  · intro execution
    cases execution with
    | code actual => exact actual
  · exact StructuredExec.code

/-- Selected numeric sequences inhabit the existing lowering contract. -/
def numericLowering (ir : List Evm.Instr) (code : Program)
    (selected : compileNumeric ir = some code) : LoweringCertificate ir (.code code) where
  success := by
    intro input output m stack
    rw [structured_code_iff, compileNumeric_equation ir code selected input m stack]
    cases actual : Scalar.run code input with
    | none => simp only [reduceCtorEq]
    | some reached =>
      simpa only [Evm.Out.ok.injEq, and_true, Option.some.injEq] using
        stack_update_eq m reached output

theorem selected_fault_iff (ir : List Evm.Instr) (code : Program)
    (selected : compileNumeric ir = some code) (input : Scalar.Stack)
    (m : Evm.Machine) (stack : m.stack = irStack input) :
    Evm.run ir m = .fault ↔ Scalar.run code input = none := by
  rw [compileNumeric_equation ir code selected input m stack]
  cases actual : Scalar.run code input with
  | none => simp only
  | some output => simp only [reduceCtorEq]

namespace NumericSequenceControls

def sampleIR : List Evm.Instr :=
  [.push (.val (Evm.wmod 5)), .push (.val (Evm.wmod 17)), .div,
   .push (.val (Evm.wmod 3)), .add]
def sampleCode : Program :=
  [Scalar.pushWord 5, Scalar.pushWord 17, .op .DIV, Scalar.pushWord 3, .op .ADD]

theorem sample_selected : compileNumeric sampleIR = some sampleCode := rfl

def sample_lowering : LoweringCertificate sampleIR (.code sampleCode) :=
  numericLowering sampleIR sampleCode sample_selected

theorem sample_run (tail : Scalar.Stack) :
    Scalar.run sampleCode tail = some (6 :: tail) := by
  have actual : Scalar.run sampleCode [] = some [6] := by decide
  exact Scalar.run_frame actual tail

theorem sample_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.run sampleIR { m with stack := irStack tail } =
      .ok { m with stack := irStack (6 :: tail) } 0 := by
  rw [compileNumeric_equation sampleIR sampleCode sample_selected tail
    { m with stack := irStack tail } rfl, sample_run tail]

theorem sample_size : size sampleCode = 101 := by decide

theorem wrong_order_result : Scalar.run sampleCode [23] ≠ some [3, 23] := by decide
theorem corrupt_tail : Scalar.run sampleCode [23] ≠ some [6, 24] := by decide

def earlyIR : List Evm.Instr := [.div, .push (.val (Evm.wmod 17))]
def earlyCode : Program := [.op .DIV, Scalar.pushWord 17]
def lateIR : List Evm.Instr := [.push (.val (Evm.wmod 17)), .div]
def lateCode : Program := [Scalar.pushWord 17, .op .DIV]

theorem early_selected : compileNumeric earlyIR = some earlyCode := rfl
theorem late_selected : compileNumeric lateIR = some lateCode := rfl

theorem early_fault (m : Evm.Machine) :
    Evm.run earlyIR { m with stack := [] } = .fault := by
  exact (selected_fault_iff earlyIR earlyCode early_selected []
    { m with stack := [] } rfl).mpr rfl

theorem late_fault (m : Evm.Machine) :
    Evm.run lateIR { m with stack := [] } = .fault := by
  have actual : Scalar.run lateCode [] = none := by decide
  exact (selected_fault_iff lateIR lateCode late_selected []
    { m with stack := [] } rfl).mpr actual

/-- Component refusal is distinct from actual IR revert observation. -/
theorem unsupported_revert (m : Evm.Machine) :
    compileNumeric [.revert] = none ∧ Evm.run [.revert] m = .revert := by
  exact ⟨rfl, rfl⟩

end NumericSequenceControls

#print axioms NumericSequenceControls.sample_selected
#print axioms NumericSequenceControls.sample_lowering
#print axioms NumericSequenceControls.sample_run
#print axioms NumericSequenceControls.sample_complete_frame
#print axioms NumericSequenceControls.sample_size
#print axioms NumericSequenceControls.wrong_order_result
#print axioms NumericSequenceControls.corrupt_tail
#print axioms NumericSequenceControls.early_selected
#print axioms NumericSequenceControls.late_selected
#print axioms NumericSequenceControls.early_fault
#print axioms NumericSequenceControls.late_fault
#print axioms NumericSequenceControls.unsupported_revert
#print axioms selectNumeric_complete
#print axioms instruction_equation
#print axioms compileNumeric_equation
#print axioms structured_code_iff
#print axioms numericLowering
#print axioms selected_fault_iff

end Solidity.Backend.Selection
