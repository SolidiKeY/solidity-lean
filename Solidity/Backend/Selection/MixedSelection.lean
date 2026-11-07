import Solidity.Backend.Selection.StackSelection

/-! Mixed numeric/native-stack sequences specialize the existing common
certificate compiler; no second lowering framework or evaluator is introduced. -/
namespace Solidity.Backend.Selection

/-- Numeric priority retains the existing numeric choice; native stack is fallback. -/
def selectScalar (instruction : Evm.Instr) : Option (InstructionCertificate instruction) :=
  (selectNumeric instruction).orElse (fun _ => selectStack instruction)

theorem selectScalar_numeric (instruction : Evm.Instr)
    (certificate : InstructionCertificate instruction)
    (selected : selectNumeric instruction = some certificate) :
    selectScalar instruction = some certificate := by
  rw [selectScalar, selected]
  rfl

theorem selectScalar_pop : selectScalar .pop = some popCertificate := rfl

theorem selectScalar_dup (index : Fin 16) :
    selectScalar (.dup (index.val + 1)) = some (dupCertificate index) := by
  change (if valid : index.val < 16 then
    (some (dupCertificate ⟨index.val, valid⟩) :
      Option (InstructionCertificate (.dup (index.val + 1)))) else none) = _
  rw [dif_pos index.isLt]

theorem selectScalar_swap (index : Fin 16) :
    selectScalar (.swap (index.val + 1)) = some (swapCertificate index) := by
  change (if valid : index.val < 16 then
    (some (swapCertificate ⟨index.val, valid⟩) :
      Option (InstructionCertificate (.swap (index.val + 1)))) else none) = _
  rw [dif_pos index.isLt]

def compileScalar : List Evm.Instr → Option Program := compileWith selectScalar

/-- Every previously selected numeric program retains the exact same code. -/
theorem numeric_code_preserved (ir : List Evm.Instr) (code : Program)
    (selected : compileNumeric ir = some code) : compileScalar ir = some code := by
  induction ir generalizing code with
  | nil =>
    simp only [compileNumeric, compileWith, Option.some.injEq] at selected
    subst code
    rfl
  | cons instruction rest ih =>
    cases first : selectNumeric instruction with
    | none => simp only [compileNumeric, compileWith, first, Option.bind_none, reduceCtorEq] at selected
    | some certificate =>
      cases next : compileWith selectNumeric rest with
      | none =>
        simp only [compileNumeric, compileWith, first, next, Option.bind_some,
          Option.map_none, reduceCtorEq] at selected
      | some tailCode =>
        have codes : certificate.code ++ tailCode = code := by
          simpa only [compileNumeric, compileWith, first, next, Option.bind_some,
            Option.map_some, Option.some.injEq] using selected
        subst code
        have extended : selectScalar instruction = some certificate :=
          selectScalar_numeric instruction certificate first
        have tail : compileWith selectScalar rest = some tailCode := ih tailCode next
        simp only [compileScalar, compileWith, extended, tail, Option.bind_some, Option.map_some]

theorem compileScalar_equation (ir : List Evm.Instr) (code : Program)
    (selected : compileScalar ir = some code) (input : Scalar.Stack)
    (m : Evm.Machine) (stack : m.stack = irStack input) :
    Evm.run ir m = match Scalar.run code input with
      | none => .fault
      | some output => .ok { m with stack := irStack output } 0 :=
  compileWith_equation selectScalar ir code selected input m stack

def scalarLowering (ir : List Evm.Instr) (code : Program)
    (selected : compileScalar ir = some code) : LoweringCertificate ir (.code code) :=
  loweringWith selectScalar ir code selected

theorem scalar_fault_iff (ir : List Evm.Instr) (code : Program)
    (selected : compileScalar ir = some code) (input : Scalar.Stack)
    (m : Evm.Machine) (stack : m.stack = irStack input) :
    Evm.run ir m = .fault ↔ Scalar.run code input = none :=
  compileWith_fault_iff selectScalar ir code selected input m stack

namespace MixedControls

def sampleIR : List Evm.Instr :=
  [.push (.val (Evm.wmod 5)), .push (.val (Evm.wmod 17)), .dup 2, .swap 1, .div, .pop]
def sampleCode : Program :=
  [Scalar.pushWord 5, Scalar.pushWord 17, .op (.DUP 1), .op (.SWAP 0), .op .DIV, .op .POP]

theorem sample_selected : compileScalar sampleIR = some sampleCode := rfl

def sample_lowering : LoweringCertificate sampleIR (.code sampleCode) :=
  scalarLowering sampleIR sampleCode sample_selected

theorem sample_run (tail : Scalar.Stack) : Scalar.run sampleCode tail = some (5 :: tail) := by
  have actual : Scalar.run sampleCode [] = some [5] := by decide
  exact Scalar.run_frame actual tail

theorem sample_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.run sampleIR { m with stack := irStack tail } =
      .ok { m with stack := irStack (5 :: tail) } 0 := by
  rw [compileScalar_equation sampleIR sampleCode sample_selected tail
    { m with stack := irStack tail } rfl, sample_run tail]

def sample_frame : V2.FrameCertificate [] [5] :=
  V2.ofRun sampleCode [] [5] (sample_run []) (by decide)

theorem sample_capacity : sample_frame.peak = 6 ∧
    Scalar.run sample_frame.code [23, 41] = some [5, 23, 41] ∧
    Scalar.stackBound sample_frame.code 2 = true := by
  exact ⟨rfl, sample_frame.frame [23, 41], sample_frame.capacity [23, 41] (by decide)⟩

theorem sample_prefixes (before after : Program) (reached : Scalar.Stack)
    (split : before ++ after = sample_frame.code)
    (actual : Scalar.run before [23, 41] = some reached) : reached.length ≤ 1024 :=
  sample_frame.prefixes [23, 41] (by decide) before after reached split actual

theorem sample_size : size sampleCode = 70 := by decide

theorem wrong_result : Scalar.run sampleCode [23] ≠ some [3, 23] := by decide
theorem corrupt_tail : Scalar.run sampleCode [23, 41] ≠ some [5, 23, 42] := by decide

/-- Observe DIV before POP erases it, so native operand/order errors remain visible. -/
def boundaryIR : List Evm.Instr :=
  [.push (.val (Evm.wmod 5)), .push (.val (Evm.wmod 17)), .dup 2, .swap 1, .div]
def boundaryCode : Program :=
  [Scalar.pushWord 5, Scalar.pushWord 17, .op (.DUP 1), .op (.SWAP 0), .op .DIV]

theorem actual_boundary : boundaryIR ++ [.pop] = sampleIR ∧
    boundaryCode ++ [.op .POP] = sampleCode := by exact ⟨rfl, rfl⟩

theorem boundary_selected : compileScalar boundaryIR = some boundaryCode := rfl

theorem boundary_run (tail : Scalar.Stack) :
    Scalar.run boundaryCode tail = some (3 :: 5 :: tail) := by
  have actual : Scalar.run boundaryCode [] = some [3, 5] := by decide
  exact Scalar.run_frame actual tail

theorem boundary_complete_frame (m : Evm.Machine) (tail : Scalar.Stack) :
    Evm.run boundaryIR { m with stack := irStack tail } =
      .ok { m with stack := irStack (3 :: 5 :: tail) } 0 := by
  rw [compileScalar_equation boundaryIR boundaryCode boundary_selected tail
    { m with stack := irStack tail } rfl, boundary_run tail]

def wrongDupCode : Program :=
  [Scalar.pushWord 5, Scalar.pushWord 17, .op (.DUP 0), .op (.SWAP 0), .op .DIV]
def omittedSwapCode : Program :=
  [Scalar.pushWord 5, Scalar.pushWord 17, .op (.DUP 1), .op .DIV]

theorem order_mutants :
    Scalar.run wrongDupCode [23] = some [1, 5, 23] ∧
    Scalar.run omittedSwapCode [23] = some [0, 5, 23] ∧
    Scalar.run boundaryCode [23] ≠ Scalar.run wrongDupCode [23] ∧
    Scalar.run boundaryCode [23] ≠ Scalar.run omittedSwapCode [23] := by decide

def lateIR : List Evm.Instr := [.push (.val (Evm.wmod 5)), .swap 1]
def lateCode : Program := [Scalar.pushWord 5, .op (.SWAP 0)]
theorem late_selected : compileScalar lateIR = some lateCode := rfl

theorem late_fault (m : Evm.Machine) : Evm.run lateIR { m with stack := [] } = .fault := by
  have actual : Scalar.run lateCode [] = none := by decide
  exact (scalar_fault_iff lateIR lateCode late_selected [] { m with stack := [] } rfl).mpr actual

theorem unsupported_depth (m : Evm.Machine) : compileScalar [.dup 17] = none ∧
    Evm.run [.dup 17] { m with stack := irStack (List.replicate 17 7) } =
      .ok { m with stack := irStack (List.replicate 18 7) } 0 := by exact ⟨rfl, rfl⟩

theorem numeric_unchanged : compileScalar NumericSequenceControls.sampleIR =
    some NumericSequenceControls.sampleCode :=
  numeric_code_preserved _ _ NumericSequenceControls.sample_selected

end MixedControls

#print axioms selectScalar_numeric
#print axioms selectScalar_pop
#print axioms selectScalar_dup
#print axioms selectScalar_swap
#print axioms numeric_code_preserved
#print axioms compileScalar_equation
#print axioms scalarLowering
#print axioms scalar_fault_iff
#print axioms MixedControls.sample_selected
#print axioms MixedControls.sample_lowering
#print axioms MixedControls.sample_run
#print axioms MixedControls.sample_complete_frame
#print axioms MixedControls.sample_frame
#print axioms MixedControls.sample_capacity
#print axioms MixedControls.sample_prefixes
#print axioms MixedControls.sample_size
#print axioms MixedControls.wrong_result
#print axioms MixedControls.corrupt_tail
#print axioms MixedControls.actual_boundary
#print axioms MixedControls.boundary_selected
#print axioms MixedControls.boundary_run
#print axioms MixedControls.boundary_complete_frame
#print axioms MixedControls.order_mutants
#print axioms MixedControls.late_selected
#print axioms MixedControls.late_fault
#print axioms MixedControls.unsupported_depth
#print axioms MixedControls.numeric_unchanged

end Solidity.Backend.Selection
