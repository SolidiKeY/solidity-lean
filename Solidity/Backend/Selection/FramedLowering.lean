import Solidity.Backend.Selection.FramedLoweringInterface
import Solidity.Backend.Selection.MixedSelection

/-! Construct the strengthened existing lowering contract from actual selected
IR execution and compose its complete caller frame through sequences. -/
namespace Solidity.Backend.Selection
namespace FramedLoweringCertificate

def ofForwardReflect {ir : List Evm.Instr} {block : Block}
    (forward : ∀ (input output : Scalar.Stack) (initial : Evm.Machine),
      initial.stack = irStack input → StructuredExec block input output →
      Evm.run ir initial = .ok { initial with stack := irStack output } 0)
    (reflection : ∀ (input : Scalar.Stack) (initial final : Evm.Machine) (skip : Nat),
      initial.stack = irStack input → Evm.run ir initial = .ok final skip →
      ∃ output : Scalar.Stack, skip = 0 ∧ final = { initial with stack := irStack output } ∧
        StructuredExec block input output) : FramedLoweringCertificate ir block where
  toLoweringCertificate := {
    success := by
      intro input output initial stack
      constructor
      · intro actual
        obtain ⟨recovered,zero,frame,structured⟩ := reflection input initial _ 0 stack actual
        have same : output = recovered := (stack_update_eq initial output recovered).mp frame
        subst recovered
        exact structured
      · exact forward input output initial stack
  }
  reflect := reflection

/-- The existing selector equation classifies every actual successful result;
no target result, caller-frame equality or pending-skip assumption is supplied. -/
def scalar (ir : List Evm.Instr) (code : Program) (selected : compileScalar ir = some code) :
    FramedLoweringCertificate ir (.code code) where
  toLoweringCertificate := scalarLowering ir code selected
  reflect := by
    intro input initial final skip stack actual
    rw [compileScalar_equation ir code selected input initial stack] at actual
    cases run : Scalar.run code input with
    | none => simp only [run, reduceCtorEq] at actual
    | some output =>
      simp only [run] at actual
      have parts : { initial with stack := irStack output } = final ∧ 0 = skip := Evm.Out.ok.inj actual
      exact ⟨output,parts.2.symm,parts.1.symm,.code run⟩

theorem seq_forward {leftIR rightIR : List Evm.Instr} {left right : Block}
    (first : FramedLoweringCertificate leftIR left) (second : FramedLoweringCertificate rightIR right)
    (input output : Scalar.Stack) (initial : Evm.Machine) (stack : initial.stack = irStack input)
    (actual : StructuredExec (.seq left right) input output) :
    Evm.run (leftIR ++ rightIR) initial = .ok { initial with stack := irStack output } 0 := by
  cases actual with
  | @seq a b s middle t leftRun rightRun =>
    have runLeft : Evm.run leftIR initial = .ok { initial with stack := irStack middle } 0 :=
      (first.success input middle initial stack).mpr leftRun
    rw [Evm.run_append_ok runLeft]
    exact (second.success middle output { initial with stack := irStack middle } rfl).mpr rightRun

theorem seq_reflect {leftIR rightIR : List Evm.Instr} {left right : Block}
    (first : FramedLoweringCertificate leftIR left) (second : FramedLoweringCertificate rightIR right)
    (input : Scalar.Stack) (initial final : Evm.Machine) (skip : Nat)
    (stack : initial.stack = irStack input) (actual : Evm.run (leftIR ++ rightIR) initial = .ok final skip) :
    ∃ output : Scalar.Stack, skip = 0 ∧ final = { initial with stack := irStack output } ∧
      StructuredExec (.seq left right) input output := by
  have combined : (Evm.run leftIR initial).bind (fun middle pending => Evm.exec rightIR pending middle) =
      .ok final skip := by
    simpa only [Evm.run, Evm.exec_append] using actual
  cases runLeft : Evm.run leftIR initial with
  | revert => simp only [runLeft, Evm.Out.bind, reduceCtorEq] at combined
  | fault => simp only [runLeft, Evm.Out.bind, reduceCtorEq] at combined
  | ok middle pending =>
    obtain ⟨reached,zero,frame,leftRun⟩ := first.reflect input initial middle pending stack runLeft
    subst pending
    subst middle
    have runRight : Evm.run rightIR { initial with stack := irStack reached } = .ok final skip := by
      simpa only [runLeft, Evm.Out.bind] using combined
    obtain ⟨output,zero,frame,rightRun⟩ := second.reflect reached
      { initial with stack := irStack reached } final skip rfl runRight
    exact ⟨output,zero,frame,.seq leftRun rightRun⟩

/-- Sequence extends the existing lowering framework, including reflection of
its actual intermediate machine, rather than postulating frame preservation. -/
def seq {leftIR rightIR : List Evm.Instr} {left right : Block}
    (first : FramedLoweringCertificate leftIR left) (second : FramedLoweringCertificate rightIR right) :
    FramedLoweringCertificate (leftIR ++ rightIR) (.seq left right) :=
  ofForwardReflect (seq_forward first second) (seq_reflect first second)

#print axioms ofForwardReflect
#print axioms scalar
#print axioms seq_forward
#print axioms seq_reflect
#print axioms seq

end FramedLoweringCertificate
end Solidity.Backend.Selection
