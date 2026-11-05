import Solidity.Backend.Selection.IRBranchPackets

/-! Produce framed lowering for the existing relative-jump branch emitter,
using actual component results and preserving the complete numeric caller frame. -/
namespace Solidity.Backend.Selection
namespace FramedLoweringCertificate

theorem branch_forward {conditionIR leftIR rightIR : List Evm.Instr} {code : Program} {left right : Block}
    (condition : FramedLoweringCertificate conditionIR (.code code))
    (yes : FramedLoweringCertificate leftIR left) (no : FramedLoweringCertificate rightIR right)
    (input output : Scalar.Stack) (initial : Evm.Machine) (stack : initial.stack = irStack input)
    (actual : StructuredExec (.ite code left right) input output) :
    Evm.run (IRBranch.emit conditionIR leftIR rightIR) initial =
      .ok { initial with stack := irStack output } 0 := by
  cases actual with
  | @iteTrue c a b s middle t word conditionRun nonzero bodyRun =>
    have runCondition : Evm.run conditionIR initial = .ok { initial with stack := irStack (word :: middle) } 0 :=
      (condition.success input (word :: middle) initial stack).mpr (.code conditionRun)
    have runBody : Evm.run leftIR { initial with stack := irStack middle } =
        .ok { initial with stack := irStack output } 0 :=
      (yes.success middle output { initial with stack := irStack middle } rfl).mpr bodyRun
    have flag : (word == 0) = false := Bool.eq_false_iff.mpr (fun equal => nonzero (beq_iff_eq.mp equal))
    rw [IRBranch.run runCondition]
    simp only [flag, Bool.false_eq_true, if_false, runBody, Evm.Out.ok_bind, IRBranch.join_normal]
  | @iteFalse c a b s middle t conditionRun bodyRun =>
    have runCondition : Evm.run conditionIR initial = .ok { initial with stack := irStack (0 :: middle) } 0 :=
      (condition.success input (0 :: middle) initial stack).mpr (.code conditionRun)
    rw [IRBranch.run runCondition]
    simp only [beq_self_eq_true, if_true]
    exact (no.success middle output { initial with stack := irStack middle } rfl).mpr bodyRun

theorem branch_reflect {conditionIR leftIR rightIR : List Evm.Instr} {code : Program} {left right : Block}
    (condition : FramedLoweringCertificate conditionIR (.code code))
    (yes : FramedLoweringCertificate leftIR left) (no : FramedLoweringCertificate rightIR right)
    (input : Scalar.Stack) (initial final : Evm.Machine) (skip : Nat)
    (stack : initial.stack = irStack input)
    (actual : Evm.run (IRBranch.emit conditionIR leftIR rightIR) initial = .ok final skip) :
    ∃ output : Scalar.Stack, skip = 0 ∧ final = { initial with stack := irStack output } ∧
      StructuredExec (.ite code left right) input output := by
  rw [IRBranch.split] at actual
  cases runCondition : Evm.run conditionIR initial with
  | revert => simp only [runCondition, Evm.Out.bind, reduceCtorEq] at actual
  | fault => simp only [runCondition, Evm.Out.bind, reduceCtorEq] at actual
  | ok tested pending =>
    obtain ⟨values,zero,frame,structured⟩ := condition.reflect input initial tested pending stack runCondition
    subst pending
    subst tested
    have tailActual : Evm.run (IRBranch.emit [] leftIR rightIR)
        { initial with stack := irStack values } = .ok final skip := by
      simpa only [runCondition, Evm.Out.ok_bind] using actual
    have conditionRun : Scalar.run code input = some values := by
      cases structured with
      | code run => exact run
    cases values with
    | nil => rw [IRBranch.empty_suffix] at tailActual; cases tailActual
    | cons word middle =>
      rw [IRBranch.suffix_run] at tailActual
      by_cases zero : word = 0
      · subst word
        simp only [beq_self_eq_true, if_true] at tailActual
        obtain ⟨output,zero,frame,bodyRun⟩ := no.reflect middle
          { initial with stack := irStack middle } final skip rfl tailActual
        exact ⟨output,zero,frame,.iteFalse conditionRun bodyRun⟩
      · have flag : (word == 0) = false := Bool.eq_false_iff.mpr (fun equal => zero (beq_iff_eq.mp equal))
        simp only [flag, Bool.false_eq_true, if_false] at tailActual
        cases runBody : Evm.run leftIR { initial with stack := irStack middle } with
        | revert => simp only [runBody, Evm.Out.bind, reduceCtorEq] at tailActual
        | fault => simp only [runBody, Evm.Out.bind, reduceCtorEq] at tailActual
        | ok reached pending =>
          obtain ⟨output,zeroSkip,frame,bodyRun⟩ := yes.reflect middle
            { initial with stack := irStack middle } reached pending rfl runBody
          subst pending
          subst reached
          have result : Evm.Out.ok { initial with stack := irStack output } 0 = .ok final skip := by
            simpa only [runBody, Evm.Out.ok_bind, IRBranch.join_normal] using tailActual
          have parts : { initial with stack := irStack output } = final ∧ 0 = skip := Evm.Out.ok.inj result
          exact ⟨output,parts.2.symm,parts.1.symm,.iteTrue conditionRun zero bodyRun⟩

/-- Existing relative IR branches lower to the same existing labelled block;
all child certificates are proved components, not a whole-branch premise. -/
def branch {conditionIR leftIR rightIR : List Evm.Instr} {code : Program} {left right : Block}
    (condition : FramedLoweringCertificate conditionIR (.code code))
    (yes : FramedLoweringCertificate leftIR left) (no : FramedLoweringCertificate rightIR right) :
    FramedLoweringCertificate (IRBranch.emit conditionIR leftIR rightIR) (.ite code left right) :=
  ofForwardReflect (branch_forward condition yes no) (branch_reflect condition yes no)

#print axioms branch_forward
#print axioms branch_reflect
#print axioms branch

end FramedLoweringCertificate
end Solidity.Backend.Selection
