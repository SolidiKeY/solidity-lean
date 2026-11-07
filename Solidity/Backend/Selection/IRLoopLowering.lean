import Solidity.Backend.Selection.IRLoopPackets

/-! Actual compiler-IR recursive loops lower through the same existing block
contract. Successful intermediate frames and finite witnesses are derived. -/
namespace Solidity.Backend.Selection
namespace FramedLoweringCertificate

theorem loop_forward_finite {block : Block} {input output : Scalar.Stack}
    (actual : StructuredExec block input output) :
    ∀ (code : Program) (body : Block), block = .loop code body →
    ∀ (conditionIR bodyIR : List Evm.Instr),
    FramedLoweringCertificate conditionIR (.code code) → FramedLoweringCertificate bodyIR body →
    ∀ (initial : Evm.Machine), initial.stack = irStack input →
    ∃ count, Evm.loopIterN (Evm.run conditionIR) (Evm.run bodyIR) count initial =
      .inr (.ok { initial with stack := irStack output } 0) := by
  induction actual with
  | code run => intro code body equal; cases equal
  | seq left right ihLeft ihRight => intro code body equal; cases equal
  | iteTrue run nonzero body ih => intro code body equal; cases equal
  | iteFalse run body ih => intro code body equal; cases equal
  | @loopDone c b input output run =>
    intro code body equal conditionIR bodyIR condition bodyCertificate initial stack
    cases equal
    have runCondition : Evm.run conditionIR initial = .ok { initial with stack := irStack (0 :: output) } 0 :=
      (condition.success input (0 :: output) initial stack).mpr (.code run)
    refine ⟨1,?_⟩
    rw [Evm.loopIterN, IRLoop.turn_word _ _ initial 0 output runCondition]
    rfl
  | @loopMore c b input middle next output word run nonzero bodyRun rest ihBody ihRest =>
    intro code body equal conditionIR bodyIR condition bodyCertificate initial stack
    cases equal
    have runCondition : Evm.run conditionIR initial = .ok { initial with stack := irStack (word :: middle) } 0 :=
      (condition.success input (word :: middle) initial stack).mpr (.code run)
    have runBody : Evm.run bodyIR { initial with stack := irStack middle } =
        .ok { initial with stack := irStack next } 0 :=
      (bodyCertificate.success middle next { initial with stack := irStack middle } rfl).mpr bodyRun
    obtain ⟨count,trace⟩ := ihRest c b rfl conditionIR bodyIR condition bodyCertificate
      { initial with stack := irStack next } rfl
    have flag : (word == 0) = false := Bool.eq_false_iff.mpr (fun equal => nonzero (beq_iff_eq.mp equal))
    refine ⟨count + 1,?_⟩
    rw [Evm.loopIterN, IRLoop.turn_word _ _ initial word middle runCondition]
    simpa only [flag, Bool.false_eq_true, if_false, runBody] using trace

theorem loop_forward {conditionIR bodyIR : List Evm.Instr} {code : Program} {body : Block}
    (condition : FramedLoweringCertificate conditionIR (.code code))
    (bodyCertificate : FramedLoweringCertificate bodyIR body)
    (input output : Scalar.Stack) (initial : Evm.Machine) (stack : initial.stack = irStack input)
    (actual : StructuredExec (.loop code body) input output) :
    Evm.run [.loop conditionIR bodyIR] initial = .ok { initial with stack := irStack output } 0 := by
  obtain ⟨count,trace⟩ := loop_forward_finite actual code body rfl conditionIR bodyIR condition bodyCertificate initial stack
  rw [IRLoop.single_run]
  exact Evm.loopRun_of_iterN trace

theorem loop_iter_reflect {conditionIR bodyIR : List Evm.Instr} {code : Program} {body : Block}
    (condition : FramedLoweringCertificate conditionIR (.code code))
    (bodyCertificate : FramedLoweringCertificate bodyIR body)
    (count : Nat) (input : Scalar.Stack) (initial final : Evm.Machine) (skip : Nat)
    (stack : initial.stack = irStack input)
    (actual : Evm.loopIterN (Evm.run conditionIR) (Evm.run bodyIR) count initial = .inr (.ok final skip)) :
    ∃ output : Scalar.Stack, skip = 0 ∧ final = { initial with stack := irStack output } ∧
      StructuredExec (.loop code body) input output := by
  induction count generalizing input initial with
  | zero => cases actual
  | succ count ih =>
    rw [Evm.loopIterN] at actual
    cases runCondition : Evm.run conditionIR initial with
    | revert => simp only [Evm.loopTurn, runCondition] at actual; cases actual
    | fault => simp only [Evm.loopTurn, runCondition] at actual; cases actual
    | ok tested pending =>
      obtain ⟨values,zero,frame,structured⟩ := condition.reflect input initial tested pending stack runCondition
      subst pending
      subst tested
      have conditionRun : Scalar.run code input = some values := by
        cases structured with
        | code run => exact run
      cases values with
      | nil => rw [IRLoop.turn_empty _ _ initial runCondition] at actual; cases actual
      | cons word middle =>
        rw [IRLoop.turn_word _ _ initial word middle runCondition] at actual
        by_cases zero : word = 0
        · subst word
          simp only [beq_self_eq_true, if_true] at actual
          have result : Evm.Out.ok { initial with stack := irStack middle } 0 = .ok final skip := Sum.inr.inj actual
          have parts : { initial with stack := irStack middle } = final ∧ 0 = skip := Evm.Out.ok.inj result
          exact ⟨middle,parts.2.symm,parts.1.symm,.loopDone conditionRun⟩
        · have flag : (word == 0) = false := Bool.eq_false_iff.mpr (fun equal => zero (beq_iff_eq.mp equal))
          simp only [flag, Bool.false_eq_true, if_false] at actual
          cases runBody : Evm.run bodyIR { initial with stack := irStack middle } with
          | revert => simp only [runBody] at actual; cases actual
          | fault => simp only [runBody] at actual; cases actual
          | ok next pending =>
            obtain ⟨reached,zeroSkip,frame,bodyRun⟩ := bodyCertificate.reflect middle
              { initial with stack := irStack middle } next pending rfl runBody
            subst pending
            subst next
            have remainder : Evm.loopIterN (Evm.run conditionIR) (Evm.run bodyIR) count
                { initial with stack := irStack reached } = .inr (.ok final skip) := by
              simpa only [runBody] using actual
            obtain ⟨output,zeroSkip,frame,restRun⟩ := ih reached
              { initial with stack := irStack reached } rfl remainder
            exact ⟨output,zeroSkip,frame,.loopMore conditionRun zero bodyRun restRun⟩

theorem loop_reflect {conditionIR bodyIR : List Evm.Instr} {code : Program} {body : Block}
    (condition : FramedLoweringCertificate conditionIR (.code code))
    (bodyCertificate : FramedLoweringCertificate bodyIR body)
    (input : Scalar.Stack) (initial final : Evm.Machine) (skip : Nat)
    (stack : initial.stack = irStack input) (actual : Evm.run [.loop conditionIR bodyIR] initial = .ok final skip) :
    ∃ output : Scalar.Stack, skip = 0 ∧ final = { initial with stack := irStack output } ∧
      StructuredExec (.loop code body) input output := by
  rw [IRLoop.single_run] at actual
  obtain ⟨count,trace⟩ := IRLoop.finite_success _ _ initial final skip actual
  exact loop_iter_reflect condition bodyCertificate count input initial final skip stack trace

/-- Recursive IR loop lowering is produced from proved components and the
actual unbounded loopRun laws; no whole-loop lowering premise is assumed. -/
def loop {conditionIR bodyIR : List Evm.Instr} {code : Program} {body : Block}
    (condition : FramedLoweringCertificate conditionIR (.code code))
    (bodyCertificate : FramedLoweringCertificate bodyIR body) :
    FramedLoweringCertificate [.loop conditionIR bodyIR] (.loop code body) :=
  ofForwardReflect (loop_forward condition bodyCertificate) (loop_reflect condition bodyCertificate)

#print axioms loop_forward_finite
#print axioms loop_forward
#print axioms loop_iter_reflect
#print axioms loop_reflect
#print axioms loop

end FramedLoweringCertificate
end Solidity.Backend.Selection
