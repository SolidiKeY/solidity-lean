import Solidity.Backend.PrimitivePackets.CheckedSub.Controls
import «tests».h62.item4.«generic-primitive-packets».SubFixtures

/-! Live intrinsic execution bridge for every typed operand pair in the frozen
CheckedSub fixture family. Source bytes and coarse target revert remain distinct.
This is not a v4.35 migration or a whole-language adequacy claim. -/
namespace H62.PrimitivePackets.SubCorrespondence
open Solidity Solidity.Evm Solidity.Evm.Memory
open Solidity.Backend.PrimitivePackets
open CheckedSub.Controls
open Source.SemanticsExamples (E0 G0 F0)

theorem target_execution (f : SubFixture W) (tail : List Word) :
    run Fixture.differenceCode
      {Fixture.machine f.lhs.val f.rhs.val f.lhs.isLt f.rhs.isLt with stack := tail} =
    match subtract f with
    | .ok z => .ok
        ({Fixture.machine f.lhs.val f.rhs.val f.lhs.isLt f.rhs.isLt with stack := tail}.push
          (.val z)) 0
    | .error _ => .revert := by
  by_cases enough : f.rhs.val ≤ f.lhs.val
  · rw [subtract_success f enough]
    exact Fixture.result _ _ _ _ enough tail
  · rw [subtract_refusal f enough]
    have outside : ¬ (CheckedSub.U.lo ≤ (f.lhs.val : Int)-f.rhs.val ∧
        (f.lhs.val : Int)-f.rhs.val ≤ CheckedSub.U.hi) :=
      (CheckedSub.underflow_iff _ _ (Fixture.nat_range _ f.lhs.isLt)
        (Fixture.nat_range _ f.rhs.isLt)).mpr (by omega)
    exact CheckedSub.target_underflow
      (Fixture.target _ _ f.lhs.isLt f.rhs.isLt) .here (.there .here)
      f.lhs.val f.rhs.val (Fixture.nat_range _ f.lhs.isLt)
      (Fixture.nat_range _ f.rhs.isLt) rfl rfl outside
      (Fixture.represented _ _ f.lhs.isLt f.rhs.isLt) tail

theorem source_execution (f : SubFixture W) (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) {F0 with checked := true} (fuel+3)
      (.binary .sub (.local (Fixture.si false)) (.local (Fixture.si true)))).run
      (Fixture.source f.lhs.val f.rhs.val f.lhs.isLt f.rhs.isLt) =
    match subtract f with
    | .ok z =>
      (.ok (.val (.int (z.val : Int) (Fixture.nat_range z.val z.isLt))),
        Fixture.source f.lhs.val f.rhs.val f.lhs.isLt f.rhs.isLt)
    | .error _ =>
      (.error (.revert (Source.panicData .arithmetic)),
        Fixture.source f.lhs.val f.rhs.val f.lhs.isLt f.rhs.isLt) := by
  by_cases enough : f.rhs.val ≤ f.lhs.val
  · rw [subtract_success f enough]
    have fits : CheckedSub.U.lo ≤ (f.lhs.val : Int)-f.rhs.val ∧
        (f.lhs.val : Int)-f.rhs.val ≤ CheckedSub.U.hi :=
      (CheckedSub.success_iff _ _ (Fixture.nat_range _ f.lhs.isLt)
        (Fixture.nat_range _ f.rhs.isLt)).mpr (by omega)
    have step := CheckedSub.source_success (G0 p) F0 fuel
      (Fixture.source _ _ f.lhs.isLt f.rhs.isLt) (Fixture.si false) (Fixture.si true)
      f.lhs.val f.rhs.val (Fixture.nat_range _ f.lhs.isLt)
      (Fixture.nat_range _ f.rhs.isLt) rfl rfl fits
    simpa only [Int.ofNat_sub enough] using step
  · rw [subtract_refusal f enough]
    have outside : ¬ (CheckedSub.U.lo ≤ (f.lhs.val : Int)-f.rhs.val ∧
        (f.lhs.val : Int)-f.rhs.val ≤ CheckedSub.U.hi) :=
      (CheckedSub.underflow_iff _ _ (Fixture.nat_range _ f.lhs.isLt)
        (Fixture.nat_range _ f.rhs.isLt)).mpr (by omega)
    exact CheckedSub.source_underflow (G0 p) F0 fuel
      (Fixture.source _ _ f.lhs.isLt f.rhs.isLt) (Fixture.si false) (Fixture.si true)
      f.lhs.val f.rhs.val (Fixture.nat_range _ f.lhs.isLt)
      (Fixture.nat_range _ f.rhs.isLt) rfl rfl outside

/-- The physical input is constructed, not an uninhabited representation premise. -/
theorem initial_representation (f : SubFixture W) :
    StateRepr 1 0 8 Fixture.F (Fixture.target _ _ f.lhs.isLt f.rhs.isLt)
      CompileExamples.base (Fixture.machine _ _ f.lhs.isLt f.rhs.isLt) :=
  Fixture.represented _ _ f.lhs.isLt f.rhs.isLt

/-- The public compiler, rather than a supplied compiled-value certificate. -/
theorem public_selection :
    Memory.compileVal 0 Fixture.F
      (CheckedSub.value (C:=CompileExamples.C) .here (.there .here)) =
      some (CheckedSub.selected 0 Fixture.F .here (.there .here)) :=
  CheckedSub.public_selection 0 Fixture.F .here (.there .here)

/-- All seven original rows inherit the same selected-code equation. -/
theorem table_target (c : OriginalSubCase) (tail : List Word) :
    run Fixture.differenceCode
      {Fixture.machine (fixture c).lhs.val (fixture c).rhs.val
        (fixture c).lhs.isLt (fixture c).rhs.isLt with stack := tail} =
    match subtract (fixture c) with
    | .ok z => .ok
        ({Fixture.machine (fixture c).lhs.val (fixture c).rhs.val
          (fixture c).lhs.isLt (fixture c).rhs.isLt with stack := tail}.push (.val z)) 0
    | .error _ => .revert :=
  target_execution (fixture c) tail

theorem regular_target (tail : List Word) :
    run Fixture.differenceCode {Fixture.machine 9 7 (by decide) (by decide) with stack := tail} =
      .ok ({Fixture.machine 9 7 (by decide) (by decide) with stack := tail}.push w[2]) 0 := by
  simpa only [fixture, subtract] using target_execution (fixture .regular) tail

theorem wrong_order_target (tail : List Word) :
    run Fixture.differenceCode {Fixture.machine 7 9 (by decide) (by decide) with stack := tail} =
      .revert := by
  simpa only [fixture, subtract] using target_execution (fixture .wrong_order_refused) tail

theorem reject_all_refuted (tail : List Word) :
    run Fixture.differenceCode {Fixture.machine 9 7 (by decide) (by decide) with stack := tail} ≠
      .revert := by
  rw [regular_target]
  intro impossible
  cases impossible

theorem accept_underflow_refuted (tail : List Word) (out : Machine) (cost : Nat) :
    run Fixture.differenceCode {Fixture.machine 7 9 (by decide) (by decide) with stack := tail} ≠
      .ok out cost := by
  rw [wrong_order_target]
  intro impossible
  cases impossible

#print axioms target_execution
#print axioms source_execution
#print axioms initial_representation
#print axioms public_selection
#print axioms table_target
#print axioms regular_target
#print axioms wrong_order_target
#print axioms reject_all_refuted
#print axioms accept_underflow_refuted
end H62.PrimitivePackets.SubCorrespondence
