import Solidity.Backend.PrimitivePackets.CheckedMul.Controls
import «tests».h62.item4.«generic-primitive-packets».MulFixtures

/-! Regression: reject-all and silently wrapping checked-multiply implementations
cannot satisfy this populated fixture family. Every typed uint256 operand pair
uses public compiler selection and actual execution, with arbitrary saved tails
and either pipeline. Source exact panic bytes and coarse target revert remain
distinct. This is not whole-language/session or gas adequacy. -/
namespace H62.PrimitivePackets.MulCorrespondence
open Solidity Solidity.Evm Solidity.Evm.Memory
open Solidity.Backend.PrimitivePackets
open CheckedMul.Controls
open Source.SemanticsExamples (E0 G0 F0)

/-- A product outside the natural range is outside the actual Source int type. -/
theorem overflow_bounds (f : MulFixture W)
    (large : ¬ f.lhs.val * f.rhs.val < W) :
    ¬ (CheckedMul.U.lo ≤ (f.lhs.val : Int)*f.rhs.val ∧
      (f.lhs.val : Int)*f.rhs.val ≤ CheckedMul.U.hi) := by
  change ¬ (0 ≤ ((f.lhs.val*f.rhs.val : Nat) : Int) ∧
    ((f.lhs.val*f.rhs.val : Nat) : Int) ≤ (W : Int)-1)
  omega

theorem target_execution (f : MulFixture W) (tail : List Word) :
    run Fixture.productCode
      {Fixture.machine f.lhs.val f.rhs.val f.lhs.isLt f.rhs.isLt with stack := tail} =
    match multiply f with
    | .ok z => .ok
        ({Fixture.machine f.lhs.val f.rhs.val f.lhs.isLt f.rhs.isLt with stack := tail}.push
          (.val z)) 0
    | .error _ => .revert := by
  by_cases small : f.lhs.val * f.rhs.val < W
  · rw [multiply_success f small]
    exact Fixture.result _ _ _ _ small tail
  · rw [multiply_refusal f small]
    have outside := overflow_bounds f small
    exact CheckedMul.target_overflow
      (Fixture.target _ _ f.lhs.isLt f.rhs.isLt) .here (.there .here)
      f.lhs.val f.rhs.val (Fixture.nat_range _ f.lhs.isLt)
      (Fixture.nat_range _ f.rhs.isLt) rfl rfl outside
      (Fixture.represented _ _ f.lhs.isLt f.rhs.isLt) tail

theorem source_execution (f : MulFixture W) (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) {F0 with checked := true} (fuel+3)
      (.binary .mul (.local (Fixture.si false)) (.local (Fixture.si true)))).run
      (Fixture.source f.lhs.val f.rhs.val f.lhs.isLt f.rhs.isLt) =
    match multiply f with
    | .ok z =>
      (.ok (.val (.int (z.val : Int) (Fixture.nat_range z.val z.isLt))),
        Fixture.source f.lhs.val f.rhs.val f.lhs.isLt f.rhs.isLt)
    | .error _ =>
      (.error (.revert (Source.panicData .arithmetic)),
        Fixture.source f.lhs.val f.rhs.val f.lhs.isLt f.rhs.isLt) := by
  by_cases small : f.lhs.val * f.rhs.val < W
  · rw [multiply_success f small]
    simpa only [Int.natCast_mul] using
      CheckedMul.source_success (G0 p) F0 fuel
        (Fixture.source _ _ f.lhs.isLt f.rhs.isLt) (Fixture.si false) (Fixture.si true)
        f.lhs.val f.rhs.val (Fixture.nat_range _ f.lhs.isLt)
        (Fixture.nat_range _ f.rhs.isLt) rfl rfl
        (Fixture.nat_range (f.lhs.val*f.rhs.val) small)
  · rw [multiply_refusal f small]
    have outside := overflow_bounds f small
    exact CheckedMul.source_overflow (G0 p) F0 fuel
      (Fixture.source _ _ f.lhs.isLt f.rhs.isLt) (Fixture.si false) (Fixture.si true)
      f.lhs.val f.rhs.val (Fixture.nat_range _ f.lhs.isLt)
      (Fixture.nat_range _ f.rhs.isLt) rfl rfl outside

theorem initial_representation (f : MulFixture W) :
    StateRepr 1 0 8 Fixture.F (Fixture.target _ _ f.lhs.isLt f.rhs.isLt)
      CheckedMul.Populated.base (Fixture.machine _ _ f.lhs.isLt f.rhs.isLt) :=
  Fixture.represented _ _ f.lhs.isLt f.rhs.isLt

theorem public_selection :
    Memory.compileVal 0 Fixture.F
      (CheckedMul.value (C:=CheckedMul.Populated.C) .here (.there .here)) =
      some (CheckedMul.selected 0 Fixture.F .here (.there .here)) :=
  CheckedMul.public_selection 0 Fixture.F .here (.there .here)

theorem table_target (c : OriginalMulCase) (tail : List Word) :
    run Fixture.productCode
      {Fixture.machine (mulFixture c).lhs.val (mulFixture c).rhs.val
        (mulFixture c).lhs.isLt (mulFixture c).rhs.isLt with stack := tail} =
    match multiply (mulFixture c) with
    | .ok z => .ok
        ({Fixture.machine (mulFixture c).lhs.val (mulFixture c).rhs.val
          (mulFixture c).lhs.isLt (mulFixture c).rhs.isLt with stack := tail}.push (.val z)) 0
    | .error _ => .revert := target_execution (mulFixture c) tail

theorem reject_all_refuted (tail : List Word) :
    run Fixture.productCode {Fixture.machine 7 9 (by decide) (by decide) with stack := tail} ≠
      .revert := by
  rw [Fixture.regular]
  intro impossible
  cases impossible

theorem accept_overflow_refuted (tail : List Word) (out : Machine) (cost : Nat) :
    run Fixture.productCode {Fixture.machine (W-1) 2 (by decide) (by decide) with stack := tail} ≠
      .ok out cost := by
  rw [Fixture.overflow]
  intro impossible
  cases impossible

theorem low_fuel (f : MulFixture W) (p : Roadmap.Pipeline) :
    (Source.evalE (G0 p) {F0 with checked := true} 0
      (.binary .mul (.local (Fixture.si false)) (.local (Fixture.si true)))).run
      (Fixture.source f.lhs.val f.rhs.val f.lhs.isLt f.rhs.isLt) =
      (.error .timeout, Fixture.source f.lhs.val f.rhs.val f.lhs.isLt f.rhs.isLt) := by
  rfl

#print axioms overflow_bounds
#print axioms target_execution
#print axioms source_execution
#print axioms initial_representation
#print axioms public_selection
#print axioms table_target
#print axioms reject_all_refuted
#print axioms accept_overflow_refuted
#print axioms low_fuel
end H62.PrimitivePackets.MulCorrespondence
