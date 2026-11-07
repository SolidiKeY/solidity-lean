import Solidity.Backend.PrimitivePackets.SignedCheckedSub.Controls
import «tests».h62.item4.«generic-primitive-packets».SignedCheckedFixtures

/-! Regression: checked signed subtraction must neither wrap at either boundary nor
reject all valid mixed-sign inputs. Actual Source evaluation and public-selected
structured-EVM code retain their separate failure observations. The existing
populated signed runtime fixture supplies physical state and arbitrary tails;
this does not claim whole-session/world or fetched-EVM/gas adequacy. -/
namespace H62.PrimitivePackets.SignedSubCorrespondence
open Solidity Solidity.Evm Solidity.Evm.Memory Solidity.Lowering.V07
open Solidity.Backend.PrimitivePackets
open Source.SemanticsExamples (G0 F0)
abbrev U := SignedCheckedSub.U

namespace Runtime
abbrev C := SignedDiv.Controls.P
abbrev F := SignedDiv.Controls.F
abbrev base := Evm.Memory.CompileExamples.base
def lower (x : Int) (hx : U.lo ≤ x ∧ x ≤ U.hi) : PrimTy.int.Denote := integerValue U x hx
def source (x y : Int) (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi) :=
  SignedDiv.Controls.source (lower x hx) (lower y hy)
def target (x y : Int) (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi) :=
  SignedDiv.Controls.target (lower x hx) (lower y hy)
def machine (x y : Int) (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi) :=
  SignedDiv.Controls.machine (lower x hx) (lower y hy)
abbrev represented (x y : Int) (hx : U.lo ≤ x ∧ x ≤ U.hi) (hy : U.lo ≤ y ∧ y ≤ U.hi) :=
  SignedDiv.Controls.initial (lower x hx) (lower y hy)
end Runtime

/-- The bounded pair adapters include the original native source and runtime inputs. -/
theorem original_inputs (a b : PrimTy.int.Denote) :
    Runtime.source a.val b.val (SignedDiv.range a) (SignedDiv.range b) = SignedDiv.Controls.source a b ∧
    Runtime.target a.val b.val (SignedDiv.range a) (SignedDiv.range b) = SignedDiv.Controls.target a b ∧
    Runtime.machine a.val b.val (SignedDiv.range a) (SignedDiv.range b) = SignedDiv.Controls.machine a b :=
  ⟨rfl,rfl,rfl⟩

def code : List Instr :=
  (SignedCheckedSub.selected (C:=Runtime.C) 0 Runtime.F .here (.there .here)).code

theorem target_execution (f : SignedFixture U.lo U.hi) (tail : List Word) :
    run code {Runtime.machine f.lhs.val f.rhs.val f.lhs.property f.rhs.property with stack := tail} =
    match signedSubtract f with
    | .ok z => .ok
        ({Runtime.machine f.lhs.val f.rhs.val f.lhs.property f.rhs.property with stack := tail}.push
          (.val (sword z.val))) 0
    | .error _ => .revert := by
  unfold signedSubtract
  by_cases small : U.lo ≤ f.lhs.val-f.rhs.val ∧ f.lhs.val-f.rhs.val ≤ U.hi
  · rw [checkedSigned_success Int.sub f small]
    obtain ⟨word,repr,ran⟩ := SignedCheckedSub.target_success
      (Runtime.target _ _ f.lhs.property f.rhs.property) .here (.there .here)
      f.lhs.val f.rhs.val f.lhs.property f.rhs.property rfl rfl small
      (Runtime.represented _ _ f.lhs.property f.rhs.property) tail
    have unique : word = .val (sword (f.lhs.val-f.rhs.val)) :=
      SignedDiv.Controls.word_unique _ word repr
    rw [unique] at ran
    exact ran
  · rw [checkedSigned_refusal Int.sub f small]
    exact SignedCheckedSub.target_overflow
      (Runtime.target _ _ f.lhs.property f.rhs.property) .here (.there .here)
      f.lhs.val f.rhs.val f.lhs.property f.rhs.property rfl rfl small
      (Runtime.represented _ _ f.lhs.property f.rhs.property) tail

theorem source_execution (f : SignedFixture U.lo U.hi) (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) {F0 with checked := true} (fuel+3)
      (.binary .sub (.local .here) (.local (.there .here)))).run
      (Runtime.source f.lhs.val f.rhs.val f.lhs.property f.rhs.property) =
    match signedSubtract f with
    | .ok z =>
      (.ok (.val (.int z.val z.property)),
        Runtime.source f.lhs.val f.rhs.val f.lhs.property f.rhs.property)
    | .error _ =>
      (.error (.revert (Source.panicData .arithmetic)),
        Runtime.source f.lhs.val f.rhs.val f.lhs.property f.rhs.property) := by
  unfold signedSubtract
  by_cases small : U.lo ≤ f.lhs.val-f.rhs.val ∧ f.lhs.val-f.rhs.val ≤ U.hi
  · rw [checkedSigned_success Int.sub f small]
    exact SignedCheckedSub.source_success (G0 p) F0 fuel
      (Runtime.source _ _ f.lhs.property f.rhs.property) .here (.there .here)
      f.lhs.val f.rhs.val f.lhs.property f.rhs.property rfl rfl small
  · rw [checkedSigned_refusal Int.sub f small]
    exact SignedCheckedSub.source_overflow (G0 p) F0 fuel
      (Runtime.source _ _ f.lhs.property f.rhs.property) .here (.there .here)
      f.lhs.val f.rhs.val f.lhs.property f.rhs.property rfl rfl small

theorem initial_representation (f : SignedFixture U.lo U.hi) :
    StateRepr 1 0 6 Runtime.F (Runtime.target _ _ f.lhs.property f.rhs.property)
      Runtime.base (Runtime.machine _ _ f.lhs.property f.rhs.property) :=
  Runtime.represented _ _ f.lhs.property f.rhs.property

theorem public_selection :
    Memory.compileVal 0 Runtime.F
      (SignedCheckedSub.value (C:=Runtime.C) .here (.there .here)) =
      some (SignedCheckedSub.selected 0 Runtime.F .here (.there .here)) :=
  SignedCheckedSub.public_selection 0 Runtime.F .here (.there .here)

theorem table_target (c : OriginalSignedSubCase) (tail : List Word) :
    run code {Runtime.machine (signedSubFixture c).lhs.val (signedSubFixture c).rhs.val
      (signedSubFixture c).lhs.property (signedSubFixture c).rhs.property with stack := tail} =
    match signedSubtract (signedSubFixture c) with
    | .ok z => .ok
        ({Runtime.machine (signedSubFixture c).lhs.val (signedSubFixture c).rhs.val
          (signedSubFixture c).lhs.property (signedSubFixture c).rhs.property with stack := tail}.push
            (.val (sword z.val))) 0
    | .error _ => .revert := target_execution (signedSubFixture c) tail

theorem table_source (c : OriginalSignedSubCase) (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) {F0 with checked := true} (fuel+3)
      (.binary .sub (.local .here) (.local (.there .here)))).run
      (Runtime.source (signedSubFixture c).lhs.val (signedSubFixture c).rhs.val
        (signedSubFixture c).lhs.property (signedSubFixture c).rhs.property) =
    match signedSubtract (signedSubFixture c) with
    | .ok z => (.ok (.val (.int z.val z.property)),
        Runtime.source (signedSubFixture c).lhs.val (signedSubFixture c).rhs.val
          (signedSubFixture c).lhs.property (signedSubFixture c).rhs.property)
    | .error _ => (.error (.revert (Source.panicData .arithmetic)),
        Runtime.source (signedSubFixture c).lhs.val (signedSubFixture c).rhs.val
          (signedSubFixture c).lhs.property (signedSubFixture c).rhs.property) :=
  source_execution (signedSubFixture c) p fuel

theorem reject_all_refuted (tail : List Word) :
    run code {Runtime.machine 7 2 (by decide) (by decide) with stack := tail} ≠ .revert := by
  have actual : run code {Runtime.machine 7 2 (by decide) (by decide) with stack := tail} =
      .ok ({Runtime.machine 7 2 (by decide) (by decide) with stack := tail}.push
        (.val (sword 5))) 0 := by
    simpa only [signedSubFixture,signedSubtract,checkedSignedResult] using target_execution (signedSubFixture .regular) tail
  rw [actual]
  intro impossible
  cases impossible

theorem positive_overflow_refuted (tail : List Word) (out : Machine) (cost : Nat) :
    run code {Runtime.machine U.hi (-1) (by decide) (by decide) with stack := tail} ≠ .ok out cost := by
  have actual : run code {Runtime.machine U.hi (-1) (by decide) (by decide) with stack := tail} = .revert := by
    simpa only [signedSubFixture,signedSubtract,checkedSignedResult] using target_execution (signedSubFixture .upper) tail
  rw [actual]
  intro impossible
  cases impossible

theorem negative_overflow_refuted (tail : List Word) (out : Machine) (cost : Nat) :
    run code {Runtime.machine U.lo 1 (by decide) (by decide) with stack := tail} ≠ .ok out cost := by
  have actual : run code {Runtime.machine U.lo 1 (by decide) (by decide) with stack := tail} = .revert := by
    simpa only [signedSubFixture,signedSubtract,checkedSignedResult] using target_execution (signedSubFixture .lower) tail
  rw [actual]
  intro impossible
  cases impossible

theorem low_fuel (f : SignedFixture U.lo U.hi) (p : Roadmap.Pipeline) :
    (Source.evalE (G0 p) {F0 with checked := true} 0
      (.binary .sub (.local .here) (.local (.there .here)))).run
      (Runtime.source f.lhs.val f.rhs.val f.lhs.property f.rhs.property) =
      (.error .timeout,
        Runtime.source f.lhs.val f.rhs.val f.lhs.property f.rhs.property) := by rfl

#print axioms original_inputs
#print axioms target_execution
#print axioms source_execution
#print axioms initial_representation
#print axioms public_selection
#print axioms table_target
#print axioms table_source
#print axioms reject_all_refuted
#print axioms positive_overflow_refuted
#print axioms negative_overflow_refuted
#print axioms low_fuel
end H62.PrimitivePackets.SignedSubCorrespondence
