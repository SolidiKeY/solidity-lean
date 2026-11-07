import Solidity.Backend.PrimitivePackets.SignedCheckedAdd.Controls
import Solidity.Backend.PrimitivePackets.SignedMod.Controls
import «tests».h62.item4.«generic-primitive-packets».SignedFixtures

/-! Regression: checked signed addition must neither wrap at either boundary nor
reject all valid mixed-sign inputs. Actual Source evaluation and public-selected
structured-EVM code retain their separate failure observations. The existing
populated signed runtime fixture supplies physical state and arbitrary tails;
this does not claim whole-session/world or fetched-EVM/gas adequacy. -/
namespace H62.PrimitivePackets.SignedAddCorrespondence
open Solidity Solidity.Evm Solidity.Evm.Memory Solidity.Lowering.V07
open Solidity.Backend.PrimitivePackets
open Source.SemanticsExamples (G0 F0)
abbrev U := SignedCheckedAdd.U

namespace Runtime
abbrev C := SignedMod.Controls.C
abbrev F := SignedMod.Controls.fragment
abbrev target := SignedMod.Controls.target
abbrev machine := SignedMod.Controls.machine
abbrev represented := SignedMod.Controls.initial
abbrev base := SignedMod.Controls.HeapFixture.base
end Runtime

def code : List Instr :=
  (SignedCheckedAdd.selected (C:=Runtime.C) 0 Runtime.F .here (.there .here)).code

theorem target_execution (f : SignedFixture U.lo U.hi) (tail : List Word) :
    run code {Runtime.machine f.lhs.val f.rhs.val f.lhs.property f.rhs.property with stack := tail} =
    match signedAdd f with
    | .ok z => .ok
        ({Runtime.machine f.lhs.val f.rhs.val f.lhs.property f.rhs.property with stack := tail}.push
          (.val (sword z.val))) 0
    | .error _ => .revert := by
  by_cases small : U.lo ≤ f.lhs.val+f.rhs.val ∧ f.lhs.val+f.rhs.val ≤ U.hi
  · rw [signedAdd_success f small]
    obtain ⟨word,repr,ran⟩ := SignedCheckedAdd.target_success
      (Runtime.target _ _ f.lhs.property f.rhs.property) .here (.there .here)
      f.lhs.val f.rhs.val f.lhs.property f.rhs.property rfl rfl small
      (Runtime.represented _ _ f.lhs.property f.rhs.property) tail
    have unique : word = .val (sword (f.lhs.val+f.rhs.val)) :=
      SignedMod.int_repr_unique repr (ReprV.int_word _)
    rw [unique] at ran
    exact ran
  · rw [signedAdd_refusal f small]
    exact SignedCheckedAdd.target_overflow
      (Runtime.target _ _ f.lhs.property f.rhs.property) .here (.there .here)
      f.lhs.val f.rhs.val f.lhs.property f.rhs.property rfl rfl small
      (Runtime.represented _ _ f.lhs.property f.rhs.property) tail

theorem source_execution (f : SignedFixture U.lo U.hi) (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) {F0 with checked := true} (fuel+3)
      (.binary .add (.local .here) (.local (.there .here)))).run
      (SignedCheckedAdd.Controls.input f.lhs.val f.rhs.val f.lhs.property f.rhs.property) =
    match signedAdd f with
    | .ok z =>
      (.ok (.val (.int z.val z.property)),
        SignedCheckedAdd.Controls.input f.lhs.val f.rhs.val f.lhs.property f.rhs.property)
    | .error _ =>
      (.error (.revert (Source.panicData .arithmetic)),
        SignedCheckedAdd.Controls.input f.lhs.val f.rhs.val f.lhs.property f.rhs.property) := by
  by_cases small : U.lo ≤ f.lhs.val+f.rhs.val ∧ f.lhs.val+f.rhs.val ≤ U.hi
  · rw [signedAdd_success f small]
    exact SignedCheckedAdd.source_success (G0 p) F0 fuel
      (SignedCheckedAdd.Controls.input _ _ f.lhs.property f.rhs.property) .here (.there .here)
      f.lhs.val f.rhs.val f.lhs.property f.rhs.property rfl rfl small
  · rw [signedAdd_refusal f small]
    exact SignedCheckedAdd.source_overflow (G0 p) F0 fuel
      (SignedCheckedAdd.Controls.input _ _ f.lhs.property f.rhs.property) .here (.there .here)
      f.lhs.val f.rhs.val f.lhs.property f.rhs.property rfl rfl small

theorem initial_representation (f : SignedFixture U.lo U.hi) :
    StateRepr 1 0 8 Runtime.F (Runtime.target _ _ f.lhs.property f.rhs.property)
      Runtime.base (Runtime.machine _ _ f.lhs.property f.rhs.property) :=
  Runtime.represented _ _ f.lhs.property f.rhs.property

theorem public_selection :
    Memory.compileVal 0 Runtime.F
      (SignedCheckedAdd.value (C:=Runtime.C) .here (.there .here)) =
      some (SignedCheckedAdd.selected 0 Runtime.F .here (.there .here)) :=
  SignedCheckedAdd.public_selection 0 Runtime.F .here (.there .here)

theorem table_target (c : OriginalSignedAddCase) (tail : List Word) :
    run code {Runtime.machine (signedAddFixture c).lhs.val (signedAddFixture c).rhs.val
      (signedAddFixture c).lhs.property (signedAddFixture c).rhs.property with stack := tail} =
    match signedAdd (signedAddFixture c) with
    | .ok z => .ok
        ({Runtime.machine (signedAddFixture c).lhs.val (signedAddFixture c).rhs.val
          (signedAddFixture c).lhs.property (signedAddFixture c).rhs.property with stack := tail}.push
            (.val (sword z.val))) 0
    | .error _ => .revert := target_execution (signedAddFixture c) tail

theorem table_source (c : OriginalSignedAddCase) (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) {F0 with checked := true} (fuel+3)
      (.binary .add (.local .here) (.local (.there .here)))).run
      (SignedCheckedAdd.Controls.input (signedAddFixture c).lhs.val (signedAddFixture c).rhs.val
        (signedAddFixture c).lhs.property (signedAddFixture c).rhs.property) =
    match signedAdd (signedAddFixture c) with
    | .ok z => (.ok (.val (.int z.val z.property)),
        SignedCheckedAdd.Controls.input (signedAddFixture c).lhs.val (signedAddFixture c).rhs.val
          (signedAddFixture c).lhs.property (signedAddFixture c).rhs.property)
    | .error _ => (.error (.revert (Source.panicData .arithmetic)),
        SignedCheckedAdd.Controls.input (signedAddFixture c).lhs.val (signedAddFixture c).rhs.val
          (signedAddFixture c).lhs.property (signedAddFixture c).rhs.property) :=
  source_execution (signedAddFixture c) p fuel

theorem reject_all_refuted (tail : List Word) :
    run code {Runtime.machine (-7) 9 (by decide) (by decide) with stack := tail} ≠ .revert := by
  have actual : run code {Runtime.machine (-7) 9 (by decide) (by decide) with stack := tail} =
      .ok ({Runtime.machine (-7) 9 (by decide) (by decide) with stack := tail}.push
        (.val (sword 2))) 0 := by
    simpa only [signedAddFixture,signedAdd] using target_execution (signedAddFixture .mixed_signs) tail
  rw [actual]
  intro impossible
  cases impossible

theorem positive_overflow_refuted (tail : List Word) (out : Machine) (cost : Nat) :
    run code {Runtime.machine U.hi 1 (by decide) (by decide) with stack := tail} ≠ .ok out cost := by
  have actual : run code {Runtime.machine U.hi 1 (by decide) (by decide) with stack := tail} = .revert := by
    simpa only [signedAddFixture,signedAdd] using target_execution (signedAddFixture .positive_overflow) tail
  rw [actual]
  intro impossible
  cases impossible

theorem negative_overflow_refuted (tail : List Word) (out : Machine) (cost : Nat) :
    run code {Runtime.machine U.lo (-1) (by decide) (by decide) with stack := tail} ≠ .ok out cost := by
  have actual : run code {Runtime.machine U.lo (-1) (by decide) (by decide) with stack := tail} = .revert := by
    simpa only [signedAddFixture,signedAdd] using target_execution (signedAddFixture .negative_overflow) tail
  rw [actual]
  intro impossible
  cases impossible

theorem low_fuel (f : SignedFixture U.lo U.hi) (p : Roadmap.Pipeline) :
    (Source.evalE (G0 p) {F0 with checked := true} 0
      (.binary .add (.local .here) (.local (.there .here)))).run
      (SignedCheckedAdd.Controls.input f.lhs.val f.rhs.val f.lhs.property f.rhs.property) =
      (.error .timeout,
        SignedCheckedAdd.Controls.input f.lhs.val f.rhs.val f.lhs.property f.rhs.property) := by rfl

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
end H62.PrimitivePackets.SignedAddCorrespondence
