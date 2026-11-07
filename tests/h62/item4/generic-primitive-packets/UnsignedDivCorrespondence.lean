import Solidity.Backend.PrimitivePackets.UnsignedDiv.Witness
import Solidity.Backend.PrimitivePackets.CheckedMul.Controls
import «tests».h62.item4.«generic-primitive-packets».UnsignedDivFixtures

/-! Regression: selected unsigned DIV/MOD must refuse a zero divisor, preserve
nonempty caller memory and arbitrary saved stacks, and agree with independent
Source execution in checked or unchecked frames. Source globals, local tails and
state remain general. This is primitive content correspondence, not an arbitrary
heap/world map or fetched-EVM/gas/session adequacy. -/
namespace H62.PrimitivePackets.UnsignedDivCorrespondence
open Solidity Solidity.Evm Solidity.Evm.Memory
open Solidity.Backend.PrimitivePackets
open Source.SemanticsExamples (G0 F0 s0)

namespace Runtime
abbrev C := CheckedMul.Populated.C
abbrev Γ := CheckedMul.Populated.Γ
abbrev F := CheckedMul.Controls.Fixture.F
abbrev native := CheckedMul.Controls.Fixture.u
abbrev target := CheckedMul.Controls.Fixture.target
abbrev machine := CheckedMul.Controls.Fixture.machine
abbrev represented := CheckedMul.Controls.Fixture.represented
abbrev base := CheckedMul.Populated.base
end Runtime

theorem native_round_trip (v : UnsignedDiv.Uint) :
    Runtime.native (UnsignedDiv.localWord v).val (UnsignedDiv.localWord v).isLt = v := by
  apply Subtype.ext
  have h := Backend.Scalar.uint_range v
  change (v.val.toNat : Int) = v.val
  omega

theorem original_source_inputs {D : Source.Layout} {Δ : Source.RCtx}
    (a d : UnsignedDiv.Uint) (tail : Source.Locals D Δ) :
    UnsignedDiv.sourceLocals (Runtime.native (UnsignedDiv.localWord a).val (UnsignedDiv.localWord a).isLt)
      (Runtime.native (UnsignedDiv.localWord d).val (UnsignedDiv.localWord d).isLt) tail =
      UnsignedDiv.sourceLocals a d tail := by
  rw [native_round_trip, native_round_trip]

theorem initial_representation (f : SubFixture W) (saved : List Word) :
    StateRepr 1 0 8 Runtime.F (Runtime.target _ _ f.lhs.isLt f.rhs.isLt)
      Runtime.base {Runtime.machine _ _ f.lhs.isLt f.rhs.isLt with stack := saved} :=
  (Runtime.represented _ _ f.lhs.isLt f.rhs.isLt).stack saved

namespace Division
def code : List Instr := (UnsignedDiv.selectedDiv (C:=Runtime.C) (Γ:=Runtime.Γ) 0 Runtime.F).code

theorem public_selection :
    Memory.compileVal 0 Runtime.F (UnsignedDiv.modelDiv Runtime.C Runtime.Γ) =
      some (UnsignedDiv.selectedDiv 0 Runtime.F) := UnsignedDiv.select_div 0 Runtime.F

theorem joint_execution {E : Source.Env} {Δ : Source.RCtx}
    (f : SubFixture W) (saved : List Word) (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    Memory.compileVal 0 Runtime.F (UnsignedDiv.modelDiv Runtime.C Runtime.Γ) = some (UnsignedDiv.selectedDiv 0 Runtime.F) ∧
    (Source.evalE G fr (fuel+3) (UnsignedDiv.sourceDiv E Δ)).run
      (UnsignedDiv.sourceLocals (Runtime.native _ f.lhs.isLt) (Runtime.native _ f.rhs.isLt) tail,state) =
      (match unsignedQuotient f with
       | .ok z => (.ok (.val (UnsignedDiv.sourceUInt E.layout (Runtime.native z.val z.isLt))),
           (UnsignedDiv.sourceLocals (Runtime.native _ f.lhs.isLt) (Runtime.native _ f.rhs.isLt) tail,state))
       | .error _ => (.error (.revert (Source.panicData .divZero)),
           (UnsignedDiv.sourceLocals (Runtime.native _ f.lhs.isLt) (Runtime.native _ f.rhs.isLt) tail,state))) ∧
    run code {Runtime.machine _ _ f.lhs.isLt f.rhs.isLt with stack := saved} =
      (match unsignedQuotient f with
       | .ok z => .ok ({Runtime.machine _ _ f.lhs.isLt f.rhs.isLt with stack := saved}.push (.val z)) 0
       | .error _ => .revert) := by
  unfold unsignedQuotient
  by_cases zero : f.rhs.val = 0
  · rw [guardedUnsigned_refusal Nat.div Nat.div_le_self f zero]
    have hz : (Runtime.target _ _ f.lhs.isLt f.rhs.isLt).env.2.1.val = 0 := by
      change (f.rhs.val : Int) = 0
      omega
    have packet := UnsignedDiv.division_zero_packet (initial_representation f saved) G fr fuel tail state hz
    exact ⟨packet.2.1,packet.1,packet.2.2⟩
  · rw [guardedUnsigned_success Nat.div Nat.div_le_self f zero]
    have hz : (Runtime.target _ _ f.lhs.isLt f.rhs.isLt).env.2.1.val ≠ 0 := by
      change (f.rhs.val : Int) ≠ 0
      omega
    obtain ⟨selection,v,word,value,sourceRun,repr,targetRun⟩ :=
      UnsignedDiv.division_packet (initial_representation f saved) G fr fuel tail state hz
    have sameValue : v = Runtime.native (f.lhs.val / f.rhs.val)
        (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) f.lhs.isLt) := by
      apply Subtype.ext
      change v.val = ((f.lhs.val / f.rhs.val : Nat) : Int) at value
      exact value
    rw [sameValue] at sourceRun repr
    rcases repr with ⟨actual,rfl,content⟩
    have sameWord : actual = (⟨f.lhs.val / f.rhs.val,
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _) f.lhs.isLt⟩ : Fin W) := by
      apply Fin.ext
      change actual.val = f.lhs.val / f.rhs.val
      change ((f.lhs.val / f.rhs.val : Nat) : Int) = actual.val at content
      omega
    rw [sameWord] at targetRun
    exact ⟨selection,sourceRun,targetRun⟩

theorem target_execution (f : SubFixture W) (saved : List Word) :
    run code {Runtime.machine _ _ f.lhs.isLt f.rhs.isLt with stack := saved} =
      (match unsignedQuotient f with
       | .ok z => .ok ({Runtime.machine _ _ f.lhs.isLt f.rhs.isLt with stack := saved}.push (.val z)) 0
       | .error _ => .revert) :=
  (joint_execution f saved (G0 .legacy) F0 0 .nil s0).2.2

theorem source_execution {E : Source.Env} {Δ : Source.RCtx}
    (f : SubFixture W) (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    (Source.evalE G fr (fuel+3) (UnsignedDiv.sourceDiv E Δ)).run
      (UnsignedDiv.sourceLocals (Runtime.native _ f.lhs.isLt) (Runtime.native _ f.rhs.isLt) tail,state) =
      (match unsignedQuotient f with
       | .ok z => (.ok (.val (UnsignedDiv.sourceUInt E.layout (Runtime.native z.val z.isLt))),
           (UnsignedDiv.sourceLocals (Runtime.native _ f.lhs.isLt) (Runtime.native _ f.rhs.isLt) tail,state))
       | .error _ => (.error (.revert (Source.panicData .divZero)),
           (UnsignedDiv.sourceLocals (Runtime.native _ f.lhs.isLt) (Runtime.native _ f.rhs.isLt) tail,state))) :=
  (joint_execution f [] G fr fuel tail state).2.1

/-- New regression input, not an additional original-case census row. -/
theorem regular (saved : List Word) :
    run code {Runtime.machine 7 2 (by decide) (by decide) with stack := saved} =
      .ok ({Runtime.machine 7 2 (by decide) (by decide) with stack := saved}.push w[3]) 0 := by
  simpa only [unsignedQuotient,guardedUnsignedResult] using
    target_execution (⟨⟨7,by decide⟩,⟨2,by decide⟩⟩ : SubFixture W) saved

theorem reject_all_refuted (saved : List Word) :
    run code {Runtime.machine 7 2 (by decide) (by decide) with stack := saved} ≠ .revert := by
  rw [regular]
  intro impossible
  cases impossible

theorem accept_zero_refuted (saved : List Word) (out : Machine) (cost : Nat) :
    run code {Runtime.machine 7 0 (by decide) (by decide) with stack := saved} ≠ .ok out cost := by
  have actual : run code {Runtime.machine 7 0 (by decide) (by decide) with stack := saved} = .revert := by
    simpa only [unsignedQuotient,guardedUnsignedResult] using
      target_execution (⟨⟨7,by decide⟩,⟨0,by decide⟩⟩ : SubFixture W) saved
  rw [actual]
  intro impossible
  cases impossible

theorem low_fuel {E : Source.Env} {Δ : Source.RCtx}
    (f : SubFixture W) (G : Source.Glob E) (fr : Source.Fr)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    (Source.evalE G fr 0 (UnsignedDiv.sourceDiv E Δ)).run
      (UnsignedDiv.sourceLocals (Runtime.native _ f.lhs.isLt) (Runtime.native _ f.rhs.isLt) tail,state) =
      (.error .timeout,
        (UnsignedDiv.sourceLocals (Runtime.native _ f.lhs.isLt) (Runtime.native _ f.rhs.isLt) tail,state)) := by rfl

#print axioms public_selection
#print axioms joint_execution
#print axioms target_execution
#print axioms source_execution
#print axioms regular
#print axioms reject_all_refuted
#print axioms accept_zero_refuted
#print axioms low_fuel
end Division

namespace Remainder
def code : List Instr := (UnsignedDiv.selectedMod (C:=Runtime.C) (Γ:=Runtime.Γ) 0 Runtime.F).code

theorem public_selection :
    Memory.compileVal 0 Runtime.F (UnsignedDiv.modelMod Runtime.C Runtime.Γ) =
      some (UnsignedDiv.selectedMod 0 Runtime.F) := UnsignedDiv.select_mod 0 Runtime.F

theorem joint_execution {E : Source.Env} {Δ : Source.RCtx}
    (f : SubFixture W) (saved : List Word) (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    Memory.compileVal 0 Runtime.F (UnsignedDiv.modelMod Runtime.C Runtime.Γ) = some (UnsignedDiv.selectedMod 0 Runtime.F) ∧
    (Source.evalE G fr (fuel+3) (UnsignedDiv.sourceMod E Δ)).run
      (UnsignedDiv.sourceLocals (Runtime.native _ f.lhs.isLt) (Runtime.native _ f.rhs.isLt) tail,state) =
      (match unsignedRemainder f with
       | .ok z => (.ok (.val (UnsignedDiv.sourceUInt E.layout (Runtime.native z.val z.isLt))),
           (UnsignedDiv.sourceLocals (Runtime.native _ f.lhs.isLt) (Runtime.native _ f.rhs.isLt) tail,state))
       | .error _ => (.error (.revert (Source.panicData .divZero)),
           (UnsignedDiv.sourceLocals (Runtime.native _ f.lhs.isLt) (Runtime.native _ f.rhs.isLt) tail,state))) ∧
    run code {Runtime.machine _ _ f.lhs.isLt f.rhs.isLt with stack := saved} =
      (match unsignedRemainder f with
       | .ok z => .ok ({Runtime.machine _ _ f.lhs.isLt f.rhs.isLt with stack := saved}.push (.val z)) 0
       | .error _ => .revert) := by
  unfold unsignedRemainder
  by_cases zero : f.rhs.val = 0
  · rw [guardedUnsigned_refusal Nat.mod Nat.mod_le f zero]
    have hz : (Runtime.target _ _ f.lhs.isLt f.rhs.isLt).env.2.1.val = 0 := by
      change (f.rhs.val : Int) = 0
      omega
    have packet := UnsignedDiv.remainder_zero_packet (initial_representation f saved) G fr fuel tail state hz
    exact ⟨packet.2.1,packet.1,packet.2.2⟩
  · rw [guardedUnsigned_success Nat.mod Nat.mod_le f zero]
    have hz : (Runtime.target _ _ f.lhs.isLt f.rhs.isLt).env.2.1.val ≠ 0 := by
      change (f.rhs.val : Int) ≠ 0
      omega
    obtain ⟨selection,v,word,value,sourceRun,repr,targetRun⟩ :=
      UnsignedDiv.remainder_packet (initial_representation f saved) G fr fuel tail state hz
    have sameValue : v = Runtime.native (f.lhs.val % f.rhs.val)
        (Nat.lt_of_le_of_lt (Nat.mod_le _ _) f.lhs.isLt) := by
      apply Subtype.ext
      change v.val = ((f.lhs.val % f.rhs.val : Nat) : Int) at value
      exact value
    rw [sameValue] at sourceRun repr
    rcases repr with ⟨actual,rfl,content⟩
    have sameWord : actual = (⟨f.lhs.val % f.rhs.val,
        Nat.lt_of_le_of_lt (Nat.mod_le _ _) f.lhs.isLt⟩ : Fin W) := by
      apply Fin.ext
      change actual.val = f.lhs.val % f.rhs.val
      change ((f.lhs.val % f.rhs.val : Nat) : Int) = actual.val at content
      omega
    rw [sameWord] at targetRun
    exact ⟨selection,sourceRun,targetRun⟩

theorem target_execution (f : SubFixture W) (saved : List Word) :
    run code {Runtime.machine _ _ f.lhs.isLt f.rhs.isLt with stack := saved} =
      (match unsignedRemainder f with
       | .ok z => .ok ({Runtime.machine _ _ f.lhs.isLt f.rhs.isLt with stack := saved}.push (.val z)) 0
       | .error _ => .revert) :=
  (joint_execution f saved (G0 .legacy) F0 0 .nil s0).2.2

theorem source_execution {E : Source.Env} {Δ : Source.RCtx}
    (f : SubFixture W) (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    (Source.evalE G fr (fuel+3) (UnsignedDiv.sourceMod E Δ)).run
      (UnsignedDiv.sourceLocals (Runtime.native _ f.lhs.isLt) (Runtime.native _ f.rhs.isLt) tail,state) =
      (match unsignedRemainder f with
       | .ok z => (.ok (.val (UnsignedDiv.sourceUInt E.layout (Runtime.native z.val z.isLt))),
           (UnsignedDiv.sourceLocals (Runtime.native _ f.lhs.isLt) (Runtime.native _ f.rhs.isLt) tail,state))
       | .error _ => (.error (.revert (Source.panicData .divZero)),
           (UnsignedDiv.sourceLocals (Runtime.native _ f.lhs.isLt) (Runtime.native _ f.rhs.isLt) tail,state))) :=
  (joint_execution f [] G fr fuel tail state).2.1

/-- New regression input, not an additional original-case census row. -/
theorem regular (saved : List Word) :
    run code {Runtime.machine 7 2 (by decide) (by decide) with stack := saved} =
      .ok ({Runtime.machine 7 2 (by decide) (by decide) with stack := saved}.push w[1]) 0 := by
  simpa only [unsignedRemainder,guardedUnsignedResult] using
    target_execution (⟨⟨7,by decide⟩,⟨2,by decide⟩⟩ : SubFixture W) saved

theorem reject_all_refuted (saved : List Word) :
    run code {Runtime.machine 7 2 (by decide) (by decide) with stack := saved} ≠ .revert := by
  rw [regular]
  intro impossible
  cases impossible

theorem accept_zero_refuted (saved : List Word) (out : Machine) (cost : Nat) :
    run code {Runtime.machine 7 0 (by decide) (by decide) with stack := saved} ≠ .ok out cost := by
  have actual : run code {Runtime.machine 7 0 (by decide) (by decide) with stack := saved} = .revert := by
    simpa only [unsignedRemainder,guardedUnsignedResult] using
      target_execution (⟨⟨7,by decide⟩,⟨0,by decide⟩⟩ : SubFixture W) saved
  rw [actual]
  intro impossible
  cases impossible

theorem low_fuel {E : Source.Env} {Δ : Source.RCtx}
    (f : SubFixture W) (G : Source.Glob E) (fr : Source.Fr)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    (Source.evalE G fr 0 (UnsignedDiv.sourceMod E Δ)).run
      (UnsignedDiv.sourceLocals (Runtime.native _ f.lhs.isLt) (Runtime.native _ f.rhs.isLt) tail,state) =
      (.error .timeout,
        (UnsignedDiv.sourceLocals (Runtime.native _ f.lhs.isLt) (Runtime.native _ f.rhs.isLt) tail,state)) := by rfl

#print axioms public_selection
#print axioms joint_execution
#print axioms target_execution
#print axioms source_execution
#print axioms regular
#print axioms reject_all_refuted
#print axioms accept_zero_refuted
#print axioms low_fuel
end Remainder

#print axioms native_round_trip
#print axioms original_source_inputs
#print axioms initial_representation
end H62.PrimitivePackets.UnsignedDivCorrespondence
