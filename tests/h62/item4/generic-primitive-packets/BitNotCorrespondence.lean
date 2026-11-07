import Solidity.Backend.PrimitivePackets.BitNot.Controls

/-! Regression: unsigned complement must clean to the declared byte width,
preserve populated caller memory and all saved stacks, and evaluate independent
Source locals in either pipeline/check mode. Involution rules out an incorrect
arithmetic classifier. Existing mask/index/refusal controls stay unchanged;
this primitive content law does not assert a heap/world or gas/session map. -/
namespace H62.PrimitivePackets.BitNotCorrespondence
open Solidity Solidity.Evm Solidity.Evm.Memory
open Solidity.Lowering.V07
open Solidity.Backend.PrimitivePackets.BitNot
open UnsignedNarrowing (ty)

theorem narrow_result (bits x : Nat) (bound : x < 2^bits) :
    Controls.Fixture.resultNat bits x < 2^bits := by
  have positive := Source.two_pow_pos bits
  unfold Controls.Fixture.resultNat
  omega

theorem involution (bits x : Nat) (bound : x < 2^bits) :
    Controls.Fixture.resultNat bits (Controls.Fixture.resultNat bits x) = x := by
  unfold Controls.Fixture.resultNat
  omega

def source {E : Source.Env} {Δ : Source.RCtx}
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x : Nat) (bound : x < 2^bits) (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    Source.EMState E (.int (ty bits valid) :: Δ) :=
  (.cons (.int x (Controls.Fixture.nat_range bits valid x bound)) tail,state)

theorem joint {E : Source.Env} {Δ : Source.RCtx}
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x y : Nat) (hx : x < 2^bits) (hy : y < 2^bits)
    (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) (saved : List Word) :
    compileVal 0 Controls.Fixture.F (value (C := CompileExamples.C) bits .here) =
      some (selected bits 0 Controls.Fixture.F .here) ∧
    (Source.evalE G fr (fuel+2) (.unary .bitNot (.local .here))).run
      (source bits valid x hx tail state) =
      (.ok (.val (Source.intWrap (ty bits valid) (-(x : Int)-1))),
        source bits valid x hx tail state) ∧
    (ty bits valid).wrap (-(x : Int)-1) = (Controls.Fixture.resultNat bits x : Int) ∧
    run (Controls.Fixture.code bits)
      {Controls.Fixture.machine bits valid x y hx hy with stack := saved} =
      .ok ({Controls.Fixture.machine bits valid x y hx hy with stack := saved}.push
        (.val ⟨Controls.Fixture.resultNat bits x,Controls.Fixture.result_range bits valid x⟩)) 0 := by
  exact ⟨public_selection bits 0 Controls.Fixture.F .here,
    source_success bits valid G fr fuel (source bits valid x hx tail state) .here x
      (Controls.Fixture.nat_range bits valid x hx) rfl,
    Controls.Fixture.computed bits valid x hx, Controls.Fixture.result bits valid x y hx hy saved⟩

theorem reject_all_refuted (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x y : Nat) (hx : x < 2^bits) (hy : y < 2^bits) (saved : List Word) :
    run (Controls.Fixture.code bits)
      {Controls.Fixture.machine bits valid x y hx hy with stack := saved} ≠ .revert := by
  rw [Controls.Fixture.result bits valid x y hx hy saved]
  intro h
  cases h

theorem low_fuel {E : Source.Env} {Δ : Source.RCtx}
    (bits : Nat) (valid : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256)
    (x : Nat) (bound : x < 2^bits) (G : Source.Glob E) (fr : Source.Fr)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    (Source.evalE G fr 0 (.unary .bitNot (.local .here))).run
      (source bits valid x bound tail state) =
      (.error .timeout, source bits valid x bound tail state) := rfl

#print axioms narrow_result
#print axioms involution
#print axioms joint
#print axioms reject_all_refuted
#print axioms low_fuel
end H62.PrimitivePackets.BitNotCorrespondence
