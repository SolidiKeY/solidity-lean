import Solidity.Backend.PrimitivePackets.SignedMod.Controls

/-! Regression: signed remainder must keep the dividend sign and must succeed
for minimum signed integer modulo -1, while zero divisors still panic in either
checked mode. These additive laws use public selection and constructed populated
target memory. Source state/tails and globals remain general; no whole-world,
gas or fetched-EVM correspondence is inferred from primitive content agreement. -/
namespace H62.PrimitivePackets.SignedModCorrespondence
open Solidity Solidity.Evm Solidity.Evm.Memory
open Solidity.Backend.PrimitivePackets.SignedMod

-- Source locals are constructed, so operand evaluation is not an assumed run.
def source {E : Source.Env} {Δ : Source.RCtx} (x y : Int)
    (hx : Range x) (hy : Range y) (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    Source.EMState E (.int ty :: .int ty :: Δ) :=
  (.cons (.int x hx) (.cons (.int y hy) tail), state)

theorem joint_success {E : Source.Env} {Δ : Source.RCtx}
    (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat)
    (tail : Source.Locals E.layout Δ) (state : Source.St E)
    (x y : Int) (hx : Range x) (hy : Range y) (nonzero : y ≠ 0) (saved : List Word) :
    compileVal 0 Solidity.Backend.PrimitivePackets.SignedMod.Controls.fragment (expression (C := Solidity.Backend.PrimitivePackets.SignedMod.Controls.C) .here (.there .here)) =
      some (selected (C := Solidity.Backend.PrimitivePackets.SignedMod.Controls.C) 0 Solidity.Backend.PrimitivePackets.SignedMod.Controls.fragment .here (.there .here)) ∧
    (Source.evalE G fr (fuel+3) (.binary .mod (.local .here) (.local (.there .here)))).run
      (source x y hx hy tail state) =
      (.ok (.val (.int (x.tmod y) (remainder_range x y hy nonzero))), source x y hx hy tail state) ∧
    run Solidity.Backend.PrimitivePackets.SignedMod.Controls.code {Solidity.Backend.PrimitivePackets.SignedMod.Controls.machine x y hx hy with stack := w[77] :: saved} =
      .ok {Solidity.Backend.PrimitivePackets.SignedMod.Controls.machine x y hx hy with stack := .val (sword (x.tmod y)) :: w[77] :: saved} 0 := by
  exact ⟨public_selection 0 Solidity.Backend.PrimitivePackets.SignedMod.Controls.fragment .here (.there .here),
    source_locals_nonzero G fr fuel (source x y hx hy tail state) .here (.there .here)
      x y hx hy rfl rfl nonzero, Solidity.Backend.PrimitivePackets.SignedMod.Controls.target_success x y hx hy nonzero saved⟩

theorem joint_zero {E : Source.Env} {Δ : Source.RCtx}
    (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat)
    (tail : Source.Locals E.layout Δ) (state : Source.St E)
    (x : Int) (hx : Range x) (saved : List Word) :
    (Source.evalE G fr (fuel+3) (.binary .mod (.local .here) (.local (.there .here)))).run
      (source x 0 hx (by decide) tail state) =
      (.error (.revert (Source.panicData .divZero)), source x 0 hx (by decide) tail state) ∧
    run Solidity.Backend.PrimitivePackets.SignedMod.Controls.code {Solidity.Backend.PrimitivePackets.SignedMod.Controls.machine x 0 hx (by decide) with stack := w[77] :: saved} = .revert := by
  exact ⟨source_locals_zero G fr fuel (source x 0 hx (by decide) tail state)
    .here (.there .here) x hx (by decide) rfl rfl, Solidity.Backend.PrimitivePackets.SignedMod.Controls.target_failure x hx saved⟩

theorem low_fuel {E : Source.Env} {Δ : Source.RCtx}
    (G : Source.Glob E) (fr : Source.Fr) (tail : Source.Locals E.layout Δ) (state : Source.St E)
    (x y : Int) (hx : Range x) (hy : Range y) :
    (Source.evalE G fr 0 (.binary .mod (.local .here) (.local (.there .here)))).run
      (source x y hx hy tail state) = (.error .timeout, source x y hx hy tail state) := rfl

theorem negative_dividend_run (saved : List Word) :
    run Solidity.Backend.PrimitivePackets.SignedMod.Controls.code {Solidity.Backend.PrimitivePackets.SignedMod.Controls.machine (-7) 3 (by decide) (by decide) with stack := w[77] :: saved} =
      .ok {Solidity.Backend.PrimitivePackets.SignedMod.Controls.machine (-7) 3 (by decide) (by decide) with stack := .val (sword (-1)) :: w[77] :: saved} 0 :=
  Solidity.Backend.PrimitivePackets.SignedMod.Controls.target_success (-7) 3 (by decide) (by decide) (by decide) saved

theorem reject_all_refuted (saved : List Word) :
    run Solidity.Backend.PrimitivePackets.SignedMod.Controls.code {Solidity.Backend.PrimitivePackets.SignedMod.Controls.machine (-7) 3 (by decide) (by decide) with stack := w[77] :: saved} ≠ .revert := by
  rw [negative_dividend_run saved]
  intro h
  cases h

theorem minimum_run (saved : List Word) :
    run Solidity.Backend.PrimitivePackets.SignedMod.Controls.code
      {Solidity.Backend.PrimitivePackets.SignedMod.Controls.machine (-(H : Int)) (-1)
        (by decide) (by decide) with stack := w[77] :: saved} =
      .ok {Solidity.Backend.PrimitivePackets.SignedMod.Controls.machine (-(H : Int)) (-1)
        (by decide) (by decide) with stack := .val (sword 0) :: w[77] :: saved} 0 := by
  have h := Solidity.Backend.PrimitivePackets.SignedMod.Controls.target_success
    (-(H : Int)) (-1) (by decide) (by decide) (by decide) saved
  simpa only [minimum_remainder_neg_one] using h

#print axioms minimum_run
#print axioms joint_success
#print axioms joint_zero
#print axioms low_fuel
#print axioms negative_dividend_run
#print axioms reject_all_refuted
end H62.PrimitivePackets.SignedModCorrespondence
