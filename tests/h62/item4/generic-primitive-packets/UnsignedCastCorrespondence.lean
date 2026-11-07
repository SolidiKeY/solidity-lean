import Solidity.Backend.PrimitivePackets.UnsignedCast.Transport
import Solidity.Backend.PrimitivePackets.BitNot.Controls

/-! Regression: explicit uint256 narrowing must wrap even in checked frames,
preserve populated caller memory and arbitrary saved stacks, and retain the
physical representation after execution. The original strict-smaller-width
profile (8..248 byte multiples) is unchanged. No widening/uint256 identity,
heap/world/session/gas or fetched-EVM adequacy is asserted. -/
namespace H62.PrimitivePackets.UnsignedCastCorrespondence
open Solidity Solidity.Evm Solidity.Evm.Memory Solidity.Lowering.V07
open Solidity.Backend.PrimitivePackets.UnsignedCast
open Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture (F)

def range (x : Fin W) : Source.IntTy.u256.lo ≤ (x.val : Int) ∧
    (x.val : Int) ≤ Source.IntTy.u256.hi :=
  Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.nat_range 256 (by decide) x.val x.isLt
abbrev target (x y : Fin W) :=
  Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.target 256 (by decide) x.val y.val x.isLt y.isLt
abbrev machine (x y : Fin W) :=
  Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.machine 256 (by decide) x.val y.val x.isLt y.isLt
abbrev result (bits : Nat) (legal : Legal bits) (x : Fin W) :=
  integerValue (targetTy bits legal) ((targetTy bits legal).wrap (x.val : Int))
    ((targetTy bits legal).wrap_mem (x.val : Int))
def code (bits : Nat) (legal : Legal bits) :=
  (selected (C := CompileExamples.C) 0 F bits legal .here).code

theorem execute (bits : Nat) (legal : Legal bits) (x y : Fin W) (saved : List Word) :
    run (code bits legal) {machine x y with stack := saved} =
      .ok ({machine x y with stack := saved}.push (.val (result bits legal x).word)) 0 :=
  machine_run (target x y) 0 1 8 F CompileExamples.base (machine x y)
    (Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.represented
      256 (by decide) x.val y.val x.isLt y.isLt)
    bits legal .here x.val (range x) rfl saved

theorem post_representation (bits : Nat) (legal : Legal bits) (x y : Fin W) (saved : List Word) :
    StateRepr 1 0 8 F (target x y) CompileExamples.base
      ({machine x y with stack := saved}.push (.val (result bits legal x).word)) :=
  ((Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.represented
    256 (by decide) x.val y.val x.isLt y.isLt).stack saved).push _

def source {E : Source.Env} {Δ : Source.RCtx} (x : Fin W)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    Source.EMState E (.int Source.IntTy.u256 :: Δ) := (.cons (.int x.val (range x)) tail,state)

theorem joint {E : Source.Env} {Δ : Source.RCtx}
    (bits : Nat) (legal : Legal bits) (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat)
    (x y : Fin W) (tail : Source.Locals E.layout Δ) (state : Source.St E) (saved : List Word) :
    compileVal 0 F (value (C := CompileExamples.C) bits legal .here) =
      some (selected 0 F bits legal .here) ∧
    (Source.evalE G fr (fuel+2) (expression bits legal .here)).run (source x tail state) =
      (.ok (.val (Source.intWrap (targetTy bits legal) x.val)),source x tail state) ∧
    run (code bits legal) {machine x y with stack := saved} =
      .ok ({machine x y with stack := saved}.push (.val (result bits legal x).word)) 0 ∧
    StateRepr 1 0 8 F (target x y) CompileExamples.base
      ({machine x y with stack := saved}.push (.val (result bits legal x).word)) :=
  ⟨compile_selection 0 F bits legal .here,
    source_run G fr fuel (source x tail state) bits legal .here x.val (range x) rfl,
    execute bits legal x y saved, post_representation bits legal x y saved⟩

theorem reject_all_refuted (bits : Nat) (legal : Legal bits) (x y : Fin W) (saved : List Word) :
    run (code bits legal) {machine x y with stack := saved} ≠ .revert := by
  rw [execute]
  intro h
  cases h

theorem low_fuel {E : Source.Env} {Δ : Source.RCtx}
    (bits : Nat) (legal : Legal bits) (G : Source.Glob E) (fr : Source.Fr)
    (x : Fin W) (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    (Source.evalE G fr 0 (expression bits legal .here)).run (source x tail state) =
      (.error .timeout,source x tail state) ∧
    (Source.evalE G fr 1 (expression bits legal .here)).run (source x tail state) =
      (.error .timeout,source x tail state) :=
  source_timeout G fr (source x tail state) bits legal .here

#print axioms execute
#print axioms post_representation
#print axioms joint
#print axioms reject_all_refuted
#print axioms low_fuel
end H62.PrimitivePackets.UnsignedCastCorrespondence
