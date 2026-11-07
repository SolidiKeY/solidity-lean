import Solidity.Backend.PrimitivePackets.Shifts.General
import Solidity.Backend.PrimitivePackets.BitNot.Controls

/-! Regression: unchecked uint256 shifts must preserve populated caller memory
and arbitrary saved stacks, keep count zero unchanged and saturate counts >=256.
The published unchecked Source restriction remains explicit. Actual public code,
local reads and input representation are constructed, not supplied runs; no
heap/world, checked-shift, gas/session or fetched-EVM adequacy is asserted. -/
namespace H62.PrimitivePackets.ShiftsCorrespondence
open Solidity Solidity.Evm Solidity.Evm.Memory
open Solidity.Backend.PrimitivePackets.Shifts
open Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture (F)

abbrev machine (x k : Fin W) :=
  Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.machine 256 (by decide)
    x.val k.val x.isLt k.isLt

def code (left : Bool) :=
  (General.selected (C := CompileExamples.C) 0 left
    (.here : Idx Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.Γ (.val .uint))
    (.there .here)).code

theorem reads (x k : Fin W) (saved : List Word) :
    ({machine x k with stack := saved} : Machine).mem 5 = .val x ∧
    ({machine x k with stack := saved} : Machine).mem 4 = .val k := by
  simp only [machine, Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.machine,
    writeMachine, upd]
  constructor <;> rfl

theorem execute (left : Bool) (x k : Fin W) (saved : List Word) :
    run (code left) {machine x k with stack := saved} =
      .ok ({machine x k with stack := saved}.push (.val (resultWord left x k))) 0 := by
  have hr := reads x k saved
  exact General.runtime_execution 0 left .here (.there .here) x k
    {machine x k with stack := saved} hr.1 hr.2

def source {E : Source.Env} {Δ : Source.RCtx} (x k : Fin W)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) :
    Source.EMState E (.int Source.IntTy.u256 :: .int Source.IntTy.u256 :: Δ) :=
  (.cons (.int x.val (word_range x)) (.cons (.int k.val (word_range k)) tail),state)

theorem joint {E : Source.Env} {Δ : Source.RCtx}
    (G : Source.Glob E) (fr : Source.Fr) (fuel : Nat) (left : Bool) (x k : Fin W)
    (tail : Source.Locals E.layout Δ) (state : Source.St E) (saved : List Word) :
    StateRepr 1 0 8 F
      (Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.target 256 (by decide)
        x.val k.val x.isLt k.isLt) CompileExamples.base (machine x k) ∧
    compileVal 0 F (General.target (C := CompileExamples.C) left .here (.there .here)) =
      some (General.selected 0 left .here (.there .here)) ∧
    (Source.evalE G {fr with checked := false} (fuel+3)
      (General.expression left .here (.there .here))).run (source x k tail state) =
      (.ok (.val (.int (resultWord left x k).val (word_range (resultWord left x k)))),
        source x k tail state) ∧
    run (code left) {machine x k with stack := saved} =
      .ok ({machine x k with stack := saved}.push (.val (resultWord left x k))) 0 := by
  exact ⟨Solidity.Backend.PrimitivePackets.BitNot.Controls.Fixture.represented
      256 (by decide) x.val k.val x.isLt k.isLt,
    General.public_selection 0 left .here (.there .here),
    General.source_execution G fr fuel left .here (.there .here)
      (source x k tail state).1 state x k rfl rfl, execute left x k saved⟩

theorem zero_count (left : Bool) (x : Fin W) (saved : List Word) :
    run (code left) {machine x ⟨0,by decide⟩ with stack := saved} =
      .ok ({machine x ⟨0,by decide⟩ with stack := saved}.push (.val x)) 0 := by
  rw [execute, result_zero_count]

theorem saturated (left : Bool) (x k : Fin W) (large : 256 ≤ k.val) (saved : List Word) :
    run (code left) {machine x k with stack := saved} =
      .ok ({machine x k with stack := saved}.push (.val ⟨0,by decide⟩)) 0 := by
  rw [execute, result_saturated left x k large]

theorem reject_all_refuted (left : Bool) (x k : Fin W) (saved : List Word) :
    run (code left) {machine x k with stack := saved} ≠ .revert := by
  rw [execute]
  intro h
  cases h

#print axioms reads
#print axioms execute
#print axioms joint
#print axioms zero_count
#print axioms saturated
#print axioms reject_all_refuted
end H62.PrimitivePackets.ShiftsCorrespondence
