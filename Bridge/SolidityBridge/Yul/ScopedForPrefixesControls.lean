import SolidityBridge.Yul.ScopedForPrefixes
import SolidityBridge.Yul.ScopedForAdequacyControls

/-! Genuine prefixes of the literal-true original scoped/switch FOR, with a
separately realized actual prelude. Only bounded prefixes are runtime-tested. -/
namespace SolidityBridge.Yul.ScopedForPrefixes.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed Solidity.Yul.Compilation ProducerExpressions
open ScopedFor.Controls ScopedForAdequacy.Controls

def cc := (foreverPrepared.test.lowered.code 0).get (by rfl)
def bodyBlock := foreverPrepared.inside.emit.get (by rfl)
def postBlock := foreverPrepared.after.emit.get (by rfl)
def preBlock := foreverPrepared.before.emit.get (by rfl)
def condSlice := (OccurrenceSelection.selectCode cc).get (by rfl)
def bodySelected := (LoopSelection.selectBlock (.seq bodyBlock postBlock)).get (by rfl)
def preSelected := (LoopSelection.selectBlock preBlock).get (by rfl)

/-- The actual compiled prelude runs once and resets the counter without
changing the dirty accumulator, caller tail or any nonstack machine field. -/
theorem prelude (initial : Scalar.Word) (caller : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([initial,dirty] ++ caller)) :
    Evm.run preSelected.realization.ir m = .ok {m with stack := irStack ([2,dirty] ++ caller)} 0 :=
  preSelected.realization.execute _ _ m represented
    (foreverPrepared.before.structured preBlock (Option.some_get (by rfl)).symm #v[initial,dirty] caller)

/-- All finite prefixes, including zero, at a loop-entry local frame. The
source/compiler components and selected instruction certificates are concrete. -/
theorem every_prefix (count : Nat) (locals : Vector Scalar.Word 2) (caller : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack (locals.toList ++ caller)) :
    Evm.loopIterN (Evm.run condSlice.ir) (Evm.run bodySelected.realization.ir) count m =
      .inl {m with stack := irStack ((Nat.repeat (ScopedFor.update foreverPrepared) count locals).toList ++ caller)} :=
  macro_prefix foreverPrepared cc postBlock bodyBlock (Option.some_get (by rfl)).symm
    (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm condSlice bodySelected.realization
    count locals caller (by intro j bound; change (1 : Scalar.Word) ≠ 0; decide) m represented

/-- Prefixes begin after the separately proved prelude, without silently
identifying initial source locals with the counter-reset loop-entry locals. -/
theorem after_prelude (count : Nat) (initial : Scalar.Word) (caller : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([initial,dirty] ++ caller)) :
    Evm.run preSelected.realization.ir m = .ok {m with stack := irStack ([2,dirty] ++ caller)} 0 ∧
    Evm.loopIterN (Evm.run condSlice.ir) (Evm.run bodySelected.realization.ir) count
      {m with stack := irStack ([2,dirty] ++ caller)} =
      .inl {m with stack := irStack ((Nat.repeat (ScopedFor.update foreverPrepared) count #v[2,dirty]).toList ++ caller)} :=
  ⟨prelude initial caller m represented,every_prefix count #v[2,dirty] caller _ rfl⟩

theorem no_finite_loop_outcome (locals : Vector Scalar.Word 2) (caller : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack (locals.toList ++ caller)) :
    Evm.loopRun (Evm.run condSlice.ir) (Evm.run bodySelected.realization.ir) m = .fault :=
  loop_no_finite_outcome foreverPrepared cc postBlock bodyBlock (Option.some_get (by rfl)).symm
    (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm condSlice bodySelected.realization
    locals caller (by intro j; change (1 : Scalar.Word) ≠ 0; decide) m represented

/-- Even after the local counter first becomes zero, the actual literal-true
condition keeps this program running; the old local-condition loop terminates. -/
theorem two_turns : Nat.repeat (ScopedFor.update foreverPrepared) 2 #v[2,dirty] = #v[0,dirty+11] := by
  change ScopedFor.update prepared (ScopedFor.update prepared #v[2,dirty]) = _
  rw [after_one,after_two]

theorem two_prefix (caller : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([2,dirty] ++ caller)) :
    Evm.loopIterN (Evm.run condSlice.ir) (Evm.run bodySelected.realization.ir) 2 m =
      .inl {m with stack := irStack ([0,dirty+11] ++ caller)} := by
  have actual := every_prefix 2 #v[2,dirty] caller m represented
  rw [two_turns] at actual
  exact actual

def observedThree := match Evm.loopIterN (Evm.run condSlice.ir) (Evm.run bodySelected.realization.ir)
    3 (machine [2,dirty,88]) with
  | .inl m => observe (.ok m 0)
  | .inr _ => none
#guard observedThree ==
  some ([some (2^256-1),some (dirty+12).toNat,some 88],some dirty.toNat,23,99,99,7,11,19,31,false)
#check after_prelude 0 99 [88,dirty]
#check after_prelude 3 0 []
#check ScopedForAdequacy.Controls.successful_output_refused 99 [88,dirty]
/-- info: 'SolidityBridge.Yul.ScopedForPrefixes.Controls.prelude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prelude
/-- info: 'SolidityBridge.Yul.ScopedForPrefixes.Controls.every_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms every_prefix
/-- info: 'SolidityBridge.Yul.ScopedForPrefixes.Controls.after_prelude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms after_prelude
/-- info: 'SolidityBridge.Yul.ScopedForPrefixes.Controls.no_finite_loop_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms no_finite_loop_outcome
/-- info: 'SolidityBridge.Yul.ScopedForPrefixes.Controls.two_turns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_turns
/-- info: 'SolidityBridge.Yul.ScopedForPrefixes.Controls.two_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_prefix
end SolidityBridge.Yul.ScopedForPrefixes.Controls
