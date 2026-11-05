import SolidityBridge.Yul.ForCompletion
import SolidityBridge.Yul.StructuredForControls
import SolidityBridge.Yul.ForPrefixesControls

/-! Derive target results from genuine original source runs, without supplying
iteration counts/guards. Source exhaustion and noncompletion controls do not
claim native failure, gas/1024 capacity, or full logical Source/G24 adequacy. -/
namespace SolidityBridge.Yul.ForCompletion.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed
open Solidity.Yul.Compilation ProducerExpressions
open StructuredFor.Controls

/-- Three branch-bearing original components, full dirty/high words, arbitrary
numeric caller and complete mathematical machine frame. No count supplied. -/
theorem from_source_eight (tail : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([77,dirty] ++ ([99,dirty,high] ++ tail))) :
    StructuredExec target ([77,dirty] ++ ([99,dirty,high] ++ tail))
      ([77,dirty] ++ ([0,dirty+1,high] ++ tail)) ∧
    Evm.run selected.realization.ir m =
      .ok {m with stack := irStack ([77,dirty] ++ ([0,dirty+1,high] ++ tail))} 0 :=
  transport_output (c := ⟨false,false⟩) test after inside before 8 #v[99,dirty,high]
    #v[0,dirty+1,high] source_eight 2 target rfl selected #v[77,dirty] tail m represented

/-- Zero guard/false prelude, derived from the actual earlier source witness. -/
theorem from_zero_source (tail : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([77,dirty] ++ ([0,dirty,0] ++ tail))) :
    StructuredExec target ([77,dirty] ++ ([0,dirty,0] ++ tail))
      ([77,dirty] ++ ([0,dirty,0] ++ tail)) ∧
    Evm.run selected.realization.ir m =
      .ok {m with stack := irStack ([77,dirty] ++ ([0,dirty,0] ++ tail))} 0 :=
  transport_output (c := ⟨false,false⟩) test after inside before 6 #v[0,dirty,0]
    #v[0,dirty,0] zero_source 2 target rfl selected #v[77,dirty] tail m represented

/-- A tiny horizon cannot satisfy source completion, even if a guard would
otherwise be zero. This is a source horizon boundary, not EVM underflow. -/
theorem short_horizon_refused (fuel : Nat) (small : fuel ≤ 1)
    (locals : Vector Scalar.Word 3) (out : Outcome ⟨false,false⟩ 3) :
    evalStmt fuel .nil True.intro statement actualProfile (sourceLocals locals) ≠ some out := by
  intro ran
  obtain ⟨count,bound,_⟩ := source_complete (c := ⟨false,false⟩) test after inside before fuel locals out ran
  omega

/-- The actual infinite witness supplies no completion premise at any horizon. -/
theorem infinite_refused (fuel : Nat) (out : Outcome ⟨false,false⟩ 3) :
    evalStmt fuel .nil True.intro statement actualProfile
      (sourceLocals ForPrefixes.Controls.initial) ≠ some out := by
  rw [ForPrefixes.Controls.source_all_horizons fuel]
  intro impossible
  cases impossible

-- Evaluate finite programs only. The high flag's low byte is zero, but it
-- still takes both real prelude/body branches and preserves every high bit.
#guard high.toNat % 256 = 0
#guard observe (Evm.run selected.realization.ir (machine [77,dirty,99,dirty,high,88])) ==
  some ([some 77,some dirty.toNat,some 0,some (dirty+1).toNat,some high.toNat,some 88],some dirty.toNat,23,99,99,7,11,19,31,false)
#check from_source_eight [88,dirty]
#check from_zero_source []
#check short_horizon_refused 1 (by decide)
#check infinite_refused 0

/-- info: 'SolidityBridge.Yul.ForCompletion.Controls.from_source_eight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms from_source_eight
/-- info: 'SolidityBridge.Yul.ForCompletion.Controls.from_zero_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms from_zero_source
/-- info: 'SolidityBridge.Yul.ForCompletion.Controls.short_horizon_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms short_horizon_refused
/-- info: 'SolidityBridge.Yul.ForCompletion.Controls.infinite_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms infinite_refused
end SolidityBridge.Yul.ForCompletion.Controls
