import SolidityBridge.Yul.ForReflection
import SolidityBridge.Yul.StructuredForControls
import SolidityBridge.Yul.ForPrefixesControls

/-! Reflection witnesses use actual selected original programs and numeric
model runs. Finite nontrivial/zero results, pending-skip refusal, genuine
noncompletion and model-success/capacity separation are not native claims. -/
namespace SolidityBridge.Yul.ForReflection.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed
open Solidity.Yul.Compilation ProducerExpressions
open StructuredFor.Controls
abbrev cc := ForPrefixes.Controls.cc
abbrev preBlock := ForPrefixes.Controls.preBlock
abbrev postBlock := ForPrefixes.Controls.postBlock
abbrev bodyBlock := ForPrefixes.Controls.bodyBlock
abbrev update := ForPrefixes.Controls.update

/-- A source horizon/result is recovered from the actual branch-bearing
selected-model success, without supplying a source run or iteration count. -/
theorem two_reflected (tail : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([77,dirty] ++ ([99,dirty,high] ++ tail))) :
    ∃ count,
      evalStmt (4+(count+2)) .nil True.intro statement actualProfile (sourceLocals #v[99,dirty,high]) =
        some ⟨sourceLocals (Nat.repeat update count (before.update #v[99,dirty,high])),.normal⟩ ∧
      {m with stack := irStack ([77,dirty] ++ ([0,dirty+1,high] ++ tail))} =
        {m with stack := irStack ([77,dirty] ++
          ((Nat.repeat update count (before.update #v[99,dirty,high])).toList ++ tail))} ∧
      (0 : Nat) = 0 :=
  source_of_model (c := ⟨false,false⟩) test after inside before 2 preBlock cc postBlock bodyBlock
    rfl rfl rfl rfl selected 4 (by decide) (by decide) (by decide) (by decide)
    #v[99,dirty,high] #v[77,dirty] tail m _ 0 represented (model_two tail m represented)

/-- The same real inverse handles an initially zero condition/false prelude. -/
theorem zero_reflected (tail : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([77,dirty] ++ ([0,dirty,0] ++ tail))) :
    ∃ count,
      evalStmt (4+(count+2)) .nil True.intro statement actualProfile (sourceLocals #v[0,dirty,0]) =
        some ⟨sourceLocals (Nat.repeat update count (before.update #v[0,dirty,0])),.normal⟩ ∧
      m = {m with stack := irStack ([77,dirty] ++
        ((Nat.repeat update count (before.update #v[0,dirty,0])).toList ++ tail))} ∧
      (0 : Nat) = 0 := by
  have ran := StructuredFor.model (c := ⟨false,false⟩) test after inside before 2 target rfl selected
    0 #v[0,dirty,0] #v[77,dirty] tail (by intro j bound; omega) (by decide) m represented
  change Evm.run selected.realization.ir m = .ok {m with stack := irStack ([77,dirty] ++ ([0,dirty,0] ++ tail))} 0 at ran
  rw [←represented] at ran
  exact source_of_model (c := ⟨false,false⟩) test after inside before 2 preBlock cc postBlock bodyBlock
    rfl rfl rfl rfl selected 4 (by decide) (by decide) (by decide) (by decide)
    #v[0,dirty,0] #v[77,dirty] tail m m 0 represented ran

/-- Successful selection cannot leak an unconsumed instruction-skip count. -/
theorem pending_refused (tail : Stack) (m actual : Evm.Machine) (pending : Nat)
    (represented : m.stack = irStack ([77,dirty] ++ ([99,dirty,high] ++ tail)))
    (nonzero : pending ≠ 0) : Evm.run selected.realization.ir m ≠ .ok actual pending := by
  intro ran
  obtain ⟨count,source,frame,zero⟩ := source_of_model (c := ⟨false,false⟩) test after inside before
    2 preBlock cc postBlock bodyBlock rfl rfl rfl rfl selected 4
    (by decide) (by decide) (by decide) (by decide) #v[99,dirty,high] #v[77,dirty] tail
    m actual pending represented ran
  exact nonzero zero

/-- Never execute this unending model run: use the prior proved noncompletion
law. Model fault here denotes no finite outcome, not native exceptional halt. -/
theorem infinite_success_refused (tail : Stack) (m actual : Evm.Machine) (pending : Nat)
    (represented : m.stack = irStack ([77,dirty] ++ ([99,dirty,0] ++ tail))) :
    Evm.run selected.realization.ir m ≠ .ok actual pending := by
  rw [ForPrefixes.Controls.whole_model_no_finite_outcome tail m represented]
  intro impossible
  cases impossible

/-- Actual mathematical execution success is not a 1024-capacity theorem. -/
theorem oversized_model :
    Evm.run selected.realization.ir (machine ([77,dirty,99,dirty,high] ++ List.replicate 1020 0)) =
      .ok {(machine ([77,dirty,99,dirty,high] ++ List.replicate 1020 0)) with
        stack := irStack ([77,dirty,0,dirty+1,high] ++ List.replicate 1020 0)} 0 ∧
    Scalar.stackBound cc 1025 = false :=
  ⟨model_two (List.replicate 1020 0) _ rfl,by decide⟩

#guard high.toNat % 256 = 0
#guard !(Scalar.stackBound cc 1024)
#guard observe (Evm.run selected.realization.ir (machine [77,dirty,99,dirty,high,88])) ==
  some ([some 77,some dirty.toNat,some 0,some (dirty+1).toNat,some high.toNat,some 88],some dirty.toNat,23,99,99,7,11,19,31,false)
#check two_reflected [88,dirty]
#check zero_reflected []

/-- info: 'SolidityBridge.Yul.ForReflection.Controls.two_reflected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_reflected
/-- info: 'SolidityBridge.Yul.ForReflection.Controls.zero_reflected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_reflected
/-- info: 'SolidityBridge.Yul.ForReflection.Controls.pending_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pending_refused
/-- info: 'SolidityBridge.Yul.ForReflection.Controls.infinite_success_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms infinite_success_refused
/-- info: 'SolidityBridge.Yul.ForReflection.Controls.oversized_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oversized_model
end SolidityBridge.Yul.ForReflection.Controls
