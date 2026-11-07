import SolidityBridge.Yul.ScopedForReflection
import SolidityBridge.Yul.ScopedForCompletionControls

/-! Concrete nested-scope/switch FOR inverse witnesses, retaining the original
source fuel, dirty words and full numeric machine observations. Not native EVM. -/
namespace SolidityBridge.Yul.ScopedForReflection.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul.Closed Solidity.Yul.Compilation ProducerExpressions
open ScopedFor.Controls

/-- Source completion is recovered from the actual combined compiler model
run for every input counter, caller suffix and represented full machine. -/
theorem reflected (initial : Scalar.Word) (caller : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([initial,dirty] ++ caller)) :
    ∃ count,
      evalStmt (6+(count+2)) .nil True.intro statement (ScopedFor.profile prepared)
        (sourceLocals #v[initial,dirty]) =
        some ⟨sourceLocals (Nat.repeat (ScopedFor.update prepared) count
          (prepared.before.update #v[initial,dirty])),.normal⟩ ∧
      {m with stack := irStack ([0,dirty+11] ++ caller)} =
        {m with stack := irStack ((Nat.repeat (ScopedFor.update prepared) count
          (prepared.before.update #v[initial,dirty])).toList ++ caller)} ∧ (0 : Nat) = 0 :=
  source_of_model prepared packet 6 (by decide) #v[initial,dirty] caller m _ 0 represented
    (ScopedForCompletion.Controls.from_ten initial caller m represented).2

theorem pending_refused (initial : Scalar.Word) (caller : Stack) (m actual : Evm.Machine) (pending : Nat)
    (represented : m.stack = irStack ([initial,dirty] ++ caller)) (nonzero : pending ≠ 0) :
    Evm.run packet.selected.realization.ir m ≠ .ok actual pending := by
  intro ran
  obtain ⟨count,source,frame,zero⟩ := source_of_model prepared packet 6 (by decide)
    #v[initial,dirty] caller m actual pending represented ran
  exact nonzero zero

/-- A changed accumulator cannot be a successful selected result; the full
model/frame equality, not merely a source-output assertion, rules it out. -/
theorem wrong_order_refused (initial : Scalar.Word) (caller : Stack) (m : Evm.Machine)
    (represented : m.stack = irStack ([initial,dirty] ++ caller)) :
    Evm.run packet.selected.realization.ir m ≠
      .ok {m with stack := irStack ([0,dirty+2] ++ caller)} 0 := by
  intro ran
  have same := Evm.Out.ok.inj (ran.symm.trans
    (ScopedForCompletion.Controls.from_ten initial caller m represented).2)
  have stacks := congrArg Evm.Machine.stack same.1
  have word := congrArg (fun s => s[1]?) stacks
  change some (Evm.Word.val (Evm.wmod (dirty+2).toNat)) = some (Evm.Word.val (Evm.wmod (dirty+11).toNat)) at word
  exact (by decide : some (Evm.Word.val (Evm.wmod (dirty+2).toNat)) ≠ some (Evm.Word.val (Evm.wmod (dirty+11).toNat))) word

/-- Scalar/model success does not establish native 1024-word validity. The
arbitrary-caller theorem remains true even when the initial stack is too long. -/
theorem oversized_model :
    Evm.run packet.selected.realization.ir (machine ([99,dirty] ++ List.replicate 1023 0)) =
      .ok {(machine ([99,dirty] ++ List.replicate 1023 0)) with
        stack := irStack ([0,dirty+11] ++ List.replicate 1023 0)} 0 ∧
    1024 < ([99,dirty] ++ List.replicate 1023 (0 : Scalar.Word)).length :=
  ⟨(ScopedForCompletion.Controls.from_ten 99 (List.replicate 1023 0) _ rfl).2,by simp only [List.length_append,List.length_cons,List.length_nil,List.length_replicate]; decide⟩

#check reflected 0 [88,dirty]
#check reflected 99 []
#guard observe (Evm.run packet.selected.realization.ir (machine [0,dirty,88])) ==
  some ([some 0,some (dirty+11).toNat,some 88],some dirty.toNat,23,99,99,7,11,19,31,false)
/-- info: 'SolidityBridge.Yul.ScopedForReflection.Controls.reflected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reflected
/-- info: 'SolidityBridge.Yul.ScopedForReflection.Controls.pending_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pending_refused
/-- info: 'SolidityBridge.Yul.ScopedForReflection.Controls.wrong_order_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_order_refused
/-- info: 'SolidityBridge.Yul.ScopedForReflection.Controls.oversized_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms oversized_model
end SolidityBridge.Yul.ScopedForReflection.Controls
