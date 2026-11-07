import Solidity.Yul.Compilation.SourceLoopModelCompletion
import Solidity.Yul.Compilation.SourceLoopControls
/-! Concrete bidirectional success consumers for the actual original for,
including arbitrary source horizons/model results and caller frames. Fixed
source exhaustion is not reclassified as model fault. No native/G24 claim. -/
namespace Solidity.Yul.Compilation.SourceLoopModelCompletion.Controls
open Backend Scalar MachineAdapter Solidity.Yul.Closed ProducerExpressions
open SourceLoop.Controls

theorem success_iff (locals out : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 (∃ fuel, evalStmt fuel .nil True.intro source words (sourceLocals locals) =
    some ⟨sourceLocals out,.normal⟩) ↔
 Evm.run code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 simpa only [Vector.toList_empty,List.nil_append] using
  completion_iff (c := root) condition post body 0 block code
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm locals out #v[] m caller

theorem arbitrary_source (fuel : Nat) (locals : Vector Scalar.Word 2) (result : Outcome root 2)
 (ran : evalStmt fuel .nil True.intro source words (sourceLocals locals) = some result)
 (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ out : Vector Scalar.Word 2, result = ⟨sourceLocals out,.normal⟩ ∧
 Evm.run code {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := out.toList.map coreWord++caller} 0 := by
 simpa only [Vector.toList_empty,List.nil_append] using
  SourceLoopCompletion.source_to_model (c := root) condition post body 0 block code
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm fuel locals result ran #v[] m caller

theorem arbitrary_model (locals : Vector Scalar.Word 2) (m final : Evm.Machine)
 (caller : List Evm.Word) (skip : Nat)
 (ran : Evm.run code {m with stack := locals.toList.map coreWord++caller} = .ok final skip) :
 ∃ (fuel : Nat) (out : Vector Scalar.Word 2),
 evalStmt fuel .nil True.intro source words (sourceLocals locals) = some ⟨sourceLocals out,.normal⟩ ∧
 skip = 0 ∧ final = {m with stack := out.toList.map coreWord++caller} := by
 simpa only [Vector.toList_empty,List.nil_append] using
  model_to_source (c := root) condition post body 0 block code
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm locals #v[] m final caller skip ran

/-- Recover source completion using the MODEL witness, without supplying its
count, guard sequence or a source horizon to the equivalence. -/
theorem recovered_source (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 ∃ fuel, evalStmt fuel .nil True.intro source words (sourceLocals #v[2,b]) =
  some ⟨sourceLocals #v[0,~~~(~~~b+3)+3],.normal⟩ := by
 apply (success_iff #v[2,b] #v[0,~~~(~~~b+3)+3] m caller).mpr
 exact (source_and_target b m caller).2

/-- Derive the zero-exit MODEL result from actual source completion instead. -/
theorem zero_target (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run code {m with stack := [coreWord 0,coreWord b]++caller} =
 .ok {m with stack := [coreWord 0,coreWord b]++caller} 0 :=
 (success_iff #v[0,b] #v[0,b] m caller).mp ⟨7,source_zero b⟩

/-- Finite source-horizon exhaustion and actual model success coexist. No
failure/divergence equivalence is smuggled into the success-only theorem. -/
theorem exhaustion_not_fault (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 evalStmt 0 .nil True.intro source words (sourceLocals #v[2,b]) = none ∧
 Evm.run code {m with stack := [coreWord 2,coreWord b]++caller} =
 .ok {m with stack := [coreWord 0,coreWord (~~~(~~~b+3)+3)]++caller} 0 :=
 ⟨rfl,(source_and_target b m caller).2⟩

theorem pending_refused (locals : Vector Scalar.Word 2) (m final : Evm.Machine)
 (caller : List Evm.Word) (skip : Nat) :
 Evm.run code {m with stack := locals.toList.map coreWord++caller} ≠ .ok final (skip+1) := by
 intro ran
 obtain ⟨_,_,_,zero,_⟩ := arbitrary_model locals m final caller (skip+1) ran
 omega

#guard (evalStmt 1 .nil True.intro source words (sourceLocals #v[2,dirty])).isNone
#guard (SourceLoop.emit (c := root) condition post body 15).isNone
#guard SourceLoop.next (c := root) body post #v[2,dirty] = #v[1,~~~dirty+3]
#guard Nat.repeat (SourceLoop.next (c := root) body post) 2 #v[2,dirty] = #v[0,dirty]
/-- info: 'Solidity.Yul.Compilation.SourceLoopModelCompletion.Controls.success_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms success_iff
/-- info: 'Solidity.Yul.Compilation.SourceLoopModelCompletion.Controls.arbitrary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms arbitrary_source
/-- info: 'Solidity.Yul.Compilation.SourceLoopModelCompletion.Controls.arbitrary_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms arbitrary_model
/-- info: 'Solidity.Yul.Compilation.SourceLoopModelCompletion.Controls.recovered_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms recovered_source
/-- info: 'Solidity.Yul.Compilation.SourceLoopModelCompletion.Controls.zero_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_target
/-- info: 'Solidity.Yul.Compilation.SourceLoopModelCompletion.Controls.exhaustion_not_fault' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms exhaustion_not_fault
/-- info: 'Solidity.Yul.Compilation.SourceLoopModelCompletion.Controls.pending_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms pending_refused
end Solidity.Yul.Compilation.SourceLoopModelCompletion.Controls
