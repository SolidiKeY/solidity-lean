import SolidityBridge.Yul.WordStructuredCompilation
import SolidityBridge.Yul.NestedSwitchControls
import SolidityBridge.Yul.ScopedForControls
/-! Actual existing lexical switch and scoped FOR fixtures under concrete word
selection. Symbolic callers are outside the numeric local frame. Untaken bad
arms need no run proof; an unending whole loop is never host-evaluated. -/
namespace SolidityBridge.Yul.WordStructuredCompilation.Controls
open Solidity Backend Scalar Selection
open Solidity.Yul Solidity.Yul.Closed Solidity.Yul.Compilation ProducerExpressions MachineAdapter

abbrev nested := NestedSwitch.Controls.compiled
abbrev nestedStmt := NestedSwitch.Controls.statement
abbrev nestedBlock := NestedSwitch.Controls.block
abbrev dirty := NestedSwitch.Controls.dirty
def nestedCode := (WordControl.blockCode nestedBlock).get (by rfl)

theorem nested_visit : NestedSwitch.compile 13 nestedStmt = some nested := (Option.some_get (by rfl)).symm

theorem nested_run (locals : Vector Scalar.Word 3) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run nestedCode {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := (nested.update locals).toList.map coreWord++caller} 0 :=
 nested_model nested nestedBlock nestedCode (Option.some_get (by rfl)).symm
   (Option.some_get (by rfl)).symm locals m caller

theorem nested_source_target (locals : Vector Scalar.Word 3) (m : Evm.Machine) (caller : List Evm.Word) :
 (evalStmt 13 .nil True.intro nestedStmt nested.profile (sourceLocals locals) =
   some ⟨sourceLocals (nested.update locals),.normal⟩) ∧
 Evm.run nestedCode {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := (nested.update locals).toList.map coreWord++caller} 0 :=
 nested_source_model nestedStmt nested nested_visit nestedBlock nestedCode
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm locals m caller

theorem first_match : nested.update #v[1,11,23] = #v[3,dirty+11,23] := by decide
theorem skipped_arm : nested.update #v[1,11,0] = #v[1,11,0] := by decide
theorem later_match : nested.update #v[3,11,23] = #v[3,999,23] := by decide
theorem fallback_match : nested.update #v[8,11,23] = #v[8,42,23] := by decide
theorem dirty_unmatched : nested.update #v[dirty,11,23] = #v[dirty,11,23] := by decide

theorem nested_dirty_run (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run nestedCode {m with stack := [coreWord 1,coreWord 11,coreWord 23]++caller} =
 .ok {m with stack := [coreWord 3,coreWord (dirty+11),coreWord 23]++caller} 0 :=
 (nested_run #v[1,11,23] m caller).trans (congrArg (fun locals : Vector Scalar.Word 3 =>
   Evm.Out.ok {m with stack := locals.toList.map coreWord++caller} 0) first_match)

abbrev forPrepared := ScopedFor.Controls.prepared
abbrev forBlock := ScopedFor.Controls.target
abbrev forStmt := ScopedFor.Controls.statement
abbrev forDirty := ScopedFor.Controls.dirty
def forCode := (WordControl.blockCode forBlock).get (by rfl)

theorem for_run (initial : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run forCode {m with stack := [coreWord initial,coreWord forDirty]++caller} =
 .ok {m with stack := [coreWord 0,coreWord (forDirty+11)]++caller} 0 := by
 have stopped : forPrepared.test.value (Nat.repeat (ScopedFor.update forPrepared) 2
   (forPrepared.before.update #v[initial,forDirty])) = 0 := by rw [ScopedFor.Controls.finish]; rfl
 have law := scoped_for_model forPrepared forBlock forCode
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm
   2 #v[initial,forDirty] m caller (ScopedFor.Controls.two_running initial) stopped
 simpa only [ScopedFor.Controls.finish] using law

theorem for_source_target (initial : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 (evalStmt 10 .nil True.intro forStmt (ScopedFor.profile forPrepared) (sourceLocals #v[initial,forDirty]) =
   some ⟨sourceLocals #v[0,forDirty+11],.normal⟩) ∧
 Evm.run forCode {m with stack := [coreWord initial,coreWord forDirty]++caller} =
 .ok {m with stack := [coreWord 0,coreWord (forDirty+11)]++caller} 0 := by
 have stopped : forPrepared.test.value (Nat.repeat (ScopedFor.update forPrepared) 2
   (forPrepared.before.update #v[initial,forDirty])) = 0 := by rw [ScopedFor.Controls.finish]; rfl
 have law := scoped_for_source_model forPrepared 6 2 (by decide) forBlock forCode
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm
   #v[initial,forDirty] m caller (ScopedFor.Controls.two_running initial) stopped
 simpa only [ScopedFor.Controls.finish] using law

/-- The original finite target relation never executes this bad false arm. -/
def untakenUnderflow : Backend.Block := .ite [pushWord 1] (.code []) (.code [.op .POP])
def untakenCode := (WordControl.blockCode untakenUnderflow).get (by rfl)

theorem untaken_structured : StructuredExec untakenUnderflow [] [] :=
 .iteTrue (w := 1) (by rfl) (by decide) (.code rfl)

theorem untaken_run (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run untakenCode {m with stack := caller} = .ok {m with stack := caller} 0 :=
 WordBlockExecution.execute untaken_structured untakenCode (Option.some_get (by rfl)).symm m caller

def endless : Backend.Block := .loop [pushWord 1] (.code [])
def skippedLoop : Backend.Block := .ite [pushWord 0] endless (.code [])
def skippedCode := (WordControl.blockCode skippedLoop).get (by rfl)

theorem skipped_structured : StructuredExec skippedLoop [] [] := .iteFalse (by rfl) (.code rfl)

theorem skipped_run (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run skippedCode {m with stack := caller} = .ok {m with stack := caller} 0 :=
 WordBlockExecution.execute skipped_structured skippedCode (Option.some_get (by rfl)).symm m caller

theorem oversized (initial : Scalar.Word) (m : Evm.Machine) (caller : Vector Evm.Word 1023) :
 Evm.run forCode {m with stack := [coreWord initial,coreWord forDirty]++caller.toList} =
 .ok {m with stack := [coreWord 0,coreWord (forDirty+11)]++caller.toList} 0 ∧
 1024 < ([coreWord initial,coreWord forDirty]++caller.toList).length := by
 constructor
 · exact for_run initial m caller.toList
 · simp only [List.length_append,List.length_cons,List.length_nil,Vector.length_toList]; omega

def nestedObserved := match Evm.run nestedCode {Evm.Machine.init with stack :=
 [coreWord 1,coreWord 11,coreWord 23,.slot (.root 17)]} with
 | .ok m skip => some (m.stack,skip)
 | _ => none
#guard nestedObserved = some ([coreWord 3,coreWord (dirty+11),coreWord 23,.slot (.root 17)],0)
#guard match Evm.run forCode {Evm.Machine.init with stack := [coreWord 99,coreWord forDirty,.slot (.root 17)]} with
 | .ok m 0 => m.stack == [coreWord 0,coreWord (forDirty+11),.slot (.root 17)]
 | _ => false
#guard Scalar.run [.op .POP] [] = none
#guard match Evm.run [.pop] Evm.Machine.init with | .fault => true | _ => false
#guard match Evm.run untakenCode {Evm.Machine.init with stack := [.slot (.root 17)]} with
 | .ok m 0 => m.stack == [.slot (.root 17)]
 | _ => false
#guard match Evm.run skippedCode {Evm.Machine.init with stack := [.slot (.root 17)]} with
 | .ok m 0 => m.stack == [.slot (.root 17)]
 | _ => false
#guard (NestedSwitch.compile 0 nestedStmt).isNone
#guard (NestedSwitch.compile 2 nestedStmt).isNone
#guard NestedSwitch.Controls.inaccessible.emit.isNone
#guard NestedSwitch.Controls.accessible.emit.isSome
#guard (WordControl.blockCode (.code [.op .SSTORE])).isNone
#guard match Evm.run nestedCode Evm.Machine.init with | .fault => true | _ => false
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.Controls.nested_visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nested_visit
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.Controls.nested_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nested_run
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.Controls.nested_source_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nested_source_target
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.Controls.first_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms first_match
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.Controls.skipped_arm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms skipped_arm
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.Controls.later_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms later_match
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.Controls.fallback_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms fallback_match
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.Controls.dirty_unmatched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dirty_unmatched
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.Controls.nested_dirty_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nested_dirty_run
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.Controls.for_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms for_run
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.Controls.for_source_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms for_source_target
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.Controls.untaken_structured' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms untaken_structured
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.Controls.untaken_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms untaken_run
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.Controls.skipped_structured' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms skipped_structured
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.Controls.skipped_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms skipped_run
/-- info: 'SolidityBridge.Yul.WordStructuredCompilation.Controls.oversized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms oversized
end SolidityBridge.Yul.WordStructuredCompilation.Controls
