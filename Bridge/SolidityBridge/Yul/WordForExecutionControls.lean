import SolidityBridge.Yul.WordForExecution
import SolidityBridge.Yul.NormalForControls
/-! Reuse the existing original FOR fixture and component compilers; this
checks the concrete WordControl selector, not the earlier realization callback.
All source locals, symbolic caller words and nonstack machine fields are general. -/
namespace SolidityBridge.Yul.WordForExecution.Controls
open Solidity Backend Scalar
open Solidity.Yul.Closed
open Solidity.Yul.Compilation ProducerExpressions MachineAdapter

abbrev prepared := NormalFor.Controls.prepared
abbrev test := prepared.test
abbrev after := prepared.after
abbrev inside := prepared.inside
abbrev before := prepared.before
abbrev statement := NormalFor.Controls.statement
abbrev profile := NormalFor.Controls.actualProfile
abbrev target := NormalFor.Controls.target
def code := (WordControl.blockCode target).get (by rfl)
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)

theorem actual_preparation : NormalFor.prepare 3 (c := ⟨false,false⟩)
 NormalFor.Controls.pre NormalFor.Controls.condition NormalFor.Controls.post NormalFor.Controls.body =
 some prepared := (Option.some_get (by rfl)).symm

theorem actual_emission : NormalFor.emit (c := ⟨false,false⟩) test after inside before 2 = some target :=
 (Option.some_get (by rfl)).symm

theorem actual_selection : WordControl.blockCode target = some code := (Option.some_get (by rfl)).symm

theorem before_update (a b : Scalar.Word) : before.update #v[a,b] = #v[2,b] := by rfl
theorem inside_update (a b : Scalar.Word) : inside.update #v[a,b] = #v[a-1,b] := by rfl
theorem after_update (a b : Scalar.Word) : after.update #v[a,b] = #v[a,b+a] := by rfl

theorem repeat_two (a b : Scalar.Word) :
 Nat.repeat (fun l => after.update (inside.update l)) 2 (before.update #v[a,b]) = #v[0,b+1] := by
 change after.update (inside.update (after.update (inside.update (before.update #v[a,b])))) = _
 rw [before_update,inside_update,after_update,inside_update,after_update]
 change #v[0,(b+1)+0] = _
 exact congrArg (fun x : Scalar.Word => (#v[0,x] : Vector Scalar.Word 2)) (BitVec.add_zero (b+1))

theorem guards_two (a b : Scalar.Word) :
 ∀ j, j < 2 → test.value (Nat.repeat (fun l => after.update (inside.update l)) j
   (before.update #v[a,b])) ≠ 0 := by
 intro j bound
 have cases : j = 0 ∨ j = 1 := by omega
 rcases cases with rfl | rfl
 · change test.value (before.update #v[a,b]) ≠ 0
   rw [before_update]
   change (2 : Scalar.Word) ≠ 0
   decide
 · change test.value (after.update (inside.update (before.update #v[a,b]))) ≠ 0
   rw [before_update,inside_update,after_update]
   change (1 : Scalar.Word) ≠ 0
   decide

theorem stopped_two (a b : Scalar.Word) :
 test.value (Nat.repeat (fun l => after.update (inside.update l)) 2 (before.update #v[a,b])) = 0 := by
 rw [repeat_two]
 rfl

theorem two_run (a b : Scalar.Word) (newer : Vector Scalar.Word 2)
 (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run code {m with stack := (newer.toList++[a,b]).map coreWord++caller} =
 .ok {m with stack := (newer.toList++[0,b+1]).map coreWord++caller} 0 := by
 have law := model (c := ⟨false,false⟩) test after inside before 2 target code actual_emission actual_selection
   2 #v[a,b] newer m caller (guards_two a b) (stopped_two a b)
 simpa only [repeat_two] using law

/-- Both full original FOR evaluation and concrete model execution, not just
four leaf equations. No runtime stack/source execution premise is assumed. -/
theorem source_target (a b : Scalar.Word) (newer : Vector Scalar.Word 2)
 (m : Evm.Machine) (caller : List Evm.Word) :
 (evalStmt 7 .nil True.intro statement profile (sourceLocals #v[a,b]) =
 some ⟨sourceLocals #v[0,b+1],.normal⟩) ∧
 Evm.run code {m with stack := (newer.toList++[a,b]).map coreWord++caller} =
 .ok {m with stack := (newer.toList++[0,b+1]).map coreWord++caller} 0 := by
 have law := source_model (c := ⟨false,false⟩) test after inside before 3 2
   (by decide) (by decide) (by decide) (by decide)
   2 target code actual_emission actual_selection #v[a,b] newer m caller (guards_two a b) (stopped_two a b)
 simpa only [repeat_two] using law

def boundaryTarget := (NormalFor.emit (c := ⟨false,false⟩) test after inside before 13).get (by rfl)
def boundaryCode := (WordControl.blockCode boundaryTarget).get (by rfl)

theorem boundary_run (a b : Scalar.Word) (newer : Vector Scalar.Word 13)
 (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run boundaryCode {m with stack := (newer.toList++[a,b]).map coreWord++caller} =
 .ok {m with stack := (newer.toList++[0,b+1]).map coreWord++caller} 0 := by
 have law := model (c := ⟨false,false⟩) test after inside before 13 boundaryTarget boundaryCode
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm
   2 #v[a,b] newer m caller (guards_two a b) (stopped_two a b)
 simpa only [repeat_two] using law

theorem oversized (a b : Scalar.Word) (m : Evm.Machine) (caller : Vector Evm.Word 1021) :
 Evm.run code {m with stack := ([77,dirty]++[a,b]).map coreWord++caller.toList} =
 .ok {m with stack := ([77,dirty]++[0,b+1]).map coreWord++caller.toList} 0 ∧
 1024 < (([77,dirty]++[a,b]).map coreWord++caller.toList).length := by
 constructor
 · exact two_run a b #v[77,dirty] m caller.toList
 · simp only [List.length_append,List.length_map,List.length_cons,List.length_nil,Vector.length_toList]; omega

def observed := match Evm.run code {Evm.Machine.init with stack :=
 [coreWord 77,coreWord dirty,coreWord 99,coreWord dirty,.slot (.root 17)]} with
 | .ok m skip => some (m.stack,skip)
 | _ => none
#guard observed = some ([coreWord 77,coreWord dirty,coreWord 0,coreWord (dirty+1),.slot (.root 17)],0)
#guard (evalStmt 2 .nil True.intro statement profile (sourceLocals #v[99,dirty])).isNone
#guard (NormalFor.prepare 2 (c := ⟨false,false⟩) NormalFor.Controls.pre NormalFor.Controls.condition
 NormalFor.Controls.post NormalFor.Controls.body).isNone
#guard (NormalFor.prepare 3 (c := ⟨false,false⟩) NormalFor.Controls.pre NormalFor.Controls.condition
 NormalFor.Controls.post .break_).isNone
#guard (NormalFor.prepare 3 (c := ⟨false,false⟩) NormalFor.Controls.pre NormalFor.Controls.condition
 NormalFor.Controls.post .continue_).isNone
#guard (NormalFor.emit (c := ⟨false,false⟩) test after inside before 14).isNone
#guard (NormalFor.emit (c := ⟨false,false⟩) test after inside before 15).isNone
#guard match Evm.run code Evm.Machine.init with | .fault => true | _ => false
/-- info: 'SolidityBridge.Yul.WordForExecution.Controls.actual_preparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_preparation
/-- info: 'SolidityBridge.Yul.WordForExecution.Controls.actual_emission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_emission
/-- info: 'SolidityBridge.Yul.WordForExecution.Controls.actual_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_selection
/-- info: 'SolidityBridge.Yul.WordForExecution.Controls.before_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms before_update
/-- info: 'SolidityBridge.Yul.WordForExecution.Controls.inside_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inside_update
/-- info: 'SolidityBridge.Yul.WordForExecution.Controls.after_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms after_update
/-- info: 'SolidityBridge.Yul.WordForExecution.Controls.repeat_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms repeat_two
/-- info: 'SolidityBridge.Yul.WordForExecution.Controls.guards_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guards_two
/-- info: 'SolidityBridge.Yul.WordForExecution.Controls.stopped_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stopped_two
/-- info: 'SolidityBridge.Yul.WordForExecution.Controls.two_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_run
/-- info: 'SolidityBridge.Yul.WordForExecution.Controls.source_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source_target
/-- info: 'SolidityBridge.Yul.WordForExecution.Controls.boundary_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms boundary_run
/-- info: 'SolidityBridge.Yul.WordForExecution.Controls.oversized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oversized
end SolidityBridge.Yul.WordForExecution.Controls
