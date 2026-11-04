import Solidity.Yul.Compilation.WhileWordExecution
/-! Actual emitted counter loop and endless-prefix controls. Whole source-loop,
native backedge/gas/capacity and Source/G24 adequacy are not inferred. -/
namespace Solidity.Yul.Compilation.WhileWordExecution.Controls
open Solidity.Yul Solidity.Yul.Closed ProducerExpressions
open Backend Scalar MachineAdapter

def testExpr : Expr [] [] 2 1 := .local 0
def bodyStmt : Stmt [] [] ⟨false,false⟩ 2 := .seq
 (.assign (fun _ : Fin 1 => .local 0)
   (.builtin (.pure .sub) (Fin.cases (.local 0) (fun _ => .literal 1))))
 (.assign (fun _ : Fin 1 => .local 1) (.builtin (.pure .not) (fun _ => .local 1)))
def test := (PureExpressions.compile 1 testExpr).get (by rfl)
def body := (ScopedStatements.compile 5 bodyStmt).get (by rfl)
def cc := (test.lowered.code 0).get (by rfl)
def bb := (body.lowered.code 0).get (by rfl)
def qc := (WordMachine.selectCode cc).get (by rfl)
def qb := (WordMachine.selectCode bb).get (by rfl)
def block := (lowerWhile test.lowered body.lowered 0).get (by rfl)
def code := (WordControl.blockCode block).get (by rfl)
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)

theorem actual_emission : lowerWhile test.lowered body.lowered 0 = some block := (Option.some_get (by rfl)).symm
theorem actual_selection : WordControl.blockCode block = some code := (Option.some_get (by rfl)).symm

theorem test_source (locals : Vector Scalar.Word 2) :
 evalExpr 1 .nil True.intro testExpr test.profile (sourceLocals locals) =
 some (fun _ => (test.value locals).toFin) := test.source locals

theorem body_source (locals : Vector Scalar.Word 2) :
 evalStmt 5 .nil True.intro bodyStmt body.profile (sourceLocals locals) =
 some ⟨sourceLocals (body.update locals),.normal⟩ := body.source locals

theorem update_eq (a b : Scalar.Word) : body.update #v[a,b] = #v[a-1,~~~b] := by rfl

theorem repeat_two (b : Scalar.Word) : Nat.repeat body.update 2 #v[2,b] = #v[0,b] := by
 change body.update (body.update #v[2,b]) = _
 rw [update_eq,update_eq,BitVec.not_not]
 rfl

theorem guards_two (b : Scalar.Word) :
 ∀ j, j < 2 → test.value (Nat.repeat body.update j #v[2,b]) ≠ 0 := by
 intro j bound
 have cases : j = 0 ∨ j = 1 := by omega
 rcases cases with rfl | rfl
 · change (2 : Scalar.Word) ≠ 0; decide
 · change test.value (body.update #v[2,b]) ≠ 0
   rw [update_eq]
   change (1 : Scalar.Word) ≠ 0
   decide

theorem stopped_two (b : Scalar.Word) : test.value (Nat.repeat body.update 2 #v[2,b]) = 0 := by
 rw [repeat_two]
 rfl

theorem two_prefix (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.loopIterN (Evm.run qc) (Evm.run qb) 2 {m with stack := [coreWord 2,coreWord b]++caller} =
 .inl {m with stack := [coreWord 0,coreWord b]++caller} := by
 have law := running_prefix test.lowered body.lowered cc bb qc qb
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm
   2 #v[2,b] #v[] m caller (guards_two b)
 simpa only [repeat_two,Vector.toList_empty,List.nil_append] using law

theorem two_run (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run code {m with stack := [coreWord 2,coreWord b]++caller} =
 .ok {m with stack := [coreWord 0,coreWord b]++caller} 0 := by
 have law := lowered test.lowered body.lowered block code actual_emission actual_selection
   2 #v[2,b] #v[] m caller (guards_two b) (stopped_two b)
 simpa only [repeat_two,Vector.toList_empty,List.nil_append] using law

theorem zero_run (b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run code {m with stack := [coreWord 0,coreWord b]++caller} =
 .ok {m with stack := [coreWord 0,coreWord b]++caller} 0 := by
 have law := lowered test.lowered body.lowered block code actual_emission actual_selection
   0 #v[0,b] #v[] m caller (by intro j h; omega) (by rfl)
 simpa only [Nat.repeat,Vector.toList_empty,List.nil_append] using law

def shiftedBlock := (lowerWhile test.lowered body.lowered 13).get (by rfl)
def shiftedCode := (WordControl.blockCode shiftedBlock).get (by rfl)

theorem shifted_run (b : Scalar.Word) (newer : Vector Scalar.Word 13)
 (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run shiftedCode {m with stack := (newer.toList++[2,b]).map coreWord++caller} =
 .ok {m with stack := (newer.toList++[0,b]).map coreWord++caller} 0 := by
 have law := lowered test.lowered body.lowered shiftedBlock shiftedCode
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm
   2 #v[2,b] newer m caller (guards_two b) (stopped_two b)
 simpa only [repeat_two] using law

def boundaryBlock := (lowerWhile test.lowered body.lowered 14).get (by rfl)
def boundaryCode := (WordControl.blockCode boundaryBlock).get (by rfl)

theorem boundary_run (b : Scalar.Word) (newer : Vector Scalar.Word 14)
 (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run boundaryCode {m with stack := (newer.toList++[2,b]).map coreWord++caller} =
 .ok {m with stack := (newer.toList++[0,b]).map coreWord++caller} 0 := by
 have law := lowered test.lowered body.lowered boundaryBlock boundaryCode
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm
   2 #v[2,b] newer m caller (guards_two b) (stopped_two b)
 simpa only [repeat_two] using law

def alwaysExpr : Expr [] [] 2 1 := .literal 1
def always := (PureExpressions.compile 1 alwaysExpr).get (by rfl)
def ac := (always.lowered.code 0).get (by rfl)
def aq := (WordMachine.selectCode ac).get (by rfl)

theorem endless_prefix (count : Nat) (locals : Vector Scalar.Word 2)
 (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.loopIterN (Evm.run aq) (Evm.run qb) count {m with stack := locals.toList.map coreWord++caller} =
 .inl {m with stack := (Nat.repeat body.update count locals).toList.map coreWord++caller} := by
 have law := running_prefix always.lowered body.lowered ac bb aq qb
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm
   count locals #v[] m caller (by intro j _; change (1 : Scalar.Word) ≠ 0; decide)
 simpa only [Vector.toList_empty,List.nil_append] using law

/-- A theorem about the mathematical model, never evaluated as a host loop. -/
theorem endless_model_fault (locals : Vector Scalar.Word 2)
 (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run [.loop aq qb] {m with stack := locals.toList.map coreWord++caller} = .fault := by
 have law := all_prefixes_fault always.lowered body.lowered ac bb aq qb
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm
   locals #v[] m caller (by intro j; change (1 : Scalar.Word) ≠ 0; decide)
 simpa only [Vector.toList_empty,List.nil_append] using law

theorem oversized (b : Scalar.Word) (m : Evm.Machine) (caller : Vector Evm.Word 1023) :
 Evm.run code {m with stack := [coreWord 2,coreWord b]++caller.toList} =
 .ok {m with stack := [coreWord 0,coreWord b]++caller.toList} 0 ∧
 1024 < ([coreWord 2,coreWord b]++caller.toList).length := by
 constructor
 · exact two_run b m caller.toList
 · simp only [List.length_append,List.length_cons,List.length_nil,Vector.length_toList]; omega

def observed := match Evm.run code
 {Evm.Machine.init with stack := [coreWord 2,coreWord dirty,.slot (.root 77)]} with
 | .ok m skip => some (m.stack,skip)
 | _ => none
#guard observed = some ([coreWord 0,coreWord dirty,.slot (.root 77)],0)
#guard match Evm.loopIterN (Evm.run qc) (Evm.run qb) 1
 {Evm.Machine.init with stack := [coreWord 2,coreWord dirty,.slot (.root 77)]} with
 | .inl m => m.stack == [coreWord 1,coreWord (~~~dirty),.slot (.root 77)]
 | _ => false
#guard match Evm.loopIterN (Evm.run qc) (Evm.run qb) 3
 {Evm.Machine.init with stack := [coreWord 2,coreWord dirty,.slot (.root 77)]} with
 | .inr (.ok m 0) => m.stack == [coreWord 0,coreWord dirty,.slot (.root 77)]
 | _ => false
#guard match Evm.loopIterN (Evm.run aq) (Evm.run qb) 8
 {Evm.Machine.init with stack := [coreWord 2,coreWord dirty,.slot (.root 77)]} with
 | .inl _ => true
 | _ => false
#guard match Evm.run code Evm.Machine.init with | .fault => true | _ => false
#guard (PureExpressions.compile 0 testExpr).isNone
#guard (body.lowered.code 15).isNone
#guard (body.lowered.code 16).isNone
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.Controls.actual_emission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_emission
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.Controls.actual_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_selection
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.Controls.test_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms test_source
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.Controls.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms body_source
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.Controls.update_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms update_eq
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.Controls.repeat_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms repeat_two
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.Controls.guards_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms guards_two
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.Controls.stopped_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms stopped_two
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.Controls.two_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms two_prefix
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.Controls.two_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms two_run
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.Controls.zero_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_run
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.Controls.shifted_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shifted_run
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.Controls.boundary_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms boundary_run
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.Controls.endless_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms endless_prefix
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.Controls.endless_model_fault' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms endless_model_fault
/-- info: 'Solidity.Yul.Compilation.WhileWordExecution.Controls.oversized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms oversized
end Solidity.Yul.Compilation.WhileWordExecution.Controls
