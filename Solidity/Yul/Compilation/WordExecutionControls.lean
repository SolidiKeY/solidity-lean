import Solidity.Yul.Compilation.WordExecution
/-! Combined original-source witness for all six extra WordMachine operations,
with numeric composition, actual local writes, symbolic callers and refusals.
Finite checks are controls; universal execution follows the general theorem. -/
namespace Solidity.Yul.Compilation.WordExecution.Controls
open Solidity.Yul Solidity.Yul.Closed ProducerExpressions
open Backend Scalar MachineAdapter

def binary (op : Solidity.Yul.Pure 2) (a b : Expr [] [] 2 1) : Expr [] [] 2 1 :=
  .builtin (.pure op) (Fin.cases a (fun _ => b))
def unary (op : Solidity.Yul.Pure 1) (a : Expr [] [] 2 1) : Expr [] [] 2 1 :=
  .builtin (.pure op) (fun _ => a)
def expr : Expr [] [] 2 1 :=
  binary .add (unary .iszero (binary .eq (.local 0) (.local 1)))
    (binary .add (binary .lt (.local 0) (.local 1))
      (binary .add (binary .gt (.local 0) (.local 1))
        (binary .exp (.local 0) (binary .and (unary .not (.local 1)) (.literal 3)))))
def compiled := (PureExpressions.compile 8 expr).get (by rfl)
def code := (compiled.lowered.code 0).get (by rfl)
def model := (WordMachine.selectCode code).get (by rfl)
def shiftedCode := (compiled.lowered.code 5).get (by rfl)
def shiftedModel := (WordMachine.selectCode shiftedCode).get (by rfl)
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)

theorem actual_visit : PureExpressions.compile 8 expr = some compiled := (Option.some_get (by rfl)).symm
theorem actual_emission : compiled.lowered.code 0 = some code := (Option.some_get (by rfl)).symm
theorem actual_selection : WordMachine.selectCode code = some model := (Option.some_get (by rfl)).symm

theorem source (locals : Vector Scalar.Word 2) :
 evalExpr 8 .nil True.intro expr compiled.profile (sourceLocals locals) =
   some (fun _ => (compiled.value locals).toFin) := compiled.source locals

theorem model_run (locals : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run model {m with stack := locals.toList.map coreWord++caller} =
   .ok {m with stack := coreWord (compiled.value locals)::(locals.toList.map coreWord++caller)} 0 := by
 simpa only [Vector.toList_empty,List.nil_append] using
   loweredExpr_machine compiled.lowered 0 code model actual_emission actual_selection locals #v[] m caller

theorem shifted_run (locals : Vector Scalar.Word 2) (newer : Vector Scalar.Word 5)
 (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run shiftedModel {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
   .ok {m with stack := coreWord (compiled.value locals)::((newer.toList++locals.toList).map coreWord++caller)} 0 :=
 loweredExpr_machine compiled.lowered 5 shiftedCode shiftedModel
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm locals newer m caller

def boundaryCode := (compiled.lowered.code 13).get (by rfl)
def boundaryModel := (WordMachine.selectCode boundaryCode).get (by rfl)

theorem boundary_run (locals : Vector Scalar.Word 2) (newer : Vector Scalar.Word 13)
 (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run boundaryModel {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
   .ok {m with stack := coreWord (compiled.value locals)::((newer.toList++locals.toList).map coreWord++caller)} 0 :=
 loweredExpr_machine compiled.lowered 13 boundaryCode boundaryModel
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm locals newer m caller

theorem dirty_distinct : compiled.value #v[dirty,0] ≠ compiled.value #v[257,0] := by decide

theorem concrete_value : compiled.value #v[2,3] = 3 := by decide
theorem equal_value : compiled.value #v[5,5] = 25 := by decide
theorem zero_value : compiled.value #v[0,0] = 0 := by decide

theorem concrete_run (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run model {m with stack := [coreWord 2,coreWord 3]++caller} =
 .ok {m with stack := coreWord 3::([coreWord 2,coreWord 3]++caller)} 0 :=
 (model_run #v[2,3] m caller).trans (congrArg (fun x : Scalar.Word =>
   Evm.Out.ok {m with stack := coreWord x::([coreWord 2,coreWord 3]++caller)} 0) concrete_value)

def stmt : Stmt [] [] ⟨false,false⟩ 2 :=
 .seq (.assign (fun _ : Fin 1 => .local 0) expr)
   (.assign (fun _ : Fin 1 => .local 1) (unary .not (.local 0)))
def statementCompiled := (ScopedStatements.compile 9 stmt).get (by rfl)
def statementCode := (statementCompiled.lowered.code 0).get (by rfl)
def statementModel := (WordMachine.selectCode statementCode).get (by rfl)

theorem statement_run (locals : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run statementModel {m with stack := locals.toList.map coreWord++caller} =
 .ok {m with stack := (statementCompiled.update locals).toList.map coreWord++caller} 0 := by
 simpa only [Vector.toList_empty,List.nil_append] using
 loweredStmt_machine statementCompiled.lowered 0 statementCode statementModel
   (Option.some_get (by rfl)).symm (Option.some_get (by rfl)).symm locals #v[] m caller

theorem statement_update : statementCompiled.update #v[2,3] = #v[3,~~~(3 : Scalar.Word)] := by decide

theorem oversized (m : Evm.Machine) (caller : Vector Evm.Word 1023) :
 Evm.run model {m with stack := [coreWord dirty,coreWord 0]++caller.toList} =
 .ok {m with stack := coreWord (compiled.value #v[dirty,0])::([coreWord dirty,coreWord 0]++caller.toList)} 0 ∧
 ([coreWord dirty,coreWord 0]++caller.toList).length > 1024 := by
 constructor
 · exact model_run #v[dirty,0] m caller.toList
 · simp only [List.length_append,List.length_cons,List.length_nil,Vector.length_toList]; omega

def observed (a b : Scalar.Word) := match Evm.run model
 {Evm.Machine.init with stack := [coreWord a,coreWord b,.slot (.root 17)]} with
 | .ok m skip => some (m.stack,skip)
 | _ => none
#guard observed 2 3 = some ([coreWord 3,coreWord 2,coreWord 3,.slot (.root 17)],0)
#guard observed 5 5 = some ([coreWord 25,coreWord 5,coreWord 5,.slot (.root 17)],0)
#guard observed dirty 0 = some ([coreWord (compiled.value #v[dirty,0]),coreWord dirty,coreWord 0,.slot (.root 17)],0)
#guard (NumericMachine.selectCode code).isNone
#guard (PureExpressions.compile 5 expr).isNone
#guard (compiled.lowered.code 14).isNone
#guard (compiled.lowered.code 16).isNone
#guard match Evm.run model Evm.Machine.init with | .fault => true | _ => false
#guard match Evm.Instr.step .exp {Evm.Machine.init with stack := [coreWord 2]} with | .fault => true | _ => false
#guard (WordMachine.selectInstr (.op .SSTORE)).isNone
#guard (WordMachine.selectInstr (.op .CLZ)).isNone
/-- info: 'Solidity.Yul.Compilation.WordExecution.Controls.boundary_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms boundary_run
/-- info: 'Solidity.Yul.Compilation.WordExecution.Controls.dirty_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms dirty_distinct
/-- info: 'Solidity.Yul.Compilation.WordExecution.Controls.actual_visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_visit
/-- info: 'Solidity.Yul.Compilation.WordExecution.Controls.actual_emission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_emission
/-- info: 'Solidity.Yul.Compilation.WordExecution.Controls.actual_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_selection
/-- info: 'Solidity.Yul.Compilation.WordExecution.Controls.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source
/-- info: 'Solidity.Yul.Compilation.WordExecution.Controls.model_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_run
/-- info: 'Solidity.Yul.Compilation.WordExecution.Controls.shifted_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shifted_run
/-- info: 'Solidity.Yul.Compilation.WordExecution.Controls.concrete_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms concrete_value
/-- info: 'Solidity.Yul.Compilation.WordExecution.Controls.equal_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms equal_value
/-- info: 'Solidity.Yul.Compilation.WordExecution.Controls.zero_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_value
/-- info: 'Solidity.Yul.Compilation.WordExecution.Controls.concrete_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms concrete_run
/-- info: 'Solidity.Yul.Compilation.WordExecution.Controls.statement_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms statement_run
/-- info: 'Solidity.Yul.Compilation.WordExecution.Controls.statement_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms statement_update
/-- info: 'Solidity.Yul.Compilation.WordExecution.Controls.oversized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms oversized
end Solidity.Yul.Compilation.WordExecution.Controls
