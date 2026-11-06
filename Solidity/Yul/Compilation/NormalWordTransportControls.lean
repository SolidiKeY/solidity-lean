import Solidity.Yul.Compilation.NormalWordTransport
import Solidity.Yul.Compilation.WordExecutionControls
/-! Original word conditions and dependent arm writes through the existing
normal-control derivation and WordControl selector. Model-only boundaries. -/
namespace Solidity.Yul.Compilation.NormalWordTransport.Controls
open Backend Scalar MachineAdapter Closed ProducerExpressions

def pair : Fin 2 → Solidity.Yul.Expr [] [] 2 1 := Fin.cases (.local 0) (fun _ => .local 1)
def equal : Solidity.Yul.Expr [] [] 2 1 := .builtin (.pure .eq) pair
def highCondition : Solidity.Yul.Expr [] [] 2 1 :=
 .builtin (.pure .exp) (Fin.cases (.local 0) (fun _ => .literal 1))
def body : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 := .seq
 (.assign (fun _ : Fin 1 => .local 1) (.builtin (.pure .not) (fun _ => .local 0)))
 (.assign (fun _ : Fin 1 => .local 0) (.literal 7))
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 := .seq
 (.if_ equal WordExecution.Controls.stmt) (.if_ highCondition body)
def compiled := (NormalControl.compile 11 statement).get (by rfl)
def block := (compiled.emit 0).get (by rfl)
def code := (WordControl.blockCode block).get (by rfl)
def shiftedBlock := (compiled.emit 13).get (by rfl)
def shiftedCode := (WordControl.blockCode shiftedBlock).get (by rfl)
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def highOnly : Scalar.Word := BitVec.ofNat 256 (2^200)

theorem actual_visit : NormalControl.compile 11 statement = some compiled :=
  (Option.some_get (by rfl)).symm

theorem actual_emission : compiled.emit 0 = some block :=
  (Option.some_get (by rfl)).symm

theorem actual_selection : WordControl.blockCode block = some code :=
  (Option.some_get (by rfl)).symm

theorem source (locals : Vector Scalar.Word 2) :
    evalStmt 11 .nil True.intro statement compiled.profile (sourceLocals locals) =
      some ⟨sourceLocals (compiled.update locals),.normal⟩ := compiled.source locals

theorem model_run (locals : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run code {m with stack := locals.toList.map coreWord++caller} =
      .ok {m with stack := (compiled.update locals).toList.map coreWord++caller} 0 := by
  simpa only [Vector.toList_empty,List.nil_append] using
    machine compiled 0 block code actual_emission actual_selection locals #v[] m caller

theorem shifted_run (locals : Vector Scalar.Word 2) (newer : Vector Scalar.Word 13)
    (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run shiftedCode {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
      .ok {m with stack := (newer.toList++(compiled.update locals).toList).map coreWord++caller} 0 :=
  machine compiled 13 shiftedBlock shiftedCode (Option.some_get (by rfl)).symm
    (Option.some_get (by rfl)).symm locals newer m caller

theorem source_model (locals : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
    (evalStmt 11 .nil True.intro statement compiled.profile (sourceLocals locals) =
      some ⟨sourceLocals (compiled.update locals),.normal⟩) ∧
    Evm.run code {m with stack := locals.toList.map coreWord++caller} =
      .ok {m with stack := (compiled.update locals).toList.map coreWord++caller} 0 := by
  simpa only [Vector.toList_empty,List.nil_append] using
    source_machine statement compiled actual_visit 0 block code actual_emission actual_selection
      locals #v[] m caller


theorem unequal_update : compiled.update #v[2,3] = #v[7,~~~(2 : Scalar.Word)] := by decide
theorem equal_update : compiled.update #v[5,5] = #v[7,~~~(25 : Scalar.Word)] := by decide
theorem zero_update : compiled.update #v[0,0] = #v[0,~~~(0 : Scalar.Word)] := by decide
theorem high_update : compiled.update #v[highOnly,0] = #v[7,~~~highOnly] := by decide

theorem high_run (m : Evm.Machine) (caller : List Evm.Word) :
 Evm.run code {m with stack := [coreWord highOnly,coreWord 0]++caller} =
 .ok {m with stack := [coreWord 7,coreWord (~~~highOnly)]++caller} 0 :=
 (model_run #v[highOnly,0] m caller).trans
 (congrArg (fun locals : Vector Scalar.Word 2 => Evm.Out.ok {m with stack := locals.toList.map coreWord++caller} 0) high_update)

theorem oversized (locals : Vector Scalar.Word 2) (m : Evm.Machine)
 (caller : Vector Evm.Word 1023) :
 Evm.run code {m with stack := locals.toList.map coreWord++caller.toList} =
 .ok {m with stack := (compiled.update locals).toList.map coreWord++caller.toList} 0 ∧
 1024 < (locals.toList.map coreWord++caller.toList).length := by
 refine ⟨model_run locals m caller.toList,?_⟩
 simp only [List.length_append,List.length_map,Vector.length_toList]; omega

def observed (a b : Scalar.Word) := match Evm.run code
 {Evm.Machine.init with stack := [coreWord a,coreWord b,.slot (.root 77)]} with
 | .ok m skip => some (m.stack,skip)
 | _ => none
#guard observed 2 3 = some ([coreWord 7,coreWord (~~~(2 : Scalar.Word)),.slot (.root 77)],0)
#guard observed 5 5 = some ([coreWord 7,coreWord (~~~(25 : Scalar.Word)),.slot (.root 77)],0)
#guard observed 0 0 = some ([coreWord 0,coreWord (~~~(0 : Scalar.Word)),.slot (.root 77)],0)
#guard observed highOnly 0 = some ([coreWord 7,coreWord (~~~highOnly),.slot (.root 77)],0)
#guard observed dirty 0 = some ([coreWord 7,coreWord (~~~dirty),.slot (.root 77)],0)
#guard (MachineControl.blockCode block).isNone
#guard (NormalControl.compile 5 statement).isNone
#guard (compiled.emit 14).isNone
#guard match Evm.run code Evm.Machine.init with | .fault => true | _ => false
#guard (NormalControl.compile 3 (Solidity.Yul.Stmt.for_ .skip (.literal 0) .skip .skip :
 Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2)).isNone
/-- info: 'Solidity.Yul.Compilation.NormalWordTransport.Controls.actual_visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_visit
/-- info: 'Solidity.Yul.Compilation.NormalWordTransport.Controls.actual_emission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_emission
/-- info: 'Solidity.Yul.Compilation.NormalWordTransport.Controls.actual_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms actual_selection
/-- info: 'Solidity.Yul.Compilation.NormalWordTransport.Controls.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source
/-- info: 'Solidity.Yul.Compilation.NormalWordTransport.Controls.model_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms model_run
/-- info: 'Solidity.Yul.Compilation.NormalWordTransport.Controls.shifted_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shifted_run
/-- info: 'Solidity.Yul.Compilation.NormalWordTransport.Controls.source_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_model
/-- info: 'Solidity.Yul.Compilation.NormalWordTransport.Controls.unequal_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms unequal_update
/-- info: 'Solidity.Yul.Compilation.NormalWordTransport.Controls.equal_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms equal_update
/-- info: 'Solidity.Yul.Compilation.NormalWordTransport.Controls.zero_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_update
/-- info: 'Solidity.Yul.Compilation.NormalWordTransport.Controls.high_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms high_update
/-- info: 'Solidity.Yul.Compilation.NormalWordTransport.Controls.high_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms high_run
/-- info: 'Solidity.Yul.Compilation.NormalWordTransport.Controls.oversized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms oversized
end Solidity.Yul.Compilation.NormalWordTransport.Controls
