import Solidity.Yul.Compilation.NormalNumericTransport
import Solidity.Yul.Compilation.NormalStackTransport

/-! Actual arithmetic guard, dependent true-arm writes and post-join update.
All source indices and existing selector refusal contracts remain unchanged.
Model relative jumps are not native byte-PC/gas/capacity certificates. -/
namespace Solidity.Yul.Compilation.NormalNumericTransport.Controls
open Backend Scalar MachineAdapter Closed ProducerExpressions

def pair : Fin 2 → Solidity.Yul.Expr [] [] 2 1 := Fin.cases (.local 0) (fun _ => .local 1)
def condition : Solidity.Yul.Expr [] [] 2 1 := .builtin (.pure .sub) pair
def body : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 := .seq
  (.assign (fun _ : Fin 1 => .local 0) (.builtin (.pure .add) pair))
  (.assign (fun _ : Fin 1 => .local 1) (.builtin (.pure .xor) pair))
def post : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
  .assign (fun _ : Fin 1 => .local 0) (.builtin (.pure .sub) pair)
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 := .seq (.if_ condition body) post
def compiled := (NormalControl.compile 6 statement).get (by rfl)
def block := (compiled.emit 0).get (by rfl)
def code := (MachineControl.blockCode block).get (by rfl)
def shiftedBlock := (compiled.emit 14).get (by rfl)
def shiftedCode := (MachineControl.blockCode shiftedBlock).get (by rfl)
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)
def highOnly : Scalar.Word := BitVec.ofNat 256 (2^200)

theorem actual_visit : NormalControl.compile 6 statement = some compiled :=
  (Option.some_get (by rfl)).symm

theorem actual_emission : compiled.emit 0 = some block :=
  (Option.some_get (by rfl)).symm

theorem actual_selection : MachineControl.blockCode block = some code :=
  (Option.some_get (by rfl)).symm

theorem source (locals : Vector Scalar.Word 2) :
    evalStmt 6 .nil True.intro statement compiled.profile (sourceLocals locals) =
      some ⟨sourceLocals (compiled.update locals),.normal⟩ := compiled.source locals

theorem model_run (locals : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run code {m with stack := locals.toList.map coreWord++caller} =
      .ok {m with stack := (compiled.update locals).toList.map coreWord++caller} 0 := by
  simpa only [Vector.toList_empty,List.nil_append] using
    machine compiled 0 block code actual_emission actual_selection locals #v[] m caller

theorem shifted_run (locals : Vector Scalar.Word 2) (newer : Vector Scalar.Word 14)
    (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run shiftedCode {m with stack := (newer.toList++locals.toList).map coreWord++caller} =
      .ok {m with stack := (newer.toList++(compiled.update locals).toList).map coreWord++caller} 0 :=
  machine compiled 14 shiftedBlock shiftedCode (Option.some_get (by rfl)).symm
    (Option.some_get (by rfl)).symm locals newer m caller

theorem source_model (locals : Vector Scalar.Word 2) (m : Evm.Machine) (caller : List Evm.Word) :
    (evalStmt 6 .nil True.intro statement compiled.profile (sourceLocals locals) =
      some ⟨sourceLocals (compiled.update locals),.normal⟩) ∧
    Evm.run code {m with stack := locals.toList.map coreWord++caller} =
      .ok {m with stack := (compiled.update locals).toList.map coreWord++caller} 0 := by
  simpa only [Vector.toList_empty,List.nil_append] using
    source_machine statement compiled actual_visit 0 block code actual_emission actual_selection
      locals #v[] m caller

/-- Nonzero arithmetic guard executes both dependent writes and post-join SUB. -/
theorem true_update : compiled.update #v[1,2] = #v[2,1] := by decide

theorem false_update : compiled.update #v[5,5] = #v[0,5] := by decide

theorem high_update : compiled.update #v[highOnly,0] = #v[0,highOnly] := by decide

theorem true_run (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run code {m with stack := [coreWord 1,coreWord 2]++caller} =
      .ok {m with stack := [coreWord 2,coreWord 1]++caller} 0 :=
  (model_run #v[1,2] m caller).trans
    (congrArg (fun locals : Vector Scalar.Word 2 => Evm.Out.ok {m with stack := locals.toList.map coreWord++caller} 0) true_update)

theorem false_run (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run code {m with stack := [coreWord 5,coreWord 5]++caller} =
      .ok {m with stack := [coreWord 0,coreWord 5]++caller} 0 :=
  (model_run #v[5,5] m caller).trans
    (congrArg (fun locals : Vector Scalar.Word 2 => Evm.Out.ok {m with stack := locals.toList.map coreWord++caller} 0) false_update)

theorem high_run (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run code {m with stack := [coreWord highOnly,coreWord 0]++caller} =
      .ok {m with stack := [coreWord 0,coreWord highOnly]++caller} 0 :=
  (model_run #v[highOnly,0] m caller).trans
    (congrArg (fun locals : Vector Scalar.Word 2 => Evm.Out.ok {m with stack := locals.toList.map coreWord++caller} 0) high_update)

/-- A high-only guard is nonzero; narrowing it to a Boolean low bit would
choose the false path and miss the actual [0,highOnly] result. -/
theorem symbolic_high (m : Evm.Machine) :
    Evm.run code {m with stack := [coreWord highOnly,coreWord 0,.slot (.root 77)]} =
      .ok {m with stack := [coreWord 0,coreWord highOnly,.slot (.root 77)]} 0 :=
  high_run m [.slot (.root 77)]

/-- Existing uncapped model success is not a native initial-height proof. -/
theorem oversized (locals : Vector Scalar.Word 2) (m : Evm.Machine)
    (caller : Vector Evm.Word 1023) :
    Evm.run code {m with stack := locals.toList.map coreWord++caller.toList} =
      .ok {m with stack := (compiled.update locals).toList.map coreWord++caller.toList} 0 ∧
    1024 < (locals.toList.map coreWord++caller.toList).length := by
  refine ⟨model_run locals m caller.toList,?_⟩
  simp only [List.length_append,List.length_map,Vector.length_toList]
  decide

def result (a b : Scalar.Word) (caller : List Evm.Word) : Option (List Evm.Word × Nat) :=
  match Evm.run code {Evm.Machine.init with stack := [coreWord a,coreWord b]++caller} with
  | .ok out skip => some (out.stack,skip)
  | _ => none

def projectedSource (a b : Scalar.Word) : Option (Nat × Nat × Bool) :=
  (evalStmt 6 .nil True.intro statement compiled.profile (sourceLocals #v[a,b])).map
    (fun out => ((out.vars 0).val,(out.vars 1).val,out.flow.isNormal))

#guard result 1 2 [.slot (.root 77)] = some ([coreWord 2,coreWord 1,.slot (.root 77)],0)
#guard result 5 5 [.slot (.root 77)] = some ([coreWord 0,coreWord 5,.slot (.root 77)],0)
#guard projectedSource 1 2 = some (2,1,true)
#guard projectedSource 5 5 = some (0,5,true)
#guard (NormalStackTransport.blockCode block).isNone
#guard (NormalControl.compile 5 statement).isNone
#guard (compiled.emit 15).isNone
#guard (NormalControl.compile 3 (Solidity.Yul.Stmt.for_ (c := ⟨false,false⟩) (n := 2)
  .skip (.literal (word 0)) .skip .skip)).isNone
#guard match Evm.run code Evm.Machine.init with | .fault => true | _ => false

/-- info: 'Solidity.Yul.Compilation.NormalNumericTransport.Controls.actual_visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_visit
/-- info: 'Solidity.Yul.Compilation.NormalNumericTransport.Controls.actual_emission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_emission
/-- info: 'Solidity.Yul.Compilation.NormalNumericTransport.Controls.actual_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_selection
/-- info: 'Solidity.Yul.Compilation.NormalNumericTransport.Controls.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source
/-- info: 'Solidity.Yul.Compilation.NormalNumericTransport.Controls.model_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms model_run
/-- info: 'Solidity.Yul.Compilation.NormalNumericTransport.Controls.shifted_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shifted_run
/-- info: 'Solidity.Yul.Compilation.NormalNumericTransport.Controls.source_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_model
/-- info: 'Solidity.Yul.Compilation.NormalNumericTransport.Controls.true_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms true_update
/-- info: 'Solidity.Yul.Compilation.NormalNumericTransport.Controls.false_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms false_update
/-- info: 'Solidity.Yul.Compilation.NormalNumericTransport.Controls.high_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms high_update
/-- info: 'Solidity.Yul.Compilation.NormalNumericTransport.Controls.true_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms true_run
/-- info: 'Solidity.Yul.Compilation.NormalNumericTransport.Controls.false_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms false_run
/-- info: 'Solidity.Yul.Compilation.NormalNumericTransport.Controls.high_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms high_run
/-- info: 'Solidity.Yul.Compilation.NormalNumericTransport.Controls.symbolic_high' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms symbolic_high
/-- info: 'Solidity.Yul.Compilation.NormalNumericTransport.Controls.oversized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms oversized

end Solidity.Yul.Compilation.NormalNumericTransport.Controls
