import Solidity.Yul.Compilation.NumericExecution
import Solidity.Yul.Compilation.ScopedVisitorShapesControls

/-! Actual ten-operator original expression plus a nested scoped statement
run in the existing compiler machine. Symbolic callers/nonstack fields remain
arbitrary; model success is kept separate from native1024 capacity. -/
namespace Solidity.Yul.Compilation.NumericExecution.Controls
open Backend Scalar MachineAdapter Closed ProducerExpressions

def bin (op : Solidity.Yul.Pure 2) (a b : Solidity.Yul.Expr [] [] 2 1) :
    Solidity.Yul.Expr [] [] 2 1 := .builtin (.pure op) (Fin.cases a (fun _ => b))
def sum := bin .add (.local 0) (.local 1)
def difference := bin .sub sum (.local 1)
def product := bin .mul difference (.local 1)
def quotient := bin .div product (.local 1)
def remainder := bin .mod quotient (.local 1)
def masked := bin .and remainder (.local 0)
def joined := bin .or masked (.local 1)
def leftShift := bin .shl (.local 1) joined
def rightShift := bin .shr (.local 1) leftShift
def expr := bin .xor rightShift (.local 0)
def compiled := (PureExpressions.compile 11 expr).get (by rfl)
def code := (compiled.lowered.code 0).get (by rfl)
def model := (NumericMachine.selectCode code).get (by rfl)
def shiftedCode := (compiled.lowered.code 7).get (by rfl)
def shiftedModel := (NumericMachine.selectCode shiftedCode).get (by rfl)
def value (op : Backend.Op) (a b : Scalar.Word) : Scalar.Word :=
  (Scalar.binary op).getD (fun _ _ => 0) a b
def result (a b : Scalar.Word) : Scalar.Word :=
  value .XOR (value .SHR b (value .SHL b
    (value .OR (value .AND (value .MOD (value .DIV
      (value .MUL (value .SUB (value .ADD a b) b) b) b) b) a) b))) a
def dirty : Scalar.Word := BitVec.ofNat 256 (2^200+257)

theorem actual_visit : PureExpressions.compile 11 expr = some compiled :=
  (Option.some_get (by rfl)).symm

theorem actual_selection : NumericMachine.selectCode code = some model :=
  (Option.some_get (by rfl)).symm

theorem actual_model : model = [.dup 1,.dup 3,.dup 3,.dup 5,.dup 6,.dup 7,.dup 8,.dup 9,.dup 9,
    .add,.sub,.mul,.div,.mod,.and,.or,.dup 4,.shl,.dup 4,.shr,.xor] := by rfl

theorem value_eq (a b : Scalar.Word) : compiled.value #v[a,b] = result a b := by rfl

theorem source (a b : Scalar.Word) :
    evalExpr 11 .nil True.intro expr compiled.profile (sourceLocals #v[a,b]) =
      some (fun _ => (result a b).toFin) := compiled.source #v[a,b]

theorem model_run (a b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run model {m with stack := [coreWord a,coreWord b]++caller} =
      .ok {m with stack := coreWord (result a b)::([coreWord a,coreWord b]++caller)} 0 := by
  simpa only [Vector.toList_empty,List.nil_append] using
    loweredExpr_machine compiled.lowered 0 code model (Option.some_get (by rfl)).symm
      actual_selection #v[a,b] #v[] m caller

theorem shifted_run (a b : Scalar.Word) (newer : Vector Scalar.Word 7)
    (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run shiftedModel {m with stack := (newer.toList++[a,b]).map coreWord++caller} =
      .ok {m with stack := coreWord (result a b)::((newer.toList++[a,b]).map coreWord++caller)} 0 :=
  loweredExpr_machine compiled.lowered 7 shiftedCode shiftedModel (Option.some_get (by rfl)).symm
    (Option.some_get (by rfl)).symm #v[a,b] newer m caller

/-- Both quotients are zero when divisorzero; the final XOR retains allbits. -/
theorem result_zero (a : Scalar.Word) : result a 0 = a := by
  have zero : ((0 : Scalar.Word) == 0) = true := by rfl
  have bits : (0 : Scalar.Word).toNat = 0 := by rfl
  simp only [result,value,Scalar.binary,Option.getD_some,zero,bits,↓reduceIte]
  simp only [if_pos (by decide : (0 : Nat) < 256)]
  rw [show (0 : Scalar.Word) &&& a = 0 from BitVec.zero_and]
  rw [show (0 : Scalar.Word) ||| 0 = 0 from BitVec.or_zero]
  change (0 : Scalar.Word) ^^^ a = a
  exact BitVec.zero_xor

theorem zero_run (a : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run model {m with stack := [coreWord a,coreWord 0]++caller} =
      .ok {m with stack := coreWord a::([coreWord a,coreWord 0]++caller)} 0 := by
  have same := congrArg (fun x : Scalar.Word =>
    Evm.Out.ok {m with stack := coreWord x::([coreWord a,coreWord 0]++caller)} 0) (result_zero a)
  exact (model_run a 0 m caller).trans same

theorem concrete_result : result 5 2 = 6 := by decide

theorem concrete_run (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run model {m with stack := [coreWord 5,coreWord 2]++caller} =
      .ok {m with stack := coreWord 6::([coreWord 5,coreWord 2]++caller)} 0 :=
  (model_run 5 2 m caller).trans (congrArg (fun x : Scalar.Word =>
    Evm.Out.ok {m with stack := coreWord x::([coreWord 5,coreWord 2]++caller)} 0) concrete_result)

abbrev scope := ScopedVisitorShapes.Controls.compiled
abbrev scopeStmt := ScopedVisitorShapes.Controls.statement
abbrev scopeCode := ScopedVisitorShapes.Controls.code
def scopeModel := (NumericMachine.selectCode scopeCode).get (by rfl)

theorem scope_run (a b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word) :
    Evm.run scopeModel {m with stack := [coreWord a,coreWord b]++caller} =
      .ok {m with stack := [coreWord (ScopedVisitorShapes.Controls.result a b ||| a),
        coreWord (ScopedVisitorShapes.Controls.result a b)]++caller} 0 := by
  have actual := loweredStmt_machine scope.lowered 0 scopeCode scopeModel (Option.some_get (by rfl)).symm
    (Option.some_get (by rfl)).symm #v[a,b] #v[] m caller
  rw [ScopedVisitorShapes.Controls.update] at actual
  simpa only [Vector.toList_empty,List.nil_append] using actual

abbrev large := ScopedVisitorShapes.Controls.largeCompiled
abbrev largeCode := ScopedVisitorShapes.Controls.largeCode
def largeModel := (NumericMachine.selectCode largeCode).get (by rfl)

theorem oversized_model (a b : Scalar.Word) (m : Evm.Machine) (caller : List Evm.Word)
    (sized : caller.length = 1006) :
    Evm.run largeModel {m with stack := [coreWord a,coreWord b]++caller} =
      .ok {m with stack := [coreWord a,coreWord b]++caller} 0 ∧
    stackBound largeCode (2+caller.length) = false := by
  refine ⟨?_,?_⟩
  · simpa only [Vector.toList_empty,List.nil_append] using
      loweredStmt_machine large.lowered 0 largeCode largeModel (Option.some_get (by rfl)).symm
        (Option.some_get (by rfl)).symm #v[a,b] #v[] m caller
  · rw [sized]
    exact ScopedVisitorShapes.Controls.large_capacity_next

def isFault : Evm.Out → Bool | .fault => true | _ => false

#guard (PureExpressions.compile 10 expr).isNone
#guard compiled.lowered.code 8 = none
#guard (NumericMachine.selectCode [.op .EXP]).isNone
#guard (NumericMachine.selectCode [.op .SSTORE]).isNone
#guard (NumericMachine.selectCode [.op .CLZ]).isNone
#guard Scalar.run code [dirty] = none
#guard isFault (Evm.run model {Evm.Machine.init with stack := [coreWord dirty]})
#guard Scalar.run [.op .ADD] [] = none
#guard isFault (Evm.run [.add] Evm.Machine.init)
#guard result dirty dirty = dirty
#guard model.length = 21
theorem symbolic_zero (m : Evm.Machine) :
    Evm.run model {m with stack := [coreWord dirty,coreWord 0,.slot (.root 17)]} =
      .ok {m with stack := [coreWord dirty,coreWord dirty,coreWord 0,.slot (.root 17)]} 0 :=
  zero_run dirty m [.slot (.root 17)]


/-- info: 'Solidity.Yul.Compilation.NumericExecution.Controls.actual_visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_visit
/-- info: 'Solidity.Yul.Compilation.NumericExecution.Controls.actual_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_selection
/-- info: 'Solidity.Yul.Compilation.NumericExecution.Controls.actual_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms actual_model
/-- info: 'Solidity.Yul.Compilation.NumericExecution.Controls.value_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms value_eq
/-- info: 'Solidity.Yul.Compilation.NumericExecution.Controls.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source
/-- info: 'Solidity.Yul.Compilation.NumericExecution.Controls.model_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms model_run
/-- info: 'Solidity.Yul.Compilation.NumericExecution.Controls.shifted_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shifted_run
/-- info: 'Solidity.Yul.Compilation.NumericExecution.Controls.result_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms result_zero
/-- info: 'Solidity.Yul.Compilation.NumericExecution.Controls.zero_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zero_run
/-- info: 'Solidity.Yul.Compilation.NumericExecution.Controls.concrete_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms concrete_result
/-- info: 'Solidity.Yul.Compilation.NumericExecution.Controls.concrete_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms concrete_run
/-- info: 'Solidity.Yul.Compilation.NumericExecution.Controls.scope_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms scope_run
/-- info: 'Solidity.Yul.Compilation.NumericExecution.Controls.oversized_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms oversized_model
/-- info: 'Solidity.Yul.Compilation.NumericExecution.Controls.symbolic_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms symbolic_zero

end Solidity.Yul.Compilation.NumericExecution.Controls
