import SolidityBridge.Yul.ComparisonSelection
/-! Unary numeric instruction certificates over the actual Scalar compiler
selections and existing VY1 word steps. No source AST/state/convention or word
semantics is added. Native/G24/resource correspondence remains separate. -/
namespace SolidityBridge.Yul.UnarySelection
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation MachineAdapter

/-- Exact executor facts, concretely discharged below for ISZERO and NOT. -/
structure UnaryEvidence (i : Evm.Instr) (selection : UnarySelection) : Prop where
  scalarEmpty : Scalar.step (.op selection.opcode) [] = none
  modelEmpty : ∀ m : Evm.Machine, i.step {m with stack := []} = .fault
  modelOne : ∀ (a : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word),
    i.step {m with stack := coreWord a :: tail} =
      .ok {m with stack := coreWord (selection.value a) :: tail} 0

theorem scalar_outcome :
∀ (i : Solidity.Evm.Instr) (selection : Solidity.Yul.Compilation.UnarySelection) (facts : SolidityBridge.Yul.UnarySelection.UnaryEvidence i selection) (input : Solidity.Backend.Scalar.Stack),
 Solidity.Backend.Scalar.run [.op selection.opcode] input = match input with
 | a::tail => some (selection.value a::tail)
 | [] => none := by
  intro i selection facts input
  cases input with
  | nil => simp only [Solidity.Backend.Scalar.run,facts.scalarEmpty,Option.bind_none]
  | cons a tail => simp only [Solidity.Backend.Scalar.run,selection.correct,Option.bind_some]

theorem model_outcome :
∀ (i : Solidity.Evm.Instr) (selection : Solidity.Yul.Compilation.UnarySelection) (facts : SolidityBridge.Yul.UnarySelection.UnaryEvidence i selection) (input : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
 m.stack = Solidity.Backend.Selection.irStack input →
 i.step m = match input with
 | a::tail => .ok {m with stack := Solidity.Backend.Selection.irStack (selection.value a::tail)} 0
 | [] => .fault := by
  intro i selection facts input m represented
  have patched : {m with stack := Solidity.Backend.Selection.irStack input} = m := by rw [←represented]
  cases input with
  | nil =>
    have law := facts.modelEmpty m
    change i.step {m with stack := Solidity.Backend.Selection.irStack []} = .fault at law
    rw [patched] at law
    exact law
  | cons a tail =>
    have law := facts.modelOne a m (Solidity.Backend.Selection.irStack tail)
    rw [←SolidityBridge.Yul.QuotientSelection.stack_cons a tail,patched,
      ←SolidityBridge.Yul.QuotientSelection.stack_cons (selection.value a) tail] at law
    exact law

theorem bridge_step :
∀ (op : Solidity.Yul.Pure 1) (bridge : Solidity.Yul.Compilation.WordExpressions.UnaryBridge op)
 (i : Solidity.Evm.Instr)
 (producer : ∀ (m : Solidity.Evm.Machine) (x : Solidity.Yul.Word) (tail : List Solidity.Evm.Word),
 i.step {m with stack := .val x::tail} = .ok {m with stack := .val (op.eval (fun _ => x))::tail} 0)
 (a : Solidity.Backend.Scalar.Word) (m : Solidity.Evm.Machine) (tail : List Solidity.Evm.Word),
 i.step {m with stack := Solidity.Yul.Compilation.MachineAdapter.coreWord a::tail} =
 .ok {m with stack := Solidity.Yul.Compilation.MachineAdapter.coreWord (bridge.selection.value a)::tail} 0 := by
  intro op bridge i producer a m tail
  have law := producer m a.toFin tail
  rw [←bridge.agrees a] at law
  exact law

def certificate :
∀ (i : Solidity.Evm.Instr) (selection : Solidity.Yul.Compilation.UnarySelection),
 SolidityBridge.Yul.UnarySelection.UnaryEvidence i selection →
 Solidity.Backend.Selection.InstructionCertificate i := by
  intro i selection facts
  refine ⟨[.op selection.opcode],?_,?_⟩
  · intro input output m represented
    rw [SolidityBridge.Yul.UnarySelection.model_outcome i selection facts input m represented,
      SolidityBridge.Yul.UnarySelection.scalar_outcome i selection facts input]
    cases input with
    | nil => simp only [reduceCtorEq]
    | cons a tail =>
      constructor
      · intro equal
        have mapped : Solidity.Backend.Selection.irStack (selection.value a::tail) = Solidity.Backend.Selection.irStack output :=
          congrArg Solidity.Evm.Machine.stack (Solidity.Evm.Out.ok.inj equal).1
        exact congrArg some (SolidityBridge.Yul.ArithmeticSelection.irStack_injective mapped)
      · intro equal
        cases Option.some.inj equal
        rfl
  · intro input m represented
    rw [SolidityBridge.Yul.UnarySelection.model_outcome i selection facts input m represented,
      SolidityBridge.Yul.UnarySelection.scalar_outcome i selection facts input]
    cases input with
    | nil => simp only
    | cons a tail => simp only [reduceCtorEq]

def iszeroFacts : UnaryEvidence .iszero WordExpressions.iszeroBridge.selection :=
  ⟨rfl,fun _ => rfl,bridge_step .iszero WordExpressions.iszeroBridge .iszero Solidity.Yul.EvmBitwise.step_iszero⟩
def iszero : InstructionCertificate .iszero := certificate .iszero _ iszeroFacts

def notFacts : UnaryEvidence .not WordExpressions.notBridge.selection :=
  ⟨rfl,fun _ => rfl,bridge_step .not WordExpressions.notBridge .not Solidity.Yul.EvmBitwise.step_not⟩
def not : InstructionCertificate .not := certificate .not _ notFacts

def select : (i : Evm.Instr) → Option (InstructionCertificate i)
  | .iszero => some iszero
  | .not => some not
  | i => ComparisonSelection.select i

def compileLeaf : (p : Backend.Program) → Option (ControlRealization.Slice p) :=
  ControlRealization.selectSliceUsing SignedMachine.selectCode select
def compileBlock : (b : Backend.Block) → Option (ControlRealization.Realization b) :=
  ControlRealization.selectBlockWith compileLeaf

def unaryExpression (op : Solidity.Yul.Pure 1) (arg : Solidity.Yul.Expr [] [] 3 1) :
    Solidity.Yul.Expr [] [] 3 1 := .builtin (.pure op) (fun _ => arg)
def assignment (target : Fin 3) (op : Solidity.Yul.Pure 1) (arg : Fin 3) :
    Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 :=
  .assign (fun _ : Fin 1 => .local target) (unaryExpression op (.local arg))
def body : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 :=
  .seq (assignment 0 .not 0) (.seq (assignment 1 .iszero 0) (assignment 2 .not 1))
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 :=
  .if_ (unaryExpression .iszero (unaryExpression .not (.local 0))) body

def compiled := (NormalControl.compile 6 statement).get (by rfl)
def block := (compiled.emit 0).get (by rfl)
def selected := (compileBlock block).get (by rfl)
def lowering := ControlCompleteness.selected_lowering_with compileLeaf selected (by rfl)
abbrev source_model := ControlRealization.source_model compiled 0 block (by rfl) selected

def prefixedBlock := (compiled.emit 2).get (by rfl)
def prefixed := (compileBlock prefixedBlock).get (by rfl)
def prefixed_lowering := ControlCompleteness.selected_lowering_with compileLeaf prefixed (by rfl)
abbrev prefixed_source_model := ControlRealization.source_model compiled 2 prefixedBlock (by rfl) prefixed


/-- Heights only: operand existence is separately established by execution. -/
theorem iszero_capacity :
∀ h : Int, Solidity.Backend.Scalar.stackBound [.op .ISZERO] h = Solidity.Backend.Scalar.safeHeight h := by
  intro h
  simp only [Solidity.Backend.Scalar.stackBound,Solidity.Backend.Scalar.heightTrace,
    Solidity.Backend.Scalar.stackDelta,Solidity.Backend.Scalar.numericDelta,
    Solidity.Backend.Scalar.unary,Option.isSome_some,if_true,Int.add_zero,
    List.all_cons,List.all_nil,Bool.and_true,Bool.and_self]

theorem not_capacity :
∀ h : Int, Solidity.Backend.Scalar.stackBound [.op .NOT] h = Solidity.Backend.Scalar.safeHeight h := by
  intro h
  simp only [Solidity.Backend.Scalar.stackBound,Solidity.Backend.Scalar.heightTrace,
    Solidity.Backend.Scalar.stackDelta,Solidity.Backend.Scalar.numericDelta,
    Solidity.Backend.Scalar.unary,Option.isSome_some,if_true,Int.add_zero,
    List.all_cons,List.all_nil,Bool.and_true,Bool.and_self]

end SolidityBridge.Yul.UnarySelection
