import SolidityBridge.Yul.LiteralSelection
import Solidity.Yul.EvmArithmetic
/-! Concrete SUB/DIV/MOD instruction certificates from actual VY1 word-step
bodies and existing Scalar compiler selections. No duplicate word semantics,
source AST/state or frontend admission. Older selector tables are unchanged.
Numeric model certificates are not native byte/charged/G24 correspondence. -/
namespace SolidityBridge.Yul.QuotientSelection
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation MachineAdapter

/-- Real binary-operation facts; all concrete instances below discharge every
field from actual executors and producer word proofs, with no assumed run. -/
structure BinaryEvidence (i : Evm.Instr) (selection : BinarySelection) : Prop where
  scalarEmpty : Scalar.step (.op selection.opcode) [] = none
  scalarSingle : ∀ a : Scalar.Word, Scalar.step (.op selection.opcode) [a] = none
  modelEmpty : ∀ m : Evm.Machine, i.step {m with stack := []} = .fault
  modelSingle : ∀ (a : Scalar.Word) (m : Evm.Machine),
    i.step {m with stack := [coreWord a]} = .fault
  modelPair : ∀ (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word),
    i.step {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord (selection.value a b) :: tail} 0

theorem stack_cons (a : Scalar.Word) (tail : Scalar.Stack) :
    irStack (a::tail) = coreWord a :: irStack tail := by
  rw [ArithmeticSelection.irStack_words (a::tail),ArithmeticSelection.irStack_words tail]
  rfl

theorem args_eq (x y : Solidity.Yul.Word) :
    Solidity.Yul.EvmSigned.args x y = Fin.cases x (fun _ => y) := by
  funext i
  have which : i = 0 ∨ i = 1 := by omega
  rcases which with h | h <;> subst i <;> rfl

theorem scalar_outcome (i : Evm.Instr) (selection : BinarySelection)
    (facts : BinaryEvidence i selection) (input : Scalar.Stack) :
    Scalar.run [.op selection.opcode] input =
      match input with
      | a::b::tail => some (selection.value a b :: tail)
      | _ => none := by
  cases input with
  | nil => simp only [Scalar.run,facts.scalarEmpty,Option.bind_none]
  | cons a rest =>
    cases rest with
    | nil => simp only [Scalar.run,facts.scalarSingle,Option.bind_none]
    | cons b tail => simp only [Scalar.run,selection.correct,Option.bind_some]

theorem model_outcome (i : Evm.Instr) (selection : BinarySelection)
    (facts : BinaryEvidence i selection) (input : Scalar.Stack) (m : Evm.Machine)
    (represented : m.stack = irStack input) :
    i.step m = match input with
      | a::b::tail => .ok {m with stack := irStack (selection.value a b :: tail)} 0
      | _ => .fault := by
  have patched : {m with stack := irStack input} = m := by rw [←represented]
  cases input with
  | nil =>
    have law := facts.modelEmpty m
    change i.step {m with stack := irStack []} = .fault at law
    rw [patched] at law
    exact law
  | cons a rest =>
    cases rest with
    | nil =>
      have law := facts.modelSingle a m
      change i.step {m with stack := coreWord a :: irStack []} = .fault at law
      rw [←stack_cons a [],patched] at law
      exact law
    | cons b tail =>
      have law := facts.modelPair a b m (irStack tail)
      rw [←stack_cons b tail,←stack_cons a (b::tail),patched,
        ←stack_cons (selection.value a b) tail] at law
      exact law

/-- Exact published success iff and refusal contract, including operand
underflow. All numerical facts remain real premises at this helper boundary. -/
def certificate (i : Evm.Instr) (selection : BinarySelection)
    (facts : BinaryEvidence i selection) : InstructionCertificate i := by
  refine ⟨[.op selection.opcode],?_,?_⟩
  · intro input output m represented
    rw [model_outcome i selection facts input m represented,scalar_outcome i selection facts input]
    cases input with
    | nil => simp only [reduceCtorEq]
    | cons a rest =>
      cases rest with
      | nil => simp only [reduceCtorEq]
      | cons b tail =>
        constructor
        · intro equal
          have mapped : irStack (selection.value a b :: tail) = irStack output :=
            congrArg Evm.Machine.stack (Evm.Out.ok.inj equal).1
          exact congrArg some (ArithmeticSelection.irStack_injective mapped)
        · intro equal
          cases Option.some.inj equal
          rfl
  · intro input m represented
    rw [model_outcome i selection facts input m represented,scalar_outcome i selection facts input]
    cases input with
    | nil => simp only
    | cons a rest =>
      cases rest with
      | nil => simp only
      | cons b tail => simp only [reduceCtorEq]

/-- Transport actual VY1 word-step bodies through the compiler's actual word
bridge. No arithmetic definition or range proof is duplicated. -/
theorem bridge_step {op : Solidity.Yul.Pure 2} (bridge : ProducerExpressions.BinaryBridge op)
    (i : Evm.Instr)
    (producer : ∀ (m : Evm.Machine) (x y : Solidity.Yul.Word) (tail : List Evm.Word),
      i.step {m with stack := .val x :: .val y :: tail} =
        .ok {m with stack := .val (op.eval (Solidity.Yul.EvmSigned.args x y)) :: tail} 0)
    (a b : Scalar.Word) (m : Evm.Machine) (tail : List Evm.Word) :
    i.step {m with stack := coreWord a :: coreWord b :: tail} =
      .ok {m with stack := coreWord (bridge.selection.value a b) :: tail} 0 := by
  have law := producer m a.toFin b.toFin tail
  rw [args_eq,←bridge.agrees a b] at law
  exact law

/-- Concrete facts: all helper premises are discharged by actual producers. -/
def subFacts : BinaryEvidence .sub ProducerExpressions.subBridge.selection :=
  ⟨rfl,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,
    bridge_step ProducerExpressions.subBridge .sub Solidity.Yul.EvmArithmetic.step_sub⟩
def divFacts : BinaryEvidence .div QuotientExpressions.divBridge.selection :=
  ⟨rfl,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,
    bridge_step QuotientExpressions.divBridge .div Solidity.Yul.EvmArithmetic.step_div⟩
def modFacts : BinaryEvidence .mod QuotientExpressions.modBridge.selection :=
  ⟨rfl,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,
    bridge_step QuotientExpressions.modBridge .mod Solidity.Yul.EvmArithmetic.step_mod⟩

def sub : InstructionCertificate .sub := certificate .sub _ subFacts
def div : InstructionCertificate .div := certificate .div _ divFacts
def mod : InstructionCertificate .mod := certificate .mod _ modFacts

/-- New certificate table only; original tables and refusal controls remain
unchanged. This is target proof selection, not Solidity/Yul admission. -/
def select : (i : Evm.Instr) → Option (InstructionCertificate i)
  | .sub => some sub
  | .div => some div
  | .mod => some mod
  | i => LiteralSelection.select i

def assignment (op : Solidity.Yul.Pure 2) (target : Fin 2) :
    Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
  .assign (fun _ : Fin 1 => .local target)
    (.builtin (.pure op) (Fin.cases (.local 0) (fun _ => .local 1)))
def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
  .seq (assignment .sub 0) (.seq (assignment .div 1) (assignment .mod 0))
def compiled := (PureStatements.compile 5 statement).get (by rfl)
def code : List Evm.Instr :=
  [.dup 2,.dup 2,.sub,.swap 1,.pop,
   .dup 2,.dup 2,.div,.swap 2,.pop,
   .dup 2,.dup 2,.mod,.swap 1,.pop]
def certificates : SelectionSequence.Certificates code :=
  fun i member => (select i).get (by
    simp only [code,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same | same | same | same |
      same | same | same | same | same | same | same | same | same | same <;> subst i <;> rfl)

/-- Original intrinsic source evaluator, actual compiler and concrete complete
instruction certificates compose with no desired run or code-origin premise. -/
abbrev source_model := WriteSelection.statement_model compiled code certificates (by rfl)

end SolidityBridge.Yul.QuotientSelection
