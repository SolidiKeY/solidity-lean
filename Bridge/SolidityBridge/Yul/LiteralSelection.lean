import SolidityBridge.Yul.WriteSelection
import Solidity.Yul.Compilation.ScopedStatements
/-! Real numeric PUSH32 certificates and intrinsic scope consumers. Model PUSH
width erasure is not native byte/PC/resource adequacy. Earlier selectors and
source admission remain unchanged; source/G24 and physical views remain open. -/
namespace SolidityBridge.Yul.LiteralSelection
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation MachineAdapter

theorem push_success :
∀ (value : Solidity.Backend.Scalar.Word) (input output : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
    m.stack = Solidity.Backend.Selection.irStack input →
    (Solidity.Evm.Instr.step (.push (Solidity.Yul.Compilation.MachineAdapter.coreWord value)) m =
      .ok {m with stack := Solidity.Backend.Selection.irStack output} 0 ↔
      Solidity.Backend.Scalar.run [Solidity.Backend.Scalar.pushWord value] input = some output) := by
  intro value input output m represented
  have target : coreWord value :: irStack input = irStack (value::input) := by
    calc
      coreWord value :: irStack input = (value::input).map coreWord := by
        rw [ArithmeticSelection.irStack_words input]
        rfl
      _ = irStack (value::input) := (ArithmeticSelection.irStack_words _).symm
  have actual : Evm.Instr.step (.push (coreWord value)) m = .ok {m with stack := irStack (value::input)} 0 := by
    simp only [Evm.Instr.step,represented,target,Evm.Machine.next]
  have scalar : Scalar.run [pushWord value] input = some (value::input) := by
    simp only [Scalar.run,step_pushWord,Option.bind_some]
  rw [actual,scalar]
  constructor
  · intro equal
    have mapped : irStack (value::input) = irStack output := congrArg Evm.Machine.stack (Evm.Out.ok.inj equal).1
    exact congrArg some (ArithmeticSelection.irStack_injective mapped)
  · intro equal
    cases Option.some.inj equal
    rfl

theorem push_refusal :
∀ (value : Solidity.Backend.Scalar.Word) (input : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
    m.stack = Solidity.Backend.Selection.irStack input →
    (Solidity.Evm.Instr.step (.push (Solidity.Yul.Compilation.MachineAdapter.coreWord value)) m = .fault ↔
      Solidity.Backend.Scalar.run [Solidity.Backend.Scalar.pushWord value] input = none) := by
  intro value input m _represented
  simp only [Evm.Instr.step,Evm.Machine.next,Scalar.run,step_pushWord,Option.bind_some,reduceCtorEq]

def push (value : Scalar.Word) : InstructionCertificate (.push (coreWord value)) :=
  ⟨[pushWord value],push_success value,push_refusal value⟩

/-- Numeric literals only; symbolic model slots are not numeric PUSH encodings. -/
def select : (i : Evm.Instr) → Option (InstructionCertificate i)
  | .push (.val n) => some (push (BitVec.ofFin n))
  | .push (.slot _) => none
  | i => WriteSelection.select i

def letBody : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 3 := .seq
  (.assign (fun _ : Fin 1 => .local 1) (.local 0))
  (.assign (fun _ : Fin 1 => .local 2)
    (.builtin (.pure .add) (Fin.cases (.local 1) (fun _ => .local 2))))
def letStatement (literal : Scalar.Word) : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
  .let_ 1 (.literal literal.toFin) letBody
def letCompiled (literal : Scalar.Word) :=
  (ScopedStatements.compile 5 (letStatement literal)).get (by rfl)
def letIR (literal : Scalar.Word) : List Evm.Instr :=
  [.push (coreWord literal),.dup 1,.swap 2,.pop,.dup 3,.dup 3,.add,.swap 3,.pop,.pop]
def letCertificates (literal : Scalar.Word) : SelectionSequence.Certificates (letIR literal) :=
  fun i member => (select i).get (by
    simp only [letIR,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same | same | same | same | same | same | same | same | same <;> subst i <;> rfl)

def zeroBody : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 4 := .seq
  (.assign (fun _ : Fin 1 => .local 0) (.local 2))
  (.assign (fun _ : Fin 1 => .local 3)
    (.builtin (.pure .add) (Fin.cases (.local 0) (fun _ => .local 1))))
def zeroStatement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 := .zero 2 zeroBody
def zeroCompiled := (ScopedStatements.compile 5 zeroStatement).get (by rfl)
def zeroIR : List Evm.Instr :=
  [.push (coreWord 0),.push (coreWord 0),.dup 3,.swap 1,.pop,.dup 2,.dup 2,.add,.swap 4,.pop,.pop,.pop]
def zeroCertificates : SelectionSequence.Certificates zeroIR :=
  fun i member => (select i).get (by
    simp only [zeroIR,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same | same | same | same | same | same | same | same | same | same | same <;> subst i <;> rfl)

/-- Real source scope/compiler/certificate instances, with code identities closed. -/
abbrev let_model (literal : Scalar.Word) :=
  WriteSelection.statement_model (letCompiled literal) (letIR literal) (letCertificates literal) (by rfl)
abbrev zero_model :=
  WriteSelection.statement_model zeroCompiled zeroIR zeroCertificates (by rfl)

end SolidityBridge.Yul.LiteralSelection
