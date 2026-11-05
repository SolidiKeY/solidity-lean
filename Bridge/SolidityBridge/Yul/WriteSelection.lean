import SolidityBridge.Yul.StackSelection
import Solidity.Yul.Compilation.PureStatements
/-! Actual finite SWAP/POP certificates and an intrinsic assignment consumer.
Only existing numeric model/Scalar/source types and executors are used. Native
capacity/gas and general Source/G24/views remain separate. -/
namespace SolidityBridge.Yul.WriteSelection
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation

theorem swap_success :
∀ (n : Fin 16) (input output : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
    m.stack = Solidity.Backend.Selection.irStack input →
    (Solidity.Evm.Instr.step (.swap (n.val+1)) m = .ok {m with stack := Solidity.Backend.Selection.irStack output} 0 ↔
      Solidity.Backend.Scalar.run [.op (.SWAP n)] input = some output) := by
  intro n input output m represented
  cases input with
  | nil =>
    simp only [Evm.Instr.step,represented,irStack,List.map_nil,Scalar.run,Scalar.step,Scalar.swap,Option.bind_none,reduceCtorEq]
  | cons a rest =>
    by_cases bound : n.val<rest.length
    · have found : rest[n.val]? = some rest[n.val] := List.getElem?_eq_getElem bound
      have actual : Evm.Instr.step (.swap (n.val+1)) m =
          .ok {m with stack := irStack (rest[n.val]::rest.set n.val a)} 0 := by
        simp only [Evm.Instr.step,represented,irStack,List.map_cons,List.getElem?_map,found,Option.map_some,Evm.Machine.next]
        rw [← List.map_set]
      have scalar : Scalar.run [.op (.SWAP n)] (a::rest) = some (rest[n.val]::rest.set n.val a) := by
        simp only [Scalar.run,Scalar.step,Scalar.swap,exchange_set a rest n.val bound,Option.map_some,Option.bind_some]
      rw [actual,scalar]
      constructor
      · intro equal
        have mapped : irStack (rest[n.val]::rest.set n.val a) = irStack output :=
          congrArg Evm.Machine.stack (Evm.Out.ok.inj equal).1
        exact congrArg some (ArithmeticSelection.irStack_injective mapped)
      · intro equal
        cases Option.some.inj equal
        rfl
    · have outside : rest.length≤n.val := by omega
      have found : rest[n.val]? = none := List.getElem?_eq_none outside
      simp only [Evm.Instr.step,represented,irStack,List.map_cons,List.getElem?_map,found,Option.map_none,
        Scalar.run,Scalar.step,Scalar.swap,exchange_out_of_range a rest n.val outside,Option.bind_none,reduceCtorEq]

theorem swap_refusal :
∀ (n : Fin 16) (input : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
    m.stack = Solidity.Backend.Selection.irStack input →
    (Solidity.Evm.Instr.step (.swap (n.val+1)) m = .fault ↔ Solidity.Backend.Scalar.run [.op (.SWAP n)] input = none) := by
  intro n input m represented
  cases input with
  | nil =>
    simp only [Evm.Instr.step,represented,irStack,List.map_nil,Scalar.run,Scalar.step,Scalar.swap,Option.bind_none]
  | cons a rest =>
    by_cases bound : n.val<rest.length
    · have found : rest[n.val]? = some rest[n.val] := List.getElem?_eq_getElem bound
      simp only [Evm.Instr.step,represented,irStack,List.map_cons,List.getElem?_map,found,Option.map_some,
        Evm.Machine.next,Scalar.run,Scalar.step,Scalar.swap,exchange_set a rest n.val bound,Option.bind_some,reduceCtorEq]
    · have outside : rest.length≤n.val := by omega
      have found : rest[n.val]? = none := List.getElem?_eq_none outside
      simp only [Evm.Instr.step,represented,irStack,List.map_cons,List.getElem?_map,found,Option.map_none,
        Scalar.run,Scalar.step,Scalar.swap,exchange_out_of_range a rest n.val outside,Option.bind_none]

theorem pop_success :
∀ (input output : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
    m.stack = Solidity.Backend.Selection.irStack input →
    (Solidity.Evm.Instr.step .pop m = .ok {m with stack := Solidity.Backend.Selection.irStack output} 0 ↔
      Solidity.Backend.Scalar.run [.op .POP] input = some output) := by
  intro input output m represented
  cases input with
  | nil =>
    simp only [Evm.Instr.step,represented,irStack,List.map_nil,Scalar.run,Scalar.step,Scalar.pop,Option.bind_none,reduceCtorEq]
  | cons a rest =>
    have actual : Evm.Instr.step .pop m = .ok {m with stack := irStack rest} 0 := by
      simp only [Evm.Instr.step,represented,irStack,List.map_cons,Evm.Machine.next]
    have scalar : Scalar.run [.op .POP] (a::rest) = some rest := rfl
    rw [actual,scalar]
    constructor
    · intro equal
      have mapped : irStack rest = irStack output := congrArg Evm.Machine.stack (Evm.Out.ok.inj equal).1
      exact congrArg some (ArithmeticSelection.irStack_injective mapped)
    · intro equal
      cases Option.some.inj equal
      rfl

theorem pop_refusal :
∀ (input : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
    m.stack = Solidity.Backend.Selection.irStack input →
    (Solidity.Evm.Instr.step .pop m = .fault ↔ Solidity.Backend.Scalar.run [.op .POP] input = none) := by
  intro input m represented
  cases input with
  | nil =>
    simp only [Evm.Instr.step,represented,irStack,List.map_nil,Scalar.run,Scalar.step,Scalar.pop,Option.bind_none]
  | cons a rest =>
    simp only [Evm.Instr.step,Evm.Machine.next,represented,irStack,List.map_cons,Scalar.run,Scalar.step,Scalar.pop,Option.bind_some,reduceCtorEq]

def swap (n : Fin 16) : InstructionCertificate (.swap (n.val+1)) :=
  ⟨[.op (.SWAP n)],swap_success n,swap_refusal n⟩
def pop : InstructionCertificate .pop :=
  ⟨[.op .POP],pop_success,pop_refusal⟩

/-- An extension in this consumer only; earlier selectors are unchanged. -/
def select : (i : Evm.Instr) → Option (InstructionCertificate i)
  | .pop => some pop
  | .swap k =>
    if h : 0<k ∧ k≤16 then some (by
      have index : k-1<16 := by omega
      have same : (k-1)+1=k := by omega
      have result := swap ⟨k-1,index⟩
      change InstructionCertificate (.swap ((k-1)+1)) at result
      rw [same] at result
      exact result)
    else none
  | i => StackSelection.select i

open Solidity.Yul.Closed

def statement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
  .assign (fun _ : Fin 1 => .local 0) (.local 1)
def compiled := (PureStatements.compile 2 statement).get (by rfl)
def assignmentIR : List Evm.Instr := [.dup 2,.swap 1,.pop]
def assignmentCertificates : SelectionSequence.Certificates assignmentIR :=
  fun i member => (select i).get (by
    simp only [assignmentIR,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same | same <;> subst i <;> rfl)

def nextStatement : Solidity.Yul.Stmt [] [] ⟨false,false⟩ 2 :=
  .assign (fun _ : Fin 1 => .local 1)
    (.builtin (.pure .add) (Fin.cases (.local 0) (fun _ => .local 1)))
def sequenceStatement := Solidity.Yul.Stmt.seq statement nextStatement
def sequenceCompiled := (PureStatements.compile 4 sequenceStatement).get (by rfl)
def sequenceIR : List Evm.Instr := assignmentIR ++ [.dup 2,.dup 2,.add,.swap 2,.pop]
def sequenceCertificates : SelectionSequence.Certificates sequenceIR :=
  fun i member => (select i).get (by
    simp only [sequenceIR,assignmentIR,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same | same | same | same | same | same | same <;> subst i <;> rfl)

theorem statement_model :
∀ {fuel n : Nat} {c : Solidity.Yul.Control} {stmt : Solidity.Yul.Stmt [] [] c n}
    (producer : Solidity.Yul.Compilation.ProducerStatements.Compiled fuel stmt)
    (ir : List Solidity.Evm.Instr) (pick : SolidityBridge.Yul.SelectionSequence.Certificates ir),
    producer.lowered.code 0 = some (SolidityBridge.Yul.SelectionSequence.emit ir pick) →
    ∀ (locals : Vector Solidity.Backend.Scalar.Word n) (tail : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
    m.stack = Solidity.Backend.Selection.irStack (locals.toList ++ tail) →
    Solidity.Yul.Closed.evalStmt fuel .nil True.intro stmt producer.profile
      (Solidity.Yul.Compilation.ProducerExpressions.sourceLocals locals) =
      some ⟨Solidity.Yul.Compilation.ProducerExpressions.sourceLocals (producer.update locals),.normal⟩ ∧
    Solidity.Evm.run ir m = .ok {m with stack := Solidity.Backend.Selection.irStack ((producer.update locals).toList ++ tail)} 0 := by
  intro fuel n c stmt producer ir pick emitted locals tail m represented
  have scalar := producer.lowered.correct 0 (SelectionSequence.emit ir pick) emitted locals #v[] tail
  change Scalar.run (SelectionSequence.emit ir pick) (locals.toList ++ tail) =
    some ((producer.update locals).toList ++ tail) at scalar
  have transport := SelectionSequence.execute ir pick (locals.toList ++ tail) m represented
  rw [scalar] at transport
  exact ⟨producer.source locals,transport⟩

/-- Concrete source/compiler/certificate composition, with no emitted-code premise. -/
abbrev assignment_model := statement_model compiled assignmentIR assignmentCertificates (by rfl)
abbrev sequence_model := statement_model sequenceCompiled sequenceIR sequenceCertificates (by rfl)

end SolidityBridge.Yul.WriteSelection
