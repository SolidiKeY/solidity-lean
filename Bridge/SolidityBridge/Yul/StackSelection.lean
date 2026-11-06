import SolidityBridge.Yul.SelectionSequence
/-! Actual finite DUP instruction certificates and source-slice consumers.
These are numeric compiler-model/Scalar laws, not native capacity/gas or general
Source/G24. Existing indices, IR, executor and published contracts are unchanged. -/
namespace SolidityBridge.Yul.StackSelection
open Solidity Backend Scalar Selection

theorem dup_success :
∀ (n : Fin 16) (input output : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
    m.stack = Solidity.Backend.Selection.irStack input →
    (Solidity.Evm.Instr.step (.dup (n.val+1)) m = .ok {m with stack := Solidity.Backend.Selection.irStack output} 0 ↔
      Solidity.Backend.Scalar.run [.op (.DUP n)] input = some output) := by
  intro n input output m represented
  cases found : input[n.val]? with
  | none =>
    simp only [Evm.Instr.step,represented,irStack,List.getElem?_map,Nat.add_sub_cancel,found,
      Option.map_none,Scalar.run,Scalar.step,Scalar.duplicate,Option.bind_none,reduceCtorEq]
  | some value =>
    have actual : Evm.Instr.step (.dup (n.val+1)) m =
        .ok {m with stack := irStack (value::input)} 0 := by
      simp only [Evm.Instr.step,represented,irStack,List.getElem?_map,Nat.add_sub_cancel,
        found,Option.map_some,Evm.Machine.next,List.map_cons]
    have scalar : Scalar.run [.op (.DUP n)] input = some (value::input) := by
      simp only [Scalar.run,Scalar.step,Scalar.duplicate,found,Option.map_some,Option.bind_some]
    rw [actual,scalar]
    constructor
    · intro equal
      have mapped : irStack (value::input) = irStack output :=
        congrArg Evm.Machine.stack (Evm.Out.ok.inj equal).1
      exact congrArg some (ArithmeticSelection.irStack_injective mapped)
    · intro equal
      cases Option.some.inj equal
      rfl

theorem dup_refusal :
∀ (n : Fin 16) (input : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
    m.stack = Solidity.Backend.Selection.irStack input →
    (Solidity.Evm.Instr.step (.dup (n.val+1)) m = .fault ↔
      Solidity.Backend.Scalar.run [.op (.DUP n)] input = none) := by
  intro n input m represented
  cases found : input[n.val]? with
  | none =>
    simp only [Evm.Instr.step,represented,irStack,List.getElem?_map,Nat.add_sub_cancel,found,
      Option.map_none,Scalar.run,Scalar.step,Scalar.duplicate,Option.bind_none]
  | some value =>
    simp only [Evm.Instr.step,represented,irStack,List.getElem?_map,Nat.add_sub_cancel,found,
      Option.map_some,Evm.Machine.next,Scalar.run,Scalar.step,Scalar.duplicate,Option.bind_some,reduceCtorEq]

/-- All sixteen real Backend DUPs, preserving the published exact contract. -/
def dup (n : Fin 16) : InstructionCertificate (.dup (n.val+1)) :=
  ⟨[.op (.DUP n)],dup_success n,dup_refusal n⟩

/-- Narrow concrete certificate selection, not a source admission policy. -/
def select : (i : Evm.Instr) → Option (InstructionCertificate i)
  | .add => some ArithmeticSelection.add
  | .mul => some ArithmeticSelection.mul
  | .dup k =>
    if h : 0<k ∧ k≤16 then some (by
      have index : k-1<16 := by omega
      have same : (k-1)+1=k := by omega
      have result := dup ⟨k-1,index⟩
      change InstructionCertificate (.dup ((k-1)+1)) at result
      rw [same] at result
      exact result)
    else none
  | _ => none

/-- Actual compiler read prefixes and ADD/MUL, with inhabited certificate inputs. -/
def addCertificates : SelectionSequence.Certificates [.dup 2,.dup 2,.add] :=
  fun i member => (select i).get (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same | same <;> subst i <;> rfl)
def mulCertificates : SelectionSequence.Certificates [.dup 2,.dup 2,.mul] :=
  fun i member => (select i).get (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same | same <;> subst i <;> rfl)

end SolidityBridge.Yul.StackSelection
