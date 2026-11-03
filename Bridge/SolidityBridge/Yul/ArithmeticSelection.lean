import Solidity.Backend.Selection.Interface
import Solidity.Yul.Compilation.ArithmeticMachine
/-! Concrete Yul compiler clients of the published selection certificate types.
These are existing compiler-machine/Scalar laws, not native fetched-byte, gas,
world, physical source views or general G24/compiler-pass preservation. -/
namespace SolidityBridge.Yul.ArithmeticSelection
open Solidity Backend Scalar Selection
open Solidity.Yul.Compilation MachineAdapter

theorem irStack_words (s : Scalar.Stack) : irStack s = s.map coreWord := by
  apply List.map_congr_left
  intro w _
  apply congrArg Evm.Word.val
  apply Fin.ext
  change w.toNat % Evm.W = w.toNat
  exact Nat.mod_eq_of_lt w.isLt

theorem irStack_injective : Function.Injective irStack := by
  intro a b h
  rw [irStack_words,irStack_words] at h
  exact (List.map_inj_right (fun _ _ h => coreWord_injective h)).mp h

theorem add_success :
∀ (input output : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
    m.stack = Solidity.Backend.Selection.irStack input →
    (Solidity.Evm.Instr.step .add m = .ok {m with stack := Solidity.Backend.Selection.irStack output} 0 ↔
      Solidity.Backend.Scalar.run [.op .ADD] input = some output) := by
  intro input output m represented
  cases input with
  | nil =>
    simp only [Evm.Instr.step,represented,irStack,List.map_nil,Scalar.run,Scalar.step,numericStep,unary,binary,applyBinary,Option.bind_none,reduceCtorEq]
  | cons a rest =>
    cases rest with
    | nil =>
      simp only [Evm.Instr.step,represented,irStack,List.map_cons,List.map_nil,Scalar.run,Scalar.step,numericStep,unary,binary,applyBinary,Option.bind_none,reduceCtorEq]
    | cons b tail =>
      have inputStack : coreWord a :: coreWord b :: irStack tail = m.stack := by
        calc
          coreWord a :: coreWord b :: irStack tail = (a::b::tail).map coreWord := by
            rw [irStack_words tail]
            rfl
          _ = irStack (a::b::tail) := (irStack_words _).symm
          _ = m.stack := represented.symm
      have targetStack : coreWord (a+b) :: irStack tail = irStack ((a+b)::tail) := by
        calc
          coreWord (a+b) :: irStack tail = ((a+b)::tail).map coreWord := by
            rw [irStack_words tail]
            rfl
          _ = irStack ((a+b)::tail) := (irStack_words _).symm
      have actual : Evm.Instr.step .add m = .ok {m with stack := irStack ((a+b)::tail)} 0 := by
        simpa only [inputStack,targetStack] using ArithmeticMachine.add_step a b m (irStack tail)
      have scalar : Scalar.run [.op .ADD] (a::b::tail) = some ((a+b)::tail) := rfl
      rw [actual,scalar]
      constructor
      · intro equal
        have mapped : irStack ((a+b)::tail) = irStack output :=
          congrArg Evm.Machine.stack (Evm.Out.ok.inj equal).1
        exact congrArg some (irStack_injective mapped)
      · intro equal
        cases Option.some.inj equal
        rfl

theorem add_refusal :
∀ (input : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
    m.stack = Solidity.Backend.Selection.irStack input →
    (Solidity.Evm.Instr.step .add m = .fault ↔ Solidity.Backend.Scalar.run [.op .ADD] input = none) := by
  intro input m represented
  cases input with
  | nil =>
    simp only [Evm.Instr.step,represented,irStack,List.map_nil,Scalar.run,Scalar.step,numericStep,unary,binary,applyBinary,Option.bind_none]
  | cons a rest =>
    cases rest with
    | nil =>
      simp only [Evm.Instr.step,represented,irStack,List.map_cons,List.map_nil,Scalar.run,Scalar.step,numericStep,unary,binary,applyBinary,Option.bind_none]
    | cons b tail =>
      simp only [Evm.Instr.step,Evm.Machine.next,represented,irStack,List.map_cons,Scalar.run,Scalar.step,numericStep,unary,binary,applyBinary,Option.bind_some,reduceCtorEq]

def add : InstructionCertificate .add :=
  ⟨[.op .ADD],add_success,add_refusal⟩

theorem mul_success :
∀ (input output : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
    m.stack = Solidity.Backend.Selection.irStack input →
    (Solidity.Evm.Instr.step .mul m = .ok {m with stack := Solidity.Backend.Selection.irStack output} 0 ↔
      Solidity.Backend.Scalar.run [.op .MUL] input = some output) := by
  intro input output m represented
  cases input with
  | nil =>
    simp only [Evm.Instr.step,represented,irStack,List.map_nil,Scalar.run,Scalar.step,numericStep,unary,binary,applyBinary,Option.bind_none,reduceCtorEq]
  | cons a rest =>
    cases rest with
    | nil =>
      simp only [Evm.Instr.step,represented,irStack,List.map_cons,List.map_nil,Scalar.run,Scalar.step,numericStep,unary,binary,applyBinary,Option.bind_none,reduceCtorEq]
    | cons b tail =>
      have inputStack : coreWord a :: coreWord b :: irStack tail = m.stack := by
        calc
          coreWord a :: coreWord b :: irStack tail = (a::b::tail).map coreWord := by
            rw [irStack_words tail]
            rfl
          _ = irStack (a::b::tail) := (irStack_words _).symm
          _ = m.stack := represented.symm
      have targetStack : coreWord (a*b) :: irStack tail = irStack ((a*b)::tail) := by
        calc
          coreWord (a*b) :: irStack tail = ((a*b)::tail).map coreWord := by
            rw [irStack_words tail]
            rfl
          _ = irStack ((a*b)::tail) := (irStack_words _).symm
      have actual : Evm.Instr.step .mul m = .ok {m with stack := irStack ((a*b)::tail)} 0 := by
        simpa only [inputStack,targetStack] using ArithmeticMachine.mul_step a b m (irStack tail)
      have scalar : Scalar.run [.op .MUL] (a::b::tail) = some ((a*b)::tail) := rfl
      rw [actual,scalar]
      constructor
      · intro equal
        have mapped : irStack ((a*b)::tail) = irStack output :=
          congrArg Evm.Machine.stack (Evm.Out.ok.inj equal).1
        exact congrArg some (irStack_injective mapped)
      · intro equal
        cases Option.some.inj equal
        rfl

theorem mul_refusal :
∀ (input : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
    m.stack = Solidity.Backend.Selection.irStack input →
    (Solidity.Evm.Instr.step .mul m = .fault ↔ Solidity.Backend.Scalar.run [.op .MUL] input = none) := by
  intro input m represented
  cases input with
  | nil =>
    simp only [Evm.Instr.step,represented,irStack,List.map_nil,Scalar.run,Scalar.step,numericStep,unary,binary,applyBinary,Option.bind_none]
  | cons a rest =>
    cases rest with
    | nil =>
      simp only [Evm.Instr.step,represented,irStack,List.map_cons,List.map_nil,Scalar.run,Scalar.step,numericStep,unary,binary,applyBinary,Option.bind_none]
    | cons b tail =>
      simp only [Evm.Instr.step,Evm.Machine.next,represented,irStack,List.map_cons,Scalar.run,Scalar.step,numericStep,unary,binary,applyBinary,Option.bind_some,reduceCtorEq]

def mul : InstructionCertificate .mul :=
  ⟨[.op .MUL],mul_success,mul_refusal⟩

end SolidityBridge.Yul.ArithmeticSelection
