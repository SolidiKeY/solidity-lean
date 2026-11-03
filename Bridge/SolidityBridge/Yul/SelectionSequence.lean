import SolidityBridge.Yul.ArithmeticSelection
/-! Composition of actual published instruction certificates over existing IR.
The instruction list is the existing compiler IR, not a new AST. Certificates
supply their real selection obligations. Concrete ADD/MUL bodies inhabit them.
This model/Scalar composition is not native, physical capacity or Source/G24. -/
namespace SolidityBridge.Yul.SelectionSequence
open Solidity Backend Scalar Selection

/-- Choose an actual instruction-indexed certificate for each list member. -/
abbrev Certificates (ir : List Evm.Instr) :=
  (i : Evm.Instr) → i ∈ ir → InstructionCertificate i

def emit : (ir : List Evm.Instr) → Certificates ir → Backend.Program
  | [],_ => []
  | i::rest,pick => (pick i (List.mem_cons_self)).code ++
      emit rest (fun j member => pick j (List.mem_cons_of_mem i member))

/-- Constructive selection by the existing instruction, with no new IR. -/
def addMulCertificates : Certificates [.add,.mul] := by
  intro i member
  cases i <;> simp only [List.mem_cons,List.not_mem_nil,or_false,reduceCtorEq] at member
  all_goals first | exact ArithmeticSelection.add | exact ArithmeticSelection.mul

theorem execute :
∀ (ir : List Solidity.Evm.Instr) (pick : SolidityBridge.Yul.SelectionSequence.Certificates ir)
    (input : Solidity.Backend.Scalar.Stack) (m : Solidity.Evm.Machine),
    m.stack = Solidity.Backend.Selection.irStack input →
    Solidity.Evm.run ir m =
      match Solidity.Backend.Scalar.run (SolidityBridge.Yul.SelectionSequence.emit ir pick) input with
      | none => .fault
      | some output => .ok {m with stack := Solidity.Backend.Selection.irStack output} 0 := by
  intro ir
  induction ir with
  | nil =>
    intro pick input m represented
    simp only [emit,Scalar.run,Evm.run,Evm.exec,←represented]
  | cons i rest ih =>
    intro pick input m represented
    let head := pick i List.mem_cons_self
    let more : Certificates rest := fun j member => pick j (List.mem_cons_of_mem i member)
    change Evm.run (i::rest) m =
      match Scalar.run (head.code ++ emit rest more) input with
      | none => .fault
      | some output => .ok {m with stack := irStack output} 0
    rw [Scalar.run_append]
    cases found : Scalar.run head.code input with
    | none =>
      have fault : i.step m = .fault := (head.refusal input m represented).mpr found
      simp only [Option.bind_none,Evm.run,Evm.exec,fault,Evm.Out.bind]
    | some middle =>
      have step : i.step m = .ok {m with stack := irStack middle} 0 :=
        (head.success input middle m represented).mpr found
      have next := ih more middle {m with stack := irStack middle} rfl
      simp only [Option.bind_some,Evm.run,Evm.exec,step,Evm.Out.bind]
      simpa only [Evm.run] using next
end SolidityBridge.Yul.SelectionSequence
