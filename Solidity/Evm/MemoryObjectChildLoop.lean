import Solidity.Evm.MemoryObjectReserve

/-! Target loop steps for distinct empty child allocation. No evaluator budget
is assumed: termination will use the finite loopIterN witness. -/
namespace Solidity.Evm.Memory.Objects

def childrenCondition : List Instr := [.dup 2, .dup 2, .lt]
def storeChild : List Instr := [.dup 4, .dup 3, .add, .push w[1], .add,
  .mstoreAt, .push w[1], .add]
def childrenBody : List Instr := [.push w[0]] ++ allocateArrayCode ++ storeChild

def control (m : Machine) (parent total index : Fin W) : Machine :=
  ((m.push (.val parent)).push (.val total)).push (.val index)

def storeChildMachine (m : Machine) (parent index child : Fin W) : Machine :=
  writeMachine m (wmod (parent.val + index.val + 1)).val (.val child)

theorem childrenCondition_run (m : Machine) (parent total index : Fin W) :
    run childrenCondition (control m parent total index) =
      .ok ((control m parent total index).push (.val (bword (index.val < total.val)))) 0 := by
  simp only [run, childrenCondition, control, Machine.push, exec_cons_zero,
    Instr.step, Machine.next, Out.ok_bind, List.getElem?_cons_succ,
    List.getElem?_cons_zero, exec_nil]

theorem storeChild_run (m : Machine) (parent total index child : Fin W) :
    run storeChild ((control m parent total index).push (.val child)) =
      .ok (control (storeChildMachine m parent index child) parent total
        (wmod (index.val + 1))) 0 := by
  simp only [run, storeChild, control, storeChildMachine, writeMachine, Machine.push,
    exec_cons_zero, Instr.step, Machine.next, Out.ok_bind,
    List.getElem?_cons_succ, List.getElem?_cons_zero, exec_nil,
    wmod_def, Nat.add_mod, Nat.mod_mod, Nat.add_comm]

theorem childrenBody_run (m : Machine) (parent total index cursor : Fin W)
    (hc : m.mem 0 = .val cursor) :
    run childrenBody (control m parent total index) =
      .ok (control (storeChildMachine (allocateMachine m cursor (wmod 0)) parent index cursor)
        parent total (wmod (index.val + 1))) 0 := by
  have hz : Word.val (wmod 0) = w[0] := congrArg Word.val (Fin.ext rfl)
  have hp : run [.push w[0]] (control m parent total index) =
      .ok ((control m parent total index).push (.val (wmod 0))) 0 := by
    rw [hz]
    rfl
  rw [childrenBody, List.append_assoc, run_append_ok hp,
    run_append_ok (allocateArray_run (control m parent total index) cursor (wmod 0) hc)]
  exact storeChild_run (allocateMachine m cursor (wmod 0)) parent total index cursor

end Solidity.Evm.Memory.Objects
