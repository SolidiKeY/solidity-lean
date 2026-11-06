import Solidity.Yul.Compilation.MachineAdapter
import Solidity.Yul.Compilation.LocalScopeLoweringControls
import Solidity.Yul.Compilation.ResultFrameControls
namespace Solidity.Yul.Compilation.MachineAdapter
open Backend Scalar
private def dirty : Word := BitVec.ofNat 256 (2 ^ 200 + 257)

example : stackCode [pushWord dirty] = some [.push (coreWord dirty)] := stackCode_pushWord dirty
example (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.push (coreWord dirty)] { m with stack := tail } =
      .ok { m with stack := coreWord dirty :: tail } 0 := rfl

example (m : Evm.Machine) (locals : Vector Word 16) (tail : List Evm.Word) :
    Evm.run [.dup 16] { m with stack := locals.toList.map coreWord ++ tail } =
      .ok { m with stack := coreWord locals[15] :: (locals.toList.map coreWord ++ tail) } 0 :=
  local_machine ⟨15, by decide⟩ (by decide) locals #v[] m tail

example (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.swap 4, .pop]
      { m with stack := coreWord dirty :: ([100, 101, 8, 7, 9].map coreWord ++ tail) } =
      .ok { m with stack := [100, 101, 8, dirty, 9].map coreWord ++ tail } 0 :=
  write_local_machine ⟨1, by decide⟩ (by decide) #v[8, 7, 9] #v[100, 101] dirty m tail

example (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run [.push (coreWord dirty), .swap 4, .pop]
      { m with stack := [100, 101, 8, 7, 9].map coreWord ++ tail } =
      .ok { m with stack := [100, 101, 8, dirty, 9].map coreWord ++ tail } 0 :=
  assign_literal_machine ⟨1, by decide⟩ (by decide) dirty #v[8, 7, 9] #v[100, 101] m tail

def machineScope : List Evm.Instr := (stackCode scopeCode).get (by rfl)
example : stackCode scopeCode = some machineScope := rfl
example (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run machineScope { m with stack := [8, 7].map coreWord ++ tail } =
      .ok { m with stack := [dirty, 7].map coreWord ++ tail } 0 :=
  loweredStmt_machine scopeCompiled 0 scopeCode machineScope rfl rfl #v[8, 7] #v[] m tail

def machineFrame : List Evm.Instr := (stackCode closedFrame.code).get (by rfl)
example : stackCode closedFrame.code = some machineFrame := rfl
example (m : Evm.Machine) (tail : List Evm.Word) :
    Evm.run machineFrame { m with stack := [dirty, 7, 99].map coreWord ++ tail } =
      .ok { m with stack := [7, dirty].map coreWord ++ tail } 0 :=
  arity_machine closedFrame machineFrame rfl #v[dirty, 7, 99] m tail
example : Evm.run machineFrame
    { Evm.Machine.init with stack := [dirty, 7, 99].map coreWord ++ [.slot (.root 17), coreWord 88] } =
      .ok { Evm.Machine.init with stack := [7, dirty].map coreWord ++ [.slot (.root 17), coreWord 88] } 0 :=
  arity_machine closedFrame machineFrame rfl #v[dirty, 7, 99] Evm.Machine.init
    [.slot (.root 17), coreWord 88]

/-- Width erasure is a model adapter fact, not equality of emitted bytes. -/
example : stackCode [pushByte 1] = some [.push (coreWord 1)] := rfl
example : encode [pushByte 1] ≠ encode [pushWord 1] := by decide +kernel
example : selectStack (.op .ADD) = none := rfl
example : selectStack (.op .SSTORE) = none := rfl
example : selectStack (.op .JUMP) = none := rfl
example : (lowerLocal (n := 17) ⟨16, by decide⟩).code 0 = none := rfl

/-- Underflow of a numeric prefix does not imply core fault with an arbitrary
caller. Do not turn success-only framing into an invalid failure theorem. -/
example : Scalar.run [.op .POP] [] = none := rfl
example (m : Evm.Machine) : Evm.run [.pop] { m with stack := [.slot (.root 17)] } =
    .ok { m with stack := [] } 0 := rfl
example (m : Evm.Machine) : Evm.run [.pop] { m with stack := [] } = .fault := rfl
example (m : Evm.Machine) : Evm.run [.dup 16] { m with stack := [coreWord 1] } = .fault := rfl

/-- The compiler machine is uncapped. Capacity is an independent actual trace
obligation and must not be inferred from this successful execution. -/
example (m : Evm.Machine) : Evm.run [.dup 1]
    { m with stack := [coreWord 9] ++ List.replicate 1024 (.slot (.root 17)) } =
      .ok { m with stack := coreWord 9 ::
        ([coreWord 9] ++ List.replicate 1024 (.slot (.root 17))) } 0 :=
  local_machine ⟨0, by decide⟩ (by decide) #v[9] #v[] m (List.replicate 1024 (.slot (.root 17)))
example : stackBound [readSlot ⟨0, by decide⟩] 1023 = true := by decide +kernel
example : stackBound [readSlot ⟨0, by decide⟩] 1024 = false := by decide +kernel
example : stackBound [readSlot ⟨0, by decide⟩] 1025 = false := by decide +kernel
end Solidity.Yul.Compilation.MachineAdapter
