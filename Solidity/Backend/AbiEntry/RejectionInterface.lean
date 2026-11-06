import Solidity.Semantics.AbiEntry
import Solidity.Backend.Failure.Correct

/-! Concrete conditional rejection-consumer signatures, before the V13 port.
The target is the EXISTING checked byte-slice runner, not an abstract execution
relation. This does not certify execution of a calldata decoder. -/
namespace Solidity.Backend.AbiEntry.Interface

/-- Only actual entry reverts select rejection code. Its actual checked run
returns exactly empty revert bytes, retaining the original stack and memory.
Architectural Fits/stack bounds are explicit and the suffix is unreachable. -/
structure RejectionConsumer
    (reject : Solidity.AbiEntry.Input → Nat → List Solidity.AbiEntry.Param → Nat → Option Program) : Prop where
  selected : ∀ input fuel parameters address,
    (reject input fuel parameters address).isSome = true ↔
      Solidity.AbiEntry.entry input fuel parameters = .error .revert
  checked : ∀ input fuel parameters address suffix (machine : Failure.Slice.Machine),
    Solidity.AbiEntry.entry input fuel parameters = .error .revert →
    Failure.Fits address [] → machine.stack.length + 2 ≤ 1024 →
    (reject input fuel parameters address).bind
      (fun code => Failure.Slice.checkedRun (code ++ suffix) machine) =
      some (machine, some (.revert []))

end Solidity.Backend.AbiEntry.Interface
