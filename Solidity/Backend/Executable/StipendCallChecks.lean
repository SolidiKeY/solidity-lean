import Solidity.Backend.Executable.StipendCall
import Solidity.Backend.Executable.ValueCallChecks

/-! Inhabited runtime-dependent requested-gas controls. These are kernel
numeric-slice and encoding facts, not a universal forwarded-gas theorem. -/
namespace Solidity.Backend.Executable.StipendCallChecks
open Semantics ContractWorld Scalar ScalarSequence StipendCall
open ScalarSequenceChecks (caller contract)
open ValueCallChecks (recipient alternate)

def zeroCaller : State contract [.val .int,.val .uint] :=
  {caller with env := (⟨-7,by decide⟩,(⟨0,by decide⟩,()))}

theorem uniform_inputs :
    run (operands recipient) (frameTail zeroCaller [17,29]) =
      some [2300,4097,0,0,0,0,0,BitVec.ofInt 256 (-7),0,17,29] ∧
    run (operands recipient) (frameTail caller [17,29]) =
      some [0,4097,99,0,0,0,0,BitVec.ofInt 256 (-7),99,17,29] ∧
    run (operands recipient) (frameTail alternate [17,29]) =
      some [0,4097,13,0,0,0,0,BitVec.ofInt 256 (-9),13,17,29] := by
  refine ⟨?_,?_,?_⟩ <;> decide +kernel

/-- The same operand program copies the actual runtime amount before testing it. -/
theorem runtime_test_boundary :
    run (ValueCall.emptyBuffers ++ ValueCall.localAmount ++ literal .uint recipient.1 ++
      [.op (.DUP ⟨1,by decide⟩),.op .ISZERO]) (frameTail caller [17,29]) =
      some [0,4097,99,0,0,0,0,BitVec.ofInt 256 (-7),99,17,29] ∧
    run (ValueCall.emptyBuffers ++ ValueCall.localAmount ++ literal .uint recipient.1 ++
      [.op (.DUP ⟨1,by decide⟩),.op .ISZERO]) (frameTail zeroCaller [17,29]) =
      some [1,4097,0,0,0,0,0,BitVec.ofInt 256 (-7),0,17,29] := by
  constructor <;> decide +kernel

/-- A zero-test flag plus the stipend PUSH creates the eighth transient word. -/
theorem peak_boundary :
    run (ValueCall.emptyBuffers ++ ValueCall.localAmount ++ literal .uint recipient.1 ++
      [.op (.DUP ⟨1,by decide⟩),.op .ISZERO] ++ literal .uint stipend)
      (frameTail caller [17,29]) =
      some [2300,0,4097,99,0,0,0,0,BitVec.ofInt 256 (-7),99,17,29] := by decide +kernel

theorem capacity_edges :
    stackBound (operands recipient) 1016 = true ∧
    stackBound (operands recipient) 1017 = false ∧
    stackBound (operands recipient) ((frameTail caller (List.replicate 1014 17)).length : Int) = true ∧
    ¬ stackBound (operands recipient) ((frameTail caller (List.replicate 1015 17)).length : Int) = true := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_⟩
  · exact (local_capacity caller _ recipient).mpr (by rw [List.length_replicate]; omega)
  · rw [local_capacity, List.length_replicate]; omega

theorem wrong_fixed_request :
    run (operands recipient) (frameTail caller [17,29]) ≠
      some [2300,4097,99,0,0,0,0,BitVec.ofInt 256 (-7),99,17,29] ∧
    run (operands recipient) (frameTail zeroCaller [17,29]) ≠
      some [0,4097,0,0,0,0,0,BitVec.ofInt 256 (-7),0,17,29] := by
  constructor <;> decide +kernel

theorem maximum_amount :
    run gasCode [4097,BitVec.ofNat 256 (2^256-1),17,29] =
      some [0,4097,BitVec.ofNat 256 (2^256-1),17,29] := by decide +kernel

theorem byte_and_numeric_boundaries :
    (Backend.encode (StipendCall.code recipient)).length = 76 ∧
    Backend.decode (Backend.encode (StipendCall.code recipient)) = some (StipendCall.code recipient) ∧
    run (StipendCall.code recipient) (frameTail caller [17,29]) = none :=
  ⟨byte_length recipient,decode_bytes recipient,numeric_boundary caller [17,29] recipient⟩

/-- info: 'Solidity.Backend.Executable.StipendCallChecks.uniform_inputs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uniform_inputs

/-- info: 'Solidity.Backend.Executable.StipendCallChecks.runtime_test_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runtime_test_boundary

/-- info: 'Solidity.Backend.Executable.StipendCallChecks.peak_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms peak_boundary

/-- info: 'Solidity.Backend.Executable.StipendCallChecks.capacity_edges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capacity_edges

/-- info: 'Solidity.Backend.Executable.StipendCallChecks.wrong_fixed_request' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_fixed_request

/-- info: 'Solidity.Backend.Executable.StipendCallChecks.maximum_amount' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms maximum_amount

/-- info: 'Solidity.Backend.Executable.StipendCallChecks.byte_and_numeric_boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms byte_and_numeric_boundaries

end Solidity.Backend.Executable.StipendCallChecks
