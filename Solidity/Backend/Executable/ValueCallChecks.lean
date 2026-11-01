import Solidity.Backend.Executable.ValueCall
import Solidity.Backend.Executable.ScalarSequenceChecks

/-! Actual emitted CALL operand controls. Gas operands are supplied data, not
forwarded-gas proofs. Scalar.run stops before unsupported CALL semantics. -/
namespace Solidity.Backend.Executable.ValueCallChecks
open Semantics ContractWorld Scalar ScalarSequence ValueCall
open ScalarSequenceChecks (caller contract)

def gas : PrimTy.uint.Denote := ⟨2300,by decide⟩
def zero : PrimTy.uint.Denote := ⟨0,by decide⟩
def one : PrimTy.uint.Denote := ⟨1,by decide⟩
def recipient : Address := ⟨⟨4097,by decide +kernel⟩,by decide +kernel⟩
def highWord : PrimTy.uint.Denote := ⟨(2 : Int)^160-1,by decide +kernel⟩
private theorem high_bound : highWord.1 < (2 : Int)^160 := by decide +kernel
def highRecipient : Address := ⟨highWord,high_bound⟩

/-- Distinct zero/nonzero value inputs have exact chosen gas/value operands;
neither choice asserts how much gas the eventual CALL forwards. -/
theorem literal_inputs :
    run (operandCode zero recipient one) [17,29] = some [0,4097,1,0,0,0,0,17,29] ∧
    run (operandCode gas recipient zero) [17,29] = some [2300,4097,0,0,0,0,0,17,29] := by
  constructor <;> decide +kernel

/-- Inhabited local lowering: uniform actual source read, real DUP6, exact
operand order, protected signed/uint locals and populated spill, derived room. -/
theorem local_client :
    (LocalFrame.uintRead (C := contract)).evalT caller = .ok ⟨99,by decide⟩ ∧
    run (localOperands gas recipient) (frameTail caller [17,29]) =
      some [2300,4097,99,0,0,0,0,BitVec.ofInt 256 (-7),99,17,29] ∧
    stackBound (localOperands gas recipient) ((frameTail caller [17,29]).length : Int) = true ∧
    (Backend.encode (localCode gas recipient)).length = 73 ∧
    Backend.decode (Backend.encode (localCode gas recipient)) = some (localCode gas recipient) := by
  refine ⟨local_source caller, ?_, (local_capacity caller [17,29] gas recipient).mpr (by decide),
    local_byte_length gas recipient, local_decode gas recipient⟩
  exact (local_correct caller [17,29] gas recipient).trans (by decide +kernel)

def alternate : State contract [.val .int,.val .uint] :=
  {caller with env := (⟨-9,by decide⟩,(⟨13,by decide⟩,()))}

/-- The same emitted code reads a changed runtime local, without specializing
it to the first caller's source state. Observe the actual CALL value position. -/
theorem two_callers :
    ((run (localOperands gas recipient) (frameTail caller [17,29])).bind fun st => st[2]?) = some 99 ∧
    ((run (localOperands gas recipient) (frameTail alternate [17,29])).bind fun st => st[2]?) = some 13 := by
  constructor <;> decide +kernel

/-- Unshifted existing DUP2 now selects a buffer zero, not the uint local. -/
theorem wrong_index :
    run (emptyBuffers ++ LocalFrame.uintCode) (frameTail caller [17,29]) =
      some (0 :: [0,0,0,0] ++ frameTail caller [17,29]) ∧
    run (emptyBuffers ++ localAmount) (frameTail caller [17,29]) =
      some (99 :: [0,0,0,0] ++ frameTail caller [17,29]) := by
  constructor
  · exact run_comp (empty_buffers _) rfl
  · exact (local_amount_stage caller [17,29]).trans (by decide +kernel)

theorem wrong_order :
    run (localOperands gas recipient) (frameTail caller [17,29]) ≠
      some [4097,2300,99,0,0,0,0,BitVec.ofInt 256 (-7),99,17,29] := by decide +kernel

/-- Seven operand cells on top of two locals leave at most1015 spill words.
The numeric run alone is deliberately not used as a physical-capacity proof. -/
theorem capacity_edges :
    stackBound (localOperands gas recipient) 1017 = true ∧
    stackBound (localOperands gas recipient) 1018 = false ∧
    ¬ stackBound (localOperands gas recipient)
      ((frameTail caller (List.replicate 1016 17)).length : Int) = true := by
  refine ⟨by decide +kernel,by decide +kernel,?_⟩
  rw [local_capacity, List.length_replicate]
  omega

theorem concrete_bytes :
    Backend.encode emptyBuffers = [0x60,0,0x80,0x80,0x80] ∧
    Backend.encode localAmount = [0x85] ∧
    bytes gas recipient one = Backend.encode (operandCode gas recipient one) ++ [0xf1] ∧
    (bytes gas recipient one).length = 105 :=
  ⟨rfl,rfl,byte_observation gas recipient one,byte_length gas recipient one⟩

/-- Full160-bit input is preserved, with no implicit address-word truncation. -/
theorem address_boundary :
    ((run (operandCode gas highRecipient one) [17,29]).bind fun st => st[1]?).map BitVec.toNat =
      some (2^160-1) := by decide +kernel

/-- Unsupported here is not failed EVM CALL or failed source payment. -/
theorem numeric_limit :
    run (localCode gas recipient) (frameTail caller [17,29]) = none ∧
    Backend.decode (Backend.encode (localCode gas recipient)) = some (localCode gas recipient) :=
  ⟨local_numeric_boundary caller [17,29] gas recipient,local_decode gas recipient⟩

/-- info: 'Solidity.Backend.Executable.ValueCallChecks.literal_inputs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms literal_inputs
/-- info: 'Solidity.Backend.Executable.ValueCallChecks.local_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms local_client
/-- info: 'Solidity.Backend.Executable.ValueCallChecks.two_callers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms two_callers
/-- info: 'Solidity.Backend.Executable.ValueCallChecks.wrong_index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_index
/-- info: 'Solidity.Backend.Executable.ValueCallChecks.wrong_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_order
/-- info: 'Solidity.Backend.Executable.ValueCallChecks.capacity_edges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capacity_edges
/-- info: 'Solidity.Backend.Executable.ValueCallChecks.concrete_bytes' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms concrete_bytes
/-- info: 'Solidity.Backend.Executable.ValueCallChecks.address_boundary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms address_boundary
/-- info: 'Solidity.Backend.Executable.ValueCallChecks.numeric_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms numeric_limit
end Solidity.Backend.Executable.ValueCallChecks
