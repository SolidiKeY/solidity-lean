import SolidityBridge.RoadmapV15.P10.UnsignedNonStrictConsumer
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Exact complete States for unsigned LE/GE, including equality and direction
negatives. These do not assert source/compiler entry or full opcode coverage. -/
namespace SolidityBridge.RoadmapV15.P10.UnsignedNonStrictControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External WordPushFixtures

def expected (op : Backend.Op) (perm : Bool) (result _a _b : Scalar.Word)
    (tail : Scalar.Stack) : EVM.State :=
  {seed 6 perm with
    executionEnv := {(seed 6 perm).executionEnv with
      code := ⟨(Backend.encode (before ++ [.op op,.op .ISZERO] ++ after)).toArray⟩}
    pc := u 5,gasAvailable := u 0,execLength := 43
    stack := (result::tail).map (fun w => UInt256.mk w.toFin)}

private theorem le_fits : (Backend.encode (before ++ [.op .GT])).length < UInt256.size := by decide
private theorem le_same (perm : Bool) (a b : Scalar.Word) (tail : Scalar.Stack) :
    unsignedLeOutput (seed 6 perm) before after a b tail =
      expected .GT perm (Scalar.flag (!(decide (b.toNat < a.toNat)))) a b tail := by
  have gasEq : (unsignedLeOutput (seed 6 perm) before after a b tail).gasAvailable = u 0 := by
    apply congrArg UInt256.mk
    apply Fin.ext
    exact unsigned_le_debit (seed 6 perm) before after a b tail (by change 6 ≤ 6;decide)
  change ({unsignedLeInput (seed 6 perm) before after a b tail with
    pc := u 5,gasAvailable := (unsignedLeOutput (seed 6 perm) before after a b tail).gasAvailable,
    execLength := 43,stack := (Scalar.flag (!(decide (b.toNat < a.toNat)))::tail).map
      (fun w => UInt256.mk w.toFin)} : EVM.State) = _
  rw [gasEq]
  rfl

theorem le_populated (valid : Array UInt256) (perm : Bool) (a b : Scalar.Word)
    (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024) :
    Assembly.driverSteps 2 3 valid (unsignedLeInput (seed 6 perm) before after a b tail) =
      .ok (expected .GT perm (Scalar.flag (!(decide (b.toNat < a.toNat)))) a b tail) := by
  have h := (unsigned_le_execution valid (seed 6 perm) before after a b tail le_fits room
    (by change 6 ≤ 6;decide) 0).2.1
  exact h.trans (congrArg Except.ok (le_same perm a b tail))

private theorem ge_fits : (Backend.encode (before ++ [.op .LT])).length < UInt256.size := by decide
private theorem ge_same (perm : Bool) (a b : Scalar.Word) (tail : Scalar.Stack) :
    unsignedGeOutput (seed 6 perm) before after a b tail =
      expected .LT perm (Scalar.flag (!(decide (a.toNat < b.toNat)))) a b tail := by
  have gasEq : (unsignedGeOutput (seed 6 perm) before after a b tail).gasAvailable = u 0 := by
    apply congrArg UInt256.mk
    apply Fin.ext
    exact unsigned_ge_debit (seed 6 perm) before after a b tail (by change 6 ≤ 6;decide)
  change ({unsignedGeInput (seed 6 perm) before after a b tail with
    pc := u 5,gasAvailable := (unsignedGeOutput (seed 6 perm) before after a b tail).gasAvailable,
    execLength := 43,stack := (Scalar.flag (!(decide (a.toNat < b.toNat)))::tail).map
      (fun w => UInt256.mk w.toFin)} : EVM.State) = _
  rw [gasEq]
  rfl

theorem ge_populated (valid : Array UInt256) (perm : Bool) (a b : Scalar.Word)
    (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024) :
    Assembly.driverSteps 2 3 valid (unsignedGeInput (seed 6 perm) before after a b tail) =
      .ok (expected .LT perm (Scalar.flag (!(decide (a.toNat < b.toNat)))) a b tail) := by
  have h := (unsigned_ge_execution valid (seed 6 perm) before after a b tail ge_fits room
    (by change 6 ≤ 6;decide) 0).2.1
  exact h.trans (congrArg Except.ok (ge_same perm a b tail))

def low : PrimTy.uint.Denote := ⟨7,by decide⟩
def high : PrimTy.uint.Denote := ⟨513,by decide⟩
def maximum : Scalar.Word := BitVec.ofNat 256 ((2^256 : Nat)-1)
def topBit : Scalar.Word := BitVec.ofNat 256 (2^255 : Nat)

theorem typed_clients (valid : Array UInt256) :
    Scalar.run Scalar.uintLe.code (Scalar.encodeValue .uint low::Scalar.encodeValue .uint high::spill) =
      some (Scalar.encodeValue .bool true::spill) ∧
    Scalar.run Scalar.uintGe.code (Scalar.encodeValue .uint low::Scalar.encodeValue .uint high::spill) =
      some (Scalar.encodeValue .bool false::spill) ∧
    Assembly.driverSteps 2 3 valid (unsignedLeInput (seed 6 true) before after
      (Scalar.encodeValue .uint low) (Scalar.encodeValue .uint high) spill) =
      .ok (expected .GT true 1 (Scalar.encodeValue .uint low) (Scalar.encodeValue .uint high) spill) ∧
    Assembly.driverSteps 2 3 valid (unsignedGeInput (seed 6 false) before after
      (Scalar.encodeValue .uint low) (Scalar.encodeValue .uint high) spill) =
      .ok (expected .LT false 0 (Scalar.encodeValue .uint low) (Scalar.encodeValue .uint high) spill) := by
  have le := selected_unsigned_le_execution valid (seed 6 true) before after low high spill le_fits
    (by decide) (by decide) 0
  have ge := selected_unsigned_ge_execution valid (seed 6 false) before after low high spill ge_fits
    (by decide) (by decide) 0
  have leval : BinOp.le.evalT (p := .uint) rfl low high = some true := by rfl
  have geval : BinOp.ge.evalT (p := .uint) rfl low high = some false := by rfl
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [leval,Option.map_some] using le.1
  · simpa only [geval,Option.map_some] using ge.1
  · exact le.2.1.trans (congrArg Except.ok (le_same true _ _ spill))
  · exact ge.2.1.trans (congrArg Except.ok (ge_same false _ _ spill))

theorem equality_and_extremes (valid : Array UInt256) :
    Assembly.driverSteps 2 3 valid (unsignedLeInput (seed 6 true) before after 7 7 spill) =
      .ok (expected .GT true 1 7 7 spill) ∧
    Assembly.driverSteps 2 3 valid (unsignedGeInput (seed 6 false) before after 7 7 spill) =
      .ok (expected .LT false 1 7 7 spill) ∧
    Assembly.driverSteps 2 3 valid (unsignedLeInput (seed 6 false) before after maximum 0 spill) =
      .ok (expected .GT false 0 maximum 0 spill) ∧
    Assembly.driverSteps 2 3 valid (unsignedGeInput (seed 6 true) before after maximum 0 spill) =
      .ok (expected .LT true 1 maximum 0 spill) ∧
    (expected .GT true 1 7 7 spill).stack ≠ [u 0,u 258,u 513] := by
  exact ⟨le_populated valid true 7 7 spill (by decide),ge_populated valid false 7 7 spill (by decide),
    le_populated valid false maximum 0 spill (by decide),ge_populated valid true maximum 0 spill (by decide),
    by decide⟩

theorem boundaries (valid : Array UInt256) :
    Assembly.driverSteps 2 3 valid (unsignedLeInput (seed 6 true) before after 0 0 []) =
      .ok (expected .GT true 1 0 0 []) ∧
    Assembly.driverSteps 2 3 valid
      (unsignedGeInput (seed 6 false) before after topBit 0 (List.replicate 1022 9)) =
      .ok (expected .LT false 1 topBit 0 (List.replicate 1022 9)) := by
  exact ⟨le_populated valid true 0 0 [] (by decide),
    ge_populated valid false topBit 0 (List.replicate 1022 9)
      (by simp only [List.length_replicate];omega)⟩

theorem resource_refusals (valid : Array UInt256) :
    Assembly.driverSteps 2 3 valid (unsignedLeInput (seed 5 false) before after 7 7 spill) =
      .error .OutOfGass ∧
    Assembly.driverSteps 2 3 valid (unsignedGeInput (seed 5 true) before after 7 7 spill) =
      .error .OutOfGass ∧
    Assembly.driverSteps 2 2 valid (unsignedGeInput (seed 6 false) before after 7 7 spill) =
      .error .OutOfFuel := by
  exact ⟨rfl,rfl,rfl⟩

theorem ordered_observation :
    (expected .GT true 1 7 513 spill).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x11,0x15,0x00] ∧
    (expected .LT false 1 maximum 0 spill).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x10,0x15,0x00] ∧
    (expected .GT true 1 7 513 spill).stack = [u 1,u 258,u 513] ∧
    (expected .GT true 1 7 513 spill).stack ≠ [u 513,u 258,u 1] ∧
    (expected .GT true 1 7 513 spill).returnData.data.toList = [0xcc,0xdd] ∧
    (expected .LT false 1 maximum 0 spill).H_return.data.toList = [0xee,0xff] ∧
    (expected .LT false 1 maximum 0 spill).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (expected .GT true 1 7 513 spill).memory = (seed 6 true).memory ∧
    (expected .LT false 1 maximum 0 spill).accountMap = accounts ∧
    (expected .LT false 1 maximum 0 spill).σ₀ = accounts ∧
    (expected .LT false 1 maximum 0 spill).substate = (seed 6 false).substate := by
  exact ⟨rfl,rfl,rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms le_populated
#print axioms ge_populated
#print axioms typed_clients
#print axioms equality_and_extremes
#print axioms boundaries
#print axioms resource_refusals
#print axioms ordered_observation
end SolidityBridge.RoadmapV15.P10.UnsignedNonStrictControls
