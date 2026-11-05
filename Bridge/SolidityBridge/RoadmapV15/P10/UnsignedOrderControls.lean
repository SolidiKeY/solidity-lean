import SolidityBridge.RoadmapV15.P10.UnsignedOrderConsumer
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Full populated LT/GT observations, typed clients and signedness controls.
These are native reference instruction clients, not source-origin witnesses. -/
namespace SolidityBridge.RoadmapV15.P10.UnsignedOrderControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External WordPushFixtures

def site (op : Backend.Op) (gas : Nat) (perm : Bool) : Site op :=
  ⟨seed gas perm,before,after,by decide⟩
def input (op : Backend.Op) (gas : Nat) (perm : Bool) (a b : Scalar.Word)
    (tail : Scalar.Stack) : EVM.State := (modularSite (site op gas perm) (a::b::tail)).state
def expected (op : Backend.Op) (perm : Bool) (result a b : Scalar.Word)
    (tail : Scalar.Stack) : EVM.State :=
  {input op 6 perm a b tail with
    pc := u 4,gasAvailable := u 3,execLength := 42
    stack := (result::tail).map (fun w => UInt256.mk w.toFin)}

private theorem same (op : Backend.Op) (perm : Bool) (result a b : Scalar.Word) (tail : Scalar.Stack) :
    (Assembly.chargedPrepare (input op 6 perm a b tail) 3).replaceStackAndIncrPC
      ((result::tail).map (fun w => UInt256.mk w.toFin)) = expected op perm result a b tail := by
  simp only [expected,input,site,modularSite,Site.state,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,WordPushFixtures.seed,WordPushFixtures.before,
    WordPushFixtures.u,Backend.encode_cons,Backend.encode_nil,Instr.encode,List.length_append,
    List.length_cons,List.length_nil]
  rfl

theorem lt_populated (valid : Array UInt256) (perm : Bool) (a b : Scalar.Word)
    (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024) :
    Assembly.driverSteps 1 2 valid (input .LT 6 perm a b tail) =
      .ok (expected .LT perm (Scalar.flag (decide (a.toNat < b.toNat))) a b tail) := by
  have h := (unsigned_lt_agreement valid (site .LT 6 perm) a b tail room
    (by change 3 ≤ 6;decide) 0).2.1
  exact h.trans (congrArg Except.ok (same .LT perm _ a b tail))

theorem gt_populated (valid : Array UInt256) (perm : Bool) (a b : Scalar.Word)
    (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024) :
    Assembly.driverSteps 1 2 valid (input .GT 6 perm a b tail) =
      .ok (expected .GT perm (Scalar.flag (decide (b.toNat < a.toNat))) a b tail) := by
  have h := (unsigned_gt_agreement valid (site .GT 6 perm) a b tail room
    (by change 3 ≤ 6;decide) 0).2.1
  exact h.trans (congrArg Except.ok (same .GT perm _ a b tail))

def low : PrimTy.uint.Denote := ⟨7,by decide⟩
def high : PrimTy.uint.Denote := ⟨513,by decide⟩
def negative : Scalar.Word := BitVec.ofInt 256 (-1)
def maximum : Scalar.Word := BitVec.ofNat 256 ((2^256 : Nat)-1)
def topBit : Scalar.Word := BitVec.ofNat 256 (2^255 : Nat)

theorem typed_clients (valid : Array UInt256) :
    Scalar.run Scalar.uintLt.code (Scalar.encodeValue .uint low::Scalar.encodeValue .uint high::spill) =
      some (Scalar.encodeValue .bool true::spill) ∧
    Scalar.run Scalar.uintGt.code (Scalar.encodeValue .uint low::Scalar.encodeValue .uint high::spill) =
      some (Scalar.encodeValue .bool false::spill) ∧
    Assembly.driverSteps 1 2 valid (input .LT 6 true
      (Scalar.encodeValue .uint low) (Scalar.encodeValue .uint high) spill) =
      .ok (expected .LT true 1 (Scalar.encodeValue .uint low) (Scalar.encodeValue .uint high) spill) ∧
    Assembly.driverSteps 1 2 valid (input .GT 6 false
      (Scalar.encodeValue .uint low) (Scalar.encodeValue .uint high) spill) =
      .ok (expected .GT false 0 (Scalar.encodeValue .uint low) (Scalar.encodeValue .uint high) spill) := by
  have lt := selected_unsigned_lt_agreement valid (site .LT 6 true) low high spill (by decide) (by decide) 0
  have gt := selected_unsigned_gt_agreement valid (site .GT 6 false) low high spill (by decide) (by decide) 0
  have leval : BinOp.lt.evalT (p := .uint) rfl low high = some true := by rfl
  have geval : BinOp.gt.evalT (p := .uint) rfl low high = some false := by rfl
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [leval,Option.map_some] using lt.1
  · simpa only [geval,Option.map_some] using gt.1
  · exact lt.2.1.trans (congrArg Except.ok (same .LT true 1 _ _ spill))
  · exact gt.2.1.trans (congrArg Except.ok (same .GT false 0 _ _ spill))

theorem signedness_and_operand_order (valid : Array UInt256) :
    Assembly.driverSteps 1 2 valid (input .LT 6 true negative 0 spill) =
      .ok (expected .LT true 0 negative 0 spill) ∧
    Assembly.driverSteps 1 2 valid (input .GT 6 false negative 0 spill) =
      .ok (expected .GT false 1 negative 0 spill) ∧
    Assembly.driverSteps 1 2 valid (input .LT 6 false 0 negative spill) =
      .ok (expected .LT false 1 0 negative spill) ∧
    UInt256.slt (UInt256.mk negative.toFin) (u 0) = u 1 ∧
    (expected .GT false 1 negative 0 spill).stack ≠ [u 0,u 258,u 513] := by
  exact ⟨lt_populated valid true negative 0 spill (by decide),
    gt_populated valid false negative 0 spill (by decide),
    lt_populated valid false 0 negative spill (by decide),by decide,by decide⟩

theorem boundaries (valid : Array UInt256) :
    Assembly.driverSteps 1 2 valid (input .LT 6 true 0 0 []) = .ok (expected .LT true 0 0 0 []) ∧
    Assembly.driverSteps 1 2 valid (input .GT 6 false maximum maximum spill) =
      .ok (expected .GT false 0 maximum maximum spill) ∧
    Assembly.driverSteps 1 2 valid (input .GT 6 true topBit 0 (List.replicate 1022 9)) =
      .ok (expected .GT true 1 topBit 0 (List.replicate 1022 9)) := by
  exact ⟨lt_populated valid true 0 0 [] (by decide),
    gt_populated valid false maximum maximum spill (by decide),
    gt_populated valid true topBit 0 (List.replicate 1022 9)
      (by simp only [List.length_replicate];omega)⟩

theorem resource_refusals (valid : Array UInt256) :
    EVM.X 2 valid (input .LT 2 false 7 513 spill) = .error .OutOfGass ∧
    EVM.X 2 valid (input .GT 2 true 7 513 spill) = .error .OutOfGass ∧
    Assembly.driverSteps 1 1 valid (input .LT 6 true 7 513 spill) = .error .OutOfFuel ∧
    EVM.X 2 valid ((modularSite (site .GT 6 false) [7]).state) = .error .StackUnderflow := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem ordered_observation :
    (expected .LT true 1 7 513 spill).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x10,0x00] ∧
    (expected .GT false 1 negative 0 spill).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x11,0x00] ∧
    (expected .LT true 1 7 513 spill).stack = [u 1,u 258,u 513] ∧
    (expected .LT true 1 7 513 spill).stack ≠ [u 513,u 258,u 1] ∧
    (expected .LT true 1 7 513 spill).returnData.data.toList = [0xcc,0xdd] ∧
    (expected .GT false 1 negative 0 spill).H_return.data.toList = [0xee,0xff] ∧
    (expected .GT false 1 negative 0 spill).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (expected .LT true 1 7 513 spill).memory = (seed 6 true).memory ∧
    (expected .GT false 1 negative 0 spill).accountMap = accounts ∧
    (expected .GT false 1 negative 0 spill).σ₀ = accounts ∧
    (expected .GT false 1 negative 0 spill).substate = (seed 6 false).substate := by
  exact ⟨rfl,rfl,rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms lt_populated
#print axioms gt_populated
#print axioms typed_clients
#print axioms signedness_and_operand_order
#print axioms boundaries
#print axioms resource_refusals
#print axioms ordered_observation
end SolidityBridge.RoadmapV15.P10.UnsignedOrderControls
