import SolidityBridge.RoadmapV15.P10.InequalityConsumer
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Complete native State clients of the actual two-instruction inequality
consumer, including all intrinsic primitive certificate types. -/
namespace SolidityBridge.RoadmapV15.P10.InequalityControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External WordPushFixtures

private theorem fits : (Backend.encode (before ++ [.op .EQ])).length < UInt256.size := by decide

def expected (perm : Bool) (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  {inequalityInput (seed 6 perm) before after a b tail with
    pc := u 5,gasAvailable := u 0,execLength := 43
    stack := (Scalar.flag (!(a == b))::tail).map (fun w => UInt256.mk w.toFin)}

private theorem output_same (perm : Bool) (a b : Scalar.Word) (tail : Scalar.Stack) :
    inequalityOutput (seed 6 perm) before after a b tail = expected perm a b tail := by
  have gasEq : (inequalityOutput (seed 6 perm) before after a b tail).gasAvailable = u 0 := by
    apply congrArg UInt256.mk
    apply Fin.ext
    exact inequality_debit (seed 6 perm) before after a b tail (by change 6 ≤ 6;decide)
  change ({inequalityInput (seed 6 perm) before after a b tail with
    pc := u 5,gasAvailable := (inequalityOutput (seed 6 perm) before after a b tail).gasAvailable,
    execLength := 43,stack := (Scalar.flag (!(a == b))::tail).map (fun w => UInt256.mk w.toFin)} : EVM.State) = _
  rw [gasEq]
  rfl

theorem populated (valid : Array UInt256) (perm : Bool) (a b : Scalar.Word)
    (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024) :
    Assembly.driverSteps 2 3 valid (inequalityInput (seed 6 perm) before after a b tail) =
      .ok (expected perm a b tail) := by
  have h := (inequality_execution valid (seed 6 perm) before after a b tail fits room
    (by change 6 ≤ 6;decide) 0).2.1
  exact h.trans (congrArg Except.ok (output_same perm a b tail))

theorem typed_budget (valid : Array UInt256) (perm : Bool) (p : PrimTy) (a b : p.Denote)
    (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024) :
    Scalar.run (Scalar.scalarNe p).code (Scalar.encodeValue p a::Scalar.encodeValue p b::tail) =
      (BinOp.neB.evalT (p := p) (by cases p <;> rfl) a b).map
        (fun result => Scalar.encodeValue .bool result::tail) ∧
    Assembly.driverSteps 2 3 valid
      (inequalityInput (seed 6 perm) before after (Scalar.encodeValue p a) (Scalar.encodeValue p b) tail) =
      .ok (expected perm (Scalar.encodeValue p a) (Scalar.encodeValue p b) tail) := by
  have h := selected_inequality_execution valid (seed 6 perm) before after p a b tail fits room
    (by change 6 ≤ 6;decide) 0
  exact ⟨h.1,h.2.1.trans (congrArg Except.ok
    (output_same perm (Scalar.encodeValue p a) (Scalar.encodeValue p b) tail))⟩

def negative : PrimTy.int.Denote := ⟨-7,by decide⟩
def low : PrimTy.uint.Denote := ⟨7,by decide⟩
def high : PrimTy.uint.Denote := ⟨(2^255 : Nat)+7,by decide⟩
def maximum : Scalar.Word := BitVec.ofNat 256 ((2^256 : Nat)-1)

theorem primitive_clients (valid : Array UInt256) :
    Assembly.driverSteps 2 3 valid (inequalityInput (seed 6 false) before after
      (Scalar.encodeValue .bool false) (Scalar.encodeValue .bool true) spill) =
      .ok (expected false (Scalar.encodeValue .bool false) (Scalar.encodeValue .bool true) spill) ∧
    Assembly.driverSteps 2 3 valid (inequalityInput (seed 6 true) before after
      (Scalar.encodeValue .int negative) (Scalar.encodeValue .int negative) spill) =
      .ok (expected true (Scalar.encodeValue .int negative) (Scalar.encodeValue .int negative) spill) ∧
    Assembly.driverSteps 2 3 valid (inequalityInput (seed 6 false) before after
      (Scalar.encodeValue .uint high) (Scalar.encodeValue .uint low) spill) =
      .ok (expected false (Scalar.encodeValue .uint high) (Scalar.encodeValue .uint low) spill) := by
  exact ⟨(typed_budget valid false .bool false true spill (by decide)).2,
    (typed_budget valid true .int negative negative spill (by decide)).2,
    (typed_budget valid false .uint high low spill (by decide)).2⟩

theorem source_and_word_values :
    BinOp.neB.evalT (p := .bool) rfl false true = some true ∧
    BinOp.neB.evalT (p := .int) rfl negative negative = some false ∧
    BinOp.neB.evalT (p := .uint) rfl high low = some true ∧
    (expected false (Scalar.encodeValue .uint high) (Scalar.encodeValue .uint low) spill).stack =
      [u 1,u 258,u 513] ∧
    (expected true (Scalar.encodeValue .int negative) (Scalar.encodeValue .int negative) spill).stack =
      [u 0,u 258,u 513] := by
  exact ⟨rfl,rfl,rfl,by decide,by decide⟩

theorem boundaries (valid : Array UInt256) :
    Assembly.driverSteps 2 3 valid (inequalityInput (seed 6 true) before after 0 0 []) =
      .ok (expected true 0 0 []) ∧
    Assembly.driverSteps 2 3 valid
      (inequalityInput (seed 6 false) before after maximum 0 (List.replicate 1022 9)) =
      .ok (expected false maximum 0 (List.replicate 1022 9)) := by
  exact ⟨populated valid true 0 0 [] (by decide),
    populated valid false maximum 0 (List.replicate 1022 9)
      (by simp only [List.length_replicate];omega)⟩

theorem refusals (valid : Array UInt256) :
    Assembly.driverSteps 2 3 valid (inequalityInput (seed 5 false) before after 7 7 spill) =
      .error .OutOfGass ∧
    Assembly.driverSteps 2 2 valid (inequalityInput (seed 6 true) before after 7 7 spill) =
      .error .OutOfFuel := by
  exact ⟨rfl,rfl⟩

theorem ordered_observation :
    (expected false (Scalar.encodeValue .uint high) (Scalar.encodeValue .uint low) spill).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x14,0x15,0x00] ∧
    (expected false (Scalar.encodeValue .uint high) (Scalar.encodeValue .uint low) spill).stack ≠
      [u 513,u 258,u 1] ∧
    (expected true 7 7 spill).returnData.data.toList = [0xcc,0xdd] ∧
    (expected true 7 7 spill).H_return.data.toList = [0xee,0xff] ∧
    (expected true 7 7 spill).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (expected true 7 7 spill).memory = (seed 6 true).memory ∧
    (expected true 7 7 spill).accountMap = accounts ∧
    (expected true 7 7 spill).σ₀ = accounts ∧
    (expected true 7 7 spill).substate = (seed 6 true).substate := by
  exact ⟨rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms populated
#print axioms typed_budget
#print axioms primitive_clients
#print axioms source_and_word_values
#print axioms boundaries
#print axioms refusals
#print axioms ordered_observation
end SolidityBridge.RoadmapV15.P10.InequalityControls
