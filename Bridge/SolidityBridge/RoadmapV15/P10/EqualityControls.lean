import SolidityBridge.RoadmapV15.P10.EqualityConsumer
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Populated exact native EQ states and typed equality clients. These do not
assert source/compiler origin or close an entire opcode correspondence row. -/
namespace SolidityBridge.RoadmapV15.P10.EqualityControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External WordPushFixtures

def site (gas : Nat) (perm : Bool) : Site .EQ :=
  ⟨seed gas perm,before,after,by decide⟩
def input (gas : Nat) (perm : Bool) (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  (modularSite (site gas perm) (a::b::tail)).state
def expected (perm : Bool) (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  {input 6 perm a b tail with
    pc := u 4,gasAvailable := u 3,execLength := 42
    stack := (Scalar.flag (a == b)::tail).map (fun w => UInt256.mk w.toFin)}

theorem populated (valid : Array UInt256) (perm : Bool) (a b : Scalar.Word)
    (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024) :
    Assembly.driverSteps 1 2 valid (input 6 perm a b tail) = .ok (expected perm a b tail) := by
  have h := (equality_agreement valid (site 6 perm) a b tail room (by change 3 ≤ 6;decide) 0).2.1
  have same : (Assembly.chargedPrepare (input 6 perm a b tail) 3).replaceStackAndIncrPC
      ((Scalar.flag (a == b)::tail).map (fun w => UInt256.mk w.toFin)) = expected perm a b tail := by
    simp only [expected,input,site,modularSite,Site.state,Assembly.chargedPrepare,
      EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,WordPushFixtures.seed,
      WordPushFixtures.before,WordPushFixtures.u,Backend.encode_cons,Backend.encode_nil,
      Instr.encode,List.length_append,List.length_cons,List.length_nil]
    rfl
  exact h.trans (congrArg Except.ok same)

def high : Scalar.Word := BitVec.ofNat 256 ((2^255 : Nat)+7)
def maximum : Scalar.Word := BitVec.ofNat 256 ((2^256 : Nat)-1)

def negative : PrimTy.int.Denote := ⟨-7,by decide⟩

theorem typed_client (valid : Array UInt256) :
    Scalar.run (Scalar.scalarEq .int).code
      (Scalar.encodeValue .int negative::Scalar.encodeValue .int negative::spill) =
      some (Scalar.encodeValue .bool true::spill) ∧
    Assembly.driverSteps 1 2 valid
      (input 6 true (Scalar.encodeValue .int negative) (Scalar.encodeValue .int negative) spill) =
      .ok (expected true (Scalar.encodeValue .int negative) (Scalar.encodeValue .int negative) spill) := by
  have h := selected_equality_agreement valid (site 6 true) .int negative negative spill
    (by decide) (by change 3 ≤ 6;decide) 0
  have source : BinOp.eqB.evalT (p := .int) rfl negative negative = some true := by
    rfl
  have same : (Assembly.chargedPrepare
      (input 6 true (Scalar.encodeValue .int negative) (Scalar.encodeValue .int negative) spill) 3).replaceStackAndIncrPC ((Scalar.flag
        (Scalar.encodeValue .int negative == Scalar.encodeValue .int negative)::spill).map
          (fun w => UInt256.mk w.toFin)) =
      expected true (Scalar.encodeValue .int negative) (Scalar.encodeValue .int negative) spill := by
    rfl
  exact ⟨by simpa only [source,Option.map_some] using h.1,h.2.1.trans (congrArg Except.ok same)⟩

theorem equal_and_distinct (valid : Array UInt256) :
    Assembly.driverSteps 1 2 valid (input 6 false 7 7 spill) = .ok (expected false 7 7 spill) ∧
    Assembly.driverSteps 1 2 valid (input 6 true high 7 spill) =
      .ok (expected true high 7 spill) ∧
    (expected false 7 7 spill).stack = [u 1,u 258,u 513] ∧
    (expected true high 7 spill).stack = [u 0,u 258,u 513] ∧
    (expected true high 7 spill).stack ≠ [u 1,u 258,u 513] := by
  exact ⟨populated valid false 7 7 spill (by decide),
    populated valid true high 7 spill (by decide),by decide,by decide,by decide⟩

theorem legal_boundaries (valid : Array UInt256) :
    Assembly.driverSteps 1 2 valid (input 6 true 0 0 []) = .ok (expected true 0 0 []) ∧
    Assembly.driverSteps 1 2 valid
      (input 6 false maximum maximum (List.replicate 1022 9)) =
      .ok (expected false maximum maximum (List.replicate 1022 9)) := by
  exact ⟨populated valid true 0 0 [] (by decide),
    populated valid false maximum maximum (List.replicate 1022 9) (by simp only [List.length_replicate];omega)⟩

theorem refusals (valid : Array UInt256) :
    EVM.X 2 valid (input 2 false 7 7 spill) = .error .OutOfGass ∧
    Assembly.driverSteps 1 1 valid (input 6 true 7 7 spill) = .error .OutOfFuel ∧
    EVM.X 2 valid ((modularSite (site 6 false) [7]).state) = .error .StackUnderflow := by
  exact ⟨rfl,rfl,rfl⟩

theorem ordered_observations :
    (expected true high 7 spill).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x14,0x00] ∧
    (expected true high 7 spill).stack ≠ [u 513,u 258,u 0] ∧
    (expected true 7 7 spill).memory = (seed 6 true).memory ∧
    (expected true 7 7 spill).returnData.data.toList = [0xcc,0xdd] ∧
    (expected true 7 7 spill).H_return.data.toList = [0xee,0xff] ∧
    (expected true 7 7 spill).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (expected true 7 7 spill).accountMap = accounts ∧
    (expected true 7 7 spill).σ₀ = accounts ∧
    (expected true 7 7 spill).substate = (seed 6 true).substate := by
  exact ⟨rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms populated
#print axioms typed_client
#print axioms equal_and_distinct
#print axioms legal_boundaries
#print axioms refusals
#print axioms ordered_observations
end SolidityBridge.RoadmapV15.P10.EqualityControls
