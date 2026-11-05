import SolidityBridge.RoadmapV15.P10.SignedGeConsumer
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Complete signed LT/GE native states and typed clients. Minimum and unsigned
contrast controls retain the actual signed interpretation, without source origin. -/
namespace SolidityBridge.RoadmapV15.P10.SignedGeControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External WordPushFixtures

private theorem fits : (Backend.encode (before ++ [.op .SLT])).length < UInt256.size := by decide
def ltSite (gas : Nat) (perm : Bool) : Site .SLT := ⟨seed gas perm,before,after,by decide⟩
def ltInput (gas : Nat) (perm : Bool) (a b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  (modularSite (ltSite gas perm) (a::b::tail)).state
def ltExpected (perm : Bool) (result _a _b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  {seed 6 perm with
    executionEnv := {(seed 6 perm).executionEnv with code := ⟨(Backend.encode (before ++ [.op .SLT] ++ after)).toArray⟩}
    pc := u 4,gasAvailable := u 3,execLength := 42
    stack := (result::tail).map (fun w => UInt256.mk w.toFin)}
def expected (perm : Bool) (result _a _b : Scalar.Word) (tail : Scalar.Stack) : EVM.State :=
  {seed 6 perm with
    executionEnv := {(seed 6 perm).executionEnv with code := ⟨(Backend.encode (before ++ [.op .SLT,.op .ISZERO] ++ after)).toArray⟩}
    pc := u 5,gasAvailable := u 0,execLength := 43
    stack := (result::tail).map (fun w => UInt256.mk w.toFin)}

private theorem lt_same (perm : Bool) (result a b : Scalar.Word) (tail : Scalar.Stack) :
    (Assembly.chargedPrepare (ltInput 6 perm a b tail) 3).replaceStackAndIncrPC
      ((result::tail).map (fun w => UInt256.mk w.toFin)) = ltExpected perm result a b tail := by
  simp only [ltExpected,ltInput,ltSite,modularSite,Site.state,Assembly.chargedPrepare,
    EVM.State.replaceStackAndIncrPC,EVM.State.incrPC,WordPushFixtures.seed,WordPushFixtures.before,
    WordPushFixtures.u,Backend.encode_cons,Backend.encode_nil,Instr.encode,List.length_append,
    List.length_cons,List.length_nil]
  rfl
private theorem ge_same (perm : Bool) (a b : Scalar.Word) (tail : Scalar.Stack) :
    signedGeOutput (seed 6 perm) before after a b tail =
      expected perm (Scalar.flag (!(decide (a.toInt < b.toInt)))) a b tail := by
  have gasEq : (signedGeOutput (seed 6 perm) before after a b tail).gasAvailable = u 0 := by
    apply congrArg UInt256.mk
    apply Fin.ext
    exact signed_ge_debit (seed 6 perm) before after a b tail (by change 6 ≤ 6;decide)
  change ({signedGeInput (seed 6 perm) before after a b tail with
    pc := u 5,gasAvailable := (signedGeOutput (seed 6 perm) before after a b tail).gasAvailable,
    execLength := 43,stack := (Scalar.flag (!(decide (a.toInt < b.toInt)))::tail).map
      (fun w => UInt256.mk w.toFin)} : EVM.State) = _
  rw [gasEq]
  rfl

theorem lt_populated (valid : Array UInt256) (perm : Bool) (a b : Scalar.Word)
    (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024) :
    Assembly.driverSteps 1 2 valid (ltInput 6 perm a b tail) =
      .ok (ltExpected perm (Scalar.flag (decide (a.toInt < b.toInt))) a b tail) := by
  have h := (signed_lt_agreement valid (ltSite 6 perm) a b tail room (by change 3 ≤ 6;decide) 0).2.1
  exact h.trans (congrArg Except.ok (lt_same perm _ a b tail))

theorem ge_populated (valid : Array UInt256) (perm : Bool) (a b : Scalar.Word)
    (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024) :
    Assembly.driverSteps 2 3 valid (signedGeInput (seed 6 perm) before after a b tail) =
      .ok (expected perm (Scalar.flag (!(decide (a.toInt < b.toInt)))) a b tail) := by
  have h := (signed_ge_execution valid (seed 6 perm) before after a b tail fits room
    (by change 6 ≤ 6;decide) 0).2.1
  exact h.trans (congrArg Except.ok (ge_same perm a b tail))

def negative : PrimTy.int.Denote := ⟨-7,by decide⟩
def positive : PrimTy.int.Denote := ⟨7,by decide⟩
def minimum : Scalar.Word := Scalar.encodeValue .int Scalar.minimumInt
def maximum : Scalar.Word := BitVec.ofNat 256 ((2^255 : Nat)-1)

theorem typed_clients (valid : Array UInt256) :
    Scalar.run Scalar.intLt.code (Scalar.encodeValue .int negative::Scalar.encodeValue .int positive::spill) =
      some (Scalar.encodeValue .bool true::spill) ∧
    Scalar.run Scalar.intGe.code (Scalar.encodeValue .int negative::Scalar.encodeValue .int positive::spill) =
      some (Scalar.encodeValue .bool false::spill) ∧
    Assembly.driverSteps 1 2 valid (ltInput 6 true
      (Scalar.encodeValue .int negative) (Scalar.encodeValue .int positive) spill) =
      .ok (ltExpected true 1 (Scalar.encodeValue .int negative) (Scalar.encodeValue .int positive) spill) ∧
    Assembly.driverSteps 2 3 valid (signedGeInput (seed 6 false) before after
      (Scalar.encodeValue .int negative) (Scalar.encodeValue .int positive) spill) =
      .ok (expected false 0 (Scalar.encodeValue .int negative) (Scalar.encodeValue .int positive) spill) := by
  have lt := selected_signed_lt_agreement valid (ltSite 6 true) negative positive spill (by decide) (by decide) 0
  have ge := selected_signed_ge_execution valid (seed 6 false) before after negative positive spill fits
    (by decide) (by decide) 0
  have leval : BinOp.lt.evalT (p := .int) rfl negative positive = some true := by rfl
  have geval : BinOp.ge.evalT (p := .int) rfl negative positive = some false := by rfl
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [leval,Option.map_some] using lt.1
  · simpa only [geval,Option.map_some] using ge.1
  · exact lt.2.1.trans (congrArg Except.ok (lt_same true 1 _ _ spill))
  · exact ge.2.1.trans (congrArg Except.ok (ge_same false _ _ spill))

theorem directions_and_equality (valid : Array UInt256) :
    Assembly.driverSteps 2 3 valid (signedGeInput (seed 6 true) before after
      (Scalar.encodeValue .int positive) (Scalar.encodeValue .int negative) spill) =
      .ok (expected true 1 (Scalar.encodeValue .int positive) (Scalar.encodeValue .int negative) spill) ∧
    Assembly.driverSteps 2 3 valid (signedGeInput (seed 6 false) before after minimum minimum spill) =
      .ok (expected false 1 minimum minimum spill) ∧
    UInt256.lt (UInt256.mk (Scalar.encodeValue .int negative).toFin)
      (UInt256.mk (Scalar.encodeValue .int positive).toFin) = u 0 ∧
    (expected false 0 (Scalar.encodeValue .int negative) (Scalar.encodeValue .int positive) spill).stack ≠
      [u 1,u 258,u 513] := by
  exact ⟨ge_populated valid true (Scalar.encodeValue .int positive) (Scalar.encodeValue .int negative) spill (by decide),
    ge_populated valid false minimum minimum spill (by decide),by decide,by decide⟩

theorem boundaries (valid : Array UInt256) :
    Assembly.driverSteps 2 3 valid (signedGeInput (seed 6 true) before after minimum 0 []) =
      .ok (expected true 0 minimum 0 []) ∧
    Assembly.driverSteps 2 3 valid
      (signedGeInput (seed 6 false) before after maximum minimum (List.replicate 1022 9)) =
      .ok (expected false 1 maximum minimum (List.replicate 1022 9)) := by
  exact ⟨ge_populated valid true minimum 0 [] (by decide),
    ge_populated valid false maximum minimum (List.replicate 1022 9)
      (by simp only [List.length_replicate];omega)⟩

theorem resource_refusals (valid : Array UInt256) :
    Assembly.driverSteps 2 3 valid (signedGeInput (seed 5 false) before after 7 7 spill) =
      .error .OutOfGass ∧
    Assembly.driverSteps 2 2 valid (signedGeInput (seed 6 true) before after 7 7 spill) =
      .error .OutOfFuel ∧
    EVM.X 2 valid ((modularSite (ltSite 6 false) [7]).state) = .error .StackUnderflow := by
  exact ⟨rfl,rfl,rfl⟩

theorem ordered_observation :
    (ltExpected true 1 7 513 spill).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x12,0x00] ∧
    (expected false 1 maximum minimum spill).executionEnv.code.data.toList = [0x60,0x7f,0x50,0x12,0x15,0x00] ∧
    (expected true 1 7 7 spill).stack = [u 1,u 258,u 513] ∧
    (expected true 1 7 7 spill).stack ≠ [u 513,u 258,u 1] ∧
    (expected true 1 7 7 spill).returnData.data.toList = [0xcc,0xdd] ∧
    (expected false 1 maximum minimum spill).H_return.data.toList = [0xee,0xff] ∧
    (expected false 1 maximum minimum spill).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (expected true 1 7 7 spill).memory = (seed 6 true).memory ∧
    (expected false 1 maximum minimum spill).accountMap = accounts ∧
    (expected false 1 maximum minimum spill).σ₀ = accounts ∧
    (expected false 1 maximum minimum spill).substate = (seed 6 false).substate := by
  exact ⟨rfl,rfl,rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms lt_populated
#print axioms ge_populated
#print axioms typed_clients
#print axioms directions_and_equality
#print axioms boundaries
#print axioms resource_refusals
#print axioms ordered_observation
end SolidityBridge.RoadmapV15.P10.SignedGeControls
