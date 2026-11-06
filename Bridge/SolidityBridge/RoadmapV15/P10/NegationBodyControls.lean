import SolidityBridge.RoadmapV15.P10.NegationBody
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Two-step body controls, not native checked-negation guard/panic execution.
The signed minimum explicitly demonstrates why the guard cannot be omitted. -/
namespace SolidityBridge.RoadmapV15.P10.NegationBodyControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed u before after spill accounts)

def positive : PrimTy.int.Denote := ⟨7,by decide⟩
def negative : PrimTy.int.Denote := ⟨-7,by decide⟩
def zero : PrimTy.int.Denote := ⟨0,by decide⟩
def maximum : PrimTy.int.Denote := ⟨(2^255 : Nat)-1,by decide⟩
def fits : (Backend.encode (before ++ [Scalar.pushWord 0])).length < UInt256.size := by
  simp only [Backend.encode_append,Backend.encode_cons,Backend.encode_nil,
    Scalar.encode_pushWord,List.length_append,List.length_cons,List.length_nil,Vector.length_toList]
  decide

def observed (perm : Bool) (a : PrimTy.int.Denote) (tail : Scalar.Stack) : EVM.State :=
  {negationBodyInput (seed 6 perm) before after a tail with
    pc := u 37,gasAvailable := u 0,execLength := 43
    stack := (BitVec.ofInt 256 (-a.val)::tail).map (fun w => UInt256.mk w.toFin)}

theorem exact_budget (valid : Array UInt256) (perm : Bool) (a : PrimTy.int.Denote)
    (tail : Scalar.Stack) (room : tail.length+2 ≤ 1024) :
    Assembly.driverSteps 2 3 valid (negationBodyInput (seed 6 perm) before after a tail) =
      .ok (observed perm a tail) := by
  have h := (negation_body_execution valid (seed 6 perm) before after a tail fits room
    (by change 6 ≤ 6;decide) 0).2.1
  have gasEq : (negationBodyOutput (seed 6 perm) before after a tail).gasAvailable = u 0 := by
    apply congrArg UInt256.mk
    apply Fin.ext
    exact negation_body_debit (seed 6 perm) before after a tail (by change 6 ≤ 6;decide)
  have same : negationBodyOutput (seed 6 perm) before after a tail = observed perm a tail := by
    change ({negationBodyInput (seed 6 perm) before after a tail with
      pc := u 37,gasAvailable := (negationBodyOutput (seed 6 perm) before after a tail).gasAvailable,
      execLength := 43,stack := (BitVec.ofInt 256 (-a.val)::tail).map (fun w => UInt256.mk w.toFin)} : EVM.State) = _
    rw [gasEq]
    rfl
  rw [same] at h
  exact h

theorem signed_and_zero :
    Assembly.driverSteps 2 3 #[] (negationBodyInput (seed 6 false) before after positive spill) =
      .ok (observed false positive spill) ∧
    Assembly.driverSteps 2 3 #[u 99] (negationBodyInput (seed 6 true) before after negative spill) =
      .ok (observed true negative spill) ∧
    Assembly.driverSteps 2 3 #[] (negationBodyInput (seed 6 false) before after zero spill) =
      .ok (observed false zero spill) := by
  exact ⟨exact_budget _ _ _ _ (by decide),exact_budget _ _ _ _ (by decide),exact_budget _ _ _ _ (by decide)⟩

theorem edge_inputs :
    Assembly.driverSteps 2 3 #[] (negationBodyInput (seed 6 false) before after Scalar.minimumInt spill) =
      .ok (observed false Scalar.minimumInt spill) ∧
    Assembly.driverSteps 2 3 #[] (negationBodyInput (seed 6 true) before after maximum spill) =
      .ok (observed true maximum spill) := by
  exact ⟨exact_budget _ _ _ _ (by decide),exact_budget _ _ _ _ (by decide)⟩

theorem legal_capacity :
    Assembly.driverSteps 2 3 #[] (negationBodyInput (seed 6 false) before after negative []) =
      .ok (observed false negative []) ∧
    Assembly.driverSteps 2 3 #[u 99] (negationBodyInput (seed 6 true) before after positive (List.replicate 1022 513)) =
      .ok (observed true positive (List.replicate 1022 513)) := by
  exact ⟨exact_budget _ _ _ _ (by decide),exact_budget _ _ _ _ (by simp only [List.length_replicate];decide)⟩

/-- This body wraps; the original source/Scalar guard still selects overflow. -/
theorem minimum_wrap_requires_guard :
    Assembly.driverSteps 2 3 #[u 99] (negationBodyInput (seed 6 false) before after Scalar.minimumInt spill) =
      .ok (observed false Scalar.minimumInt spill) ∧
    (observed false Scalar.minimumInt spill).stack =
      (Scalar.encodeValue .int Scalar.minimumInt::spill).map (fun w => UInt256.mk w.toFin) ∧
    Scalar.guarded Scalar.negationTest Scalar.negationBody Scalar.overflowFailure
      (Scalar.encodeValue .int Scalar.minimumInt::spill) = some (.error Scalar.overflowFailure) ∧
    UnOp.evalT .neg (p := .int) rfl Scalar.minimumInt = none := by
  exact ⟨exact_budget _ _ _ _ (by decide),by first | rfl | decide | simp only,rfl,rfl⟩

theorem resource_refusals :
    EVM.X 3 #[u 99] (negationBodyInput (seed 5 false) before after negative spill) = .error .OutOfGass ∧
    Assembly.driverSteps 2 2 #[u 99] (negationBodyInput (seed 6 false) before after negative spill) = .error .OutOfFuel := by
  constructor
  · have h := (word_push_table_agreement #[u 99] (seed 5 false) before (.op .SUB::after) 0
      (Scalar.encodeValue .int negative::spill) (by decide) (by decide) (by decide) 1).2.2
    refine h.trans ?_
    conv_lhs => rw [Assembly.X_unfold]
    rfl
  · have h : Assembly.driverSteps 1 2 #[u 99]
        (negationBodyInput (seed 6 false) before after negative spill) =
        .ok (negationBodyPushed (seed 6 false) before after negative spill) :=
      (word_push_table_agreement #[u 99] (seed 6 false) before (.op .SUB::after) 0
        (Scalar.encodeValue .int negative::spill) (by decide) (by decide) (by decide) 0).2.1
    rw [fetched_steps_append 1 1 0,h]
    rfl

theorem opposite_sign_words :
    (observed false positive spill).stack = [u (2^256-7),u 258,u 513] ∧
    (observed true negative spill).stack = [u 7,u 258,u 513] ∧
    (observed false positive spill).stack ≠ [u 7,u 258,u 513] ∧
    (observed false zero spill).stack = [u 0,u 258,u 513] := by
  first | decide | simp only | rfl

theorem complete_ordered_observation :
    (observed true negative spill).executionEnv.code.data.toList =
      [0x60,0x7f,0x50,0x7f] ++ List.replicate 32 0 ++ [0x03,0x00] ∧
    (observed true negative spill).stack = [u 7,u 258,u 513] ∧
    (observed true negative spill).stack ≠ [u 513,u 258,u 7] ∧
    (observed true negative spill).pc = u 37 ∧
    (observed true negative spill).gasAvailable = u 0 ∧
    (observed true negative spill).execLength = 43 ∧
    (observed true negative spill).memory.data.toList = [0xaa,0xbb]++List.replicate 30 0 ∧
    (observed true negative spill).activeWords = u 1 ∧
    (observed true negative spill).returnData.data.toList = [0xcc,0xdd] ∧
    (observed true negative spill).H_return.data.toList = [0xee,0xff] ∧
    (observed true negative spill).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (observed true negative spill).accountMap = accounts ∧
    (observed true negative spill).σ₀ = accounts ∧
    (observed true negative spill).substate = (seed 6 true).substate := by
  exact ⟨rfl,rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms exact_budget
#print axioms signed_and_zero
#print axioms edge_inputs
#print axioms legal_capacity
#print axioms minimum_wrap_requires_guard
#print axioms resource_refusals
#print axioms opposite_sign_words
#print axioms complete_ordered_observation
end SolidityBridge.RoadmapV15.P10.NegationBodyControls
