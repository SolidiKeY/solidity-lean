import SolidityBridge.RoadmapV15.P10.LinkedZero
import SolidityBridge.RoadmapV15.P10.WordPushFixtures

/-! Populated word, sign and legal-capacity clients. Counted-prefix success is
separated from following-PUSH failure; missing operands keep native gate order. -/
namespace SolidityBridge.RoadmapV15.P10.LinkedZeroControls
open Solidity Solidity.Backend EvmYul Solidity.Evm.External
open WordPushFixtures (seed u accounts spill)

def observed (perm : Bool) (a : Scalar.Word) : EVM.State :=
  {linkedZeroInput (seed 10 perm) a spill with
    pc := u 3,gasAvailable := u 5,execLength := 44,
    stack := (Scalar.flag (a == 0)::spill).map (fun w => UInt256.mk w.toFin)}

theorem arbitrary_word_client (perm : Bool) (a : Scalar.Word) :
    Assembly.driverSteps 3 4 #[u 73] (linkedZeroInput (seed 10 perm) a spill) =
      .ok (observed perm a) ∧
    EVM.X 4 #[u 73] (linkedZeroInput (seed 10 perm) a spill) =
      EVM.X 1 #[u 73] (observed perm a) := by
  have h := (linked_zero_prefix #[u 73] (seed 10 perm) a spill (by decide)
    (by change 5 ≤ 10;decide) 0).2
  have gasEq : (linkedZeroOutput (seed 10 perm) a spill).gasAvailable = u 5 := by
    apply congrArg UInt256.mk
    apply Fin.ext
    exact linked_zero_debit (seed 10 perm) a spill (by change 5 ≤ 10;decide)
  have same : linkedZeroOutput (seed 10 perm) a spill = observed perm a := by
    change ({linkedZeroInput (seed 10 perm) a spill with
      pc := u 3,gasAvailable := (linkedZeroOutput (seed 10 perm) a spill).gasAvailable,
      execLength := 44,stack := (Scalar.flag (a == 0)::spill).map (fun w => UInt256.mk w.toFin)} : EVM.State) = _
    rw [gasEq]
    rfl
  rw [←same]
  exact h

theorem zero_and_signed_clients :
    Assembly.driverSteps 3 4 #[u 73] (linkedZeroInput (seed 10 false) 0 spill) =
      .ok (observed false 0) ∧
    (observed false 0).stack = [u 1,u 258,u 513] ∧
    Assembly.driverSteps 3 4 #[] (linkedZeroInput (seed 10 true) (BitVec.ofInt 256 (-1)) spill) =
      .ok (linkedZeroOutput (seed 10 true) (BitVec.ofInt 256 (-1)) spill) ∧
    (observed true (BitVec.ofInt 256 (-1))).stack = [u 0,u 258,u 513] := by
  exact ⟨(arbitrary_word_client false 0).1,rfl,
    (linked_zero_prefix #[] (seed 10 true) _ spill (by decide) (by decide) 0).2.1,rfl⟩

theorem legal_capacity :
    Assembly.driverSteps 3 4 #[] (linkedZeroInput (seed 5 false) 0 []) =
      .ok (linkedZeroOutput (seed 5 false) 0 []) ∧
    Assembly.driverSteps 3 4 #[] (linkedZeroInput (seed 5 true) 258 (List.replicate 1023 513)) =
      .ok (linkedZeroOutput (seed 5 true) 258 (List.replicate 1023 513)) := by
  exact ⟨(linked_zero_prefix _ _ _ _ (by decide) (by decide) 0).2.1,
    (linked_zero_prefix _ _ _ _ (by simp only [List.length_replicate];decide) (by decide) 0).2.1⟩

theorem failure_order :
    EVM.X 5 #[] (linkedZeroInput (seed 5 false) 0 spill) = .error .OutOfGass ∧
    Assembly.driverSteps 3 3 #[] (linkedZeroInput (seed 5 false) 0 spill) = .error .OutOfFuel ∧
    EVM.X 5 #[] (linkedEntryInput (seed 4 false) []) = .error .OutOfGass ∧
    EVM.X 5 #[] (linkedEntryInput (seed 5 false) []) = .error .StackUnderflow := by
  constructor
  · have h := (linked_zero_prefix #[] (seed 5 false) 0 spill (by decide) (by decide) 1).2.2
    refine h.trans ?_
    conv_lhs => rw [Assembly.X_unfold]
    rfl
  · refine ⟨rfl,?_,?_⟩
    · have h := (linked_entry_prefix #[] (seed 4 false) [] (by decide) (by decide) 2).2
      refine h.trans ?_
      conv_lhs => rw [Assembly.X_unfold]
      rfl
    · have h := (linked_entry_prefix #[] (seed 5 false) [] (by decide) (by decide) 2).2
      refine h.trans ?_
      conv_lhs => rw [Assembly.X_unfold]
      rfl

theorem ordered_observations :
    (observed false 0).stack = [u 1,u 258,u 513] ∧
    (observed false 0).stack ≠ [u 1,u 513,u 258] ∧
    (observed false 0).pc = u 3 ∧
    (observed false 0).pc ≠ u 36 ∧
    (observed false 0).gasAvailable = u 5 ∧
    (observed false 0).execLength = 44 ∧
    (observed false 0).executionEnv.code.data.toList =
      [0x5b,0x5b,0x15,0x7f] ++ List.replicate 31 0 ++ [0x48,0x57,0x5b,0x7f] ++
        List.replicate 32 0 ++ [0x56,0x5b,0x00] ∧
    (observed false 0).memory.data.toList = [0xaa,0xbb] ++ List.replicate 30 0 ∧
    (observed false 0).activeWords = u 1 ∧
    (observed false 0).returnData.data.toList = [0xcc,0xdd] ∧
    (observed false 0).H_return.data.toList = [0xee,0xff] ∧
    (observed false 0).executionEnv.calldata.data.toList = [0x11,0x22,0x33] ∧
    (observed false 0).accountMap = accounts ∧
    (observed false 0).σ₀ = accounts ∧
    (observed false 0).substate = (seed 10 false).substate := by
  exact ⟨rfl,by decide,rfl,by decide,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms arbitrary_word_client
#print axioms zero_and_signed_clients
#print axioms legal_capacity
#print axioms failure_order
#print axioms ordered_observations
end SolidityBridge.RoadmapV15.P10.LinkedZeroControls
