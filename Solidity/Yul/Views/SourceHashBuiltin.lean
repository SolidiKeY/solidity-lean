import Solidity.Yul.Views.SourceHashWord
import Solidity.Yul.Views.InventorySourceReads

namespace Solidity.Yul.Views

/-- Actual memory byte lookup, with source errors/state left to the owner.
This successful case needs the actual typed heap lookup, not a byte oracle. -/
theorem sourceBytesOfMemory_run {E Γ} (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (a : Nat) (bs : Roadmap.Bytes) (found : s.2.heap.get a=some ⟨.bytes .memory,Source.Data.bytes bs⟩) :
    (Source.bytesOfRV F n (Source.RVal.val (Source.Val.memRef (τ := .bytes .memory) rfl a))).run s=(.ok bs,s) := by
  change (Source.heapBytes a).run s= _
  exact heapBytes_known s a bs (Or.inr found)

/-- Existing owner dangling-reference outcome, not a preparation None or
invented Yul refusal. It is an API boundary, not a reachable-MemOK claim. -/
theorem sourceBytesOfMemory_missing {E Γ} (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (a : Nat) (missing : s.2.heap.get a=none) :
    (Source.bytesOfRV F n (Source.RVal.val (Source.Val.memRef (τ := .bytes .memory) rfl a))).run s=
      (.error (.stuck "dangling memory reference"),s) := by
  have absent : (Source.heapObj a).run s=(.error (.stuck "dangling memory reference"),s) := by
    have state : (Source.EM.st : Source.EM E Γ (Source.St E)).run s=(.ok s.2,s) := by cases s; rfl
    unfold Source.heapObj
    rw [Source.Hoare.run_bind,state]
    simp only []
    rw [missing]
    rfl
  change (Source.heapBytes a).run s= _
  rw [Source.heapBytes,Source.Hoare.run_bind,absent]

/-- The real builtin evaluator over ONE actual typed bytes.memory LOCAL.
No implicit string admission, storage copy, literal allocation or new AST. -/
theorem sourceKeccakMemory_run {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (index : Source.Idx Γ (.bytes .memory)) (a : Nat) (bs : Roadmap.Bytes)
    (localValue : s.1.get index=Source.Val.memRef rfl a)
    (found : s.2.heap.get a=some ⟨.bytes .memory,Source.Data.bytes bs⟩) :
    (Source.evalBuiltin G F (n+3) .keccak256 (.cons (.local index) .nil) Source.STy.bytes32).run s=
      (.ok (.val (Source.mkBytes (n := 32) (h := by decide) (Source.wordBytes (G.fixed.hash bs)))),s) := by
  have localRun : (Source.evalE G F (n+1) (Source.RExpr.local index)).run s=
      (.ok (.val (Source.Val.memRef rfl a)),s) := by
    change ((Except.ok (Source.RVal.val (s.1.get index)) : Except Source.Halt (Source.RVal E.layout (.bytes .memory))),s)= _
    rw [localValue]
  have argsRun : (Source.evalArgs G F (n+2) (Source.RArgs.cons (.local index) .nil)).run s=
      (.ok (.cons (.val (Source.Val.memRef rfl a)) .nil),s) := by
    rw [Source.evalArgs,Source.Hoare.run_bind,localRun]
    rfl
  rw [Source.evalBuiltin]
  simp only [reduceCtorEq,decide_false,Bool.false_or,Bool.false_and,Bool.false_eq_true,if_false]
  rw [Source.Hoare.run_bind,argsRun]
  change (do
    let bytes ← Source.bytesOfRV F (n+2) (.val (Source.Val.memRef (τ := .bytes .memory) rfl a))
    Source.ret32 Source.STy.bytes32 (Source.wordBytes (G.fixed.hash bytes))).run s= _
  rw [Source.Hoare.run_bind,sourceBytesOfMemory_run F (n+2) s a bs found]
  rfl

end Solidity.Yul.Views
