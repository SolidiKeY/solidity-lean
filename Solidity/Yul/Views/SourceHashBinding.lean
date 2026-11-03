import Solidity.Yul.Views.SourceHashBuiltin

namespace Solidity.Yul.Views

/-- Actual intrinsic builtin expression, using the owner's checked signature. -/
def sourceMemoryHashExpr {E Γ} (index : Source.Idx Γ (.bytes .memory)) : Source.RExpr E Γ Source.STy.bytes32 :=
  .builtin .keccak256 (.cons (.local index) .nil) (by rfl)

theorem sourceMemoryHashExpr_run {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (index : Source.Idx Γ (.bytes .memory)) (a : Nat) (bs : Roadmap.Bytes)
    (localValue : s.1.get index=Source.Val.memRef rfl a)
    (found : s.2.heap.get a=some ⟨.bytes .memory,Source.Data.bytes bs⟩) :
    (Source.evalE G F (n+4) (sourceMemoryHashExpr index)).run s=
      (.ok (.val (Source.mkBytes (n := 32) (h := by decide) (Source.wordBytes (G.fixed.hash bs)))),s) :=
  sourceKeccakMemory_run G F n s index a bs localValue found

/-- Actual source expression, constructed whole physical heap view and SAME
approved Fixed field. No final hash/input/view/output agreement is assumed. -/
theorem sourceMemoryHash_encoded {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (H : Source.HeapTy) (s : Source.EMState E Γ) (p : Placement s.2.heap) (residual : ByteView)
    (ok : Source.MemOK E H s)
    (supported : ∀ a τ d, s.2.heap.get a=some ⟨τ,d⟩ → InventoryTypeSupported E τ)
    (index : Source.Idx Γ (.bytes .memory)) (a : Nat) (bs : Roadmap.Bytes)
    (localValue : s.1.get index=Source.Val.memRef rfl a)
    (found : s.2.heap.get a=some ⟨.bytes .memory,Source.Data.bytes bs⟩) :
    let value := Source.mkBytes (D := E.layout) (n := 32) (h := by decide) (Source.wordBytes (G.fixed.hash bs))
    (Source.evalE G F (n+4) (sourceMemoryHashExpr index)).run s=(.ok (.val value),s) ∧
      value.word=some (keccak256 G.fixed.evm (encodeMixedHeap p (generatedHeapEntries p) residual) (p.address a+32) bs.length) := by
  dsimp only
  exact ⟨sourceMemoryHashExpr_run G F n s index a bs localValue found,
    (hashWord_observe E.layout (G.fixed.hash bs)).trans (congrArg some
      (encodedSourceBytes_hash H s p residual ok supported a bs found G.fixed).symm)⟩

end Solidity.Yul.Views
