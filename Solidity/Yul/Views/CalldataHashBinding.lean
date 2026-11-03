import Solidity.Yul.Views.SourceHashBinding
import Solidity.Yul.Views.AbiCalldataAgreement

/-! Actual keccak on a calldata local includes the existing implicit memory
allocation. Physical copying uses the effective clipped source slice length;
CALDATACOPY's zero padding is not silently substituted for source clipping.
The same approved Fixed field supplies source and physical hashes. -/
namespace Solidity.Yul.Views

def sourceCalldataHashExpr {E Γ} (index : Source.Idx Γ (.bytes .calldata)) : Source.RExpr E Γ Source.STy.bytes32 :=
  .builtin .keccak256 (.cons (.local index) .nil) (by rfl)

theorem sourceCalldataConv_run {E Γ} (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ) (off len : Nat) :
    (Source.convRV F n (.bytes .memory) (.val (Source.Val.cdRef (τ:=.bytes .calldata) rfl off len))).run s=
      (.ok (.val (.memRef rfl s.2.heap.next)),objectAllocatedState s (Source.Data.bytes (l:=.memory) ((F.cd.drop off).take len))) := by
  change ((do let v ← Source.allocRef (Source.Data.bytes (l:=.memory) ((F.cd.drop off).take len));pure (Source.RVal.val v)) :
    Source.EM E Γ (Source.RVal E.layout (.bytes .memory))).run s=_
  rw [Source.Hoare.run_bind,objectAllocRef_run s _ rfl]
  rfl

theorem sourceCalldataHash_run {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (index : Source.Idx Γ (.bytes .calldata)) (off len : Nat)
    (localValue : s.1.get index=Source.Val.cdRef rfl off len) :
    let bs:=(F.cd.drop off).take len
    let after:=objectAllocatedState s (Source.Data.bytes (l:=.memory) bs)
    let value:=Source.mkBytes (D:=E.layout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash bs))
    (Source.evalE G F (n+4) (sourceCalldataHashExpr index)).run s=(.ok (.val value),after) := by
  have localRun : (Source.evalE G F (n+1) (Source.RExpr.local index)).run s=
      (.ok (.val (Source.Val.cdRef rfl off len)),s) := by
    change (Except.ok (Source.RVal.val (s.1.get index)),s)=_
    rw [localValue]
  have argsRun : (Source.evalArgs G F (n+2) (.cons (.local index) .nil)).run s=
      (.ok (.cons (.val (Source.Val.cdRef rfl off len)) .nil),s) := by
    rw [Source.evalArgs,Source.Hoare.run_bind,localRun]
    rfl
  change (Source.evalBuiltin G F (n+3) .keccak256 (.cons (.local index) .nil) Source.STy.bytes32).run s=_
  rw [Source.evalBuiltin]
  simp only [reduceCtorEq,decide_false,Bool.false_or,Bool.false_and,Bool.false_eq_true,if_false]
  rw [Source.Hoare.run_bind,argsRun]
  change (do
    let bs ← (do
      let v ← Source.convRV F (n+2) (.bytes .memory) (.val (Source.Val.cdRef (τ:=.bytes .calldata) rfl off len))
      Source.bytesOfRV F (n+2) v)
    Source.ret32 Source.STy.bytes32 (Source.wordBytes (G.fixed.hash bs))).run s=_
  rw [Source.Hoare.run_bind,Source.Hoare.run_bind,sourceCalldataConv_run F (n+2) s off len]
  simp only []
  rw [sourceBytesOfMemory_run F (n+2) (objectAllocatedState s (Source.Data.bytes (l:=.memory) ((F.cd.drop off).take len)))
    s.2.heap.next ((F.cd.drop off).take len) (Source.Heap.alloc_get s.2.heap _)]
  rfl

/-- The clipped payload is copied exactly, including empty and past-end slices.
No well-formed calldata-reference premise or artificial copy cap is imposed. -/
theorem calldataCopy_clipped (F : Source.Fr) (off len dst : Nat) (m : ByteView) :
    let bs:=(F.cd.drop off).take len
    readBytes (calldatacopy m F.cd dst off bs.length) dst bs.length=bs := by
  dsimp only
  apply List.ext_getElem
  · simp only [readBytes,List.length_map,List.length_range]
  · intro i hi hj
    simp only [readBytes,List.getElem_map,List.getElem_range]
    change copyBytes m (calldataBytes F.cd) dst off _ (dst+i)=_
    rw [find_copyBytes _ _ dst off _ i hj]
    have inside : off+i<F.cd.length := by
      simp only [List.length_take,List.length_drop] at hj
      omega
    simp only [calldataBytes,List.getElem?_eq_getElem inside,Option.getD_some,List.getElem_take,List.getElem_drop,Nat.add_comm]

/-- Actual Source allocation/hash result, exact physical input and observed word.
The actual source state changes by allocation; it is not silently erased. -/
theorem sourceCalldataHash_physical {E Γ} (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (index : Source.Idx Γ (.bytes .calldata)) (off len dst : Nat) (m : ByteView)
    (localValue : s.1.get index=Source.Val.cdRef rfl off len) :
    let bs:=(F.cd.drop off).take len
    let after:=objectAllocatedState s (Source.Data.bytes (l:=.memory) bs)
    let memory:=calldatacopy m F.cd dst off bs.length
    let value:=Source.mkBytes (D:=E.layout) (n:=32) (h:=by decide) (Source.wordBytes (G.fixed.hash bs))
    (Source.evalE G F (n+4) (sourceCalldataHashExpr index)).run s=(.ok (.val value),after) ∧
      value.word=some (keccak256 G.fixed.evm memory dst bs.length) ∧
      (∀ H : Source.HeapTy,Source.MemOK E H s → Source.MemOK E H after) := by
  dsimp only
  refine ⟨sourceCalldataHash_run G F n s index off len localValue,?_,?_⟩
  · exact (hashWord_observe E.layout (G.fixed.hash ((F.cd.drop off).take len))).trans
      (congrArg some (fixedHash_physical G.fixed _ dst _ _ (calldataCopy_clipped F off len dst m)).symm)
  · intro H ok
    exact (objectAllocRef_MemOK H s (Source.Data.bytes (l:=.memory) ((F.cd.drop off).take len)) rfl trivial trivial (.bytes _) ok).1
end Solidity.Yul.Views
