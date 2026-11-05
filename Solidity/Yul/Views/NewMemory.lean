import Solidity.Yul.Views.AllocationSequence

/-! Actual Source new-memory expressions over an intrinsic uint256 local.
Length evaluation, the existing 2^64 allocation panic, newData and allocation
are the owner's computations. Physical preparation is separate from execution;
canonical support and mathematical placement do not imply target refinement. -/
namespace Solidity.Yul.Views.NewMemory

def expr {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy} (newable : τ.newable=true) (index : Source.Idx Γ (.int Source.IntTy.u256)) :
    Source.RExpr E Γ τ := .newArray newable (.local index) rfl

theorem run {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (newable : τ.newable=true) (index : Source.Idx Γ (.int Source.IntTy.u256))
    (length : Nat) (fits : Source.IntTy.u256.lo≤(length : Int) ∧ (length : Int)≤Source.IntTy.u256.hi)
    (localValue : s.1.get index=Source.Val.int length fits) (small : length<2^64)
    (data : Source.Data E.layout τ) (computed : Source.newData τ length=.ok data)
    (memory : τ.loc?=some .memory) :
    (Source.evalE G F (n+2) (expr newable index)).run s=
      (.ok (.val (.memRef memory s.2.heap.next)),objectAllocatedState s data) := by
  first | (simp only;done) | decide | omega | rfl | skip
  have localRun : (Source.evalE G F (n+1) (Source.RExpr.local index)).run s=(.ok (.val (Source.Val.int length fits)),s) := by
    change (Except.ok (Source.RVal.val (s.1.get index)),s)=_
    rw [localValue]
  change (do
    let k ← Source.indexNat (← Source.evalE G F (n+1) (Source.RExpr.local index))
    if 2^64≤k then Source.EM.lift (Source.panic .alloc)
    else return Source.RVal.val (← Source.allocRef (← Source.EM.lift (Source.newData τ k)))).run s=_
  rw [Source.Hoare.run_bind,localRun]
  dsimp only
  change (if 2^64≤length then Source.EM.lift (Source.panic .alloc)
    else do return Source.RVal.val (← Source.allocRef (← Source.EM.lift (Source.newData τ length)))).run s=_
  rw [if_neg (by omega)]
  change (do return Source.RVal.val (← Source.allocRef (← Source.EM.lift (Source.newData τ length)))).run s=_
  simp only [Source.EM.lift,computed,Source.Hoare.run_bind]
  have pureRun : ((pure data : Source.EM E Γ (Source.Data E.layout τ)).run s)=(.ok data,s) := rfl
  rw [pureRun]
  dsimp only
  rw [objectAllocRef_run s data memory]
  rfl

theorem panic {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy} (G : Source.Glob E) (F : Source.Fr) (n : Nat)
    (s : Source.EMState E Γ) (newable : τ.newable=true) (index : Source.Idx Γ (.int Source.IntTy.u256))
    (length : Nat) (fits : Source.IntTy.u256.lo≤(length : Int) ∧ (length : Int)≤Source.IntTy.u256.hi)
    (localValue : s.1.get index=Source.Val.int length fits) (large : 2^64≤length) :
    (Source.evalE G F (n+2) (expr newable index)).run s=(.error (.revert (Source.panicData .alloc)),s) := by
  first | (simp only;done) | decide | omega | rfl | skip
  have localRun : (Source.evalE G F (n+1) (Source.RExpr.local index)).run s=(.ok (.val (Source.Val.int length fits)),s) := by
    change (Except.ok (Source.RVal.val (s.1.get index)),s)=_
    rw [localValue]
  change (do
    let k ← Source.indexNat (← Source.evalE G F (n+1) (Source.RExpr.local index))
    if 2^64≤k then Source.EM.lift (Source.panic .alloc)
    else return Source.RVal.val (← Source.allocRef (← Source.EM.lift (Source.newData τ k)))).run s=_
  rw [Source.Hoare.run_bind,localRun]
  dsimp only
  change (if 2^64≤length then Source.EM.lift (Source.panic .alloc)
    else do return Source.RVal.val (← Source.allocRef (← Source.EM.lift (Source.newData τ length)))).run s=_
  rw [if_pos large]
  rfl
theorem low {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (s : Source.EMState E Γ)
    (newable : τ.newable=true) (index : Source.Idx Γ (.int Source.IntTy.u256)) :
    (Source.evalE G F 0 (expr newable index)).run s=(.error .timeout,s) ∧
    (Source.evalE G F 1 (expr newable index)).run s=(.error .timeout,s) := ⟨rfl,rfl⟩

theorem physical {E : Source.Env} {Γ : Source.RCtx} {τ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (newable : τ.newable=true) (index : Source.Idx Γ (.int Source.IntTy.u256))
    (length : Nat) (fits : Source.IntTy.u256.lo≤(length : Int) ∧ (length : Int)≤Source.IntTy.u256.hi)
    (localValue : s.1.get index=Source.Val.int length fits) (small : length<2^64)
    (data : Source.Data E.layout τ) (computed : Source.newData τ length=.ok data)
    (shape : MemoryShape) (found : ComputedPlacement.objectShape data=some shape)
    (p : Placement s.2.heap) (done : ComputedPlacement.prepare s.2.heap=.ok p)
    (bound : p.free.val+max 1 shape.size<2^256) (H : Source.HeapTy)
    (ok : Source.MemOK E H s) (inner : Source.Data.Inner (E:=E) data)
    (valid : Source.DataOK E s.2.heap.ty data) (newSupported : InventoryTypeSupported E τ)
    (oldSupported : ∀ a σ d,s.2.heap.get a=some ⟨σ,d⟩ → InventoryTypeSupported E σ)
    (memory : ByteView) (reads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free) :
    let after := objectAllocatedState s data
    let q := ComputedAllocationWrite.placement s.2.heap p done data shape found bound
    ∃ raw, ComputedAllocationWrite.prepare s.2.heap p done data shape found bound memory=some raw ∧
      (Source.evalE G F (n+2) (expr newable index)).run s=
        (.ok (.val (.memRef (ComputedPlacement.objectShape_memory data shape found) s.2.heap.next)),after) ∧
      Source.MemOK E H after ∧ encodeMixedHeap q (generatedHeapEntries q) raw=raw ∧
      enumeratedMemoryWriteback after q q (retainInitial _ _) raw=.ok (some (.ok (),after)) ∧
      ReservedOK raw (ComputedAllocationWrite.nextFree p shape bound) := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  obtain ⟨raw,step⟩ := Option.isSome_iff_exists.mp
    (ComputedAllocationWrite.complete s.2.heap p done data shape found bound memory newSupported inner valid)
  have sound := ComputedAllocationWrite.sound H s p done data shape found bound memory raw step ok inner valid
    newSupported oldSupported reads
  exact ⟨raw,step,run G F n s newable index length fits localValue small data computed
    (ComputedPlacement.objectShape_memory data shape found),sound.2.1,sound.2.2.2.1,sound.2.2.2.2,
    ComputedAllocationWrite.reserved s.2.heap p done data shape found bound memory raw step reserved⟩
end Solidity.Yul.Views.NewMemory
