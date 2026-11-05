import Solidity.Yul.Views.NewMemory

/-! Contextual transport for any actual typed new-memory length expression.
The same owner evaluation produces the reached state consumed by allocation or
size panic; no independent runs, substitute evaluator or callback are supplied.
This does not claim instrumentation of every discarded intermediate reference. -/
namespace Solidity.Yul.Views.NewMemoryOperand

theorem decompose {E : Source.Env} {Γ : Source.RCtx} {τ σ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s : Source.EMState E Γ)
    (newable : τ.newable=true) (length : Source.RExpr E Γ σ) (indexable : σ.isIndex=true) :
    (Source.evalE G F (n+1) (.newArray newable length indexable)).run s=
      match (Source.evalE G F n length).run s with
      | (.error error,reached) => (.error error,reached)
      | (.ok value,reached) => (do
          let k ← Source.indexNat value
          if 2^64≤k then Source.EM.lift (Source.panic .alloc)
          else return Source.RVal.val (← Source.allocRef (← Source.EM.lift (Source.newData τ k)))).run reached := by
  first | (simp only;done) | decide | omega | rfl | skip
  change (do
    let value ← Source.evalE G F n length
    let k ← Source.indexNat value
    if 2^64≤k then Source.EM.lift (Source.panic .alloc)
    else return Source.RVal.val (← Source.allocRef (← Source.EM.lift (Source.newData τ k)))).run s=_
  rw [Source.Hoare.run_bind]
  rcases actual : (Source.evalE G F n length).run s with ⟨result,reached⟩
  cases result <;> rfl

theorem halt {E : Source.Env} {Γ : Source.RCtx} {τ σ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s reached : Source.EMState E Γ)
    (newable : τ.newable=true) (length : Source.RExpr E Γ σ) (indexable : σ.isIndex=true)
    (error : Source.Halt) (actual : (Source.evalE G F n length).run s=(.error error,reached)) :
    (Source.evalE G F (n+1) (.newArray newable length indexable)).run s=(.error error,reached) := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [decompose G F n s newable length indexable,actual]

theorem run {E : Source.Env} {Γ : Source.RCtx} {τ σ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s reached : Source.EMState E Γ)
    (newable : τ.newable=true) (length : Source.RExpr E Γ σ) (indexable : σ.isIndex=true)
    (value : Source.RVal E.layout σ) (actual : (Source.evalE G F n length).run s=(.ok value,reached))
    (k : Nat) (amount : value.amount=.ok k) (small : k<2^64)
    (data : Source.Data E.layout τ) (computed : Source.newData τ k=.ok data)
    (memory : τ.loc?=some .memory) :
    (Source.evalE G F (n+1) (.newArray newable length indexable)).run s=
      (.ok (.val (.memRef memory reached.2.heap.next)),objectAllocatedState reached data) := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [decompose G F n s newable length indexable,actual]
  dsimp only
  have indexed : (Source.indexNat (E:=E) (Γ:=Γ) value).run reached=(.ok k,reached) := by
    unfold Source.indexNat Source.EM.lift
    rw [amount]
    rfl
  rw [Source.Hoare.run_bind,indexed]
  dsimp only
  rw [if_neg (by omega)]
  have lifted : (Source.EM.lift (E:=E) (Γ:=Γ) (Source.newData τ k)).run reached=(.ok data,reached) := by
    unfold Source.EM.lift
    rw [computed]
    rfl
  rw [Source.Hoare.run_bind,lifted]
  dsimp only
  rw [Source.Hoare.run_bind,objectAllocRef_run reached data memory]
  rfl

theorem panic {E : Source.Env} {Γ : Source.RCtx} {τ σ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s reached : Source.EMState E Γ)
    (newable : τ.newable=true) (length : Source.RExpr E Γ σ) (indexable : σ.isIndex=true)
    (value : Source.RVal E.layout σ) (actual : (Source.evalE G F n length).run s=(.ok value,reached))
    (k : Nat) (amount : value.amount=.ok k) (large : 2^64≤k) :
    (Source.evalE G F (n+1) (.newArray newable length indexable)).run s=
      (.error (.revert (Source.panicData .alloc)),reached) := by
  first | (simp only;done) | decide | omega | rfl | skip
  rw [decompose G F n s newable length indexable,actual]
  dsimp only
  have indexed : (Source.indexNat (E:=E) (Γ:=Γ) value).run reached=(.ok k,reached) := by
    unfold Source.indexNat Source.EM.lift
    rw [amount]
    rfl
  rw [Source.Hoare.run_bind,indexed]
  dsimp only
  rw [if_pos large]
  rfl
/-- Physical encoding starts from the actual reached operand state. Agreement
at the original state is deliberately insufficient for an effectful operand. -/
theorem physical {E : Source.Env} {Γ : Source.RCtx} {τ σ : Source.STy}
    (G : Source.Glob E) (F : Source.Fr) (n : Nat) (s reached : Source.EMState E Γ)
    (newable : τ.newable=true) (length : Source.RExpr E Γ σ) (indexable : σ.isIndex=true)
    (value : Source.RVal E.layout σ) (actual : (Source.evalE G F n length).run s=(.ok value,reached))
    (k : Nat) (amount : value.amount=.ok k) (small : k<2^64)
    (data : Source.Data E.layout τ) (computed : Source.newData τ k=.ok data)
    (shape : MemoryShape) (found : ComputedPlacement.objectShape data=some shape)
    (p : Placement reached.2.heap) (done : ComputedPlacement.prepare reached.2.heap=.ok p)
    (bound : p.free.val+max 1 shape.size<2^256) (H : Source.HeapTy)
    (ok : Source.MemOK E H reached) (inner : Source.Data.Inner (E:=E) data)
    (valid : Source.DataOK E reached.2.heap.ty data) (newSupported : InventoryTypeSupported E τ)
    (oldSupported : ∀ a υ d,reached.2.heap.get a=some ⟨υ,d⟩ → InventoryTypeSupported E υ)
    (memory : ByteView) (reads : ∀ e∈generatedHeapEntries p,e.image.Reads memory (p.address e.id))
    (reserved : ReservedOK memory p.free) :
    let after := objectAllocatedState reached data
    let q := ComputedAllocationWrite.placement reached.2.heap p done data shape found bound
    ∃ raw, ComputedAllocationWrite.prepare reached.2.heap p done data shape found bound memory=some raw ∧
      (Source.evalE G F (n+1) (.newArray newable length indexable)).run s=
        (.ok (.val (.memRef (ComputedPlacement.objectShape_memory data shape found) reached.2.heap.next)),after) ∧
      Source.MemOK E H after ∧ encodeMixedHeap q (generatedHeapEntries q) raw=raw ∧
      enumeratedMemoryWriteback after q q (retainInitial _ _) raw=.ok (some (.ok (),after)) ∧
      ReservedOK raw (ComputedAllocationWrite.nextFree p shape bound) := by
  first | (simp only;done) | decide | omega | rfl | skip
  dsimp only
  obtain ⟨raw,step⟩ := Option.isSome_iff_exists.mp
    (ComputedAllocationWrite.complete reached.2.heap p done data shape found bound memory newSupported inner valid)
  have sound := ComputedAllocationWrite.sound H reached p done data shape found bound memory raw step ok inner valid
    newSupported oldSupported reads
  exact ⟨raw,step,run G F n s reached newable length indexable value actual k amount small data computed
    (ComputedPlacement.objectShape_memory data shape found),sound.2.1,sound.2.2.2.1,sound.2.2.2.2,
    ComputedAllocationWrite.reserved reached.2.heap p done data shape found bound memory raw step reserved⟩
end Solidity.Yul.Views.NewMemoryOperand
