import Solidity.Yul.Views.NominalInventoryView
import Solidity.Yul.Views.NominalRetained

/-! Exact compatibility with the existing retained nominal-array operation.
Guard reordering preserves complete preparation and Source success/error results;
no new array planner, capacity policy or state representation is introduced. -/
namespace Solidity.Yul.Views.NominalInventory

theorem singleton_run {E : Source.Env} {Γ : Source.RCtx} {origin h : Source.Heap E.layout}
    {allocated : Placement origin} {p : Placement h} (u : OwnedInventoryUpdate allocated p)
    (s : Source.EMState E Γ) :
    (runInventoryUpdates [u]).run s=(Source.heapPut u.entry.id ⟨u.entry.ty,u.object.data⟩).run s := by
  first
  | solve | rfl
  | rw [runInventoryUpdates,Source.Hoare.run_bind]
    cases step : (Source.heapPut u.entry.id ⟨u.entry.ty,u.object.data⟩ : Source.EM E Γ Unit).run s with
    | mk result out =>
      cases result with
      | error error => rfl
      | ok value => cases value; rfl

theorem singleton_writeback {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (e : MixedHeapEntry p) (m : ByteView) :
    writeback s allocated p history [e] m=(update allocated p [e] e m).map
      (fun u => (Source.heapPut u.entry.id ⟨u.entry.ty,u.object.data⟩).run s) := by
  unfold writeback updates
  cases prepared : update allocated p [e] e m with
  | none => rfl
  | some u =>
    change some ((runInventoryUpdates [u]).run s)=some _
    rw [singleton_run]

theorem dynamic_compat {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (s : Source.EMState E Γ) (allocated : Placement origin) (p : Placement s.2.heap)
    (history : RetainedAllocation allocated p) (e : MixedHeapEntry p) (name : Source.DeclName)
    (type : e.ty=.array .memory (.udvt name) none) (m : ByteView) :
    writeback s allocated p history [e] m=NominalMemory.retainedState s allocated p history e.id name m := by
  rw [singleton_writeback]
  rcases e with ⟨root,τ,data,found,image⟩
  cases type
  unfold update decode snapshot NominalMemory.retainedState
  dsimp only [arrayLengthChoice,arrayPayloadOffset]
  simp only [Option.getD_none,Option.isNone_none,↓reduceIte]
  by_cases declared : NominalMemory.declaredUDVT E name=true
  · simp only [declared,↓reduceIte]
    rw [dif_pos (mload m (p.address root)).isLt]
    by_cases absent : NominalMemory.decodeArray E.layout name (mload m (p.address root)).val m
        (p.address root+32)=none
    · rw [Option.pmap_none' absent]
      simp only [Bind.bind,Option.bind,Option.map_none,absent]
      split <;> rfl
    · obtain ⟨values,decoded⟩ := Option.ne_none_iff_exists'.mp absent
      rw [Option.pmap_some' decoded]
      dsimp only [Bind.bind,Pure.pure,Option.bind,Option.map]
      conv => rhs; rw [decoded]
      by_cases capacity : (MemoryShape.array true (mload m (p.address root)).val).size≤(allocated.shape root).size
      · simp only [dif_pos capacity,if_pos capacity]
        rfl
      · simp only [dif_neg capacity,if_neg capacity]
  · simp only [declared,Bool.false_eq_true,↓reduceIte,Bind.bind,Option.bind,Option.map_none]

end Solidity.Yul.Views.NominalInventory
