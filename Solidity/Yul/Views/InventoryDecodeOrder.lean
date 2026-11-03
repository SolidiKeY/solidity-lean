import Solidity.Yul.Views.InventorySequential
import Solidity.Yul.Views.InventoryOrder

/-! Visit-order transport for the actual pure inventory decoder and actual
Source update runner. The candidate inventory stays fixed: changing pointer
lookup coverage is a different obligation. None remains unsupported preparation,
not a Source/Yul refusal or a successful no-op. -/
namespace Solidity.Yul.Views

theorem decodeInventoryUpdates_filterMap {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (candidates entries : List (MixedHeapEntry p))
    (m : ByteView) : decodeInventoryUpdates allocated p candidates entries m=
      if entries.all (fun e=>(decodeInventoryUpdate allocated p candidates e m).isSome)
      then some (entries.filterMap (fun e=>decodeInventoryUpdate allocated p candidates e m)) else none := by
  induction entries with
  | nil => rfl
  | cons e entries ih =>
    rw [decodeInventoryUpdates,ih]
    cases one : decodeInventoryUpdate allocated p candidates e m with
    | none =>
      simp only [one,List.all_cons,Option.isSome_none,Bool.false_and]
      rfl
    | some u =>
      cases all : entries.all (fun e=>(decodeInventoryUpdate allocated p candidates e m).isSome) <;>
        simp only [List.all_cons,List.filterMap_cons,one,all,Option.isSome_some,Bool.true_and,↓reduceIte] <;> rfl

/-- Exact all-or-none behavior under any visit permutation; successful decoded
updates are a real permutation of the actual typed decoded objects. -/
theorem decodeInventoryUpdates_perm {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (candidates : List (MixedHeapEntry p))
    {entries others : List (MixedHeapEntry p)} (perm : entries.Perm others) (m : ByteView) :
    (decodeInventoryUpdates allocated p candidates entries m=none ↔
      decodeInventoryUpdates allocated p candidates others m=none) ∧
    (∀ us,decodeInventoryUpdates allocated p candidates entries m=some us →
      ∃ vs,decodeInventoryUpdates allocated p candidates others m=some vs ∧ us.Perm vs) := by
  have same : entries.all (fun e=>(decodeInventoryUpdate allocated p candidates e m).isSome)=
      others.all (fun e=>(decodeInventoryUpdate allocated p candidates e m).isSome) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.all_eq_true,List.all_eq_true]
    constructor <;> intro all e member
    · exact all e (perm.mem_iff.mpr member)
    · exact all e (perm.mem_iff.mp member)
  rw [decodeInventoryUpdates_filterMap,decodeInventoryUpdates_filterMap,same]
  cases valid : others.all (fun e=>(decodeInventoryUpdate allocated p candidates e m).isSome) with
  | false => exact ⟨Iff.rfl,by intro us bad;cases bad⟩
  | true =>
    constructor
    · constructor <;> intro bad <;> cases bad
    · intro us decoded
      cases decoded
      exact ⟨_,rfl,perm.filterMap _⟩

/-- Same fixed candidates and supplied raw map, arbitrary distinct-root visit
order: COMPLETE actual Source results (including its error/prefix state) agree. -/
theorem decodedInventory_runs_perm {E : Source.Env} {Γ : Source.RCtx} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (candidates : List (MixedHeapEntry p))
    {entries others : List (MixedHeapEntry p)} (perm : entries.Perm others)
    (distinct : (entries.map MixedHeapEntry.id).Nodup) (m : ByteView)
    (s : Source.EMState E Γ) (types : s.2.heap.ty=h.ty) :
    (decodeInventoryUpdates allocated p candidates entries m).map (fun us=>(runInventoryUpdates us).run s)=
      (decodeInventoryUpdates allocated p candidates others m).map (fun us=>(runInventoryUpdates us).run s) := by
  have order := decodeInventoryUpdates_perm allocated p candidates perm m
  cases decoded : decodeInventoryUpdates allocated p candidates entries m with
  | none => rw [order.1.mp decoded]
  | some us =>
    obtain ⟨vs,other,permuted⟩ := order.2 us decoded
    rw [other]
    simp only [Option.map_some]
    have ids := decodeInventoryUpdates_ids allocated p candidates entries m us decoded
    exact congrArg some (runInventoryUpdates_perm permuted (ids ▸ distinct) s types)
/-- The existing writeback entrypoint agrees with any distinct-root visit order,
while retaining its ORIGINAL pointer candidates and exact unsupported result. -/
theorem inventoryStateWriteback_visit_perm {E : Source.Env} {Γ : Source.RCtx}
    {origin : Source.Heap E.layout} (s : Source.EMState E Γ) (allocated : Placement origin)
    (p : Placement s.2.heap) (history : RetainedAllocation allocated p)
    (entries others : List (MixedHeapEntry p)) (perm : entries.Perm others)
    (distinct : (entries.map MixedHeapEntry.id).Nodup) (m : ByteView) :
    inventoryStateWriteback s allocated p history entries m=
      (decodeInventoryUpdates allocated p entries others m).map (fun us=>(runInventoryUpdates us).run s) :=
  decodedInventory_runs_perm allocated p entries perm distinct m s rfl

/-- Actual sequential placement/history/candidate refresh after EVERY write may
visit distinct roots in any order. The pointer candidate inventory is fixed at
entry and concretely transported by the existing refresh proof. None is exact. -/
theorem inventoryStateWriteback_sequential_perm {E : Source.Env} {Γ : Source.RCtx}
    {origin : Source.Heap E.layout} (s : Source.EMState E Γ) (allocated : Placement origin)
    (p : Placement s.2.heap) (history : RetainedAllocation allocated p)
    (entries others : List (MixedHeapEntry p)) (perm : entries.Perm others)
    (distinct : (entries.map MixedHeapEntry.id).Nodup) (m : ByteView) :
    inventoryStateWriteback s allocated p history entries m=
      (sequentialInventory allocated p history others s.2.heap p history rfl entries m).map
        (fun realized=>((.ok () : Except Source.Halt Unit),withSourceHeap s realized.heap)) := by
  rw [inventoryStateWriteback_visit_perm s allocated p history entries others perm distinct m]
  rw [sequentialInventory_snapshot_aux allocated p history entries others s.2.heap p history rfl entries
    rfl (fun _ _=>rfl),Option.map_map]
  apply congrArg (fun f=>(decodeInventoryUpdates allocated p entries others m).map f)
  funext us
  exact realizeInventory_run allocated p history us s p history rfl entries

end Solidity.Yul.Views
