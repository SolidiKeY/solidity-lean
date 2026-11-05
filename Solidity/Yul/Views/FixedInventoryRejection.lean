import Solidity.Yul.Views.FixedInventoryHistory
import Solidity.Yul.Views.FixedInventoryTransport

/-! Rejection is derived from an actual covered root's decoder failure, not
an assumed execution verdict. Preparation runs before writes; a rejected later
snapshot retains the successful prefix and the exact remaining input suffix. -/
namespace Solidity.Yul.Views.FixedInventory
open NominalInventory (SnapshotCursor)

theorem updates_reject_member {E : Source.Env} {origin h : Source.Heap E.layout}
    (allocated : Placement origin) (p : Placement h) (es entries : List (MixedHeapEntry p))
    (e : MixedHeapEntry p) (member : e∈entries) (m : ByteView)
    (rejected : update allocated p es e m=none) : updates allocated p es entries m=none := by
  first | solve | simp only [updates]
        | induction entries with
          | nil => cases member
          | cons a rest ih =>
            rcases List.mem_cons.mp member with same | tail
            · subst a
              simp only [updates,rejected,Bind.bind,Option.bind_none]
            · unfold updates
              cases first : update allocated p es a m with
              | none => rfl
              | some u => simp only [Bind.bind,Option.bind_some,ih tail,Option.bind_none]

theorem snapshotStep_reject_entry {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (e : MixedHeapEntry c.placement) (member : e∈c.entries) (m : ByteView)
    (rejected : decode c.placement c.entries e.ty m (c.placement.address e.id)=none) :
    snapshotStep allocated s c m=none := by
  first | solve | simp only [snapshotStep_eq]
        | have one : update allocated c.placement c.entries e m=none := by
            simp only [update,rejected,Bind.bind,Option.bind_none]
          rw [snapshotStep_eq,updates_reject_member allocated c.placement c.entries c.entries e member m one]
          rfl

/-- Coverage identifies a real typed entry; decoder failure then rejects the
whole snapshot independently of inventory order and preceding prepared entries. -/
theorem snapshotStep_reject_fixed {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (coverage : CoversMixedHeap c.entries) (root : Nat) (f : Source.FixTy) (k : Option Nat)
    (typed : s.2.heap.ty root=some (.array .memory (.fixed f) k)) (m : ByteView)
    (rejected : snapshot c.placement f k m (c.placement.address root)=none) :
    snapshotStep allocated s c m=none := by
  first | solve | simp only [snapshotStep_eq]
        | have present : (s.2.heap.get root).isSome := by
            change (s.2.heap.get root).map Sigma.fst=some (.array .memory (.fixed f) k) at typed
            cases found : s.2.heap.get root with
            | none => rw [found] at typed; cases typed
            | some d => rfl
          obtain ⟨e,member,id⟩ := coverage root present
          have entryType := heap_ty_of_get s.2.heap e.id e.ty e.data e.found
          rw [id,typed] at entryType
          have ty : e.ty=.array .memory (.fixed f) k := (Option.some.inj entryType).symm
          apply snapshotStep_reject_entry allocated s c e member m
          rw [ty,id]
          exact rejected

/-- Rejected preparation leaves the full reached cursor and suffix untouched. -/
theorem runSnapshots_rejected {E : Source.Env} {Γ : Source.RCtx} {origin : Source.Heap E.layout}
    (allocated : Placement origin) (s : Source.EMState E Γ) (c : SnapshotCursor allocated s)
    (m : ByteView) (ms : List ByteView) (rejected : snapshotStep allocated s c m=none) :
    runSnapshots allocated s c (m::ms)=⟨⟨s,c⟩,m::ms⟩ := by
  simp only [runSnapshots,rejected]

end Solidity.Yul.Views.FixedInventory
