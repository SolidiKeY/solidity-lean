import Solidity.Yul.Views.JointRaw

namespace Solidity.Yul.Views

/-- Snapshot joint decoding is EXACTLY the second concrete root decoder after
actually applying the first source write and refreshing all owned candidates.
The equality includes None and every complete source error result of that
second operation. Only the real first-root lookup/decode and constructor image
are inputs; decoder stability/outputPlacement are proved, not assumed. -/
theorem canonicalJoint_sequential {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (a : Nat) (name : Source.DeclName)
    (old fs : Source.DataList E.layout (E.layout.fields name))
    (found : s.2.heap.get a = some ⟨.struct .memory name,.struct old⟩)
    (ws : List Roadmap.Word) (fields : MemoryFields p fs ws)
    (b : Nat) (τ : Source.STy) (k : Option Nat) (n : Nat) (hl : ∀ z, k = some z → z = n)
    (m : ByteView) (decoded : decodeCanonicalFields p es (E.layout.fields name) m (p.address a) = some fs) :
    let ht := heap_ty_of_get s.2.heap a _ _ found
    let next := withSourceHeap s (s.2.heap.write a (.struct fs) ht)
    let q := structWrittenPlacement s.2.heap p a name old fs found
    let image : MemoryImage q (.struct (l := .memory) fs) := .words _ ws (.strct fs ws
      (fields.transport q (funext (fun c => Source.Heap.write_ty s.2.heap a c (.struct fs) ht)) rfl))
    let entries := refreshMixedEntries p a (.struct fs) ht q rfl image es
    canonicalJointState s p es a name b τ k n hl false m = canonicalArrayState next q entries b τ k n hl m := by
  dsimp only
  unfold canonicalJointState canonicalArrayState
  rw [decodeCanonicalArray_refresh]
  simp only [structWrittenPlacement, heapWritePlacement]
  split
  · rw [decoded]
    cases da : decodeCanonicalArray p es τ n m (p.address b + arrayPayloadOffset k) with
    | none => rfl
    | some values =>
      simp only [Bool.false_eq_true, if_false, Option.map_some]
      change some ((twoHeapPut a (Source.Data.struct (l := .memory) fs) b (memberArrayData E.layout τ k n hl values)).run s) =
        some ((Source.heapPut b ⟨_,memberArrayData E.layout τ k n hl values⟩ : Source.EM E Γ Unit).run
          (withSourceHeap s (s.2.heap.write a (.struct fs) (heap_ty_of_get s.2.heap a _ _ found))))
      rw [twoHeapPut, Source.Hoare.run_bind, heapPutConcrete_run s a (.struct fs) (heap_ty_of_get s.2.heap a _ _ found)]
  · rfl

end Solidity.Yul.Views
