import Solidity.Yul.Views.FixedNominalFields
import Solidity.Yul.Views.InventoryObject

/-! Mixed fixed/nominal struct snapshots construct actual typed inventory images.
Writeback executes existing Source.heapPut with its complete result; unchanged
and owner-safety laws retain genuine image/coverage/typing premises. -/
namespace Solidity.Yul.Views.FixedNominalMember
open Solidity.Yul.Views

theorem decodedFields_snapshot {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (τs : List Source.STy) (m : ByteView) (base : Nat)
    (fs : Source.DataList E.layout τs) (decoded : decodeFields p es τs m base = some fs) :
    MemoryFields p fs (List.ofFn (fun i : Fin τs.length => mload m (base+i.val*32))) := by
  obtain ⟨ws,fields,reads⟩ := decodeFields_representation p es τs m base fs decoded
  have same : ws = List.ofFn (fun i : Fin τs.length => mload m (base+i.val*32)) := by
    apply List.ext_getElem
    · simp only [List.length_ofFn]; exact fields.length
    · intro i hi hj
      simp only [List.getElem_ofFn]
      exact (reads i ws[i] (List.getElem?_eq_getElem hi)).symm
  rw [← same]
  exact fields

def snapshotStruct {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h) (es : List (MixedHeapEntry p))
    (l : Source.DataLoc) (name : Source.DeclName) (m : ByteView) (base : Nat) : Option (InventoryObject p (.struct l name)) :=
  (decodeFields p es (E.layout.fields name) m base).pmap (fun fs decoded =>
    ⟨.struct fs,.strct (E.layout.fields name).length,.strct fs,
      .words _ _ (.strct fs _ (decodedFields_snapshot p es _ m base fs decoded))⟩)
    (fun _ member => member)

theorem snapshotStruct_raw {E : Source.Env} {h : Source.Heap E.layout} (p : Placement h)
    (es : List (MixedHeapEntry p)) (l : Source.DataLoc) (name : Source.DeclName)
    (m : ByteView) (base : Nat) (o : InventoryObject p (.struct l name))
    (decoded : snapshotStruct p es l name m base=some o) : o.image.encode m base=m := by
  first | solve | simp only [snapshotStruct] at decoded ⊢
        | obtain ⟨fs,valid,dec,same⟩ := Option.pmap_eq_some_iff.mp decoded
          subst o
          exact decodeStaticUint_reencode (E.layout.fields name).length m base

def structHeap {E : Source.Env} (h : Source.Heap E.layout) (p : Placement h) (es : List (MixedHeapEntry p))
    (root : Nat) (name : Source.DeclName) (old : Source.DataList E.layout (E.layout.fields name))
    (found : h.get root = some ⟨.struct .memory name, .struct old⟩) (m : ByteView) : Option (Source.Heap E.layout) :=
  (decodeFields p es (E.layout.fields name) m (p.address root)).map
    (fun fs => h.write root (.struct fs) (heap_ty_of_get h root _ _ found))

def structState {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ) (p : Placement s.2.heap)
    (es : List (MixedHeapEntry p)) (root : Nat) (name : Source.DeclName) (m : ByteView) : Option (Except Source.Halt Unit × Source.EMState E Γ) :=
  (decodeFields p es (E.layout.fields name) m (p.address root)).map (fun fs => (Source.heapPut root ⟨.struct .memory name, .struct fs⟩).run s)

theorem structState_MemOK (E : Source.Env) {Γ : Source.RCtx} (H : Source.HeapTy) (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (root : Nat) (name : Source.DeclName) (m : ByteView)
    (result : Except Source.Halt Unit × Source.EMState E Γ) (step : structState s p es root name m = some result)
    (ok : Source.MemOK E H s) : Source.MemOK E H result.2 := by
  obtain ⟨fs, decoded, same⟩ := Option.map_eq_some_iff.mp step
  subst result
  obtain ⟨ws, fields, reads⟩ := decodeFields_representation p es _ m (p.address root) fs decoded
  have valid : Source.DataOK E s.2.heap.ty (Source.Data.struct (l := .memory) fs) := .struct fields.dataOK
  have one := Source.heapPut_ok (E := E) (Γ := Γ) (H := H) root ⟨.struct .memory name, .struct fs⟩ s ⟨ok.1, valid⟩
  have two := Source.heapPut_top (E := E) (Γ := Γ) root ⟨.struct .memory name, .struct fs⟩ s ⟨ok.2.1, trivial⟩
  have three := Source.heapPut_inner (E := E) (Γ := Γ) root ⟨.struct .memory name, .struct fs⟩ s ⟨ok.2.2, fields.allVal⟩
  cases run : (Source.heapPut root ⟨.struct .memory name, .struct fs⟩ : Source.EM E Γ Unit).run s with
  | mk outcome out =>
    cases outcome with
    | ok value => exact ⟨by simpa only [run] using one, by simpa only [run] using two, by simpa only [run] using three⟩
    | error e =>
      have em : Source.EMOK E H out ∧ (Source.NotStuck e ∨ out.2.heap.ty root ≠ some (.struct .memory name)) := by simpa only [run] using one
      exact ⟨em.1, by simpa only [run] using two, by simpa only [run] using three⟩

theorem struct_encode {E : Source.Env} (h : Source.Heap E.layout) (p : Placement h) (es : List (MixedHeapEntry p))
    (coverage : CoversMixedHeap es) (root : Nat) (name : Source.DeclName) (old fs : Source.DataList E.layout (E.layout.fields name))
    (found : h.get root = some ⟨.struct .memory name, .struct old⟩) (ws : List Roadmap.Word) (fields : MemoryFields p fs ws)
    (supported : ∀ τ ∈ E.layout.fields name, Supported E τ) (m : ByteView) :
    structHeap h p es root name old found (wordListView ws m (p.address root)) =
      some (h.write root (.struct fs) (heap_ty_of_get h root _ _ found)) := by
  unfold structHeap
  rw [decodeFields_reads p es coverage fields supported _ _ (fun i w found => wordList_read ws m (p.address root) i w found)]
  rfl

theorem struct_unchanged {E : Source.Env} {Γ : Source.RCtx} (s : Source.EMState E Γ)
    (p : Placement s.2.heap) (es : List (MixedHeapEntry p)) (coverage : CoversMixedHeap es) (root : Nat) (name : Source.DeclName)
    (old : Source.DataList E.layout (E.layout.fields name)) (found : s.2.heap.get root = some ⟨.struct .memory name, .struct old⟩)
    (ws : List Roadmap.Word) (fields : MemoryFields p old ws) (supported : ∀ τ ∈ E.layout.fields name, Supported E τ)
    (m : ByteView) (reads : ∀ i w, ws[i]? = some w → mload m (p.address root + i * 32) = w) :
    structState s p es root name m = some (.ok (), s) := by
  unfold structState
  rw [decodeFields_reads p es coverage fields supported _ _ reads]
  simp only [Option.map_some]
  rw [structHeapPut_run s root name old (heap_ty_of_get s.2.heap root _ _ found), heap_write_unchanged s.2.heap root _ _ found, withSourceHeap_unchanged]

theorem struct_result {E : Source.Env} (h : Source.Heap E.layout) (p : Placement h) (es : List (MixedHeapEntry p))
    (root : Nat) (name : Source.DeclName) (old : Source.DataList E.layout (E.layout.fields name))
    (found : h.get root = some ⟨.struct .memory name, .struct old⟩) (m : ByteView) (out : Source.Heap E.layout)
    (step : structHeap h p es root name old found m = some out) :
    (∃ q : Placement out, q.address = p.address ∧ q.shape = p.shape ∧ q.free = p.free) ∧
      out.ty = h.ty ∧ out.next = h.next ∧ (∀ a, h.next ≤ a → out.cells a = none) ∧ ∀ a, a ≠ root → out.get a = h.get a := by
  obtain ⟨fs, decoded, same⟩ := Option.map_eq_some_iff.mp step
  subst out
  exact ⟨⟨structWrittenPlacement h p root name old fs found, rfl, rfl, rfl⟩,
    funext (fun a => Source.Heap.write_ty _ _ a _ _), rfl, fun a ha => (h.write root _ _).bounded a ha, fun a ha => Source.Heap.write_other _ ha _ _⟩

end Solidity.Yul.Views.FixedNominalMember
