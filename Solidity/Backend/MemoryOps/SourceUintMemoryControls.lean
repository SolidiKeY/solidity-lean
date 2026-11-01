import Solidity.Backend.MemoryOps.SourceUintMemory
import Solidity.Backend.MemoryOps.SnapshotScheduleControls
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceUintMemoryControls
open Source.SemanticsExamples (E0 F0 s0)
private abbrev U := PrimTy.uint.Denote
private def zero : U := ⟨0,by decide⟩
private def seven : U := ⟨7,by decide⟩
private def maximum : U := ⟨((2^256-1 : Nat) : Int),by decide⟩
private abbrev A : RefTy := .array (.prim .uint)
private abbrev P : RefTy := .fixed (.ref A) 3
private abbrev H : HTy := [A,A,P]
private def r : HRef H A := ⟨0,rfl⟩
private def neighbor : HRef H A := ⟨1,rfl⟩
private def parent : HRef H P := ⟨2,rfl⟩
private def initial (n : Nat) : List U := [seven,maximum,maximum]++List.replicate n zero
private def hp (n : Nat) (hn : n+3<2^256) : Heap H :=
  (⟨initial n,by simp only [initial,List.length_append,List.length_cons,List.length_nil,List.length_replicate];omega⟩,
    ⟨[maximum,zero],by decide⟩,⟨[r,neighbor,r],rfl⟩,())
private theorem elems (n : Nat) (hn : n+3<2^256) : MObj.elems .dyn ((hp n hn).get r)=initial n := by
  simp only [Heap.get,Objs.get,hp,r,MObj.elems_dyn]
private theorem neighbor_elems (n : Nat) (hn : n+3<2^256) : MObj.elems .dyn ((hp n hn).get neighbor)=[maximum,zero] := by
  simp only [Heap.get,Objs.get,hp,neighbor,MObj.elems_dyn]
private theorem parent_elems (n : Nat) (hn : n+3<2^256) : MObj.elems .fixed ((hp n hn).get parent)=[r,neighbor,r] := by
  simp only [Heap.get,Objs.get,hp,parent,MObj.elems_fixed]
private theorem len (n : Nat) (hn : n+3<2^256) : (hp n hn).len r .dyn=n+3 := by
  simp only [Heap.len,elems,initial,List.length_append,List.length_cons,List.length_nil,List.length_replicate];omega
private abbrev SH := (Source.Heap.empty (D := E0.layout)).ty
private def y0 : Source.EMState E0 [] := (.nil,s0)
private def firstSource (n : Nat) : Source.EMState E0 [] := ((Source.allocRef (sourceUintMemory (initial n))).run y0).2
private def sy (n : Nat) : Source.EMState E0 [] := ((Source.allocRef (sourceUintMemory [maximum,zero])).run (firstSource n)).2
private theorem represented (n : Nat) (hn : n+3<2^256) : SourceUintMemoryAt (sy n) 0 (hp n hn) r .dyn := by
  unfold SourceUintMemoryAt;rw [elems];rfl
private theorem neighbor_represented (n : Nat) (hn : n+3<2^256) : SourceUintMemoryAt (sy n) 1 (hp n hn) neighbor .dyn := by
  unfold SourceUintMemoryAt
  rw [neighbor_elems]
  rfl
private abbrev SΓ : Source.RCtx := [.array .memory (.int .u256) none,.array .memory (.int .u256) none,.int .u256]
private def args (n : Nat) (k : U) : Source.EMState E0 SΓ :=
  (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (sourceUint k) .nil)),(sy n).2)

/-- Two actual Source allocations establish numeric array/neighbor contents and
MemOK, with the source table independent of the intrinsic heap constructor. -/
theorem allocated_source (n : Nat) (hn : n+3<2^256) :
    (Source.allocRef (sourceUintMemory (initial n))).run y0=(.ok (.memRef rfl 0),firstSource n) ∧
    (Source.allocRef (sourceUintMemory [maximum,zero])).run (firstSource n)=(.ok (.memRef rfl 1),sy n) ∧
    Source.MemOK E0 SH (sy n) ∧ SourceUintMemoryAt (sy n) 0 (hp n hn) r .dyn ∧
    SourceUintMemoryAt (sy n) 1 (hp n hn) neighbor .dyn ∧
    [(sy n).2.heap.get 0,(sy n).2.heap.get 1]=
      [some ⟨.array .memory (.int .u256) none,sourceUintMemory (initial n)⟩,
       some ⟨.array .memory (.int .u256) none,sourceUintMemory [maximum,zero]⟩] ∧
    (sy n).2.heap.next=2 ∧ MObj.elems .fixed ((hp n hn).get parent)=[r,neighbor,r] := by
  have hi : Source.MemOK E0 SH y0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have h0 := source_uint_alloc y0 (initial n)
  change (Source.allocRef (sourceUintMemory (initial n))).run y0=(.ok (.memRef rfl 0),firstSource n) at h0
  have hm0 := source_uint_alloc_memOK (E := E0) (Γ := []) SH (initial n) y0 hi
  rw [h0] at hm0
  have h1 := source_uint_alloc (firstSource n) [maximum,zero]
  change (Source.allocRef (sourceUintMemory [maximum,zero])).run (firstSource n)=(.ok (.memRef rfl 1),sy n) at h1
  have hm1 := source_uint_alloc_memOK (E := E0) (Γ := []) SH [maximum,zero] (firstSource n) hm0.1
  rw [h1] at hm1
  exact ⟨h0,h1,hm1.1,represented n hn,neighbor_represented n hn,rfl,rfl,parent_elems n hn⟩

/-- Both actual declared Source pipelines read the same represented uint through
shared locals; every valid runtime index is covered, not only a fixture index. -/
theorem resolved_reads (p : Roadmap.Pipeline) (n : Nat) (hn : n+3<2^256) (k : U) (hk : k.1.toNat<n+3) :
    let v := (initial n)[k.1.toNat]'(by simp only [initial,List.length_append,List.length_cons,List.length_nil,List.length_replicate];omega)
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local (.here : Source.Idx SΓ _)) (.local (.there (.there .here))) rfl)).run (args n k)=
      (.ok (.val (sourceUint v)),args n k) ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local (.there .here : Source.Idx SΓ _)) (.local (.there (.there .here))) rfl)).run (args n k)=
      (.ok (.val (sourceUint v)),args n k) ∧
    (hp n hn).index r .dyn k=some v := by
  have hr : SourceUintMemoryAt (args n k) 0 (hp n hn) r .dyn := represented n hn
  have hb : k.1.toNat<(hp n hn).len r .dyn := by rw [len];exact hk
  refine ⟨?_,?_,?_⟩
  · simpa only [elems] using hr.eval_index (Source.SemanticsExamples.G0 p) F0 0 .here (.there (.there .here)) k rfl rfl hb
  · simpa only [elems] using hr.eval_index (Source.SemanticsExamples.G0 p) F0 0 (.there .here) (.there (.there .here)) k rfl rfl hb
  · change (MObj.elems .dyn ((hp n hn).get r))[k.1.toNat]?=some _
    rw [elems]
    exact List.getElem?_eq_getElem _

private theorem provenance (n copies : Nat) (hn : n+3<2^256) :
    ∀ k,(MObj.elems .dyn ((hp n hn).get r))[captureOrigin (ScheduleControls.restoreCycles copies) k]?=
      (MObj.elems .dyn ((hp n hn).get r))[k]? := by
  have hc : ∀ k,(MObj.elems .dyn ((hp n hn).get r))[captureOrigin ScheduleControls.cycle k]?=(MObj.elems .dyn ((hp n hn).get r))[k]? := by
    intro k;rw [ScheduleControls.cycle_origin]
    by_cases he : k=1
    · subst k;rw [if_pos rfl,elems];rfl
    · rw [if_neg he]
  induction copies with
  | zero => intro k;rfl
  | succ copies ih => intro k;rw [ScheduleControls.restoreCycles,captureOrigin_append];exact (hc _).trans (ih k)

/-- Arbitrarily many REAL break/repair cycles restore numeric contents using
computed INITIAL provenance; repeated old references and neighbor are retained. -/
theorem restoring_cycles (n copies : Nat) (hn : n+3<2^256) :
    runCaptures (hp n hn) r .dyn (ScheduleControls.restoreCycles copies)=some (hp n hn) ∧
    SourceUintMemoryAt (sy n) 0 (hp n hn) r .dyn ∧
    [MObj.elems .dyn ((hp n hn).get r),MObj.elems .dyn ((hp n hn).get neighbor)]=[initial n,[maximum,zero]] ∧
    (MObj.elems .fixed ((hp n hn).get parent)).map HRef.id=[0,1,0] := by
  have hv : CapturesValid ((hp n hn).len r .dyn) (ScheduleControls.restoreCycles copies) := by
    rw [len];exact ScheduleControls.cycles_valid _ copies (by omega)
  obtain ⟨out,ho⟩ := (runCaptures_success_iff (hp n hn) r .dyn _).mpr hv
  have he := (runCaptures_heap_restore_iff (hp n hn) out r .dyn _ ho).mpr (provenance n copies hn)
  exact ⟨ho.trans (congrArg some he),represented n hn,by rw [elems,neighbor_elems],by rw [parent_elems];rfl⟩

private theorem hs (n : Nat) (hn : n+3<2^256) : SliceBounds ((hp n hn).len r .dyn) 0 1 := by rw [len];exact ⟨by decide,by omega⟩
private theorem hd (n : Nat) (hn : n+3<2^256) : 1+(1-0)≤(hp n hn).len r .dyn := by rw [len];omega
private def mid (n : Nat) (hn : n+3<2^256) := captureOverwrite (hp n hn) r .dyn r .dyn 0 1 1 (hs n hn) (hd n hn)
private theorem mid_values (n : Nat) (hn : n+3<2^256) : MObj.elems .dyn ((mid n hn).get r)=[seven,seven,maximum]++List.replicate n zero := by
  rw [mid,captureOverwrite,overwriteSlice_elems]
  simp only [sliceElems,elems,initial]
  rfl

/-- A materially changed reached heap disagrees at the old Source index, while
its computed INITIAL-origin read agrees. Wrong max truncation is discriminated. -/
theorem changed_intermediate (n : Nat) (hn : n+3<2^256) :
    runCaptures (hp n hn) r .dyn [ScheduleControls.first]=some (mid n hn) ∧
    [MObj.elems .dyn ((hp n hn).get r),MObj.elems .dyn ((mid n hn).get r)]=
      [initial n,[seven,seven,maximum]++List.replicate n zero] ∧
    ¬ SourceUintMemoryAt (sy n) 0 (mid n hn) r .dyn ∧
    (Source.readLoc (E := E0) (Γ := []) F0 (τ := .int .u256) (.mem 0 1)).run (sy n)=(.ok (sourceUint maximum),sy n) ∧
    (Source.readLoc (E := E0) (Γ := []) F0 (τ := .int .u256) (.mem 0 (captureOrigin [ScheduleControls.first] 1))).run (sy n)=
      (.ok (sourceUint seven),sy n) ∧
    MObj.elems .dyn ((mid n hn).get neighbor)=[maximum,zero] ∧
    (MObj.elems .fixed ((mid n hn).get parent)).map HRef.id=[0,1,0] := by
  have ho : runCaptures (hp n hn) r .dyn [ScheduleControls.first]=some (mid n hn) := by
    rw [runCaptures_singleton]
    exact checkedCaptureOverwrite_some _ r .dyn r .dyn 0 1 1 (hs n hn) (hd n hn)
  have hread : (Source.readLoc (E := E0) (Γ := []) F0 (τ := .int .u256) (.mem 0 1)).run (sy n)=(.ok (sourceUint maximum),sy n) :=
    ((represented n hn).read_nat_iff F0 1 maximum).mpr (by rw [elems];rfl)
  refine ⟨ho,?_,?_,hread,((represented n hn).schedule_read_iff _ _ ho F0 1 seven).mpr ?_,?_,?_⟩
  · rw [elems,mid_values]
  · intro hbad
    have he := (hbad.read_nat_iff F0 1 maximum).mp hread
    rw [mid_values] at he
    exact (show seven≠maximum by decide) (Option.some.inj he)
  · rw [mid_values];rfl
  · rw [runCaptures_frame _ _ _ _ _ ho neighbor (by decide),neighbor_elems]
  · rw [runCaptures_frame _ _ _ _ _ ho parent (by decide),parent_elems];rfl

private def copiedChild : SVal (.ref A) := .array (.cons (.prim maximum) (.cons (.prim seven) .nil)) .nil (by decide)
private def tree : SVal (.ref (.fixed (.ref A) 1)) := .fixed (.cons copiedChild .nil)

/-- Real nested builder plus numeric old-root recapture cycles: recursive mirror,
INITIAL Source provenance and fresh child contents/identity are all derived. -/
theorem copied_tree (n copies : Nat) (hn : n+3<2^256) :
    let g := tree.copyStToM (hp n hn) rfl
    ∃ (out : Heap g.H') (q : HRef g.H' A),
      runCaptures g.heap (r.wk g.ext) .dyn (ScheduleControls.restoreCycles copies)=some out ∧
      tree.Mirrors out H.length g.val ∧
      H.length≤g.val.id ∧ H.length≤q.id ∧ q.id≠(r.wk g.ext).id ∧
      MObj.elems .fixed (out.get g.val)=[q] ∧ MObj.elems .dyn (out.get q)=[maximum,seven] ∧
      MObj.elems .dyn (out.get (r.wk g.ext))=initial n ∧
      MObj.elems .dyn (out.get (neighbor.wk g.ext))=[maximum,zero] ∧
      (MObj.elems .fixed (out.get (parent.wk g.ext))).map HRef.id=[0,1,0] ∧
      (Source.readLoc (E := E0) (Γ := []) F0 (τ := .int .u256) (.mem 0 (captureOrigin (ScheduleControls.restoreCycles copies) 1))).run (sy n)=
        (.ok (sourceUint maximum),sy n) := by
  dsimp only
  have hb := (restoring_cycles n copies hn).1
  obtain ⟨out,ho,hk,hm,hframes⟩ := copy_schedule_transport (hp n hn) (hp n hn) tree rfl r .dyn _ hb
  have hs := (represented n hn).copy_schedule tree rfl _ out ho F0 1 maximum
  have hmirror := hs.1
  change H.length≤_ ∧ _ at hmirror
  obtain ⟨q,qs,hroot,hchild,hqs⟩ := hmirror.2
  change qs=[] at hqs
  subst qs
  change H.length≤q.id ∧ _ at hchild
  obtain ⟨x,xs,hvals,hx,hxs⟩ := hchild.2
  change x=maximum at hx
  subst x
  obtain ⟨v,vs,hvals₂,hv,hvs⟩ := hxs
  change v=seven at hv
  subst v
  change vs=[] at hvs
  subst vs
  have hvals' : MObj.elems .dyn (out.get q)=[maximum,seven] := hvals.trans (congrArg (List.cons maximum) hvals₂)
  have hold : MObj.elems .dyn (out.get (r.wk (tree.copyStToM (hp n hn) rfl).ext))=initial n := by
    rw [hk r,MObj.elems_wk,List.map_id'' (f := MVal.wk (tree.copyStToM (hp n hn) rfl).ext (.prim .uint)) (fun _ => rfl)]
    exact elems n hn
  refine ⟨out,q,ho,hs.1,hmirror.1,hchild.1,?_,hroot,hvals',hold,?_,?_,hs.2.mpr ?_⟩
  · have hf := hchild.1
    change 3≤q.id at hf
    change q.id≠0
    omega
  · rw [hk neighbor,MObj.elems_wk,List.map_id'' (f := MVal.wk (tree.copyStToM (hp n hn) rfl).ext (.prim .uint)) (fun _ => rfl)]
    exact neighbor_elems n hn
  · rw [hk parent,MObj.elems_wk,parent_elems]
    rfl
  · rw [hold];rfl

/-- Empty-array, raw wrong-type/missing errors and a genuinely invalid later
capture remain distinct. Raw mismatched reads are not typed Source programs. -/
theorem endpoints_and_negatives :
    let y : Source.EMState E0 [] := ((Source.allocRef (sourceUintMemory [])).run y0).2
    (Source.readLoc F0 (τ := .int .u256) (.mem 0 0)).run y=(.error (.revert (Source.panicData .index)),y) ∧
    (Source.readLoc (E := E0) (Γ := []) F0 (τ := .bool) (.mem 0 0)).run (sy 0)=(.error (.stuck "element type"),sy 0) ∧
    (Source.readLoc (E := E0) (Γ := []) F0 (τ := .int .u256) (.mem 0 0)).run y0=(.error (.stuck "dangling memory reference"),y0) ∧
    runCaptures (hp 0 (by decide)) r .dyn [ScheduleControls.first,(2,1,0)]=none := by
  dsimp only
  refine ⟨source_uint_bounds _ 0 [] (by rfl) 0 (by decide),rfl,rfl,?_⟩
  rw [runCaptures]
  have hfirst : checkedCaptureOverwrite (hp 0 (by decide)) r .dyn r .dyn 0 1 1=some (mid 0 (by decide)) :=
    checkedCaptureOverwrite_some _ r .dyn r .dyn 0 1 1 (hs 0 (by decide)) (hd 0 (by decide))
  change (checkedCaptureOverwrite (hp 0 (by decide)) r .dyn r .dyn 0 1 1).bind _=none
  rw [hfirst]
  change runCaptures (mid 0 (by decide)) r .dyn [(2,1,0)]=none
  apply (runCaptures_none_iff _ _ _ _).mpr
  intro hv
  have hb := hv (2,1,0) (by simp only [List.mem_cons,List.not_mem_nil,or_false])
  exact (by decide : ¬2≤1) hb.1

private def boundaryValues : List U := List.replicate 31 zero++[seven,maximum]
private abbrev BH : HTy := [A]
private def br : HRef BH A := ⟨0,rfl⟩
private def boundaryHeap : Heap BH := (⟨boundaryValues,by decide⟩,())
private def boundarySource : Source.EMState E0 [] := ((Source.allocRef (sourceUintMemory boundaryValues)).run y0).2
private def boundaryArgs (k : U) : Source.EMState E0 SΓ :=
  (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (sourceUint k) .nil)),boundarySource.2)
private theorem boundary_elems : MObj.elems .dyn (boundaryHeap.get br)=boundaryValues := by
  simp only [Heap.get,Objs.get,boundaryHeap,br,MObj.elems_dyn]
private def u31 : U := ⟨31,by decide⟩
private def u32 : U := ⟨32,by decide⟩

/-- Explicit logical element31/32 and exact endpoint33; these are element
indices, not physical byte-word encoding. Both pipelines execute actual syntax. -/
theorem element_boundary (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local (.here : Source.Idx SΓ _)) (.local (.there (.there .here))) rfl)).run (boundaryArgs u31)=
      (.ok (.val (sourceUint seven)),boundaryArgs u31) ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local (.here : Source.Idx SΓ _)) (.local (.there (.there .here))) rfl)).run (boundaryArgs u32)=
      (.ok (.val (sourceUint maximum)),boundaryArgs u32) ∧
    (Source.readLoc (E := E0) (Γ := []) F0 (τ := .int .u256) (.mem 0 33)).run boundarySource=
      (.error (.revert (Source.panicData .index)),boundarySource) ∧
    (Source.indexLoc (E := E0) (Γ := []) F0 (.memRef rfl 0 : Source.Val E0.layout (.array .memory (.int .u256) none)) 33).run boundarySource=
      (.error (.revert (Source.panicData .index)),boundarySource) ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 1 (.indexArray (.local (.here : Source.Idx SΓ _)) (.local (.there (.there .here))) rfl)).run (boundaryArgs u32)=
      (.error .timeout,boundaryArgs u32) ∧
    [boundaryValues[30]?,boundaryValues[31]?,boundaryValues[32]?,boundaryValues[33]?]=[some zero,some seven,some maximum,none] ∧
    sourceUint (D := E0.layout) maximum≠sourceUint zero := by
  have hr : SourceUintMemoryAt boundarySource 0 boundaryHeap br .dyn := by
    unfold SourceUintMemoryAt;rw [boundary_elems];rfl
  have h31 : SourceUintMemoryAt (boundaryArgs u31) 0 boundaryHeap br .dyn := hr
  have h32 : SourceUintMemoryAt (boundaryArgs u32) 0 boundaryHeap br .dyn := hr
  refine ⟨?_,?_,source_uint_bounds boundarySource 0 boundaryValues (by simpa only [SourceUintMemoryAt,boundary_elems] using hr) 33 (by decide),hr.indexLoc_bounds F0 33 (by rw [Heap.len,boundary_elems];decide),?_,rfl,?_⟩
  · have h := h31.eval_index (Source.SemanticsExamples.G0 p) F0 0 .here (.there (.there .here)) u31 rfl rfl (by rw [Heap.len,boundary_elems];decide)
    simpa only [boundary_elems] using h
  · have h := h32.eval_index (Source.SemanticsExamples.G0 p) F0 0 .here (.there (.there .here)) u32 rfl rfl (by rw [Heap.len,boundary_elems];decide)
    simpa only [boundary_elems] using h
  · rfl
  · intro he
    have hv := congrArg (fun v : Source.Val E0.layout (.int .u256) => calldataUint (.val v)) he
    have h : maximum=zero := by simpa only [calldataUint_sourceUint] using hv
    exact (by decide : maximum≠zero) h

private abbrev FK : HTy := [.fixed (.prim .uint) 2]
private def fr : HRef FK (.fixed (.prim .uint) 2) := ⟨0,rfl⟩
private def fh : Heap FK := (⟨[maximum,zero],rfl⟩,())
private theorem fixed_elems : MObj.elems .fixed (fh.get fr)=[maximum,zero] := by
  simp only [Heap.get,Objs.get,fh,fr,MObj.elems_fixed]
private def fixedOut := captureOverwrite fh fr .fixed fr .fixed 0 1 1 (by rw [Heap.len,fixed_elems];exact ⟨by decide,by decide⟩) (by rw [Heap.len,fixed_elems];decide)

/-- Dynamic Source object observed through the published intrinsic fixed ArrTy.
This is contents/shape observation, not a Source fixed-array lowering theorem. -/
theorem intrinsic_fixed :
    SourceUintMemoryAt (sy 0) 1 fh fr .fixed ∧
    runCaptures fh fr .fixed [ScheduleControls.first]=some fixedOut ∧
    [MObj.elems .fixed (fh.get fr),MObj.elems .fixed (fixedOut.get fr)]=[[maximum,zero],[maximum,maximum]] ∧
    (Source.readLoc (E := E0) (Γ := []) F0 (τ := .int .u256) (.mem 1 (captureOrigin [ScheduleControls.first] 1))).run (sy 0)=
      (.ok (sourceUint maximum),sy 0) ∧
    ¬ SourceUintMemoryAt (sy 0) 1 fixedOut fr .fixed := by
  have hr : SourceUintMemoryAt (sy 0) 1 fh fr .fixed := by
    unfold SourceUintMemoryAt;rw [fixed_elems];rfl
  have ho : runCaptures fh fr .fixed [ScheduleControls.first]=some fixedOut := by
    rw [runCaptures_singleton]
    exact checkedCaptureOverwrite_some fh fr .fixed fr .fixed 0 1 1
      (by rw [Heap.len,fixed_elems];exact ⟨by decide,by decide⟩) (by rw [Heap.len,fixed_elems];decide)
  have hv : MObj.elems .fixed (fixedOut.get fr)=[maximum,maximum] := by
    rw [fixedOut,captureOverwrite,overwriteSlice_elems]
    simp only [sliceElems,fixed_elems]
    rfl
  refine ⟨hr,ho,by rw [fixed_elems,hv],(hr.schedule_read_iff _ _ ho F0 1 maximum).mpr (by rw [hv];rfl),?_⟩
  intro hbad
  have hs : (Source.readLoc (E := E0) (Γ := []) F0 (τ := .int .u256) (.mem 1 1)).run (sy 0)=(.ok (sourceUint zero),sy 0) :=
    (hr.read_nat_iff F0 1 zero).mpr (by rw [fixed_elems];rfl)
  have he := (hbad.read_nat_iff F0 1 zero).mp hs
  rw [hv] at he
  exact (by decide : maximum≠zero) (Option.some.inj he)

/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryControls.allocated_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allocated_source
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryControls.resolved_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_reads
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryControls.restoring_cycles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms restoring_cycles
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryControls.changed_intermediate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms changed_intermediate
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryControls.copied_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms copied_tree
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryControls.endpoints_and_negatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms endpoints_and_negatives
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryControls.element_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms element_boundary
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMemoryControls.intrinsic_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms intrinsic_fixed
end Solidity.Backend.MemoryOps.SourceUintMemoryControls
