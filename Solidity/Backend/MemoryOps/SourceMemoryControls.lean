import Solidity.Backend.MemoryOps.SourceWrite
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceMemoryControls
open Source.SemanticsExamples (E0 F0 s0)
private abbrev B : RefTy := .array (.prim .bool)
private abbrev H : HTy := [B,B]
private def r : HRef H B := ⟨0,rfl⟩
private def neighbor : HRef H B := ⟨1,rfl⟩
private def initial (n : Nat) := [true,false,false]++List.replicate n false
private def finalValues (n : Nat) := [true,true,true]++List.replicate n false
private def hp (n : Nat) (hn : n+3<2^256) : Heap H :=
  (⟨initial n,by simp only [initial,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega⟩,
    ⟨[false,true],by decide⟩,())
private theorem old_elems (n : Nat) (hn : n+3<2^256) : MObj.elems .dyn ((hp n hn).get r)=initial n := by
  simp only [Heap.get,Objs.get,hp,r,MObj.elems_dyn]
private theorem neighbor_elems (n : Nat) (hn : n+3<2^256) : MObj.elems .dyn ((hp n hn).get neighbor)=[false,true] := by
  simp only [Heap.get,Objs.get,hp,neighbor,MObj.elems_dyn]
private abbrev emptyTy : Source.HeapTy := (Source.Heap.empty (D := E0.layout)).ty
private def y0 : Source.EMState E0 [] := (.nil,s0)
/-- The Source state is the actual published allocator's output, not a custom
state evaluator or a desired postcondition supplied by the caller. -/
private def sy (n : Nat) : Source.EMState E0 [] :=
  ((Source.allocRef (sourceBoolMemory (initial n))).run y0).2
private theorem represented (n : Nat) (hn : n+3<2^256) : SourceBoolMemoryAt (sy n) 0 (hp n hn) r .dyn := by
  unfold SourceBoolMemoryAt
  rw [old_elems]
  rfl
private def schedule (n copies : Nat) : List SnapshotArgs :=
  [(0,1,1),(1,2,2)]++List.replicate copies (n+3,n+3,n+3)
private theorem size (n : Nat) (hn : n+3<2^256) : (hp n hn).len r .dyn=n+3 := by
  simp only [Heap.len,old_elems,initial,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega
private theorem valid (n copies : Nat) : CapturesValid (n+3) (schedule n copies) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · change 0≤1 ∧ 1≤n+3 ∧ 1+(1-0)≤n+3
      omega
    · change 1≤2 ∧ 2≤n+3 ∧ 2+(2-1)≤n+3
      omega
  · have he := (List.mem_replicate.mp hx).2
    subst x
    change n+3≤n+3 ∧ n+3≤n+3 ∧ n+3+((n+3)-(n+3))≤n+3
    omega
private theorem end_origin (n copies k : Nat) : captureOrigin (List.replicate copies (n,n,n)) k=k := by
  induction copies with
  | zero => rfl
  | succ copies ih =>
    simp only [List.replicate_succ,captureOrigin,ih,snapshotOrigin,Nat.sub_self,Nat.add_zero]
    rw [if_neg (by omega)]
private theorem values (n copies : Nat) (hn : n+3<2^256) (out : Heap H)
    (ho : runCaptures (hp n hn) r .dyn (schedule n copies)=some out) :
    MObj.elems .dyn (out.get r)=finalValues n := by
  apply List.ext_getElem?
  intro k
  rw [runCaptures_read _ _ _ _ _ ho k]
  simp only [schedule,captureOrigin_append,end_origin,old_elems]
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k =>
      cases k with
      | zero => rfl
      | succ k =>
        simp only [captureOrigin,snapshotOrigin,
          show ¬(2≤k+3 ∧ k+3<2+(2-1)) from by omega,
          show ¬(1≤k+3 ∧ k+3<1+(1-0)) from by omega,if_false]
        simp only [initial,finalValues,List.getElem?_cons_succ,List.cons_append]

private abbrev Tree (n : Nat) : RefTy := .fixed (.ref B) n
private def child : SVal (.ref B) := .array (.cons (.prim true) .nil) .nil (by decide)
private def tree (n : Nat) : SVal (.ref (Tree n)) := .fixed (SVec.replicate child n)

/-- Actual source allocation yields an independently inhabited initial relation
and consumes the published MemOK theorem with structural premises discharged. -/
theorem allocated_source (n : Nat) (hn : n+3<2^256) :
    (Source.allocRef (sourceBoolMemory (initial n))).run y0=(.ok (.memRef rfl 0),sy n) ∧
    Source.MemOK E0 emptyTy (sy n) ∧ SourceBoolMemoryAt (sy n) 0 (hp n hn) r .dyn := by
  have hinit : Source.MemOK E0 emptyTy y0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have hm := source_bool_alloc_memOK (E := E0) (Γ := []) emptyTy (initial n) y0 hinit
  have hs := source_bool_alloc y0 (initial n)
  change (Source.allocRef (sourceBoolMemory (initial n))).run y0=(.ok (.memRef rfl 0),sy n) at hs
  rw [hs] at hm
  exact ⟨hs,hm.1,represented n hn⟩

/-- Actual Source reads of the composed INITIAL origin agree with real reached
intrinsic snapshots after a nonprimitive recursive copy. Complete old/copied/
final vectors, an untouched neighbor and a frozen-origin negative are retained. -/
theorem observed_copy_schedule (n copies : Nat) (hn : n+3<2^256) :
    let g := (tree (n+1)).copyStToM (hp n hn) rfl
    ∃ out : Heap g.H', runCaptures g.heap (r.wk g.ext) .dyn (schedule n copies)=some out ∧
      (tree (n+1)).Mirrors out H.length g.val ∧
      [MObj.elems .dyn ((hp n hn).get r),MObj.elems (H := g.H') .dyn (g.heap.get (r.wk g.ext)),
        MObj.elems (H := g.H') .dyn (out.get (r.wk g.ext))]=[initial n,initial n,finalValues n] ∧
      MObj.elems .dyn (out.get (neighbor.wk g.ext))=[false,true] ∧
      (Source.readLoc (E := E0) (Γ := []) F0 (τ := .bool) (.mem 0 (captureOrigin (schedule n copies) 2))).run (sy n)=
        (.ok (.bool true),sy n) ∧
      (Source.readLoc (E := E0) (Γ := []) F0 (τ := .bool) (.mem 0 1)).run (sy n)=(.ok (.bool false),sy n) ∧
      (MObj.elems .dyn (out.get (r.wk g.ext)))[2]? ≠ some false := by
  dsimp only
  obtain ⟨base,hbase⟩ := (runCaptures_success_iff (hp n hn) r .dyn (schedule n copies)).mpr (by rw [size]; exact valid n copies)
  obtain ⟨out,ho,hk,hm,hframes⟩ := copy_schedule_transport (hp n hn) base (tree (n+1)) rfl r .dyn (schedule n copies) hbase
  have hv := values n copies hn base hbase
  have he : MObj.elems .dyn (out.get (r.wk ((tree (n+1)).copyStToM (hp n hn) rfl).ext))=finalValues n := by
    rw [hk r,MObj.elems_wk,List.map_id'' (f := MVal.wk ((tree (n+1)).copyStToM (hp n hn) rfl).ext (.prim .bool)) (fun _ => rfl)]
    exact hv
  have hs := (represented n hn).copy_schedule (tree (n+1)) rfl (schedule n copies) out ho F0 2 true
  refine ⟨out,ho,hs.1,?_,?_,hs.2.mpr ?_,?_,?_⟩
  · have hc : MObj.elems .dyn (((tree (n+1)).copyStToM (hp n hn) rfl).heap.get (r.wk ((tree (n+1)).copyStToM (hp n hn) rfl).ext))=initial n := by
      rw [SVal.keeps_copyStToM (tree (n+1)) rfl (hp n hn) r,MObj.elems_wk,
        List.map_id'' (f := MVal.wk ((tree (n+1)).copyStToM (hp n hn) rfl).ext (.prim .bool)) (fun _ => rfl)]
      exact old_elems n hn
    calc
      _ = [initial n,MObj.elems (H := ((tree (n+1)).copyStToM (hp n hn) rfl).H') .dyn (((tree (n+1)).copyStToM (hp n hn) rfl).heap.get (r.wk ((tree (n+1)).copyStToM (hp n hn) rfl).ext)),MObj.elems (H := ((tree (n+1)).copyStToM (hp n hn) rfl).H') .dyn (out.get (r.wk ((tree (n+1)).copyStToM (hp n hn) rfl).ext))] := by rw [old_elems]
      _ = [initial n,initial n,MObj.elems (H := ((tree (n+1)).copyStToM (hp n hn) rfl).H') .dyn (out.get (r.wk ((tree (n+1)).copyStToM (hp n hn) rfl).ext))] := congrArg (fun xs : List Bool => [initial n,xs,MObj.elems .dyn (out.get (r.wk ((tree (n+1)).copyStToM (hp n hn) rfl).ext))]) hc
      _ = _ := congrArg (fun xs : List Bool => [initial n,initial n,xs]) he
  · rw [hk neighbor,MObj.elems_wk,List.map_id'' (f := MVal.wk ((tree (n+1)).copyStToM (hp n hn) rfl).ext (.prim .bool)) (fun _ => rfl),
      runCaptures_frame _ _ _ _ _ hbase neighbor (by decide)]
    exact neighbor_elems n hn
  · rw [he]; rfl
  · exact source_bool_read (sy n) 0 (initial n) (by simpa only [SourceBoolMemoryAt,old_elems] using represented n hn) 1 (by simp only [initial,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega)
  · rw [he]
    change (some true : Option Bool) ≠ some false
    decide
/-- Empty allocation and endpoint rejection are actual Source operations, not
Option failures re-labelled as halts. The source state is exactly retained. -/
theorem empty_source :
    let y : Source.EMState E0 [] := ((Source.allocRef (sourceBoolMemory [])).run y0).2
    (Source.allocRef (sourceBoolMemory [])).run y0=(.ok (.memRef rfl 0),y) ∧
      (Source.readLoc F0 (τ := .bool) (.mem 0 0)).run y=(.error (.revert (Source.panicData .index)),y) := by
  dsimp only
  constructor
  · exact source_bool_alloc y0 []
  · exact source_bool_bounds _ 0 [] (by rfl) 0 (by decide)

/-- Invalid type and missing object distinguish actual stuck from bounds panic.
These are negative controls, never new admitted-source restrictions. -/
theorem wrong_type_and_missing :
    (Source.readLoc (E := E0) (Γ := []) F0 (τ := .int .u256) (.mem 0 0)).run (sy 0)=
      (.error (.stuck "element type"),sy 0) ∧
    (Source.readLoc (E := E0) (Γ := []) F0 (τ := .bool) (.mem 0 0)).run y0=
      (.error (.stuck "dangling memory reference"),y0) := by
  constructor <;> rfl

theorem source_endpoint (n : Nat) (hn : n+3<2^256) :
    (Source.readLoc (E := E0) (Γ := []) F0 (τ := .bool) (.mem 0 (n+3))).run (sy n)=
      (.error (.revert (Source.panicData .index)),sy n) ∧
    (MObj.elems .dyn ((hp n hn).get r))[n+3]?=none := by
  constructor
  · exact source_bool_bounds (sy n) 0 (initial n)
      (by simpa only [SourceBoolMemoryAt,old_elems] using represented n hn) _
      (by simp only [initial,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega)
  · apply List.getElem?_eq_none
    rw [old_elems]
    simp only [initial,List.length_append,List.length_cons,List.length_nil,List.length_replicate]
    omega

/-- Element32 is a typed array observation, not a physical-byte claim. -/
theorem source_boundary32 :
    (Source.readLoc (E := E0) (Γ := []) F0 (τ := .bool) (.mem 0 32)).run (sy 33)=(.ok (.bool false),sy 33) ∧
    ∃ out : Heap ((tree 1).copyStToM (hp 33 (by decide)) rfl).H',
      runCaptures ((tree 1).copyStToM (hp 33 (by decide)) rfl).heap
        (r.wk ((tree 1).copyStToM (hp 33 (by decide)) rfl).ext) .dyn (schedule 33 4)=some out ∧
      (MObj.elems .dyn (out.get (r.wk ((tree 1).copyStToM (hp 33 (by decide)) rfl).ext)))[32]?=some false := by
  have hread : (Source.readLoc (E := E0) (Γ := []) F0 (τ := .bool) (.mem 0 32)).run (sy 33)=(.ok (.bool false),sy 33) :=
    source_bool_read (sy 33) 0 (initial 33) (by rfl) 32 (by decide)
  refine ⟨hread,?_⟩
  obtain ⟨base,hbase⟩ := (runCaptures_success_iff (hp 33 (by decide)) r .dyn (schedule 33 4)).mpr (by rw [size]; exact valid 33 4)
  obtain ⟨out,ho,hk,hm,hframes⟩ := copy_schedule_transport (hp 33 (by decide)) base (tree 1) rfl r .dyn (schedule 33 4) hbase
  have hs := (represented 33 (by decide)).copy_schedule (tree 1) rfl (schedule 33 4) out ho F0 32 false
  have hi : captureOrigin (schedule 33 4) 32=32 := by
    simp only [schedule,captureOrigin_append,end_origin]
    rfl
  rw [hi] at hs
  exact ⟨out,ho,hs.2.mp hread⟩
private theorem singleton_values (input output : Heap H) (src dst : Nat)
    (hs : src<input.len r .dyn) (hd : dst<input.len r .dyn)
    (ho : checkedCaptureOverwrite input r .dyn r .dyn src (src+1) dst=some output) :
    MObj.elems .dyn (output.get r)=(MObj.elems .dyn (input.get r)).set dst (MObj.elems .dyn (input.get r))[src] := by
  obtain ⟨hs',hd',rfl⟩ := (checkedCaptureOverwrite_some_iff input r .dyn r .dyn src (src+1) dst output).mp ho
  exact capture_singleton_elems input r .dyn src dst hs hd

/-- Both independent Source transitions execute at the ACTUAL reached state.
All intermediate/final source contents and intrinsic vectors are observed. -/
theorem source_written_copies (n : Nat) (hn : n+3<2^256) :
    ∃ (mid out : Heap H) (z₁ z₂ : Source.EMState E0 []),
      checkedCaptureOverwrite (hp n hn) r .dyn r .dyn 0 1 1=some mid ∧
      (sourceBoolCopy F0 0 0 0 1).run (sy n)=(.ok (),z₁) ∧
      checkedCaptureOverwrite mid r .dyn r .dyn 1 2 2=some out ∧
      (sourceBoolCopy F0 0 0 1 2).run z₁=(.ok (),z₂) ∧
      [MObj.elems .dyn ((hp n hn).get r),MObj.elems .dyn (mid.get r),MObj.elems .dyn (out.get r)]=
        [initial n,[true,true,false]++List.replicate n false,finalValues n] ∧
      [((sy n).2.heap.get 0),z₁.2.heap.get 0,z₂.2.heap.get 0]=
        [some ⟨.array .memory .bool none,sourceBoolMemory (initial n)⟩,
         some ⟨.array .memory .bool none,sourceBoolMemory ([true,true,false]++List.replicate n false)⟩,
         some ⟨.array .memory .bool none,sourceBoolMemory (finalValues n)⟩] ∧
      MObj.elems .dyn (mid.get neighbor)=[false,true] ∧ MObj.elems .dyn (out.get neighbor)=[false,true] ∧
      Source.MemOK E0 emptyTy z₁ ∧ Source.MemOK E0 emptyTy z₂ ∧
      (Source.readLoc (E := E0) (Γ := []) F0 (τ := .bool) (.mem 0 1)).run (sy n)=(.ok (.bool false),sy n) ∧
      (Source.readLoc (E := E0) (Γ := []) F0 (τ := .bool) (.mem 0 1)).run z₁=(.ok (.bool true),z₁) ∧
      (Source.readLoc (E := E0) (Γ := []) F0 (τ := .bool) (.mem 0 2)).run z₂=(.ok (.bool true),z₂) ∧
      (MObj.elems .dyn (out.get r))[2]?≠some false ∧ r.id=0 ∧ neighbor.id=1 := by
  have h0 := allocated_source n hn
  have hs0 : 0<(hp n hn).len r .dyn := by rw [size]; omega
  have hd1 : 1<(hp n hn).len r .dyn := by rw [size]; omega
  obtain ⟨mid,z₁,hm,hs₁,hr₁⟩ := h0.2.2.copy F0 0 0 1 hs0 hd1
  have hv₁ : MObj.elems .dyn (mid.get r)=[true,true,false]++List.replicate n false := by
    rw [singleton_values _ _ 0 1 hs0 hd1 hm]
    simp only [old_elems]
    rfl
  have hl₁ : mid.len r .dyn=n+3 := by
    simp only [Heap.len,hv₁,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega
  have hsrc : 1<mid.len r .dyn := by rw [hl₁]; omega
  have hdst : 2<mid.len r .dyn := by rw [hl₁]; omega
  obtain ⟨out,z₂,ho,hs₂,hr₂⟩ := hr₁.copy F0 0 1 2 hsrc hdst
  have hv₂ : MObj.elems .dyn (out.get r)=finalValues n := by
    rw [singleton_values _ _ 1 2 hsrc hdst ho]
    simp only [hv₁]
    rfl
  have hn₁ := checkedCaptureOverwrite_frame (hp n hn) r .dyn r .dyn 0 1 1 mid hm neighbor (by decide)
  have hn₂ := checkedCaptureOverwrite_frame mid r .dyn r .dyn 1 2 2 out ho neighbor (by decide)
  have hm₁ := h0.2.2.copy_memOK F0 0 0 1 hs0 hs₁ emptyTy h0.2.1
  have hm₂ := hr₁.copy_memOK F0 0 1 2 hsrc hs₂ emptyTy hm₁
  refine ⟨mid,out,z₁,z₂,hm,hs₁,ho,hs₂,?_,?_,?_,?_,hm₁,hm₂,?_,?_,?_,?_,rfl,rfl⟩
  · rw [old_elems,hv₁,hv₂]
  · change [_,_,_]=_
    rw [show (sy n).2.heap.get 0=some ⟨.array .memory .bool none,sourceBoolMemory (initial n)⟩ from rfl,
      show z₁.2.heap.get 0=some ⟨.array .memory .bool none,sourceBoolMemory (MObj.elems .dyn (mid.get r))⟩ from hr₁,
      show z₂.2.heap.get 0=some ⟨.array .memory .bool none,sourceBoolMemory (MObj.elems .dyn (out.get r))⟩ from hr₂,hv₁,hv₂]
  · rw [hn₁,neighbor_elems]
  · rw [hn₂,hn₁,neighbor_elems]
  · exact source_bool_read (sy n) 0 (initial n) rfl 1 (by simp only [initial,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega)
  · have he : z₁.2.heap.get 0=some ⟨.array .memory .bool none,sourceBoolMemory ([true,true,false]++List.replicate n false)⟩ := by rw [←hv₁]; exact hr₁
    exact source_bool_read z₁ 0 _ he 1 (by simp only [List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega)
  · have he : z₂.2.heap.get 0=some ⟨.array .memory .bool none,sourceBoolMemory (finalValues n)⟩ := by rw [←hv₂]; exact hr₂
    exact source_bool_read z₂ 0 _ he 2 (by simp only [finalValues,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega)
  · rw [hv₂]
    change (some true : Option Bool)≠some false
    decide

/-- Independent first-read and reached-write endpoint failures, plus the
successful read which precedes the bad write. -/
theorem source_copy_failures (n : Nat) (hn : n+3<2^256) :
    (sourceBoolCopy F0 0 0 (n+3) 0).run (sy n)=(.error (.revert (Source.panicData .index)),sy n) ∧
      checkedCaptureOverwrite (hp n hn) r .dyn r .dyn (n+3) (n+4) 0=none ∧
    (Source.readLoc (E := E0) (Γ := []) F0 (τ := .bool) (.mem 0 0)).run (sy n)=(.ok (.bool true),sy n) ∧
    (sourceBoolCopy F0 0 0 0 (n+3)).run (sy n)=(.error (.revert (Source.panicData .index)),sy n) ∧
      checkedCaptureOverwrite (hp n hn) r .dyn r .dyn 0 1 (n+3)=none := by
  have h := represented n hn
  have h₁ := h.copy_bounds F0 0 (n+3) 0 (Or.inl (by rw [size]; exact Nat.le_refl _))
  have h₂ := h.copy_bounds F0 0 0 (n+3) (Or.inr (by rw [size]; exact Nat.le_refl _))
  refine ⟨h₁.1,h₁.2,?_,h₂.1,h₂.2⟩
  exact source_bool_read (sy n) 0 (initial n) rfl 0 (by simp only [initial,List.length_append,List.length_cons,List.length_nil,List.length_replicate]; omega)

theorem source_write_boundary32 :
    ∃ (out : Heap H) (z : Source.EMState E0 []),
      checkedCaptureOverwrite (hp 33 (by decide)) r .dyn r .dyn 0 1 32=some out ∧
      (sourceBoolCopy F0 0 0 0 32).run (sy 33)=(.ok (),z) ∧
      (Source.readLoc (E := E0) (Γ := []) F0 (τ := .bool) (.mem 0 32)).run (sy 33)=(.ok (.bool false),sy 33) ∧
      (Source.readLoc (E := E0) (Γ := []) F0 (τ := .bool) (.mem 0 32)).run z=(.ok (.bool true),z) ∧
      (MObj.elems .dyn (out.get r))[32]?=some true ∧ MObj.elems .dyn (out.get neighbor)=[false,true] := by
  have hs : 0<(hp 33 (by decide)).len r .dyn := by rw [size]; decide
  have hd : 32<(hp 33 (by decide)).len r .dyn := by rw [size]; decide
  obtain ⟨out,z,ho,hz,hr⟩ := (represented 33 (by decide)).copy F0 0 0 32 hs hd
  have he := singleton_values _ _ 0 32 hs hd ho
  have hv : (MObj.elems .dyn (out.get r))[32]?=some true := by
    rw [he,List.getElem?_set_self hd]
    simp only [old_elems]
    rfl
  refine ⟨out,z,ho,hz,?_,?_,hv,?_⟩
  · exact source_bool_read (sy 33) 0 (initial 33) rfl 32 (by decide)
  · have hh := hr.read_iff F0 (uintOfNat 32) true
    have hu : (uintOfNat 32).1.toNat=32 := by rw [uintOfNat_val (by decide)]; rfl
    apply hh.mpr
    change (MObj.elems .dyn (out.get r))[(uintOfNat 32).1.toNat]?=some true
    rw [hu]; exact hv
  · rw [checkedCaptureOverwrite_frame _ _ _ _ _ _ _ _ _ ho neighbor (by decide),neighbor_elems]

/-- info: 'Solidity.Backend.MemoryOps.SourceMemoryControls.source_written_copies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_written_copies
/-- info: 'Solidity.Backend.MemoryOps.SourceMemoryControls.source_copy_failures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_copy_failures
/-- info: 'Solidity.Backend.MemoryOps.SourceMemoryControls.source_write_boundary32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_write_boundary32

/-- info: 'Solidity.Backend.MemoryOps.SourceMemoryControls.allocated_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms allocated_source
/-- info: 'Solidity.Backend.MemoryOps.SourceMemoryControls.observed_copy_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms observed_copy_schedule
/-- info: 'Solidity.Backend.MemoryOps.SourceMemoryControls.empty_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms empty_source
/-- info: 'Solidity.Backend.MemoryOps.SourceMemoryControls.wrong_type_and_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms wrong_type_and_missing
/-- info: 'Solidity.Backend.MemoryOps.SourceMemoryControls.source_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_endpoint
/-- info: 'Solidity.Backend.MemoryOps.SourceMemoryControls.source_boundary32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms source_boundary32
end Solidity.Backend.MemoryOps.SourceMemoryControls
