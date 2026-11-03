import Solidity.Backend.MemoryOps.SourceCalldataSlice
import Solidity.Backend.MemoryOps.SourceCalldataUintTransfer
import Solidity.Source.SemanticsExamples

/-! Populated actual Source slice/copy clients, for either pipeline. These
execute no target bytecode and do not assert ABI entry admission. -/
namespace Solidity.Backend.MemoryOps.UintSliceControls
open Source.SemanticsExamples (E0 F0 G0 s0)
private abbrev A : RefTy := .array (.prim .uint)
private abbrev H : HTy := [A,A]
private abbrev SU := Source.STy.array .memory (.int .u256) none
private abbrev CD := Source.STy.array .calldata (.int .u256) none
private abbrev Γ : Source.RCtx := [CD,.int .u256,.int .u256,SU,SU,SU]
private def u (n : Nat) : PrimTy.uint.Denote := Evm.Memory.indexValue (Evm.wmod n)
private def maximum : PrimTy.uint.Denote := Evm.Memory.indexValue Evm.wMax
private def old := [u 7,u 0,maximum]
private def neighbor := [u 8,u 9]
private def payload := [u 0,maximum]
private def hp : Heap H := (⟨old,by decide⟩,⟨neighbor,by decide⟩,())
private def left : HRef H A := ⟨0,rfl⟩
private def right : HRef H A := ⟨1,rfl⟩
private def y0 : Source.EMState E0 [] := (.nil,s0)
private def y1 : Source.EMState E0 [] := ((Source.allocRef (sourceUintMemory old)).run y0).2
private def y2 : Source.EMState E0 [] := ((Source.allocRef (sourceUintMemory neighbor)).run y1).2
private def sy (s e : Nat) : Source.EMState E0 Γ :=
  (.cons (.cdRef rfl 0 3) (.cons (sourceUint (u s)) (.cons (sourceUint (u e))
    (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil))))),y2.2)
private abbrev SH := (Source.Heap.empty (D := E0.layout)).ty
private def frame : Source.Fr := {F0 with cd :=
  (List.replicate 31 0++[2])++List.replicate 32 0++List.replicate 32 255}
private def decoded : List (Source.Val E0.layout (.int .u256)) :=
  [sourceUint (u 0),sourceUint maximum]
private def out : Heap (H++[A]) := (hp.alloc (R := A) (⟨payload,by decide⟩ : MObj H A)).1
private def fresh : HRef (H++[A]) A := (hp.alloc (R := A) (⟨payload,by decide⟩ : MObj H A)).2
private def z (s e : Nat) : Source.EMState E0 Γ :=
  ((sy s e).1,{(sy s e).2 with heap := ((sy s e).2.heap.alloc ⟨SU,sourceUintMemory payload⟩).1})
private theorem actual_decode : sourceCalldataUintValues E0 frame 32 2=.ok decoded := by rfl
private theorem old_at (s e : Nat) : SourceUintMemoryAt (sy s e) 0 hp left .dyn := by
  unfold SourceUintMemoryAt
  change (sy s e).2.heap.get 0=some ⟨SU,sourceUintMemory (MObj.elems .dyn (⟨old,by decide⟩ : MObj H A))⟩
  rw [MObj.elems_dyn]
  rfl
private theorem neighbor_at (s e : Nat) : SourceUintMemoryAt (sy s e) 1 hp right .dyn := by
  unfold SourceUintMemoryAt
  change (sy s e).2.heap.get 1=some ⟨SU,sourceUintMemory (MObj.elems .dyn (⟨neighbor,by decide⟩ : MObj H A))⟩
  rw [MObj.elems_dyn]
  rfl
private theorem memOK (s e : Nat) : Source.MemOK E0 SH (sy s e) := by
  have h0 : Source.MemOK E0 SH y0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have h1 := source_uint_alloc_memOK (E := E0) (Γ := []) SH old y0 h0
  change Source.MemOK E0 SH y1 ∧ _ at h1
  have h2 := source_uint_alloc_memOK (E := E0) (Γ := []) SH neighbor y1 h1.1
  change Source.MemOK E0 SH y2 ∧ _ at h2
  exact ⟨⟨h2.1.1.1,⟨trivial,⟨trivial,⟨trivial,⟨⟨SU,rfl,rfl⟩,⟨⟨SU,rfl,rfl⟩,⟨⟨SU,rfl,rfl⟩,trivial⟩⟩⟩⟩⟩⟩⟩,h2.1.2⟩

/-- The slice changes the actual offset before decoding; the existing checked
transfer and native allocation produce the same new payload. -/
theorem slice_copy_client (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) frame (fuel+2)
      (.slice (.local (.here : Source.Idx Γ CD)) (by decide)
        (.local (.there .here)) rfl (.local (.there (.there .here))) rfl false)).run (sy 1 3)=
      (.ok (.val (.cdRef rfl 32 2)),sy 1 3) ∧
    (Source.evalE (G0 p) frame (fuel+3)
      (sourceUintSliceCopy .here (.there .here) (.there (.there .here)) false)).run (sy 1 3)=
      (.ok (.val (.memRef rfl 2)),z 1 3) ∧
    checkedSourceFreshUints (E := E0) frame 32 2 hp (by decide)=.ok (some out) ∧
    Heap.Keeps (List.prefix_append H [A]) hp out ∧
    SourceUintMemoryAt (z 1 3) 2 out fresh .dyn ∧ Source.MemOK E0 SH (z 1 3) ∧
    SourceUintMemoryAt (z 1 3) 0 out (left.wk (List.prefix_append H [A])) .dyn ∧
    SourceUintMemoryAt (z 1 3) 1 out (right.wk (List.prefix_append H [A])) .dyn := by
  have copied := source_cd_uint_copy (sy 1 3) hp id frame 32 2 (by decide) SH (memOK 1 3)
  rw [actual_decode] at copied
  obtain ⟨valid,run,keeps,new,mok,identity,sourceIdentity,oldMap,separate,preserved,aliases,loc,ex,ev,logs,fn⟩ := copied
  obtain ⟨valid',checked,native⟩ := checkedSourceFreshUints_some frame 32 2 hp (by decide) decoded actual_decode
  refine ⟨?_,?_,native,keeps,new,mok,aliases A left .dyn (old_at 1 3),aliases A right .dyn (neighbor_at 1 3)⟩
  · rw [source_uint_slice_eval (G0 p) frame fuel (sy 1 3) .here (.there .here)
      (.there (.there .here)) 0 3 (u 1) (u 3) false rfl rfl rfl]
    rfl
  · rw [source_uint_slice_copy_window (G0 p) frame fuel (sy 1 3) .here (.there .here)
      (.there (.there .here)) 0 3 (u 1) (u 3) false rfl rfl rfl (by decide) (by decide)]
    exact run

/-- Complete ordered object tables, operand/alias locals, native objects and
all Source world fields at the initial, slice boundary and copy result. -/
theorem complete_vectors :
    [(sy 1 3).2.heap.get 0,(sy 1 3).2.heap.get 1,(sy 1 3).2.heap.get 2,(sy 1 3).2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,none,none] ∧
    [(z 1 3).2.heap.get 0,(z 1 3).2.heap.get 1,(z 1 3).2.heap.get 2,(z 1 3).2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory payload⟩,none] ∧
    (z 1 3).1=(sy 1 3).1 ∧ (sy 1 3).1=
      .cons (.cdRef rfl 0 3) (.cons (sourceUint (u 1)) (.cons (sourceUint (u 3))
        (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil))))) ∧
    [MObj.elems .dyn (out.get (left.wk (List.prefix_append H [A]))),
      MObj.elems .dyn (out.get (right.wk (List.prefix_append H [A]))),MObj.elems .dyn (out.get fresh)]=
      [old,neighbor,payload] ∧
    [left.id,right.id,fresh.id]=[0,1,2] ∧ (sy 1 3).2.heap.next=2 ∧ (z 1 3).2.heap.next=3 ∧
    (z 1 3).2.ex=(sy 1 3).2.ex ∧ (z 1 3).2.events=(sy 1 3).2.events ∧
    (z 1 3).2.logs=(sy 1 3).2.logs ∧ (z 1 3).2.fnLocals=(sy 1 3).2.fnLocals := by
  refine ⟨rfl,rfl,rfl,rfl,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  unfold out fresh
  rw [(hp.keeps_alloc (R := A) (⟨payload,by decide⟩ : MObj H A)) left,
    (hp.keeps_alloc (R := A) (⟨payload,by decide⟩ : MObj H A)) right,Heap.get_alloc,MObj.elems_wk,MObj.elems_wk,MObj.elems_wk]
  simp only [MObj.elems_dyn,List.map_id'' (f := MVal.wk (List.prefix_append H [A]) (.prim .uint)) (fun _ => rfl)]
  rfl

/-- Empty exact-end slices allocate an actual empty object; omitted end uses
len even when the supplied finish local is zero. Rejected slices allocate none. -/
theorem endpoints (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) frame (fuel+3)
      (sourceUintSliceCopy .here (.there .here) (.there (.there .here)) false)).run (sy 3 3)=
      (.ok (.val (.memRef rfl 2)),((sy 3 3).1,{(sy 3 3).2 with heap :=
        ((sy 3 3).2.heap.alloc ⟨SU,sourceUintMemory []⟩).1})) ∧
    (Source.evalE (G0 p) frame (fuel+3)
      (sourceUintSliceCopy .here (.there .here) (.there (.there .here)) true)).run (sy 1 0)=
      (.ok (.val (.memRef rfl 2)),z 1 0) ∧
    (Source.evalE (G0 p) frame (fuel+3)
      (sourceUintSliceCopy .here (.there .here) (.there (.there .here)) false)).run (sy 2 1)=
      (.error (.revert []),sy 2 1) ∧
    (Source.evalE (G0 p) frame (fuel+3)
      (sourceUintSliceCopy .here (.there .here) (.there (.there .here)) false)).run (sy 1 4)=
      (.error (.revert []),sy 1 4) := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [source_uint_slice_copy_eval (G0 p) frame fuel (sy 3 3) .here (.there .here)
      (.there (.there .here)) 0 3 (u 3) (u 3) false rfl rfl rfl]
    rfl
  · rw [source_uint_slice_copy_eval (G0 p) frame fuel (sy 1 0) .here (.there .here)
      (.there (.there .here)) 0 3 (u 1) (u 0) true rfl rfl rfl]
    rfl
  · rw [source_uint_slice_copy_eval (G0 p) frame fuel (sy 2 1) .here (.there .here)
      (.there (.there .here)) 0 3 (u 2) (u 1) false rfl rfl rfl]
    rfl
  · rw [source_uint_slice_copy_eval (G0 p) frame fuel (sy 1 4) .here (.there .here)
      (.there (.there .here)) 0 3 (u 1) (u 4) false rfl rfl rfl]
    rfl

/-- Real reads distinguish the shifted decoded object from the stale unsliced
payload and retained old aliases. A short horizon exposes no allocation suffix. -/
theorem stale_window_and_timeout (p : Roadmap.Pipeline) :
    sourceCalldataUintValues E0 frame 0 3=.ok
      [sourceUint (u 2),sourceUint (u 0),sourceUint maximum] ∧
    sourceCalldataUintValues E0 frame 32 2=.ok decoded ∧
    (Source.memElem (E := E0) (Γ := Γ) 2 0 (.int .u256)).run (z 1 3)=
      (.ok (sourceUint (u 0)),z 1 3) ∧
    (Source.memElem (E := E0) (Γ := Γ) 0 0 (.int .u256)).run (z 1 3)=
      (.ok (sourceUint (u 7)),z 1 3) ∧
    (Source.memElem (E := E0) (Γ := Γ) 2 1 (.int .u256)).run (z 1 3)=
      (.ok (sourceUint maximum),z 1 3) ∧
    (Source.evalE (G0 p) frame 2
      (sourceUintSliceCopy .here (.there .here) (.there (.there .here)) false)).run (sy 1 3)=
      (.error .timeout,sy 1 3) := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  cases p <;> rfl

/-- Statement execution discards only the expression result; the actual fresh
allocation remains. Original parameter count is retained, not replaced by Γ. -/
theorem slice_copy_statement (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.execS (G0 p) frame (fuel+4) nps none
      (.expr (sourceUintSliceCopy .here (.there .here) (.there (.there .here)) false) :
        Source.RStmt E0 [] false .body Γ Γ) (sy 1 3).1).run (.nil,(sy 1 3).2)=
        (.ok (.normal (z 1 3).1),(.nil,(z 1 3).2)) := by
  exact source_expr_statement_run (G0 p) frame (fuel+3) nps _ (sy 1 3) (z 1 3)
    (.val (.memRef rfl 2)) (slice_copy_client p fuel).2.1

/-- info: 'Solidity.Backend.MemoryOps.UintSliceControls.slice_copy_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slice_copy_client
/-- info: 'Solidity.Backend.MemoryOps.UintSliceControls.complete_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms complete_vectors
/-- info: 'Solidity.Backend.MemoryOps.UintSliceControls.endpoints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms endpoints
/-- info: 'Solidity.Backend.MemoryOps.UintSliceControls.stale_window_and_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stale_window_and_timeout
/-- info: 'Solidity.Backend.MemoryOps.UintSliceControls.slice_copy_statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slice_copy_statement
end Solidity.Backend.MemoryOps.UintSliceControls
