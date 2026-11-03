import Solidity.Backend.MemoryOps.SourceCalldataUintCopy
import Solidity.Source.SemanticsExamples
import Solidity.Evm.Memory

/-! Actual populated uint Source/intrinsic copy clients. No target copy code,
ABI admission or external compiler/EVM execution is claimed. -/
namespace Solidity.Backend.MemoryOps.UintCopyControls
open Source.SemanticsExamples (E0 F0 G0 s0)
private abbrev A : RefTy := .array (.prim .uint)
private abbrev H : HTy := [A,A]
private abbrev SU := Source.STy.array .memory (.int .u256) none
private abbrev CD := Source.STy.array .calldata (.int .u256) none
private abbrev Γ : Source.RCtx := [CD,SU,SU,SU]
private def u (n : Nat) : PrimTy.uint.Denote := Evm.Memory.indexValue (Evm.wmod n)
private def maximum : PrimTy.uint.Denote := Evm.Memory.indexValue Evm.wMax
private def old : List PrimTy.uint.Denote := [u 7,u 0,maximum]
private def neighbor : List PrimTy.uint.Denote := [u 8,u 9]
private def payload : List PrimTy.uint.Denote := [u 2,u 0,maximum]
private def hp : Heap H := (⟨old,by decide⟩,⟨neighbor,by decide⟩,())
private def left : HRef H A := ⟨0,rfl⟩
private def right : HRef H A := ⟨1,rfl⟩
private def y0 : Source.EMState E0 [] := (.nil,s0)
private def y1 : Source.EMState E0 [] := ((Source.allocRef (sourceUintMemory old)).run y0).2
private def y2 : Source.EMState E0 [] := ((Source.allocRef (sourceUintMemory neighbor)).run y1).2
private def sy (off len : Nat) : Source.EMState E0 Γ :=
  (.cons (.cdRef rfl off len) (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil))),y2.2)
private abbrev SH := (Source.Heap.empty (D := E0.layout)).ty
private def frame : Source.Fr := {F0 with cd :=
  (List.replicate 31 0++[2])++List.replicate 32 0++List.replicate 32 255}
private def decoded : List (Source.Val E0.layout (.int .u256)) :=
  [sourceUint (u 2),sourceUint (u 0),sourceUint maximum]
private def out : Heap (H++[A]) := (hp.alloc (R := A) (⟨payload,by decide⟩ : MObj H A)).1
private def fresh : HRef (H++[A]) A := (hp.alloc (R := A) (⟨payload,by decide⟩ : MObj H A)).2
private def z : Source.EMState E0 Γ :=
  ((sy 0 3).1,{(sy 0 3).2 with heap := ((sy 0 3).2.heap.alloc ⟨SU,sourceUintMemory payload⟩).1})
private theorem actually_decoded : sourceCalldataUintValues E0 frame 0 3=.ok decoded := by
  rfl
private theorem old_at (off len : Nat) : SourceUintMemoryAt (sy off len) 0 hp left .dyn := by
  unfold SourceUintMemoryAt
  change (sy off len).2.heap.get 0=some ⟨SU,sourceUintMemory (MObj.elems .dyn (⟨old,by decide⟩ : MObj H A))⟩
  rw [MObj.elems_dyn]
  rfl
private theorem neighbor_at (off len : Nat) : SourceUintMemoryAt (sy off len) 1 hp right .dyn := by
  unfold SourceUintMemoryAt
  change (sy off len).2.heap.get 1=some ⟨SU,sourceUintMemory (MObj.elems .dyn (⟨neighbor,by decide⟩ : MObj H A))⟩
  rw [MObj.elems_dyn]
  rfl
private theorem memOK (off len : Nat) : Source.MemOK E0 SH (sy off len) := by
  have h0 : Source.MemOK E0 SH y0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have h1 := source_uint_alloc_memOK (E := E0) (Γ := []) SH old y0 h0
  change Source.MemOK E0 SH y1 ∧ _ at h1
  have h2 := source_uint_alloc_memOK (E := E0) (Γ := []) SH neighbor y1 h1.1
  change Source.MemOK E0 SH y2 ∧ _ at h2
  exact ⟨⟨h2.1.1.1,⟨trivial,⟨⟨SU,rfl,rfl⟩,⟨⟨SU,rfl,rfl⟩,⟨⟨SU,rfl,rfl⟩,trivial⟩⟩⟩⟩⟩,h2.1.2⟩

/-- Both pipelines execute real resolved conversion, reaching a new identity;
all old aliases and neighbor observations follow from the generic copy law. -/
theorem copy_client (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) frame (fuel+2) (sourceUintCalldataCopy (E := E0) (Γ := Γ) .here)).run (sy 0 3)=
      (.ok (.val (.memRef rfl 2)),z) ∧
    Heap.Keeps (List.prefix_append H [A]) hp out ∧
    SourceUintMemoryAt z 2 out fresh .dyn ∧ Source.MemOK E0 SH z ∧
    SourceUintMemoryAt z 0 out (left.wk (List.prefix_append H [A])) .dyn ∧
    SourceUintMemoryAt z 1 out (right.wk (List.prefix_append H [A])) .dyn ∧
    fresh.id=2 ∧ left.id≠fresh.id ∧ right.id≠fresh.id := by
  have result := source_cd_uint_copy (sy 0 3) hp id frame 0 3 (by decide) SH (memOK 0 3)
  rw [actually_decoded] at result
  obtain ⟨valid,run,keeps,new,mok,identity,sourceIdentity,oldMap,separate,preserved,aliases,loc,ex,ev,logs,fn⟩ := result
  have oldFrame := aliases A left .dyn (old_at 0 3)
  have neighborFrame := aliases A right .dyn (neighbor_at 0 3)
  refine ⟨?_,keeps,new,mok,oldFrame,neighborFrame,rfl,by decide,by decide⟩
  rw [source_cd_uint_eval (G0 p) frame fuel (sy 0 3) .here 0 3 rfl,source_cd_uint_run,actually_decoded]
  rfl

/-- Complete ordered Source tables, locals, typed contents and world frames at
initial/final states. No Source local is rebound merely by evaluating the RHS. -/
theorem complete_vectors :
    [(sy 0 3).2.heap.get 0,(sy 0 3).2.heap.get 1,(sy 0 3).2.heap.get 2,(sy 0 3).2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,none,none] ∧
    [z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2,z.2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory payload⟩,none] ∧
    z.1=(sy 0 3).1 ∧ (sy 0 3).1=
      .cons (.cdRef rfl 0 3) (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil))) ∧
    [MObj.elems .dyn (out.get (left.wk (List.prefix_append H [A]))),
      MObj.elems .dyn (out.get (right.wk (List.prefix_append H [A]))),MObj.elems .dyn (out.get fresh)]=
      [old,neighbor,payload] ∧
    (sy 0 3).2.heap.next=2 ∧ z.2.heap.next=3 ∧
    z.2.ex=(sy 0 3).2.ex ∧ z.2.events=(sy 0 3).2.events ∧ z.2.logs=(sy 0 3).2.logs ∧ z.2.fnLocals=(sy 0 3).2.fnLocals := by
  refine ⟨rfl,rfl,rfl,rfl,?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
  unfold out fresh
  rw [(hp.keeps_alloc (R := A) (⟨payload,by decide⟩ : MObj H A)) left,
    (hp.keeps_alloc (R := A) (⟨payload,by decide⟩ : MObj H A)) right,Heap.get_alloc,MObj.elems_wk,MObj.elems_wk,MObj.elems_wk]
  simp only [MObj.elems_dyn,List.map_id'' (f := MVal.wk (List.prefix_append H [A]) (.prim .uint)) (fun _ => rfl)]
  rfl

/-- Actual reached reads discriminate a stale old root and an accidental Bool
conversion: numeric2 is valid here while the Bool decoder rejects it. -/
theorem reached_read_negatives (p : Roadmap.Pipeline) :
    (Source.memElem (E := E0) (Γ := Γ) 2 0 (.int .u256)).run z=(.ok (sourceUint (u 2)),z) ∧
    (Source.memElem (E := E0) (Γ := Γ) 0 0 (.int .u256)).run z=(.ok (sourceUint (u 7)),z) ∧
    (Source.memElem (E := E0) (Γ := Γ) 2 2 (.int .u256)).run z=(.ok (sourceUint maximum),z) ∧
    sourceCalldataBoolValues E0 frame 0 3=.error (.revert []) ∧
    (Source.evalE (G0 p) frame 1 (sourceUintCalldataCopy (E := E0) (Γ := Γ) .here)).run (sy 0 3)=
      (.error .timeout,sy 0 3) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Empty copy allocates a literal empty uint object; positive reads of an
empty raw frame are zero padded. Neither establishes ABI bounds admission. -/
theorem empty_and_boundary (n off : Nat) :
    sourceCalldataUintValues E0 {F0 with cd := []} off n=
      .ok (List.replicate n (sourceUint (u 0))) ∧
    (Source.cdToMem frame SU 96 0).run (sy 96 0)=
      (.ok (.val (.memRef rfl 2)),((sy 96 0).1,{(sy 96 0).2 with heap :=
        ((sy 96 0).2.heap.alloc ⟨SU,sourceUintMemory []⟩).1})) ∧
    (Source.cdToMem frame (.array .memory (.int .u256) (some 3)) 0 3).run (sy 0 3)=
      (.error (.stuck "calldata conversion"),sy 0 3) := by
  refine ⟨sourceCalldataUintValues_empty _ rfl off n,?_,source_cd_uint_fixed_stuck frame 0 3 3 (sy 0 3)⟩
  rw [source_cd_uint_run]
  rfl

/-- A real zero-padded33-element Source copy supports last element32 and
rejects endpoint33. The intrinsic endpoint is None, not a Source panic object. -/
theorem element32_endpoint :
    let xs := List.replicate 33 (u 0)
    let q : Source.EMState E0 Γ :=
      ((sy 0 33).1,{(sy 0 33).2 with heap := ((sy 0 33).2.heap.alloc ⟨SU,sourceUintMemory xs⟩).1})
    (Source.cdToMem {F0 with cd := []} SU 0 33).run (sy 0 33)=(.ok (.val (.memRef rfl 2)),q) ∧
    (Source.memElem (E := E0) (Γ := Γ) 2 32 (.int .u256)).run q=(.ok (sourceUint (u 0)),q) ∧
    (Source.memElem (E := E0) (Γ := Γ) 2 33 (.int .u256)).run q=
      (.error (.revert (Source.panicData .index)),q) ∧
    let t := hp.alloc (R := A) (⟨xs,by decide⟩ : MObj H A)
    t.1.index t.2 .dyn (u 33)=none := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · rw [source_cd_uint_run,sourceCalldataUintValues_empty _ rfl]
    simp only [sourceUintValuePayload,List.map_replicate,calldataUint_sourceUint]
    rfl
  · exact source_uint_read _ 2 (List.replicate 33 (u 0)) (by rfl) 32 (by decide)
  · exact source_uint_bounds _ 2 (List.replicate 33 (u 0)) (by rfl) 33 (by decide)
  · change (MObj.elems .dyn _)[33]?=none
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
    rfl

/-- Discarding the result really executes the Source expression statement at
its declared next horizon, with the original parameter count left arbitrary. -/
theorem copy_statement (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.execS (G0 p) frame (fuel+3) nps none
      (.expr (sourceUintCalldataCopy .here) : Source.RStmt E0 [] false .body Γ Γ)
      (sy 0 3).1).run (.nil,(sy 0 3).2)=(.ok (.normal z.1),(.nil,z.2)) := by
  exact source_expr_statement_run (G0 p) frame (fuel+2) nps _ (sy 0 3) z
    (.val (.memRef rfl 2)) (copy_client p fuel).1

/-- Direct application of the main paired copy law at arbitrary runtime zero
count, including0 and33; no separate desired boundary correspondence premise. -/
theorem paired_zero_runtime (off n : Nat) (capacity : n<2^256) :
    ∃ valid : (List.replicate n (u 0)).length<2^256,
    let o : MObj H A := ⟨List.replicate n (u 0),valid⟩
    let t := hp.alloc o
    let q : Source.EMState E0 Γ :=
      ((sy off n).1,{(sy off n).2 with heap := ((sy off n).2.heap.alloc ⟨SU,sourceUintMemory (List.replicate n (u 0))⟩).1})
    (Source.cdToMem {F0 with cd := []} SU off n).run (sy off n)=(.ok (.val (.memRef rfl 2)),q) ∧
    Heap.Keeps (List.prefix_append H [A]) hp t.1 ∧
    SourceUintMemoryAt q 2 t.1 t.2 .dyn ∧ Source.MemOK E0 SH q := by
  have result := source_cd_uint_copy (sy off n) hp id {F0 with cd := []} off n capacity SH (memOK off n)
  rw [sourceCalldataUintValues_empty _ rfl] at result
  simp only [sourceUintValuePayload,List.map_replicate,calldataUint_sourceUint] at result
  obtain ⟨valid,run,keep,new,mok,rest⟩ := result
  exact ⟨valid,run,keep,new,mok⟩

/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.copy_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copy_client
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.complete_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms complete_vectors
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.reached_read_negatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms reached_read_negatives
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.empty_and_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_and_boundary
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.element32_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms element32_endpoint
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.copy_statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms copy_statement
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.paired_zero_runtime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms paired_zero_runtime
end Solidity.Backend.MemoryOps.UintCopyControls
