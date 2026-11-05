import Solidity.Backend.MemoryOps.SourceGuardedUintDelete
import Solidity.Backend.MemoryOps.SourceRawUintDelete
import Solidity.Backend.MemoryOps.SourceCalldataMixedCopy
import Solidity.Backend.MemoryOps.SourceCalldataUintDelete
import Solidity.Backend.MemoryOps.SourceCalldataUintMutation
import Solidity.Backend.MemoryOps.SourceCalldataUintBinding
import Solidity.Backend.MemoryOps.SourceCalldataUintTransfer
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

/-! Additional actual checked-transfer agreement clients. -/
private def zeros : MObj H A := ⟨[u 0,u 0,u 0],by decide⟩
private def zeroPair := hp.alloc (R := A) zeros

/-- Both actual Source executions and actual decoded-table transfer reach the
same computed intrinsic heap, rather than independently supplied successes. -/
theorem checked_copy_client (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G0 p) frame (fuel+2) (sourceUintCalldataCopy (E := E0) (Γ := Γ) .here)).run (sy 0 3)=
      (.ok (.val (.memRef rfl 2)),z) ∧
    (Source.execS (G0 p) frame (fuel+3) nps none
      (.expr (sourceUintCalldataCopy .here) : Source.RStmt E0 [] false .body Γ Γ)
      (sy 0 3).1).run (.nil,(sy 0 3).2)=(.ok (.normal z.1),(.nil,z.2)) ∧
    checkedCalldataUints (sourceUintTable frame 0 decoded) 0 zeroPair.1 zeroPair.2 .dyn 0 3 0=some out ∧
    checkedSourceFreshUints (E := E0) frame 0 3 hp (by decide)=.ok (some out) ∧
    Heap.Keeps (List.prefix_append H [A]) hp out ∧
    SourceUintMemoryAt z 2 out fresh .dyn ∧ Source.MemOK E0 SH z := by
  have result := source_cd_uint_checked_copy (sy 0 3) hp id frame 0 3 (by decide) SH (memOK 0 3)
  rw [actually_decoded] at result
  obtain ⟨valid,direct,wrapped,run,keep,new,mok,old,loc,ex,events,logs,fn⟩ := result
  have expression : (Source.evalE (G0 p) frame (fuel+2)
      (sourceUintCalldataCopy (E := E0) (Γ := Γ) .here)).run (sy 0 3)=(.ok (.val (.memRef rfl 2)),z) := by
    rw [source_cd_uint_eval (G0 p) frame fuel (sy 0 3) .here 0 3 rfl]
    exact run
  exact ⟨expression,source_expr_statement_run (G0 p) frame (fuel+2) nps _ (sy 0 3) z
    (.val (.memRef rfl 2)) expression,direct,wrapped,keep,new,mok⟩

/-- All old/zero-stage/final contents and IDs, actual immutable input, payload
and absent unrelated table key are retained as ordered observations. -/
theorem checked_stage_vectors :
    [MObj.elems .dyn (hp.get left),MObj.elems .dyn (hp.get right)]=[old,neighbor] ∧
    [MObj.elems .dyn (zeroPair.1.get (left.wk (List.prefix_append H [A]))),
      MObj.elems .dyn (zeroPair.1.get (right.wk (List.prefix_append H [A]))),
      MObj.elems .dyn (zeroPair.1.get zeroPair.2)]=[old,neighbor,[u 0,u 0,u 0]] ∧
    [MObj.elems .dyn (out.get (left.wk (List.prefix_append H [A]))),
      MObj.elems .dyn (out.get (right.wk (List.prefix_append H [A]))),MObj.elems .dyn (out.get fresh)]=
      [old,neighbor,payload] ∧
    [left.id,right.id,zeroPair.2.id,fresh.id]=[0,1,2,2] ∧
    (sourceUintTable frame 0 decoded).input=frame.cd ∧
    calldataUints (sourceUintTable frame 0 decoded) 0=some payload ∧
    (sourceUintTable frame 0 decoded).objects 1=none := by
  refine ⟨?_,?_,complete_vectors.2.2.2.2.1,rfl,rfl,?_,sourceUintTable_other frame 0 1 decoded (by decide)⟩
  · simp only [MObj.elems_dyn]
    rfl
  · unfold zeroPair
    rw [(hp.keeps_alloc (R := A) zeros) left,(hp.keeps_alloc (R := A) zeros) right,
      Heap.get_alloc,MObj.elems_wk,MObj.elems_wk,MObj.elems_wk]
    simp only [MObj.elems_dyn,List.map_id'' (f := MVal.wk (List.prefix_append H [A]) (.prim .uint)) (fun _ => rfl)]
    rfl
  · rw [sourceUintTable_payload]
    rfl

/-- Omitting the write retains zeros, while the real checked operation changes
both value2 and the high word. Capacity rejection remains Except.ok None. -/
theorem checked_rejection_and_omission :
    zeroPair.1≠out ∧
    checkedSourceFreshUints (E := E0) frame 0 3 hp (by decide)≠.ok (some zeroPair.1) ∧
    checkedSourceUints (E := E0) frame 0 3 hp left .dyn 1=.ok none ∧
    checkedSourceUints (E := E0) frame 0 3 hp right .dyn 0=.ok none := by
  have zeroRead : zeroPair.1.index fresh .dyn (u 0)=some (u 0) := by
    change (MObj.elems .dyn _)[0]?=some (u 0)
    rw [MObj.elems_dyn]
    rfl
  have newRead : out.index fresh .dyn (u 0)=some (u 2) := by
    change (MObj.elems .dyn _)[0]?=some (u 2)
    rw [MObj.elems_dyn]
    rfl
  have moved : zeroPair.1≠out := by
    intro same
    have observed := congrArg (fun h : Heap (H++[A]) => h.index fresh .dyn (u 0)) same
    dsimp only at observed
    rw [zeroRead,newRead] at observed
    exact (by decide : u 0≠u 2) (Option.some.inj observed)
  refine ⟨moved,?_,?_,?_⟩
  · intro same
    rw [(checked_copy_client .legacy 0 0).2.2.2.1] at same
    exact moved (Option.some.inj (Except.ok.inj same)).symm
  · apply (checkedSourceUints_none_iff frame 0 3 hp left .dyn 1 decoded actually_decoded).mpr
    simp only [Heap.len,MObj.elems_dyn]
    decide
  · apply (checkedSourceUints_none_iff frame 0 3 hp right .dyn 0 decoded actually_decoded).mpr
    simp only [Heap.len,MObj.elems_dyn]
    decide

/-- The actual combined copy/checked law also applies at every valid runtime
zero-padding count, including the literal empty and element32 witnesses. -/
theorem checked_zero_runtime (off n : Nat) (capacity : n<2^256) :
    ∃ valid : (List.replicate n (u 0)).length<2^256,
    let t := hp.alloc (R := A) (⟨List.replicate n (u 0),valid⟩ : MObj H A)
    let q : Source.EMState E0 Γ :=
      ((sy off n).1,{(sy off n).2 with heap := ((sy off n).2.heap.alloc ⟨SU,sourceUintMemory (List.replicate n (u 0))⟩).1})
    checkedSourceFreshUints (E := E0) {F0 with cd := []} off n hp capacity=.ok (some t.1) ∧
    (Source.cdToMem {F0 with cd := []} SU off n).run (sy off n)=(.ok (.val (.memRef rfl 2)),q) ∧
    Heap.Keeps (List.prefix_append H [A]) hp t.1 ∧
    SourceUintMemoryAt q 2 t.1 t.2 .dyn ∧ Source.MemOK E0 SH q := by
  have result := source_cd_uint_checked_copy (sy off n) hp id {F0 with cd := []} off n capacity SH (memOK off n)
  rw [sourceCalldataUintValues_empty _ rfl] at result
  simp only [sourceUintValuePayload,List.map_replicate,calldataUint_sourceUint] at result
  obtain ⟨valid,direct,wrapped,run,keep,new,mok,rest⟩ := result
  exact ⟨valid,wrapped,run,keep,new,mok⟩

/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.checked_copy_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_copy_client
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.checked_stage_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_stage_vectors
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.checked_rejection_and_omission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_rejection_and_omission
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.checked_zero_runtime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms checked_zero_runtime

/-! Additional actual fresh-binding/reached-read clients. -/
private abbrev BΓ : Source.RCtx := (.int .u256)::Γ
private def bIndex : Source.Idx BΓ (.int .u256) := .here
private def bSrc : Source.Idx BΓ CD := .there .here
private def bDst : Source.Idx BΓ SU := .there (.there .here)
private def bAlias : Source.Idx BΓ SU := .there (.there (.there .here))
private def bNeighbor : Source.Idx BΓ SU := .there (.there (.there (.there .here)))
private def bInput (off len : Nat) (k : PrimTy.uint.Denote) : Source.EMState E0 BΓ :=
  (.cons (sourceUint k) (sy off len).1,(sy off len).2)
private def bMid : Source.EMState E0 BΓ :=
  ((bInput 0 3 (u 0)).1.set bDst (.memRef rfl 2),z.2)
private def bFinal (value : PrimTy.uint.Denote) : Source.EMState E0 BΓ :=
  (bMid.1.set bIndex (sourceUint value),bMid.2)
private theorem bMemOK (off len : Nat) (k : PrimTy.uint.Denote) :
    Source.MemOK E0 SH (bInput off len k) :=
  ⟨⟨(memOK off len).1.1,⟨trivial,(memOK off len).1.2⟩⟩,(memOK off len).2⟩
private def bProgram : Source.RItems E0 [] false .body BΓ BΓ :=
  .stmt (.expr (sourceUintCalldataBind bDst bSrc))
    (.stmt (.expr (sourceUintReadInto bDst bIndex bIndex)) .nil)

/-- A real BOTH-pipeline program binds the fresh copy, reads through it and
stores2 in the SAME scalar slot that held the initial index0. -/
theorem bound_read_program (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G0 p) frame (fuel+4) (sourceUintCalldataBind bDst bSrc)).run (bInput 0 3 (u 0))=
      (.ok (.val (.memRef rfl 2)),bMid) ∧
    (Source.evalE (G0 p) frame (fuel+2) (.indexArray (.local bDst) (.local bIndex) rfl)).run bMid=
      (.ok (.val (sourceUint (u 2))),bMid) ∧
    (Source.evalE (G0 p) frame (fuel+3) (sourceUintReadInto bDst bIndex bIndex)).run bMid=
      (.ok (.val (sourceUint (u 2))),bFinal (u 2)) ∧
    (Source.execItems (G0 p) frame (fuel+6) nps none bProgram (bInput 0 3 (u 0)).1).run (.nil,(bInput 0 3 (u 0)).2)=
      (.ok (.normal (bFinal (u 2)).1),(.nil,(bFinal (u 2)).2)) ∧
    checkedSourceFreshUints (E := E0) frame 0 3 hp (by decide)=.ok (some out) ∧
    Heap.Keeps (List.prefix_append H [A]) hp out ∧
    SourceUintMemoryAt (bFinal (u 2)) 2 out fresh .dyn ∧ Source.MemOK E0 SH (bFinal (u 2)) ∧
    SourceUintMemoryAt (bFinal (u 2)) 0 out (left.wk (List.prefix_append H [A])) .dyn ∧
    SourceUintMemoryAt (bFinal (u 2)) 1 out (right.wk (List.prefix_append H [A])) .dyn ∧
    (bFinal (u 2)).1.get bAlias=.memRef rfl 0 ∧ (bFinal (u 2)).1.get bNeighbor=.memRef rfl 1 := by
  have result := source_cd_uint_bind_read (bInput 0 3 (u 0)) hp (G0 p) frame fuel nps
    bDst bSrc bIndex bIndex 0 3 (u 0) rfl rfl (by decide) (by decide) SH (bMemOK 0 3 (u 0))
  rw [actually_decoded] at result
  obtain ⟨valid,value,hit,first,read,second,program,adapter,keep,new,mok,selected,stored,other,preserved,ex,events,logs,fn⟩ := result
  change some (u 2)=some value at hit
  cases Option.some.inj hit
  have oldInitial : SourceUintMemoryAt (bInput 0 3 (u 0)) 0 hp left .dyn := old_at 0 3
  have neighborInitial : SourceUintMemoryAt (bInput 0 3 (u 0)) 1 hp right .dyn := neighbor_at 0 3
  have oldFinal := oldInitial.transport keep (fun b obj hb => (preserved b obj hb).1)
  have neighborFinal := neighborInitial.transport keep (fun b obj hb => (preserved b obj hb).1)
  exact ⟨first,read,second,program,adapter,keep,new,mok,oldFinal,neighborFinal,rfl,rfl⟩

/-- Full ordered local/object/identity observations at all three Source stages;
old aliases/neighbor survive while the selected local and scalar really change. -/
theorem bound_vectors :
    (bInput 0 3 (u 0)).1=.cons (sourceUint (u 0)) (.cons (.cdRef rfl 0 3)
      (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil)))) ∧
    bMid.1=.cons (sourceUint (u 0)) (.cons (.cdRef rfl 0 3)
      (.cons (.memRef rfl 2) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil)))) ∧
    (bFinal (u 2)).1=.cons (sourceUint (u 2)) (.cons (.cdRef rfl 0 3)
      (.cons (.memRef rfl 2) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil)))) ∧
    [(bInput 0 3 (u 0)).2.heap.get 0,(bInput 0 3 (u 0)).2.heap.get 1,(bInput 0 3 (u 0)).2.heap.get 2,
      (bInput 0 3 (u 0)).2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,none,none] ∧
    [bMid.2.heap.get 0,bMid.2.heap.get 1,bMid.2.heap.get 2,bMid.2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory payload⟩,none] ∧
    [(bFinal (u 2)).2.heap.get 0,(bFinal (u 2)).2.heap.get 1,(bFinal (u 2)).2.heap.get 2,(bFinal (u 2)).2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory payload⟩,none] ∧
    [left.id,right.id,fresh.id]=[0,1,2] ∧
    (bFinal (u 2)).2.ex=(bInput 0 3 (u 0)).2.ex ∧
    (bFinal (u 2)).2.events=(bInput 0 3 (u 0)).2.events ∧
    (bFinal (u 2)).2.logs=(bInput 0 3 (u 0)).2.logs ∧
    (bFinal (u 2)).2.fnLocals=(bInput 0 3 (u 0)).2.fnLocals := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Reversing the two REAL statements reads old7 before binding, retaining7 in
the final scalar. This differs from the proper program's final scalar2. -/
theorem wrong_order_program (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.execItems (G0 p) frame (fuel+6) nps none
      (.stmt (.expr (sourceUintReadInto bDst bIndex bIndex))
        (.stmt (.expr (sourceUintCalldataBind bDst bSrc)) .nil) : Source.RItems E0 [] false .body BΓ BΓ)
      (bInput 0 3 (u 0)).1).run (.nil,(bInput 0 3 (u 0)).2)=
        (.ok (.normal (bFinal (u 7)).1),(.nil,(bFinal (u 7)).2)) ∧
    (bFinal (u 2)).1.get bIndex≠(bFinal (u 7)).1.get bIndex := by
  let initial := bInput 0 3 (u 0)
  let mid : Source.EMState E0 BΓ := (initial.1.set bIndex (sourceUint (u 7)),initial.2)
  have oldAt : SourceUintMemoryAt initial 0 hp left .dyn := old_at 0 3
  have bound : (u 0).1.toNat<hp.len left .dyn := by
    simp only [Heap.len,MObj.elems_dyn]
    decide
  have read := oldAt.eval_index (G0 p) frame (fuel+1) bDst bIndex (u 0) rfl rfl bound
  have actualRead : (Source.evalE (G0 p) frame (fuel+3)
      (.indexArray (.local bDst) (.local bIndex) rfl)).run initial=(.ok (.val (sourceUint (u 7))),initial) := by
    simpa only [MObj.elems_dyn] using read
  have first := source_uint_read_into_of_run (G0 p) frame (fuel+1) initial bDst bIndex bIndex (u 7) actualRead
  have firstStatement := source_expr_statement_run (G0 p) frame (fuel+4) nps _ initial mid _ first
  have second : (Source.evalE (G0 p) frame (fuel+3) (sourceUintCalldataBind bDst bSrc)).run mid=
      (.ok (.val (.memRef rfl 2)),bFinal (u 7)) := by
    rw [source_cd_uint_bind_run (G0 p) frame fuel mid bDst bSrc 0 3 rfl,actually_decoded]
    rfl
  have secondStatement := source_expr_statement_run (G0 p) frame (fuel+3) nps _ mid (bFinal (u 7)) _ second
  refine ⟨source_items_pair_run (G0 p) frame fuel nps _ _ initial mid (bFinal (u 7)) firstStatement secondStatement,?_⟩
  intro same
  have observed := congrArg (fun v : Source.Val E0.layout (.int .u256) => calldataUint (.val v)) same
  change u 2=u 7 at observed
  exact (by decide : u 2≠u 7) observed

/-- Empty copy REALLY binds a new empty root before the second read fails.
The error outcome exposes its retained state, not a final local environment. -/
theorem bound_empty_error (p : Roadmap.Pipeline) (fuel nps : Nat) :
    let initial := bInput 0 0 (u 0)
    let mid : Source.EMState E0 BΓ :=
      (initial.1.set bDst (.memRef rfl 2),{initial.2 with heap := (initial.2.heap.alloc ⟨SU,sourceUintMemory []⟩).1})
    (Source.evalE (G0 p) frame (fuel+4) (sourceUintCalldataBind bDst bSrc)).run initial=
      (.ok (.val (.memRef rfl 2)),mid) ∧
    (Source.evalE (G0 p) frame (fuel+3) (sourceUintReadInto bDst bIndex bIndex)).run mid=
      (.error (.revert (Source.panicData .index)),mid) ∧
    (Source.execItems (G0 p) frame (fuel+6) nps none bProgram initial.1).run (.nil,initial.2)=
      (.error (.revert (Source.panicData .index)),(.nil,mid.2)) ∧
    let pair := hp.alloc (R := A) (⟨[],by decide⟩ : MObj H A)
    checkedSourceFreshUints (E := E0) frame 0 0 hp (by decide)=.ok (some pair.1) ∧
    Heap.Keeps (List.prefix_append H [A]) hp pair.1 ∧
    SourceUintMemoryAt mid 2 pair.1 pair.2 .dyn ∧ Source.MemOK E0 SH mid ∧
    pair.1.index pair.2 .dyn (u 0)=none ∧
    mid.2.heap.get 2=some ⟨SU,sourceUintMemory []⟩ ∧ mid.2.heap.next=3 := by
  dsimp only
  let initial := bInput 0 0 (u 0)
  let mid : Source.EMState E0 BΓ :=
    (initial.1.set bDst (.memRef rfl 2),{initial.2 with heap := (initial.2.heap.alloc ⟨SU,sourceUintMemory []⟩).1})
  have binding := source_cd_uint_bind_copy initial hp (G0 p) frame (fuel+1) nps bDst bSrc 0 0 rfl (by decide) SH (bMemOK 0 0 (u 0))
  have decodedEmpty : sourceCalldataUintValues E0 frame 0 0=.ok [] := rfl
  rw [decodedEmpty] at binding
  obtain ⟨valid,first,firstStatement,adapter,keep,freshRep,mok,selected,other,identity,preserved,ex,events,logs,fn⟩ := binding
  have read := freshRep.eval_read_bounds (G0 p) frame fuel bDst bIndex (u 0) selected rfl
    (by simp only [Heap.len,Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn,sourceUintValuePayload,List.map_nil,List.length_nil];exact Nat.le_refl _)
  have actualRead : (Source.evalE (G0 p) frame (fuel+2)
      (.indexArray (.local bDst) (.local bIndex) rfl)).run mid=
      (.error (.revert (Source.panicData .index)),mid) := read
  have second : (Source.evalE (G0 p) frame (fuel+3) (sourceUintReadInto bDst bIndex bIndex)).run mid=
      (.error (.revert (Source.panicData .index)),mid) := by
    unfold sourceUintReadInto
    rw [Source.evalE,Source.Hoare.run_bind,actualRead]
  have secondStatement := source_expr_statement_error (G0 p) frame (fuel+3) nps _ mid mid _ second
  refine ⟨first,second,source_items_pair_error (G0 p) frame fuel nps _ _ initial mid mid
    (.revert (Source.panicData .index)) firstStatement secondStatement,
    adapter,keep,freshRep,mok,?_,rfl,rfl⟩
  change (MObj.elems .dyn _)[0]?=none
  rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
  rfl

theorem binding_low (p : Roadmap.Pipeline) (fuel : Nat) (low : fuel≤2) :
    (Source.evalE (G0 p) frame fuel (sourceUintCalldataBind bDst bSrc)).run (bInput 0 3 (u 0))=
      (.error .timeout,bInput 0 3 (u 0)) :=
  source_cd_uint_bind_low (G0 p) frame _ bDst bSrc fuel low

/-- Full reversed-order final local vector; its heap/world is exactly the
forward heap/world, while the stored scalar observation differs. -/
theorem wrong_order_vectors :
    (bFinal (u 7)).1=.cons (sourceUint (u 7)) (.cons (.cdRef rfl 0 3)
      (.cons (.memRef rfl 2) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil)))) ∧
    (bFinal (u 7)).2=(bFinal (u 2)).2 ∧
    [(bFinal (u 7)).2.heap.get 0,(bFinal (u 7)).2.heap.get 1,(bFinal (u 7)).2.heap.get 2,(bFinal (u 7)).2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory payload⟩,none] := by
  exact ⟨rfl,rfl,rfl⟩

/-- The complete retained EMPTY-prefix table and its reached locals. These
locals belong to the successful prefix, not the erased error outcome context. -/
theorem empty_prefix_vectors :
    let initial := bInput 0 0 (u 0)
    let mid : Source.EMState E0 BΓ :=
      (initial.1.set bDst (.memRef rfl 2),{initial.2 with heap := (initial.2.heap.alloc ⟨SU,sourceUintMemory []⟩).1})
    mid.1=.cons (sourceUint (u 0)) (.cons (.cdRef rfl 0 0)
      (.cons (.memRef rfl 2) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil)))) ∧
    [mid.2.heap.get 0,mid.2.heap.get 1,mid.2.heap.get 2,mid.2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory []⟩,none] ∧
    mid.2.ex=initial.2.ex ∧ mid.2.events=initial.2.events ∧ mid.2.logs=initial.2.logs ∧ mid.2.fnLocals=initial.2.fnLocals := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.bound_read_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bound_read_program
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.bound_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bound_vectors
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.wrong_order_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_order_program
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.bound_empty_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bound_empty_error
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.binding_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms binding_low
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.wrong_order_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms wrong_order_vectors
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.empty_prefix_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_prefix_vectors

/-! Additional actual fresh-binding/mutation clients. -/
private def mType : bMid.2.heap.ty 2=some SU := rfl
private def mPayload : List PrimTy.uint.Denote := [u 0,u 0,maximum]
private def mSource : Source.EMState E0 BΓ :=
  (bMid.1,{bMid.2 with heap := bMid.2.heap.write 2 (sourceUintMemory mPayload) mType})
private def mOut : Heap (H++[A]) := out.set fresh (MObj.setElem .dyn (out.get fresh) 0 (u 0))
private def mProgram : Source.RItems E0 [] false .body BΓ BΓ :=
  .stmt (.expr (sourceUintCalldataBind bDst bSrc))
    (.stmt (.expr (sourceUintIndexedAssign bDst bIndex bIndex)) .nil)

/-- Actual copy/bind then material numeric mutation in ONE Source program,
linked to the same checked-copy heap and a real intrinsic writeAddr. -/
theorem bound_mutation_program (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G0 p) frame (fuel+4) (sourceUintCalldataBind bDst bSrc)).run (bInput 0 3 (u 0))=
      (.ok (.val (.memRef rfl 2)),bMid) ∧
    (Source.evalE (G0 p) frame (fuel+3) (sourceUintIndexedAssign bDst bIndex bIndex)).run bMid=
      (.ok (.val (sourceUint (u 0))),mSource) ∧
    (Source.execItems (G0 p) frame (fuel+6) nps none mProgram (bInput 0 3 (u 0)).1).run (.nil,(bInput 0 3 (u 0)).2)=
      (.ok (.normal mSource.1),(.nil,mSource.2)) ∧
    checkedSourceFreshUints (E := E0) frame 0 3 hp (by decide)=.ok (some out) ∧
    out.writeAddr (.index fresh .dyn (u 0)) (u 0)=some mOut ∧
    SourceUintMemoryAt mSource 2 mOut fresh .dyn ∧ Source.MemOK E0 SH mSource ∧
    Heap.Keeps (List.prefix_append H [A]) hp mOut ∧
    SourceUintMemoryAt mSource 0 mOut (left.wk (List.prefix_append H [A])) .dyn ∧
    SourceUintMemoryAt mSource 1 mOut (right.wk (List.prefix_append H [A])) .dyn := by
  have result := source_cd_uint_bind_assign (bInput 0 3 (u 0)) hp (G0 p) frame fuel nps
    bDst bSrc bIndex bIndex 0 3 (u 0) (u 0) rfl rfl rfl (by decide) (by decide) SH (bMemOK 0 3 (u 0))
  rw [actually_decoded] at result
  obtain ⟨valid,native,zs,first,second,program,adapter,hw,new,mok,keep,values,occupied,locals,ex,events,logs,fn⟩ := result
  have nativeBound : (u 0).1.toNat<(MObj.elems .dyn (out.get fresh)).length := by
    unfold out fresh
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn,List.length_map]
    decide
  have nativeRun : out.writeAddr (.index fresh .dyn (u 0)) (u 0)=some mOut := by
    simp only [Heap.writeAddr,Heap.setIndex,nativeBound,↓reduceIte]
    rfl
  have equalNative : native=mOut := Option.some.inj (hw.symm.trans nativeRun)
  subst native
  have before : SourceUintMemoryAt bMid 2 out fresh .dyn := (copy_client p 0).2.2.1
  have bound : (u 0).1.toNat<out.len fresh .dyn := by
    simp only [Heap.len,MObj.elems_dyn]
    decide
  obtain ⟨ht,write⟩ := source_uint_write bMid 2 payload (by rfl) 0 (by decide) (u 0)
  have actualWrite : (Source.writeLoc (E := E0) (Γ := BΓ) frame (fuel+2) (.mem 2 0) (sourceUint (u 0))).run bMid=
      (.ok (),mSource) := write
  have actual := before.eval_assign_of_run (G0 p) frame fuel bDst bIndex bIndex (u 0) (u 0) rfl rfl rfl bound actualWrite
  have equalSource : zs=mSource := congrArg Prod.snd (second.symm.trans actual)
  subst zs
  have oldInitial : SourceUintMemoryAt (bInput 0 3 (u 0)) 0 hp left .dyn := old_at 0 3
  have neighborInitial : SourceUintMemoryAt (bInput 0 3 (u 0)) 1 hp right .dyn := neighbor_at 0 3
  exact ⟨first,second,program,adapter,nativeRun,new,mok,keep,
    oldInitial.transport keep occupied,neighborInitial.transport keep occupied⟩

/-- Full post-mutation local/Source object/world vector. Previous full initial,
copied and typed vectors remain available unchanged. -/
theorem mutation_vectors :
    mSource.1=bMid.1 ∧
    [mSource.2.heap.get 0,mSource.2.heap.get 1,mSource.2.heap.get 2,mSource.2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory mPayload⟩,none] ∧
    [MObj.elems .dyn (mOut.get (left.wk (List.prefix_append H [A]))),
      MObj.elems .dyn (mOut.get (right.wk (List.prefix_append H [A]))),MObj.elems .dyn (mOut.get fresh)]=
      [old,neighbor,mPayload] ∧
    [left.id,right.id,fresh.id]=[0,1,2] ∧ mSource.2.heap.next=3 ∧
    mSource.2.ex=(bInput 0 3 (u 0)).2.ex ∧ mSource.2.events=(bInput 0 3 (u 0)).2.events ∧
    mSource.2.logs=(bInput 0 3 (u 0)).2.logs ∧ mSource.2.fnLocals=(bInput 0 3 (u 0)).2.fnLocals := by
  refine ⟨rfl,rfl,?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨_,_,_,_,hw,_,_,keep,_,_⟩ := bound_mutation_program .legacy 0 0
  have original : MObj.elems .dyn (out.get fresh)=payload := by
    unfold out fresh
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
    exact List.map_id'' (fun _ => rfl) _
  rw [keep left,keep right,MObj.elems_wk,MObj.elems_wk,
    indexedWrite_elems out mOut fresh .dyn (u 0) (u 0) hw,original]
  simp only [MObj.elems_dyn,List.map_id'' (f := MVal.wk (List.prefix_append H [A]) (.prim .uint)) (fun _ => rfl)]
  rfl

private def staleType : (bInput 0 3 (u 0)).2.heap.ty 0=some SU := rfl
private def staleSource : Source.EMState E0 BΓ :=
  let initial := bInput 0 3 (u 0)
  (initial.1,{initial.2 with heap := initial.2.heap.write 0 (sourceUintMemory (old.set 0 (u 0))) staleType})

/-- Skipping the binding actually writes old object0; skipping the write keeps
fresh2. Complete stored values distinguish both from the supported execution. -/
theorem mutation_negatives (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) frame (fuel+3) (sourceUintIndexedAssign bDst bIndex bIndex)).run (bInput 0 3 (u 0))=
      (.ok (.val (sourceUint (u 0))),staleSource) ∧
    [staleSource.2.heap.get 0,staleSource.2.heap.get 1,staleSource.2.heap.get 2,staleSource.2.heap.get 3]=
      [some ⟨SU,sourceUintMemory [u 0,u 0,maximum]⟩,some ⟨SU,sourceUintMemory neighbor⟩,none,none] ∧
    (Source.memElem (E := E0) (Γ := BΓ) 2 0 (.int .u256)).run bMid=(.ok (sourceUint (u 2)),bMid) ∧
    (Source.memElem (E := E0) (Γ := BΓ) 2 0 (.int .u256)).run mSource=(.ok (sourceUint (u 0)),mSource) ∧
    (Source.memElem (E := E0) (Γ := BΓ) 0 0 (.int .u256)).run mSource=(.ok (sourceUint (u 7)),mSource) := by
  have oldAt : SourceUintMemoryAt (bInput 0 3 (u 0)) 0 hp left .dyn := old_at 0 3
  have bound : (u 0).1.toNat<hp.len left .dyn := by
    simp only [Heap.len,MObj.elems_dyn]
    decide
  obtain ⟨ht,write⟩ := source_uint_write (bInput 0 3 (u 0)) 0 old (by rfl) 0 (by decide) (u 0)
  have actualWrite : (Source.writeLoc (E := E0) (Γ := BΓ) frame (fuel+2) (.mem 0 0) (sourceUint (u 0))).run (bInput 0 3 (u 0))=
      (.ok (),staleSource) := write
  have actual := oldAt.eval_assign_of_run (G0 p) frame fuel bDst bIndex bIndex (u 0) (u 0) rfl rfl rfl bound actualWrite
  exact ⟨actual,rfl,rfl,rfl,rfl⟩

/-- A successful empty allocating/binding prefix followed by an actual write
bounds panic retains the prefix Source.St; native write rejection is None. -/
theorem empty_mutation_error (p : Roadmap.Pipeline) (fuel nps : Nat) :
    let initial := bInput 0 0 (u 0)
    let mid : Source.EMState E0 BΓ :=
      (initial.1.set bDst (.memRef rfl 2),{initial.2 with heap := (initial.2.heap.alloc ⟨SU,sourceUintMemory []⟩).1})
    let pair := hp.alloc (R := A) (⟨[],by decide⟩ : MObj H A)
    (Source.evalE (G0 p) frame (fuel+4) (sourceUintCalldataBind bDst bSrc)).run initial=
      (.ok (.val (.memRef rfl 2)),mid) ∧
    (Source.evalE (G0 p) frame (fuel+3) (sourceUintIndexedAssign bDst bIndex bIndex)).run mid=
      (.error (.revert (Source.panicData .index)),mid) ∧
    (Source.execItems (G0 p) frame (fuel+6) nps none mProgram initial.1).run (.nil,initial.2)=
      (.error (.revert (Source.panicData .index)),(.nil,mid.2)) ∧
    checkedSourceFreshUints (E := E0) frame 0 0 hp (by decide)=.ok (some pair.1) ∧
    pair.1.writeAddr (.index pair.2 .dyn (u 0)) (u 0)=none ∧
    mid.2.heap.get 2=some ⟨SU,sourceUintMemory []⟩ ∧ mid.2.heap.next=3 := by
  dsimp only
  let initial := bInput 0 0 (u 0)
  let mid : Source.EMState E0 BΓ :=
    (initial.1.set bDst (.memRef rfl 2),{initial.2 with heap := (initial.2.heap.alloc ⟨SU,sourceUintMemory []⟩).1})
  have binding := source_cd_uint_bind_copy initial hp (G0 p) frame (fuel+1) nps bDst bSrc 0 0 rfl (by decide) SH (bMemOK 0 0 (u 0))
  have decodedEmpty : sourceCalldataUintValues E0 frame 0 0=.ok [] := rfl
  rw [decodedEmpty] at binding
  obtain ⟨valid,first,firstStatement,adapter,keep,freshRep,mok,selected,other,identity,preserved,ex,events,logs,fn⟩ := binding
  have second : (Source.evalE (G0 p) frame (fuel+3) (sourceUintIndexedAssign bDst bIndex bIndex)).run mid=
      (.error (.revert (Source.panicData .index)),mid) :=
    freshRep.eval_assign_bounds (G0 p) frame fuel bDst bIndex bIndex (u 0) (u 0) selected rfl rfl
      (by simp only [Heap.len,Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn,sourceUintValuePayload,List.map_nil,List.length_nil];exact Nat.le_refl _)
  have secondStatement := source_expr_statement_error (G0 p) frame (fuel+3) nps _ mid mid _ second
  refine ⟨first,second,source_items_pair_error (G0 p) frame fuel nps _ _ initial mid mid
    (.revert (Source.panicData .index)) firstStatement secondStatement,adapter,?_,rfl,rfl⟩
  simp only [Heap.writeAddr,Heap.setIndex,Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn,List.map_nil,List.length_nil]
  rfl

private def rType : (bFinal (u 2)).2.heap.ty 2=some SU := rfl
private def rPayload : List PrimTy.uint.Denote := [u 2,u 0,u 2]
private def rSource : Source.EMState E0 BΓ :=
  let initial := bFinal (u 2)
  (initial.1,{initial.2 with heap := initial.2.heap.write 2 (sourceUintMemory rPayload) rType})
private def rOut : Heap (H++[A]) := out.set fresh (MObj.setElem .dyn (out.get fresh) 2 (u 2))

/-- Three REAL Source statements: copy/bind, read into the index scalar, then
write through the COMPUTED reached index2, materially changing max to2. -/
theorem read_driven_mutation_program (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G0 p) frame (fuel+5) (sourceUintCalldataBind bDst bSrc)).run (bInput 0 3 (u 0))=
      (.ok (.val (.memRef rfl 2)),bMid) ∧
    (Source.evalE (G0 p) frame (fuel+4) (sourceUintReadInto bDst bIndex bIndex)).run bMid=
      (.ok (.val (sourceUint (u 2))),bFinal (u 2)) ∧
    (Source.evalE (G0 p) frame (fuel+3) (sourceUintIndexedAssign bDst bIndex bIndex)).run (bFinal (u 2))=
      (.ok (.val (sourceUint (u 2))),rSource) ∧
    (Source.execItems (G0 p) frame (fuel+7) nps none
      (.stmt (.expr (sourceUintCalldataBind bDst bSrc))
        (.stmt (.expr (sourceUintReadInto bDst bIndex bIndex))
          (.stmt (.expr (sourceUintIndexedAssign bDst bIndex bIndex)) .nil)) : Source.RItems E0 [] false .body BΓ BΓ)
      (bInput 0 3 (u 0)).1).run (.nil,(bInput 0 3 (u 0)).2)=(.ok (.normal rSource.1),(.nil,rSource.2)) ∧
    out.writeAddr (.index fresh .dyn (u 2)) (u 2)=some rOut ∧
    SourceUintMemoryAt rSource 2 rOut fresh .dyn ∧ Source.MemOK E0 SH rSource ∧
    Heap.Keeps (List.prefix_append H [A]) hp rOut := by
  obtain ⟨first,_,second,_,adapter,oldKeep,before,mokBefore,_,_,_,_⟩ := bound_read_program p (fuel+1) nps
  have nativeBound : (u 2).1.toNat<(MObj.elems .dyn (out.get fresh)).length := by
    unfold out fresh
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn,List.length_map]
    decide
  have expectedNative : out.writeAddr (.index fresh .dyn (u 2)) (u 2)=some rOut := by
    simp only [Heap.writeAddr,Heap.setIndex,nativeBound,↓reduceIte]
    rfl
  obtain ⟨native,zs,hw,hs,new,mok,values,frames,sourceFrames,locals,ex,events,logs,fn⟩ :=
    before.write_observed frame (fuel+2) (u 2) (u 2) nativeBound SH mokBefore
  have equalNative : native=rOut := Option.some.inj (hw.symm.trans expectedNative)
  subst native
  obtain ⟨ht,write⟩ := source_uint_write (bFinal (u 2)) 2 payload (by rfl) 2 (by decide) (u 2)
  have actualWrite : (Source.writeLoc (E := E0) (Γ := BΓ) frame (fuel+2) (.mem 2 2) (sourceUint (u 2))).run (bFinal (u 2))=
      (.ok (),rSource) := write
  have equalSource : zs=rSource := congrArg Prod.snd (hs.symm.trans actualWrite)
  subst zs
  have third := before.eval_assign_of_run (G0 p) frame fuel bDst bIndex bIndex (u 2) (u 2) rfl rfl rfl nativeBound actualWrite
  have firstStatement := source_expr_statement_run (G0 p) frame (fuel+5) nps _ (bInput 0 3 (u 0)) bMid _ first
  have secondStatement := source_expr_statement_run (G0 p) frame (fuel+4) nps _ bMid (bFinal (u 2)) _ second
  have thirdStatement := source_expr_statement_run (G0 p) frame (fuel+3) nps _ (bFinal (u 2)) rSource _ third
  have tail := source_items_pair_run (G0 p) frame fuel nps _ _ bMid (bFinal (u 2)) rSource secondStatement thirdStatement
  have program := source_items_cons_run (G0 p) frame (fuel+6) nps _ _ (bInput 0 3 (u 0)) bMid rSource firstStatement tail
  have keep : Heap.Keeps (List.prefix_append H [A]) hp rOut := by
    intro Q q
    have different : fresh.id≠(q.wk (List.prefix_append H [A])).id := Ne.symm (Nat.ne_of_lt q.id_lt)
    exact (frames Q (q.wk (List.prefix_append H [A])) different).trans (oldKeep q)
  exact ⟨first,second,third,program,expectedNative,new,mok,keep⟩

/-- Complete final observations of the data-dependent write, preserving the
old aliases/neighbor and scalar2 while the fresh LAST element changes. -/
theorem read_driven_vectors :
    rSource.1=(bFinal (u 2)).1 ∧
    [rSource.2.heap.get 0,rSource.2.heap.get 1,rSource.2.heap.get 2,rSource.2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory rPayload⟩,none] ∧
    [MObj.elems .dyn (rOut.get (left.wk (List.prefix_append H [A]))),
      MObj.elems .dyn (rOut.get (right.wk (List.prefix_append H [A]))),MObj.elems .dyn (rOut.get fresh)]=
      [old,neighbor,rPayload] ∧
    rSource.2.heap.next=3 ∧ rSource.2.ex=(bInput 0 3 (u 0)).2.ex ∧
    rSource.2.events=(bInput 0 3 (u 0)).2.events ∧ rSource.2.logs=(bInput 0 3 (u 0)).2.logs ∧
    rSource.2.fnLocals=(bInput 0 3 (u 0)).2.fnLocals := by
  refine ⟨rfl,rfl,?_,rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨_,_,_,_,hw,_,_,keep⟩ := read_driven_mutation_program .legacy 0 0
  have original : MObj.elems .dyn (out.get fresh)=payload := by
    unfold out fresh
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
    exact List.map_id'' (fun _ => rfl) _
  rw [keep left,keep right,MObj.elems_wk,MObj.elems_wk,
    indexedWrite_elems out rOut fresh .dyn (u 2) (u 2) hw,original]
  simp only [MObj.elems_dyn,List.map_id'' (f := MVal.wk (List.prefix_append H [A]) (.prim .uint)) (fun _ => rfl)]
  rfl

/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.bound_mutation_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms bound_mutation_program
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.mutation_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mutation_vectors
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.mutation_negatives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms mutation_negatives
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.empty_mutation_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms empty_mutation_error
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.read_driven_mutation_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms read_driven_mutation_program
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.read_driven_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms read_driven_vectors

/-! Actual copy/bind/delete clients; all preceding fixtures remain unchanged. -/
private def dPayload : List PrimTy.uint.Denote := [u 2,u 0,u 0]
private def dSource : Source.EMState E0 BΓ :=
  let mid := bFinal (u 2)
  (mid.1,{mid.2 with heap := mid.2.heap.write 2 (sourceUintMemory dPayload) rType})
private def dOut : Heap (H++[A]) := out.set fresh (MObj.setElem .dyn (out.get fresh) 2 (PrimTy.dflt .uint))
private def dProgram : Source.RItems E0 [] false .body BΓ BΓ :=
  .stmt (.expr (sourceUintCalldataBind bDst bSrc))
    (.stmt (.expr (sourceUintIndexedDelete bDst bIndex)) .nil)

/-- Both pipelines copy/bind then actually DELETE the maximum last word. -/
theorem bound_delete_program (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G0 p) frame (fuel+4) (sourceUintCalldataBind bDst bSrc)).run (bInput 0 3 (u 2))=
      (.ok (.val (.memRef rfl 2)),bFinal (u 2)) ∧
    (Source.evalE (G0 p) frame (fuel+3) (sourceUintIndexedDelete bDst bIndex)).run (bFinal (u 2))=
      (.ok Source.RVal.unit,dSource) ∧
    (Source.execItems (G0 p) frame (fuel+6) nps none dProgram (bInput 0 3 (u 2)).1).run (.nil,(bInput 0 3 (u 2)).2)=
      (.ok (.normal dSource.1),(.nil,dSource.2)) ∧
    checkedSourceFreshUints (E := E0) frame 0 3 hp (by decide)=.ok (some out) ∧
    out.writeAddr (.index fresh .dyn (u 2)) (PrimTy.dflt .uint)=some dOut ∧
    SourceUintMemoryAt dSource 2 dOut fresh .dyn ∧ Source.MemOK E0 SH dSource ∧
    Heap.Keeps (List.prefix_append H [A]) hp dOut ∧
    SourceUintMemoryAt dSource 0 dOut (left.wk (List.prefix_append H [A])) .dyn ∧
    SourceUintMemoryAt dSource 1 dOut (right.wk (List.prefix_append H [A])) .dyn := by
  have result := source_cd_uint_bind_delete (bInput 0 3 (u 2)) hp (G0 p) frame fuel nps
    bDst bSrc bIndex 0 3 (u 2) rfl rfl (by decide) (by decide) SH (bMemOK 0 3 (u 2))
  rw [actually_decoded] at result
  obtain ⟨valid,native,zs,first,second,program,adapter,hw,new,mok,keep,values,occupied,locals,ex,events,logs,fn⟩ := result
  have nativeBound : (u 2).1.toNat<(MObj.elems .dyn (out.get fresh)).length := by
    unfold out fresh
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn,List.length_map]
    decide
  have nativeRun : out.writeAddr (.index fresh .dyn (u 2)) (PrimTy.dflt .uint)=some dOut := by
    simp only [Heap.writeAddr,Heap.setIndex,nativeBound,↓reduceIte]
    rfl
  have equalNative : native=dOut := Option.some.inj (hw.symm.trans nativeRun)
  subst native
  have before : SourceUintMemoryAt (bFinal (u 2)) 2 out fresh .dyn := (copy_client p 0).2.2.1
  obtain ⟨ht,write⟩ := source_uint_write (bFinal (u 2)) 2 payload (by rfl) 2 (by decide) (PrimTy.dflt .uint)
  have actualWrite : (Source.deleteLoc (E := E0) (Γ := BΓ) frame (fuel+2) (τ := .int .u256) (.mem 2 2)).run (bFinal (u 2))=
      (.ok (),dSource) := write
  have actual := before.eval_delete_of_run (G0 p) frame fuel bDst bIndex (u 2) rfl rfl nativeBound actualWrite
  have equalSource : zs=dSource := congrArg Prod.snd (second.symm.trans actual)
  subst zs
  have oldInitial : SourceUintMemoryAt (bInput 0 3 (u 2)) 0 hp left .dyn := old_at 0 3
  have neighborInitial : SourceUintMemoryAt (bInput 0 3 (u 2)) 1 hp right .dyn := neighbor_at 0 3
  exact ⟨first,second,program,adapter,nativeRun,new,mok,keep,
    oldInitial.transport keep occupied,neighborInitial.transport keep occupied⟩

/-- Ordered full Source/native tables, locals, identities and world frames.
The separate delete_prefix_vectors records the exact index2 prefix. -/
theorem delete_vectors :
    dSource.1=(bFinal (u 2)).1 ∧
    [dSource.2.heap.get 0,dSource.2.heap.get 1,dSource.2.heap.get 2,dSource.2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory dPayload⟩,none] ∧
    [MObj.elems .dyn (dOut.get (left.wk (List.prefix_append H [A]))),
      MObj.elems .dyn (dOut.get (right.wk (List.prefix_append H [A]))),MObj.elems .dyn (dOut.get fresh)]=
      [old,neighbor,dPayload] ∧
    [left.id,right.id,fresh.id]=[0,1,2] ∧ dSource.2.heap.next=3 ∧
    dSource.2.ex=(bInput 0 3 (u 2)).2.ex ∧ dSource.2.events=(bInput 0 3 (u 2)).2.events ∧
    dSource.2.logs=(bInput 0 3 (u 2)).2.logs ∧ dSource.2.fnLocals=(bInput 0 3 (u 2)).2.fnLocals := by
  refine ⟨rfl,rfl,?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
  obtain ⟨_,_,_,_,hw,_,_,keep,_,_⟩ := bound_delete_program .legacy 0 0
  have original : MObj.elems .dyn (out.get fresh)=payload := by
    unfold out fresh
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
    exact List.map_id'' (fun _ => rfl) _
  rw [keep left,keep right,MObj.elems_wk,MObj.elems_wk,
    indexedWrite_elems out dOut fresh .dyn (u 2) (PrimTy.dflt .uint) hw,original]
  simp only [MObj.elems_dyn,List.map_id'' (f := MVal.wk (List.prefix_append H [A]) (.prim .uint)) (fun _ => rfl)]
  rfl

/-- Literal empty copy succeeds before the reached deletion rejects index0. -/
theorem empty_delete_error (p : Roadmap.Pipeline) (fuel nps : Nat) :
    let initial := bInput 0 0 (u 0)
    let mid : Source.EMState E0 BΓ :=
      (initial.1.set bDst (.memRef rfl 2),{initial.2 with heap := (initial.2.heap.alloc ⟨SU,sourceUintMemory []⟩).1})
    let pair := hp.alloc (R := A) (⟨[],by decide⟩ : MObj H A)
    (Source.evalE (G0 p) frame (fuel+4) (sourceUintCalldataBind bDst bSrc)).run initial=
      (.ok (.val (.memRef rfl 2)),mid) ∧
    (Source.evalE (G0 p) frame (fuel+3) (sourceUintIndexedDelete bDst bIndex)).run mid=
      (.error (.revert (Source.panicData .index)),mid) ∧
    (Source.execItems (G0 p) frame (fuel+6) nps none dProgram initial.1).run (.nil,initial.2)=
      (.error (.revert (Source.panicData .index)),(.nil,mid.2)) ∧
    checkedSourceFreshUints (E := E0) frame 0 0 hp (by decide)=.ok (some pair.1) ∧
    pair.1.writeAddr (.index pair.2 .dyn (u 0)) (PrimTy.dflt .uint)=none ∧
    [mid.2.heap.get 0,mid.2.heap.get 1,mid.2.heap.get 2,mid.2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory []⟩,none] ∧
    mid.2.heap.next=3 := by
  dsimp only
  have result := source_cd_uint_bind_delete_bounds (bInput 0 0 (u 0)) hp (G0 p) frame fuel nps
    bDst bSrc bIndex 0 0 (u 0) rfl rfl (by decide) (by decide) SH (bMemOK 0 0 (u 0))
  have decodedEmpty : sourceCalldataUintValues E0 frame 0 0=.ok [] := rfl
  rw [decodedEmpty] at result
  obtain ⟨valid,first,second,program,adapter,failed,new,mok,keep,preserved⟩ := result
  exact ⟨first,second,program,adapter,failed,rfl,rfl⟩

/-- Exact nonempty endpoint3 rejects after the real copied prefix, not before it. -/
theorem endpoint_delete_error (p : Roadmap.Pipeline) (fuel nps : Nat) :
    let mid := bFinal (u 3)
    (Source.evalE (G0 p) frame (fuel+4) (sourceUintCalldataBind bDst bSrc)).run (bInput 0 3 (u 3))=
      (.ok (.val (.memRef rfl 2)),mid) ∧
    (Source.evalE (G0 p) frame (fuel+3) (sourceUintIndexedDelete bDst bIndex)).run mid=
      (.error (.revert (Source.panicData .index)),mid) ∧
    (Source.execItems (G0 p) frame (fuel+6) nps none dProgram (bInput 0 3 (u 3)).1).run (.nil,(bInput 0 3 (u 3)).2)=
      (.error (.revert (Source.panicData .index)),(.nil,mid.2)) ∧
    out.writeAddr (.index fresh .dyn (u 3)) (PrimTy.dflt .uint)=none ∧
    mid.2.heap.get 2=some ⟨SU,sourceUintMemory payload⟩ ∧ mid.2.heap.next=3 := by
  dsimp only
  have result := source_cd_uint_bind_delete_bounds (bInput 0 3 (u 3)) hp (G0 p) frame fuel nps
    bDst bSrc bIndex 0 3 (u 3) rfl rfl (by decide) (by decide) SH (bMemOK 0 3 (u 3))
  rw [actually_decoded] at result
  obtain ⟨valid,first,second,program,adapter,failed,new,mok,keep,preserved⟩ := result
  exact ⟨first,second,program,failed,rfl,rfl⟩

/-- Omitting deletion retains maximum; stale retained alias still reads7.
The returned deletion value is unit, not the removed maximum. -/
theorem delete_omission_and_alias (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) frame (fuel+2) (.indexArray (.local bDst) (.local bIndex) rfl)).run (bFinal (u 2))=
      (.ok (.val (sourceUint maximum)),bFinal (u 2)) ∧
    (Source.evalE (G0 p) frame (fuel+2) (.indexArray (.local bDst) (.local bIndex) rfl)).run dSource=
      (.ok (.val (sourceUint (u 0))),dSource) ∧
    (Source.evalE (G0 p) frame (fuel+2) (.indexArray (.local bAlias) (.local bIndex) rfl)).run
      (dSource.1.set bIndex (sourceUint (u 0)),dSource.2)=
      (.ok (.val (sourceUint (u 7))),(dSource.1.set bIndex (sourceUint (u 0)),dSource.2)) ∧
    (sourceUint maximum : Source.Val E0.layout (.int .u256))≠sourceUint (u 0) := by
  have before : SourceUintMemoryAt (bFinal (u 2)) 2 out fresh .dyn := (copy_client p 0).2.2.1
  have size : (u 2).1.toNat<out.len fresh .dyn := by
    unfold Heap.len out fresh
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn,List.length_map]
    decide
  have first := before.eval_index (G0 p) frame fuel bDst bIndex (u 2) rfl rfl size
  have original : MObj.elems .dyn (out.get fresh)=payload := by
    unfold out fresh
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
    exact List.map_id'' (fun _ => rfl) _
  simp only [original] at first
  obtain ⟨_,_,_,_,_,after,mok,keep,oldAt,_⟩ := bound_delete_program p fuel 0
  have values : MObj.elems .dyn (dOut.get fresh)=dPayload :=
    (List.cons.inj (List.cons.inj (List.cons.inj delete_vectors.2.2.1).2).2).1
  have sizeAfter : (u 2).1.toNat<dOut.len fresh .dyn := by
    unfold Heap.len
    rw [values]
    decide
  have second := after.eval_index (G0 p) frame fuel bDst bIndex (u 2) rfl rfl sizeAfter
  simp only [values] at second
  have different : (sourceUint maximum : Source.Val E0.layout (.int .u256))≠sourceUint (u 0) := by
    intro same
    have converted := congrArg (fun v : Source.Val E0.layout (.int .u256) => calldataUint (.val v)) same
    have unequal : maximum≠u 0 := by decide
    exact unequal (by simpa only [calldataUint_sourceUint] using converted)
  refine ⟨first,second,?_,different⟩
  have oldRep : SourceUintMemoryAt (dSource.1.set bIndex (sourceUint (u 0)),dSource.2) 0 dOut
      (left.wk (List.prefix_append H [A])) .dyn := oldAt
  have oldBound : (u 0).1.toNat<dOut.len (left.wk (List.prefix_append H [A])) .dyn := by
    unfold Heap.len
    rw [keep left,MObj.elems_wk,MObj.elems_dyn,List.length_map]
    decide
  have read := oldRep.eval_index (G0 p) frame fuel bAlias bIndex (u 0) rfl rfl oldBound
  simp only [keep left,MObj.elems_wk,MObj.elems_dyn] at read
  exact read


private def dOldType : (bInput 0 3 (u 2)).2.heap.ty 0=some SU := rfl
private def dOldSource : Source.EMState E0 BΓ :=
  let initial := bInput 0 3 (u 2)
  (initial.1,{initial.2 with heap := initial.2.heap.write 0 (sourceUintMemory [u 7,u 0,u 0]) dOldType})
private def dReverse : Source.EMState E0 BΓ :=
  (dOldSource.1.set bDst (.memRef rfl 2),
    {dOldSource.2 with heap := (dOldSource.2.heap.alloc ⟨SU,sourceUintMemory payload⟩).1})

/-- Reversing actual DELETE and binding changes the OLD object and then copies
an uncleared maximum into the fresh object, unlike the supported order. -/
theorem delete_wrong_order (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G0 p) frame (fuel+4) (sourceUintIndexedDelete bDst bIndex)).run (bInput 0 3 (u 2))=
      (.ok Source.RVal.unit,dOldSource) ∧
    (Source.evalE (G0 p) frame (fuel+3) (sourceUintCalldataBind bDst bSrc)).run dOldSource=
      (.ok (.val (.memRef rfl 2)),dReverse) ∧
    (Source.execItems (G0 p) frame (fuel+6) nps none
      (.stmt (.expr (sourceUintIndexedDelete bDst bIndex))
        (.stmt (.expr (sourceUintCalldataBind bDst bSrc)) .nil) : Source.RItems E0 [] false .body BΓ BΓ)
      (bInput 0 3 (u 2)).1).run (.nil,(bInput 0 3 (u 2)).2)=(.ok (.normal dReverse.1),(.nil,dReverse.2)) ∧
    [dOldSource.2.heap.get 0,dOldSource.2.heap.get 1,dOldSource.2.heap.get 2,dOldSource.2.heap.get 3]=
      [some ⟨SU,sourceUintMemory [u 7,u 0,u 0]⟩,some ⟨SU,sourceUintMemory neighbor⟩,none,none] ∧
    [dReverse.2.heap.get 0,dReverse.2.heap.get 1,dReverse.2.heap.get 2,dReverse.2.heap.get 3]=
      [some ⟨SU,sourceUintMemory [u 7,u 0,u 0]⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory payload⟩,none] := by
  have oldAt : SourceUintMemoryAt (bInput 0 3 (u 2)) 0 hp left .dyn := old_at 0 3
  have bound : (u 2).1.toNat<hp.len left .dyn := by
    simp only [Heap.len,MObj.elems_dyn]
    decide
  obtain ⟨ht,write⟩ := source_uint_write (bInput 0 3 (u 2)) 0 old (by rfl) 2 (by decide) (PrimTy.dflt .uint)
  have actualWrite : (Source.deleteLoc (E := E0) (Γ := BΓ) frame (fuel+3) (τ := .int .u256) (.mem 0 2)).run
      (bInput 0 3 (u 2))=(.ok (),dOldSource) := write
  have first := oldAt.eval_delete_of_run (G0 p) frame (fuel+1) bDst bIndex (u 2) rfl rfl bound actualWrite
  have second := source_cd_uint_bind_run (G0 p) frame fuel dOldSource bDst bSrc 0 3 rfl
  rw [actually_decoded] at second
  have firstStatement := source_expr_statement_run (G0 p) frame (fuel+4) nps _ (bInput 0 3 (u 2)) dOldSource _ first
  have secondStatement := source_expr_statement_run (G0 p) frame (fuel+3) nps _ dOldSource dReverse _ second
  exact ⟨first,second,source_items_pair_run (G0 p) frame fuel nps _ _ _ _ _ firstStatement secondStatement,rfl,rfl⟩

/-- Insufficient deletion horizon stops at the actual reached copied state.
It does not undo that already executed copy or expose a target revert machine. -/
theorem delete_reached_timeout (p : Roadmap.Pipeline) :
    (Source.evalE (G0 p) frame 2 (sourceUintIndexedDelete bDst bIndex)).run (bFinal (u 2))=
      (.error .timeout,bFinal (u 2)) ∧
    (bFinal (u 2)).2.heap.get 2=some ⟨SU,sourceUintMemory payload⟩ ∧
    (bFinal (u 2)).2.heap.next=3 := by
  exact ⟨rfl,rfl,rfl⟩


/-- Exact ordered locals and object tables of THIS deletion's index2 prefix,
not the different scalar-producing read prefix from prior controls. -/
theorem delete_prefix_vectors :
    (bInput 0 3 (u 2)).1=.cons (sourceUint (u 2)) (.cons (.cdRef rfl 0 3)
      (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil)))) ∧
    (bFinal (u 2)).1=.cons (sourceUint (u 2)) (.cons (.cdRef rfl 0 3)
      (.cons (.memRef rfl 2) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil)))) ∧
    [(bInput 0 3 (u 2)).2.heap.get 0,(bInput 0 3 (u 2)).2.heap.get 1,
      (bInput 0 3 (u 2)).2.heap.get 2,(bInput 0 3 (u 2)).2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,none,none] ∧
    [(bFinal (u 2)).2.heap.get 0,(bFinal (u 2)).2.heap.get 1,
      (bFinal (u 2)).2.heap.get 2,(bFinal (u 2)).2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory payload⟩,none] ∧
    (bInput 0 3 (u 2)).2.heap.next=2 ∧ (bFinal (u 2)).2.heap.next=3 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.bound_delete_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bound_delete_program
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.delete_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms delete_vectors
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.empty_delete_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms empty_delete_error
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.endpoint_delete_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms endpoint_delete_error
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.delete_omission_and_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms delete_omission_and_alias
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.delete_wrong_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms delete_wrong_order
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.delete_reached_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms delete_reached_timeout
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.delete_prefix_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms delete_prefix_vectors

/-! Ordered actual heterogeneous Source copies and a late decode rejection. -/
private abbrev MCtx : Source.RCtx := (.array .calldata .bool none)::BΓ
private abbrev BA : RefTy := .array (.prim .bool)
private def mixFrame : Source.Fr := {frame with cd := (frame.cd ++ (List.replicate 31 0 ++ [1]) ++ (List.replicate 32 0) ++ (List.replicate 31 0 ++ [1]))}
private def mixBadFrame : Source.Fr := {frame with cd := (frame.cd ++ (List.replicate 31 0 ++ [1]) ++ (List.replicate 32 0) ++ (List.replicate 31 0 ++ [2]))}
private def mixInput : Source.EMState E0 MCtx := (.cons (.cdRef rfl 96 3) (bInput 0 3 (u 0)).1,(bInput 0 3 (u 0)).2)
private def mixUDst : Source.Idx MCtx SU := .there bDst
private def mixUSrc : Source.Idx MCtx CD := .there bSrc
private def mixBSrc : Source.Idx MCtx (.array .calldata .bool none) := .here
private def mixMid : Source.EMState E0 MCtx := (mixInput.1.set mixUDst (.memRef rfl 2),bMid.2)
private def mixBPayload : List Bool := [true,false,true]
private def mixBObject : MObj (H++[A]) BA := ⟨mixBPayload,by decide⟩
private def mixPair := out.alloc mixBObject
private def mixBe := List.prefix_append (H++[A]) [BA]
private def mixExt := (List.prefix_append H [A]).trans mixBe
private def mixFinal : Source.EMState E0 MCtx :=
  (mixMid.1,{mixMid.2 with heap := (mixMid.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory mixBPayload⟩).1})
private def mixProgram : Source.RItems E0 [] false .body MCtx MCtx :=
  .stmt (.expr (sourceUintCalldataBind mixUDst mixUSrc)) (.stmt (.expr (sourceBoolCalldataCopy mixBSrc)) .nil)
private theorem mixMemOK : Source.MemOK E0 SH mixInput :=
  ⟨⟨(bMemOK 0 3 (u 0)).1.1,⟨trivial,(bMemOK 0 3 (u 0)).1.2⟩⟩,(bMemOK 0 3 (u 0)).2⟩
private theorem mixUintDecoded : sourceCalldataUintValues E0 mixFrame 0 3=.ok decoded := rfl
private theorem mixBoolDecoded : sourceCalldataBoolValues E0 mixFrame 96 3=.ok [.bool true,.bool false,.bool true] := rfl
private theorem mixBadUintDecoded : sourceCalldataUintValues E0 mixBadFrame 0 3=.ok decoded := rfl
private theorem mixBadBoolDecoded : sourceCalldataBoolValues E0 mixBadFrame 96 3=.error (.revert []) := rfl

/-- Both pipelines execute two different real decoders and allocations, with
uint binding retained while the Boolean expression result is discarded. -/
theorem mixed_copy_program (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G0 p) mixFrame (fuel+4) (sourceUintCalldataBind mixUDst mixUSrc)).run mixInput=
      (.ok (.val (.memRef rfl 2)),mixMid) ∧
    (Source.evalE (G0 p) mixFrame (fuel+3) (sourceBoolCalldataCopy mixBSrc)).run mixMid=
      (.ok (.val (.memRef rfl 3)),mixFinal) ∧
    (Source.execItems (G0 p) mixFrame (fuel+6) nps none mixProgram mixInput.1).run (.nil,mixInput.2)=
      (.ok (.normal mixFinal.1),(.nil,mixFinal.2)) ∧
    checkedSourceFreshUints (E := E0) mixFrame 0 3 hp (by decide)=.ok (some out) ∧
    checkedSourceFreshBools (E := E0) mixFrame 96 3 out (by decide)=.ok (some mixPair.1) ∧
    Heap.Keeps mixBe out mixPair.1 ∧ Heap.Keeps mixExt hp mixPair.1 ∧
    SourceUintMemoryAt mixFinal 2 mixPair.1 (fresh.wk mixBe) .dyn ∧
    SourceBoolMemoryAt mixFinal 3 mixPair.1 mixPair.2 .dyn ∧ Source.MemOK E0 SH mixFinal ∧
    SourceUintMemoryAt mixFinal 0 mixPair.1 (left.wk mixExt) .dyn ∧
    SourceUintMemoryAt mixFinal 1 mixPair.1 (right.wk mixExt) .dyn ∧
    fresh.id=2 ∧ mixPair.2.id=3 ∧ fresh.id≠mixPair.2.id := by
  have result := source_cd_uint_bind_bool_copy mixInput hp (G0 p) mixFrame fuel nps mixUDst mixUSrc mixBSrc
    0 3 96 3 rfl rfl (by decide) (by decide) SH mixMemOK
  rw [mixUintDecoded,mixBoolDecoded] at result
  obtain ⟨uv,first,ua,uk,ur,um,bv,second,program,ba,bk,fu,fb,fm,occupied,uid,bid,ne,sne,locals,ex,events,logs,fn⟩ := result
  have keep : Heap.Keeps mixExt hp mixPair.1 := uk.trans bk
  have initialOld : SourceUintMemoryAt mixInput 0 hp left .dyn := old_at 0 3
  have initialNeighbor : SourceUintMemoryAt mixInput 1 hp right .dyn := neighbor_at 0 3
  exact ⟨first,second,program,ua,ba,bk,keep,fu,fb,fm,
    initialOld.transport keep occupied,initialNeighbor.transport keep occupied,uid,bid,ne⟩

/-- Complete ordered Source tables/local vectors and both native element types. -/
theorem mixed_copy_vectors :
    mixInput.1=.cons (.cdRef rfl 96 3) (.cons (sourceUint (u 0)) (.cons (.cdRef rfl 0 3)
      (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil))))) ∧
    mixMid.1=.cons (.cdRef rfl 96 3) (.cons (sourceUint (u 0)) (.cons (.cdRef rfl 0 3)
      (.cons (.memRef rfl 2) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil))))) ∧ mixFinal.1=mixMid.1 ∧
    [mixInput.2.heap.get 0,mixInput.2.heap.get 1,mixInput.2.heap.get 2,mixInput.2.heap.get 3,mixInput.2.heap.get 4]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,none,none,none] ∧
    [mixMid.2.heap.get 0,mixMid.2.heap.get 1,mixMid.2.heap.get 2,mixMid.2.heap.get 3,mixMid.2.heap.get 4]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory payload⟩,none,none] ∧
    [mixFinal.2.heap.get 0,mixFinal.2.heap.get 1,mixFinal.2.heap.get 2,mixFinal.2.heap.get 3,mixFinal.2.heap.get 4]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory payload⟩,
        some ⟨SourceBoolArrayTy,sourceBoolMemory mixBPayload⟩,none] ∧
    [MObj.elems .dyn (mixPair.1.get (left.wk mixExt)),MObj.elems .dyn (mixPair.1.get (right.wk mixExt)),
      MObj.elems .dyn (mixPair.1.get (fresh.wk mixBe))]=[old,neighbor,payload] ∧
    MObj.elems .dyn (mixPair.1.get mixPair.2)=mixBPayload ∧
    [mixInput.2.heap.next,mixMid.2.heap.next,mixFinal.2.heap.next]=[2,3,4] ∧
    mixFinal.2.ex=mixInput.2.ex ∧ mixFinal.2.events=mixInput.2.events ∧ mixFinal.2.logs=mixInput.2.logs ∧
    mixFinal.2.fnLocals=mixInput.2.fnLocals := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · obtain ⟨_,_,_,_,_,bk,keep,_,_,_,_,_,_,_,_⟩ := mixed_copy_program .legacy 0 0
    have original : MObj.elems .dyn (out.get fresh)=payload := by
      unfold out fresh
      rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
      exact List.map_id'' (fun _ => rfl) _
    rw [keep left,keep right,bk fresh,MObj.elems_wk,MObj.elems_wk,MObj.elems_wk,original]
    simp only [MObj.elems_dyn,
      List.map_id'' (f := MVal.wk mixExt (.prim .uint)) (fun _ => rfl),
      List.map_id'' (f := MVal.wk mixBe (.prim .uint)) (fun _ => rfl)]
    rfl
  · unfold mixPair
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
    exact List.map_id'' (fun _ => rfl) _

/-- The Boolean decoder reads true/false before its actual third word2 fails.
The UINT copy, changed destination binding and allocation survive that halt. -/
theorem mixed_copy_late_error (p : Roadmap.Pipeline) (fuel nps : Nat) :
    sourceCalldataBoolValues E0 mixBadFrame 96 2=.ok [.bool true,.bool false] ∧
    (Source.evalE (G0 p) mixBadFrame (fuel+4) (sourceUintCalldataBind mixUDst mixUSrc)).run mixInput=
      (.ok (.val (.memRef rfl 2)),mixMid) ∧
    (Source.evalE (G0 p) mixBadFrame (fuel+3) (sourceBoolCalldataCopy mixBSrc)).run mixMid=
      (.error (.revert []),mixMid) ∧
    (Source.execItems (G0 p) mixBadFrame (fuel+6) nps none mixProgram mixInput.1).run (.nil,mixInput.2)=
      (.error (.revert []),(.nil,mixMid.2)) ∧
    checkedSourceFreshUints (E := E0) mixBadFrame 0 3 hp (by decide)=.ok (some out) ∧
    checkedSourceFreshBools (E := E0) mixBadFrame 96 3 out (by decide)=.error (.revert []) ∧
    SourceUintMemoryAt mixMid 2 out fresh .dyn ∧ Source.MemOK E0 SH mixMid ∧
    [mixMid.2.heap.get 0,mixMid.2.heap.get 1,mixMid.2.heap.get 2,mixMid.2.heap.get 3,mixMid.2.heap.get 4]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory payload⟩,none,none] ∧
    mixMid.2.heap.next=3 ∧ mixMid.1.get mixUDst=.memRef rfl 2 := by
  have result := source_cd_uint_bind_bool_copy mixInput hp (G0 p) mixBadFrame fuel nps mixUDst mixUSrc mixBSrc
    0 3 96 3 rfl rfl (by decide) (by decide) SH mixMemOK
  rw [mixBadUintDecoded,mixBadBoolDecoded] at result
  obtain ⟨uv,first,ua,uk,ur,um,second,program,ba⟩ := result
  exact ⟨rfl,first,second,program,ua,ba,ur,um,rfl,rfl,rfl⟩

private def mixReverseMid : Source.EMState E0 MCtx :=
  (mixInput.1,{mixInput.2 with heap := (mixInput.2.heap.alloc ⟨SourceBoolArrayTy,sourceBoolMemory mixBPayload⟩).1})
private def mixReverseFinal : Source.EMState E0 MCtx :=
  (mixInput.1.set mixUDst (.memRef rfl 3),
    {mixReverseMid.2 with heap := (mixReverseMid.2.heap.alloc ⟨SU,sourceUintMemory payload⟩).1})

/-- Swapping the real statements swaps allocation types/IDs and changes the
retained numeric local2 to3, even though both input payloads are unchanged. -/
theorem mixed_copy_wrong_order (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G0 p) mixFrame (fuel+4) (sourceBoolCalldataCopy mixBSrc)).run mixInput=
      (.ok (.val (.memRef rfl 2)),mixReverseMid) ∧
    (Source.evalE (G0 p) mixFrame (fuel+3) (sourceUintCalldataBind mixUDst mixUSrc)).run mixReverseMid=
      (.ok (.val (.memRef rfl 3)),mixReverseFinal) ∧
    (Source.execItems (G0 p) mixFrame (fuel+6) nps none
      (.stmt (.expr (sourceBoolCalldataCopy mixBSrc)) (.stmt (.expr (sourceUintCalldataBind mixUDst mixUSrc)) .nil) :
        Source.RItems E0 [] false .body MCtx MCtx) mixInput.1).run (.nil,mixInput.2)=
      (.ok (.normal mixReverseFinal.1),(.nil,mixReverseFinal.2)) ∧
    [mixReverseMid.2.heap.get 0,mixReverseMid.2.heap.get 1,mixReverseMid.2.heap.get 2,mixReverseMid.2.heap.get 3,mixReverseMid.2.heap.get 4]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SourceBoolArrayTy,sourceBoolMemory mixBPayload⟩,none,none] ∧
    [mixReverseFinal.2.heap.get 0,mixReverseFinal.2.heap.get 1,mixReverseFinal.2.heap.get 2,mixReverseFinal.2.heap.get 3,mixReverseFinal.2.heap.get 4]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SourceBoolArrayTy,sourceBoolMemory mixBPayload⟩,
        some ⟨SU,sourceUintMemory payload⟩,none] ∧
    mixFinal.1.get mixUDst=.memRef rfl 2 ∧ mixReverseFinal.1.get mixUDst=.memRef rfl 3 := by
  have first := source_cd_bool_eval (G0 p) mixFrame (fuel+2) mixInput mixBSrc 96 3 rfl
  rw [source_cd_bool_run,mixBoolDecoded] at first
  have second := source_cd_uint_bind_run (G0 p) mixFrame fuel mixReverseMid mixUDst mixUSrc 0 3 rfl
  rw [mixUintDecoded] at second
  have firstStmt := source_expr_statement_run (G0 p) mixFrame (fuel+4) nps _ mixInput mixReverseMid _ first
  have secondStmt := source_expr_statement_run (G0 p) mixFrame (fuel+3) nps _ mixReverseMid mixReverseFinal _ second
  exact ⟨first,second,source_items_pair_run (G0 p) mixFrame fuel nps _ _ _ _ _ firstStmt secondStmt,rfl,rfl,rfl,rfl⟩


/-- Actual final reads distinguish the retained old alias/neighbor from the
rebound fresh uint local, plus the independently typed fresh Boolean contents. -/
theorem mixed_copy_reached_reads (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) mixFrame (fuel+2)
      (.indexArray (.local mixUDst) (.local (.there bIndex)) rfl)).run mixFinal=
      (.ok (.val (sourceUint (u 2))),mixFinal) ∧
    (Source.evalE (G0 p) mixFrame (fuel+2)
      (.indexArray (.local (.there bAlias)) (.local (.there bIndex)) rfl)).run mixFinal=
      (.ok (.val (sourceUint (u 7))),mixFinal) ∧
    (Source.evalE (G0 p) mixFrame (fuel+2)
      (.indexArray (.local (.there bNeighbor)) (.local (.there bIndex)) rfl)).run mixFinal=
      (.ok (.val (sourceUint (u 8))),mixFinal) ∧
    (Source.readLoc (E := E0) (Γ := MCtx) mixFrame (τ := .bool) (.mem 3 1)).run mixFinal=
      (.ok (.bool false),mixFinal) := by
  obtain ⟨_,_,_,_,_,_,_,ur,br,_,oldAt,neighborAt,_,_,_⟩ := mixed_copy_program p fuel 0
  obtain ⟨_,_,_,_,_,_,vs,bs,_,_,_,_,_⟩ := mixed_copy_vectors
  have oldValues : MObj.elems .dyn (mixPair.1.get (left.wk mixExt))=old := (List.cons.inj vs).1
  have neighborValues : MObj.elems .dyn (mixPair.1.get (right.wk mixExt))=neighbor := (List.cons.inj (List.cons.inj vs).2).1
  have freshValues : MObj.elems .dyn (mixPair.1.get (fresh.wk mixBe))=payload :=
    (List.cons.inj (List.cons.inj (List.cons.inj vs).2).2).1
  have oldBound : (u 0).1.toNat<mixPair.1.len (left.wk mixExt) .dyn := by
    unfold Heap.len
    rw [oldValues]
    decide
  have neighborBound : (u 0).1.toNat<mixPair.1.len (right.wk mixExt) .dyn := by
    unfold Heap.len
    rw [neighborValues]
    decide
  have freshBound : (u 0).1.toNat<mixPair.1.len (fresh.wk mixBe) .dyn := by
    unfold Heap.len
    rw [freshValues]
    decide
  have readFresh := ur.eval_index (G0 p) mixFrame fuel mixUDst (.there bIndex) (u 0) rfl rfl freshBound
  have readOld := oldAt.eval_index (G0 p) mixFrame fuel (.there bAlias) (.there bIndex) (u 0) rfl rfl oldBound
  have readNeighbor := neighborAt.eval_index (G0 p) mixFrame fuel (.there bNeighbor) (.there bIndex) (u 0) rfl rfl neighborBound
  simp only [freshValues] at readFresh
  simp only [oldValues] at readOld
  simp only [neighborValues] at readNeighbor
  refine ⟨readFresh,readOld,readNeighbor,?_⟩
  apply (br.read_iff mixFrame (u 1) false).mpr
  change (MObj.elems .dyn (mixPair.1.get mixPair.2))[1]?=some false
  rw [bs]
  rfl

/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.mixed_copy_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mixed_copy_program
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.mixed_copy_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mixed_copy_vectors
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.mixed_copy_late_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mixed_copy_late_error
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.mixed_copy_wrong_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mixed_copy_wrong_order
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.mixed_copy_reached_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mixed_copy_reached_reads
private def rawFrame : Source.Fr := {F0 with cd := [171,205,239]++Source.natBytes 32 7++Source.natBytes 32 42}
private def rawShort : Source.Fr := {F0 with cd := [171,205,239]++Source.natBytes 32 7}
private def rawPayload : List PrimTy.uint.Denote := [u 7,u 42]
private theorem rawValues : CalldataPackets.RawUint.payload rawFrame 3 2=rawPayload := by decide
private def rawPair := hp.alloc (R := A) (⟨rawPayload,by decide⟩ : MObj H A)
private def rawMid (k : PrimTy.uint.Denote) : Source.EMState E0 BΓ :=
  ((bInput 3 2 k).1.set bDst (.memRef rfl 2),
    {(bInput 3 2 k).2 with heap := ((bInput 3 2 k).2.heap.alloc ⟨SU,sourceUintMemory rawPayload⟩).1})
private def rawDone : Source.EMState E0 BΓ :=
  ((rawMid (u 1)).1,{(rawMid (u 1)).2 with heap := (rawMid (u 1)).2.heap.write 2 (sourceUintMemory [u 7,u 0]) (by rfl)})
private def rawHeap : Heap (H++[A]) := rawPair.1.set rawPair.2
  (MObj.setElem .dyn (rawPair.1.get rawPair.2) 1 (PrimTy.dflt .uint))
private theorem rawAt : SourceUintMemoryAt (rawMid (u 1)) 2 rawPair.1 rawPair.2 .dyn := by
  unfold SourceUintMemoryAt rawPair
  rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
  rw [List.map_id'' (f := MVal.wk (List.prefix_append H [A]) (.prim .uint)) (fun _ => rfl)]
  rfl

/-- Actual nonzero-offset bytes produce both unequal words, then the SAME
Source Items program deletes42 through the new root while old aliases survive. -/
theorem raw_delete_program (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G0 p) rawFrame (fuel+4) (sourceUintCalldataBind bDst bSrc)).run (bInput 3 2 (u 1))=
      (.ok (.val (.memRef rfl 2)),rawMid (u 1)) ∧
    (Source.evalE (G0 p) rawFrame (fuel+3) (sourceUintIndexedDelete bDst bIndex)).run (rawMid (u 1))=(.ok Source.RVal.unit,rawDone) ∧
    (Source.execItems (G0 p) rawFrame (fuel+6) nps none dProgram (bInput 3 2 (u 1)).1).run (.nil,(bInput 3 2 (u 1)).2)=
      (.ok (.normal rawDone.1),(.nil,rawDone.2)) ∧
    rawPair.1.writeAddr (.index rawPair.2 .dyn (u 1)) (PrimTy.dflt .uint)=some rawHeap ∧
    SourceUintMemoryAt rawDone 2 rawHeap rawPair.2 .dyn ∧ Source.MemOK E0 SH rawDone ∧
    Heap.Keeps (List.prefix_append H [A]) hp rawHeap ∧
    SourceUintMemoryAt rawDone 0 rawHeap (left.wk (List.prefix_append H [A])) .dyn ∧
    SourceUintMemoryAt rawDone 1 rawHeap (right.wk (List.prefix_append H [A])) .dyn := by
  first
  | solve | rfl | simp only [] | omega
  | have result := source_raw_uint_bind_delete (bInput 3 2 (u 1)) hp (G0 p) rawFrame fuel nps
      bDst bSrc bIndex 3 2 (u 1) rfl rfl (by decide) (by decide) SH (bMemOK 3 2 (u 1))
    rw [rawValues] at result
    obtain ⟨valid,native,zs,first,second,program,adapter,hw,new,mok,keep,values,occupied,locals,ex,events,logs,fn⟩ := result
    have size : (u 1).1.toNat<(MObj.elems .dyn (rawPair.1.get rawPair.2)).length := by
      unfold rawPair
      rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn,List.length_map];decide
    have nativeRun : rawPair.1.writeAddr (.index rawPair.2 .dyn (u 1)) (PrimTy.dflt .uint)=some rawHeap := by
      simp only [Heap.writeAddr,Heap.setIndex,size,↓reduceIte];rfl
    have sameNative : native=rawHeap := Option.some.inj (hw.symm.trans nativeRun)
    subst native
    obtain ⟨ht,write⟩ := source_uint_write (rawMid (u 1)) 2 rawPayload (by rfl) 1 (by decide) (PrimTy.dflt .uint)
    have actualWrite : (Source.deleteLoc (E := E0) (Γ := BΓ) rawFrame (fuel+2) (τ := .int .u256) (.mem 2 1)).run (rawMid (u 1))=(.ok (),rawDone) := write
    have actual := rawAt.eval_delete_of_run (G0 p) rawFrame fuel bDst bIndex (u 1) rfl rfl size actualWrite
    have sameSource : zs=rawDone := congrArg Prod.snd (second.symm.trans actual)
    subst zs
    have oldInitial : SourceUintMemoryAt (bInput 3 2 (u 1)) 0 hp left .dyn := old_at 3 2
    have neighborInitial : SourceUintMemoryAt (bInput 3 2 (u 1)) 1 hp right .dyn := neighbor_at 3 2
    exact ⟨first,second,program,nativeRun,new,mok,keep,oldInitial.transport keep occupied,neighborInitial.transport keep occupied⟩

/-- Complete ordered Source object/local tables and typed contents at input,
copy prefix and final delete; no projected word target image is invented. -/
theorem raw_delete_vectors :
    [(bInput 3 2 (u 1)).2.heap.get 0,(bInput 3 2 (u 1)).2.heap.get 1,(bInput 3 2 (u 1)).2.heap.get 2,(bInput 3 2 (u 1)).2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,none,none] ∧
    [(rawMid (u 1)).2.heap.get 0,(rawMid (u 1)).2.heap.get 1,(rawMid (u 1)).2.heap.get 2,(rawMid (u 1)).2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory [u 7,u 42]⟩,none] ∧
    [rawDone.2.heap.get 0,rawDone.2.heap.get 1,rawDone.2.heap.get 2,rawDone.2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory [u 7,u 0]⟩,none] ∧
    (bInput 3 2 (u 1)).1=.cons (sourceUint (u 1)) (.cons (.cdRef rfl 3 2)
      (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil)))) ∧
    rawDone.1=.cons (sourceUint (u 1)) (.cons (.cdRef rfl 3 2)
      (.cons (.memRef rfl 2) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil)))) ∧
    (rawMid (u 1)).1=rawDone.1 ∧
    (MObj.elems .dyn (rawHeap.get (left.wk (List.prefix_append H [A]))),
     MObj.elems .dyn (rawHeap.get (right.wk (List.prefix_append H [A]))),MObj.elems .dyn (rawHeap.get rawPair.2))=
      (old,neighbor,[u 7,u 0]) ∧
    (rawPair.2.id,(bInput 3 2 (u 1)).2.heap.next,(rawMid (u 1)).2.heap.next,rawDone.2.heap.next)=(2,2,3,3) ∧
    (rawDone.2.ex,rawDone.2.events,rawDone.2.logs,rawDone.2.fnLocals)=
      ((bInput 3 2 (u 1)).2.ex,(bInput 3 2 (u 1)).2.events,(bInput 3 2 (u 1)).2.logs,(bInput 3 2 (u 1)).2.fnLocals) := by
  first
  | solve | rfl | simp only [] | omega
  | refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_,rfl,rfl⟩
    simp only [rawHeap,rawPair,Heap.get,Objs.get,Heap.set,Objs.set,hp,left,right,MObj.elems_dyn,MObj.setElem_dyn]
    rfl

/-- Endpoint2 rejects only AFTER the actual copied root was bound. -/
theorem raw_delete_endpoint (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G0 p) rawFrame (fuel+4) (sourceUintCalldataBind bDst bSrc)).run (bInput 3 2 (u 2))=
      (.ok (.val (.memRef rfl 2)),rawMid (u 2)) ∧
    (Source.evalE (G0 p) rawFrame (fuel+3) (sourceUintIndexedDelete bDst bIndex)).run (rawMid (u 2))=
      (.error (.revert (Source.panicData .index)),rawMid (u 2)) ∧
    (Source.execItems (G0 p) rawFrame (fuel+6) nps none dProgram (bInput 3 2 (u 2)).1).run (.nil,(bInput 3 2 (u 2)).2)=
      (.error (.revert (Source.panicData .index)),(.nil,(rawMid (u 2)).2)) ∧
    rawPair.1.writeAddr (.index rawPair.2 .dyn (u 2)) (PrimTy.dflt .uint)=none ∧
    SourceUintMemoryAt (rawMid (u 2)) 2 rawPair.1 rawPair.2 .dyn := by
  first
  | solve | rfl | simp only [] | omega
  | have result := source_raw_uint_bind_delete_bounds (bInput 3 2 (u 2)) hp (G0 p) rawFrame fuel nps
      bDst bSrc bIndex 3 2 (u 2) rfl rfl (by decide) (by decide) SH (bMemOK 3 2 (u 2))
    rw [rawValues] at result
    obtain ⟨valid,first,second,program,adapter,hw,new,rest⟩ := result
    exact ⟨first,second,program,hw,new⟩

/-- Standalone short copies really zero-pad; this is NOT entry rejection. -/
theorem raw_short_padding : CalldataPackets.RawUint.payload rawShort 3 2=[u 7,u 0] ∧
    (Source.cdToMem (E := E0) (Γ := BΓ) rawShort SU 3 2).run (bInput 3 2 (u 1))=
      (.ok (.val (.memRef rfl 2)),((bInput 3 2 (u 1)).1,
        {(bInput 3 2 (u 1)).2 with heap := ((bInput 3 2 (u 1)).2.heap.alloc ⟨SU,sourceUintMemory [u 7,u 0]⟩).1})) := by
  first
  | solve | rfl | simp only [] | omega
  | have values : CalldataPackets.RawUint.payload rawShort 3 2=[u 7,u 0] := by decide
    refine ⟨values,?_⟩
    rw [CalldataPackets.RawUint.copy_run,values]
    rfl

/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.raw_delete_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_delete_program
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.raw_delete_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_delete_vectors
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.raw_delete_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_delete_endpoint
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.raw_short_padding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_short_padding

/-- Actual prefix/read and final/read distinguish skipped deletion and stale
root selection; all reads are existing Source syntax on the reached heaps. -/
theorem raw_delete_reads (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) rawFrame (fuel+2) (.indexArray (.local bDst) (.local bIndex) rfl)).run (rawMid (u 1))=
      (.ok (.val (sourceUint (u 42))),rawMid (u 1)) ∧
    (Source.evalE (G0 p) rawFrame (fuel+2) (.indexArray (.local bDst) (.local bIndex) rfl)).run rawDone=
      (.ok (.val (sourceUint (u 0))),rawDone) ∧
    (Source.evalE (G0 p) rawFrame (fuel+2) (.indexArray (.local bAlias) (.local bIndex) rfl)).run rawDone=
      (.ok (.val (sourceUint (u 0))),rawDone) ∧
    (sourceUint (D := E0.layout) (u 42))≠sourceUint (u 0) := by
  first
  | solve | rfl | simp only [] | omega
  | have values : MObj.elems .dyn (rawPair.1.get rawPair.2)=[u 7,u 42] := by
      unfold rawPair
      rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn,List.map_id'' (f := MVal.wk (List.prefix_append H [A]) (.prim .uint)) (fun _ => rfl)]
      rfl
    have beforeBound : (u 1).1.toNat<rawPair.1.len rawPair.2 .dyn := by
      change (u 1).1.toNat<(MObj.elems .dyn (rawPair.1.get rawPair.2)).length
      rw [values];decide
    have client := raw_delete_program p 0 0
    have after := client.2.2.2.2.1
    have oldAlias := client.2.2.2.2.2.2.2.1
    have keep : Heap.Keeps (List.prefix_append H [A]) hp rawHeap := client.2.2.2.2.2.2.1
    have afterValues : MObj.elems .dyn (rawHeap.get rawPair.2)=[u 7,u 0] := by
      unfold rawHeap
      rw [Heap.get_set_same,MObj.elems_setElem,values];rfl
    have afterBound : (u 1).1.toNat<rawHeap.len rawPair.2 .dyn := by
      change (u 1).1.toNat<(MObj.elems .dyn (rawHeap.get rawPair.2)).length
      rw [afterValues];decide
    have oldValues : MObj.elems .dyn (rawHeap.get (left.wk (List.prefix_append H [A])))=old := by
      rw [keep left,MObj.elems_wk,MObj.elems_dyn,List.map_id'' (f := MVal.wk (List.prefix_append H [A]) (.prim .uint)) (fun _ => rfl)]
      rfl
    have oldBound : (u 1).1.toNat<rawHeap.len (left.wk (List.prefix_append H [A])) .dyn := by
      change (u 1).1.toNat<(MObj.elems .dyn (rawHeap.get (left.wk (List.prefix_append H [A])))).length
      rw [oldValues];decide
    have a := rawAt.eval_index (G0 p) rawFrame fuel bDst bIndex (u 1) rfl rfl beforeBound
    have b := after.eval_index (G0 p) rawFrame fuel bDst bIndex (u 1) rfl rfl afterBound
    have c := oldAlias.eval_index (G0 p) rawFrame fuel bAlias bIndex (u 1) rfl rfl oldBound
    have different : (sourceUint (D := E0.layout) (u 42))≠sourceUint (u 0) := by
      intro same
      have converted := congrArg (fun v : Source.Val E0.layout (.int .u256) => calldataUint (.val v)) same
      exact (by decide : u 42≠u 0) (by simpa only [calldataUint_sourceUint] using converted)
    refine ⟨?_,?_,?_,different⟩
    · simpa only [values,List.getElem_cons_succ,List.getElem_cons_zero] using a
    · simpa only [afterValues,List.getElem_cons_succ,List.getElem_cons_zero] using b
    · simpa only [oldValues,old,List.getElem_cons_succ,List.getElem_cons_zero] using c

/-- Horizon5 retains the ACTUAL copy/bind prefix before suffix timeout.
The Items outcome exposes globals, not a returned local environment. -/
theorem raw_delete_late_timeout (p : Roadmap.Pipeline) (nps : Nat) :
    (Source.execItems (G0 p) rawFrame 5 nps none dProgram (bInput 3 2 (u 1)).1).run (.nil,(bInput 3 2 (u 1)).2)=
      (.error .timeout,(.nil,(rawMid (u 1)).2)) := by
  first
  | solve | rfl | simp only [] | omega
  | have first : (Source.evalE (G0 p) rawFrame 3 (sourceUintCalldataBind bDst bSrc)).run (bInput 3 2 (u 1))=
        (.ok (.val (.memRef rfl 2)),rawMid (u 1)) := by
      rw [source_cd_uint_bind_run (G0 p) rawFrame 0 (bInput 3 2 (u 1)) bDst bSrc 3 2 rfl,
        source_cd_uint_values_raw]
      dsimp only
      rw [source_uint_payload_sourceUint,rawValues]
      rfl
    have statement := source_expr_statement_run (G0 p) rawFrame 3 nps _ _ _ _ first
    rw [dProgram,Source.execItems,Source.Hoare.run_bind,statement]
    rfl

/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.raw_delete_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_delete_reads
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.raw_delete_late_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_delete_late_timeout

private def entrySelector : List UInt8 := [222,173,190,239]
private def entryData : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 2++Source.natBytes 32 7++Source.natBytes 32 42
private def entryTruncated : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 2++Source.natBytes 32 7
private def entryZero : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 0
private def entryLarge : List UInt8 := Source.natBytes 32 32++Source.natBytes 32 (2^64)
private def entryFrame (data : List UInt8) : Source.Fr := {F0 with cd := entrySelector++data}
private theorem entryOff : Source.wordAt entryData 0=32 := by decide
private theorem entryLen : Source.wordAt (entryData.drop 32) 0=2 := by decide
private theorem entryBytes : entryData.length=128 := by
  simp only [entryData,Source.natBytes,List.length_append,Source.beBytes_length]
private theorem entryValues : CalldataPackets.RawUint.dataPayload entryData 64 2=rawPayload := by decide
private def entryMid (k : PrimTy.uint.Denote) : Source.EMState E0 BΓ :=
  ((bInput 68 2 k).1.set bDst (.memRef rfl 2),(rawMid k).2)
private def entryDone : Source.EMState E0 BΓ := ((entryMid (u 1)).1,rawDone.2)

/-- Full actual entry guard -> Items program, linked to the same byte-derived
fresh root, with old Source/native objects framed. Both pipelines quantified. -/
theorem guarded_entry_delete_program (p : Roadmap.Pipeline) (fuel nps : Nat) :
    Source.cdTail entryData 0 32=.ok (68,2) ∧
    (Source.evalE (G0 p) (entryFrame entryData) (fuel+4) (sourceUintCalldataBind bDst bSrc)).run (bInput 68 2 (u 1))=
      (.ok (.val (.memRef rfl 2)),entryMid (u 1)) ∧
    (Source.evalE (G0 p) (entryFrame entryData) (fuel+3) (sourceUintIndexedDelete bDst bIndex)).run (entryMid (u 1))=
      (.ok Source.RVal.unit,entryDone) ∧
    (sourceGuardedUintDelete (G0 p) (entryFrame entryData) fuel nps bDst bSrc bIndex entryData 0 (bInput 68 2 (u 1)).1).run (.nil,(bInput 68 2 (u 1)).2)=
      (.ok (.normal entryDone.1),(.nil,entryDone.2)) ∧
    rawPair.1.writeAddr (.index rawPair.2 .dyn (u 1)) (PrimTy.dflt .uint)=some rawHeap ∧
    SourceUintMemoryAt entryDone 2 rawHeap rawPair.2 .dyn ∧ Source.MemOK E0 SH entryDone ∧
    Heap.Keeps (List.prefix_append H [A]) hp rawHeap ∧
    SourceUintMemoryAt entryDone 0 rawHeap (left.wk (List.prefix_append H [A])) .dyn ∧
    SourceUintMemoryAt entryDone 1 rawHeap (right.wk (List.prefix_append H [A])) .dyn := by
  first
  | solve | rfl | simp only [] | omega
  | have result := source_guarded_uint_bind_delete (bInput 68 2 (u 1)) hp (G0 p) (entryFrame entryData) fuel nps
      bDst bSrc bIndex entrySelector entryData rfl rfl 0 (u 1)
      (by rw [entryOff,entryLen];rfl) rfl
      (by rw [entryOff,entryLen];decide) (by rw [entryOff,entryLen,entryBytes];decide)
      (by rw [entryOff,entryLen];decide) SH (bMemOK 68 2 (u 1))
    simp only [entryOff,entryLen,entryValues] at result
    obtain ⟨guard,valid,native,zs,first,second,program,adapter,hw,new,mok,keep,values,occupied,locals,ex,events,logs,fn,guarded⟩ := result
    have nativeRun := (raw_delete_program p 0 0).2.2.2.1
    have sameNative : native=rawHeap := Option.some.inj (hw.symm.trans nativeRun)
    subst native
    have before : SourceUintMemoryAt (entryMid (u 1)) 2 rawPair.1 rawPair.2 .dyn := rawAt
    have size : (u 1).1.toNat<rawPair.1.len rawPair.2 .dyn := by
      unfold rawPair Heap.len
      rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn,List.length_map];decide
    obtain ⟨ht,write⟩ := source_uint_write (entryMid (u 1)) 2 rawPayload (by rfl) 1 (by decide) (PrimTy.dflt .uint)
    have actualWrite : (Source.deleteLoc (E := E0) (Γ := BΓ) (entryFrame entryData) (fuel+2) (τ := .int .u256) (.mem 2 1)).run (entryMid (u 1))=(.ok (),entryDone) := write
    have actual := before.eval_delete_of_run (G0 p) (entryFrame entryData) fuel bDst bIndex (u 1) rfl rfl size actualWrite
    have sameSource : zs=entryDone := congrArg Prod.snd (second.symm.trans actual)
    subst zs
    have oldInitial : SourceUintMemoryAt (bInput 68 2 (u 1)) 0 hp left .dyn := old_at 68 2
    have neighborInitial : SourceUintMemoryAt (bInput 68 2 (u 1)) 1 hp right .dyn := neighbor_at 68 2
    exact ⟨guard,first,second,guarded,nativeRun,new,mok,keep,oldInitial.transport keep occupied,neighborInitial.transport keep occupied⟩

/-- Complete initial/prefix/final object tables, locals and frame values are
retained; the shifted Source view really points after selector and length. -/
theorem guarded_entry_vectors :
    [(bInput 68 2 (u 1)).2.heap.get 0,(bInput 68 2 (u 1)).2.heap.get 1,(bInput 68 2 (u 1)).2.heap.get 2,(bInput 68 2 (u 1)).2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,none,none] ∧
    [(entryMid (u 1)).2.heap.get 0,(entryMid (u 1)).2.heap.get 1,(entryMid (u 1)).2.heap.get 2,(entryMid (u 1)).2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory [u 7,u 42]⟩,none] ∧
    [entryDone.2.heap.get 0,entryDone.2.heap.get 1,entryDone.2.heap.get 2,entryDone.2.heap.get 3]=
      [some ⟨SU,sourceUintMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,some ⟨SU,sourceUintMemory [u 7,u 0]⟩,none] ∧
    (bInput 68 2 (u 1)).1=.cons (sourceUint (u 1)) (.cons (.cdRef rfl 68 2)
      (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil)))) ∧
    entryDone.1=.cons (sourceUint (u 1)) (.cons (.cdRef rfl 68 2)
      (.cons (.memRef rfl 2) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil)))) ∧
    (entryMid (u 1)).1=entryDone.1 ∧
    ((entryMid (u 1)).2.heap.next,entryDone.2.heap.next,rawPair.2.id)=(3,3,2) ∧
    (MObj.elems .dyn (rawHeap.get (left.wk (List.prefix_append H [A]))),
     MObj.elems .dyn (rawHeap.get (right.wk (List.prefix_append H [A]))),MObj.elems .dyn (rawHeap.get rawPair.2))=
      (old,neighbor,[u 7,u 0]) ∧
    (entryDone.2.ex,entryDone.2.events,entryDone.2.logs,entryDone.2.fnLocals)=
      ((bInput 68 2 (u 1)).2.ex,(bInput 68 2 (u 1)).2.events,(bInput 68 2 (u 1)).2.logs,(bInput 68 2 (u 1)).2.fnLocals) ∧
    (entryFrame entryData).cd=entrySelector++entryData ∧
    ((entryFrame entryData).this,(entryFrame entryData).sender,(entryFrame entryData).value,(entryFrame entryData).static,
      (entryFrame entryData).contract,(entryFrame entryData).checked,(entryFrame entryData).depth)=
      (F0.this,F0.sender,F0.value,F0.static,F0.contract,F0.checked,F0.depth) := by
  first
  | solve | rfl | simp only [] | omega
  | refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,rfl,rfl,rfl⟩
    exact raw_delete_vectors.2.2.2.2.2.2.1

/-- The three real entry refusals preserve the original globals BEFORE copy.
The same short data still admits standalone cdToMem padding, separately below. -/
theorem guarded_entry_refusals (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (sourceGuardedUintDelete (G0 p) (entryFrame entryTruncated) fuel nps bDst bSrc bIndex entryTruncated 0 (bInput 68 2 (u 1)).1).run (.nil,(bInput 68 2 (u 1)).2)=
      (.error (.revert []),(.nil,(bInput 68 2 (u 1)).2)) ∧
    (sourceGuardedUintDelete (G0 p) (entryFrame entryLarge) fuel nps bDst bSrc bIndex entryLarge 0 (bInput 68 2 (u 1)).1).run (.nil,(bInput 68 2 (u 1)).2)=
      (.error (.revert []),(.nil,(bInput 68 2 (u 1)).2)) ∧
    (sourceGuardedUintDelete (G0 p) (entryFrame []) fuel nps bDst bSrc bIndex [] 0 (bInput 68 2 (u 1)).1).run (.nil,(bInput 68 2 (u 1)).2)=
      (.error (.revert []),(.nil,(bInput 68 2 (u 1)).2)) := by
  first
  | solve | rfl | simp only [] | omega
  | refine ⟨?_,?_,?_⟩
    · exact source_guarded_uint_delete_refusal (G0 p) (entryFrame entryTruncated) fuel nps bDst bSrc bIndex entryTruncated 0 (bInput 68 2 (u 1)) (by decide)
    · exact source_guarded_uint_delete_refusal (G0 p) (entryFrame entryLarge) fuel nps bDst bSrc bIndex entryLarge 0 (bInput 68 2 (u 1)) (by decide)
    · exact source_guarded_uint_delete_refusal (G0 p) (entryFrame []) fuel nps bDst bSrc bIndex [] 0 (bInput 68 2 (u 1)) (by decide)

/-- A valid ZERO-length dynamic entry passes its guard and then rejects deletion
on the actual fresh empty array, preserving its allocated prefix globals. -/
theorem guarded_entry_empty (p : Roadmap.Pipeline) (fuel nps : Nat) :
    Source.cdTail entryZero 0 32=.ok (68,0) ∧
    ∃ (mid : Source.EMState E0 BΓ),
      (Source.evalE (G0 p) (entryFrame entryZero) (fuel+4) (sourceUintCalldataBind bDst bSrc)).run (bInput 68 0 (u 0))=
        (.ok (.val (.memRef rfl 2)),mid) ∧
      (sourceGuardedUintDelete (G0 p) (entryFrame entryZero) fuel nps bDst bSrc bIndex entryZero 0 (bInput 68 0 (u 0)).1).run (.nil,(bInput 68 0 (u 0)).2)=
        (.error (.revert (Source.panicData .index)),(.nil,mid.2)) ∧
      mid.2.heap.get 2=some ⟨SU,sourceUintMemory []⟩ ∧ mid.2.heap.next=3 ∧
      mid.2.heap.get 0=some ⟨SU,sourceUintMemory old⟩ ∧ mid.2.heap.get 1=some ⟨SU,sourceUintMemory neighbor⟩ := by
  first
  | solve | rfl | simp only [] | omega
  | have off : Source.wordAt entryZero 0=32 := by decide
    have size : Source.wordAt (entryZero.drop 32) 0=0 := by decide
    have values : CalldataPackets.RawUint.dataPayload entryZero 64 0=[] := rfl
    have result := source_guarded_uint_bind_delete_bounds (bInput 68 0 (u 0)) hp (G0 p) (entryFrame entryZero) fuel nps
      bDst bSrc bIndex entrySelector entryZero rfl rfl 0 (u 0)
      (by rw [off,size];rfl) rfl (by rw [off,size];decide)
      (by rw [off,size];decide) (by rw [off,size];decide) SH (bMemOK 68 0 (u 0))
    simp only [off,size,values] at result
    obtain ⟨guard,valid,first,second,program,adapter,write,fresh,mok,keep,occupied,guarded⟩ := result
    refine ⟨guard,_,first,guarded,?_,rfl,?_,?_⟩
    · rfl
    · rfl
    · rfl

/-- Actual standalone copy of that SAME truncated entry pads the absent second
word instead of running the entry-span check or inventing a guard failure. -/
theorem guarded_entry_standalone_padding :
    (Source.cdToMem (E := E0) (Γ := BΓ) (entryFrame entryTruncated) SU 68 2).run (bInput 68 2 (u 1))=
      (.ok (.val (.memRef rfl 2)),((bInput 68 2 (u 1)).1,
        {(bInput 68 2 (u 1)).2 with heap := ((bInput 68 2 (u 1)).2.heap.alloc ⟨SU,sourceUintMemory [u 7,u 0]⟩).1})) := by
  first
  | solve | rfl | simp only [] | omega
  | have values : CalldataPackets.RawUint.payload (entryFrame entryTruncated) 68 2=[u 7,u 0] := by decide
    rw [CalldataPackets.RawUint.copy_run,values]
    rfl

/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.guarded_entry_delete_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms guarded_entry_delete_program
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.guarded_entry_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms guarded_entry_vectors
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.guarded_entry_refusals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms guarded_entry_refusals
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.guarded_entry_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms guarded_entry_empty
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.guarded_entry_standalone_padding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms guarded_entry_standalone_padding

/-- A FULL valid entry can fail later at endpoint2: the copy happened and its
prefix globals remain, with index panic bytes distinct from early empty revert. -/
theorem guarded_entry_endpoint (p : Roadmap.Pipeline) (fuel nps : Nat) :
    Source.cdTail entryData 0 32=.ok (68,2) ∧
    (sourceGuardedUintDelete (G0 p) (entryFrame entryData) fuel nps bDst bSrc bIndex entryData 0 (bInput 68 2 (u 2)).1).run (.nil,(bInput 68 2 (u 2)).2)=
      (.error (.revert (Source.panicData .index)),(.nil,(entryMid (u 2)).2)) ∧
    rawPair.1.writeAddr (.index rawPair.2 .dyn (u 2)) (PrimTy.dflt .uint)=none ∧
    (entryMid (u 2)).2.heap.get 2=some ⟨SU,sourceUintMemory rawPayload⟩ ∧
    Source.panicData .index≠[] := by
  first
  | solve | rfl | simp only [] | omega
  | have result := source_guarded_uint_bind_delete_bounds (bInput 68 2 (u 2)) hp (G0 p) (entryFrame entryData) fuel nps
      bDst bSrc bIndex entrySelector entryData rfl rfl 0 (u 2)
      (by rw [entryOff,entryLen];rfl) rfl
      (by rw [entryOff,entryLen];decide) (by rw [entryOff,entryLen,entryBytes];decide)
      (by rw [entryOff,entryLen];decide) SH (bMemOK 68 2 (u 2))
    simp only [entryOff,entryLen,entryValues] at result
    obtain ⟨guard,valid,first,second,program,adapter,write,fresh,mok,keep,occupied,guarded⟩ := result
    exact ⟨guard,guarded,write,rfl,by decide⟩

/-- The actual guard succeeds, then horizon5 times out AFTER the real binding
prefix. No wrapper changes the Items fuel and no rollback state is invented. -/
theorem guarded_entry_late_timeout (p : Roadmap.Pipeline) (nps : Nat) :
    ((Source.EM.lift (Source.cdTail entryData 0 32)) >>= fun _ =>
      Source.execItems (G0 p) (entryFrame entryData) 5 nps none dProgram (bInput 68 2 (u 1)).1).run (.nil,(bInput 68 2 (u 1)).2)=
      (.error .timeout,(.nil,(entryMid (u 1)).2)) := by
  first
  | solve | simp only [] | omega
  | have bytes : CalldataPackets.RawUint.payload (entryFrame entryData) 68 2=rawPayload :=
      (CalldataPackets.RawUint.payload_frame (entryFrame entryData) entrySelector entryData rfl rfl 64 2).trans entryValues
    have first : (Source.evalE (G0 p) (entryFrame entryData) 3 (sourceUintCalldataBind bDst bSrc)).run (bInput 68 2 (u 1))=
        (.ok (.val (.memRef rfl 2)),entryMid (u 1)) := by
      rw [source_cd_uint_bind_run (G0 p) (entryFrame entryData) 0 (bInput 68 2 (u 1)) bDst bSrc 68 2 rfl,source_cd_uint_values_raw]
      dsimp only
      rw [source_uint_payload_sourceUint,bytes]
      rfl
    have statement := source_expr_statement_run (G0 p) (entryFrame entryData) 3 nps _ _ _ _ first
    rw [(guarded_entry_delete_program p 0 nps).1]
    change (Source.execItems (G0 p) (entryFrame entryData) 5 nps none dProgram (bInput 68 2 (u 1)).1).run (.nil,(bInput 68 2 (u 1)).2)=_
    rw [dProgram,Source.execItems,Source.Hoare.run_bind,statement]
    rfl

/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.guarded_entry_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms guarded_entry_endpoint
/-- info: 'Solidity.Backend.MemoryOps.UintCopyControls.guarded_entry_late_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms guarded_entry_late_timeout

end Solidity.Backend.MemoryOps.UintCopyControls
