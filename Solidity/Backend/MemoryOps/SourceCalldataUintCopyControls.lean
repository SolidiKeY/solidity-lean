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
end Solidity.Backend.MemoryOps.UintCopyControls
