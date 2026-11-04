import Solidity.Backend.MemoryOps.SourceRawBoolSliceSequence
import Solidity.Source.SemanticsExamples

/-! Actual Boolean calldata views select or exclude a malformed word. A real
successful copy precedes a later failed decoder in one Source RItems program.
No target copying or transaction rollback is inferred. -/
namespace Solidity.Backend.MemoryOps.BoolSliceControls
open Source.SemanticsExamples (E0 F0 G0 s0)
private abbrev A : RefTy := .array (.prim .bool)
private abbrev H : HTy := [A,A]
private abbrev SU := Source.STy.array .memory .bool none
private abbrev CD := Source.STy.array .calldata .bool none
private abbrev Γ : Source.RCtx := [CD,.int .u256,.int .u256,.int .u256,.int .u256,SU,SU,SU]
private def u (n : Nat) : PrimTy.uint.Denote := Evm.Memory.indexValue (Evm.wmod n)
private def old : List Bool := [true,false,true]
private def neighbor : List Bool := [false,false]
private def payload : List Bool := [false,true]
private def hp : Heap H := (⟨old,by decide⟩,⟨neighbor,by decide⟩,())
private def left : HRef H A := ⟨0,rfl⟩
private def right : HRef H A := ⟨1,rfl⟩
private def y0 : Source.EMState E0 [] := (.nil,s0)
private def y1 : Source.EMState E0 [] := ((Source.allocRef (sourceBoolMemory old)).run y0).2
private def y2 : Source.EMState E0 [] := ((Source.allocRef (sourceBoolMemory neighbor)).run y1).2
private def sy (s e bs be : Nat) : Source.EMState E0 Γ :=
  (.cons (.cdRef rfl 0 4) (.cons (sourceUint (u s)) (.cons (sourceUint (u e))
    (.cons (sourceUint (u bs)) (.cons (sourceUint (u be)) (.cons (.memRef rfl 0)
      (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil))))))),y2.2)
private def initial := sy 2 4 0 3
private def frame : Source.Fr := {F0 with cd :=
  ((List.replicate 31 0++[1])++(List.replicate 31 0++[2])++
    List.replicate 32 0++(List.replicate 31 0++[1]))}
private def root : Source.Idx Γ CD := .here
private def start : Source.Idx Γ (.int .u256) := .there .here
private def finish : Source.Idx Γ (.int .u256) := .there (.there .here)
private def badStart : Source.Idx Γ (.int .u256) := .there (.there (.there .here))
private def badFinish : Source.Idx Γ (.int .u256) := .there (.there (.there (.there .here)))
private def first := sourceBoolSliceCopy (E := E0) root start finish false
private def second := sourceBoolSliceCopy (E := E0) root badStart badFinish false
private def program : Source.RItems E0 [] false .body Γ Γ :=
  .stmt (.expr first) (.stmt (.expr second) .nil)
private def decoded : List (Source.Val E0.layout .bool) := [.bool false,.bool true]
private def out : Heap (H++[A]) := (hp.alloc (R := A) (⟨payload,by decide⟩ : MObj H A)).1
private def fresh : HRef (H++[A]) A := (hp.alloc (R := A) (⟨payload,by decide⟩ : MObj H A)).2
private def middle : Source.EMState E0 Γ :=
  (initial.1,{initial.2 with heap := (initial.2.heap.alloc ⟨SU,sourceBoolMemory payload⟩).1})
private abbrev SH := (Source.Heap.empty (D := E0.layout)).ty
private theorem actual_decode : sourceCalldataBoolValues E0 frame 64 2=.ok decoded := by rfl
private theorem malformed : sourceCalldataBoolValues E0 frame 0 3=.error (.revert []) := by rfl
private theorem old_at : SourceBoolMemoryAt initial 0 hp left .dyn := by
  unfold SourceBoolMemoryAt
  change initial.2.heap.get 0=some ⟨SU,sourceBoolMemory (MObj.elems .dyn (⟨old,by decide⟩ : MObj H A))⟩
  rw [MObj.elems_dyn]
  rfl
private theorem neighbor_at : SourceBoolMemoryAt initial 1 hp right .dyn := by
  unfold SourceBoolMemoryAt
  change initial.2.heap.get 1=some ⟨SU,sourceBoolMemory (MObj.elems .dyn (⟨neighbor,by decide⟩ : MObj H A))⟩
  rw [MObj.elems_dyn]
  rfl
private theorem memOK (s e bs be : Nat) : Source.MemOK E0 SH (sy s e bs be) := by
  have h0 : Source.MemOK E0 SH y0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have h1 := source_bool_alloc_memOK (E := E0) (Γ := []) SH old y0 h0
  rw [source_bool_alloc] at h1
  change Source.MemOK E0 SH y1 ∧ _ at h1
  have h2 := source_bool_alloc_memOK (E := E0) (Γ := []) SH neighbor y1 h1.1
  rw [source_bool_alloc] at h2
  change Source.MemOK E0 SH y2 ∧ _ at h2
  refine ⟨⟨h2.1.1.1,?_⟩,h2.1.2⟩
  exact ⟨trivial,⟨trivial,⟨trivial,⟨trivial,⟨trivial,⟨⟨SU,rfl,rfl⟩,⟨⟨SU,rfl,rfl⟩,⟨⟨SU,rfl,rfl⟩,trivial⟩⟩⟩⟩⟩⟩⟩⟩

/-- The second slice bounds succeed, then its decoder fails AFTER a genuine
first copy. Source exposes exactly that prefix heap, never a fabricated suffix. -/
theorem reached_failure_client (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G0 p) frame (fuel+4) first).run initial=
      (.ok (.val (.memRef rfl 2)),middle) ∧
    (Source.evalE (G0 p) frame (fuel+3) second).run middle=(.error (.revert []),middle) ∧
    (Source.execItems (G0 p) frame (fuel+6) nps none program initial.1).run (.nil,initial.2)=
      (.error (.revert []),(.nil,middle.2)) ∧
    checkedSourceFreshBools (E := E0) frame 64 2 hp (by decide)=.ok (some out) ∧
    checkedSourceFreshBools (E := E0) frame 0 3 out (by decide)=.error (.revert []) ∧
    Heap.Keeps (List.prefix_append H [A]) hp out ∧
    SourceBoolMemoryAt middle 2 out fresh .dyn ∧ Source.MemOK E0 SH middle ∧
    SourceBoolMemoryAt middle 0 out (left.wk (List.prefix_append H [A])) .dyn ∧
    SourceBoolMemoryAt middle 1 out (right.wk (List.prefix_append H [A])) .dyn := by
  have sequence := source_bool_slice_copy_late_error (G0 p) frame fuel nps initial
    root start finish badStart badFinish 0 4 (u 2) (u 4) (u 0) (u 3) false false
    rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) (.revert []) malformed SH (memOK 2 4 0 3)
  have decodedFirst : sourceCalldataBoolValues E0 frame (0+32*(u 2).1.toNat)
      ((if false then 4 else (u 4).1.toNat)-(u 2).1.toNat)=.ok decoded := actual_decode
  rw [decodedFirst] at sequence
  obtain ⟨run1,run2,items,mok,preserved,locals,next,ex,ev,logs,fn⟩ := sequence
  obtain ⟨valid,checked,native⟩ := checkedSourceFreshBools_some frame 64 2 hp (by decide) decoded actual_decode
  have keeps : Heap.Keeps (List.prefix_append H [A]) hp out := hp.keeps_alloc _
  have new : SourceBoolMemoryAt middle 2 out fresh .dyn := by
    unfold SourceBoolMemoryAt out fresh
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
    simp only [List.map_id'' (f := MVal.wk (List.prefix_append H [A]) (.prim .bool)) (fun _ => rfl)]
    rfl
  refine ⟨run1,run2,items,native,checkedSourceFreshBools_error frame 0 3 out (by decide) _ malformed,
    keeps,new,mok,?_,?_⟩
  · exact old_at.transport keeps (fun b obj occupied => (preserved b obj occupied).1)
  · exact neighbor_at.transport keeps (fun b obj occupied => (preserved b obj occupied).1)

/-- Full initial/prefix/error-boundary tables and every local, native object,
identity and Source world field. The error boundary is literally middle. -/
theorem complete_vectors :
    [Source.cdWordAt frame 0,Source.cdWordAt frame 32,
      Source.cdWordAt frame 64,Source.cdWordAt frame 96]=[1,2,0,1] ∧
    [initial.2.heap.get 0,initial.2.heap.get 1,initial.2.heap.get 2,initial.2.heap.get 3]=
      [some ⟨SU,sourceBoolMemory old⟩,some ⟨SU,sourceBoolMemory neighbor⟩,none,none] ∧
    [middle.2.heap.get 0,middle.2.heap.get 1,middle.2.heap.get 2,middle.2.heap.get 3]=
      [some ⟨SU,sourceBoolMemory old⟩,some ⟨SU,sourceBoolMemory neighbor⟩,some ⟨SU,sourceBoolMemory payload⟩,none] ∧
    middle.1=initial.1 ∧ initial.1=
      .cons (.cdRef rfl 0 4) (.cons (sourceUint (u 2)) (.cons (sourceUint (u 4))
        (.cons (sourceUint (u 0)) (.cons (sourceUint (u 3)) (.cons (.memRef rfl 0)
          (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil))))))) ∧
    [MObj.elems .dyn (out.get (left.wk (List.prefix_append H [A]))),
      MObj.elems .dyn (out.get (right.wk (List.prefix_append H [A]))),MObj.elems .dyn (out.get fresh)]=
      [old,neighbor,payload] ∧
    [left.id,right.id,fresh.id]=[0,1,2] ∧ initial.2.heap.next=2 ∧ middle.2.heap.next=3 ∧
    middle.2.ex=initial.2.ex ∧ middle.2.events=initial.2.events ∧
    middle.2.logs=initial.2.logs ∧ middle.2.fnLocals=initial.2.fnLocals := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  unfold out fresh
  rw [(hp.keeps_alloc (R := A) (⟨payload,by decide⟩ : MObj H A)) left,
    (hp.keeps_alloc (R := A) (⟨payload,by decide⟩ : MObj H A)) right,Heap.get_alloc,MObj.elems_wk,MObj.elems_wk,MObj.elems_wk]
  simp only [MObj.elems_dyn,List.map_id'' (f := MVal.wk (List.prefix_append H [A]) (.prim .bool)) (fun _ => rfl)]
  rfl

/-- The malformed window itself is an actual successful slice. Its decode
has a nonempty true prefix before malformed2. Reversed/end bounds reject earlier. -/
theorem slice_and_decoder_boundaries (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) frame (fuel+2)
      (.slice (.local root) (by decide) (.local badStart) rfl (.local badFinish) rfl false)).run middle=
      (.ok (.val (.cdRef rfl 0 3)),middle) ∧
    sourceCalldataBoolValues E0 frame 0 1=.ok [.bool true] ∧
    sourceCalldataBoolValues E0 frame 0 3=.error (.revert []) ∧
    sourceCalldataBoolValues E0 frame 64 2=.ok decoded ∧
    (Source.evalE (G0 p) frame (fuel+3) first).run (sy 3 2 0 3)=
      (.error (.revert []),sy 3 2 0 3) ∧
    (Source.evalE (G0 p) frame (fuel+3) first).run (sy 2 5 0 3)=
      (.error (.revert []),sy 2 5 0 3) := by
  refine ⟨?_,rfl,malformed,actual_decode,?_,?_⟩
  · rw [source_bool_slice_eval (G0 p) frame fuel middle root badStart badFinish 0 4 (u 0) (u 3) false rfl rfl rfl]
    rfl
  · unfold first
    rw [source_bool_slice_copy_eval (G0 p) frame fuel (sy 3 2 0 3) root start finish 0 4 (u 3) (u 2) false rfl rfl rfl]
    rfl
  · unfold first
    rw [source_bool_slice_copy_eval (G0 p) frame fuel (sy 2 5 0 3) root start finish 0 4 (u 2) (u 5) false rfl rfl rfl]
    rfl

/-- Swapping the real statements fails before allocation, whereas the actual
order retains a fresh object. A short horizon likewise has no invented suffix. -/
theorem wrong_order_and_timeout (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.execItems (G0 p) frame (fuel+6) nps none
      (.stmt (.expr second) (.stmt (.expr first) .nil) : Source.RItems E0 [] false .body Γ Γ)
        initial.1).run (.nil,initial.2)=(.error (.revert []),(.nil,initial.2)) ∧
    initial.2.heap.get 2=none ∧ middle.2.heap.get 2=some ⟨SU,sourceBoolMemory payload⟩ ∧
    (Source.evalE (G0 p) frame 2 first).run initial=(.error .timeout,initial) ∧
    (Source.memElem (E := E0) (Γ := Γ) 2 0 .bool).run middle=(.ok (.bool false),middle) ∧
    (Source.memElem (E := E0) (Γ := Γ) 0 0 .bool).run middle=(.ok (.bool true),middle) := by
  refine ⟨?_,rfl,rfl,?_,rfl,rfl⟩
  · have badFirst : (Source.evalE (G0 p) frame (fuel+4) second).run initial=(.error (.revert []),initial) := by
      unfold second
      rw [source_bool_slice_copy_window (G0 p) frame (fuel+1) initial root badStart badFinish
        0 4 (u 0) (u 3) false rfl rfl rfl (by decide) (by decide)]
      change (Source.cdToMem frame SU 0 3).run initial=_
      rw [source_cd_bool_run,malformed]
    have badStatement := source_expr_statement_error (G0 p) frame (fuel+4) nps _ initial initial _ badFirst
    rw [Source.execItems,Source.Hoare.run_bind,badStatement]
  · cases p <;> rfl

/-- Empty exact-end succeeds without reading the malformed earlier word.
The unrelated checked-transfer capacity refusal is Option None, not Source error. -/
theorem empty_and_capacity (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) frame (fuel+3) first).run (sy 4 4 0 3)=
      (.ok (.val (.memRef rfl 2)),((sy 4 4 0 3).1,{(sy 4 4 0 3).2 with heap :=
        ((sy 4 4 0 3).2.heap.alloc ⟨SU,sourceBoolMemory []⟩).1})) ∧
    checkedSourceBools (E := E0) frame 64 2 hp left .dyn 2=.ok none := by
  refine ⟨?_,?_⟩
  · unfold first
    rw [source_bool_slice_copy_eval (G0 p) frame fuel (sy 4 4 0 3) root start finish
      0 4 (u 4) (u 4) false rfl rfl rfl]
    rfl
  · apply (checkedSourceBools_none_iff frame 64 2 hp left .dyn 2 decoded actual_decode).mpr
    simp only [Heap.len,MObj.elems_dyn]
    decide

/-- info: 'Solidity.Backend.MemoryOps.BoolSliceControls.reached_failure_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reached_failure_client
/-- info: 'Solidity.Backend.MemoryOps.BoolSliceControls.complete_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms complete_vectors
/-- info: 'Solidity.Backend.MemoryOps.BoolSliceControls.slice_and_decoder_boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slice_and_decoder_boundaries
/-- info: 'Solidity.Backend.MemoryOps.BoolSliceControls.wrong_order_and_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_order_and_timeout
/-- info: 'Solidity.Backend.MemoryOps.BoolSliceControls.empty_and_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms empty_and_capacity
/-- The original inhabited program consumes raw-word premises, not the earlier
fixture decoder-run lemmas. Its complete ordered observations remain unchanged;
reversed order and low horizon distinguish the real allocated prefix. -/
theorem raw_word_program (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G0 p) frame (fuel+4) first).run initial=(.ok (.val (.memRef rfl 2)),middle) ∧
    (Source.evalE (G0 p) frame (fuel+3) second).run middle=(.error (.revert []),middle) ∧
    (Source.execItems (G0 p) frame (fuel+6) nps none program initial.1).run (.nil,initial.2)=
      (.error (.revert []),(.nil,middle.2)) ∧
    Source.MemOK E0 SH middle ∧
    (∀ b obj,initial.2.heap.get b=some obj → middle.2.heap.get b=some obj ∧ b≠initial.2.heap.next) ∧
    middle.1=initial.1 ∧ middle.2.heap.next=initial.2.heap.next+1 ∧
    middle.2.ex=initial.2.ex ∧ middle.2.events=initial.2.events ∧
    middle.2.logs=initial.2.logs ∧ middle.2.fnLocals=initial.2.fnLocals ∧
    (Source.execItems (G0 p) frame (fuel+6) nps none
      (.stmt (.expr second) (.stmt (.expr first) .nil) : Source.RItems E0 [] false .body Γ Γ)
        initial.1).run (.nil,initial.2)=(.error (.revert []),(.nil,initial.2)) ∧
    (Source.evalE (G0 p) frame 2 first).run initial=(.error .timeout,initial) ∧
    initial.2.heap.get 2=none ∧ middle.2.heap.get 2=some ⟨SU,sourceBoolMemory payload⟩ := by
  first
  | solve | simp only [] | omega
  | have canonical : ∀ j,j<((if false then 4 else (u 4).1.toNat)-(u 2).1.toNat) →
        Source.cdWordAt frame (0+32*(u 2).1.toNat+32*j)=0 ∨ Source.cdWordAt frame (0+32*(u 2).1.toNat+32*j)=1 := by
      change ∀ j,j<2 → Source.cdWordAt frame (64+32*j)=0 ∨ Source.cdWordAt frame (64+32*j)=1
      intro j hj
      have casesJ : j=0 ∨ j=1 := by omega
      rcases casesJ with rfl|rfl <;> decide
    have raw := source_bool_slice_raw_late_error (G0 p) frame fuel nps initial
      root start finish badStart badFinish 0 4 (u 2) (u 4) (u 0) (u 3) false false
      rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide) canonical [0] [2] 1 rfl
      (by intro j hj;simp only [List.mem_cons,List.not_mem_nil,or_false] at hj;subst j;decide)
      (by decide) SH (memOK 2 4 0 3)
    have values : rawBoolPayload frame (0+32*(u 2).1.toNat)
        ((if false then 4 else (u 4).1.toNat)-(u 2).1.toNat)=payload := by decide
    dsimp only at raw
    rw [values] at raw
    obtain ⟨run1,run2,items,mok,keeps,locals,next,ex,events,logs,fn⟩ := raw
    have negative := wrong_order_and_timeout p fuel nps
    exact ⟨run1,run2,items,mok,keeps,locals,next,ex,events,logs,fn,negative.1,negative.2.2.2.1,rfl,rfl⟩

/-- info: 'Solidity.Backend.MemoryOps.BoolSliceControls.raw_word_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_word_program
end Solidity.Backend.MemoryOps.BoolSliceControls
