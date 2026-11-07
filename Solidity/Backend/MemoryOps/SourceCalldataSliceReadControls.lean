import Solidity.Backend.MemoryOps.SourceCalldataSliceReadCopy
import Solidity.Backend.MemoryOps.SourceCalldataSlice
import Solidity.Source.SemanticsExamples

/-! Real Source reads through a slice, lazy malformed-word handling, exact
bounds stages and a checked native-copy observation. No target code is run. -/
namespace Solidity.Backend.MemoryOps.SliceReadControls
open Source.SemanticsExamples (E0 F0 G0 s0)
private abbrev B : RefTy := .array (.prim .bool)
private abbrev U : RefTy := .array (.prim .uint)
private abbrev H : HTy := [B,U]
private abbrev SB := Source.STy.array .memory .bool none
private abbrev SU := Source.STy.array .memory (.int .u256) none
private abbrev Γ (element : Source.STy) : Source.RCtx :=
  [.array .calldata element none,.int .u256,.int .u256,.int .u256,SB,SB,SU]
private def u (n : Nat) : PrimTy.uint.Denote := Evm.Memory.indexValue (Evm.wmod n)
private def maximum : PrimTy.uint.Denote := Evm.Memory.indexValue Evm.wMax
private def old : List Bool := [true,false,true]
private def neighbor : List PrimTy.uint.Denote := [u 8,u 9]
private def hp : Heap H := (⟨old,by decide⟩,⟨neighbor,by decide⟩,())
private def left : HRef H B := ⟨0,rfl⟩
private def right : HRef H U := ⟨1,rfl⟩
private def y0 : Source.EMState E0 [] := (.nil,s0)
private def y1 : Source.EMState E0 [] := ((Source.allocRef (sourceBoolMemory old)).run y0).2
private def y2 : Source.EMState E0 [] := ((Source.allocRef (sourceUintMemory neighbor)).run y1).2
private def sy (element : Source.STy) (len s e i : Nat) : Source.EMState E0 (Γ element) :=
  (.cons (.cdRef rfl 0 len) (.cons (sourceUint (u s)) (.cons (sourceUint (u e))
    (.cons (sourceUint (u i)) (.cons (.memRef rfl 0)
      (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil)))))),y2.2)
private def root (element : Source.STy) : Source.Idx (Γ element) (.array .calldata element none) := .here
private def start (element : Source.STy) : Source.Idx (Γ element) (.int .u256) := .there .here
private def finish (element : Source.STy) : Source.Idx (Γ element) (.int .u256) := .there (.there .here)
private def index (element : Source.STy) : Source.Idx (Γ element) (.int .u256) := .there (.there (.there .here))
private def read (element : Source.STy) (single : element.oneWord=true) (toEnd : Bool) :=
  sourceSliceIndex (E := E0) element single (root element) (start element) (finish element) (index element) toEnd
private def boolFrame : Source.Fr := {F0 with cd :=
  ((List.replicate 31 0++[1])++(List.replicate 31 0++[2])++List.replicate 32 0++(List.replicate 31 0++[1]))}
private def uintFrame : Source.Fr := {F0 with cd :=
  ((List.replicate 31 0++[7])++List.replicate 32 0++List.replicate 32 255)}
private def decoded : List (Source.Val E0.layout .bool) := [.bool false,.bool true]
private def out : Heap (H++[B]) := (hp.alloc (R := B) (⟨[false,true],by decide⟩ : MObj H B)).1
private def fresh : HRef (H++[B]) B := (hp.alloc (R := B) (⟨[false,true],by decide⟩ : MObj H B)).2
private theorem actual_decode : sourceCalldataBoolValues E0 boolFrame 64 2=.ok decoded := by rfl

/-- A selected canonical word succeeds without validating a different bad
word. Selecting that malformed word fails, with no allocation or state change. -/
theorem boolean_reads (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) boolFrame (fuel+3) (read .bool rfl false)).run (sy .bool 4 2 4 1)=
      (.ok (.val (.bool true)),sy .bool 4 2 4 1) ∧
    (Source.evalE (G0 p) boolFrame (fuel+3) (read .bool rfl false)).run (sy .bool 4 0 4 0)=
      (.ok (.val (.bool true)),sy .bool 4 0 4 0) ∧
    (Source.evalE (G0 p) boolFrame (fuel+3) (read .bool rfl false)).run (sy .bool 4 0 4 1)=
      (.error (.revert []),sy .bool 4 0 4 1) ∧
    (Source.evalE (G0 p) boolFrame (fuel+3) (read .bool rfl true)).run (sy .bool 4 2 0 1)=
      (.ok (.val (.bool true)),sy .bool 4 2 0 1) := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals unfold read
  · rw [source_slice_index_eval .bool rfl (G0 p) boolFrame fuel (sy .bool 4 2 4 1)
      (root .bool) (start .bool) (finish .bool) (index .bool) 0 4 (u 2) (u 4) (u 1) false rfl rfl rfl rfl]
    rfl
  · rw [source_slice_index_eval .bool rfl (G0 p) boolFrame fuel (sy .bool 4 0 4 0)
      (root .bool) (start .bool) (finish .bool) (index .bool) 0 4 (u 0) (u 4) (u 0) false rfl rfl rfl rfl]
    rfl
  · rw [source_slice_index_eval .bool rfl (G0 p) boolFrame fuel (sy .bool 4 0 4 1)
      (root .bool) (start .bool) (finish .bool) (index .bool) 0 4 (u 0) (u 4) (u 1) false rfl rfl rfl rfl]
    rfl
  · rw [source_slice_index_eval .bool rfl (G0 p) boolFrame fuel (sy .bool 4 2 0 1)
      (root .bool) (start .bool) (finish .bool) (index .bool) 0 4 (u 2) (u 0) (u 1) true rfl rfl rfl rfl]
    rfl

/-- Numeric indexing uses the same typed path, preserving its uint type and
maximum word. Omitting the start would return zero instead of maximum. -/
theorem uint_reads (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) uintFrame (fuel+3) (read (.int .u256) rfl false)).run (sy (.int .u256) 3 1 3 1)=
      (.ok (.val (sourceUint maximum)),sy (.int .u256) 3 1 3 1) ∧
    (Source.evalE (G0 p) uintFrame (fuel+3) (read (.int .u256) rfl false)).run (sy (.int .u256) 3 0 3 1)=
      (.ok (.val (sourceUint (u 0))),sy (.int .u256) 3 0 3 1) ∧
    (Source.evalE (G0 p) boolFrame (fuel+3) (read (.int .u256) rfl false)).run (sy (.int .u256) 4 0 4 1)=
      (.ok (.val (sourceUint (u 2))),sy (.int .u256) 4 0 4 1) := by
  refine ⟨?_,?_,?_⟩
  all_goals unfold read
  · rw [source_slice_index_eval (.int .u256) rfl (G0 p) uintFrame fuel (sy (.int .u256) 3 1 3 1)
      (root _) (start _) (finish _) (index _) 0 3 (u 1) (u 3) (u 1) false rfl rfl rfl rfl]
    rfl
  · rw [source_slice_index_eval (.int .u256) rfl (G0 p) uintFrame fuel (sy (.int .u256) 3 0 3 1)
      (root _) (start _) (finish _) (index _) 0 3 (u 0) (u 3) (u 1) false rfl rfl rfl rfl]
    rfl
  · rw [source_slice_index_eval (.int .u256) rfl (G0 p) boolFrame fuel (sy (.int .u256) 4 0 4 1)
      (root _) (start _) (finish _) (index _) 0 4 (u 0) (u 4) (u 1) false rfl rfl rfl rfl]
    rfl

/-- Actual selected-word Source observation agrees with an actual checked
fresh transfer and native indexed read, not a supplied successful heap/run. -/
theorem checked_copy_read_client (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) boolFrame (fuel+3) (read .bool rfl false)).run (sy .bool 4 2 4 1)=
      (.ok (.val (.bool true)),sy .bool 4 2 4 1) ∧
    checkedSourceFreshBools (E := E0) boolFrame 64 2 hp (by decide)=.ok (some out) ∧
    out.index fresh .dyn (u 1)=some true ∧
    Heap.Keeps (List.prefix_append H [B]) hp out ∧ fresh.id=2 ∧ left.id≠fresh.id ∧ right.id≠fresh.id := by
  obtain ⟨valid,value,run,checked,hit,keeps,identity⟩ := source_bool_slice_index_checked (G0 p) boolFrame fuel
    (sy .bool 4 2 4 1) (root .bool) (start .bool) (finish .bool) (index .bool) 0 4 (u 2) (u 4) (u 1) false
    rfl rfl rfl rfl (by decide) (by decide) (by decide) hp (by decide) decoded actual_decode
  have observed := hit
  change (MObj.elems .dyn ((hp.alloc (R := B)
    (⟨sourceBoolValuePayload decoded,valid⟩ : MObj H B)).1.get
      (hp.alloc (R := B) (⟨sourceBoolValuePayload decoded,valid⟩ : MObj H B)).2))[(u 1).1.toNat]?=some value at observed
  rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn] at observed
  simp only [List.map_id'' (f := MVal.wk (List.prefix_append H [B]) (.prim .bool)) (fun _ => rfl)] at observed
  change some true=some value at observed
  cases Option.some.inj observed
  exact ⟨run,checked,hit,keeps,rfl,by decide,by decide⟩

/-- Complete raw input and retained Source object/local tables, with old
aliases and unrelated numeric neighbour; native copy contents are complete. -/
theorem complete_vectors :
    [Source.cdWordAt boolFrame 0,Source.cdWordAt boolFrame 32,Source.cdWordAt boolFrame 64,Source.cdWordAt boolFrame 96]=[1,2,0,1] ∧
    [Source.cdWordAt uintFrame 0,Source.cdWordAt uintFrame 32,Source.cdWordAt uintFrame 64]=[7,0,2^256-1] ∧
    [(sy .bool 4 2 4 1).2.heap.get 0,(sy .bool 4 2 4 1).2.heap.get 1,(sy .bool 4 2 4 1).2.heap.get 2]=
      [some ⟨SB,sourceBoolMemory old⟩,some ⟨SU,sourceUintMemory neighbor⟩,none] ∧
    (sy .bool 4 2 4 1).1=
      .cons (.cdRef rfl 0 4) (.cons (sourceUint (u 2)) (.cons (sourceUint (u 4))
        (.cons (sourceUint (u 1)) (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (.memRef rfl 1) .nil)))))) ∧
    [(sy .bool 4 2 4 1).2.heap.next,left.id,right.id,fresh.id]=[2,0,1,2] ∧
    (sy .bool 4 2 4 1).2.ex=y2.2.ex ∧ (sy .bool 4 2 4 1).2.events=y2.2.events ∧
    (sy .bool 4 2 4 1).2.logs=y2.2.logs ∧ (sy .bool 4 2 4 1).2.fnLocals=y2.2.fnLocals ∧
    [MObj.elems .dyn (out.get (left.wk (List.prefix_append H [B]))),MObj.elems .dyn (out.get fresh)]=
      [old,[false,true]] ∧
    MObj.elems .dyn (out.get (right.wk (List.prefix_append H [B])))=neighbor := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · unfold out fresh
    rw [(hp.keeps_alloc (R := B) (⟨[false,true],by decide⟩ : MObj H B)) left,
      Heap.get_alloc,MObj.elems_wk,MObj.elems_wk]
    simp only [MObj.elems_dyn,List.map_id'' (f := MVal.wk (List.prefix_append H [B]) (.prim .bool)) (fun _ => rfl)] <;> rfl
  · unfold out
    rw [(hp.keeps_alloc (R := B) (⟨[false,true],by decide⟩ : MObj H B)) right,MObj.elems_wk]
    simp only [MObj.elems_dyn,List.map_id'' (f := MVal.wk (List.prefix_append H [B]) (.prim .uint)) (fun _ => rfl)] <;> rfl

/-- Slice rejection precedes index bounds; an empty exact-end slice is valid,
but indexing it panics. Past the selected length uses the original panic bytes. -/
theorem bounds_and_timeout (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) boolFrame (fuel+3) (read .bool rfl false)).run (sy .bool 4 3 2 0)=
      (.error (.revert []),sy .bool 4 3 2 0) ∧
    (Source.evalE (G0 p) boolFrame (fuel+3) (read .bool rfl false)).run (sy .bool 4 0 5 0)=
      (.error (.revert []),sy .bool 4 0 5 0) ∧
    (Source.evalE (G0 p) boolFrame (fuel+3) (read .bool rfl false)).run (sy .bool 4 4 4 0)=
      (.error (.revert (Source.panicData .index)),sy .bool 4 4 4 0) ∧
    (Source.evalE (G0 p) boolFrame (fuel+3) (read .bool rfl false)).run (sy .bool 4 2 4 2)=
      (.error (.revert (Source.panicData .index)),sy .bool 4 2 4 2) ∧
    (Source.evalE (G0 p) boolFrame 2 (read .bool rfl false)).run (sy .bool 4 2 4 0)=
      (.error .timeout,sy .bool 4 2 4 0) ∧ Source.panicData .index≠[] := by
  refine ⟨?_,?_,?_,?_,?_,by decide⟩
  all_goals unfold read
  · rw [source_slice_index_eval .bool rfl (G0 p) boolFrame fuel (sy .bool 4 3 2 0)
      (root _) (start _) (finish _) (index _) 0 4 (u 3) (u 2) (u 0) false rfl rfl rfl rfl]
    rfl
  · rw [source_slice_index_eval .bool rfl (G0 p) boolFrame fuel (sy .bool 4 0 5 0)
      (root _) (start _) (finish _) (index _) 0 4 (u 0) (u 5) (u 0) false rfl rfl rfl rfl]
    rfl
  · rw [source_slice_index_eval .bool rfl (G0 p) boolFrame fuel (sy .bool 4 4 4 0)
      (root _) (start _) (finish _) (index _) 0 4 (u 4) (u 4) (u 0) false rfl rfl rfl rfl]
    rfl
  · rw [source_slice_index_eval .bool rfl (G0 p) boolFrame fuel (sy .bool 4 2 4 2)
      (root _) (start _) (finish _) (index _) 0 4 (u 2) (u 4) (u 2) false rfl rfl rfl rfl]
    rfl
  · cases p <;> rfl

/-- Replacing a lazy slice read by eager memory conversion changes behavior:
the unused malformed word would reject before the selected canonical read. -/
theorem eager_copy_negative (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) boolFrame (fuel+4)
      (.indexArray (sourceBoolSliceCopy (root .bool) (start .bool) (finish .bool) false)
        (.local (index .bool)) rfl)).run (sy .bool 4 0 4 0)=
      (.error (.revert []),sy .bool 4 0 4 0) ∧
    (Source.evalE (G0 p) boolFrame (fuel+3) (read .bool rfl false)).run (sy .bool 4 0 4 0)=
      (.ok (.val (.bool true)),sy .bool 4 0 4 0) := by
  refine ⟨?_,(boolean_reads p fuel).2.1⟩
  rw [Source.evalE,Source.Hoare.run_bind,
    source_bool_slice_copy_eval (G0 p) boolFrame fuel (sy .bool 4 0 4 0)
      (root .bool) (start .bool) (finish .bool) 0 4 (u 0) (u 4) false rfl rfl rfl]
  rfl

/-- info: 'Solidity.Backend.MemoryOps.SliceReadControls.boolean_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boolean_reads
/-- info: 'Solidity.Backend.MemoryOps.SliceReadControls.uint_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uint_reads
/-- info: 'Solidity.Backend.MemoryOps.SliceReadControls.checked_copy_read_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked_copy_read_client
/-- info: 'Solidity.Backend.MemoryOps.SliceReadControls.complete_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms complete_vectors
/-- info: 'Solidity.Backend.MemoryOps.SliceReadControls.bounds_and_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bounds_and_timeout
/-- info: 'Solidity.Backend.MemoryOps.SliceReadControls.eager_copy_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eager_copy_negative
end Solidity.Backend.MemoryOps.SliceReadControls
