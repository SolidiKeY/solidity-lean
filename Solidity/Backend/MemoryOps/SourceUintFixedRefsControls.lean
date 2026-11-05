import Solidity.Backend.MemoryOps.SourceUintFixedRefsMemory
import Solidity.Source.SemanticsExamples

/-! Independent Source objects with repeated fixed-child references. These are
read witnesses over existing heaps, not fresh-reference compiler certificates. -/
namespace Solidity.Backend.MemoryOps.SourceUintFixedRefsControls
open Evm Evm.Memory
open Source.SemanticsExamples (E0 F0 s0 G0)
private abbrev A : RefTy := .fixed (.prim .uint) 3
private abbrev P := UintFixedRefsRef 3
private abbrev H : HTy := [P,A,A]
private def root : HRef H P := ⟨0,rfl⟩
private def left : HRef H A := ⟨1,rfl⟩
private def right : HRef H A := ⟨2,rfl⟩
private def u (n : Nat) : PrimTy.uint.Denote := indexValue (wmod n)
private def hp : Heap H := (⟨[left,left,right],by decide⟩,⟨[u 7,u 0,u (W-1)],rfl⟩,⟨[u 8,u 9,u 10],rfl⟩,())
private def address (i : Nat) : Nat := if i=0 then 2 else if i=1 then 0 else 1
private def h0 : Source.Heap E0.layout := (s0 (E := E0)).heap
private def h1 := (h0.alloc ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (hp.get left)⟩).1
private def h2 := (h1.alloc ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (hp.get right)⟩).1
private def sourceHeap := (h2.alloc ⟨SourceUintFixedRefsTy 3,sourceUintFixedRefMemory address [left,left,right]⟩).1
private abbrev Γ : Source.RCtx := [.int .u256,.int .u256,SourceUintFixedRefsTy 3]
private def si : Source.Idx Γ (.int .u256) := .here
private def sj : Source.Idx Γ (.int .u256) := .there .here
private def sr : Source.Idx Γ (SourceUintFixedRefsTy 3) := .there (.there .here)
private def sy (i j : Nat) : Source.EMState E0 Γ :=
  (.cons (sourceUint (u i)) (.cons (sourceUint (u j)) (.cons (.memRef rfl 2) .nil)),{s0 with heap := sourceHeap})
private def readExpr : Source.RExpr E0 Γ (.int .u256) :=
  .indexArray (.indexArray (.local sr) (.local si) rfl) (.local sj) rfl
private theorem parentElements : MObj.elems .dyn (hp.get root)=[left,left,right] := by rw [MObj.elems_dyn];rfl
private theorem leftAt (i j : Nat) : SourceUintFixedAt (sy i j) 0 hp left := by rfl
private theorem rightAt (i j : Nat) : SourceUintFixedAt (sy i j) 1 hp right := by rfl
private theorem graph (i j : Nat) : SourceUintFixedRefsAt (sy i j) 2 hp root address := by
  refine ⟨?_,?_⟩
  · rw [parentElements]
    rfl
  · intro q member
    rw [parentElements] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl
    · exact leftAt i j
    · exact leftAt i j
    · exact rightAt i j
private theorem selectLeft : hp.index root .dyn (u 1)=some left := by
  change (MObj.elems .dyn (hp.get root))[1]?=some left
  rw [parentElements];rfl
private theorem selectRight : hp.index root .dyn (u 2)=some right := by
  change (MObj.elems .dyn (hp.get root))[2]?=some right
  rw [parentElements];rfl

/-- All three Source objects, complete typed contents, locals and the heap
bound are observed. Aliased parent entries0/1 and distinct entry2 coexist. -/
theorem initial_tables (i j : Nat) :
    SourceUintFixedRefsAt (sy i j) 2 hp root address ∧
    [(sy i j).2.heap.get 0,(sy i j).2.heap.get 1,(sy i j).2.heap.get 2]=
      [some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (hp.get left)⟩,
       some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (hp.get right)⟩,
       some ⟨SourceUintFixedRefsTy 3,sourceUintFixedRefMemory address [left,left,right]⟩] ∧
    (MObj.elems .dyn (hp.get root),MObj.elems .fixed (hp.get left),MObj.elems .fixed (hp.get right))=
      ([left,left,right],[u 7,u 0,u (W-1)],[u 8,u 9,u 10]) ∧
    (sy i j).1=.cons (sourceUint (u i)) (.cons (sourceUint (u j)) (.cons (.memRef rfl 2) .nil)) ∧
    (sy i j).2.heap.next=3 ∧ (∀ a,3≤a → (sy i j).2.heap.get a=none) := by
  first
  | solve | simp only [] | omega
  | refine ⟨graph i j,rfl,?_,rfl,rfl,?_⟩
    · rw [parentElements,MObj.elems_fixed,MObj.elems_fixed];rfl
    · intro a ha
      exact (sy i j).2.heap.bounded a ha

/-- Both pipelines read through the actual repeated parent slot to fixed max,
then through the distinct sibling to10; complete Source states are retained. -/
theorem selected_reads (pipeline : Roadmap.Pipeline) (horizon : Nat) :
    (Source.evalE (G0 pipeline) F0 (horizon+3) readExpr).run (sy 1 2)=
      (.ok (.val (sourceUint (u (W-1)))),sy 1 2) ∧
    (Source.evalE (G0 pipeline) F0 (horizon+3) readExpr).run (sy 2 2)=
      (.ok (.val (sourceUint (u 10))),sy 2 2) ∧
    (Source.readLoc (E := E0) (Γ := Γ) F0 (τ := .array .memory (.int .u256) (some 3)) (.mem 2 0)).run (sy 1 2)=
      (.ok (.memRef rfl 0),sy 1 2) ∧
    (Source.readLoc (E := E0) (Γ := Γ) F0 (τ := .array .memory (.int .u256) (some 3)) (.mem 2 1)).run (sy 1 2)=
      (.ok (.memRef rfl 0),sy 1 2) := by
  first
  | solve | simp only [] | omega
  | refine ⟨?_,?_,?_,?_⟩
    · exact ((graph 1 2).eval_nested_read (G0 pipeline) F0 horizon sr si sj (u 1) (u 2) left rfl rfl rfl selectLeft (by decide)).2
    · exact ((graph 2 2).eval_nested_read (G0 pipeline) F0 horizon sr si sj (u 2) (u 2) right rfl rfl rfl selectRight (by decide)).2
    · exact (graph 1 2).parent_read F0 0 left (by rw [parentElements];rfl)
    · exact (graph 1 2).parent_read F0 1 left (by rw [parentElements];rfl)

/-- Actual bounds/timeout failures retain their Source state and bytes. Parent
and child bounds share the same panic code; no distinct payload is invented. -/
theorem rejecting_reads (pipeline : Roadmap.Pipeline) (horizon : Nat) :
    (Source.evalE (G0 pipeline) F0 (horizon+3) readExpr).run (sy 3 0)=
      (.error (.revert (Source.panicData .index)),sy 3 0) ∧
    (Source.evalE (G0 pipeline) F0 (horizon+3) readExpr).run (sy 1 3)=
      (.error (.revert (Source.panicData .index)),sy 1 3) ∧
    (Source.evalE (G0 pipeline) F0 0 readExpr).run (sy 1 2)=(.error .timeout,sy 1 2) := by
  first
  | solve | simp only [] | omega
  | refine ⟨?_,?_,rfl⟩
    · apply (graph 3 0).eval_nested_parent_bounds (G0 pipeline) F0 horizon sr si sj (u 3) rfl rfl
      change (MObj.elems .dyn (hp.get root)).length≤3
      rw [parentElements];decide
    · exact (graph 1 3).eval_nested_child_bounds (G0 pipeline) F0 horizon sr si sj (u 1) (u 3) left rfl rfl rfl selectLeft (by decide)

theorem wrong_child_and_type :
    hp.index root .dyn (u 1)≠some right ∧
    (sy 1 2).2.heap.ty 0≠some (.array .memory (.int .u256) none) := by
  first
  | solve | simp only [] | omega
  | constructor
    · intro wrong
      rw [selectLeft] at wrong
      have ids := congrArg (fun value : Option (HRef H A) => value.map HRef.id) wrong
      change (some 1 : Option Nat)=some 2 at ids
      cases ids
    · intro wrong
      have actual : (sy 1 2).2.heap.ty 0=some (.array .memory (.int .u256) (some 3)) := rfl
      rw [actual] at wrong
      cases wrong

private def emptyHp : Heap H := (⟨[],by decide⟩,⟨[u 7,u 0,u (W-1)],rfl⟩,⟨[u 8,u 9,u 10],rfl⟩,())
private def emptyHeap := (h2.alloc ⟨SourceUintFixedRefsTy 3,sourceUintFixedRefMemory address ([] : List (HRef H A))⟩).1
private def ey : Source.EMState E0 Γ :=
  (.cons (sourceUint (u 0)) (.cons (sourceUint (u 0)) (.cons (.memRef rfl 2) .nil)),{s0 with heap := emptyHeap})
private theorem emptyElements : MObj.elems .dyn (emptyHp.get root)=[] := by rw [MObj.elems_dyn];rfl
private theorem emptyGraph : SourceUintFixedRefsAt ey 2 emptyHp root address := by
  refine ⟨?_,?_⟩
  · rw [emptyElements];rfl
  · intro q member
    rw [emptyElements] at member
    cases member

/-- A literal empty dynamic parent has actual length0 and rejects index0.
Its two existing fixed children still have positive length3; no fixed-zero
Source admission is asserted. -/
theorem empty_parent (pipeline : Roadmap.Pipeline) (horizon : Nat) :
    (Source.lengthOf (E := E0) (Γ := Γ) F0 (.memRef rfl 2 : Source.Val E0.layout (SourceUintFixedRefsTy 3))).run ey=(.ok 0,ey) ∧
    (Source.evalE (G0 pipeline) F0 (horizon+3) readExpr).run ey=
      (.error (.revert (Source.panicData .index)),ey) ∧
    emptyHp.index root .dyn (u 0)=none ∧
    ey.2.heap.get 0=some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (hp.get left)⟩ ∧
    ey.2.heap.get 1=some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (hp.get right)⟩ := by
  first
  | solve | simp only [] | omega
  | refine ⟨?_,?_,?_,rfl,rfl⟩
    · simpa only [Heap.len,emptyElements,List.length_nil] using emptyGraph.length_run F0
    · apply emptyGraph.eval_nested_parent_bounds (G0 pipeline) F0 horizon sr si sj (u 0) rfl rfl
      change (MObj.elems .dyn (emptyHp.get root)).length≤0
      rw [emptyElements];decide
    · change (MObj.elems .dyn (emptyHp.get root))[0]?=none
      rw [emptyElements];rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.empty_parent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_parent
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.initial_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial_tables
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.selected_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected_reads
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.rejecting_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejecting_reads
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.wrong_child_and_type' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_child_and_type
end Solidity.Backend.MemoryOps.SourceUintFixedRefsControls
