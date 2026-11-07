import Solidity.Backend.MemoryOps.SourceUintFixedRefsLate
import Solidity.Backend.MemoryOps.SourceUintFixedRefsDeleteTarget
import Solidity.Backend.MemoryOps.SourceUintFixedRefsExact
import Solidity.Evm.Correct
import Solidity.Backend.MemoryOps.PhysicalNestedFixedWrite
import Solidity.Backend.MemoryOps.PhysicalByteStoreSequence
import Solidity.Backend.MemoryOps.SourceUintFixedDeclaration
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
private abbrev ΓW : Source.RCtx := [.int .u256,.int .u256,.int .u256,SourceUintFixedRefsTy 3]
private def wi : Source.Idx ΓW (.int .u256) := .here
private def wj : Source.Idx ΓW (.int .u256) := .there .here
private def wv : Source.Idx ΓW (.int .u256) := .there (.there .here)
private def wr : Source.Idx ΓW (SourceUintFixedRefsTy 3) := .there (.there (.there .here))
private def sw (i j v : Nat) : Source.EMState E0 ΓW :=
  (.cons (sourceUint (u i)) (.cons (sourceUint (u j)) (.cons (sourceUint (u v)) (.cons (.memRef rfl 2) .nil))),(sy 0 0).2)
private abbrev SH := (Source.Heap.empty (D := E0.layout)).ty
private def b0 : Source.EMState E0 [] := (.nil,s0)
private def b1 : Source.EMState E0 [] := (.nil,{s0 with heap := h1})
private def b2 : Source.EMState E0 [] := (.nil,{s0 with heap := h2})
private theorem graphW (i j v : Nat) : SourceUintFixedRefsAt (sw i j v) 2 hp root address := (graph 0 0).same_heap rfl
private theorem memOKW (i j v : Nat) : Source.MemOK E0 SH (sw i j v) := by
  have initial : Source.MemOK E0 SH b0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have first := source_uint_fixed_alloc_memOK (E := E0) (Γ := []) SH (hp.get left) b0 initial
  change Source.MemOK E0 SH b1 ∧ _ at first
  have second := source_uint_fixed_alloc_memOK (E := E0) (Γ := []) SH (hp.get right) b1 first.1
  change Source.MemOK E0 SH b2 ∧ _ at second
  have dataOK : Source.DataOK E0 h2.ty (sourceUintFixedRefMemory address [left,left,right]) := by
    apply Source.DataOK.array
    intro index
    apply Source.DataOK.val
    refine ⟨.array .memory (.int .u256) (some 3),?_,rfl⟩
    rcases index with ⟨index,hi⟩
    cases index with
    | zero => rfl
    | succ index => cases index with
      | zero => rfl
      | succ index => cases index with
        | zero => rfl
        | succ index => simp only [List.length_cons,List.length_nil] at hi;omega
  have third := Source.allocRef_mem' (E := E0) (Γ := []) (H := SH)
    (sourceUintFixedRefMemory address [left,left,right]) (by trivial)
    (by change ∀ index : Fin 3,∃ value,_=Source.Data.val value;intro index;exact ⟨_,rfl⟩)
    b2 ⟨second.1,dataOK⟩
  change Source.MemOK E0 SH ((.nil,(sy 0 0).2) : Source.EMState E0 []) ∧ _ at third
  exact ⟨⟨third.1.1.1,⟨trivial,⟨trivial,⟨trivial,⟨⟨SourceUintFixedRefsTy 3,rfl,rfl⟩,trivial⟩⟩⟩⟩⟩,third.1.2⟩
private theorem selectedSeparation : ∀ t∈MObj.elems .dyn (hp.get root),t.id≠left.id → address t.id≠address left.id := by
  intro t member different
  rw [parentElements] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl
  · exact (different rfl).elim
  · exact (different rfl).elim
  · decide

/-- INITIAL graph, locals and MemOK are independently inhabited. -/
theorem mutation_initial : SourceUintFixedRefsAt (sw 1 1 42) 2 hp root address ∧
    Source.MemOK E0 SH (sw 1 1 42) ∧
    (∀ t∈MObj.elems .dyn (hp.get root),t.id≠left.id → address t.id≠address left.id) :=
  ⟨graphW 1 1 42,memOKW 1 1 42,selectedSeparation⟩

/-- Real nested assignment mutates0 to42, retains both parent aliases and the
other child, and feeds a genuine reached nested read. Whole Source objects,
locals, heap bound and world fields remain explicit. -/
theorem nested_mutation (pipeline : Roadmap.Pipeline) (horizon nps : Nat) :
    ∃ (out : Heap H) (z : Source.EMState E0 ΓW),
      hp.writeAddr (.index left .fixed (u 1)) (u 42)=some out ∧
      (Source.evalE (G0 pipeline) F0 (horizon+4) (sourceUintFixedNestedAssign wr wi wj wv)).run (sw 1 1 42)=
        (.ok (.val (sourceUint (u 42))),z) ∧
      (Source.execS (G0 pipeline) F0 (horizon+5) nps none
        (.expr (sourceUintFixedNestedAssign wr wi wj wv) : Source.RStmt E0 [] false .body ΓW ΓW) (sw 1 1 42).1).run (.nil,(sw 1 1 42).2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      SourceUintFixedRefsAt z 2 out root address ∧ Source.MemOK E0 SH z ∧
      (Source.evalE (G0 pipeline) F0 (horizon+3)
        (.indexArray (.indexArray (.local wr) (.local wi) rfl) (.local wj) rfl)).run z=(.ok (.val (sourceUint (u 42))),z) ∧
      MObj.elems .fixed (out.get left)=[u 7,u 42,u (W-1)] ∧ out.get right=hp.get right ∧
      [z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2]=
        [some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (out.get left)⟩,
         some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (hp.get right)⟩,
         some ⟨SourceUintFixedRefsTy 3,sourceUintFixedRefMemory address [left,left,right]⟩] ∧
      z.1=(sw 1 1 42).1 ∧ z.2.heap.next=3 ∧ (∀ a,3≤a → z.2.heap.get a=none) ∧
      z.2.ex=(sw 1 1 42).2.ex ∧ z.2.events=(sw 1 1 42).2.events ∧ z.2.logs=(sw 1 1 42).2.logs ∧ z.2.fnLocals=(sw 1 1 42).2.fnLocals := by
  first
  | solve | simp only [] | omega
  | obtain ⟨out,z,typed,expr,stmt,reached,preserved,locals,next,parent,objects,addresses,world,events,logs,fnLocals⟩ :=
      (graphW 1 1 42).resolved_write (G0 pipeline) F0 horizon nps wr wi wj wv (u 1) (u 1) (u 42) left
        rfl rfl rfl rfl selectLeft selectedSeparation (by decide) SH (memOKW 1 1 42)
    have canonical : hp.writeAddr (.index left .fixed (u 1)) (u 42)=
        some (hp.set left (MObj.setElem .fixed (hp.get left) 1 (u 42))) := by
      have valid : (u 1).1.toNat<(MObj.elems .fixed (hp.get left)).length := by rw [MObj.elems_fixed,(hp.get left).2];decide
      simp only [Heap.writeAddr,Heap.setIndex,valid,↓reduceIte]
      rfl
    have outEq := Option.some.inj (typed.symm.trans canonical)
    have contents : MObj.elems .fixed (out.get left)=[u 7,u 42,u (W-1)] := by
      rw [outEq,Heap.get_set_same,MObj.elems_setElem,MObj.elems_fixed]
      rfl
    have afterIndex : out.index root .dyn (u 1)=some left := by
      change (MObj.elems .dyn (out.get root))[1]?=some left
      rw [parent,parentElements];rfl
    have read := (reached.eval_nested_read (G0 pipeline) F0 horizon wr wi wj (u 1) (u 1) left
      (by rw [locals];rfl) (by rw [locals];rfl) (by rw [locals];rfl) afterIndex (by decide)).2
    have read42 : (Source.evalE (G0 pipeline) F0 (horizon+3)
        (.indexArray (.indexArray (.local wr) (.local wi) rfl) (.local wj) rfl)).run z=(.ok (.val (sourceUint (u 42))),z) := by
      simpa only [outEq,Heap.get_set_same,MObj.setElem_fixed,List.getElem_set_self] using read
    have leftNow := reached.children left (by rw [parent,parentElements];exact List.mem_cons_self)
    change z.2.heap.get 0=some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (out.get left)⟩ at leftNow
    have rightNow := (addresses 1 (by decide)).trans (show (sw 1 1 42).2.heap.get 1=some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (hp.get right)⟩ from rfl)
    have parentNow := reached.parent
    rw [parent,parentElements] at parentNow
    refine ⟨out,z,typed,expr,stmt,reached,preserved,read42,contents,objects right (by decide),?_,locals,next,?_,world,events,logs,fnLocals⟩
    · rw [leftNow,rightNow,parentNow]
    · intro a ha
      apply z.2.heap.bounded
      rw [next]
      exact ha

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.mutation_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mutation_initial
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.nested_mutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_mutation


/-- A materially changed prefix followed by actual nested deletion in one
Source Items execution; both Source object tables and typed payloads are retained. -/
theorem nested_mutation_delete (pipeline : Roadmap.Pipeline) (horizon nps : Nat) :
    ∃ (mid out : Heap H) (ym z : Source.EMState E0 ΓW),
      hp.writeAddr (.index left .fixed (u 1)) (u 42)=some mid ∧
      mid.writeAddr (.index left .fixed (u 1)) (PrimTy.dflt .uint)=some out ∧
      (Source.execS (G0 pipeline) F0 (horizon+6) nps none
        (.expr (sourceUintFixedNestedAssign wr wi wj wv) : Source.RStmt E0 [] false .body ΓW ΓW) (sw 1 1 42).1).run (.nil,(sw 1 1 42).2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execItems (G0 pipeline) F0 (horizon+7) nps none
        (.stmt (.expr (sourceUintFixedNestedAssign wr wi wj wv))
          (.stmt (.expr (sourceUintFixedNestedDelete wr wi wj)) .nil) : Source.RItems E0 [] false .body ΓW ΓW) (sw 1 1 42).1).run (.nil,(sw 1 1 42).2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      SourceUintFixedRefsAt ym 2 mid root address ∧ SourceUintFixedRefsAt z 2 out root address ∧
      Source.MemOK E0 SH ym ∧ Source.MemOK E0 SH z ∧
      MObj.elems .fixed (mid.get left)=[u 7,u 42,u (W-1)] ∧
      MObj.elems .fixed (out.get left)=[u 7,u 0,u (W-1)] ∧
      MObj.elems .fixed (mid.get left)≠MObj.elems .fixed (out.get left) ∧
      mid.get right=hp.get right ∧ out.get right=hp.get right ∧
      [ym.2.heap.get 0,ym.2.heap.get 1,ym.2.heap.get 2]=
        [some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (mid.get left)⟩,
         some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (hp.get right)⟩,
         some ⟨SourceUintFixedRefsTy 3,sourceUintFixedRefMemory address [left,left,right]⟩] ∧
      [z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2]=
        [some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (out.get left)⟩,
         some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (hp.get right)⟩,
         some ⟨SourceUintFixedRefsTy 3,sourceUintFixedRefMemory address [left,left,right]⟩] ∧
      ym.1=(sw 1 1 42).1 ∧ z.1=(sw 1 1 42).1 ∧ ym.2.heap.next=3 ∧ z.2.heap.next=3 ∧
      (∀ a,3≤a → ym.2.heap.get a=none ∧ z.2.heap.get a=none) ∧
      ym.2.ex=(sw 1 1 42).2.ex ∧ z.2.ex=(sw 1 1 42).2.ex ∧
      ym.2.events=(sw 1 1 42).2.events ∧ z.2.events=(sw 1 1 42).2.events ∧
      ym.2.logs=(sw 1 1 42).2.logs ∧ z.2.logs=(sw 1 1 42).2.logs ∧
      ym.2.fnLocals=(sw 1 1 42).2.fnLocals ∧ z.2.fnLocals=(sw 1 1 42).2.fnLocals := by
  first
  | solve | simp only [] | omega
  | obtain ⟨mid,ym,tw,ew,swm,rm,mm,read42,contents,sibling,table,lm,nm,bounded,wm,em,lgm,fm⟩ := nested_mutation pipeline (horizon+1) nps
    have parent : mid.get root=hp.get root := by
      have canonical : hp.writeAddr (.index left .fixed (u 1)) (u 42)=
          some (hp.set left (MObj.setElem .fixed (hp.get left) 1 (u 42))) := by
        have valid : (u 1).1.toNat<(MObj.elems .fixed (hp.get left)).length := by rw [MObj.elems_fixed,(hp.get left).2];decide
        simp only [Heap.writeAddr,Heap.setIndex,valid,↓reduceIte];rfl
      rw [Option.some.inj (tw.symm.trans canonical)]
      exact Heap.get_set_ne hp left root (by decide) _
    have middleIndex : mid.index root .dyn (u 1)=some left := by
      change (MObj.elems .dyn (mid.get root))[1]?=some left
      rw [parent];exact selectLeft
    have sep : ∀ t∈MObj.elems .dyn (mid.get root),t.id≠left.id → address t.id≠address left.id := by
      rw [parent];exact selectedSeparation
    obtain ⟨out,z,td,ed,sd,rz,mz,lz,nz,pz,oz,az,wz,ez,lgz,fz⟩ :=
      rm.resolved_delete (G0 pipeline) F0 horizon nps wr wi wj (u 1) (u 1) left
        (by rw [lm];rfl) (by rw [lm];rfl) (by rw [lm];rfl) middleIndex sep (by decide) SH mm
    have outEq : out=mid.set left (MObj.setElem .fixed (mid.get left) 1 (PrimTy.dflt .uint)) := by
      have canonical : mid.writeAddr (.index left .fixed (u 1)) (PrimTy.dflt .uint)=
          some (mid.set left (MObj.setElem .fixed (mid.get left) 1 (PrimTy.dflt .uint))) := by
        have valid : (u 1).1.toNat<(MObj.elems .fixed (mid.get left)).length := by rw [contents];decide
        simp only [Heap.writeAddr,Heap.setIndex,valid,↓reduceIte];rfl
      exact Option.some.inj (td.symm.trans canonical)
    have cleared : MObj.elems .fixed (out.get left)=[u 7,u 0,u (W-1)] := by
      rw [outEq,Heap.get_set_same,MObj.elems_setElem,contents];rfl
    have leftNow := rz.children left (by rw [pz,parent,parentElements];exact List.mem_cons_self)
    change z.2.heap.get 0=some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (out.get left)⟩ at leftNow
    have rightNow := (az 1 (by decide)).trans (show ym.2.heap.get 1=some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (hp.get right)⟩ from (List.cons.inj table).2 |> List.cons.inj |> And.left)
    have parentNow := rz.parent
    rw [pz,parent,parentElements] at parentNow
    refine ⟨mid,out,ym,z,tw,td,swm,source_items_pair_run (G0 pipeline) F0 (horizon+1) nps _ _ (sw 1 1 42) ym z swm sd,
      rm,rz,mm,mz,contents,cleared,(by rw [contents,cleared];decide),sibling,(oz right (by decide)).trans sibling,table,?_,lm,lz.trans lm,nm,nz.trans nm,?_,
      wm,wz.trans wm,em,ez.trans em,lgm,lgz.trans lgm,fm,fz.trans fm⟩
    · rw [leftNow,rightNow,parentNow]
    · intro a ha
      exact ⟨bounded a ha,z.2.heap.bounded a (by rw [nz,nm];exact ha)⟩

/-- At any actual reached state, horizon zero times out before deletion and
retains that state; this is not a transaction rollback theorem. -/
theorem nested_delete_zero_horizon (pipeline : Roadmap.Pipeline) (y : Source.EMState E0 ΓW) :
    (Source.evalE (G0 pipeline) F0 0 (sourceUintFixedNestedDelete wr wi wj)).run y=(.error .timeout,y) := by
  first | rfl | simp only [] | decide

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.nested_mutation_delete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_mutation_delete
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.nested_delete_zero_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_delete_zero_horizon


private def CT : Contract := {vars := []}
private abbrev ΔT : Ctx := [.val .uint,.val .uint,.val .uint,.mem P]
private def ti : Idx ΔT (.val .uint) := .here
private def tj : Idx ΔT (.val .uint) := .there .here
private def tv : Idx ΔT (.val .uint) := .there (.there .here)
private def tr : Idx ΔT (.mem P) := .there (.there (.there .here))
private def st : State CT ΔT := {storage := Storage.init CT,H := H,heap := hp,env := (u 1,u 1,u 42,some root,())}
private def writeStmt : Stmt CT ΔT ΔT :=
  .assignMem (.index .fixed (uintFixedChildPath tr ti) (.simple (.local tj))) (.val (.simple (.local tv)))
private def deleteStmt : Stmt CT ΔT ΔT :=
  .deleteMem (.loc (.index .fixed (uintFixedChildPath tr ti) (.simple (.local tj)))) rfl

/-- The actual Source Items output heaps also drive one existing intrinsic Prog;
this is not a replacement evaluator or a supplied second successful run. -/
theorem nested_typed_program (pipeline : Roadmap.Pipeline) (horizon nps : Nat) :
    ∃ (mid out : Heap H) (ym z : Source.EMState E0 ΓW),
      (Source.execS (G0 pipeline) F0 (horizon+6) nps none
        (.expr (sourceUintFixedNestedAssign wr wi wj wv) : Source.RStmt E0 [] false .body ΓW ΓW) (sw 1 1 42).1).run (.nil,(sw 1 1 42).2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execItems (G0 pipeline) F0 (horizon+7) nps none
        (.stmt (.expr (sourceUintFixedNestedAssign wr wi wj wv)) (.stmt (.expr (sourceUintFixedNestedDelete wr wi wj)) .nil) : Source.RItems E0 [] false .body ΓW ΓW) (sw 1 1 42).1).run (.nil,(sw 1 1 42).2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      Stmt.run st writeStmt=.ok ⟨st.withHeap mid,List.prefix_refl _⟩ ∧
      Stmt.run (st.withHeap mid) deleteStmt=.ok ⟨st.withHeap out,List.prefix_refl _⟩ ∧
      Prog.run st (.cons writeStmt (.cons deleteStmt .nil))=.ok ⟨st.withHeap out,List.prefix_refl _⟩ ∧
      SourceUintFixedRefsAt ym 2 mid root address ∧ SourceUintFixedRefsAt z 2 out root address ∧
      MObj.elems .fixed (mid.get left)=[u 7,u 42,u (W-1)] ∧
      MObj.elems .fixed (out.get left)=[u 7,u 0,u (W-1)] ∧ out.get right=hp.get right := by
  first
  | solve | simp only [] | omega
  | obtain ⟨mid,out,ym,z,tw,td,first,items,rm,rz,mm,mz,cm,cz,diff,om,oz,tablem,tablez,lm,lz,nm,nz,bounded,wm,wz,em,ez,lgm,lgz,fm,fz⟩ := nested_mutation_delete pipeline horizon nps
    have parent : mid.get root=hp.get root := by
      have canonical : hp.writeAddr (.index left .fixed (u 1)) (u 42)=some (hp.set left (MObj.setElem .fixed (hp.get left) 1 (u 42))) := by
        have valid : (u 1).1.toNat<(MObj.elems .fixed (hp.get left)).length := by rw [MObj.elems_fixed,(hp.get left).2];decide
        simp only [Heap.writeAddr,Heap.setIndex,valid,↓reduceIte];rfl
      rw [Option.some.inj (tw.symm.trans canonical)]
      exact Heap.get_set_ne hp left root (by decide) _
    have selected0 : (uintFixedChildPath (C := CT) tr ti).mvalT st=.ok left := by
      change TRes.ofOpt (hp.index root .dyn (u 1))=.ok left
      rw [selectLeft];rfl
    have firstRun : Stmt.run st writeStmt=.ok ⟨st.withHeap mid,List.prefix_refl _⟩ := by
      change TRun.assignMem (.index .fixed (uintFixedChildPath tr ti) (.simple (.local tj))) (.val (.simple (.local tv))) st=_
      simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,selected0,Val.evalT,Simple.evalT,
        show TEnv.get tv st.env=u 42 from rfl,show TEnv.get tj st.env=u 1 from rfl,
        bind,Except.bind,TRes.ofOpt,pure,Except.pure]
      change (TRes.ofOpt (hp.writeAddr (.index left .fixed (u 1)) (u 42)) >>= fun hp' => pure (⟨st.withHeap hp',List.prefix_refl _⟩ : Solidity.Out CT H ΔT))=_
      rw [tw];rfl
    have selected : mid.index root .dyn (u 1)=some left := by
      change (MObj.elems .dyn (mid.get root))[1]?=some left
      rw [parent];exact selectLeft
    have selected1 : (uintFixedChildPath (C := CT) tr ti).mvalT (st.withHeap mid)=.ok left := by
      change TRes.ofOpt (mid.index root .dyn (u 1))=.ok left
      rw [selected];rfl
    have secondRun : Stmt.run (st.withHeap mid) deleteStmt=.ok ⟨st.withHeap out,List.prefix_refl _⟩ := by
      change TRun.deleteMem (.loc (.index .fixed (uintFixedChildPath tr ti) (.simple (.local tj)))) (st.withHeap mid)=_
      rw [Evm.Memory.deleteMem_primitive_eq_assign]
      simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,selected1,Evm.Memory.deleteDefaultValue_eval,
        Val.evalT,Simple.evalT,show TEnv.get tj (st.withHeap mid).env=u 1 from rfl,
        bind,Except.bind,TRes.ofOpt,pure,Except.pure]
      change (TRes.ofOpt (mid.writeAddr (.index left .fixed (u 1)) (PrimTy.dflt .uint)) >>= fun hp' => pure (⟨st.withHeap hp',List.prefix_refl _⟩ : Solidity.Out CT H ΔT))=_
      rw [td];rfl
    exact ⟨mid,out,ym,z,first,items,firstRun,secondRun,intrinsic_heap_pair_run st writeStmt deleteStmt mid out firstRun secondRun,rm,rz,cm,cz,oz⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.nested_typed_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_typed_program


private def stEnd : State CT ΔT := {st with env := (u 1,u 3,u 42,some root,())}

/-- The actual changed prefix survives a late fixed endpoint failure. Source
retains its reached state; intrinsic failure supplies no returned state. -/
theorem nested_late_endpoint (pipeline : Roadmap.Pipeline) (horizon nps : Nat) :
    ∃ (mid : Heap H) (ym : Source.EMState E0 ΓW),
      hp.writeAddr (.index left .fixed (u 1)) (u 42)=some mid ∧
      (Source.execS (G0 pipeline) F0 (horizon+6) nps none
        (.expr (sourceUintFixedNestedAssign wr wi wi wv) : Source.RStmt E0 [] false .body ΓW ΓW) (sw 1 3 42).1).run (.nil,(sw 1 3 42).2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.evalE (G0 pipeline) F0 (horizon+4) (sourceUintFixedNestedAssign wr wi wj wv)).run ym=
        (.error (.revert (Source.panicData .index)),ym) ∧
      (Source.execItems (G0 pipeline) F0 (horizon+7) nps none
        (.stmt (.expr (sourceUintFixedNestedAssign wr wi wi wv)) (.stmt (.expr (sourceUintFixedNestedAssign wr wi wj wv)) .nil) : Source.RItems E0 [] false .body ΓW ΓW) (sw 1 3 42).1).run (.nil,(sw 1 3 42).2)=
          (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      Stmt.run (stEnd.withHeap mid) writeStmt=.error .revert ∧
      SourceUintFixedRefsAt ym 2 mid root address ∧ Source.MemOK E0 SH ym ∧
      MObj.elems .fixed (mid.get left)=[u 7,u 42,u (W-1)] ∧
      MObj.elems .fixed (mid.get left)≠MObj.elems .fixed (hp.get left) ∧ mid.get right=hp.get right ∧
      [ym.2.heap.get 0,ym.2.heap.get 1,ym.2.heap.get 2]=
        [some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (mid.get left)⟩,
         some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (hp.get right)⟩,
         some ⟨SourceUintFixedRefsTy 3,sourceUintFixedRefMemory address [left,left,right]⟩] ∧
      ym.1=(sw 1 3 42).1 ∧ ym.2.heap.next=3 ∧ (∀ a,3≤a → ym.2.heap.get a=none) ∧
      ym.2.ex=(sw 1 3 42).2.ex ∧ ym.2.events=(sw 1 3 42).2.events ∧
      ym.2.logs=(sw 1 3 42).2.logs ∧ ym.2.fnLocals=(sw 1 3 42).2.fnLocals := by
  first
  | solve | simp only [] | omega
  | obtain ⟨mid,ym,tw,ew,first,rm,mm,lm,nm,parent,objects,addresses,wm,em,lgm,fm⟩ :=
      (graphW 1 3 42).resolved_write (G0 pipeline) F0 (horizon+1) nps wr wi wi wv
        (u 1) (u 1) (u 42) left rfl rfl rfl rfl selectLeft selectedSeparation (by decide) SH (memOKW 1 3 42)
    have selected : mid.index root .dyn (u 1)=some left := by
      change (MObj.elems .dyn (mid.get root))[1]?=some left
      rw [parent];exact selectLeft
    have loc := rm.eval_nested_loc_bounds (G0 pipeline) F0 horizon wr wi wj (u 1) (u 3) left
      (by rw [lm];rfl) (by rw [lm];rfl) (by rw [lm];rfl) selected (by decide)
    have failed : (Source.evalE (G0 pipeline) F0 (horizon+4) (sourceUintFixedNestedAssign wr wi wj wv)).run ym=
        (.error (.revert (Source.panicData .index)),ym) := by
      rw [sourceUintFixedNestedAssign,Source.evalE,Source.Hoare.run_bind,
        source_local_value_run (G0 pipeline) F0 (horizon+2) ym wv (sourceUint (u 42)) (by rw [lm];rfl)]
      change ((Source.evalLoc (G0 pipeline) F0 (horizon+3) (sourceUintFixedNestedLoc wr wi wj)) >>= fun loc =>
        Source.writeLoc F0 (horizon+3) loc (sourceUint (u 42)) >>= fun _ => pure (Source.RVal.val (sourceUint (u 42)))).run ym=_
      rw [Source.Hoare.run_bind,loc]
    have second := source_expr_statement_error (G0 pipeline) F0 (horizon+4) nps _ ym ym _ failed
    have typedSelected : (uintFixedChildPath (C := CT) tr ti).mvalT (stEnd.withHeap mid)=.ok left := by
      change TRes.ofOpt (mid.index root .dyn (u 1))=.ok left
      rw [selected];rfl
    have rejected : mid.writeAddr (.index left .fixed (u 3)) (u 42)=none := by
      have length : (MObj.elems .fixed (mid.get left)).length=3 := by rw [MObj.elems_fixed];exact (mid.get left).2
      simp only [Heap.writeAddr,Heap.setIndex,length,show ¬(u 3).1.toNat<3 from by decide,↓reduceIte]
    have intrinsic : Stmt.run (stEnd.withHeap mid) writeStmt=.error .revert := by
      change TRun.assignMem (.index .fixed (uintFixedChildPath tr ti) (.simple (.local tj))) (.val (.simple (.local tv))) (stEnd.withHeap mid)=_
      simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,typedSelected,Val.evalT,Simple.evalT,
        show TEnv.get tv (stEnd.withHeap mid).env=u 42 from rfl,show TEnv.get tj (stEnd.withHeap mid).env=u 3 from rfl,
        bind,Except.bind,TRes.ofOpt,pure,Except.pure]
      change TRes.ofOpt (mid.writeAddr (.index left .fixed (u 3)) (u 42)) >>= _ = _
      rw [rejected];rfl
    have canonical : hp.writeAddr (.index left .fixed (u 1)) (u 42)=some (hp.set left (MObj.setElem .fixed (hp.get left) 1 (u 42))) := by
      have valid : (u 1).1.toNat<(MObj.elems .fixed (hp.get left)).length := by rw [MObj.elems_fixed,(hp.get left).2];decide
      simp only [Heap.writeAddr,Heap.setIndex,valid,↓reduceIte];rfl
    have contents : MObj.elems .fixed (mid.get left)=[u 7,u 42,u (W-1)] := by
      rw [Option.some.inj (tw.symm.trans canonical),Heap.get_set_same,MObj.elems_setElem,MObj.elems_fixed];rfl
    have leftNow := rm.children left (by rw [parent,parentElements];exact List.mem_cons_self)
    change ym.2.heap.get 0=some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (mid.get left)⟩ at leftNow
    have rightNow := (addresses 1 (by decide)).trans (show (sw 1 3 42).2.heap.get 1=some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (hp.get right)⟩ from rfl)
    have parentNow := rm.parent
    rw [parent,parentElements] at parentNow
    refine ⟨mid,ym,tw,first,failed,source_items_pair_error (G0 pipeline) F0 (horizon+1) nps _ _ (sw 1 3 42) ym ym _ first second,
      intrinsic,rm,mm,contents,(by rw [contents,MObj.elems_fixed];decide),objects right (by decide),?_,lm,nm,?_,wm,em,lgm,fm⟩
    · rw [leftNow,rightNow,parentNow]
    · intro a ha;exact ym.2.heap.bounded a (by rw [nm];exact ha)

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.nested_late_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_late_endpoint


private def prefixStmt : Stmt CT ΔT ΔT :=
  .assignMem (.index .fixed (uintFixedChildPath tr ti) (.simple (.local ti))) (.val (.simple (.local tv)))

/-- Same actual Source prefix also runs as the intrinsic prefix, before the
second statement rejects. The Prog error itself exposes no output state. -/
theorem nested_late_program (pipeline : Roadmap.Pipeline) (horizon nps : Nat) :
    ∃ (mid : Heap H) (ym : Source.EMState E0 ΓW),
      (Source.execS (G0 pipeline) F0 (horizon+6) nps none
        (.expr (sourceUintFixedNestedAssign wr wi wi wv) : Source.RStmt E0 [] false .body ΓW ΓW) (sw 1 3 42).1).run (.nil,(sw 1 3 42).2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execItems (G0 pipeline) F0 (horizon+7) nps none
        (.stmt (.expr (sourceUintFixedNestedAssign wr wi wi wv)) (.stmt (.expr (sourceUintFixedNestedAssign wr wi wj wv)) .nil) : Source.RItems E0 [] false .body ΓW ΓW) (sw 1 3 42).1).run (.nil,(sw 1 3 42).2)=
          (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      Stmt.run stEnd prefixStmt=.ok ⟨stEnd.withHeap mid,List.prefix_refl _⟩ ∧
      Stmt.run (stEnd.withHeap mid) writeStmt=.error .revert ∧
      Prog.run stEnd (.cons prefixStmt (.cons writeStmt .nil))=.error .revert ∧
      SourceUintFixedRefsAt ym 2 mid root address ∧ Source.MemOK E0 SH ym ∧
      MObj.elems .fixed (mid.get left)=[u 7,u 42,u (W-1)] ∧ mid.get right=hp.get right ∧
      [ym.2.heap.get 0,ym.2.heap.get 1,ym.2.heap.get 2]=
        [some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (mid.get left)⟩,
         some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (hp.get right)⟩,
         some ⟨SourceUintFixedRefsTy 3,sourceUintFixedRefMemory address [left,left,right]⟩] ∧
      ym.1=(sw 1 3 42).1 ∧ ym.2.heap.next=3 ∧ (∀ a,3≤a → ym.2.heap.get a=none) ∧
      ym.2.ex=(sw 1 3 42).2.ex ∧ ym.2.events=(sw 1 3 42).2.events ∧
      ym.2.logs=(sw 1 3 42).2.logs ∧ ym.2.fnLocals=(sw 1 3 42).2.fnLocals := by
  first
  | solve | simp only [] | omega
  | obtain ⟨mid,ym,tw,first,failed,items,intrinsic,rm,mm,contents,changed,sibling,table,locals,next,bounded,world,events,logs,fnLocals⟩ := nested_late_endpoint pipeline horizon nps
    have selected : (uintFixedChildPath (C := CT) tr ti).mvalT stEnd=.ok left := by
      change TRes.ofOpt (hp.index root .dyn (u 1))=.ok left
      rw [selectLeft];rfl
    have prefixRun : Stmt.run stEnd prefixStmt=.ok ⟨stEnd.withHeap mid,List.prefix_refl _⟩ := by
      change TRun.assignMem (.index .fixed (uintFixedChildPath tr ti) (.simple (.local ti))) (.val (.simple (.local tv))) stEnd=_
      simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,selected,Val.evalT,Simple.evalT,
        show TEnv.get tv stEnd.env=u 42 from rfl,show TEnv.get ti stEnd.env=u 1 from rfl,
        bind,Except.bind,TRes.ofOpt,pure,Except.pure]
      change (TRes.ofOpt (hp.writeAddr (.index left .fixed (u 1)) (u 42)) >>= fun hp' => pure (⟨stEnd.withHeap hp',List.prefix_refl _⟩ : Solidity.Out CT H ΔT))=_
      rw [tw];rfl
    exact ⟨mid,ym,first,items,prefixRun,intrinsic,intrinsic_heap_pair_error stEnd prefixStmt writeStmt mid .revert prefixRun intrinsic,
      rm,mm,contents,sibling,table,locals,next,bounded,world,events,logs,fnLocals⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.nested_late_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_late_program


private def wordBase (id : Nat) : Fin W := if id=0 then wmod 16 else if id=1 then wmod 8 else wmod 24
private def wordMachine : Machine := {Machine.init with stack := [w[77],w[88]],mem := fun c =>
  if c=0 then w[32] else if c=1 then w[16] else if c=2 then w[42] else if c=3 ∨ c=4 then w[1]
  else if c=16 then w[3] else if c=17 ∨ c=18 then w[8] else if c=19 then w[24]
  else if c=8 then w[7] else if c=10 then (Word.val (wmod (W-1)))
  else if c=24 then w[8] else if c=25 then w[9] else if c=26 then w[10] else w[0]}
private theorem parentLength : hp.len root .dyn=3 := by
  simp only [Heap.len,MObj.elems_dyn];rfl
private theorem refs {Q : RefTy} (q : HRef H Q) :
    (Q=P ∧ HEq q root) ∨ (Q=A ∧ HEq q left) ∨ (Q=A ∧ HEq q right) := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi;exact .inl ⟨rfl,HEq.rfl⟩
  | succ i => cases i with
    | zero => cases hi;exact .inr (.inl ⟨rfl,HEq.rfl⟩)
    | succ i => cases i with
      | zero => cases hi;exact .inr (.inr ⟨rfl,HEq.rfl⟩)
      | succ i => cases hi
private theorem wordHeap : Objects.HeapRepr hp wordBase 5 wordMachine := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · intro Q q
    rcases refs q with ⟨rfl,hq⟩ | ⟨rfl,hq⟩ | ⟨rfl,hq⟩ <;> cases hq <;> decide
  · intro Q q
    rcases refs q with ⟨rfl,hq⟩ | ⟨rfl,hq⟩ | ⟨rfl,hq⟩ <;> cases hq
    all_goals simp only [Objects.cells,parentLength];decide
  · intro Q V q r hn
    rcases refs q with ⟨rfl,hq⟩ | ⟨rfl,hq⟩ | ⟨rfl,hq⟩ <;> cases hq
      <;> rcases refs r with ⟨rfl,hr⟩ | ⟨rfl,hr⟩ | ⟨rfl,hr⟩ <;> cases hr
      <;> first | exact (hn rfl).elim | (simp only [Objects.cells,parentLength];decide)
  · intro Q V a r
    rcases refs r with ⟨rfl,hr⟩ | ⟨rfl,hr⟩ | ⟨rfl,hr⟩ <;> cases hr <;> cases a
    all_goals
      refine ⟨?_,?_,?_⟩
      · simp only [Objects.cells,parentLength];decide
      · intro hh
        first | cases (by simpa only [Objects.header] using hh : (0 : Nat)=1)
              | (rw [parentLength];rfl)
      · intro i v hit
        first
        | rw [parentElements] at hit
          cases i with
          | zero => cases hit;rfl
          | succ i => cases i with
            | zero => cases hit;rfl
            | succ i => cases i with
              | zero => cases hit;rfl
              | succ i => cases hit
        | rw [MObj.elems_fixed] at hit
          cases i with
          | zero => cases hit;exact ReprV.uint_of rfl
          | succ i => cases i with
            | zero => cases hit;exact ReprV.uint_of rfl
            | succ i => cases i with
              | zero => first | (cases hit;exact ReprV.uint_of rfl) | cases hit
              | succ i => cases hit
  · intro s r
    rcases refs r with ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ <;> cases eq
  · intro s f Q r hf
    rcases refs r with ⟨eq,_⟩ | ⟨eq,_⟩ | ⟨eq,_⟩ <;> cases eq
private theorem wordRepr : Objects.StateRepr 1 1 5 (Frag.init ΔT) st wordBase wordMachine := by
  have hc := Sim.init CT 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨?_,wordHeap,?_,by decide⟩
  · refine ⟨hc.store,?_,?_,hc.net,hc.netSelf,hc.bound,?_,hc.env,hc.funds,hc.oracle⟩
    · intro p i
      cases i with
      | here => exact ReprV.uint_of rfl
      | there i => cases i with
        | here => exact ReprV.uint_of rfl
        | there i => cases i with
          | here => exact ReprV.uint_of rfl
          | there i => cases i with | there i => nomatch i
    · intro Q i hi
      cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro Q i hi
      cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
  · intro Q i
    cases i with | there i => cases i with | there i => cases i with | there i => cases i with
      | here => exact ⟨root,rfl,rfl⟩
      | there i => nomatch i

private theorem wordAllocator : Objects.AllocatorRepr hp wordBase 5 ⟨32,by decide⟩ wordMachine := by
  refine ⟨wordHeap,⟨by decide,by decide,rfl,?_⟩,?_⟩
  · intro a ha
    change 32≤a at ha
    simp only [wordMachine,if_neg (show a≠0 by omega),if_neg (show a≠1 by omega),
      if_neg (show a≠2 by omega),if_neg (show ¬(a=3 ∨ a=4) by omega),if_neg (show a≠16 by omega),
      if_neg (show ¬(a=17 ∨ a=18) by omega),if_neg (show a≠19 by omega),if_neg (show a≠8 by omega),
      if_neg (show a≠10 by omega),if_neg (show a≠24 by omega),if_neg (show a≠25 by omega),if_neg (show a≠26 by omega)]
  · intro Q q
    rcases refs q with ⟨rfl,hq⟩ | ⟨rfl,hq⟩ | ⟨rfl,hq⟩ <;> cases hq
    all_goals simp only [Objects.cells,parentLength];decide

/-- Actual populated strong Objects input for the existing Source fixture. -/
theorem nested_word_initial : Objects.StateRepr 1 1 5 (Frag.init ΔT) st wordBase wordMachine ∧
    Objects.AllocatorRepr hp wordBase 5 ⟨32,by decide⟩ wordMachine ∧
    SourceUintFixedRefsAt (sw 1 1 42) 2 hp root address ∧ Source.MemOK E0 SH (sw 1 1 42) :=
  ⟨wordRepr,wordAllocator,graphW 1 1 42,memOKW 1 1 42⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.nested_word_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_word_initial


/-- Actual whole-word write/delete on the same inhabited Source/typed graph.
The full initial word table and saved stack are explicit; both reached Objects
representations and the final complete allocator are derived. -/
theorem nested_word_program (pipeline : Roadmap.Pipeline) (horizon nps : Nat) :
    ∃ (mid out : Heap H) (ym z : Source.EMState E0 ΓW) (mm target : Machine),
      [wordMachine.mem 0,wordMachine.mem 1,wordMachine.mem 2,wordMachine.mem 3,wordMachine.mem 4,
        wordMachine.mem 8,wordMachine.mem 9,wordMachine.mem 10,wordMachine.mem 11,
        wordMachine.mem 16,wordMachine.mem 17,wordMachine.mem 18,wordMachine.mem 19,
        wordMachine.mem 24,wordMachine.mem 25,wordMachine.mem 26]=
        [w[32],w[16],w[42],w[1],w[1],w[7],w[0],.val (wmod (W-1)),w[0],w[3],w[8],w[8],w[24],w[8],w[9],w[10]] ∧
      (Source.execItems (G0 pipeline) F0 (horizon+7) nps none
        (.stmt (.expr (sourceUintFixedNestedAssign wr wi wi wv)) (.stmt (.expr (sourceUintFixedNestedDelete wr wi wj)) .nil) : Source.RItems E0 [] false .body ΓW ΓW) (sw 1 1 42).1).run (.nil,(sw 1 1 42).2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      Evm.run (uintFixedChildWriteCode (C := CT) 1 tr ti ti tv) wordMachine=.ok mm 0 ∧
      Evm.run (uintFixedChildDeleteCode (C := CT) 1 tr ti tj) mm=.ok target 0 ∧
      Evm.run (uintFixedChildWriteCode (C := CT) 1 tr ti ti tv ++ uintFixedChildDeleteCode (C := CT) 1 tr ti tj) wordMachine=.ok target 0 ∧
      SourceUintFixedRefsAt ym 2 mid root address ∧ SourceUintFixedRefsAt z 2 out root address ∧
      Source.MemOK E0 SH ym ∧ Source.MemOK E0 SH z ∧
      Objects.StateRepr 1 1 5 (Frag.init ΔT) (st.withHeap mid) wordBase mm ∧
      Objects.StateRepr 1 1 5 (Frag.init ΔT) (st.withHeap out) wordBase target ∧
      Objects.AllocatorRepr out wordBase 5 ⟨32,by decide⟩ target ∧ target.stack=[w[77],w[88]] ∧
      MObj.elems .fixed (mid.get left)=[u 7,u 42,u (W-1)] ∧
      (MObj.elems .dyn (out.get root),MObj.elems .fixed (out.get left),MObj.elems .fixed (out.get right))=
        ([left,left,right],[u 7,u 0,u (W-1)],[u 8,u 9,u 10]) := by
  first
  | solve | simp only [] | omega
  | obtain ⟨mid,out,ym,z,mm,target,tw,td,first,second,items,prog,cw,cd,append,rm,rz,mok,mokz,hm,hz,lm,lz,nz,parent,objects,addresses,world,events,logs,fnLocals,stack,allocator⟩ :=
      (graphW 1 1 42).resolved_write_delete_word (G0 pipeline) F0 horizon nps st root address wr wi wj wv tr ti tj tv
        (u 1) (u 1) (u 42) left rfl rfl rfl rfl rfl rfl rfl rfl selectLeft selectedSeparation
        (by decide) (by decide) SH (memOKW 1 1 42) wordRepr
    have canonical : hp.writeAddr (.index left .fixed (u 1)) (u 42)=some (hp.set left (MObj.setElem .fixed (hp.get left) 1 (u 42))) := by
      have valid : (u 1).1.toNat<(MObj.elems .fixed (hp.get left)).length := by rw [MObj.elems_fixed,(hp.get left).2];decide
      simp only [Heap.writeAddr,Heap.setIndex,valid,↓reduceIte];rfl
    have contents : MObj.elems .fixed (mid.get left)=[u 7,u 42,u (W-1)] := by
      rw [Option.some.inj (tw.symm.trans canonical),Heap.get_set_same,MObj.elems_setElem,MObj.elems_fixed];rfl
    have clear : mid.writeAddr (.index left .fixed (u 1)) (PrimTy.dflt .uint)=some (mid.set left (MObj.setElem .fixed (mid.get left) 1 (PrimTy.dflt .uint))) := by
      have valid : (u 1).1.toNat<(MObj.elems .fixed (mid.get left)).length := by rw [contents];decide
      simp only [Heap.writeAddr,Heap.setIndex,valid,↓reduceIte];rfl
    have final : MObj.elems .fixed (out.get left)=[u 7,u 0,u (W-1)] := by
      rw [Option.some.inj (td.symm.trans clear),Heap.get_set_same,MObj.elems_setElem,contents];rfl
    refine ⟨mid,out,ym,z,mm,target,rfl,items,cw,cd,append,rm,rz,mok,mokz,hm,hz,
      allocator ⟨32,by decide⟩ (by decide) wordAllocator,stack,contents,?_⟩
    rw [parent,final,objects right (by decide)]
    change (MObj.elems .dyn (hp.get root),[u 7,u 0,u (W-1)],MObj.elems .fixed (hp.get right))=_
    rw [parentElements,MObj.elems_fixed];rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.nested_word_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_word_program


private def wordTable (m : Machine) : List Word :=
  [m.mem 0,m.mem 1,m.mem 2,m.mem 3,m.mem 4,m.mem 8,m.mem 9,m.mem 10,m.mem 11,
   m.mem 16,m.mem 17,m.mem 18,m.mem 19,m.mem 24,m.mem 25,m.mem 26]
private def beforeWords : List Word :=
  [w[32],w[16],w[42],w[1],w[1],w[7],w[0],.val (wmod (W-1)),w[0],w[3],w[8],w[8],w[24],w[8],w[9],w[10]]

/-- Complete initial/prefix/final raw word tables, including padding and every
represented local/object word, derived from the actual shared program runs. -/
theorem nested_word_tables (pipeline : Roadmap.Pipeline) (horizon nps : Nat) :
    ∃ (mid out : Heap H) (ym z : Source.EMState E0 ΓW) (mm target : Machine),
      (Source.execS (G0 pipeline) F0 (horizon+6) nps none
        (.expr (sourceUintFixedNestedAssign wr wi wi wv) : Source.RStmt E0 [] false .body ΓW ΓW) (sw 1 1 42).1).run (.nil,(sw 1 1 42).2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS (G0 pipeline) F0 (horizon+5) nps none
        (.expr (sourceUintFixedNestedDelete wr wi wj) : Source.RStmt E0 [] false .body ΓW ΓW) ym.1).run (.nil,ym.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems (G0 pipeline) F0 (horizon+7) nps none
        (.stmt (.expr (sourceUintFixedNestedAssign wr wi wi wv)) (.stmt (.expr (sourceUintFixedNestedDelete wr wi wj)) .nil) : Source.RItems E0 [] false .body ΓW ΓW) (sw 1 1 42).1).run (.nil,(sw 1 1 42).2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run st (.cons (.assignMem (.index .fixed (uintFixedChildPath tr ti) (.simple (.local ti))) (.val (.simple (.local tv))))
        (.cons (.deleteMem (.loc (.index .fixed (uintFixedChildPath tr ti) (.simple (.local tj)))) rfl) .nil))=
          .ok ⟨st.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (uintFixedChildWriteCode (C := CT) 1 tr ti ti tv) wordMachine=.ok mm 0 ∧
      Evm.run (uintFixedChildDeleteCode (C := CT) 1 tr ti tj) mm=.ok target 0 ∧
      Evm.run (uintFixedChildWriteCode (C := CT) 1 tr ti ti tv ++ uintFixedChildDeleteCode (C := CT) 1 tr ti tj) wordMachine=.ok target 0 ∧
      (wordTable wordMachine,wordTable mm,wordTable target)=(beforeWords,beforeWords.set 6 w[42],beforeWords) ∧
      wordTable mm≠wordTable wordMachine ∧
      SourceUintFixedRefsAt ym 2 mid root address ∧ SourceUintFixedRefsAt z 2 out root address ∧
      Objects.StateRepr 1 1 5 (Frag.init ΔT) (st.withHeap mid) wordBase mm ∧
      Objects.StateRepr 1 1 5 (Frag.init ΔT) (st.withHeap out) wordBase target ∧
      Objects.AllocatorRepr out wordBase 5 ⟨32,by decide⟩ target ∧ mm.stack=[w[77],w[88]] ∧ target.stack=[w[77],w[88]] := by
  first
  | solve | simp only [] | omega
  | obtain ⟨mid,out,ym,z,mm,target,tw,td,first,second,items,prog,cw,cd,append,rm,rz,mok,mokz,hm,hz,lm,lz,nz,parent,objects,addresses,world,events,logs,fnLocals,stack,allocator⟩ :=
      (graphW 1 1 42).resolved_write_delete_word (G0 pipeline) F0 horizon nps st root address wr wi wj wv tr ti tj tv
        (u 1) (u 1) (u 42) left rfl rfl rfl rfl rfl rfl rfl rfl selectLeft selectedSeparation
        (by decide) (by decide) SH (memOKW 1 1 42) wordRepr
    have exactFirst : Evm.run (uintFixedChildWriteCode (C := CT) 1 tr ti ti tv) wordMachine=
        .ok (writeMachine wordMachine 9 w[42]) 0 := by
      exact nested_fixed_store_exact wordRepr tr ti ti (.simple (.local tv)) rfl root left
        (wmod 1) (wmod 1) (wmod 42) rfl rfl rfl rfl selectLeft (by decide)
    have mmEq : mm=writeMachine wordMachine 9 w[42] := (Evm.Out.ok.inj (cw.symm.trans exactFirst)).1
    have canonical : hp.writeAddr (.index left .fixed (u 1)) (u 42)=some (hp.set left (MObj.setElem .fixed (hp.get left) 1 (u 42))) := by
      have valid : (u 1).1.toNat<(MObj.elems .fixed (hp.get left)).length := by rw [MObj.elems_fixed,(hp.get left).2];decide
      simp only [Heap.writeAddr,Heap.setIndex,valid,↓reduceIte];rfl
    have parentMid : mid.get root=hp.get root := by
      rw [Option.some.inj (tw.symm.trans canonical)]
      exact Heap.get_set_ne hp left root (by decide) _
    have selected : mid.index root .dyn (u 1)=some left := by
      change (MObj.elems .dyn (mid.get root))[1]?=some left
      rw [parentMid];exact selectLeft
    have exactSecond : Evm.run (uintFixedChildDeleteCode (C := CT) 1 tr ti tj) mm=
        .ok (writeMachine mm 9 w[0]) 0 := by
      exact nested_fixed_store_exact hm tr ti tj (Evm.Memory.deleteDefaultValue .uint) rfl root left
        (wmod 1) (wmod 1) (wmod 0) rfl rfl rfl rfl selected (by decide)
    have targetEq : target=writeMachine mm 9 w[0] := (Evm.Out.ok.inj (cd.symm.trans exactSecond)).1
    refine ⟨mid,out,ym,z,mm,target,first,second,items,prog,cw,cd,append,?_,?_,rm,rz,hm,hz,
      allocator ⟨32,by decide⟩ (by decide) wordAllocator,?_,stack⟩
    · rw [targetEq,mmEq];rfl
    · rw [mmEq];decide
    · rw [mmEq];rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.nested_word_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_word_tables


private def lateMachine : Machine := writeMachine wordMachine 3 w[3]
private theorem lateRepr : Objects.StateRepr 1 1 5 (Frag.init ΔT) stEnd wordBase lateMachine := by
  exact wordRepr.setVal tj (u 3) w[3] (ReprV.uint_of rfl)
private theorem lateAllocator : Objects.AllocatorRepr hp wordBase 5 ⟨32,by decide⟩ lateMachine :=
  wordAllocator.localWrite 3 (by decide) (by decide) w[3]

/-- Actual endpoint3 initial local/word binding, with unchanged represented
objects and complete allocator; no conditional fixture premise. -/
theorem nested_word_late_initial : Objects.StateRepr 1 1 5 (Frag.init ΔT) stEnd wordBase lateMachine ∧
    Objects.AllocatorRepr hp wordBase 5 ⟨32,by decide⟩ lateMachine ∧
    SourceUintFixedRefsAt (sw 1 3 42) 2 hp root address ∧ Source.MemOK E0 SH (sw 1 3 42) :=
  ⟨lateRepr,lateAllocator,graphW 1 3 42,memOKW 1 3 42⟩

/-- Complete concrete late-revert witness: the materialized prefix table and
Source globals survive at the scope their outcome types expose. No post-revert
word machine, panic payload equality or transaction rollback is asserted. -/
theorem nested_word_late_tables (pipeline : Roadmap.Pipeline) (horizon nps : Nat) :
    ∃ (mid : Heap H) (ym : Source.EMState E0 ΓW) (mm : Machine),
      (Source.execS (G0 pipeline) F0 (horizon+6) nps none
        (.expr (sourceUintFixedNestedAssign wr wi wi wv) : Source.RStmt E0 [] false .body ΓW ΓW) (sw 1 3 42).1).run (.nil,(sw 1 3 42).2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.evalE (G0 pipeline) F0 (horizon+4) (sourceUintFixedNestedAssign wr wi wj wv)).run ym=
        (.error (.revert (Source.panicData .index)),ym) ∧
      (Source.execItems (G0 pipeline) F0 (horizon+7) nps none
        (.stmt (.expr (sourceUintFixedNestedAssign wr wi wi wv)) (.stmt (.expr (sourceUintFixedNestedAssign wr wi wj wv)) .nil) : Source.RItems E0 [] false .body ΓW ΓW) (sw 1 3 42).1).run (.nil,(sw 1 3 42).2)=
          (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      Stmt.run stEnd prefixStmt=.ok ⟨stEnd.withHeap mid,List.prefix_refl _⟩ ∧
      Stmt.run (stEnd.withHeap mid) writeStmt=.error .revert ∧
      Prog.run stEnd (.cons prefixStmt (.cons writeStmt .nil))=.error .revert ∧
      Evm.run (uintFixedChildWriteCode (C := CT) 1 tr ti ti tv) lateMachine=.ok mm 0 ∧
      Evm.run (uintFixedChildWriteCode (C := CT) 1 tr ti tj tv) mm=.revert ∧
      Evm.run (uintFixedChildWriteCode (C := CT) 1 tr ti ti tv ++ uintFixedChildWriteCode (C := CT) 1 tr ti tj tv) lateMachine=.revert ∧
      (wordTable lateMachine,wordTable mm)=(beforeWords.set 3 w[3],(beforeWords.set 3 w[3]).set 6 w[42]) ∧
      wordTable mm≠wordTable lateMachine ∧
      SourceUintFixedRefsAt ym 2 mid root address ∧ Source.MemOK E0 SH ym ∧
      Objects.StateRepr 1 1 5 (Frag.init ΔT) (stEnd.withHeap mid) wordBase mm ∧
      Objects.AllocatorRepr mid wordBase 5 ⟨32,by decide⟩ mm ∧ mm.stack=[w[77],w[88]] ∧
      MObj.elems .fixed (mid.get left)=[u 7,u 42,u (W-1)] ∧ mid.get right=hp.get right ∧
      [ym.2.heap.get 0,ym.2.heap.get 1,ym.2.heap.get 2]=
        [some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (mid.get left)⟩,
         some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (hp.get right)⟩,
         some ⟨SourceUintFixedRefsTy 3,sourceUintFixedRefMemory address [left,left,right]⟩] ∧
      ym.1=(sw 1 3 42).1 ∧ ym.2.heap.next=3 ∧ (∀ a,3≤a → ym.2.heap.get a=none) ∧
      ym.2.ex=(sw 1 3 42).2.ex ∧ ym.2.events=(sw 1 3 42).2.events ∧
      ym.2.logs=(sw 1 3 42).2.logs ∧ ym.2.fnLocals=(sw 1 3 42).2.fnLocals := by
  first
  | solve | simp only [] | omega
  | obtain ⟨mid,ym,mm,tw,first,failed,items,iw,ir,prog,cw,cr,append,rm,mok,hm,locals,next,parent,objects,addresses,world,events,logs,fnLocals,stack,allocator⟩ :=
      (graphW 1 3 42).resolved_write_late_bounds_word (G0 pipeline) F0 horizon nps stEnd root address wr wi wj wv tr ti tj tv
        (u 1) (u 3) (u 42) left rfl rfl rfl rfl rfl rfl rfl rfl selectLeft selectedSeparation
        (by decide) (by decide) SH (memOKW 1 3 42) lateRepr
    have exactFirst : Evm.run (uintFixedChildWriteCode (C := CT) 1 tr ti ti tv) lateMachine=
        .ok (writeMachine lateMachine 9 w[42]) 0 := by
      exact nested_fixed_store_exact lateRepr tr ti ti (.simple (.local tv)) rfl root left
        (wmod 1) (wmod 1) (wmod 42) rfl rfl rfl rfl selectLeft (by decide)
    have mmEq : mm=writeMachine lateMachine 9 w[42] := (Evm.Out.ok.inj (cw.symm.trans exactFirst)).1
    have canonical : hp.writeAddr (.index left .fixed (u 1)) (u 42)=some (hp.set left (MObj.setElem .fixed (hp.get left) 1 (u 42))) := by
      have valid : (u 1).1.toNat<(MObj.elems .fixed (hp.get left)).length := by rw [MObj.elems_fixed,(hp.get left).2];decide
      simp only [Heap.writeAddr,Heap.setIndex,valid,↓reduceIte];rfl
    have contents : MObj.elems .fixed (mid.get left)=[u 7,u 42,u (W-1)] := by
      rw [Option.some.inj (tw.symm.trans canonical),Heap.get_set_same,MObj.elems_setElem,MObj.elems_fixed];rfl
    have sourceParent : mid.get root=hp.get root := parent
    have leftNow := rm.children left (by rw [sourceParent,parentElements];exact List.mem_cons_self)
    change ym.2.heap.get 0=some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (mid.get left)⟩ at leftNow
    have rightNow := (addresses 1 (by decide)).trans (show (sw 1 3 42).2.heap.get 1=some ⟨.array .memory (.int .u256) (some 3),sourceUintFixedObject (hp.get right)⟩ from rfl)
    have parentNow := rm.parent
    rw [sourceParent,parentElements] at parentNow
    refine ⟨mid,ym,mm,first,failed,items,iw,ir,prog,cw,cr,append,?_,?_,rm,mok,hm,
      allocator ⟨32,by decide⟩ (by decide) lateAllocator,stack,contents,objects right (by decide),?_,locals,next,?_,world,events,logs,fnLocals⟩
    · rw [mmEq];rfl
    · rw [mmEq];decide
    · rw [leftNow,rightNow,parentNow]
    · intro a ha;exact ym.2.heap.bounded a (by rw [next];exact ha)

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.nested_word_late_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_word_late_initial
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.nested_word_late_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_word_late_tables


open Physical
private def byteImage : List (Nat×Nat) := [(0,1024),(1,512),(2,42),(3,1),(4,1),(8,7),(9,0),(10,(W-1)),(11,0),(16,3),(17,256),(18,256),(19,768),(24,8),(25,9),(26,10)]
private def physicalBytes : Environment.Memory := byteImage.foldl
  (fun memory cell => Environment.writeBytes memory (32*cell.1) (Semantics.wordBytes cell.2)) (fun _ => 0)
private def numericCells : List Nat := [2,3,4,8,9,10,11,16,24,25,26]
private def pointerCells : List Nat := [0,1,17,18,19]
private theorem byteImage_read (c value : Nat) (hit : (c,value)∈byteImage) :
    Environment.readMemory physicalBytes (32*c) 32=Semantics.wordBytes value := by
  simp only [byteImage,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hit
  rcases hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals
    simp only [physicalBytes,byteImage,List.foldl_cons,List.foldl_nil]
    repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length];omega)
    simpa only [Environment.wordBytes_length] using Environment.read_written (Semantics.wordBytes _) _ _
private theorem byteNumbers : WordFrame wordMachine physicalBytes (fun c => c∈numericCells) := by
  refine ⟨?_,?_⟩
  · intro c hc
    simp only [numericCells,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro c hc
    simp only [numericCells,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨wmod 42,rfl,byteImage_read 2 42 (by decide)⟩
    · exact ⟨wmod 1,rfl,byteImage_read 3 1 (by decide)⟩
    · exact ⟨wmod 1,rfl,byteImage_read 4 1 (by decide)⟩
    · exact ⟨wmod 7,rfl,byteImage_read 8 7 (by decide)⟩
    · exact ⟨wmod 0,rfl,byteImage_read 9 0 (by decide)⟩
    · exact ⟨wmod (W-1),rfl,byteImage_read 10 (W-1) (by decide)⟩
    · exact ⟨wmod 0,rfl,byteImage_read 11 0 (by decide)⟩
    · exact ⟨wmod 3,rfl,byteImage_read 16 3 (by decide)⟩
    · exact ⟨wmod 8,rfl,byteImage_read 24 8 (by decide)⟩
    · exact ⟨wmod 9,rfl,byteImage_read 25 9 (by decide)⟩
    · exact ⟨wmod 10,rfl,byteImage_read 26 10 (by decide)⟩

private theorem bytePointers : PointerFrame wordMachine physicalBytes (fun c => c∈pointerCells) := by
  refine ⟨?_,?_⟩
  · intro c hc
    simp only [pointerCells,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro c hc
    simp only [pointerCells,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact ⟨wmod 32,rfl,by decide,byteImage_read 0 1024 (by decide)⟩
    · exact ⟨wmod 16,rfl,by decide,byteImage_read 1 512 (by decide)⟩
    · exact ⟨wmod 8,rfl,by decide,byteImage_read 17 256 (by decide)⟩
    · exact ⟨wmod 8,rfl,by decide,byteImage_read 18 256 (by decide)⟩
    · exact ⟨wmod 24,rfl,by decide,byteImage_read 19 768 (by decide)⟩

/-- Pointer cells are not silently treated as numeric bytes. -/
theorem nested_byte_initial : WordFrame wordMachine physicalBytes (fun c => c∈numericCells) ∧
    PointerFrame wordMachine physicalBytes (fun c => c∈pointerCells) ∧
    ¬CellAt wordMachine physicalBytes 1 := by
  refine ⟨byteNumbers,bytePointers,?_⟩
  intro numeric
  obtain ⟨v,word,bytes⟩ := numeric
  change (Word.val (wmod 16))=Word.val v at word
  have same : v=wmod 16 := (Word.val.inj word).symm
  rw [same] at bytes
  have different : Semantics.wordBytes 512≠Semantics.wordBytes 16 := by decide
  exact different ((byteImage_read 1 512 (by decide)).symm.trans bytes)

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.nested_byte_initial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_byte_initial


/-- Actual nested Source/word write joined to terminal byte MSTORE and the
REVERT observer of its reached bytes. This does not emit the byte-load prefix. -/
theorem nested_physical_prefix (pipeline : Roadmap.Pipeline) (horizon nps : Nat)
    (tail : List Environment.Word) (faultTail : List Roadmap.Word) (suffix : Backend.Program) :
    let next := writeMachine wordMachine 9 w[42]
    let byteNext := Environment.writeBytes physicalBytes 288 (Semantics.wordBytes 42)
    ∃ (out : Heap H) (z : Source.EMState E0 ΓW) (logical offset : Fin W),
      logical.val=9 ∧ offset.val=288 ∧
      (Source.evalE (G0 pipeline) F0 (horizon+4) (sourceUintFixedNestedAssign wr wi wi wv)).run (sw 1 1 42)=
        (.ok (.val (sourceUint (u 42))),z) ∧
      (Source.execS (G0 pipeline) F0 (horizon+5) nps none
        (.expr (sourceUintFixedNestedAssign wr wi wi wv) : Source.RStmt E0 [] false .body ΓW ΓW) (sw 1 1 42).1).run (.nil,(sw 1 1 42).2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      Evm.run (uintFixedChildWriteCode (C := CT) 1 tr ti ti tv) wordMachine=.ok next 0 ∧
      Environment.cryptoStep (.op .MSTORE) ⟨lenU offset.val offset.isLt::lenU 42 (by decide)::tail,physicalBytes⟩=
        some ⟨tail,byteNext⟩ ∧
      WordFrame next byteNext (fun c => c∈numericCells ∨ c=9) ∧ PointerFrame next byteNext (fun c => c∈pointerCells) ∧
      (∀ a,a<288 ∨ 320≤a → byteNext a=physicalBytes a) ∧
      Failure.Slice.run (.op .REVERT::suffix)
        ⟨(⟨offset.val,offset.isLt⟩ : Roadmap.Word)::(⟨32,by decide⟩ : Roadmap.Word)::faultTail,byteNext⟩=
        some (⟨faultTail,byteNext⟩,some (.revert (Semantics.wordBytes 42))) ∧
      SourceUintFixedRefsAt z 2 out root address ∧ Source.MemOK E0 SH z ∧
      Objects.StateRepr 1 1 5 (Frag.init ΔT) (st.withHeap out) wordBase next ∧
      Objects.AllocatorRepr out wordBase 5 ⟨32,by decide⟩ next ∧
      z.1=(sw 1 1 42).1 ∧ z.2.heap.next=3 ∧ out.get root=hp.get root ∧
      (∀ {Q : RefTy} (r : HRef H Q),left.id≠r.id → out.get r=hp.get r) ∧
      (∀ a,a≠0 → z.2.heap.get a=(sw 1 1 42).2.heap.get a) ∧
      z.2.ex=(sw 1 1 42).2.ex ∧ z.2.events=(sw 1 1 42).2.events ∧
      z.2.logs=(sw 1 1 42).2.logs ∧ z.2.fnLocals=(sw 1 1 42).2.fnLocals := by
  first
  | solve | simp only [] | omega
  | dsimp only
    obtain ⟨out,z,target,typed,expr,stmt,intrinsic,code,reached,memOK,repr,locals,next,parent,objects,addresses,world,events,logs,fnLocals,stack,allocator⟩ :=
      (graphW 1 1 42).resolved_write_word (G0 pipeline) F0 horizon nps st root address wr wi wi wv tr ti ti tv
        (u 1) (u 1) (u 42) left rfl rfl rfl rfl rfl rfl rfl rfl selectLeft selectedSeparation
        (by decide) SH (memOKW 1 1 42) wordRepr
    obtain ⟨logical,offset,lc,oc,word,byte,numbers,pointers,frame,revert⟩ :=
      nested_fixed_word_byte_store wordRepr tr ti ti (.simple (.local tv)) rfl root left
        (wmod 1) (wmod 1) (wmod 42) rfl rfl rfl rfl selectLeft (by decide)
        physicalBytes (fun c => c∈numericCells) (fun c => c∈pointerCells) byteNumbers bytePointers (by decide)
        (by intro c hc;simp only [pointerCells,List.mem_cons,List.not_mem_nil,or_false] at hc;rcases hc with rfl|rfl|rfl|rfl|rfl <;> decide)
        tail faultTail suffix
    have same : target=writeMachine wordMachine 9 w[42] := (Evm.Out.ok.inj (code.symm.trans word)).1
    rw [same] at repr allocator
    exact ⟨out,z,logical,offset,lc,oc,expr,stmt,word,byte,numbers,pointers,frame,revert,reached,memOK,repr,
      allocator ⟨32,by decide⟩ (by decide) wordAllocator,locals,next,parent,objects,addresses,world,events,logs,fnLocals⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.nested_physical_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_physical_prefix


private def byteTable (bytes : Environment.Memory) : List (List UInt8) :=
  byteImage.map (fun cv => Environment.readMemory bytes (32*cv.1) 32)

/-- Complete sixteen physical 32-byte rows use scaled pointer values, with
only the actual selected numeric row changed by terminal MSTORE. -/
theorem nested_physical_byte_tables (tail : List Environment.Word) :
    let after := Environment.writeBytes physicalBytes 288 (Semantics.wordBytes 42)
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU 288 (by decide)::lenU 42 (by decide)::tail,physicalBytes⟩=some ⟨tail,after⟩ ∧
    byteTable physicalBytes=byteImage.map (fun cv => Semantics.wordBytes cv.2) ∧
    byteTable after=byteImage.map (fun cv => Semantics.wordBytes (if cv.1=9 then 42 else cv.2)) ∧
    byteTable after≠byteTable physicalBytes := by
  first
  | solve | simp only [] | omega
  | dsimp only
    refine ⟨byte_mstore physicalBytes tail (⟨9,by decide⟩ : Fin W) (⟨42,by decide⟩ : Fin W) (by decide),?_,?_,?_⟩
    · apply List.map_congr_left
      intro cv member
      exact byteImage_read cv.1 cv.2 member
    · apply List.map_congr_left
      intro cv member
      rcases cv with ⟨c,v⟩
      by_cases selected : c=9
      · subst c
        simp only [↓reduceIte]
        simpa only [Environment.wordBytes_length] using Environment.read_written (Semantics.wordBytes 42) 288 physicalBytes
      · simp only [if_neg selected]
        rw [readMemory_write_frame]
        · exact byteImage_read c v member
        · rw [Environment.wordBytes_length];omega
    · intro equal
      have eq := congrArg (fun rows : List (List UInt8) => rows[6]!) equal
      change Environment.readMemory (Environment.writeBytes physicalBytes 288 (Semantics.wordBytes 42)) 288 32=
        Environment.readMemory physicalBytes 288 32 at eq
      have changedRead : Environment.readMemory (Environment.writeBytes physicalBytes 288 (Semantics.wordBytes 42)) 288 32=Semantics.wordBytes 42 := by
        simpa only [Environment.wordBytes_length] using Environment.read_written (Semantics.wordBytes 42) 288 physicalBytes
      rw [changedRead,byteImage_read 9 0 (by decide)] at eq
      exact (by decide : Semantics.wordBytes 42≠Semantics.wordBytes 0) eq

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.nested_physical_byte_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_physical_byte_tables


private def writtenBytes : Environment.Memory := Environment.writeBytes physicalBytes 288 (Semantics.wordBytes 42)
private def clearedBytes : Environment.Memory := Environment.writeBytes writtenBytes 288 (Semantics.wordBytes 0)

/-- Actual overwrite by zero, not checkpoint restoration. Every physical
observation row returns to its initial value by the two store executions. -/
theorem nested_physical_clear_table : byteTable clearedBytes=byteTable physicalBytes := by
  first
  | solve | simp only [] | omega
  | apply List.map_congr_left
    intro cv member
    rcases cv with ⟨c,v⟩
    have initial := byteImage_read c v member
    by_cases selected : c=9
    · subst c
      have zero : v=0 := by
        simp only [byteImage,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
        rcases member with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩
        all_goals omega
      rw [initial,zero]
      simpa only [Environment.wordBytes_length] using Environment.read_written (Semantics.wordBytes 0) 288 writtenBytes
    · have sep1 : 32*c+32≤288 ∨ 288+(Semantics.wordBytes 42).length≤32*c := by rw [Environment.wordBytes_length];omega
      have sep2 : 32*c+32≤288 ∨ 288+(Semantics.wordBytes 0).length≤32*c := by rw [Environment.wordBytes_length];omega
      exact (readMemory_write_frame writtenBytes (32*c) 32 288 (Semantics.wordBytes 0) sep2).trans
        (readMemory_write_frame physicalBytes (32*c) 32 288 (Semantics.wordBytes 42) sep1)

/-- Concrete Source/word write-delete and prepared terminal byte-slice store
pair share the actual reached memories. Live REVERT observes zero after delete,
not rollback or a compiled byte pointer/index prefix. -/
theorem nested_physical_write_delete (pipeline : Roadmap.Pipeline) (horizon nps : Nat)
    (frame : Environment.Frame) (tail : List Environment.Word) (faultTail : List Roadmap.Word) (suffix : Backend.Program) :
    ∃ (mid out : Heap H) (ym z : Source.EMState E0 ΓW) (mm target : Machine) (a1 a2 : Fin W),
      a1.val=288 ∧ a2.val=288 ∧
      (Source.execS (G0 pipeline) F0 (horizon+6) nps none
        (.expr (sourceUintFixedNestedAssign wr wi wi wv) : Source.RStmt E0 [] false .body ΓW ΓW) (sw 1 1 42).1).run (.nil,(sw 1 1 42).2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS (G0 pipeline) F0 (horizon+5) nps none
        (.expr (sourceUintFixedNestedDelete wr wi wj) : Source.RStmt E0 [] false .body ΓW ΓW) ym.1).run (.nil,ym.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems (G0 pipeline) F0 (horizon+7) nps none
        (.stmt (.expr (sourceUintFixedNestedAssign wr wi wi wv)) (.stmt (.expr (sourceUintFixedNestedDelete wr wi wj)) .nil) : Source.RItems E0 [] false .body ΓW ΓW) (sw 1 1 42).1).run (.nil,(sw 1 1 42).2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run st (.cons (.assignMem (.index .fixed (uintFixedChildPath tr ti) (.simple (.local ti))) (.val (.simple (.local tv))))
        (.cons (.deleteMem (.loc (.index .fixed (uintFixedChildPath tr ti) (.simple (.local tj)))) rfl) .nil))=
          .ok ⟨st.withHeap out,List.prefix_refl _⟩ ∧
      Evm.run (uintFixedChildWriteCode (C := CT) 1 tr ti ti tv) wordMachine=.ok mm 0 ∧
      Evm.run (uintFixedChildDeleteCode (C := CT) 1 tr ti tj) mm=.ok target 0 ∧
      Evm.run (uintFixedChildWriteCode (C := CT) 1 tr ti ti tv ++ uintFixedChildDeleteCode (C := CT) 1 tr ti tj) wordMachine=.ok target 0 ∧
      Environment.cryptoStep (.op .MSTORE)
        ⟨lenU a1.val a1.isLt::lenU 42 (by decide)::lenU a2.val a2.isLt::lenU 0 (by decide)::tail,physicalBytes⟩=
          some ⟨lenU a2.val a2.isLt::lenU 0 (by decide)::tail,writtenBytes⟩ ∧
      Environment.cryptoStep (.op .MSTORE)
        ⟨lenU a2.val a2.isLt::lenU 0 (by decide)::tail,writtenBytes⟩=some ⟨tail,clearedBytes⟩ ∧
      Environment.runSlice frame [.op .MSTORE,.op .MSTORE]
        ⟨lenU a1.val a1.isLt::lenU 42 (by decide)::lenU a2.val a2.isLt::lenU 0 (by decide)::tail,physicalBytes⟩=
          some ⟨tail,clearedBytes⟩ ∧
      WordFrame mm writtenBytes (fun c => c∈numericCells ∨ c=9) ∧
      WordFrame target clearedBytes (fun c => (c∈numericCells ∨ c=9) ∨ c=9) ∧
      PointerFrame mm writtenBytes (fun c => c∈pointerCells) ∧ PointerFrame target clearedBytes (fun c => c∈pointerCells) ∧
      byteTable physicalBytes=byteImage.map (fun cv => Semantics.wordBytes cv.2) ∧
      byteTable writtenBytes=byteImage.map (fun cv => Semantics.wordBytes (if cv.1=9 then 42 else cv.2)) ∧
      byteTable clearedBytes=byteTable physicalBytes ∧ byteTable writtenBytes≠byteTable physicalBytes ∧
      Failure.Slice.run (.op .REVERT::suffix)
        ⟨(⟨a2.val,a2.isLt⟩ : Roadmap.Word)::(⟨32,by decide⟩ : Roadmap.Word)::faultTail,clearedBytes⟩=
          some (⟨faultTail,clearedBytes⟩,some (.revert (Semantics.wordBytes 0))) ∧
      SourceUintFixedRefsAt ym 2 mid root address ∧ SourceUintFixedRefsAt z 2 out root address ∧
      Source.MemOK E0 SH ym ∧ Source.MemOK E0 SH z ∧
      Objects.StateRepr 1 1 5 (Frag.init ΔT) (st.withHeap mid) wordBase mm ∧
      Objects.StateRepr 1 1 5 (Frag.init ΔT) (st.withHeap out) wordBase target ∧
      Objects.AllocatorRepr out wordBase 5 ⟨32,by decide⟩ target ∧ target.stack=[w[77],w[88]] ∧
      (∀ a,a<288 ∨ 320≤a → clearedBytes a=physicalBytes a) ∧
      z.1=(sw 1 1 42).1 ∧ z.2.heap.next=3 ∧
      (∀ {Q : RefTy} (r : HRef H Q),left.id≠r.id → out.get r=hp.get r) ∧
      (∀ a,a≠0 → z.2.heap.get a=(sw 1 1 42).2.heap.get a) ∧
      z.2.ex=(sw 1 1 42).2.ex ∧ z.2.events=(sw 1 1 42).2.events ∧
      z.2.logs=(sw 1 1 42).2.logs ∧ z.2.fnLocals=(sw 1 1 42).2.fnLocals := by
  first
  | solve | simp only [] | omega
  | obtain ⟨mid,out,ym,z,mm,target,tw,td,first,second,items,prog,cw,cd,append,rm,rz,mok,mokz,hm,hz,lm,lz,nz,parent,objects,addresses,world,events,logs,fnLocals,stack,allocator⟩ :=
      (graphW 1 1 42).resolved_write_delete_word (G0 pipeline) F0 horizon nps st root address wr wi wj wv tr ti tj tv
        (u 1) (u 1) (u 42) left rfl rfl rfl rfl rfl rfl rfl rfl selectLeft selectedSeparation
        (by decide) (by decide) SH (memOKW 1 1 42) wordRepr
    have exactFirst : Evm.run (uintFixedChildWriteCode (C := CT) 1 tr ti ti tv) wordMachine=.ok (writeMachine wordMachine 9 w[42]) 0 :=
      nested_fixed_store_exact wordRepr tr ti ti (.simple (.local tv)) rfl root left (wmod 1) (wmod 1) (wmod 42)
        rfl rfl rfl rfl selectLeft (by decide)
    have mmEq : mm=writeMachine wordMachine 9 w[42] := (Evm.Out.ok.inj (cw.symm.trans exactFirst)).1
    have canonical : hp.writeAddr (.index left .fixed (u 1)) (u 42)=some (hp.set left (MObj.setElem .fixed (hp.get left) 1 (u 42))) := by
      have valid : (u 1).1.toNat<(MObj.elems .fixed (hp.get left)).length := by rw [MObj.elems_fixed,(hp.get left).2];decide
      simp only [Heap.writeAddr,Heap.setIndex,valid,↓reduceIte];rfl
    have parentMid : mid.get root=hp.get root := by
      rw [Option.some.inj (tw.symm.trans canonical)]
      exact Heap.get_set_ne hp left root (by decide) _
    have selected : mid.index root .dyn (u 1)=some left := by
      change (MObj.elems .dyn (mid.get root))[1]?=some left
      rw [parentMid];exact selectLeft
    have exactSecond : Evm.run (uintFixedChildDeleteCode (C := CT) 1 tr ti tj) mm=.ok (writeMachine mm 9 w[0]) 0 :=
      nested_fixed_store_exact hm tr ti tj (Evm.Memory.deleteDefaultValue .uint) rfl root left (wmod 1) (wmod 1) (wmod 0)
        rfl rfl rfl rfl selected (by decide)
    have targetEq : target=writeMachine mm 9 w[0] := (Evm.Out.ok.inj (cd.symm.trans exactSecond)).1
    have sep : ∀ c,c∈pointerCells → c≠(9 : Nat) := by
      intro c hc;simp only [pointerCells,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl <;> decide
    obtain ⟨a1,a2,h1,h2,bfirst,bsecond,brun,n1,n2,p1,p2,bytesFrame,revert⟩ :=
      word_byte_store_pair byteNumbers bytePointers (wmod 9) (wmod 42) (wmod 9) (wmod 0)
        (by decide) (by decide) sep sep frame tail faultTail suffix
    have observations := nested_physical_byte_tables ([] : List Environment.Word)
    refine ⟨mid,out,ym,z,mm,target,a1,a2,h1,h2,first,second,items,prog,cw,cd,append,bfirst,bsecond,brun,?_,?_,?_,?_,
      observations.2.1,observations.2.2.1,nested_physical_clear_table,observations.2.2.2,revert,rm,rz,mok,mokz,hm,hz,
      allocator ⟨32,by decide⟩ (by decide) wordAllocator,stack,
      (fun a ha => bytesFrame a ha ha),lz,nz,objects,addresses,world,events,logs,fnLocals⟩
    · rw [mmEq];exact n1
    · rw [targetEq,mmEq];exact n2
    · rw [mmEq];exact p1
    · rw [targetEq,mmEq];exact p2

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.nested_physical_clear_table' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_physical_clear_table
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.nested_physical_write_delete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_physical_write_delete


/-- Reversing the actual two terminal stores leaves42 and differs from the
correct delete-after-write table. This is a target local-slice counterexample. -/
theorem nested_physical_wrong_order (frame : Environment.Frame) (tail : List Environment.Word) :
    let reverse := Environment.writeBytes (Environment.writeBytes physicalBytes 288 (Semantics.wordBytes 0)) 288 (Semantics.wordBytes 42)
    ∃ (a1 a2 : Fin W),a1.val=288 ∧ a2.val=288 ∧
      Environment.runSlice frame [.op .MSTORE,.op .MSTORE]
        ⟨lenU a1.val a1.isLt::lenU 0 (by decide)::lenU a2.val a2.isLt::lenU 42 (by decide)::tail,physicalBytes⟩=
          some ⟨tail,reverse⟩ ∧ byteTable reverse≠byteTable clearedBytes := by
  first
  | solve | simp only [] | omega
  | dsimp only
    have sep : ∀ c,c∈pointerCells → c≠(9 : Nat) := by
      intro c hc;simp only [pointerCells,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl <;> decide
    obtain ⟨a1,a2,h1,h2,first,second,run,_⟩ := word_byte_store_pair byteNumbers bytePointers
      (wmod 9) (wmod 0) (wmod 9) (wmod 42) (by decide) (by decide) sep sep frame tail [] []
    refine ⟨a1,a2,h1,h2,run,?_⟩
    intro equal
    have eq := congrArg (fun rows : List (List UInt8) => rows[6]!) equal
    change Environment.readMemory (Environment.writeBytes (Environment.writeBytes physicalBytes 288 (Semantics.wordBytes 0)) 288 (Semantics.wordBytes 42)) 288 32=
      Environment.readMemory clearedBytes 288 32 at eq
    have leftRead : Environment.readMemory (Environment.writeBytes (Environment.writeBytes physicalBytes 288 (Semantics.wordBytes 0)) 288 (Semantics.wordBytes 42)) 288 32=Semantics.wordBytes 42 := by
      simpa only [Environment.wordBytes_length] using Environment.read_written (Semantics.wordBytes 42) 288 (Environment.writeBytes physicalBytes 288 (Semantics.wordBytes 0))
    have rightRead : Environment.readMemory clearedBytes 288 32=Semantics.wordBytes 0 := by
      simpa only [Environment.wordBytes_length] using Environment.read_written (Semantics.wordBytes 0) 288 writtenBytes
    rw [leftRead,rightRead] at eq
    exact (by decide : Semantics.wordBytes 42≠Semantics.wordBytes 0) eq

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedRefsControls.nested_physical_wrong_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nested_physical_wrong_order

end Solidity.Backend.MemoryOps.SourceUintFixedRefsControls
