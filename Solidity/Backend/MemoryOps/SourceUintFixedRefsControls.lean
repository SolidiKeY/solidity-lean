import Solidity.Backend.MemoryOps.SourceUintFixedRefsDelete
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

end Solidity.Backend.MemoryOps.SourceUintFixedRefsControls
