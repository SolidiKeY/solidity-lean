import Solidity.Backend.MemoryOps.SourceNestedMemory
import Solidity.Backend.MemoryOps.SourceNestedSelect
import Solidity.Backend.MemoryOps.SourceNestedMutation
import Solidity.Backend.MemoryOps.SourceNestedAssignment
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceNestedMemoryControls
open Evm Evm.Memory
open Source.SemanticsExamples (E0 F0 s0)
private def C : Contract := {vars := []}
private abbrev B : RefTy := .array (.prim .bool)
private abbrev R : RefTy := BoolRefsRef
private abbrev H : HTy := [B,B,R,R,R]
private def left : HRef H B := ⟨0,rfl⟩
private def right : HRef H B := ⟨1,rfl⟩
private def old : HRef H R := ⟨2,rfl⟩
private def fresh : HRef H R := ⟨3,rfl⟩
private def empty : HRef H R := ⟨4,rfl⟩
private def hp : Heap H := (⟨[true,false,false],by decide⟩,(⟨[false,true,false],by decide⟩,
  (⟨[left],by decide⟩,(⟨[left,right,left],by decide⟩,(⟨[],by decide⟩,())))))
private abbrev Γ0 : Ctx := [.mem R,.mem R,.mem R]
private def σ0 : State C Γ0 := {storage := Storage.init C,H := H,heap := hp,env := (some fresh,(some old,(some old,())))}
private def base (i : Nat) : Fin W := if i=0 then ⟨16,by decide⟩ else if i=1 then ⟨24,by decide⟩ else if i=2 then ⟨32,by decide⟩ else if i=3 then ⟨36,by decide⟩ else ⟨44,by decide⟩
private def machine0 : Machine := {Machine.init with stack := [w[42]],mem := fun a =>
  if a=0 then w[48] else if a=1 then w[32] else if a=2 then w[32] else if a=3 then w[36] else if a=7 then w[99]
  else if a=16 then w[3] else if a=17 then w[1] else if a=24 then w[3] else if a=26 then w[1]
  else if a=32 then w[1] else if a=33 then w[16] else if a=36 then w[3] else if a=37 then w[16]
  else if a=38 then w[24] else if a=39 then w[16] else w[0]}
private theorem prim_refs {p : PrimTy} (q : HRef H (.array (.prim p))) : p=.bool ∧ (HEq q left ∨ HEq q right) := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi;exact ⟨rfl,.inl HEq.rfl⟩
  | succ i => cases i with
    | zero => cases hi;exact ⟨rfl,.inr HEq.rfl⟩
    | succ i => cases i with
      | zero => cases hi
      | succ i => cases i with
        | zero => cases hi
        | succ i => cases i with
          | zero => cases hi
          | succ i => cases hi
private theorem ref_refs {Q : RefTy} (q : HRef H (.array (.ref Q))) : Q=B ∧ (HEq q old ∨ HEq q fresh ∨ HEq q empty) := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi
  | succ i => cases i with
    | zero => cases hi
    | succ i => cases i with
      | zero => cases hi;exact ⟨rfl,.inl HEq.rfl⟩
      | succ i => cases i with
        | zero => cases hi;exact ⟨rfl,.inr (.inl HEq.rfl)⟩
        | succ i => cases i with
          | zero => cases hi;exact ⟨rfl,.inr (.inr HEq.rfl)⟩
          | succ i => cases hi
private theorem no_struct {s : Name} (q : HRef H (.struct s)) : False := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi
  | succ i => cases i with
    | zero => cases hi
    | succ i => cases i with
      | zero => cases hi
      | succ i => cases i with
        | zero => cases hi
        | succ i => cases i with
          | zero => cases hi
          | succ i => cases hi
private theorem left_repr : ArrayRepr hp left (base left.id) machine0 := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Heap.len,Heap.get,Objs.get,hp,left,MObj.elems_dyn] using (show 16+1+3≤W from by decide)
  · simpa only [Heap.len,Heap.get,Objs.get,hp,left,MObj.elems_dyn] using (show machine0.mem 16=.val (wmod 3) from rfl)
  · intro i v hi
    simp only [Heap.get,Objs.get,hp,left,MObj.elems_dyn] at hi
    cases i with
    | zero => cases Option.some.inj hi;rfl
    | succ i => cases i with
      | zero => cases Option.some.inj hi;rfl
      | succ i => cases i with
        | zero => cases Option.some.inj hi;rfl
        | succ i => cases hi
private theorem right_repr : ArrayRepr hp right (base right.id) machine0 := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Heap.len,Heap.get,Objs.get,hp,right,MObj.elems_dyn] using (show 24+1+3≤W from by decide)
  · simpa only [Heap.len,Heap.get,Objs.get,hp,right,MObj.elems_dyn] using (show machine0.mem 24=.val (wmod 3) from rfl)
  · intro i v hi
    simp only [Heap.get,Objs.get,hp,right,MObj.elems_dyn] at hi
    cases i with
    | zero => cases Option.some.inj hi;rfl
    | succ i => cases i with
      | zero => cases Option.some.inj hi;rfl
      | succ i => cases i with
        | zero => cases Option.some.inj hi;rfl
        | succ i => cases hi
private theorem old_repr : RefArrayRepr hp old base machine0 := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Heap.len,Heap.get,Objs.get,hp,old,MObj.elems_dyn] using (show 32+1+1≤W from by decide)
  · simpa only [Heap.len,Heap.get,Objs.get,hp,old,MObj.elems_dyn] using (show machine0.mem 32=.val (wmod 1) from rfl)
  · intro i v hi
    simp only [Heap.get,Objs.get,hp,old,MObj.elems_dyn] at hi
    cases i with
    | zero => cases Option.some.inj hi;rfl
    | succ i => cases hi
private theorem fresh_repr : RefArrayRepr hp fresh base machine0 := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Heap.len,Heap.get,Objs.get,hp,fresh,MObj.elems_dyn] using (show 36+1+3≤W from by decide)
  · simpa only [Heap.len,Heap.get,Objs.get,hp,fresh,MObj.elems_dyn] using (show machine0.mem 36=.val (wmod 3) from rfl)
  · intro i v hi
    simp only [Heap.get,Objs.get,hp,fresh,MObj.elems_dyn] at hi
    cases i with
    | zero => cases Option.some.inj hi;rfl
    | succ i => cases i with
      | zero => cases Option.some.inj hi;rfl
      | succ i => cases i with
        | zero => cases Option.some.inj hi;rfl
        | succ i => cases hi
private theorem empty_repr : RefArrayRepr hp empty base machine0 := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Heap.len,Heap.get,Objs.get,hp,empty,MObj.elems_dyn] using (show 44+1+0≤W from by decide)
  · simpa only [Heap.len,Heap.get,Objs.get,hp,empty,MObj.elems_dyn] using (show machine0.mem 44=.val (wmod 0) from rfl)
  · intro i v hi
    simp only [Heap.get,Objs.get,hp,empty,MObj.elems_dyn] at hi
    cases hi
private theorem initial_state0 : StateRepr 1 1 8 (Frag.init Γ0) σ0 base machine0 := by
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨?_,?_,?_,by decide,?_,?_,RefFieldsRepr.withoutStructs _ _ _ (fun q => no_struct q)⟩
  · refine ⟨hc.store,?_,?_,hc.net,hc.netSelf,hc.bound,?_,hc.env,hc.funds,hc.oracle⟩
    all_goals intro p i;cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
  · refine ⟨?_,?_,?_⟩
    · intro p q;obtain ⟨rfl,hq|hq⟩ := prim_refs q <;> cases hq
      · exact left_repr
      · exact right_repr
    · intro p q;obtain ⟨rfl,hq|hq⟩ := prim_refs q <;> cases hq <;> decide
    · intro p t q z hne
      obtain ⟨rfl,hq|hq⟩ := prim_refs q <;> cases hq
      all_goals obtain ⟨rfl,hz|hz⟩ := prim_refs z <;> cases hz
      all_goals first | exact (hne rfl).elim | (simp only [Heap.len,Heap.get,left,right,MObj.elems_dyn] <;> decide)
  · intro Q i
    cases i with
    | here => exact ⟨fresh,rfl,rfl⟩
    | there i => cases i with
      | here => exact ⟨old,rfl,rfl⟩
      | there i => cases i with
        | here => exact ⟨old,rfl,rfl⟩
        | there i => nomatch i
  · exact ⟨fun q => (no_struct q).elim,fun q => (no_struct q).elim,fun q _ _ => (no_struct q).elim⟩
  · intro p s arr q;exact (no_struct q).elim
private theorem initial_refs0 : RefArrayHeapRepr hp base 8 machine0 := by
  constructor
  · intro Q q;obtain ⟨rfl,hq|hq|hq⟩ := ref_refs q <;> cases hq
    · exact old_repr
    · exact fresh_repr
    · exact empty_repr
  · intro Q q;obtain ⟨rfl,hq|hq|hq⟩ := ref_refs q <;> cases hq <;> decide
  · intro Q T q t hne
    obtain ⟨rfl,hq|hq|hq⟩ := ref_refs q <;> cases hq
    all_goals obtain ⟨rfl,ht|ht|ht⟩ := ref_refs t <;> cases ht
    all_goals first | exact (hne rfl).elim | (simp only [Heap.len,Heap.get,Objs.get,hp,old,fresh,empty,MObj.elems_dyn] <;> decide)
  · intro Q p q t
    obtain ⟨rfl,ht|ht⟩ := prim_refs t <;> cases ht
    all_goals obtain ⟨rfl,hq|hq|hq⟩ := ref_refs q <;> cases hq
    all_goals right;simp only [Heap.len,Heap.get,Objs.get,hp,left,right,old,fresh,empty,MObj.elems_dyn] <;> decide
  · intro Q s q t;exact (no_struct t).elim
private abbrev Γ : Ctx := [.val .uint,.val .uint,.mem R,.mem R,.mem R]
private def σ1 := σ0.push (t := .val .uint) (uintOfNat 1)
private def σ := σ1.push (t := .val .uint) (uintOfNat 0)
private def machine1 := writeMachine machine0 4 w[1]
private def machine := writeMachine machine1 5 w[0]
private def frag := (((Frag.init Γ0).push (.val .uint) .ok).push (.val .uint) .ok)
private theorem initial_repr : RefArrayStateRepr 1 1 8 frag σ base machine := by
  have h1 := initial_state0.consVal (uintOfNat 1) w[1] (ReprV.uint_of rfl) (by decide)
  have h2 := h1.consVal (uintOfNat 0) w[0] (ReprV.uint_of rfl) (by decide)
  exact ⟨h2,(initial_refs0.localWrite 4 (by decide) w[1]).localWrite 5 (by decide) w[0]⟩

private abbrev SB : Source.STy := .array .memory .bool none
private abbrev SR : Source.STy := SourceBoolRefsTy
private abbrev SΓ : Source.RCtx := [.int .u256,.int .u256,SR,SR,SR]
private def addresses (i : Nat) := i
private def pdata (rs : List (HRef H B)) : Source.Data E0.layout SR := sourceBoolRefMemory addresses rs
private def y0 : Source.EMState E0 [] := (.nil,s0)
private def yl : Source.EMState E0 [] := ((Source.allocRef (sourceBoolMemory [true,false,false])).run y0).2
private def yr : Source.EMState E0 [] := ((Source.allocRef (sourceBoolMemory [false,true,false])).run yl).2
private def yo : Source.EMState E0 [] := ((Source.allocRef (pdata [left])).run yr).2
private def yn : Source.EMState E0 [] := ((Source.allocRef (pdata [left,right,left])).run yo).2
private def ye : Source.EMState E0 [] := ((Source.allocRef (pdata [])).run yn).2
private def sy : Source.EMState E0 SΓ :=
  (.cons (sourceUint (uintOfNat 0)) (.cons (sourceUint (uintOfNat 1))
    (.cons (.memRef rfl 3) (.cons (.memRef rfl 2) (.cons (.memRef rfl 2) .nil)))),ye.2)
private abbrev SH : Source.HeapTy := (Source.Heap.empty (D := E0.layout)).ty
private theorem left_memOK : Source.MemOK E0 SH yl := by
  have hm : Source.MemOK E0 SH y0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have h := source_bool_alloc_memOK (E := E0) (Γ := []) SH [true,false,false] y0 hm
  have he : (Source.allocRef (E := E0) (Γ := []) (sourceBoolMemory [true,false,false])).run y0=(.ok (.memRef rfl 0),yl) := rfl
  rw [he] at h;exact h.1
private theorem right_memOK : Source.MemOK E0 SH yr := by
  have h := source_bool_alloc_memOK (E := E0) (Γ := []) SH [false,true,false] yl left_memOK
  have he : (Source.allocRef (E := E0) (Γ := []) (sourceBoolMemory [false,true,false])).run yl=(.ok (.memRef rfl 1),yr) := rfl
  rw [he] at h;exact h.1
private theorem alloc_parent_keep (y : Source.EMState E0 []) (rs : List (HRef H B))
    (hm : Source.MemOK E0 SH y) (h0 : y.2.heap.ty 0=some SB) (h1 : y.2.heap.ty 1=some SB) :
    Source.MemOK E0 SH ((Source.allocRef (pdata rs)).run y).2 := by
  have hd : Source.DataOK E0 y.2.heap.ty (pdata rs) := by
    apply Source.DataOK.array
    intro j
    apply Source.DataOK.val
    obtain ⟨_,hq|hq⟩ := prim_refs rs[j]
    · have he : rs[j]=left := eq_of_heq hq
      rw [he]
      exact ⟨SB,h0,rfl⟩
    · have he : rs[j]=right := eq_of_heq hq
      rw [he]
      exact ⟨SB,h1,rfl⟩
  have h := Source.allocRef_mem' (E := E0) (Γ := []) (H := SH) (pdata rs) (by trivial)
    (by intro j;exact ⟨.memRef rfl (addresses rs[j].id),rfl⟩) y ⟨hm,hd⟩
  have he : (Source.allocRef (E := E0) (Γ := []) (pdata rs)).run y=
      (.ok (.memRef rfl y.2.heap.next),(y.1,{y.2 with heap := (y.2.heap.alloc ⟨SR,pdata rs⟩).1})) := rfl
  rw [he] at h
  exact h.1
private theorem old_memOK : Source.MemOK E0 SH yo := alloc_parent_keep yr [left] right_memOK rfl rfl
private theorem new_memOK : Source.MemOK E0 SH yn := alloc_parent_keep yo [left,right,left] old_memOK rfl rfl
private theorem empty_memOK : Source.MemOK E0 SH ye := alloc_parent_keep yn [] new_memOK rfl rfl
private theorem source_memOK : Source.MemOK E0 SH sy := by
  refine ⟨⟨empty_memOK.1.1,?_⟩,empty_memOK.2⟩
  exact ⟨trivial,⟨trivial,⟨⟨SR,rfl,rfl⟩,⟨⟨SR,rfl,rfl⟩,⟨⟨SR,rfl,rfl⟩,trivial⟩⟩⟩⟩⟩
private theorem left_at : SourceBoolMemoryAt sy 0 hp left .dyn := by
  unfold SourceBoolMemoryAt
  simp only [Heap.get,Objs.get,hp,left,MObj.elems_dyn]
  rfl
private theorem right_at : SourceBoolMemoryAt sy 1 hp right .dyn := by
  unfold SourceBoolMemoryAt
  simp only [Heap.get,Objs.get,hp,right,MObj.elems_dyn]
  rfl
private theorem old_at : SourceBoolRefsAt sy 2 hp old addresses := by
  refine ⟨?_,?_⟩
  · simp only [Heap.get,Objs.get,hp,old,MObj.elems_dyn];rfl
  · intro q hq
    simp only [Heap.get,Objs.get,hp,old,MObj.elems_dyn,List.mem_cons,List.not_mem_nil,or_false] at hq
    subst q;exact left_at
private theorem fresh_at : SourceBoolRefsAt sy 3 hp fresh addresses := by
  refine ⟨?_,?_⟩
  · simp only [Heap.get,Objs.get,hp,fresh,MObj.elems_dyn];rfl
  · intro q hq
    simp only [Heap.get,Objs.get,hp,fresh,MObj.elems_dyn,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|hq|hq <;> subst q
    · exact left_at
    · exact right_at
    · exact left_at
private theorem empty_at : SourceBoolRefsAt sy 4 hp empty addresses := by
  refine ⟨?_,?_⟩
  · simp only [Heap.get,Objs.get,hp,empty,MObj.elems_dyn];rfl
  · intro q hq
    simp only [Heap.get,Objs.get,hp,empty,MObj.elems_dyn,List.not_mem_nil] at hq


private def ssrc : Source.Idx SΓ SR := .there (.there .here)
private def sdst : Source.Idx SΓ SR := .there (.there (.there .here))
private def backup : Source.Idx SΓ SR := .there (.there (.there (.there .here)))
private def si : Source.Idx SΓ (.int .u256) := .there .here
private def sj : Source.Idx SΓ (.int .u256) := .here
private def tsrc : Idx Γ (.mem R) := .there (.there .here)
private def tdst : Idx Γ (.mem R) := .there (.there (.there .here))
private def reached : Source.EMState E0 SΓ := (sy.1.set sdst (.memRef rfl 3),sy.2)
private def reachedState := σ.setLocal tdst (some fresh)
private def reachedMachine := writeMachine machine 2 w[36]
private def term : Source.RExpr E0 SΓ SR := sourceLocalAlias sdst ssrc
private def nested (r : Source.Idx SΓ SR) : Source.RExpr E0 SΓ .bool :=
  .indexArray (.indexArray (.local r) (.local si) rfl) (.local sj) rfl
private def cells (m : Machine) : List Word :=
  [m.mem 0,m.mem 1,m.mem 2,m.mem 3,m.mem 4,m.mem 5,m.mem 7,
   m.mem 16,m.mem 17,m.mem 18,m.mem 19,m.mem 24,m.mem 25,m.mem 26,m.mem 27,
   m.mem 32,m.mem 33,m.mem 36,m.mem 37,m.mem 38,m.mem 39,m.mem 44]
private theorem parent_one : hp.index fresh .dyn (uintOfNat 1)=some right := by
  simp only [Heap.index,Heap.get,Objs.get,hp,fresh,MObj.elems_dyn,uintOfNat]
  rfl
private theorem right_zero : hp.index right .dyn (uintOfNat 0)=some false := by
  simp only [Heap.index,Heap.get,Objs.get,hp,right,MObj.elems_dyn,uintOfNat]
  rfl
private theorem left_zero : hp.index left .dyn (uintOfNat 0)=some true := by
  simp only [Heap.index,Heap.get,Objs.get,hp,left,MObj.elems_dyn,uintOfNat]
  rfl
private theorem parent_word : hp.index fresh .dyn (indexValue ⟨1,by decide⟩)=some right := by
  simp only [Heap.index,Heap.get,Objs.get,hp,fresh,MObj.elems_dyn,indexValue,Int.toNat_natCast]
  rfl
private theorem right_word : hp.index right .dyn (indexValue ⟨0,by decide⟩)=some false := by
  simp only [Heap.index,Heap.get,Objs.get,hp,right,MObj.elems_dyn,indexValue,Int.toNat_natCast]
  rfl

/-- The independently inhabited INITIAL tables include different children and repeated aliases. -/
theorem initial_nested_views :
    Source.MemOK E0 SH sy ∧ SourceBoolRefsAt sy 2 hp old addresses ∧
    SourceBoolRefsAt sy 3 hp fresh addresses ∧ SourceBoolRefsAt sy 4 hp empty addresses ∧
    RefArrayStateRepr 1 1 8 frag σ base machine ∧
    [sy.2.heap.get 0,sy.2.heap.get 1,sy.2.heap.get 2,sy.2.heap.get 3,sy.2.heap.get 4]=
      [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,
       some ⟨SR,pdata [left]⟩,some ⟨SR,pdata [left,right,left]⟩,some ⟨SR,pdata []⟩] ∧
    [(MObj.elems .dyn (hp.get old)).map HRef.id,(MObj.elems .dyn (hp.get fresh)).map HRef.id,
      (MObj.elems .dyn (hp.get empty)).map HRef.id]=[[0],[0,1,0],[]] ∧
    [MObj.elems .dyn (hp.get left),MObj.elems .dyn (hp.get right)]=
      [[true,false,false],[false,true,false]] := by
  refine ⟨source_memOK,old_at,fresh_at,empty_at,initial_repr,rfl,?_,?_⟩
  · simp only [Heap.get,Objs.get,hp,old,fresh,empty,MObj.elems_dyn];rfl
  · simp only [Heap.get,Objs.get,hp,left,right,MObj.elems_dyn]

/-- Actual alias execution transports the INITIAL nested relation into reached reads.
The input relation is not a final graph-correctness premise. -/
theorem aligned_alias_nested (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 term).run sy=
      (.ok (.val (.memRef rfl 3)),reached) ∧
    (Source.execS (Source.SemanticsExamples.G0 p) F0 3 SΓ.length none
      (.expr term : Source.RStmt E0 [] false .body SΓ SΓ) sy.1).run (.nil,sy.2)=
      (.ok (.normal reached.1),(.nil,reached.2)) ∧
    Stmt.run σ (.rebindMem tdst (.alias (.var tsrc rfl)))=.ok ⟨reachedState,List.prefix_refl _⟩ ∧
    run (aliasLocalCode 1 tdst tsrc) machine=.ok reachedMachine 0 ∧
    SourceBoolRefsAt reached 3 reachedState.heap fresh addresses ∧ Source.MemOK E0 SH reached ∧
    RefArrayStateRepr 1 1 8 frag reachedState base reachedMachine ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (nested sdst)).run reached=
      (.ok (.val (.bool false)),reached) ∧
    (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := SB) (.mem 3 1)).run reached=
      (.ok (.memRef rfl 1),reached) ∧
    (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := .bool) (.mem 1 0)).run reached=
      (.ok (.bool false),reached) ∧
    reachedMachine.mem 38=w[24] ∧ reachedMachine.mem 25=w[0] ∧
    run (readArrayCode (base fresh.id)) (reachedMachine.push w[1])=
      .ok (reachedMachine.push w[24]) 0 ∧
    run (readArrayCode (base right.id)) (reachedMachine.push w[0])=
      .ok (reachedMachine.push w[0]) 0 ∧
    [sy.1.get sdst,sy.1.get ssrc,sy.1.get backup,reached.1.get sdst,reached.1.get ssrc,reached.1.get backup]=
      [.memRef rfl 2,.memRef rfl 3,.memRef rfl 2,.memRef rfl 3,.memRef rfl 3,.memRef rfl 2] ∧
    [cells machine,cells reachedMachine]=
      [[w[48],w[32],w[32],w[36],w[1],w[0],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[1],w[16],w[3],w[16],w[24],w[16],w[0]],
       [w[48],w[32],w[36],w[36],w[1],w[0],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[1],w[16],w[3],w[16],w[24],w[16],w[0]]] ∧
    reached.2.heap=sy.2.heap ∧ reachedState.heap=hp ∧ reachedMachine.stack=[w[42]] := by
  obtain ⟨he,hs,hi,hc,hr,hm,hd,ht,hrepr,hstack,ha⟩ :=
    SourceBoolRefsAt.alias_word (Source.SemanticsExamples.G0 p) F0 0 sy sdst ssrc 3 rfl
      SH source_memOK σ tdst tsrc fresh rfl addresses fresh_at initial_repr
  have hn := hr.eval_nested_read (Source.SemanticsExamples.G0 p) F0 0 sdst si sj
    (uintOfNat 1) (uintOfNat 0) right false hd rfl rfl parent_one right_zero
  obtain ⟨hpread,hcread,hpcell,hccell,hprun,hcrun⟩ :=
    hr.word_observe hrepr F0 ⟨1,by decide⟩ ⟨0,by decide⟩ right false parent_word right_word
  exact ⟨he,hs,hi,hc,hr,hm,hrepr,hn,hpread,hcread,hpcell,hccell,hprun,hcrun,rfl,rfl,rfl,rfl,hstack⟩

/-- Repeated identities select the same child; the materially different child
forces local address separation without a global injectivity assumption. -/
theorem shared_and_wrong_child :
    (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := SB) (.mem 3 0)).run reached=(.ok (.memRef rfl 0),reached) ∧
    (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := SB) (.mem 3 2)).run reached=(.ok (.memRef rfl 0),reached) ∧
    (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := .bool) (.mem 0 0)).run reached=(.ok (.bool true),reached) ∧
    addresses left.id≠addresses right.id ∧
    reachedMachine.mem 37=reachedMachine.mem 39 ∧ reachedMachine.mem 17≠reachedMachine.mem 25 ∧
    hp.index left .dyn (uintOfNat 0)≠hp.index right .dyn (uintOfNat 0) := by
  have hr : SourceBoolRefsAt reached 3 hp fresh addresses := fresh_at.same_heaps rfl rfl
  refine ⟨hr.parent_read F0 0 left (by simp only [Heap.get,Objs.get,hp,fresh,MObj.elems_dyn];rfl),hr.parent_read F0 2 left (by simp only [Heap.get,Objs.get,hp,fresh,MObj.elems_dyn];rfl),
    (hr.child_read_iff F0 0 left (by simp only [Heap.get,Objs.get,hp,fresh,MObj.elems_dyn];rfl) (uintOfNat 0) true).mpr left_zero,?_,rfl,?_,?_⟩
  · exact hr.child_address_ne F0 0 1 left right (by simp only [Heap.get,Objs.get,hp,fresh,MObj.elems_dyn];rfl) (by simp only [Heap.get,Objs.get,hp,fresh,MObj.elems_dyn];rfl) (uintOfNat 0) true false left_zero right_zero (by decide)
  · change w[1]≠w[0];decide
  · rw [left_zero,right_zero];decide

/-- Empty and exact endpoints retain actual Source panic, intrinsic None and
word revert observations, without claiming an encoded returndata equivalence. -/
theorem endpoint_views :
    (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := SB) (.mem 3 3)).run reached=
      (.error (.revert (Source.panicData .index)),reached) ∧
    run (readArrayCode (base fresh.id)) (reachedMachine.push w[3])=.revert ∧
    (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := .bool) (.mem 1 3)).run reached=
      (.error (.revert (Source.panicData .index)),reached) ∧
    run (readArrayCode (base right.id)) (reachedMachine.push w[3])=.revert ∧
    (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := SB) (.mem 4 0)).run reached=
      (.error (.revert (Source.panicData .index)),reached) ∧
    run (readArrayCode (base empty.id)) (reachedMachine.push w[0])=.revert := by
  have ha := aligned_alias_nested Roadmap.Pipeline.legacy
  have hr := ha.2.2.2.2.1
  have hm := ha.2.2.2.2.2.2.1
  obtain ⟨hparent,_,hc⟩ := hr.word_parent_bounds hm F0 ⟨3,by decide⟩ (by
    simp only [reachedState,State.setLocal,σ,σ1,σ0,Heap.len,Heap.get,hp,fresh,MObj.elems_dyn];decide)
  obtain ⟨_,hch,_,hcc⟩ := hr.word_child_bounds hm F0 ⟨1,by decide⟩ ⟨3,by decide⟩ right parent_word (by
    simp only [reachedState,State.setLocal,σ,σ1,σ0,Heap.len,Heap.get,hp,right,MObj.elems_dyn];decide)
  have hem : SourceBoolRefsAt reached 4 reachedState.heap empty addresses := empty_at.same_heaps rfl rfl
  obtain ⟨hep,_,hec⟩ := hem.word_parent_bounds hm F0 ⟨0,by decide⟩ (by
    simp only [reachedState,State.setLocal,σ,σ1,σ0,Heap.len,Heap.get,hp,empty,MObj.elems_dyn];decide)
  exact ⟨hparent,hc,hch,hcc,hep,hec⟩

/-- Stale binding fails at the old parent before a child read; actual rebinding
selects the different child. Both declared pipelines are covered parametrically. -/
theorem stale_binding (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (nested backup)).run reached=
      (.error (.revert (Source.panicData .index)),reached) ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (nested sdst)).run reached=
      (.ok (.val (.bool false)),reached) := by
  have ho : SourceBoolRefsAt reached 2 hp old addresses := old_at.same_heaps rfl rfl
  refine ⟨ho.eval_nested_parent_bounds (Source.SemanticsExamples.G0 p) F0 0 backup si sj
    (uintOfNat 1) rfl rfl ?_,(aligned_alias_nested p).2.2.2.2.2.2.2.1⟩
  simp only [Heap.len,Heap.get,Objs.get,hp,old,MObj.elems_dyn,uintOfNat];decide


private def childEndpoint : Source.EMState E0 SΓ := (reached.1.set sj (sourceUint (uintOfNat 3)),reached.2)
/-- The real nested syntax reaches a valid parent selection, then rejects the
child endpoint; the bound is not tested only at helper level. -/
theorem nested_child_endpoint (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (nested sdst)).run childEndpoint=
      (.error (.revert (Source.panicData .index)),childEndpoint) := by
  have hr : SourceBoolRefsAt childEndpoint 3 hp fresh addresses := fresh_at.same_heaps rfl rfl
  apply hr.eval_nested_child_bounds (Source.SemanticsExamples.G0 p) F0 0 sdst si sj
    (uintOfNat 1) (uintOfNat 3) right rfl rfl rfl parent_one
  simp only [Heap.len,Heap.get,Objs.get,hp,right,MObj.elems_dyn,uintOfNat];decide

/-- Self-aliasing executes with the same initial/reached nested correspondence;
there is no distinct-root side condition. -/
theorem self_alias_nested (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (sourceLocalAlias ssrc ssrc)).run sy=
      (.ok (.val (.memRef rfl 3)),sy) ∧
    run (aliasLocalCode 1 tsrc tsrc) machine=.ok machine 0 ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (nested ssrc)).run sy=
      (.ok (.val (.bool false)),sy) := by
  obtain ⟨he,_,_,hc,hr,_,_,_,_,_,_⟩ :=
    SourceBoolRefsAt.alias_word (Source.SemanticsExamples.G0 p) F0 0 sy ssrc ssrc 3 rfl
      SH source_memOK σ tsrc tsrc fresh rfl addresses fresh_at initial_repr
  have hs : sy.1.set ssrc (.memRef rfl 3)=sy.1 := rfl
  have hm : writeMachine machine (cellOf 1 tsrc) (.val (base fresh.id))=machine := by
    have hmem : upd machine.mem 3 w[36]=machine.mem := by
      funext a
      by_cases ha : a=3
      · subst a;rw [upd_same];rfl
      · rw [upd_other _ _ ha]
    exact congrArg (fun mem => {machine with mem := mem}) hmem
  rw [hs] at he
  rw [hm] at hc
  exact ⟨he,hc,fresh_at.eval_nested_read (Source.SemanticsExamples.G0 p) F0 0 ssrc si sj
    (uintOfNat 1) (uintOfNat 0) right false rfl rfl rfl parent_one right_zero⟩

private def runtimeHeap (rs : List (HRef H B)) (hlen : rs.length<2^256) : Heap H :=
  (⟨[true,false,false],by decide⟩,(⟨[false,true,false],by decide⟩,
    (⟨[left],by decide⟩,(⟨rs,hlen⟩,(⟨[],by decide⟩,())))))
private def runtimeSource (rs : List (HRef H B)) : Source.EMState E0 SΓ :=
  (sy.1,((Source.allocRef (pdata rs)).run yo).2.2)
/-- Actual Source construction inhabits the INITIAL observer for arbitrary
runtime lists, including empty and repeated child selections. Only the existing
intrinsic array validity bound is needed; no fixture or copy-count cutoff. -/
theorem runtime_initial_nested (rs : List (HRef H B)) (hlen : rs.length<2^256) :
    Source.MemOK E0 SH (runtimeSource rs) ∧
    SourceBoolRefsAt (runtimeSource rs) 3 (runtimeHeap rs hlen) fresh addresses ∧
    (MObj.elems .dyn ((runtimeHeap rs hlen).get fresh)).map HRef.id=rs.map HRef.id := by
  have hm := alloc_parent_keep yo rs old_memOK rfl rfl
  refine ⟨?_,⟨?_,?_⟩,?_⟩
  · refine ⟨⟨hm.1.1,?_⟩,hm.2⟩
    exact ⟨trivial,⟨trivial,⟨⟨SR,rfl,rfl⟩,⟨⟨SR,rfl,rfl⟩,⟨⟨SR,rfl,rfl⟩,trivial⟩⟩⟩⟩⟩
  · simp only [Heap.get,Objs.get,runtimeHeap,fresh,MObj.elems_dyn];rfl
  · intro q hq
    obtain ⟨_,he|he⟩ := prim_refs q
    · have h : q=left := eq_of_heq he
      subst q
      unfold SourceBoolMemoryAt
      simp only [Heap.get,Objs.get,runtimeHeap,left,MObj.elems_dyn];rfl
    · have h : q=right := eq_of_heq he
      subst q
      unfold SourceBoolMemoryAt
      simp only [Heap.get,Objs.get,runtimeHeap,right,MObj.elems_dyn];rfl
  · simp only [Heap.get,Objs.get,runtimeHeap,fresh,MObj.elems_dyn]

/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.nested_child_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms nested_child_endpoint
/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.self_alias_nested' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms self_alias_nested
/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.runtime_initial_nested' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms runtime_initial_nested

/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.initial_nested_views' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms initial_nested_views
/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.aligned_alias_nested' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms aligned_alias_nested
/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.shared_and_wrong_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shared_and_wrong_child
/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.endpoint_views' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms endpoint_views
/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.stale_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms stale_binding


private abbrev SelectSΓ : Source.RCtx := SB::SΓ
private def selectSource : Source.EMState E0 SelectSΓ := (.cons (.memRef rfl 0) sy.1,sy.2)
private def selectState := σ.push (t := .mem B) (some left)
private def selectMachine := writeMachine machine 6 w[16]
private def selectFrag := frag.push (.mem B) .ok
private def selectSrcRoot : Source.Idx SelectSΓ SR := .there ssrc
private def selectSrcIndex : Source.Idx SelectSΓ (.int .u256) := .there si
private def selectRoot : Idx (.mem B::Γ) (.mem R) := .there tsrc
private def selectIndex : Idx (.mem B::Γ) (.val .uint) := .there (.there .here)
private def selectedSource : Source.EMState E0 SelectSΓ := (selectSource.1.set .here (.memRef rfl 1),selectSource.2)
private def selectedState := selectState.setLocal (.here : Idx (.mem B::Γ) (.mem B)) (some right)
private def selectedMachine := writeMachine selectMachine 6 w[24]
private def selectedTerm : Source.RExpr E0 SelectSΓ SB := sourceSelectedAlias .here selectSrcRoot selectSrcIndex
private def selectedCode : List Instr := selectedAliasCode (C := C) 1 .here selectRoot selectIndex
private theorem select_memOK : Source.MemOK E0 SH selectSource :=
  ⟨⟨source_memOK.1.1,⟨⟨SB,rfl,rfl⟩,source_memOK.1.2⟩⟩,source_memOK.2⟩
private theorem select_at : SourceBoolRefsAt selectSource 3 selectState.heap fresh addresses := fresh_at.same_heaps rfl rfl
private theorem select_repr : RefArrayStateRepr 1 1 8 selectFrag selectState base selectMachine :=
  ⟨initial_repr.state.consMem left (by decide),initial_repr.arrays.localWrite 6 (by decide) w[16]⟩

/-- Actual indexed reference selection, not just a parent-local pointer alias:
the Source RHS and published typed word path choose the SAME different child. -/
theorem selected_child_rebind (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 selectedTerm).run selectSource=
      (.ok (.val (.memRef rfl 1)),selectedSource) ∧
    (Source.execS (Source.SemanticsExamples.G0 p) F0 4 SelectSΓ.length none
      (.expr selectedTerm : Source.RStmt E0 [] false .body SelectSΓ SelectSΓ) selectSource.1).run (.nil,selectSource.2)=
      (.ok (.normal selectedSource.1),(.nil,selectedSource.2)) ∧
    Stmt.run selectState (.rebindMem .here (.alias (.loc (.index .dyn (.var selectRoot rfl) (.simple (.local selectIndex))))))=
      .ok ⟨selectedState,List.prefix_refl _⟩ ∧ run selectedCode selectMachine=.ok selectedMachine 0 ∧
    Source.MemOK E0 SH selectedSource ∧ SourceBoolMemoryAt selectedSource 1 selectedState.heap right .dyn ∧
    SourceBoolRefsAt selectedSource 3 selectedState.heap fresh addresses ∧
    RefArrayStateRepr 1 1 8 selectFrag selectedState base selectedMachine ∧
    [selectSource.1.get .here,selectedSource.1.get .here]=[.memRef rfl 0,.memRef rfl 1] ∧
    [(TEnv.get .here selectState.env).map HRef.id,(TEnv.get .here selectedState.env).map HRef.id]=[some 0,some 1] ∧
    (Source.readLoc (E := E0) (Γ := SelectSΓ) F0 (τ := .bool) (.mem 1 0)).run selectedSource=
      (.ok (.bool false),selectedSource) ∧
    (Source.readLoc (E := E0) (Γ := SelectSΓ) F0 (τ := .bool) (.mem 0 0)).run selectedSource=
      (.ok (.bool true),selectedSource) ∧
    cells selectedMachine=cells machine ∧
    [selectMachine.mem 6,selectedMachine.mem 6,selectedMachine.mem 38,selectedMachine.mem 25,selectedMachine.mem 17]=
      [w[16],w[24],w[24],w[0],w[1]] ∧ selectedMachine.stack=[w[42]] ∧
    selectedSource.2.heap=selectSource.2.heap ∧ selectedState.heap=hp := by
  obtain ⟨he,hs,hi,hc,hm,hchild,hr,hd,ht,hrepr,hstack,ha⟩ :=
    SourceBoolRefsAt.selected_alias_word (Source.SemanticsExamples.G0 p) F0 0 selectSource .here selectSrcRoot selectSrcIndex
      3 (uintOfNat 1) rfl rfl SH select_memOK selectState .here selectRoot selectIndex fresh right rfl rfl
      addresses select_at parent_one select_repr rfl
  have hold : SourceBoolMemoryAt selectedSource 0 selectedState.heap left .dyn := by
    unfold SourceBoolMemoryAt
    simp only [selectedState,selectState,State.setLocal,State.push,σ,σ1,σ0,Heap.get,Objs.get,hp,left,MObj.elems_dyn];rfl
  exact ⟨he,hs,hi,hc,hm,hchild,hr,hrepr,rfl,rfl,
    (hchild.read_iff F0 (uintOfNat 0) false).mpr right_zero,
    (hold.read_iff F0 (uintOfNat 0) true).mpr left_zero,rfl,rfl,hstack,rfl,rfl⟩

private def failedSelectSource : Source.EMState E0 SelectSΓ :=
  (selectSource.1.set selectSrcIndex (sourceUint (uintOfNat 3)),selectSource.2)
private def failedSelectState := selectState.setLocal selectIndex (uintOfNat 3)
private def failedSelectMachine := writeMachine selectMachine 4 w[3]
private theorem failed_select_repr : RefArrayStateRepr 1 1 8 selectFrag failedSelectState base failedSelectMachine :=
  ⟨select_repr.state.setVal selectIndex (uintOfNat 3) w[3] (ReprV.uint_of rfl),
    select_repr.arrays.localWrite 4 (by decide) w[3]⟩
/-- Endpoint RHS failure leaves the actual initial local selection unchanged;
Source panic, intrinsic revert and word revert are separate observations. -/
theorem selected_child_bounds (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 selectedTerm).run failedSelectSource=
      (.error (.revert (Source.panicData .index)),failedSelectSource) ∧
    Stmt.run failedSelectState (.rebindMem .here (.alias (.loc (.index .dyn (.var selectRoot rfl) (.simple (.local selectIndex))))))=
      .error .revert ∧ run selectedCode failedSelectMachine=.revert ∧
    failedSelectSource.1.get .here=.memRef rfl 0 ∧ failedSelectMachine.mem 6=w[16] := by
  have hr : SourceBoolRefsAt failedSelectSource 3 failedSelectState.heap fresh addresses := fresh_at.same_heaps rfl rfl
  have h := SourceBoolRefsAt.selected_alias_word_bounds (Source.SemanticsExamples.G0 p) F0 0 failedSelectSource .here selectSrcRoot selectSrcIndex
    3 (uintOfNat 3) rfl rfl failedSelectState .here selectRoot selectIndex fresh rfl rfl addresses hr
    (by simp only [failedSelectState,selectState,State.setLocal,State.push,σ,σ1,σ0,Heap.len,Heap.get,Objs.get,hp,fresh,MObj.elems_dyn,uintOfNat];decide)
    failed_select_repr rfl
  exact ⟨h.1,h.2.1,h.2.2,rfl,rfl⟩


/-- Both pipelines reject insufficient horizons before the selected alias can
change its old child pointer. This tests the general bound on the actual fixture. -/
theorem selected_child_low_horizon (p : Roadmap.Pipeline) :
    ∀ n, n≤2 → (Source.evalE (Source.SemanticsExamples.G0 p) F0 n selectedTerm).run selectSource=
      (.error .timeout,selectSource) :=
  source_selected_alias_low_horizon (Source.SemanticsExamples.G0 p) F0 selectSource .here selectSrcRoot selectSrcIndex

/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.selected_child_low_horizon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms selected_child_low_horizon

/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.selected_child_rebind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms selected_child_rebind
/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.selected_child_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms selected_child_bounds


private def mutatedHeap := hp.set left (MObj.setElem .dyn (hp.get left) 0 false)
private def mutatedSource : Source.EMState E0 SΓ :=
  (sy.1,{sy.2 with heap := sy.2.heap.write 0 (sourceBoolMemory [false,false,false]) (by rfl)})
private def mutatedMachine := writeMachine machine 17 w[0]
private theorem mutated_index : mutatedHeap.index left .dyn (uintOfNat 0)=some false := by
  simp only [mutatedHeap,Heap.index,Heap.get_set_same,MObj.elems_setElem]
  simp only [Heap.get,Objs.get,hp,left,MObj.elems_dyn,uintOfNat];rfl
private theorem mutation_source_run :
    (Source.writeLoc (E := E0) (Γ := SΓ) F0 0 (.mem 0 0) (.bool false)).run sy=(.ok (),mutatedSource) := by
  have hh : sy.2.heap.get 0=some ⟨SB,sourceBoolMemory [true,false,false]⟩ := by
    simpa only [SourceBoolMemoryAt,Heap.get,Objs.get,hp,left,MObj.elems_dyn] using left_at
  obtain ⟨_,hw⟩ := source_bool_write sy 0 [true,false,false] hh 0 (by decide) false
  exact hw
private theorem mutation_heap_run : hp.writeAddr (.index left .dyn (indexValue ⟨0,by decide⟩)) false=some mutatedHeap := by
  simp only [Heap.writeAddr,Heap.setIndex,indexValue,Int.toNat_natCast]
  exact if_pos (by simp only [Heap.get,Objs.get,hp,left,MObj.elems_dyn];decide)

/-- Mutating the shared selected child changes BOTH repeated observations;
the independent other child and parent identities/fields remain intact. -/
theorem shared_child_mutation :
    hp.writeAddr (.index left .dyn (indexValue ⟨0,by decide⟩)) false=some mutatedHeap ∧
    (Source.writeLoc (E := E0) (Γ := SΓ) F0 0 (.mem 0 0) (.bool false)).run sy=(.ok (),mutatedSource) ∧
    run (writeArrayCode (base left.id)) ((machine.push w[0]).push w[0])=.ok mutatedMachine 0 ∧
    SourceBoolRefsAt mutatedSource 3 mutatedHeap fresh addresses ∧ Source.MemOK E0 SH mutatedSource ∧
    RefArrayStateRepr 1 1 8 frag (σ.withHeap mutatedHeap) base mutatedMachine ∧
    (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := SB) (.mem 3 0)).run mutatedSource=(.ok (.memRef rfl 0),mutatedSource) ∧
    (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := SB) (.mem 3 2)).run mutatedSource=(.ok (.memRef rfl 0),mutatedSource) ∧
    (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := .bool) (.mem 0 0)).run mutatedSource=(.ok (.bool false),mutatedSource) ∧
    (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := .bool) (.mem 1 1)).run mutatedSource=(.ok (.bool true),mutatedSource) ∧
    [(MObj.elems .dyn (mutatedHeap.get fresh)).map HRef.id]=[[0,1,0]] ∧
    [MObj.elems .dyn (mutatedHeap.get left),MObj.elems .dyn (mutatedHeap.get right)]=
      [[false,false,false],[false,true,false]] ∧
    cells mutatedMachine=[w[48],w[32],w[32],w[36],w[1],w[0],w[99],w[3],w[0],w[0],w[0],w[3],w[0],w[1],w[0],w[1],w[16],w[3],w[16],w[24],w[16],w[0]] ∧
    mutatedSource.1=sy.1 ∧ mutatedMachine.stack=[w[42]] := by
  obtain ⟨out,z,ho,hs,hc,hr,hm,hrepr,hl,hparent⟩ :=
    SourceBoolRefsAt.write_child_word σ fresh addresses fresh_at left
      (by change left∈MObj.elems .dyn (hp.get fresh);simp only [Heap.get,Objs.get,hp,fresh,MObj.elems_dyn,List.mem_cons];exact Or.inl trivial)
      (by intro t ht hne;exact hne) F0 0 ⟨0,by decide⟩ false
      (by simp only [σ,σ1,σ0,Heap.len,Heap.get,hp,left,MObj.elems_dyn];decide) SH source_memOK initial_repr
  have hout : out=mutatedHeap := Option.some.inj (ho.symm.trans mutation_heap_run)
  have hz : z=mutatedSource := congrArg Prod.snd (hs.symm.trans mutation_source_run)
  subst out;subst z
  have hright : SourceBoolMemoryAt mutatedSource 1 mutatedHeap right .dyn := hr.children right (by
    rw [hparent]
    change right∈MObj.elems .dyn (hp.get fresh)
    simp only [Heap.get,Objs.get,hp,fresh,MObj.elems_dyn,List.mem_cons];exact Or.inr (Or.inl trivial))
  refine ⟨ho,hs,hc,hr,hm,hrepr,hr.parent_read F0 0 left ?_,hr.parent_read F0 2 left ?_,
    (hr.child_read_iff F0 0 left ?_ (uintOfNat 0) false).mpr mutated_index,
    (hright.read_iff F0 (uintOfNat 1) true).mpr ?_,?_,?_,rfl,hl,rfl⟩
  all_goals simp only [mutatedHeap,Heap.index,Heap.get_set_ne hp left fresh (by decide),Heap.get_set_ne hp left right (by decide),Heap.get_set_same,MObj.elems_setElem]
  all_goals simp only [Heap.get,Objs.get,hp,left,right,fresh,MObj.elems_dyn,uintOfNat]
  all_goals rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.shared_child_mutation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shared_child_mutation


private def collapsedAddresses (_ : Nat) := 0
private def collapsedHeap : Heap H := (⟨[true,false,false],by decide⟩,(⟨[true,false,false],by decide⟩,
  (⟨[left],by decide⟩,(⟨[left,right,left],by decide⟩,(⟨[],by decide⟩,())))))
private def collapsedData : Source.Data E0.layout SR := sourceBoolRefMemory collapsedAddresses [left,right,left]
private def collapsedSource : Source.EMState E0 [] := ((Source.allocRef collapsedData).run yl).2
private def collapsedOut := collapsedHeap.set left (MObj.setElem .dyn (collapsedHeap.get left) 0 false)
private def collapsedPost : Source.EMState E0 [] :=
  (collapsedSource.1,{collapsedSource.2 with heap := collapsedSource.2.heap.write 0 (sourceBoolMemory [false,false,false]) (by rfl)})
private theorem collapsed_memOK : Source.MemOK E0 SH collapsedSource := by
  have hd : Source.DataOK E0 yl.2.heap.ty collapsedData := by
    apply Source.DataOK.array
    intro i
    apply Source.DataOK.val
    exact ⟨SB,rfl,rfl⟩
  have h := Source.allocRef_mem' (E := E0) (Γ := []) (H := SH) collapsedData (by trivial)
    (by intro i;exact ⟨.memRef rfl 0,rfl⟩) yl ⟨left_memOK,hd⟩
  have he : (Source.allocRef (E := E0) (Γ := []) collapsedData).run yl=
    (.ok (.memRef rfl 1),collapsedSource) := rfl
  rw [he] at h
  exact h.1
private theorem collapsed_at : SourceBoolRefsAt collapsedSource 1 collapsedHeap fresh collapsedAddresses := by
  refine ⟨?_,?_⟩
  · simp only [Heap.get,Objs.get,collapsedHeap,fresh,MObj.elems_dyn];rfl
  · intro t ht
    simp only [Heap.get,Objs.get,collapsedHeap,fresh,MObj.elems_dyn,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with ht|ht|ht <;> subst t
    all_goals unfold SourceBoolMemoryAt
    all_goals simp only [Heap.get,Objs.get,collapsedHeap,left,right,MObj.elems_dyn]
    all_goals rfl
private theorem collapsed_write :
    (Source.writeLoc (E := E0) (Γ := []) F0 0 (.mem 0 0) (.bool false)).run collapsedSource=(.ok (),collapsedPost) := by
  have hh : collapsedSource.2.heap.get 0=some ⟨SB,sourceBoolMemory [true,false,false]⟩ := rfl
  obtain ⟨_,hw⟩ := source_bool_write collapsedSource 0 [true,false,false] hh 0 (by decide) false
  exact hw
private theorem collapsed_target_write :
    collapsedHeap.writeAddr (.index left .dyn (indexValue ⟨0,by decide⟩)) false=some collapsedOut := by
  simp only [Heap.writeAddr,Heap.setIndex,indexValue,Int.toNat_natCast]
  exact if_pos (by simp only [Heap.get,Objs.get,collapsedHeap,left,MObj.elems_dyn];decide)

/-- Read agreement plus Source MemOK does not imply mutation framing: two
DISTINCT typed children may initially denote equal values at the SAME Source
address. A material write changes both Source aliases but only one intrinsic
object. This is a counterexample, not a new source-profile exclusion. -/
theorem collapsed_alias_mutation_counterexample :
    SourceBoolRefsAt collapsedSource 1 collapsedHeap fresh collapsedAddresses ∧
    Source.MemOK E0 SH collapsedSource ∧ left.id≠right.id ∧ collapsedAddresses left.id=collapsedAddresses right.id ∧
    collapsedHeap.writeAddr (.index left .dyn (indexValue ⟨0,by decide⟩)) false=some collapsedOut ∧
    (Source.writeLoc (E := E0) (Γ := []) F0 0 (.mem 0 0) (.bool false)).run collapsedSource=(.ok (),collapsedPost) ∧
    Source.MemOK E0 SH collapsedPost ∧
    ¬SourceBoolRefsAt collapsedPost 1 collapsedOut fresh collapsedAddresses ∧
    [MObj.elems .dyn (collapsedOut.get left),MObj.elems .dyn (collapsedOut.get right)]=
      [[false,false,false],[true,false,false]] ∧
    [(MObj.elems .dyn (collapsedOut.get fresh)).map HRef.id]=[[0,1,0]] ∧
    (Source.readLoc (E := E0) (Γ := []) F0 (τ := .bool) (.mem 0 0)).run collapsedPost=
      (.ok (.bool false),collapsedPost) := by
  have hnew : collapsedPost.2.heap.get 0=some ⟨SB,sourceBoolMemory [false,false,false]⟩ :=
    Source.Heap.write_get collapsedSource.2.heap 0 (sourceBoolMemory [false,false,false]) (by rfl)
  have hread := source_bool_read collapsedPost 0 [false,false,false] hnew 0 (by decide)
  have hmk := Source.writeLoc_memOK (E := E0) (Γ := []) (H := SH) F0 0
    (.mem (τ := .bool) 0 0) (.bool false) collapsedSource ⟨collapsed_memOK,trivial⟩
  rw [collapsed_write] at hmk
  refine ⟨collapsed_at,collapsed_memOK,by decide,rfl,collapsed_target_write,collapsed_write,hmk,?_,?_,?_,hread⟩
  · intro hfinal
    have hsel : (MObj.elems .dyn (collapsedOut.get fresh))[1]?=some right := by
      simp only [collapsedOut,Heap.get_set_ne collapsedHeap left fresh (by decide)]
      simp only [Heap.get,Objs.get,collapsedHeap,fresh,MObj.elems_dyn];rfl
    have hright : collapsedOut.index right .dyn (uintOfNat 0)=some true := by
      simp only [collapsedOut,Heap.index,Heap.get_set_ne collapsedHeap left right (by decide)]
      simp only [Heap.get,Objs.get,collapsedHeap,right,MObj.elems_dyn,uintOfNat];rfl
    have hbad := (hfinal.child_read_iff F0 1 right hsel (uintOfNat 0) true).mpr hright
    have he := congrArg Prod.fst (hbad.symm.trans hread)
    cases he
  · simp only [collapsedOut,Heap.get_set_same,Heap.get_set_ne collapsedHeap left right (by decide),MObj.elems_setElem]
    simp only [Heap.get,Objs.get,collapsedHeap,left,right,MObj.elems_dyn];rfl
  · simp only [collapsedOut,Heap.get_set_ne collapsedHeap left fresh (by decide)]
    simp only [Heap.get,Objs.get,collapsedHeap,fresh,MObj.elems_dyn];rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.collapsed_alias_mutation_counterexample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms collapsed_alias_mutation_counterexample


/-- Arbitrary runtime parent lists and repetitions containing the selected leaf
instantiate the actual mutation theorem, not just a fixed three-element frame.
The empty/no-selected-leaf case is outside this selected-member theorem only. -/
theorem runtime_shared_mutation (rs : List (HRef H B)) (hlen : rs.length<2^256) (hq : left∈rs) :
    ∃ (out : Heap H) (z : Source.EMState E0 SΓ),
      (runtimeHeap rs hlen).writeAddr (.index left .dyn (uintOfNat 0)) false=some out ∧
      (Source.writeLoc (E := E0) (Γ := SΓ) F0 0 (.mem 0 0) (.bool false)).run (runtimeSource rs)=(.ok (),z) ∧
      SourceBoolRefsAt z 3 out fresh addresses ∧ Source.MemOK E0 SH z ∧
      z.1=(runtimeSource rs).1 ∧ out.get fresh=(runtimeHeap rs hlen).get fresh := by
  obtain ⟨hm,hr,_⟩ := runtime_initial_nested rs hlen
  exact hr.write_child left (by
    simpa only [Heap.get,Objs.get,runtimeHeap,fresh,MObj.elems_dyn] using hq)
    (by intro t ht hne;exact hne) F0 0 (uintOfNat 0) false
    (by simp only [Heap.len,Heap.get,Objs.get,runtimeHeap,left,MObj.elems_dyn,uintOfNat];decide) SH hm

/-- The actual bad write returns no successful heap; no target rollback state
or Source halt equivalence is inferred from these separate observations. -/
theorem shared_mutation_bounds :
    (Source.writeLoc (E := E0) (Γ := SΓ) F0 0 (.mem 0 3) (.bool false)).run sy=
      (.error (.revert (Source.panicData .index)),sy) ∧
    hp.writeAddr (.index left .dyn (indexValue ⟨3,by decide⟩)) false=none ∧
    run (writeArrayCode (base left.id)) ((machine.push w[0]).push w[3])=.revert := by
  have hh : sy.2.heap.get 0=some ⟨SB,sourceBoolMemory [true,false,false]⟩ := by
    simpa only [SourceBoolMemoryAt,Heap.get,Objs.get,hp,left,MObj.elems_dyn] using left_at
  have hs := source_bool_write_bounds sy 0 [true,false,false] hh 3 (by decide) false
  have hn : hp.writeAddr (.index left .dyn (indexValue ⟨3,by decide⟩)) false=none := by
    simp only [Heap.writeAddr,Heap.setIndex,indexValue,Int.toNat_natCast]
    exact if_neg (by simp only [Heap.get,Objs.get,hp,left,MObj.elems_dyn];decide)
  rcases writeArray_correct (initial_repr.state.heap.arrays left) ⟨3,by decide⟩ false w[0] rfl with ⟨out,hw,_,_⟩|⟨_,hc⟩
  · have hw' : hp.writeAddr (.index left .dyn (indexValue ⟨3,by decide⟩)) false=some out := hw
    rw [hn] at hw';cases hw'
  · exact ⟨hs,hn,hc⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.runtime_shared_mutation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms runtime_shared_mutation
/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.shared_mutation_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms shared_mutation_bounds


private abbrev NΓ : Ctx := .val .bool::Γ
private abbrev NSΓ : Source.RCtx := .bool::SΓ
private def ns : State C NΓ := σ.push (t := .val .bool) true
private def ny : Source.EMState E0 NSΓ := (.cons (.bool true) sy.1,sy.2)
private def nm := writeMachine machine 6 w[1]
private def nf := frag.push (.val .bool) .ok
private def nroot : Idx NΓ (.mem R) := .there tsrc
private def ni : Idx NΓ (.val .uint) := .there .here
private def nj : Idx NΓ (.val .uint) := .there (.there .here)
private def nsroot : Source.Idx NSΓ SR := .there ssrc
private def nsi : Source.Idx NSΓ (.int .u256) := .there sj
private def nsj : Source.Idx NSΓ (.int .u256) := .there si
private def nterm : Source.RExpr E0 NSΓ .bool := sourceNestedAssign nsroot nsi nsj .here
private def ncode : List Instr := nestedWriteCode (C := C) 1 nroot ni nj .here
private def nprog : Stmt C NΓ NΓ := .assignMem (.index .dyn (.loc (.index .dyn (.var nroot rfl) (.simple (.local ni)))) (.simple (.local nj))) (.val (.simple (.local .here)))
private def nh := hp.set left (MObj.setElem .dyn (hp.get left) 1 true)
private def nz : Source.EMState E0 NSΓ := (ny.1,{ny.2 with heap := ny.2.heap.write 0 (sourceBoolMemory [true,true,false]) (by rfl)})
private def nt := writeMachine nm 18 w[1]
private theorem nmem : Source.MemOK E0 SH ny := ⟨⟨source_memOK.1.1,⟨trivial,source_memOK.1.2⟩⟩,source_memOK.2⟩
private theorem nrepr : RefArrayStateRepr 1 1 8 nf ns base nm :=
  ⟨initial_repr.state.consVal (p := .bool) true w[1] rfl (by decide),initial_repr.arrays.localWrite 6 (by decide) w[1]⟩
private theorem nat_initial : SourceBoolRefsAt ny 3 ns.heap fresh addresses := fresh_at.same_heaps rfl rfl
private theorem nparent : ns.heap.index fresh .dyn (indexValue ⟨0,by decide⟩)=some left := by
  change hp.index fresh .dyn (indexValue ⟨0,by decide⟩)=some left
  simp only [Heap.index,indexValue,Int.toNat_natCast,Heap.get,Objs.get,hp,fresh,MObj.elems_dyn];rfl
private theorem nheaprun : ns.heap.writeAddr (.index left .dyn (indexValue ⟨1,by decide⟩)) true=some nh := by
  change hp.writeAddr (.index left .dyn (indexValue ⟨1,by decide⟩)) true=some nh
  simp only [Heap.writeAddr,Heap.setIndex,indexValue,Int.toNat_natCast]
  exact if_pos (by simp only [Heap.get,Objs.get,hp,left,MObj.elems_dyn];decide)
private theorem nsourcerun : (Source.writeLoc (E := E0) (Γ := NSΓ) F0 3 (.mem 0 1) (.bool true)).run ny=(.ok (),nz) := by
  have hh : ny.2.heap.get 0=some ⟨SB,sourceBoolMemory [true,false,false]⟩ := rfl
  obtain ⟨_,hw⟩ := source_bool_write ny 0 [true,false,false] hh 1 (by decide) true
  exact hw

/-- Actual RHS-first nested syntax and whole path-to-write code materially
change the shared child, while all repeated IDs and other objects stay framed. -/
theorem nested_assignment_views (p : Roadmap.Pipeline) :
    (Source.evalLoc (Source.SemanticsExamples.G0 p) F0 3 (sourceNestedLoc nsroot nsi nsj)).run ny=(.ok (.mem 0 1),ny) ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 4 nterm).run ny=(.ok (.val (.bool true)),nz) ∧
    (Source.execS (Source.SemanticsExamples.G0 p) F0 5 NSΓ.length none
      (.expr nterm : Source.RStmt E0 [] false .body NSΓ NSΓ) ny.1).run (.nil,ny.2)=(.ok (.normal nz.1),(.nil,nz.2)) ∧
    Stmt.run ns nprog=.ok ⟨ns.withHeap nh,List.prefix_refl _⟩ ∧
    run ncode nm=.ok nt 0 ∧ SourceBoolRefsAt nz 3 nh fresh addresses ∧ Source.MemOK E0 SH nz ∧
    RefArrayStateRepr 1 1 8 nf (ns.withHeap nh) base nt ∧ nz.1=ny.1 ∧
    [MObj.elems .dyn (nh.get left),MObj.elems .dyn (nh.get right)]=[[true,true,false],[false,true,false]] ∧
    [(MObj.elems .dyn (nh.get old)).map HRef.id,(MObj.elems .dyn (nh.get fresh)).map HRef.id]=[[0],[0,1,0]] ∧
    (Source.readLoc (E := E0) (Γ := NSΓ) F0 (τ := SB) (.mem 3 0)).run nz=(.ok (.memRef rfl 0),nz) ∧
    (Source.readLoc (E := E0) (Γ := NSΓ) F0 (τ := SB) (.mem 3 2)).run nz=(.ok (.memRef rfl 0),nz) ∧
    (Source.readLoc (E := E0) (Γ := NSΓ) F0 (τ := .bool) (.mem 0 1)).run nz=(.ok (.bool true),nz) ∧
    cells nt=[w[48],w[32],w[32],w[36],w[1],w[0],w[99],w[3],w[1],w[1],w[0],w[3],w[0],w[1],w[0],w[1],w[16],w[3],w[16],w[24],w[16],w[0]] ∧
    [nm.mem 6,nt.mem 6]=[w[1],w[1]] ∧ nt.stack=[w[42]] ∧
    KeepsAllocator 1 8 ns base nm (ns.withHeap nh) nt := by
  obtain ⟨out,z,ho,hs,hloc,he,hstmt,hi,hc,hr,hm,hrepr,hlocals,hparent,ha⟩ :=
    SourceBoolRefsAt.resolved_nested_assign_word (Source.SemanticsExamples.G0 p) F0 0 nsroot nsi nsj .here ns
      nroot ni nj .here fresh left ⟨0,by decide⟩ ⟨1,by decide⟩ true addresses nat_initial rfl rfl rfl rfl
      rfl rfl rfl rfl nparent (by change 1<hp.len left .dyn;simp only [Heap.len,Heap.get,Objs.get,hp,left,MObj.elems_dyn];decide)
      (by intro t ht hne;exact hne) SH nmem nrepr
  have hout : out=nh := Option.some.inj (ho.symm.trans nheaprun)
  have hz : z=nz := congrArg Prod.snd (hs.symm.trans nsourcerun)
  subst out;subst z
  refine ⟨hloc,he,hstmt,hi,hc,hr,hm,hrepr,hlocals,?_,?_,hr.parent_read F0 0 left ?_,hr.parent_read F0 2 left ?_,
    (hr.child_read_iff F0 0 left ?_ (uintOfNat 1) true).mpr ?_,rfl,rfl,rfl,ha⟩
  all_goals simp only [nh,Heap.index,Heap.get_set_same,Heap.get_set_ne hp left right (by decide),
    Heap.get_set_ne hp left old (by decide),Heap.get_set_ne hp left fresh (by decide),MObj.elems_setElem]
  all_goals simp only [Heap.get,Objs.get,hp,left,right,old,fresh,MObj.elems_dyn,uintOfNat]
  all_goals rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.nested_assignment_views' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms nested_assignment_views


private def nah := hp.set right (MObj.setElem .dyn (hp.get right) 0 true)
private def naz : Source.EMState E0 NSΓ := (ny.1,{ny.2 with heap := ny.2.heap.write 1 (sourceBoolMemory [true,true,false]) (by rfl)})
private def natarget := writeMachine nm 25 w[1]
private def naltTerm : Source.RExpr E0 NSΓ .bool := sourceNestedAssign nsroot nsj nsi .here
private def naltCode : List Instr := nestedWriteCode (C := C) 1 nroot nj ni .here
private def oldSourceRoot : Source.Idx NSΓ SR := .there backup
private def oldTargetRoot : Idx NΓ (.mem R) := .there (.there (.there (.there (.there .here))))

/-- Swapping the ACTUAL current indices selects the different child and gives
materially different complete heaps/cells. Reusing the stale old parent rejects. -/
theorem nested_changed_selection (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 4 naltTerm).run ny=(.ok (.val (.bool true)),naz) ∧
    run naltCode nm=.ok natarget 0 ∧ SourceBoolRefsAt naz 3 nah fresh addresses ∧
    [MObj.elems .dyn (nah.get left),MObj.elems .dyn (nah.get right)]=[[true,false,false],[true,true,false]] ∧
    cells natarget=[w[48],w[32],w[32],w[36],w[1],w[0],w[99],w[3],w[1],w[0],w[0],w[3],w[1],w[1],w[0],w[1],w[16],w[3],w[16],w[24],w[16],w[0]] ∧
    [nt.mem 18,nt.mem 25,natarget.mem 18,natarget.mem 25]=[w[1],w[0],w[0],w[1]] ∧
    nt≠natarget ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 4 (sourceNestedAssign oldSourceRoot nsj nsi .here)).run ny=
      (.error (.revert (Source.panicData .index)),ny) ∧
    run (nestedWriteCode (C := C) 1 oldTargetRoot nj ni .here) nm=.revert := by
  have hq : ns.heap.index fresh .dyn (indexValue ⟨1,by decide⟩)=some right := by
    change hp.index fresh .dyn (indexValue ⟨1,by decide⟩)=some right
    exact parent_word
  obtain ⟨out,z,ho,hs,_,he,_,_,hc,hr,_,_,_,_,_⟩ :=
    SourceBoolRefsAt.resolved_nested_assign_word (Source.SemanticsExamples.G0 p) F0 0 nsroot nsj nsi .here ns
      nroot nj ni .here fresh right ⟨1,by decide⟩ ⟨0,by decide⟩ true addresses nat_initial rfl rfl rfl rfl rfl rfl rfl rfl
      hq (by change 0<hp.len right .dyn;simp only [Heap.len,Heap.get,Objs.get,hp,right,MObj.elems_dyn];decide)
      (by intro t ht hne;exact hne) SH nmem nrepr
  have hh : ns.heap.writeAddr (.index right .dyn (indexValue ⟨0,by decide⟩)) true=some nah := by
    change hp.writeAddr (.index right .dyn (indexValue ⟨0,by decide⟩)) true=some nah
    simp only [Heap.writeAddr,Heap.setIndex,indexValue,Int.toNat_natCast]
    exact if_pos (by simp only [Heap.get,Objs.get,hp,right,MObj.elems_dyn];decide)
  have hout : out=nah := Option.some.inj (ho.symm.trans hh)
  have hs' : (Source.writeLoc (E := E0) (Γ := NSΓ) F0 3 (.mem 1 0) (.bool true)).run ny=(.ok (),naz) := by
    have h : ny.2.heap.get 1=some ⟨SB,sourceBoolMemory [false,true,false]⟩ := rfl
    obtain ⟨_,hw⟩ := source_bool_write ny 1 [false,true,false] h 0 (by decide) true
    exact hw
  have hz : z=naz := congrArg Prod.snd (hs.symm.trans hs')
  subst out;subst z
  have hold : SourceBoolRefsAt ny 2 ns.heap old addresses := old_at.same_heaps rfl rfl
  obtain ⟨hbad,_,hbadcode⟩ := SourceBoolRefsAt.nested_assign_parent_bounds (Source.SemanticsExamples.G0 p) F0 0
    oldSourceRoot nsj nsi .here ns oldTargetRoot nj ni .here old ⟨1,by decide⟩ true addresses hold rfl rfl rfl rfl rfl rfl
    (by change hp.len old .dyn≤1;simp only [Heap.len,Heap.get,Objs.get,hp,old,MObj.elems_dyn];decide) nrepr
  refine ⟨he,hc,hr,?_,rfl,rfl,?_,hbad,hbadcode⟩
  · simp only [nah,Heap.get_set_same,Heap.get_set_ne hp right left (by decide),MObj.elems_setElem]
    simp only [Heap.get,Objs.get,hp,left,right,MObj.elems_dyn];rfl
  · intro heq
    have h := congrArg (fun x : Machine => x.mem 18) heq
    change w[1]=w[0] at h
    cases h

private def npy : Source.EMState E0 NSΓ := (ny.1.set nsi (sourceUint (indexValue ⟨3,by decide⟩)),ny.2)
private def nps := ns.setLocal ni (indexValue ⟨3,by decide⟩)
private def npm := writeMachine nm 5 w[3]
private theorem npr : RefArrayStateRepr 1 1 8 nf nps base npm :=
  ⟨nrepr.state.setVal ni (indexValue ⟨3,by decide⟩) w[3] (ReprV.uint_of rfl),nrepr.arrays.localWrite 5 (by decide) w[3]⟩
private def ncy : Source.EMState E0 NSΓ := (ny.1.set nsj (sourceUint (indexValue ⟨3,by decide⟩)),ny.2)
private def ncs := ns.setLocal nj (indexValue ⟨3,by decide⟩)
private def ncm := writeMachine nm 4 w[3]
private theorem ncr : RefArrayStateRepr 1 1 8 nf ncs base ncm :=
  ⟨nrepr.state.setVal nj (indexValue ⟨3,by decide⟩) w[3] (ReprV.uint_of rfl),nrepr.arrays.localWrite 4 (by decide) w[3]⟩

/-- Parent and child endpoint rejection are independently reached by the SAME
nested assignment; insufficient horizons are actual unchanged-state timeouts. -/
theorem nested_assignment_rejection (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 4 nterm).run npy=(.error (.revert (Source.panicData .index)),npy) ∧
    Stmt.run nps nprog=.error .revert ∧ run ncode npm=.revert ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 4 nterm).run ncy=(.error (.revert (Source.panicData .index)),ncy) ∧
    Stmt.run ncs nprog=.error .revert ∧ run ncode ncm=.revert ∧
    (∀ n,n≤3 → (Source.evalE (Source.SemanticsExamples.G0 p) F0 n nterm).run ny=(.error .timeout,ny)) := by
  have hpa : SourceBoolRefsAt npy 3 nps.heap fresh addresses := fresh_at.same_heaps rfl rfl
  obtain ⟨he,hi,hc⟩ := SourceBoolRefsAt.nested_assign_parent_bounds (Source.SemanticsExamples.G0 p) F0 0
    nsroot nsi nsj .here nps nroot ni nj .here fresh ⟨3,by decide⟩ true addresses hpa rfl rfl rfl rfl rfl rfl
    (by change hp.len fresh .dyn≤3;simp only [Heap.len,Heap.get,Objs.get,hp,fresh,MObj.elems_dyn];decide) npr
  have hch : SourceBoolRefsAt ncy 3 ncs.heap fresh addresses := fresh_at.same_heaps rfl rfl
  obtain ⟨he',hi',hc'⟩ := SourceBoolRefsAt.nested_assign_child_bounds (Source.SemanticsExamples.G0 p) F0 0
    nsroot nsi nsj .here ncs nroot ni nj .here fresh left ⟨0,by decide⟩ ⟨3,by decide⟩ true addresses hch
    rfl rfl rfl rfl rfl rfl rfl rfl nparent
    (by change hp.len left .dyn≤3;simp only [Heap.len,Heap.get,Objs.get,hp,left,MObj.elems_dyn];decide) ncr
  exact ⟨he,hi,hc,he',hi',hc',source_nested_assign_low_horizon (Source.SemanticsExamples.G0 p) F0 ny nsroot nsi nsj .here⟩

private theorem nallocator0 : StructAllocatorRepr σ0.heap base 8 ⟨48,by decide⟩ machine0 := by
  apply AllocatorRepr.withoutStructs _ (fun q => no_struct q)
  refine ⟨initial_state0.heap,?_,?_⟩
  · refine ⟨by decide,by decide,rfl,?_⟩
    intro addr ha
    change 48≤addr at ha
    change (if addr=0 then w[48] else if addr=1 then w[32] else if addr=2 then w[32] else if addr=3 then w[36] else if addr=7 then w[99]
      else if addr=16 then w[3] else if addr=17 then w[1] else if addr=24 then w[3] else if addr=26 then w[1]
      else if addr=32 then w[1] else if addr=33 then w[16] else if addr=36 then w[3] else if addr=37 then w[16]
      else if addr=38 then w[24] else if addr=39 then w[16] else w[0])=w[0]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),
      if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),
      if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  · intro p q
    obtain ⟨rfl,hq|hq⟩ := prim_refs q <;> cases hq
    all_goals simp only [σ0,Heap.len,Heap.get,Objs.get,hp,left,right,base,MObj.elems_dyn] <;> decide
private theorem nallocator : StructAllocatorRepr ns.heap base 8 ⟨48,by decide⟩ nm :=
  ((nallocator0.localWrite 4 (by decide) (by decide) w[1]).localWrite 5 (by decide) (by decide) w[0]).localWrite 6 (by decide) (by decide) w[1]

/-- The allocator conclusion is inhabited, not just a vacuous conditional. -/
theorem nested_allocator_instance (p : Roadmap.Pipeline) :
    StructAllocatorRepr ns.heap base 8 ⟨48,by decide⟩ nm ∧
    StructAllocatorRepr (ns.withHeap nh).heap base 8 ⟨48,by decide⟩ nt := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,ha⟩ := nested_assignment_views p
  exact ⟨nallocator,ha ⟨48,by decide⟩ (by decide) nallocator⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.nested_changed_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms nested_changed_selection
/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.nested_assignment_rejection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms nested_assignment_rejection
/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.nested_allocator_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms nested_allocator_instance


private def nfy : Source.EMState E0 NSΓ := (ny.1.set .here (.bool false),ny.2)
private def nfs := ns.setLocal (.here : Idx NΓ (.val .bool)) false
private def nfm := writeMachine nm 6 w[0]
private theorem nfr : RefArrayStateRepr 1 1 8 nf nfs base nfm :=
  ⟨nrepr.state.setVal .here false w[0] rfl,nrepr.arrays.localWrite 6 (by decide) w[0]⟩
private theorem nfmemo : Source.MemOK E0 SH nfy :=
  ⟨⟨nmem.1.1,Source.LocalsOK.set ny.1 .here nmem.1.2 trivial⟩,nmem.2⟩

/-- Changing the CURRENT RHS changes the written value. The whole code cannot
substitute the earlier true payload or ignore its actual stack input. -/
theorem nested_current_rhs (p : Roadmap.Pipeline) :
    ∃ (out : Heap H) (z : Source.EMState E0 NSΓ),
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 4 nterm).run nfy=(.ok (.val (.bool false)),z) ∧
      Stmt.run nfs nprog=.ok ⟨nfs.withHeap out,List.prefix_refl _⟩ ∧
      run ncode nfm=.ok (writeMachine nfm 18 w[0]) 0 ∧ SourceBoolRefsAt z 3 out fresh addresses ∧
      Source.MemOK E0 SH z ∧
      [MObj.elems .dyn (out.get left),MObj.elems .dyn (out.get right)]=[[true,false,false],[false,true,false]] ∧
      out.index left .dyn (indexValue ⟨1,by decide⟩)=some false ∧
      (Source.readLoc (E := E0) (Γ := NSΓ) F0 (τ := .bool) (.mem 0 1)).run z=(.ok (.bool false),z) ∧
      cells (writeMachine nfm 18 w[0])=cells machine ∧
      [nt.mem 18,(writeMachine nfm 18 w[0]).mem 18]=[w[1],w[0]] ∧ z.1=nfy.1 := by
  have hr : SourceBoolRefsAt nfy 3 nfs.heap fresh addresses := fresh_at.same_heaps rfl rfl
  obtain ⟨out,z,ho,_,_,he,_,hi,hc,hrep,hm,_,hl,_,_⟩ :=
    SourceBoolRefsAt.resolved_nested_assign_word (Source.SemanticsExamples.G0 p) F0 0 nsroot nsi nsj .here nfs
      nroot ni nj .here fresh left ⟨0,by decide⟩ ⟨1,by decide⟩ false addresses hr rfl rfl rfl rfl rfl rfl rfl rfl
      nparent (by change 1<hp.len left .dyn;simp only [Heap.len,Heap.get,Objs.get,hp,left,MObj.elems_dyn];decide)
      (by intro t ht hne;exact hne) SH nfmemo nfr
  have hout : out=hp.set left (MObj.setElem .dyn (hp.get left) 1 false) := by
    have hw : nfs.heap.writeAddr (.index left .dyn (indexValue ⟨1,by decide⟩)) false=
        some (hp.set left (MObj.setElem .dyn (hp.get left) 1 false)) := by
      change hp.writeAddr (.index left .dyn (indexValue ⟨1,by decide⟩)) false=_
      simp only [Heap.writeAddr,Heap.setIndex,indexValue,Int.toNat_natCast]
      exact if_pos (by simp only [Heap.get,Objs.get,hp,left,MObj.elems_dyn];decide)
    exact Option.some.inj (ho.symm.trans hw)
  have hval : out.index left .dyn (indexValue ⟨1,by decide⟩)=some false := Heap.readAddr_writeAddr_same ho
  refine ⟨out,z,he,hi,hc,hrep,hm,?_,hval,(hrep.child_read_iff F0 0 left ?_ (indexValue ⟨1,by decide⟩) false).mpr hval,rfl,rfl,hl⟩
  · rw [hout]
    simp only [Heap.get_set_same,Heap.get_set_ne hp left right (by decide),MObj.elems_setElem]
    simp only [Heap.get,Objs.get,hp,left,right,MObj.elems_dyn];rfl
  · rw [hout,Heap.get_set_ne hp left fresh (by decide)]
    simp only [Heap.get,Objs.get,hp,fresh,MObj.elems_dyn];rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.nested_current_rhs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms nested_current_rhs


private def nptr : List Instr := [.mload (cellOf 1 nroot)] ++ compileVal 1 (.simple (.local ni) : Val C NΓ .uint) ++ readArrayStackCode

/-- COMPLETE ordered RHS/pointer/index/write observations: the current RHS stays
beneath the selected child pointer and child index until the real write consumes
all three. Source parent/index observations are actual independent evaluations. -/
theorem nested_ordered_prefixes (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (.local (.here : Source.Idx NSΓ .bool))).run ny=
      (.ok (.val (.bool true)),ny) ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local nsroot) (.local nsi) rfl)).run ny=
      (.ok (.val (.memRef rfl 0)),ny) ∧
    run (compileVal 1 (.simple (.local (.here : Idx NΓ (.val .bool))) : Val C NΓ .bool)) nm=.ok (nm.push w[1]) 0 ∧
    run nptr (nm.push w[1])=.ok ((nm.push w[1]).push w[16]) 0 ∧
    run (compileVal 1 (.simple (.local nj) : Val C NΓ .uint)) ((nm.push w[1]).push w[16])=
      .ok (((nm.push w[1]).push w[16]).push w[1]) 0 ∧
    run writeArrayStackCode (((nm.push w[1]).push w[16]).push w[1])=.ok nt 0 ∧
    [MObj.elems .dyn (ns.heap.get left),MObj.elems .dyn (ns.heap.get right)]=[[true,false,false],[false,true,false]] ∧
    cells nm=cells machine ∧ [nm.mem 6,nt.mem 6]=[w[1],w[1]] := by
  have hcert : RefPtrFrag 1 nf (.loc (.index .dyn (.var nroot rfl) (.simple (.local ni)))) nptr :=
    .index _ _ (.local nroot rfl) _ rfl
  have he : (MPath.loc (.index .dyn (.var nroot rfl) (.simple (.local ni)))).mvalT ns=.ok left := by
    simp only [MPath.mvalT,MLoc.addrT,Val.evalT,Simple.evalT,
      show TEnv.get nroot ns.env=some fresh from rfl,
      show TEnv.get ni ns.env=indexValue ⟨0,by decide⟩ from rfl,
      Heap.readAddr,nparent,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have hptr := hcert.run_of_eval (nrepr.push w[1]) he
  have hwrite : run (writeArrayCode (base left.id)) ((nm.push w[1]).push w[1])=.ok nt 0 := by
    rcases writeArray_correct (nrepr.state.heap.arrays left) ⟨1,by decide⟩ true w[1] rfl with ⟨_,_,hc,_⟩|⟨hn,_⟩
    · exact hc
    · rw [nheaprun] at hn;cases hn
  refine ⟨source_local_value_run (Source.SemanticsExamples.G0 p) F0 2 ny .here (.bool true) rfl,
    nat_initial.eval_parent_read (Source.SemanticsExamples.G0 p) F0 0 nsroot nsi (indexValue ⟨0,by decide⟩) left rfl rfl nparent,
    rfl,hptr,rfl,?_,?_,rfl,rfl⟩
  · change run writeArrayStackCode (((nm.push w[1]).push (.val (base left.id))).push w[1])=.ok nt 0
    rw [writeArrayStackCode,arrayStack_append_eq (nm.push w[1]) (base left.id) ⟨1,by decide⟩ _
      (ns.heap.len_dyn_lt left) (nrepr.state.heap.arrays left).length,←writeArrayCode]
    exact hwrite
  · simp only [ns,State.push,σ,σ1,σ0,Heap.get,Objs.get,hp,left,right,MObj.elems_dyn]

/-- info: 'Solidity.Backend.MemoryOps.SourceNestedMemoryControls.nested_ordered_prefixes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms nested_ordered_prefixes

end Solidity.Backend.MemoryOps.SourceNestedMemoryControls
