import Solidity.Backend.MemoryOps.SourceNestedMemory
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

end Solidity.Backend.MemoryOps.SourceNestedMemoryControls
