import Solidity.Backend.MemoryOps.SourceReferenceRead
import Solidity.Backend.MemoryOps.SourceReferenceReadSequence
import Solidity.Backend.MemoryOps.SourceReferenceAliasSequence
import Solidity.Backend.MemoryOps.SourceReferenceAliasDelete
import Solidity.Backend.MemoryOps.SourceReferenceAliasReject
import Solidity.Backend.MemoryOps.SourceRhsAssignment
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

/-! Reuses the original owned populated nested fixture, checked against current
published interfaces. No constructor/heap/copy semantics is reimplemented. -/
namespace Solidity.Backend.MemoryOps.SourceReferenceReadControls
open Evm Evm.Memory
open Source.SemanticsExamples (E0 F0 G0 s0)
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
private theorem allocator : StructAllocatorRepr σ.heap base 8 ⟨48,by decide⟩ machine :=
  (nallocator0.localWrite 4 (by decide) (by decide) w[1]).localWrite 5 (by decide) (by decide) w[0]

private def dref (self : Bool) := if self then fresh else old
private def daddr (self : Bool) := if self then 3 else 2
private def ds (self : Bool) : Source.Idx SΓ SR := if self then ssrc else sdst
private def dt (self : Bool) : Idx Γ (.mem R) := if self then tsrc else tdst
private def ti : Idx Γ (.val .uint) := .here
private def tj : Idx Γ (.val .uint) := .there .here
private def postHeap (self : Bool) := hp.set (dref self) (MObj.setElem .dyn (hp.get (dref self)) 0 right)
private def postWord (self : Bool) := writeMachine machine ((base (dref self).id).val+1) (.val (base right.id))
private theorem dat (self : Bool) : SourceBoolRefsAt sy (daddr self) hp (dref self) addresses := by
  cases self
  · exact old_at
  · exact fresh_at
private theorem dhi (self : Bool) : 0<hp.len (dref self) .dyn := by
  cases self <;> simp only [dref,Bool.false_eq_true,if_false,if_true,Heap.len,Heap.get,Objs.get,hp,old,fresh,MObj.elems_dyn] <;> decide

/-- The RHS has no child-reference local. Actual INITIAL fresh-parent[1]
selects RIGHT, changes the old-parent slot (or the same parent), and retains
both old child contents, locals, allocation cursor and all external frames. -/
theorem computed_reference_client (p : Roadmap.Pipeline) (fuel nps : Nat) (self : Bool) :
    ∃ z : Source.EMState E0 SΓ,
      (Source.evalE (G0 p) F0 (fuel+4) (sourceReferenceReadAssign (ds self) ssrc sj si)).run sy=
        (.ok (.val (.memRef rfl 1)),z) ∧
      (Source.execS (G0 p) F0 (fuel+5) nps none (.expr (sourceReferenceReadAssign (ds self) ssrc sj si) :
        Source.RStmt E0 [] false .body SΓ SΓ) sy.1).run (.nil,sy.2)=(.ok (.normal sy.1),(.nil,z.2)) ∧
      Stmt.run σ (.assignMem (.index .dyn (.var (dt self) rfl) (.simple (.local ti)))
        (.ref (.loc (.index .dyn (.var tsrc rfl) (.simple (.local tj))))))=
          .ok ⟨σ.withHeap (postHeap self),List.prefix_refl _⟩ ∧
      run (referenceReadWriteCode (C := C) 1 (dt self) tsrc ti tj) machine=.ok (postWord self) 0 ∧
      SourceBoolRefsAt z (daddr self) (postHeap self) (dref self) addresses ∧ Source.MemOK E0 SH z ∧
      RefArrayStateRepr 1 1 8 frag (σ.withHeap (postHeap self)) base (postWord self) ∧
      SourceBoolMemoryAt z 0 (postHeap self) left .dyn ∧ SourceBoolMemoryAt z 1 (postHeap self) right .dyn ∧
      z.1=sy.1 ∧ z.2.heap.next=5 ∧
      (∀ q : HRef H B,(postHeap self).get q=hp.get q) ∧
      (∀ {Q : RefTy} (q : HRef H Q),(dref self).id≠q.id → (postHeap self).get q=hp.get q) ∧
      (∀ a,a≠daddr self → z.2.heap.get a=sy.2.heap.get a) ∧
      (z.2.ex=sy.2.ex ∧ z.2.events=sy.2.events ∧ z.2.logs=sy.2.logs ∧ z.2.fnLocals=sy.2.fnLocals) ∧
      StructAllocatorRepr (postHeap self) base 8 ⟨48,by decide⟩ (postWord self) ∧
      (postWord self).stack=[w[42]] := by
  have result := (dat self).computed_reference_assign_word (G0 p) F0 fuel nps sy σ (dref self) fresh
    (daddr self) 3 addresses fresh_at (ds self) ssrc sj si (dt self) tsrc ti tj ⟨0,by decide⟩ ⟨1,by decide⟩
    (by cases self <;> rfl) rfl rfl rfl (by cases self <;> rfl) rfl rfl rfl
    (dhi self) (by simp only [Heap.len,MObj.elems_dyn];decide) SH source_memOK initial_repr
  obtain ⟨out,z,hit,child,hw,read,expr,stmt,native,word,hr,mok,represented,locals,elems,children,sourceChildren,other,addrs,next,effects,alloc⟩ := result
  have srcElems : MObj.elems .dyn (σ.heap.get fresh)=[left,right,left] := by rw [MObj.elems_dyn];rfl
  simp only [srcElems,List.getElem_cons_succ,List.getElem_cons_zero] at hw expr word represented alloc
  have known : hp.writeAddr (.index (dref self) .dyn (indexValue ⟨0,by decide⟩)) right=some (postHeap self) := by
    simp only [Heap.writeAddr,Heap.setIndex,indexValue,Int.toNat_natCast,show 0<(MObj.elems .dyn (hp.get (dref self))).length from dhi self,↓reduceIte]
    rfl
  have outEq : out=postHeap self := Option.some.inj (hw.symm.trans known)
  subst out
  refine ⟨z,expr,stmt,native,word,hr,mok,represented,sourceChildren left left_at,sourceChildren right right_at,locals,next,children,other,addrs,effects,?_,rfl⟩
  apply alloc ⟨48,by decide⟩ allocator
  cases self <;> simp only [dref,Bool.false_eq_true,if_false,if_true,Heap.len,Heap.get,Objs.get,hp,old,fresh,MObj.elems_dyn,base] <;> decide

private def cells : List Nat := [0,1,2,3,4,5,6,7,16,17,18,19,24,25,26,27,32,33,36,37,38,39,44,45]
private def words (m : Machine) := cells.map m.mem
private def views (h : Heap H) := (MObj.elems .dyn (h.get left),MObj.elems .dyn (h.get right),
  (MObj.elems .dyn (h.get old)).map HRef.id,(MObj.elems .dyn (h.get fresh)).map HRef.id,(MObj.elems .dyn (h.get empty)).map HRef.id)
private def sourceViews (y : Source.EMState E0 SΓ) := [y.2.heap.get 0,y.2.heap.get 1,y.2.heap.get 2,y.2.heap.get 3,y.2.heap.get 4]
private def expectedSource (self : Bool) : List (Option (Σ τ : Source.STy, Source.Data E0.layout τ)) :=
  [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,
   some ⟨SR,pdata (if self then [left] else [right])⟩,
   some ⟨SR,pdata (if self then [right,right,left] else [left,right,left])⟩,some ⟨SR,pdata []⟩]
private theorem post_elems (self : Bool) :
    MObj.elems .dyn ((postHeap self).get (dref self))=(if self then [left,right,left] else [left]).set 0 right := by
  unfold postHeap
  rw [Heap.get_set_same,MObj.elems_setElem]
  cases self <;> rw [MObj.elems_dyn] <;> rfl

/-- All five native objects and every represented word are ordered observations,
including source sharing, empty parent, untouched children, guard/free-pointer,
and retained root-alias cells. -/
theorem complete_reference_vectors (self : Bool) :
    words machine=[w[48],w[32],w[32],w[36],w[1],w[0],w[0],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[1],w[16],w[3],w[16],w[24],w[16],w[0],w[0]] ∧
    words (postWord self)=[w[48],w[32],w[32],w[36],w[1],w[0],w[0],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[1],(if self then w[16] else w[24]),w[3],(if self then w[24] else w[16]),w[24],w[16],w[0],w[0]] ∧
    views hp=([true,false,false],[false,true,false],[0],[0,1,0],[]) ∧
    views (postHeap self)=([true,false,false],[false,true,false],(if self then [0] else [1]),(if self then [1,1,0] else [0,1,0]),[]) ∧
    sourceViews sy=[some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,
      some ⟨SR,pdata [left]⟩,some ⟨SR,pdata [left,right,left]⟩,some ⟨SR,pdata []⟩] ∧
    (postWord self).mem 0=w[48] ∧ (postWord self).stack=[w[42]] := by
  cases self <;> simp only [Bool.false_eq_true,if_false,if_true]
  all_goals
    refine ⟨rfl,rfl,?_,?_,rfl,rfl,rfl⟩
    · simp only [views,Heap.get,Objs.get,hp,left,right,old,fresh,empty,MObj.elems_dyn,List.map_cons,List.map_nil]
    · simp only [views,postHeap,dref,Bool.false_eq_true,if_false,if_true,Heap.set,Objs.set,Heap.get,Objs.get,hp,left,right,old,fresh,empty,MObj.elems_dyn,MObj.setElem_dyn,List.map_cons,List.map_nil]
      rfl

private theorem source_tables (self : Bool) (z : Source.EMState E0 SΓ)
    (hr : SourceBoolRefsAt z (daddr self) (postHeap self) (dref self) addresses)
    (other : ∀ a,a≠daddr self → z.2.heap.get a=sy.2.heap.get a) : sourceViews z=expectedSource self := by
  have hp := hr.parent
  rw [post_elems] at hp
  cases self
  · change z.2.heap.get 2=some ⟨SR,pdata [right]⟩ at hp
    unfold sourceViews expectedSource
    rw [hp,other 0 (by decide),other 1 (by decide),other 3 (by decide),other 4 (by decide)]
    rfl
  · change z.2.heap.get 3=some ⟨SR,pdata [right,right,left]⟩ at hp
    unfold sourceViews expectedSource
    rw [hp,other 0 (by decide),other 1 (by decide),other 2 (by decide),other 4 (by decide)]
    rfl

/-- The SAME executed assignment reaches RIGHT's false inner value; the retained
LEFT object still reads true. Complete Source tables and no fresh address5
show existing identity replacement rather than payload copy/allocation. -/
theorem computed_reference_observations (p : Roadmap.Pipeline) (fuel nps : Nat) (self : Bool) :
    ∃ z : Source.EMState E0 SΓ,
      (Source.evalE (G0 p) F0 (fuel+4) (sourceReferenceReadAssign (ds self) ssrc sj si)).run sy=
        (.ok (.val (.memRef rfl 1)),z) ∧ sourceViews z=expectedSource self ∧
      (Source.evalE (G0 p) F0 (fuel+3) (.indexArray (.indexArray (.local (ds self)) (.local sj) rfl) (.local sj) rfl)).run z=
        (.ok (.val (.bool false)),z) ∧
      (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := .bool) (.mem 0 0)).run z=(.ok (.bool true),z) ∧
      (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := .bool) (.mem 1 0)).run z=(.ok (.bool false),z) ∧
      (postHeap self).index (dref self) .dyn (uintOfNat 0)=some right ∧
      (postHeap self).index right .dyn (uintOfNat 0)=some false ∧
      z.1=sy.1 ∧ z.2.heap.next=5 ∧ z.2.heap.get 5=none ∧
      (z.2.ex=sy.2.ex ∧ z.2.events=sy.2.events ∧ z.2.logs=sy.2.logs ∧ z.2.fnLocals=sy.2.fnLocals) := by
  obtain ⟨z,expr,stmt,native,word,hr,mok,represented,hl,hright,locals,next,children,other,addrs,effects,alloc,stack⟩ :=
    computed_reference_client p fuel nps self
  have leftRead : (postHeap self).index left .dyn (uintOfNat 0)=some true := by
    simp only [Heap.index,children left,MObj.elems_dyn]
    rfl
  have rightRead : (postHeap self).index right .dyn (uintOfNat 0)=some false := by
    simp only [Heap.index,children right,MObj.elems_dyn]
    rfl
  have selected : (postHeap self).index (dref self) .dyn (uintOfNat 0)=some right := by
    change (MObj.elems .dyn ((postHeap self).get (dref self)))[(uintOfNat 0).val.toNat]?=some right
    rw [post_elems]
    cases self <;> rfl
  have nested := hr.eval_nested_read (G0 p) F0 fuel (ds self) sj sj (uintOfNat 0) (uintOfNat 0) right false
    (by rw [locals];cases self <;> rfl) (by rw [locals];rfl) (by rw [locals];rfl) selected rightRead
  have lr := (hl.read_iff F0 (uintOfNat 0) true).mpr leftRead
  have rr := (hright.read_iff F0 (uintOfNat 0) false).mpr rightRead
  refine ⟨z,expr,source_tables self z hr addrs,nested,lr,rr,selected,rightRead,locals,next,?_,effects⟩
  rw [addrs 5 (by cases self <;> decide)]
  rfl

/-- Actual initial RHS reads distinguish the supported selected index/parent
from stale-parent or wrong-index selection. Whole output word vectors differ
from an omitted redirect, although both child payloads are unchanged. -/
theorem wrong_reference_negative (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local ssrc) (.local si) rfl)).run sy=
      (.ok (.val (.memRef rfl 1)),sy) ∧
    (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local ssrc) (.local sj) rfl)).run sy=
      (.ok (.val (.memRef rfl 0)),sy) ∧
    (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local sdst) (.local sj) rfl)).run sy=
      (.ok (.val (.memRef rfl 0)),sy) ∧
    words (postWord false)≠words machine ∧ words (postWord true)≠words machine := by
  have f1 : hp.index fresh .dyn (uintOfNat 1)=some right := by rw [Heap.index,MObj.elems_dyn];rfl
  have f0 : hp.index fresh .dyn (uintOfNat 0)=some left := by rw [Heap.index,MObj.elems_dyn];rfl
  have o0 : hp.index old .dyn (uintOfNat 0)=some left := by rw [Heap.index,MObj.elems_dyn];rfl
  refine ⟨fresh_at.eval_parent_read (G0 p) F0 fuel ssrc si (uintOfNat 1) right rfl rfl f1,
    fresh_at.eval_parent_read (G0 p) F0 fuel ssrc sj (uintOfNat 0) left rfl rfl f0,
    old_at.eval_parent_read (G0 p) F0 fuel sdst sj (uintOfNat 0) left rfl rfl o0,?_,?_⟩
  · intro h
    have x := congrArg (fun v => v[17]?) h
    change some w[24]=some w[16] at x
    cases x
  · intro h
    have x := congrArg (fun v => v[19]?) h
    change some w[24]=some w[16] at x
    cases x

private def emptySource : Source.EMState E0 SΓ := (sy.1.set ssrc (.memRef rfl 4),sy.2)
private def emptyState := σ.setLocal tsrc (some empty)
private def emptyWord := writeMachine machine (cellOf 1 tsrc) (.val (base empty.id))
private theorem emptySourceOK : Source.MemOK E0 SH emptySource := by
  have h := Source.writeLoc_memOK (E := E0) (Γ := SΓ) (H := SH) F0 0 (.local ssrc)
    (.memRef rfl 4) sy ⟨source_memOK,⟨SR,rfl,rfl⟩⟩
  exact h

/-- A genuinely represented literal empty parent rejects index0 before LHS
execution. Source panic/state and erased native/word failure outcomes stay
separate; no successful suffix, post-revert machine or rollback is invented. -/
theorem empty_reference_rejection (p : Roadmap.Pipeline) (fuel : Nat) :
    Source.MemOK E0 SH emptySource ∧
    RefArrayStateRepr 1 1 8 frag emptyState base emptyWord ∧
    (Source.evalE (G0 p) F0 (fuel+4) (sourceReferenceReadAssign sdst ssrc sj sj)).run emptySource=
      (.error (.revert (Source.panicData .index)),emptySource) ∧
    Stmt.run emptyState (.assignMem (.index .dyn (.var tdst rfl) (.simple (.local ti)))
      (.ref (.loc (.index .dyn (.var tsrc rfl) (.simple (.local ti))))))=.error .revert ∧
    run (referenceReadWriteCode (C := C) 1 tdst tsrc ti ti) emptyWord=.revert := by
  have hr : SourceBoolRefsAt emptySource 4 hp empty addresses := ⟨empty_at.parent,empty_at.children⟩
  have source := hr.computed_reference_rhs_bounds (G0 p) F0 (fuel+1) sdst ssrc sj sj (uintOfNat 0) rfl rfl
    (by simp only [Heap.len,MObj.elems_dyn];decide)
  have represented : RefArrayStateRepr 1 1 8 frag emptyState base emptyWord := initial_repr.setMem tsrc empty
  have badPath : (MPath.loc (.index .dyn (.var tsrc rfl) (.simple (.local ti))) : MPath C Γ (.ref B)).mvalT emptyState=.error .revert := by
    simp only [MPath.mvalT,MLoc.addrT,Val.evalT,Simple.evalT,
      show TEnv.get tsrc emptyState.env=some empty from rfl,
      show TEnv.get ti emptyState.env=uintOfNat 0 from rfl,Heap.readAddr,Heap.index,MObj.elems_dyn,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    rfl
  have native : TRun.assignMem (.index .dyn (.var tdst rfl) (.simple (.local ti)))
      (.ref (.loc (.index .dyn (.var tsrc rfl) (.simple (.local ti))))) emptyState=.error .revert := by
    simp only [TRun.assignMem,MSrc.mvalT]
    rw [badPath]
    rfl
  have rhs : RefPtrFrag (C := C) 1 frag (.loc (.index .dyn (.var tsrc rfl) (.simple (.local ti))))
      ([.mload (cellOf 1 tsrc)] ++ compileVal 1 (.simple (.local ti) : Val C Γ .uint) ++ readArrayStackCode) :=
    .index (.var tsrc rfl) _ (.local tsrc rfl) _ rfl
  have whole := RefPtrFrag.writeReference represented (RefPtrFrag.local tdst rfl) rhs (.simple (.local ti)) rfl
  rw [native] at whole
  refine ⟨emptySourceOK,represented,source,native,?_⟩
  rcases whole with ⟨o,t,impossible,_⟩ | ⟨_,run⟩
  · cases impossible
  · exact run

/-- True destination endpoint1 is independently invalid while RHS fresh[1]
successfully reads the existing right child. The source state is unchanged. -/
theorem destination_reference_rejection (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) F0 (fuel+4) (sourceReferenceReadAssign sdst ssrc si si)).run sy=
      (.error (.revert (Source.panicData .index)),sy) ∧
    Stmt.run σ (.assignMem (.index .dyn (.var tdst rfl) (.simple (.local tj)))
      (.ref (.loc (.index .dyn (.var tsrc rfl) (.simple (.local tj))))))=.error .revert ∧
    run (referenceReadWriteCode (C := C) 1 tdst tsrc tj tj) machine=.revert := by
  have hq : hp.index fresh .dyn (uintOfNat 1)=some right := by rw [Heap.index,MObj.elems_dyn];rfl
  have loc : (Source.evalLoc (G0 p) F0 (fuel+3) (.indexArray (.local sdst) (by decide) (.local si) rfl)).run sy=
      (.error (.revert (Source.panicData .index)),sy) := by
    rw [Source.evalLoc,Source.Hoare.run_bind,source_local_value_run (G0 p) F0 (fuel+1) sy sdst (.memRef rfl 2) rfl]
    change ((Source.evalE (G0 p) F0 (fuel+2) (.local si)) >>= fun v => Source.indexNat v >>= fun k =>
      Source.indexLoc F0 (.memRef rfl 2 : Source.Val E0.layout SR) k).run sy=_
    rw [Source.Hoare.run_bind,source_local_value_run (G0 p) F0 (fuel+1) sy si _ rfl]
    change (Source.indexLoc F0 (.memRef rfl 2 : Source.Val E0.layout SR) (uintOfNat 1).val.toNat).run sy=_
    exact old_at.indexLoc_bounds F0 _ (by simp only [Heap.len,MObj.elems_dyn];decide)
  have source : (Source.evalE (G0 p) F0 (fuel+4) (sourceReferenceReadAssign sdst ssrc si si)).run sy=
      (.error (.revert (Source.panicData .index)),sy) := by
    rw [sourceReferenceReadAssign,Source.evalE,Source.Hoare.run_bind,
      fresh_at.eval_parent_read (G0 p) F0 (fuel+1) ssrc si (uintOfNat 1) right rfl rfl hq]
    change ((Source.evalLoc (G0 p) F0 (fuel+3) (.indexArray (.local sdst) (by decide) (.local si) rfl)) >>=
      fun l => Source.writeLoc F0 (fuel+3) l (.memRef rfl 1) >>= fun _ => pure (Source.RVal.val (.memRef rfl 1))).run sy=_
    rw [Source.Hoare.run_bind,loc]
  have hqState : σ.heap.index fresh .dyn (uintOfNat 1)=some right := hq
  have path : (MPath.loc (.index .dyn (.var tsrc rfl) (.simple (.local tj))) : MPath C Γ (.ref B)).mvalT σ=.ok right := by
    simp only [MPath.mvalT,MLoc.addrT,Val.evalT,Simple.evalT,
      show TEnv.get tsrc σ.env=some fresh from rfl,show TEnv.get tj σ.env=uintOfNat 1 from rfl,
      Heap.readAddr,hqState,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have fail : σ.heap.writeAddr (.index old .dyn (uintOfNat 1)) right=none := by
    change hp.setIndex old .dyn (uintOfNat 1) right=none
    unfold Heap.setIndex
    rw [MObj.elems_dyn]
    exact if_neg (by decide)
  have native : TRun.assignMem (.index .dyn (.var tdst rfl) (.simple (.local tj)))
      (.ref (.loc (.index .dyn (.var tsrc rfl) (.simple (.local tj))))) σ=.error .revert := by
    simp only [TRun.assignMem,MSrc.mvalT]
    rw [path]
    simp only [MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,
      show TEnv.get tdst σ.env=some old from rfl,show TEnv.get tj σ.env=uintOfNat 1 from rfl,
      fail,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have rhs : RefPtrFrag (C := C) 1 frag (.loc (.index .dyn (.var tsrc rfl) (.simple (.local tj))))
      ([.mload (cellOf 1 tsrc)] ++ compileVal 1 (.simple (.local tj) : Val C Γ .uint) ++ readArrayStackCode) :=
    .index (.var tsrc rfl) _ (.local tsrc rfl) _ rfl
  have whole := RefPtrFrag.writeReference initial_repr (RefPtrFrag.local tdst rfl) rhs (.simple (.local tj)) rfl
  rw [native] at whole
  refine ⟨source,native,?_⟩
  rcases whole with ⟨o,t,impossible,_⟩ | ⟨_,run⟩
  · cases impossible
  · exact run

/-- Insufficient expression horizon times out before the pointer read/write.
This is an evaluator observation, not a target halt or rollback theorem. -/
theorem reference_read_timeout (p : Roadmap.Pipeline) :
    (Source.evalE (G0 p) F0 2 (sourceReferenceReadAssign sdst ssrc sj si)).run sy=(.error .timeout,sy) := by
  cases p <;> rfl

/-- Selecting the already stored LEFT from fresh[0] is an executed same-pointer
no-op on every object table and represented word, not a deep-copy operation. -/
theorem same_pointer_noop (p : Roadmap.Pipeline) (fuel nps : Nat) :
    ∃ z : Source.EMState E0 SΓ,
      (Source.evalE (G0 p) F0 (fuel+4) (sourceReferenceReadAssign sdst ssrc sj sj)).run sy=(.ok (.val (.memRef rfl 0)),z) ∧
      Stmt.run σ (.assignMem (.index .dyn (.var tdst rfl) (.simple (.local ti)))
        (.ref (.loc (.index .dyn (.var tsrc rfl) (.simple (.local ti))))))=.ok ⟨σ.withHeap hp,List.prefix_refl _⟩ ∧
      run (referenceReadWriteCode (C := C) 1 tdst tsrc ti ti) machine=.ok (writeMachine machine 33 w[16]) 0 ∧
      sourceViews z=sourceViews sy ∧ words (writeMachine machine 33 w[16])=words machine ∧
      z.1=sy.1 ∧ z.2.heap.next=5 ∧
      (z.2.ex=sy.2.ex ∧ z.2.events=sy.2.events ∧ z.2.logs=sy.2.logs ∧ z.2.fnLocals=sy.2.fnLocals) := by
  have result := old_at.computed_reference_assign_word (G0 p) F0 fuel nps sy σ old fresh 2 3 addresses fresh_at
    sdst ssrc sj sj tdst tsrc ti ti ⟨0,by decide⟩ ⟨0,by decide⟩
    rfl rfl rfl rfl rfl rfl rfl rfl (by simp only [Heap.len,MObj.elems_dyn];decide)
    (by simp only [Heap.len,MObj.elems_dyn];decide) SH source_memOK initial_repr
  obtain ⟨out,z,hit,child,hw,read,expr,stmt,native,word,hr,mok,represented,locals,elems,children,sourceChildren,other,addrs,next,effects,alloc⟩ := result
  have srcElems : MObj.elems .dyn (σ.heap.get fresh)=[left,right,left] := by rw [MObj.elems_dyn];rfl
  simp only [srcElems,List.getElem_cons_zero] at hw expr word
  have known : hp.writeAddr (.index old .dyn (indexValue ⟨0,by decide⟩)) left=some hp := by
    simp only [Heap.writeAddr,Heap.setIndex,indexValue,Int.toNat_natCast,Heap.get,Objs.get,hp,old,MObj.elems_dyn,MObj.setElem_dyn,Heap.set,Objs.set]
    simp only [show 0<[left].length from by decide,↓reduceIte,List.set]
  have equal : out=hp := Option.some.inj (hw.symm.trans known)
  subst out
  refine ⟨z,expr,native,word,?_,rfl,locals,next,effects⟩
  have parent : z.2.heap.get 2=sy.2.heap.get 2 := hr.parent.trans old_at.parent.symm
  unfold sourceViews
  rw [parent,addrs 0 (by decide),addrs 1 (by decide),addrs 3 (by decide),addrs 4 (by decide)]

/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.same_pointer_noop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms same_pointer_noop
/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.empty_reference_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_reference_rejection
/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.destination_reference_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms destination_reference_rejection
/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.reference_read_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reference_read_timeout
/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.complete_reference_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_reference_vectors
/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.computed_reference_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms computed_reference_observations
/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.wrong_reference_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_reference_negative
/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.computed_reference_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms computed_reference_client

private def deletedHeap (self : Bool) := (postHeap self).set right (MObj.setElem .dyn ((postHeap self).get right) 1 false)
private def deletedWord (self : Bool) := writeMachine (postWord self) 26 (w[0])
private def deletedSource (self : Bool) : List (Option (Σ τ : Source.STy, Source.Data E0.layout τ)) :=
  [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,false,false]⟩,
   some ⟨SR,pdata (if self then [left] else [right])⟩,
   some ⟨SR,pdata (if self then [right,right,left] else [left,right,left])⟩,some ⟨SR,pdata []⟩]

/-- The SAME computed-pointer execution is followed by an actual reached
nested delete. Both parent-alias cases and both declared pipelines are inhabited.
RIGHT changes T to F; old LEFT and every parent/reference identity are retained. -/
theorem computed_reference_delete_client (p : Roadmap.Pipeline) (fuel : Nat) (self : Bool) :
    ∃ (ym z : Source.EMState E0 SΓ),
      (Source.execS (G0 p) F0 (fuel+6) SΓ.length none
        (.expr (sourceReferenceReadAssign (ds self) ssrc sj si) : Source.RStmt E0 [] false .body SΓ SΓ)
        sy.1).run (.nil,sy.2)=(.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS (G0 p) F0 (fuel+5) SΓ.length none
        (.expr (sourceNestedDelete (ds self) sj si) : Source.RStmt E0 [] false .body SΓ SΓ)
        ym.1).run (.nil,ym.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems (G0 p) F0 (fuel+7) SΓ.length none
        (.stmt (.expr (sourceReferenceReadAssign (ds self) ssrc sj si))
          (.stmt (.expr (sourceNestedDelete (ds self) sj si)) .nil) : Source.RItems E0 [] false .body SΓ SΓ)
        sy.1).run (.nil,sy.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run σ (.cons (referenceReadStmt (dt self) tsrc ti tj) (.cons (nestedDeleteStmt (dt self) ti tj) .nil))=
        .ok ⟨σ.withHeap (deletedHeap self),List.prefix_refl _⟩ ∧
      run (referenceReadWriteCode (C := C) 1 (dt self) tsrc ti tj) machine=.ok (postWord self) 0 ∧
      run (nestedDeleteCode (C := C) 1 (dt self) ti tj) (postWord self)=.ok (deletedWord self) 0 ∧
      run (referenceReadWriteCode (C := C) 1 (dt self) tsrc ti tj ++ nestedDeleteCode (C := C) 1 (dt self) ti tj)
        machine=.ok (deletedWord self) 0 ∧
      sourceViews sy=[some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,
        some ⟨SR,pdata [left]⟩,some ⟨SR,pdata [left,right,left]⟩,some ⟨SR,pdata []⟩] ∧
      sourceViews ym=expectedSource self ∧ sourceViews z=deletedSource self ∧
      SourceBoolRefsAt z (daddr self) (deletedHeap self) (dref self) addresses ∧
      SourceBoolMemoryAt z 0 (deletedHeap self) left .dyn ∧
      SourceBoolMemoryAt z 1 (deletedHeap self) right .dyn ∧ Source.MemOK E0 SH z ∧
      RefArrayStateRepr 1 1 8 frag (σ.withHeap (deletedHeap self)) base (deletedWord self) ∧
      ym.1=sy.1 ∧ z.1=sy.1 ∧ z.2.heap.next=5 ∧ z.2.heap.get 5=none ∧
      (z.2.ex=sy.2.ex ∧ z.2.events=sy.2.events ∧ z.2.logs=sy.2.logs ∧ z.2.fnLocals=sy.2.fnLocals) ∧
      StructAllocatorRepr (deletedHeap self) base 8 ⟨48,by decide⟩ (deletedWord self) ∧
      (deletedWord self).stack=[w[42]] := by
  first
  | solve | rfl | simp only [] | omega
  | have srcElems : MObj.elems .dyn (σ.heap.get fresh)=[left,right,left] := by rw [MObj.elems_dyn];rfl
    have result := (dat self).computed_reference_delete_sequence (G0 p) F0 fuel sy σ (dref self) fresh
      (daddr self) 3 addresses fresh_at (ds self) ssrc sj si si (dt self) tsrc ti tj tj
      ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨1,by decide⟩
      (by cases self <;> rfl) rfl rfl rfl rfl (by cases self <;> rfl) rfl rfl rfl rfl
      (dhi self) (by simp only [Heap.len,MObj.elems_dyn];decide)
      (by simp only [Heap.len,Heap.get,Objs.get,hp,fresh,MObj.elems_dyn,List.getElem_cons_succ,List.getElem_cons_zero];decide)
      (by intro t ht hn;exact hn)
      SH source_memOK initial_repr
    simp only [srcElems,List.getElem_cons_succ,List.getElem_cons_zero] at result
    obtain ⟨mid,out,ym,z,mm,target,hw₁,selected,hw₂,stmt₁,stmt₂,items,native,word₁,word₂,word,hr₁,hr₂,mok₁,mok₂,repr₁,repr₂,locals₁,locals₂,parent,child,other,write,addrs,next,effects,stack,alloc,mmEq,targetEq,midAddrs⟩ := result
    have known₁ : hp.writeAddr (.index (dref self) .dyn (indexValue ⟨0,by decide⟩)) right=some (postHeap self) := by
      simp only [Heap.writeAddr,Heap.setIndex,indexValue,Int.toNat_natCast,show 0<(MObj.elems .dyn (hp.get (dref self))).length from dhi self,↓reduceIte]
      rfl
    have midEq : mid=postHeap self := Option.some.inj (hw₁.symm.trans known₁)
    subst mid
    have known₂ : (postHeap self).writeAddr (.index right .dyn (indexValue ⟨1,by decide⟩)) false=some (deletedHeap self) := by
      cases self <;> simp only [Heap.writeAddr,Heap.setIndex,postHeap,dref,Bool.false_eq_true,if_false,if_true,indexValue,Int.toNat_natCast,
        Heap.get,Objs.get,Heap.set,Objs.set,hp,old,fresh,right,MObj.elems_dyn,MObj.setElem_dyn,deletedHeap] <;> rfl
    have outEq : out=deletedHeap self := Option.some.inj (hw₂.symm.trans known₂)
    subst out
    subst mm
    subst target
    have midTables := source_tables self ym hr₁ midAddrs
    have leftTable : z.2.heap.get 0=sy.2.heap.get 0 := addrs 0 (by cases self <;> decide) (by decide)
    have rightMember : right∈MObj.elems .dyn ((deletedHeap self).get (dref self)) := by
      rw [parent]
      exact List.mem_set (dhi self) right
    have rightAt := hr₂.children right rightMember
    have leftAt : SourceBoolMemoryAt z 0 (deletedHeap self) left .dyn := by
      change z.2.heap.get 0=some ⟨SB,sourceBoolMemory _⟩
      rw [leftTable]
      cases self <;> simp only [deletedHeap,postHeap,dref,Bool.false_eq_true,if_false,if_true,Heap.get,Objs.get,Heap.set,Objs.set,hp,old,fresh,right,left,MObj.elems_dyn,MObj.setElem_dyn] <;> simpa only [SourceBoolMemoryAt,MObj.elems_dyn] using left_at
    have finalTables : sourceViews z=deletedSource self := by
      have hparent := hr₂.parent
      have hr := rightAt
      unfold SourceBoolMemoryAt at hr
      cases self
      all_goals
        simp only [deletedHeap,postHeap,dref,daddr,addresses,Bool.false_eq_true,if_false,if_true,Heap.get,Objs.get,Heap.set,Objs.set,hp,old,fresh,right,MObj.elems_dyn,MObj.setElem_dyn,List.set_cons_zero,List.set_cons_succ] at hparent hr
        unfold sourceViews deletedSource
        simp only [Bool.false_eq_true,if_false,if_true]
        rw [leftTable,hparent,hr,addrs 4 (by decide) (by decide)]
      · rw [addrs 3 (by decide) (by decide)];rfl
      · rw [addrs 2 (by decide) (by decide)];rfl
    refine ⟨ym,z,stmt₁,stmt₂,items,native,word₁,word₂,word,rfl,midTables,finalTables,hr₂,leftAt,rightAt,mok₂,repr₂,locals₁,locals₂,next,?_,effects,?_,rfl⟩
    · rw [addrs 5 (by cases self <;> decide) (by decide)];rfl
    · apply alloc ⟨48,by decide⟩ (by decide) allocator
      cases self <;> simp only [dref,Bool.false_eq_true,if_false,if_true,Heap.len,Heap.get,Objs.get,hp,old,fresh,MObj.elems_dyn,base] <;> decide

/-- Complete INITIAL, pointer-replaced, and child-cleared word/native tables;
free pointer, all root/scalar locals, guard, headers, payloads and empty parent
are retained. Deleting without rebinding or omitting deletion is discriminated. -/
theorem complete_reference_delete_vectors (self : Bool) :
    words machine=[w[48],w[32],w[32],w[36],w[1],w[0],w[0],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[1],w[16],w[3],w[16],w[24],w[16],w[0],w[0]] ∧
    words (postWord self)=[w[48],w[32],w[32],w[36],w[1],w[0],w[0],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[1],(if self then w[16] else w[24]),w[3],(if self then w[24] else w[16]),w[24],w[16],w[0],w[0]] ∧
    words (deletedWord self)=[w[48],w[32],w[32],w[36],w[1],w[0],w[0],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[0],w[0],w[1],(if self then w[16] else w[24]),w[3],(if self then w[24] else w[16]),w[24],w[16],w[0],w[0]] ∧
    views hp=([true,false,false],[false,true,false],[0],[0,1,0],[]) ∧
    views (postHeap self)=([true,false,false],[false,true,false],(if self then [0] else [1]),(if self then [1,1,0] else [0,1,0]),[]) ∧
    views (deletedHeap self)=([true,false,false],[false,false,false],(if self then [0] else [1]),(if self then [1,1,0] else [0,1,0]),[]) ∧
    (deletedWord self).mem 0=w[48] ∧ (deletedWord self).stack=[w[42]] ∧
    words (deletedWord self)≠words (postWord self) ∧
    words (deletedWord self)≠words (writeMachine machine 18 (w[0])) := by
  first
  | solve | rfl | simp only [] | omega
  | cases self <;> simp only [Bool.false_eq_true,if_false,if_true]
    all_goals
      refine ⟨rfl,rfl,rfl,?_,?_,?_,rfl,rfl,by decide,by decide⟩
      · simp only [views,Heap.get,Objs.get,hp,left,right,old,fresh,empty,MObj.elems_dyn,List.map_cons,List.map_nil]
      · simp only [views,postHeap,dref,Bool.false_eq_true,if_false,if_true,Heap.set,Objs.set,Heap.get,Objs.get,hp,left,right,old,fresh,empty,MObj.elems_dyn,MObj.setElem_dyn,List.map_cons,List.map_nil];rfl
      · simp only [views,deletedHeap,postHeap,dref,Bool.false_eq_true,if_false,if_true,Heap.set,Objs.set,Heap.get,Objs.get,hp,left,right,old,fresh,empty,MObj.elems_dyn,MObj.setElem_dyn,List.map_cons,List.map_nil];rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.computed_reference_delete_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms computed_reference_delete_client
/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.complete_reference_delete_vectors' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms complete_reference_delete_vectors

private abbrev BoundΓ : Ctx := .val .uint :: Γ
private abbrev BoundSΓ : Source.RCtx := .int .u256 :: SΓ
private def boundState : State C BoundΓ := σ.push (t := .val .uint) (uintOfNat 3)
private def boundSource : Source.EMState E0 BoundSΓ := (.cons (sourceUint (uintOfNat 3)) sy.1,sy.2)
private def boundWord := writeMachine machine 6 w[3]
private def boundFrag := frag.push (.val .uint) .ok
private def boundPostWord := writeMachine boundWord 33 w[24]
private def boundSourceViews (y : Source.EMState E0 BoundSΓ) :=
  [y.2.heap.get 0,y.2.heap.get 1,y.2.heap.get 2,y.2.heap.get 3,y.2.heap.get 4]
private def boundarySource (inner : Bool) : Source.Idx BoundSΓ (.int .u256) :=
  if inner then .there sj else .there si
private def boundaryNative (inner : Bool) : Idx BoundΓ (.val .uint) :=
  if inner then .there ti else .there tj
private theorem boundSourceOK : Source.MemOK E0 SH boundSource :=
  ⟨⟨source_memOK.1.1,⟨trivial,source_memOK.1.2⟩⟩,source_memOK.2⟩
private theorem boundOld : SourceBoolRefsAt boundSource 2 hp old addresses :=
  ⟨old_at.parent,old_at.children⟩
private theorem boundFresh : SourceBoolRefsAt boundSource 3 hp fresh addresses :=
  ⟨fresh_at.parent,fresh_at.children⟩
private theorem boundRepr : RefArrayStateRepr 1 1 8 boundFrag boundState base boundWord :=
  ⟨initial_repr.state.consVal (uintOfNat 3) w[3] (ReprV.uint_of rfl) (by decide),
    initial_repr.arrays.localWrite 6 (by decide) w[3]⟩
private theorem boundAllocator : StructAllocatorRepr hp base 8 ⟨48,by decide⟩ boundWord :=
  allocator.localWrite 6 (by decide) (by decide) w[3]

/-- Both declared pipelines execute a materially changed replacement, THEN
reject either parent endpoint1 or reached RIGHT-child endpoint3. The new scalar
local is independently represented, not a declaration-execution claim. No target
post-revert machine/heap or transaction rollback is asserted. -/
theorem computed_reference_reject_client (p : Roadmap.Pipeline) (fuel : Nat) (inner : Bool) :
    ∃ ym : Source.EMState E0 BoundSΓ,
      (Source.execS (G0 p) F0 (fuel+6) BoundSΓ.length none
        (.expr (sourceReferenceReadAssign (.there sdst) (.there ssrc) (.there sj) (.there si)) :
          Source.RStmt E0 [] false .body BoundSΓ BoundSΓ) boundSource.1).run (.nil,boundSource.2)=
            (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.evalE (G0 p) F0 (fuel+4)
        (sourceNestedDelete (.there sdst) (boundarySource inner) .here)).run ym=
          (.error (.revert (Source.panicData .index)),ym) ∧
      (Source.execItems (G0 p) F0 (fuel+7) BoundSΓ.length none
        (.stmt (.expr (sourceReferenceReadAssign (.there sdst) (.there ssrc) (.there sj) (.there si)))
          (.stmt (.expr (sourceNestedDelete (.there sdst) (boundarySource inner) .here)) .nil) :
            Source.RItems E0 [] false .body BoundSΓ BoundSΓ) boundSource.1).run (.nil,boundSource.2)=
              (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      Stmt.run boundState (referenceReadStmt (.there tdst) (.there tsrc) (.there ti) (.there tj))=
        .ok ⟨boundState.withHeap (postHeap false),List.prefix_refl _⟩ ∧
      Stmt.run (boundState.withHeap (postHeap false))
        (nestedDeleteStmt (.there tdst) (boundaryNative inner) .here)=.error .revert ∧
      Prog.run boundState (.cons (referenceReadStmt (.there tdst) (.there tsrc) (.there ti) (.there tj))
        (.cons (nestedDeleteStmt (.there tdst) (boundaryNative inner) .here) .nil))=.error .revert ∧
      run (referenceReadWriteCode (C := C) (Δ := BoundΓ) 1 (.there tdst) (.there tsrc) (.there ti) (.there tj)) boundWord=
        .ok boundPostWord 0 ∧
      run (nestedDeleteCode (C := C) (Γ := BoundΓ) 1 (.there tdst) (boundaryNative inner) .here) boundPostWord=.revert ∧
      run (referenceReadWriteCode (C := C) (Δ := BoundΓ) 1 (.there tdst) (.there tsrc) (.there ti) (.there tj) ++
        nestedDeleteCode (C := C) (Γ := BoundΓ) 1 (.there tdst) (boundaryNative inner) .here) boundWord=.revert ∧
      boundSourceViews ym=expectedSource false ∧
      SourceBoolRefsAt ym 2 (postHeap false) old addresses ∧
      SourceBoolMemoryAt ym 0 (postHeap false) left .dyn ∧
      SourceBoolMemoryAt ym 1 (postHeap false) right .dyn ∧ Source.MemOK E0 SH ym ∧
      RefArrayStateRepr 1 1 8 boundFrag (boundState.withHeap (postHeap false)) base boundPostWord ∧
      (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local (.there sdst)) (.local (.there sj)) rfl)).run boundSource=
        (.ok (.val (.memRef rfl 0)),boundSource) ∧
      (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local (.there sdst)) (.local (.there sj)) rfl)).run ym=
        (.ok (.val (.memRef rfl 1)),ym) ∧
      (Source.readLoc (E := E0) (Γ := BoundSΓ) F0 (τ := .bool) (.mem 0 0)).run ym=(.ok (.bool true),ym) ∧
      ym.1=boundSource.1 ∧ ym.2.heap.next=5 ∧ ym.2.heap.get 5=none ∧
      (ym.2.ex=boundSource.2.ex ∧ ym.2.events=boundSource.2.events ∧
        ym.2.logs=boundSource.2.logs ∧ ym.2.fnLocals=boundSource.2.fnLocals) ∧
      StructAllocatorRepr (postHeap false) base 8 ⟨48,by decide⟩ boundPostWord ∧
      boundPostWord.stack=[w[42]] := by
  first
  | solve | rfl | simp only [] | omega
  | have result := boundOld.computed_reference_delete_reject (G0 p) F0 fuel boundSource boundState old fresh 2 3 addresses boundFresh
      (.there sdst) (.there ssrc) (.there sj) (.there si) (boundarySource inner) .here
      (.there tdst) (.there tsrc) (.there ti) (.there tj) (boundaryNative inner) .here
      ⟨0,by decide⟩ ⟨1,by decide⟩ (if inner then ⟨0,by decide⟩ else ⟨1,by decide⟩) ⟨3,by decide⟩
      rfl rfl rfl rfl (by cases inner <;> rfl) rfl rfl rfl rfl rfl (by cases inner <;> rfl) rfl
      (by simp only [Heap.len,MObj.elems_dyn];decide) (by simp only [Heap.len,MObj.elems_dyn];decide)
      (by cases inner
          · exact Or.inl (by simp only [Heap.len,MObj.elems_dyn];decide)
          · exact Or.inr ⟨rfl,by simp only [Heap.len,MObj.elems_dyn];decide⟩)
      SH boundSourceOK boundRepr
    have srcElems : MObj.elems .dyn (boundState.heap.get fresh)=[left,right,left] := by rw [MObj.elems_dyn];rfl
    simp only [srcElems,List.getElem_cons_succ,List.getElem_cons_zero] at result
    obtain ⟨mid,ym,mm,hw,selected,stmt,failed,failedStmt,items,native,badNative,badProg,word,badWord,badAppend,
      hr,child,mok,represented,locals,elems,children,addrs,next,effects,stack,alloc,mmEq⟩ := result
    have known : hp.writeAddr (.index old .dyn (indexValue ⟨0,by decide⟩)) right=some (postHeap false) := by
      simp only [Heap.writeAddr,Heap.setIndex,indexValue,Int.toNat_natCast,show 0<(MObj.elems .dyn (hp.get old)).length from dhi false,↓reduceIte]
      rfl
    have midEq : mid=postHeap false := Option.some.inj (hw.symm.trans known)
    subst mid
    subst mm
    have tables : boundSourceViews ym=expectedSource false := by
      have parent := hr.parent
      have pe := post_elems false
      change MObj.elems .dyn ((postHeap false).get old)=[right] at pe
      rw [pe] at parent
      change ym.2.heap.get 2=some ⟨SR,pdata [right]⟩ at parent
      unfold boundSourceViews expectedSource
      simp only [Bool.false_eq_true,if_false]
      rw [parent,addrs 0 (by decide),addrs 1 (by decide),addrs 3 (by decide),addrs 4 (by decide)]
      rfl
    have leftAt : SourceBoolMemoryAt ym 0 (postHeap false) left .dyn := by
      unfold SourceBoolMemoryAt
      rw [addrs 0 (by decide),children left]
      exact left_at
    have initialRead := boundOld.eval_parent_read (G0 p) F0 fuel (.there sdst) (.there sj) (uintOfNat 0) left rfl rfl
      (by simp only [Heap.index,MObj.elems_dyn];rfl)
    have reachedRead := hr.eval_parent_read (G0 p) F0 fuel (.there sdst) (.there sj) (uintOfNat 0) right
      (by rw [locals];rfl) (by rw [locals];rfl) selected
    have leftRead := source_bool_read ym 0 _ leftAt 0 (by rw [children left];simp only [MObj.elems_dyn];decide)
    refine ⟨ym,stmt,failed,items,native,badNative,badProg,word,badWord,badAppend,tables,hr,leftAt,child,mok,represented,
      initialRead,reachedRead,?_,locals,next,?_,effects,?_,rfl⟩
    · simpa only [children left,MObj.elems_dyn] using leftRead
    · rw [addrs 5 (by decide)];rfl
    · exact alloc ⟨48,by decide⟩ boundAllocator (by simp only [Heap.len,MObj.elems_dyn];decide)

/-- ALL INITIAL and retained-prefix objects/words, including new scalar cell6,
all root aliases, headers/children, empty object, free pointer and saved stack.
These are prefix observations, never a returned post-revert machine. -/
theorem complete_reference_rejection_vectors :
    boundSourceViews boundSource=[some ⟨SB,sourceBoolMemory [true,false,false]⟩,
      some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SR,pdata [left]⟩,
      some ⟨SR,pdata [left,right,left]⟩,some ⟨SR,pdata []⟩] ∧
    words boundWord=[w[48],w[32],w[32],w[36],w[1],w[0],w[3],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[1],w[16],w[3],w[16],w[24],w[16],w[0],w[0]] ∧
    words boundPostWord=[w[48],w[32],w[32],w[36],w[1],w[0],w[3],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[1],w[24],w[3],w[16],w[24],w[16],w[0],w[0]] ∧
    views hp=([true,false,false],[false,true,false],[0],[0,1,0],[]) ∧
    views (postHeap false)=([true,false,false],[false,true,false],[1],[0,1,0],[]) ∧
    boundPostWord.mem 0=w[48] ∧ boundPostWord.stack=[w[42]] ∧
    words boundPostWord≠words boundWord := by
  first
  | solve | rfl | simp only [] | omega
  | refine ⟨rfl,rfl,rfl,?_,?_,rfl,rfl,by decide⟩
    · simp only [views,Heap.get,Objs.get,hp,left,right,old,fresh,empty,MObj.elems_dyn,List.map_cons,List.map_nil]
    · simp only [views,postHeap,dref,Bool.false_eq_true,if_false,Heap.get,Objs.get,Heap.set,Objs.set,hp,left,right,old,fresh,empty,MObj.elems_dyn,MObj.setElem_dyn,List.map_cons,List.map_nil];rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.computed_reference_reject_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms computed_reference_reject_client
/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.complete_reference_rejection_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_reference_rejection_vectors

private abbrev AliasΓ : Ctx := .mem B :: Γ
private abbrev AliasSΓ : Source.RCtx := SB :: SΓ
private def aliasState : State C AliasΓ := σ.push (t := .mem B) (some left)
private def aliasSource : Source.EMState E0 AliasSΓ := (.cons (.memRef rfl 0) sy.1,sy.2)
private def aliasWord := writeMachine machine 6 w[16]
private def aliasFrag := frag.push (.mem B) .ok
private def aliasMidWord (self : Bool) := writeMachine aliasWord ((base (dref self).id).val+1) w[24]
private def aliasFinalWord (self : Bool) := writeMachine (aliasMidWord self) 6 w[24]
private def aliasFinalState (self : Bool) := (aliasState.withHeap (postHeap self)).setLocal (.here : Idx AliasΓ (.mem B)) (some right)
private def aliasViews (y : Source.EMState E0 AliasSΓ) :=
  [y.2.heap.get 0,y.2.heap.get 1,y.2.heap.get 2,y.2.heap.get 3,y.2.heap.get 4]
private theorem aliasSourceOK : Source.MemOK E0 SH aliasSource :=
  ⟨⟨source_memOK.1.1,⟨⟨SB,rfl,rfl⟩,source_memOK.1.2⟩⟩,source_memOK.2⟩
private theorem aliasAt (self : Bool) : SourceBoolRefsAt aliasSource (daddr self) hp (dref self) addresses :=
  ⟨(dat self).parent,(dat self).children⟩
private theorem aliasFresh : SourceBoolRefsAt aliasSource 3 hp fresh addresses :=
  ⟨fresh_at.parent,fresh_at.children⟩
private theorem aliasRepr : RefArrayStateRepr 1 1 8 aliasFrag aliasState base aliasWord :=
  ⟨initial_repr.state.consMem left (by decide),initial_repr.arrays.localWrite 6 (by decide) w[16]⟩
private theorem aliasAllocator : StructAllocatorRepr hp base 8 ⟨48,by decide⟩ aliasWord :=
  allocator.localWrite 6 (by decide) (by decide) w[16]

/-- Application of the EXISTING Source read/index operations to a primitive
local. The value premise is an actual typed heap lookup, not a source-run or
preservation premise; this private helper is used on independently inhabited
initial and genuinely reached child observers below. -/
private theorem alias_bool_read {Γ : Source.RCtx} (y : Source.EMState E0 Γ)
    (hp : Heap H) (q : HRef H B) (a : Nat) (hr : SourceBoolMemoryAt y a hp q .dyn)
    (p : Roadmap.Pipeline) (fuel : Nat) (root : Source.Idx Γ SB) (idx : Source.Idx Γ (.int .u256))
    (hroot : y.1.get root=.memRef rfl a) (hindex : y.1.get idx=sourceUint (uintOfNat 0))
    (v : Bool) (hv : hp.index q .dyn (uintOfNat 0)=some v) :
    (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local root) (.local idx) rfl)).run y=(.ok (.val (.bool v)),y) := by
  first
  | solve | rfl | simp only [] | omega
  | have hk : 0<hp.len q .dyn := (List.getElem?_eq_some_iff.mp hv).1
    have read := (hr.read_iff F0 (uintOfNat 0) v).mpr hv
    have zero : (uintOfNat 0).val.toNat=0 := by rw [uintOfNat_val (by decide : 0<2^256)];rfl
    simp only [zero] at read
    rw [Source.evalE,Source.Hoare.run_bind,source_local_value_run (G0 p) F0 fuel y root _ hroot]
    change ((Source.evalE (G0 p) F0 (fuel+1) (.local idx)) >>= fun val => Source.indexNat val >>= fun k =>
      Source.indexLoc F0 (.memRef rfl a : Source.Val E0.layout SB) k >>= fun loc =>
        Source.readLoc F0 loc >>= fun val => pure (Source.RVal.val val)).run y=_
    rw [Source.Hoare.run_bind,source_local_value_run (G0 p) F0 fuel y idx _ hindex]
    change (Source.indexLoc F0 (.memRef rfl a : Source.Val E0.layout SB) 0 >>= fun loc =>
      Source.readLoc F0 loc >>= fun val => pure (Source.RVal.val val)).run y=_
    rw [Source.Hoare.run_bind,hr.indexLoc_run F0 0 hk]
    change (Source.readLoc F0 (τ := .bool) (.mem a 0) >>= fun val => pure (Source.RVal.val val)).run y=_
    rw [Source.Hoare.run_bind,read]
    rfl

/-- Computed RHS installs RIGHT; selecting the reached slot rebinds an actual
LEFT local to RIGHT. Both pipelines and distinct/same parent cases execute one
Source Items/native Prog/whole word append. Actual read expressions distinguish
old LEFT true from new RIGHT false; the extra target read pushes its value. -/
theorem computed_reference_alias_client (p : Roadmap.Pipeline) (fuel : Nat) (self : Bool) :
    ∃ (ym z : Source.EMState E0 AliasSΓ),
      (Source.execS (G0 p) F0 (fuel+5) AliasSΓ.length none
        (.expr (sourceReferenceReadAssign (.there (ds self)) (.there ssrc) (.there sj) (.there si)) :
          Source.RStmt E0 [] false .body AliasSΓ AliasSΓ) aliasSource.1).run (.nil,aliasSource.2)=
            (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execItems (G0 p) F0 (fuel+6) AliasSΓ.length none
        (.stmt (.expr (sourceReferenceReadAssign (.there (ds self)) (.there ssrc) (.there sj) (.there si))) .nil :
          Source.RItems E0 [] false .body AliasSΓ AliasSΓ) aliasSource.1).run (.nil,aliasSource.2)=
            (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS (G0 p) F0 (fuel+4) AliasSΓ.length none
        (.expr (sourceSelectedAlias .here (.there (ds self)) (.there sj)) :
          Source.RStmt E0 [] false .body AliasSΓ AliasSΓ) ym.1).run (.nil,ym.2)=
            (.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems (G0 p) F0 (fuel+6) AliasSΓ.length none
        (.stmt (.expr (sourceReferenceReadAssign (.there (ds self)) (.there ssrc) (.there sj) (.there si)))
          (.stmt (.expr (sourceSelectedAlias .here (.there (ds self)) (.there sj))) .nil) :
            Source.RItems E0 [] false .body AliasSΓ AliasSΓ) aliasSource.1).run (.nil,aliasSource.2)=
              (.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run aliasState (.cons (referenceReadStmt (.there (dt self)) (.there tsrc) (.there ti) (.there tj))
        (.cons (.rebindMem .here (.alias (.loc (.index .dyn (.var (.there (dt self)) rfl) (.simple (.local (.there ti))))))) .nil))=
          .ok ⟨aliasFinalState self,List.prefix_refl _⟩ ∧
      run (referenceReadWriteCode (C := C) (Δ := AliasΓ) 1 (.there (dt self)) (.there tsrc) (.there ti) (.there tj)) aliasWord=
        .ok (aliasMidWord self) 0 ∧
      run (selectedAliasCode (C := C) (Γ := AliasΓ) 1 .here (.there (dt self)) (.there ti)) (aliasMidWord self)=
        .ok (aliasFinalWord self) 0 ∧
      run (referenceReadWriteCode (C := C) (Δ := AliasΓ) 1 (.there (dt self)) (.there tsrc) (.there ti) (.there tj) ++
        selectedAliasCode (C := C) (Γ := AliasΓ) 1 .here (.there (dt self)) (.there ti)) aliasWord=.ok (aliasFinalWord self) 0 ∧
      aliasViews ym=expectedSource self ∧ aliasViews z=expectedSource self ∧
      SourceBoolRefsAt z (daddr self) (postHeap self) (dref self) addresses ∧
      SourceBoolMemoryAt z 0 (postHeap self) left .dyn ∧ SourceBoolMemoryAt z 1 (postHeap self) right .dyn ∧
      Source.MemOK E0 SH z ∧ RefArrayStateRepr 1 1 8 aliasFrag (aliasFinalState self) base (aliasFinalWord self) ∧
      ym.1=aliasSource.1 ∧ z.1=aliasSource.1.set .here (.memRef rfl 1) ∧ z.2=ym.2 ∧
      z.1.get .here=.memRef rfl 1 ∧ TEnv.get (.here : Idx AliasΓ (.mem B)) (aliasFinalState self).env=some right ∧
      (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local (.here : Source.Idx AliasSΓ SB)) (.local (.there sj)) rfl)).run aliasSource=
        (.ok (.val (.bool true)),aliasSource) ∧
      (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local (.here : Source.Idx AliasSΓ SB)) (.local (.there sj)) rfl)).run ym=
        (.ok (.val (.bool true)),ym) ∧
      (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local (.here : Source.Idx AliasSΓ SB)) (.local (.there sj)) rfl)).run z=
        (.ok (.val (.bool false)),z) ∧
      (Source.readLoc (E := E0) (Γ := AliasSΓ) F0 (τ := .bool) (.mem 0 0)).run z=(.ok (.bool true),z) ∧
      (Val.readMem (.index .dyn (.var (.here : Idx AliasΓ (.mem B)) rfl)
        (.simple (.local (.there ti)))) : Val C AliasΓ .bool).evalT (aliasFinalState self)=.ok false ∧
      run (readLocalCode (C := C) 1 (.here : Idx AliasΓ (.mem B)) (.simple (.local (.there ti)))) (aliasFinalWord self)=
        .ok ((aliasFinalWord self).push w[0]) 0 ∧
      z.2.heap.next=5 ∧ z.2.heap.get 5=none ∧
      (z.2.ex=aliasSource.2.ex ∧ z.2.events=aliasSource.2.events ∧ z.2.logs=aliasSource.2.logs ∧ z.2.fnLocals=aliasSource.2.fnLocals) ∧
      StructAllocatorRepr (postHeap self) base 8 ⟨48,by decide⟩ (aliasFinalWord self) ∧
      (aliasFinalWord self).stack=[w[42]] := by
  first
  | solve | rfl | simp only [] | omega
  | have result := (aliasAt self).computed_reference_alias_sequence (G0 p) F0 fuel aliasSource aliasState (dref self) fresh
      (daddr self) 3 addresses aliasFresh (.there (ds self)) (.there ssrc) (.there sj) (.there si) .here
      (.there (dt self)) (.there tsrc) (.there ti) (.there tj) .here ⟨0,by decide⟩ ⟨1,by decide⟩
      (by cases self <;> rfl) rfl rfl rfl (by cases self <;> rfl) rfl rfl rfl (dhi self)
      (by simp only [Heap.len,MObj.elems_dyn];decide) SH aliasSourceOK aliasRepr
    have srcElems : MObj.elems .dyn (aliasState.heap.get fresh)=[left,right,left] := by rw [MObj.elems_dyn];rfl
    simp only [srcElems,List.getElem_cons_succ,List.getElem_cons_zero] at result
    obtain ⟨mid,ym,outputs⟩ := result
    obtain ⟨hw,selected,stmt₁,expr₂,stmt₂,items,native₁,native₂,native,word₁,word₂,word,hr₁,hr₂,child,
      mok₁,mok₂,repr₁,repr₂,locals₁,locals₂,sourceAlias,nativeAlias,heap,globals,elems,children,sourceChildren,
      addrs,next,effects,stack,alloc⟩ := outputs
    have known : hp.writeAddr (.index (dref self) .dyn (indexValue ⟨0,by decide⟩)) right=some (postHeap self) := by
      simp only [Heap.writeAddr,Heap.setIndex,indexValue,Int.toNat_natCast,show 0<(MObj.elems .dyn (hp.get (dref self))).length from dhi self,↓reduceIte]
      rfl
    have midEq : mid=postHeap self := Option.some.inj (hw.symm.trans known)
    subst mid
    simp only [MObj.elems_dyn] at nativeAlias native native₂ repr₂ expr₂ stmt₂ items word₂ word locals₂ sourceAlias child
    let z : Source.EMState E0 AliasSΓ := (ym.1.set .here (.memRef rfl 1),ym.2)
    change ∀ q : HRef H B,(postHeap self).get q=hp.get q at children
    change TEnv.get (.here : Idx AliasΓ (.mem B)) (aliasFinalState self).env=some right at nativeAlias
    change z.1=aliasSource.1.set .here (.memRef rfl 1) at locals₂
    change SourceBoolMemoryAt z 1 (postHeap self) right .dyn at child
    have finalRepr : RefArrayStateRepr 1 1 8 aliasFrag (aliasFinalState self) base (aliasFinalWord self) := repr₂
    have tables : aliasViews ym=expectedSource self := by
      have parent := hr₁.parent
      rw [post_elems] at parent
      cases self
      · change ym.2.heap.get 2=some ⟨SR,pdata [right]⟩ at parent
        unfold aliasViews expectedSource
        rw [parent,addrs 0 (by decide),addrs 1 (by decide),addrs 3 (by decide),addrs 4 (by decide)];rfl
      · change ym.2.heap.get 3=some ⟨SR,pdata [right,right,left]⟩ at parent
        unfold aliasViews expectedSource
        rw [parent,addrs 0 (by decide),addrs 1 (by decide),addrs 2 (by decide),addrs 4 (by decide)];rfl
    have leftAt : SourceBoolMemoryAt z 0 (postHeap self) left .dyn := sourceChildren left left_at
    have initialRead := alias_bool_read aliasSource hp left 0 left_at p fuel .here (.there sj) rfl rfl true
      (by simp only [Heap.index,MObj.elems_dyn];rfl)
    have rightRead : (postHeap self).index right .dyn (uintOfNat 0)=some false := by
      simp only [Heap.index,children right,MObj.elems_dyn];rfl
    have midRead := alias_bool_read ym (postHeap self) left 0 leftAt p fuel .here (.there sj)
      (by rw [locals₁];rfl) (by rw [locals₁];rfl) true
      (by simp only [Heap.index,children left,MObj.elems_dyn];rfl)
    have omittedItems := source_items_cons_run (G0 p) F0 (fuel+5) AliasSΓ.length
      (.expr (sourceReferenceReadAssign (.there (ds self)) (.there ssrc) (.there sj) (.there si))) .nil
      aliasSource ym ym stmt₁ (by rfl)
    have finalRead := alias_bool_read z (postHeap self) right 1 child p fuel .here (.there sj) sourceAlias
      (by rw [locals₂];rfl) false rightRead
    have leftRead := (leftAt.read_iff F0 (uintOfNat 0) true).mpr (by simp only [Heap.index,children left,MObj.elems_dyn];rfl)
    have finalLookup : (aliasFinalState self).heap.index right .dyn (uintOfNat 0)=some false := rightRead
    have nativeRead : (Val.readMem (.index .dyn (.var (.here : Idx AliasΓ (.mem B)) rfl)
        (.simple (.local (.there ti)))) : Val C AliasΓ .bool).evalT (aliasFinalState self)=.ok false := by
      simp only [Val.evalT,MLoc.addrT,MPath.mvalT,Simple.evalT,nativeAlias,
        show TEnv.get (.there ti) (aliasFinalState self).env=uintOfNat 0 from rfl,
        Heap.readAddr,finalLookup,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have readCode : ValOutT .bool
        ((Val.readMem (.index .dyn (.var (.here : Idx AliasΓ (.mem B)) rfl)
          (.simple (.local (.there ti)))) : Val C AliasΓ .bool).evalT (aliasFinalState self))
        (run (readLocalCode (C := C) 1 (.here : Idx AliasΓ (.mem B)) (.simple (.local (.there ti)))) (aliasFinalWord self))
        (aliasFinalWord self) :=
      readLocal_correct finalRepr.state (.here : Idx AliasΓ (.mem B)) (.simple (.local (.there ti))) rfl
    rw [nativeRead] at readCode
    have actualRead : run (readLocalCode (C := C) 1 (.here : Idx AliasΓ (.mem B)) (.simple (.local (.there ti))))
        (aliasFinalWord self)=.ok ((aliasFinalWord self).push w[0]) 0 := by
      rcases readCode with ⟨v,w,eq,rep,run⟩|⟨bad,_⟩
      · cases Except.ok.inj eq
        rw [rep.bool_inv] at run
        exact run
      · cases bad
    refine ⟨ym,z,stmt₁,omittedItems,stmt₂,items,native,word₁,word₂,word,tables,tables,hr₂,leftAt,child,mok₂,repr₂,
      locals₁,locals₂,rfl,sourceAlias,nativeAlias,initialRead,midRead,finalRead,leftRead,nativeRead,actualRead,next,?_,effects,?_,rfl⟩
    · rw [addrs 5 (by cases self <;> decide)];rfl
    · apply alloc ⟨48,by decide⟩ (by decide) aliasAllocator
      cases self <;> simp only [dref,Bool.false_eq_true,if_false,if_true,Heap.len,MObj.elems_dyn,base] <;> decide

/-- Complete INITIAL, replaced-parent and rebound-local vectors. The old
selected object and all shared/repeated references are retained; only the
parent's selected slot and alias local change. Negatives distinguish omitted
selection and selection before replacement at the word-vector scope. -/
theorem complete_reference_alias_vectors (self : Bool) :
    aliasViews aliasSource=[some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,
      some ⟨SR,pdata [left]⟩,some ⟨SR,pdata [left,right,left]⟩,some ⟨SR,pdata []⟩] ∧
    words aliasWord=[w[48],w[32],w[32],w[36],w[1],w[0],w[16],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[1],w[16],w[3],w[16],w[24],w[16],w[0],w[0]] ∧
    words (aliasMidWord self)=[w[48],w[32],w[32],w[36],w[1],w[0],w[16],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[1],(if self then w[16] else w[24]),w[3],(if self then w[24] else w[16]),w[24],w[16],w[0],w[0]] ∧
    words (aliasFinalWord self)=[w[48],w[32],w[32],w[36],w[1],w[0],w[24],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[1],(if self then w[16] else w[24]),w[3],(if self then w[24] else w[16]),w[24],w[16],w[0],w[0]] ∧
    views hp=([true,false,false],[false,true,false],[0],[0,1,0],[]) ∧
    views (postHeap self)=([true,false,false],[false,true,false],(if self then [0] else [1]),(if self then [1,1,0] else [0,1,0]),[]) ∧
    (aliasFinalState self).heap=postHeap self ∧ (aliasFinalWord self).stack=[w[42]] ∧
    words (aliasFinalWord self)≠words (aliasMidWord self) ∧ words (aliasFinalWord self)≠words aliasWord := by
  first
  | solve | rfl | simp only [] | omega
  | cases self <;> simp only [Bool.false_eq_true,if_false,if_true]
    all_goals
      refine ⟨rfl,rfl,rfl,rfl,?_,?_,rfl,rfl,by decide,by decide⟩
      · simp only [views,Heap.get,Objs.get,hp,left,right,old,fresh,empty,MObj.elems_dyn,List.map_cons,List.map_nil]
      · simp only [views,postHeap,dref,Bool.false_eq_true,if_false,if_true,Heap.get,Objs.get,Heap.set,Objs.set,hp,left,right,old,fresh,empty,MObj.elems_dyn,MObj.setElem_dyn,List.map_cons,List.map_nil];rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.computed_reference_alias_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms computed_reference_alias_client
/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.complete_reference_alias_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_reference_alias_vectors

private def aliasDeletedState (self : Bool) := (aliasFinalState self).withHeap (deletedHeap self)
private def aliasDeletedWord (self : Bool) := writeMachine (aliasFinalWord self) 26 w[0]

/-- THREE actual Source/native statements and whole target append. The computed
RIGHT pointer passes through a local before deletion; RIGHT[1] changes true to
false while old LEFT and shared parent references remain. Both pipeline orders
and both distinct/same parent cases are inhabited. Reads following the program
are separate expressions, not a fourth compiled statement. -/
theorem computed_alias_delete_client (p : Roadmap.Pipeline) (fuel : Nat) (self : Bool) :
    ∃ (ym z : Source.EMState E0 AliasSΓ),
    let ya : Source.EMState E0 AliasSΓ := (ym.1.set .here (.memRef rfl 1),ym.2);
      (Source.execS (G0 p) F0 (fuel+6) AliasSΓ.length none
        (.expr (sourceReferenceReadAssign (.there (ds self)) (.there ssrc) (.there sj) (.there si)) :
          Source.RStmt E0 [] false .body AliasSΓ AliasSΓ) aliasSource.1).run (.nil,aliasSource.2)=
            (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS (G0 p) F0 (fuel+5) AliasSΓ.length none
        (.expr (sourceSelectedAlias .here (.there (ds self)) (.there sj)) :
          Source.RStmt E0 [] false .body AliasSΓ AliasSΓ) ym.1).run (.nil,ym.2)=(.ok (.normal ya.1),(.nil,ya.2)) ∧
      (Source.execS (G0 p) F0 (fuel+4) AliasSΓ.length none
        (.expr (sourceIndexedDelete .here (.there si)) : Source.RStmt E0 [] false .body AliasSΓ AliasSΓ)
        ya.1).run (.nil,ya.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems (G0 p) F0 (fuel+7) AliasSΓ.length none
        (.stmt (.expr (sourceReferenceReadAssign (.there (ds self)) (.there ssrc) (.there sj) (.there si)))
          (.stmt (.expr (sourceSelectedAlias .here (.there (ds self)) (.there sj)))
            (.stmt (.expr (sourceIndexedDelete .here (.there si))) .nil)) :
              Source.RItems E0 [] false .body AliasSΓ AliasSΓ) aliasSource.1).run (.nil,aliasSource.2)=
                (.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run aliasState (.cons (referenceReadStmt (.there (dt self)) (.there tsrc) (.there ti) (.there tj))
        (.cons (.rebindMem .here (.alias (.loc (.index .dyn (.var (.there (dt self)) rfl) (.simple (.local (.there ti)))))))
          (.cons (.deleteMem (.loc (.index .dyn (.var .here rfl) (.simple (.local (.there tj))))) rfl) .nil)))=
            .ok ⟨aliasDeletedState self,List.prefix_refl _⟩ ∧
      run (referenceReadWriteCode (C := C) (Δ := AliasΓ) 1 (.there (dt self)) (.there tsrc) (.there ti) (.there tj)) aliasWord=
        .ok (aliasMidWord self) 0 ∧
      run (selectedAliasCode (C := C) (Γ := AliasΓ) 1 .here (.there (dt self)) (.there ti)) (aliasMidWord self)=.ok (aliasFinalWord self) 0 ∧
      run (deleteLocalCode 1 (.here : Idx AliasΓ (.mem B)) (compileVal 1 (.simple (.local (.there tj)) : Val C AliasΓ .uint)))
        (aliasFinalWord self)=.ok (aliasDeletedWord self) 0 ∧
      run ((referenceReadWriteCode (C := C) (Δ := AliasΓ) 1 (.there (dt self)) (.there tsrc) (.there ti) (.there tj) ++
        selectedAliasCode (C := C) (Γ := AliasΓ) 1 .here (.there (dt self)) (.there ti)) ++
          deleteLocalCode 1 (.here : Idx AliasΓ (.mem B)) (compileVal 1 (.simple (.local (.there tj)) : Val C AliasΓ .uint)))
        aliasWord=.ok (aliasDeletedWord self) 0 ∧
      aliasViews ym=expectedSource self ∧ aliasViews ya=expectedSource self ∧ aliasViews z=deletedSource self ∧
      SourceBoolRefsAt z (daddr self) (deletedHeap self) (dref self) addresses ∧
      SourceBoolMemoryAt z 0 (deletedHeap self) left .dyn ∧ SourceBoolMemoryAt z 1 (deletedHeap self) right .dyn ∧
      Source.MemOK E0 SH z ∧ RefArrayStateRepr 1 1 8 aliasFrag (aliasDeletedState self) base (aliasDeletedWord self) ∧
      (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local (.here : Source.Idx AliasSΓ SB)) (.local (.there si)) rfl)).run ya=
        (.ok (.val (.bool true)),ya) ∧
      (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local (.here : Source.Idx AliasSΓ SB)) (.local (.there si)) rfl)).run z=
        (.ok (.val (.bool false)),z) ∧
      (Source.readLoc (E := E0) (Γ := AliasSΓ) F0 (τ := .bool) (.mem 0 0)).run z=(.ok (.bool true),z) ∧
      z.1=aliasSource.1.set .here (.memRef rfl 1) ∧ z.2.heap.next=5 ∧ z.2.heap.get 5=none ∧
      (z.2.ex=aliasSource.2.ex ∧ z.2.events=aliasSource.2.events ∧ z.2.logs=aliasSource.2.logs ∧ z.2.fnLocals=aliasSource.2.fnLocals) ∧
      StructAllocatorRepr (deletedHeap self) base 8 ⟨48,by decide⟩ (aliasDeletedWord self) ∧
      (aliasDeletedWord self).stack=[w[42]] := by
  first
  | solve | rfl | simp only [] | omega
  | have result := (aliasAt self).computed_alias_delete_program (G0 p) F0 fuel aliasSource aliasState (dref self) fresh
      (daddr self) 3 addresses aliasFresh (.there (ds self)) (.there ssrc) (.there sj) (.there si) (.there si) .here
      (.there (dt self)) (.there tsrc) (.there ti) (.there tj) (.there tj) .here
      ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨1,by decide⟩
      (by cases self <;> rfl) rfl rfl rfl rfl (by cases self <;> rfl) rfl rfl rfl rfl
      (dhi self) (by simp only [Heap.len,MObj.elems_dyn];decide)
      (by simp only [Heap.len,MObj.elems_dyn];decide) (by intro t ht hn;exact hn)
      SH aliasSourceOK aliasRepr
    obtain ⟨mid,out,ym,z,hw₁,selected,hw₃,stmt₁,stmt₂,stmt₃,items,native,word₁,word₂,word₃,word,hr₂,hr₃,child₂,
      mok₂,mok₃,repr₂,repr₃,locals₁,locals₃,nativeAlias,parentElems,childElems,others,addrs,next,effects,stack,alloc,
      repr₁,children,midAddrs,write₃⟩ := result
    simp only [MObj.elems_dyn] at hw₁ hw₃ nativeAlias
    have known₁ : hp.writeAddr (.index (dref self) .dyn (indexValue ⟨0,by decide⟩)) right=some (postHeap self) := by
      simp only [Heap.writeAddr,Heap.setIndex,indexValue,Int.toNat_natCast,show 0<(MObj.elems .dyn (hp.get (dref self))).length from dhi self,↓reduceIte]
      rfl
    have midEq : mid=postHeap self := Option.some.inj (hw₁.symm.trans known₁)
    subst mid
    have known₃ : (postHeap self).writeAddr (.index right .dyn (indexValue ⟨1,by decide⟩)) false=some (deletedHeap self) := by
      cases self <;> simp only [Heap.writeAddr,Heap.setIndex,postHeap,dref,Bool.false_eq_true,if_false,if_true,indexValue,
        Int.toNat_natCast,Heap.get,Objs.get,Heap.set,Objs.set,hp,old,fresh,right,MObj.elems_dyn,MObj.setElem_dyn,deletedHeap] <;> rfl
    have outEq : out=deletedHeap self := Option.some.inj (hw₃.symm.trans known₃)
    subst out
    simp only [MObj.elems_dyn] at stmt₂ stmt₃ items native word₁ word₂ word₃ word hr₂ hr₃ repr₂ repr₃ child₂ locals₃ nativeAlias parentElems childElems others addrs midAddrs write₃ alloc
    let ya : Source.EMState E0 AliasSΓ := (ym.1.set .here (.memRef rfl 1),ym.2)
    change SourceBoolRefsAt ya (daddr self) (postHeap self) (dref self) addresses at hr₂
    change SourceBoolRefsAt z (daddr self) (deletedHeap self) (dref self) addresses at hr₃
    change SourceBoolMemoryAt ya 1 (postHeap self) right .dyn at child₂
    change ∀ q : HRef H B,(postHeap self).get q=hp.get q at children
    change ∀ q : HRef H B,q.id≠right.id → (deletedHeap self).get q=hp.get q at others
    change z.1=aliasSource.1.set .here (.memRef rfl 1) at locals₃
    have tables : aliasViews ym=expectedSource self := by
      have parent := hr₂.parent
      rw [post_elems] at parent
      cases self
      · change ym.2.heap.get 2=some ⟨SR,pdata [right]⟩ at parent
        unfold aliasViews expectedSource
        rw [parent,midAddrs 0 (by decide),midAddrs 1 (by decide),midAddrs 3 (by decide),midAddrs 4 (by decide)];rfl
      · change ym.2.heap.get 3=some ⟨SR,pdata [right,right,left]⟩ at parent
        unfold aliasViews expectedSource
        rw [parent,midAddrs 0 (by decide),midAddrs 1 (by decide),midAddrs 2 (by decide),midAddrs 4 (by decide)];rfl
    change ((deletedHeap self).get (dref self)).val=(hp.get (dref self)).val.set 0 right at parentElems
    change ((deletedHeap self).get right).val=(hp.get right).val.set 1 false at childElems
    have member : right∈MObj.elems .dyn ((deletedHeap self).get (dref self)) := by
      rw [MObj.elems_dyn,parentElems]
      simpa only [MObj.elems_dyn] using List.mem_set (dhi self) right
    have child₃ := hr₃.children right member
    have leftAt : SourceBoolMemoryAt z 0 (deletedHeap self) left .dyn := by
      unfold SourceBoolMemoryAt
      rw [addrs 0 (by cases self <;> decide) (by decide),others left (by decide)]
      exact left_at
    have finalTables : aliasViews z=deletedSource self := by
      have parent := hr₃.parent
      have leaf := child₃
      unfold SourceBoolMemoryAt at leaf
      cases self
      all_goals
        simp only [deletedHeap,postHeap,dref,daddr,addresses,Bool.false_eq_true,if_false,if_true,Heap.get,Objs.get,
          Heap.set,Objs.set,hp,old,fresh,right,MObj.elems_dyn,MObj.setElem_dyn,List.set_cons_zero,List.set_cons_succ] at parent leaf
        unfold aliasViews deletedSource
        simp only [Bool.false_eq_true,if_false,if_true]
        rw [parent,leaf,addrs 0 (by decide) (by decide),addrs 4 (by decide) (by decide)]
      · rw [addrs 3 (by decide) (by decide)];rfl
      · rw [addrs 2 (by decide) (by decide)];rfl
    have before : (postHeap self).index right .dyn (uintOfNat 1)=some true := by
      simp only [Heap.index,children right,MObj.elems_dyn];rfl
    have after : (deletedHeap self).index right .dyn (uintOfNat 1)=some false := by
      change (MObj.elems .dyn ((deletedHeap self).get right))[1]?=some false
      rw [MObj.elems_dyn,childElems];rfl
    have beforeRead := child₂.eval_local_read (G0 p) F0 fuel .here (.there si) (uintOfNat 1) true
      (source_locals_get_set _ _ _) (by rw [source_bool_alias_uint_frame,locals₁];rfl) before
    have afterRead := child₃.eval_local_read (G0 p) F0 fuel .here (.there si) (uintOfNat 1) false
      (by rw [locals₃];rfl) (by rw [locals₃];rfl) after
    have leftRead := (leftAt.read_iff F0 (uintOfNat 0) true).mpr
      (by simp only [Heap.index,others left (by decide),MObj.elems_dyn];rfl)
    refine ⟨ym,z,stmt₁,stmt₂,stmt₃,items,native,word₁,word₂,word₃,word,tables,tables,finalTables,hr₃,leftAt,child₃,
      mok₃,repr₃,beforeRead,afterRead,leftRead,locals₃,next,?_,effects,?_,rfl⟩
    · rw [addrs 5 (by cases self <;> decide) (by decide)];rfl
    · apply alloc ⟨48,by decide⟩ (by decide) aliasAllocator
      cases self <;> simp only [dref,Bool.false_eq_true,if_false,if_true,Heap.len,MObj.elems_dyn,base] <;> decide

/-- ALL ordered machine/native observations across replacement, rebinding and
clear. Prior vectors are reused verbatim; the final clear changes only RIGHT's
payload cell26. Skipping clear or selecting the stale LEFT object differs. -/
theorem complete_alias_delete_vectors (self : Bool) :
    words aliasWord=[w[48],w[32],w[32],w[36],w[1],w[0],w[16],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[1],w[16],w[3],w[16],w[24],w[16],w[0],w[0]] ∧
    words (aliasMidWord self)=[w[48],w[32],w[32],w[36],w[1],w[0],w[16],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[1],(if self then w[16] else w[24]),w[3],(if self then w[24] else w[16]),w[24],w[16],w[0],w[0]] ∧
    words (aliasFinalWord self)=[w[48],w[32],w[32],w[36],w[1],w[0],w[24],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[1],(if self then w[16] else w[24]),w[3],(if self then w[24] else w[16]),w[24],w[16],w[0],w[0]] ∧
    words (aliasDeletedWord self)=[w[48],w[32],w[32],w[36],w[1],w[0],w[24],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[0],w[0],w[1],(if self then w[16] else w[24]),w[3],(if self then w[24] else w[16]),w[24],w[16],w[0],w[0]] ∧
    views hp=([true,false,false],[false,true,false],[0],[0,1,0],[]) ∧
    views (postHeap self)=([true,false,false],[false,true,false],(if self then [0] else [1]),(if self then [1,1,0] else [0,1,0]),[]) ∧
    views (aliasFinalState self).heap=views (postHeap self) ∧
    views (deletedHeap self)=([true,false,false],[false,false,false],(if self then [0] else [1]),(if self then [1,1,0] else [0,1,0]),[]) ∧
    TEnv.get (.here : Idx AliasΓ (.mem B)) (aliasDeletedState self).env=some right ∧
    (aliasDeletedWord self).mem 0=w[48] ∧ (aliasDeletedWord self).stack=[w[42]] ∧
    words (aliasDeletedWord self)≠words (aliasFinalWord self) ∧
    words (aliasDeletedWord self)≠words (writeMachine (aliasFinalWord self) 18 w[0]) := by
  first
  | solve | rfl | simp only [] | omega
  | cases self <;> simp only [Bool.false_eq_true,if_false,if_true]
    all_goals
      refine ⟨rfl,rfl,rfl,rfl,?_,?_,rfl,?_,rfl,rfl,rfl,by decide,by decide⟩
      · simp only [views,Heap.get,Objs.get,hp,left,right,old,fresh,empty,MObj.elems_dyn,List.map_cons,List.map_nil]
      · simp only [views,postHeap,dref,Bool.false_eq_true,if_false,if_true,Heap.get,Objs.get,Heap.set,Objs.set,hp,left,right,old,fresh,empty,MObj.elems_dyn,MObj.setElem_dyn,List.map_cons,List.map_nil];rfl
      · simp only [views,deletedHeap,postHeap,dref,Bool.false_eq_true,if_false,if_true,Heap.get,Objs.get,Heap.set,Objs.set,hp,left,right,old,fresh,empty,MObj.elems_dyn,MObj.setElem_dyn,List.map_cons,List.map_nil];rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.computed_alias_delete_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms computed_alias_delete_client
/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.complete_alias_delete_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_alias_delete_vectors


private abbrev RejectAliasΓ : Ctx := .mem B :: BoundΓ
private abbrev RejectAliasSΓ : Source.RCtx := SB :: BoundSΓ
private def rejectAliasState : State C RejectAliasΓ := boundState.push (t := .mem B) (some left)
private def rejectAliasSource : Source.EMState E0 RejectAliasSΓ := (.cons (.memRef rfl 0) boundSource.1,boundSource.2)
private def rejectAliasWord := writeMachine boundWord 7 w[16]
private def rejectAliasFrag := boundFrag.push (.mem B) .ok
private def rejectAliasMidWord (self : Bool) := writeMachine rejectAliasWord ((base (dref self).id).val+1) w[24]
private def rejectAliasFinalWord (self : Bool) := writeMachine (rejectAliasMidWord self) 7 w[24]
private def rejectAliasFinalState (self : Bool) := (rejectAliasState.withHeap (postHeap self)).setLocal (.here : Idx RejectAliasΓ (.mem B)) (some right)
private def rejectAliasViews (y : Source.EMState E0 RejectAliasSΓ) :=
  [y.2.heap.get 0,y.2.heap.get 1,y.2.heap.get 2,y.2.heap.get 3,y.2.heap.get 4]
private theorem rejectAliasOK : Source.MemOK E0 SH rejectAliasSource :=
  ⟨⟨boundSourceOK.1.1,⟨⟨SB,rfl,rfl⟩,boundSourceOK.1.2⟩⟩,boundSourceOK.2⟩
private theorem rejectAliasAt (self : Bool) : SourceBoolRefsAt rejectAliasSource (daddr self) hp (dref self) addresses :=
  ⟨(dat self).parent,(dat self).children⟩
private theorem rejectAliasFresh : SourceBoolRefsAt rejectAliasSource 3 hp fresh addresses :=
  ⟨fresh_at.parent,fresh_at.children⟩
private theorem rejectAliasRepr : RefArrayStateRepr 1 1 8 rejectAliasFrag rejectAliasState base rejectAliasWord :=
  ⟨boundRepr.state.consMem left (by decide),boundRepr.arrays.localWrite 7 (by decide) w[16]⟩
private theorem rejectAliasAllocator : StructAllocatorRepr hp base 8 ⟨48,by decide⟩ rejectAliasWord :=
  boundAllocator.localWrite 7 (by decide) (by decide) w[16]

/-- Both pipelines, same/distinct parent: actual two changed prefixes, then
RIGHT endpoint3 rejects. Source exposes retained reached globals; intrinsic and
word failure outcomes expose no final machine. The seven locals are independently
represented (the added scalar/reference are not declaration executions). -/
theorem computed_alias_reject_client (p : Roadmap.Pipeline) (fuel : Nat) (self : Bool) :
    ∃ ym : Source.EMState E0 RejectAliasSΓ,
    let ya : Source.EMState E0 RejectAliasSΓ := (ym.1.set .here (.memRef rfl 1),ym.2);
      (Source.execS (G0 p) F0 (fuel+6) RejectAliasSΓ.length none
        (.expr (sourceReferenceReadAssign (.there (.there (ds self))) (.there (.there ssrc)) (.there (.there sj)) (.there (.there si))) :
          Source.RStmt E0 [] false .body RejectAliasSΓ RejectAliasSΓ) rejectAliasSource.1).run (.nil,rejectAliasSource.2)=
            (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS (G0 p) F0 (fuel+5) RejectAliasSΓ.length none
        (.expr (sourceSelectedAlias .here (.there (.there (ds self))) (.there (.there sj))) :
          Source.RStmt E0 [] false .body RejectAliasSΓ RejectAliasSΓ) ym.1).run (.nil,ym.2)=
            (.ok (.normal ya.1),(.nil,ya.2)) ∧
      (Source.evalE (G0 p) F0 (fuel+3) (sourceIndexedDelete (.here : Source.Idx RejectAliasSΓ SB) (.there .here))).run ya=
        (.error (.revert (Source.panicData .index)),ya) ∧
      (Source.execItems (G0 p) F0 (fuel+7) RejectAliasSΓ.length none
        (.stmt (.expr (sourceReferenceReadAssign (.there (.there (ds self))) (.there (.there ssrc)) (.there (.there sj)) (.there (.there si))))
          (.stmt (.expr (sourceSelectedAlias .here (.there (.there (ds self))) (.there (.there sj))))
            (.stmt (.expr (sourceIndexedDelete (.here : Source.Idx RejectAliasSΓ SB) (.there .here))) .nil)) :
              Source.RItems E0 [] false .body RejectAliasSΓ RejectAliasSΓ) rejectAliasSource.1).run (.nil,rejectAliasSource.2)=
                (.error (.revert (Source.panicData .index)),(.nil,ya.2)) ∧
      Prog.run rejectAliasState
        (.cons (referenceReadStmt (.there (.there (dt self))) (.there (.there tsrc)) (.there (.there ti)) (.there (.there tj)))
          (.cons (.rebindMem .here (.alias (.loc (.index .dyn (.var (.there (.there (dt self))) rfl) (.simple (.local (.there (.there ti)))))))) .nil))=
            .ok ⟨rejectAliasFinalState self,List.prefix_refl _⟩ ∧
      Stmt.run (rejectAliasFinalState self) (.deleteMem (.loc (.index .dyn (.var (.here : Idx RejectAliasΓ (.mem B)) rfl)
        (.simple (.local (.there .here))))) rfl)=.error .revert ∧
      Prog.run rejectAliasState
        (.cons (referenceReadStmt (.there (.there (dt self))) (.there (.there tsrc)) (.there (.there ti)) (.there (.there tj)))
          (.cons (.rebindMem .here (.alias (.loc (.index .dyn (.var (.there (.there (dt self))) rfl) (.simple (.local (.there (.there ti))))))))
            (.cons (.deleteMem (.loc (.index .dyn (.var (.here : Idx RejectAliasΓ (.mem B)) rfl) (.simple (.local (.there .here))))) rfl) .nil)))=.error .revert ∧
      run (referenceReadWriteCode (C := C) (Δ := RejectAliasΓ) 1 (.there (.there (dt self))) (.there (.there tsrc)) (.there (.there ti)) (.there (.there tj))) rejectAliasWord=
        .ok (rejectAliasMidWord self) 0 ∧
      run (selectedAliasCode (C := C) (Γ := RejectAliasΓ) 1 .here (.there (.there (dt self))) (.there (.there ti))) (rejectAliasMidWord self)=
        .ok (rejectAliasFinalWord self) 0 ∧
      run (deleteLocalCode 1 (.here : Idx RejectAliasΓ (.mem B)) (compileVal 1 (.simple (.local (.there .here)) : Val C RejectAliasΓ .uint))) (rejectAliasFinalWord self)=.revert ∧
      run ((referenceReadWriteCode (C := C) (Δ := RejectAliasΓ) 1 (.there (.there (dt self))) (.there (.there tsrc)) (.there (.there ti)) (.there (.there tj)) ++
        selectedAliasCode (C := C) (Γ := RejectAliasΓ) 1 .here (.there (.there (dt self))) (.there (.there ti))) ++
        deleteLocalCode 1 (.here : Idx RejectAliasΓ (.mem B)) (compileVal 1 (.simple (.local (.there .here)) : Val C RejectAliasΓ .uint))) rejectAliasWord=.revert ∧
      rejectAliasViews ym=expectedSource self ∧ rejectAliasViews ya=expectedSource self ∧
      SourceBoolRefsAt ya (daddr self) (postHeap self) (dref self) addresses ∧
      SourceBoolMemoryAt ya 0 (postHeap self) left .dyn ∧ SourceBoolMemoryAt ya 1 (postHeap self) right .dyn ∧
      Source.MemOK E0 SH ya ∧ RefArrayStateRepr 1 1 8 rejectAliasFrag (rejectAliasFinalState self) base (rejectAliasFinalWord self) ∧
      (Source.readLoc (E := E0) (Γ := RejectAliasSΓ) F0 (τ := .bool) (.mem 0 0)).run ya=(.ok (.bool true),ya) ∧
      (Source.readLoc (E := E0) (Γ := RejectAliasSΓ) F0 (τ := .bool) (.mem 1 1)).run ya=(.ok (.bool true),ya) ∧
      (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local (.here : Source.Idx RejectAliasSΓ SB)) (.local (.there (.there sj))) rfl)).run rejectAliasSource=
        (.ok (.val (.bool true)),rejectAliasSource) ∧
      (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local (.here : Source.Idx RejectAliasSΓ SB)) (.local (.there (.there sj))) rfl)).run ya=
        (.ok (.val (.bool false)),ya) ∧
      (Source.evalE (G0 p) F0 2 (sourceIndexedDelete (.here : Source.Idx RejectAliasSΓ SB) (.there .here))).run ya=(.error .timeout,ya) ∧
      ym.1=rejectAliasSource.1 ∧ ya.1=rejectAliasSource.1.set .here (.memRef rfl 1) ∧
      ya.2.heap.next=5 ∧ ya.2.heap.get 5=none ∧
      (ya.2.ex=rejectAliasSource.2.ex ∧ ya.2.events=rejectAliasSource.2.events ∧ ya.2.logs=rejectAliasSource.2.logs ∧ ya.2.fnLocals=rejectAliasSource.2.fnLocals) ∧
      StructAllocatorRepr (postHeap self) base 8 ⟨48,by decide⟩ (rejectAliasFinalWord self) ∧
      (rejectAliasFinalWord self).stack=[w[42]] := by
  first
  | solve | rfl | simp only [] | omega
  | have result := (rejectAliasAt self).computed_alias_delete_reject (G0 p) F0 fuel rejectAliasSource rejectAliasState (dref self) fresh
      (daddr self) 3 addresses rejectAliasFresh (.there (.there (ds self))) (.there (.there ssrc))
      (.there (.there sj)) (.there (.there si)) (.there .here) .here
      (.there (.there (dt self))) (.there (.there tsrc)) (.there (.there ti)) (.there (.there tj)) (.there .here) .here
      ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨3,by decide⟩
      (by cases self <;> rfl) rfl rfl rfl rfl (by cases self <;> rfl) rfl rfl rfl rfl
      (dhi self) (by simp only [Heap.len,MObj.elems_dyn];decide) (by simp only [Heap.len,MObj.elems_dyn];decide)
      SH rejectAliasOK rejectAliasRepr
    obtain ⟨mid,ym,hw,selected,stmt₁,stmt₂,expr₃,stmt₃,items,nativePrefix,native₃,native,word₁,word₂,word₃,word,hr,child,
      mok,repr,locals₁,locals₂,sourceAlias,nativeAlias,parent,children,addrs,next,effects,stack,alloc⟩ := result
    simp only [MObj.elems_dyn] at hw
    have known : hp.writeAddr (.index (dref self) .dyn (indexValue ⟨0,by decide⟩)) right=some (postHeap self) := by
      simp only [Heap.writeAddr,Heap.setIndex,indexValue,Int.toNat_natCast,show 0<(MObj.elems .dyn (hp.get (dref self))).length from dhi self,↓reduceIte]
      rfl
    have midEq : mid=postHeap self := Option.some.inj (hw.symm.trans known)
    subst mid
    simp only [MObj.elems_dyn] at stmt₂ expr₃ stmt₃ items nativePrefix native₃ native word₁ word₂ word₃ word hr child mok repr locals₂ sourceAlias nativeAlias parent children addrs next effects stack alloc
    let ya : Source.EMState E0 RejectAliasSΓ := (ym.1.set .here (.memRef rfl 1),ym.2)
    change SourceBoolRefsAt ya (daddr self) (postHeap self) (dref self) addresses at hr
    change SourceBoolMemoryAt ya 1 (postHeap self) right .dyn at child
    change ∀ q : HRef H B,(postHeap self).get q=hp.get q at children
    have tables : rejectAliasViews ya=expectedSource self := by
      have parent := hr.parent
      rw [post_elems] at parent
      cases self
      · change ya.2.heap.get 2=some ⟨SR,pdata [right]⟩ at parent
        unfold rejectAliasViews expectedSource
        rw [parent,addrs 0 (by decide),addrs 1 (by decide),addrs 3 (by decide),addrs 4 (by decide)];rfl
      · change ya.2.heap.get 3=some ⟨SR,pdata [right,right,left]⟩ at parent
        unfold rejectAliasViews expectedSource
        rw [parent,addrs 0 (by decide),addrs 1 (by decide),addrs 2 (by decide),addrs 4 (by decide)];rfl
    have leftAt : SourceBoolMemoryAt ya 0 (postHeap self) left .dyn := by
      unfold SourceBoolMemoryAt
      rw [addrs 0 (by cases self <;> decide),children left]
      exact left_at
    have leftRead := (leftAt.read_iff F0 (uintOfNat 0) true).mpr (by simp only [Heap.index,children left,MObj.elems_dyn];rfl)
    have rightRead := (child.read_iff F0 (uintOfNat 1) true).mpr (by simp only [Heap.index,children right,MObj.elems_dyn];rfl)
    have initialLeft : SourceBoolMemoryAt rejectAliasSource 0 hp left .dyn := left_at
    have oldRead := initialLeft.eval_local_read (G0 p) F0 fuel .here (.there (.there sj)) (uintOfNat 0) true rfl rfl
      (by simp only [Heap.index,MObj.elems_dyn];rfl)
    have newRead := child.eval_local_read (G0 p) F0 fuel .here (.there (.there sj)) (uintOfNat 0) false sourceAlias
      (by change (ym.1.set (.here : Source.Idx RejectAliasSΓ SB) (.memRef rfl 1)).get (.there (.there sj))=_;rw [source_bool_alias_uint_frame,locals₁];rfl) (by simp only [Heap.index,children right,MObj.elems_dyn];rfl)
    have timeout := source_indexed_delete_horizon_two (G0 p) F0 ya (.here : Source.Idx RejectAliasSΓ SB) (.there .here)
    refine ⟨ym,stmt₁,stmt₂,expr₃,items,nativePrefix,native₃,native,word₁,word₂,word₃,word,tables,tables,hr,leftAt,child,mok,repr,
      leftRead,rightRead,oldRead,newRead,timeout,locals₁,locals₂,next,?_,effects,?_,rfl⟩
    · rw [addrs 5 (by cases self <;> decide)];rfl
    · apply alloc ⟨48,by decide⟩ (by decide) rejectAliasAllocator
      cases self <;> simp only [dref,Bool.false_eq_true,if_false,if_true,Heap.len,MObj.elems_dyn,base] <;> decide

/-- Full INITIAL/replacement/rebound target vectors; failure supplies no new
machine, and both referenced child contents remain the original contents. -/
theorem complete_alias_reject_vectors (self : Bool) :
    rejectAliasViews rejectAliasSource=[some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,
      some ⟨SR,pdata [left]⟩,some ⟨SR,pdata [left,right,left]⟩,some ⟨SR,pdata []⟩] ∧
    words rejectAliasWord=[w[48],w[32],w[32],w[36],w[1],w[0],w[3],w[16],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[1],w[16],w[3],w[16],w[24],w[16],w[0],w[0]] ∧
    words (rejectAliasMidWord self)=[w[48],w[32],w[32],w[36],w[1],w[0],w[3],w[16],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[1],(if self then w[16] else w[24]),w[3],(if self then w[24] else w[16]),w[24],w[16],w[0],w[0]] ∧
    words (rejectAliasFinalWord self)=[w[48],w[32],w[32],w[36],w[1],w[0],w[3],w[24],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[1],(if self then w[16] else w[24]),w[3],(if self then w[24] else w[16]),w[24],w[16],w[0],w[0]] ∧
    views rejectAliasState.heap=views hp ∧
    views (rejectAliasFinalState self).heap=([true,false,false],[false,true,false],(if self then [0] else [1]),(if self then [1,1,0] else [0,1,0]),[]) ∧
    TEnv.get (.here : Idx RejectAliasΓ (.mem B)) rejectAliasState.env=some left ∧
    TEnv.get (.here : Idx RejectAliasΓ (.mem B)) (rejectAliasFinalState self).env=some right ∧
    (rejectAliasFinalWord self).mem 0=w[48] ∧ (rejectAliasFinalWord self).stack=[w[42]] ∧
    words (rejectAliasFinalWord self)≠words (rejectAliasMidWord self) ∧
    words (rejectAliasFinalWord self)≠words (writeMachine (rejectAliasFinalWord self) 26 w[0]) := by
  first
  | solve | rfl | simp only [] | omega
  | cases self <;> simp only [Bool.false_eq_true,if_false,if_true]
    all_goals
      refine ⟨rfl,rfl,rfl,rfl,rfl,?_,rfl,rfl,rfl,rfl,by decide,by decide⟩
      simp only [rejectAliasFinalState,State.setLocal,State.withHeap,views,postHeap,dref,Bool.false_eq_true,if_false,if_true,Heap.get,Objs.get,Heap.set,Objs.set,hp,left,right,old,fresh,empty,MObj.elems_dyn,MObj.setElem_dyn,List.map_cons,List.map_nil];rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.computed_alias_reject_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms computed_alias_reject_client
/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.complete_alias_reject_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_alias_reject_vectors


private abbrev RhsΓ : Ctx := .val .bool :: AliasΓ
private abbrev RhsSΓ : Source.RCtx := .bool :: AliasSΓ
private def rhsNumber (bad : Bool) := if bad then 3 else 0
private def rhsBase := aliasState.push (t := .val .bool) true
private def rhsState (bad : Bool) := rhsBase.setLocal (.there (.there ti)) (uintOfNat (rhsNumber bad))
private def rhsSourceBase : Source.EMState E0 RhsSΓ := (.cons (.bool true) aliasSource.1,aliasSource.2)
private def rhsSource (bad : Bool) : Source.EMState E0 RhsSΓ :=
  (rhsSourceBase.1.set (.there (.there sj)) (sourceUint (uintOfNat (rhsNumber bad))),rhsSourceBase.2)
private def rhsWord (bad : Bool) := writeMachine (writeMachine aliasWord 7 w[1]) 5 (.val (wmod (rhsNumber bad)))
private def rhsFrag := aliasFrag.push (.val .bool) .ok
private def rhsHeap := hp.set left (MObj.setElem .dyn (hp.get left) 1 true)
private def rhsMidWord (bad : Bool) := writeMachine (rhsWord bad) 18 w[1]
private def rhsViews (y : Source.EMState E0 RhsSΓ) := [y.2.heap.get 0,y.2.heap.get 1,y.2.heap.get 2,y.2.heap.get 3,y.2.heap.get 4]
private def rhsTables : List (Option (Σ τ : Source.STy,Source.Data E0.layout τ)) :=
  [some ⟨SB,sourceBoolMemory [true,true,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,
    some ⟨SR,pdata [left]⟩,some ⟨SR,pdata [left,right,left]⟩,some ⟨SR,pdata []⟩]
private theorem rhsAt (bad : Bool) : SourceBoolMemoryAt (rhsSource bad) 0 hp left .dyn := left_at
private theorem rhsOK (bad : Bool) : Source.MemOK E0 SH (rhsSource bad) := by
  have hb : Source.MemOK E0 SH rhsSourceBase :=
    ⟨⟨aliasSourceOK.1.1,⟨trivial,aliasSourceOK.1.2⟩⟩,aliasSourceOK.2⟩
  exact ⟨⟨hb.1.1,Source.LocalsOK.set rhsSourceBase.1 (.there (.there sj)) hb.1.2 trivial⟩,hb.2⟩
private theorem rhsRepr (bad : Bool) : StateRepr 1 1 8 rhsFrag (rhsState bad) base (rhsWord bad) := by
  have hb := aliasRepr.state.consVal (p := .bool) true w[1] rfl (by decide)
  exact hb.setVal (.there (.there ti)) (uintOfNat (rhsNumber bad)) (.val (wmod (rhsNumber bad)))
    (by cases bad <;> exact ReprV.uint_of rfl)
private theorem rhsAllocator (bad : Bool) : StructAllocatorRepr hp base 8 ⟨48,by decide⟩ (rhsWord bad) :=
  (aliasAllocator.localWrite 7 (by decide) (by decide) w[1]).localWrite 5 (by decide) (by decide) _
private def rhsNative (i : Idx RhsΓ (.val .uint)) : Stmt C RhsΓ RhsΓ :=
  .assignMem (.index .dyn (.var (.there .here : Idx RhsΓ (.mem B)) rfl) (.simple (.local i))) (.val (.simple (.local .here)))
private def rhsCode (i : Idx RhsΓ (.val .uint)) :=
  writeLocalCode (C := C) 1 (.there .here : Idx RhsΓ (.mem B)) (.simple (.local i)) (.simple (.local .here))
private theorem rhs_first_word (bad : Bool) :
    run (rhsCode (.there (.there tj))) (rhsWord bad)=.ok (rhsMidWord bad) 0 := by
  have codes : rhsCode (.there (.there tj))=[.mload 7,.mload 6,.mload 4] ++ writeArrayStackCode := by rfl
  rw [codes]
  have load : run [.mload 7,.mload 6,.mload 4] (rhsWord bad)=
      .ok ((((rhsWord bad).push w[1]).push w[16]).push w[1]) 0 := by cases bad <;> rfl
  rw [Evm.run_append_ok load,writeArrayStackCode,arrayStack_append_eq ((rhsWord bad).push w[1])
    (⟨16,by decide⟩ : Fin W) (⟨1,by decide⟩ : Fin W) 3 (by decide) (by cases bad <;> rfl) [.mstoreAt]]
  have addr := arrayAddr_run ((rhsWord bad).push w[1]) (⟨16,by decide⟩ : Fin W) (⟨1,by decide⟩ : Fin W) 3
    (by decide) (by cases bad <;> rfl)
  simp only [show (1 : Nat)<3 from by decide,if_pos] at addr
  rw [Evm.run_append_ok addr]
  rfl

/-- BOTH actual pipelines: RHS LEFT[1]=true materially changes the cell BEFORE
outer endpoint3 is resolved. The nested expression/statement fail with that real
RHS state; a separately executed initial LHS lookup fails without it. No target
post-revert machine or outer transaction rollback is inferred. -/
theorem rhs_late_effect_client (p : Roadmap.Pipeline) (fuel : Nat) :
    ∃ ym : Source.EMState E0 RhsSΓ,
      (Source.evalE (G0 p) F0 (fuel+3) (sourceIndexedAssign (.there .here) (.there (.there si)) .here)).run (rhsSource true)=
        (.ok (.val (.bool true)),ym) ∧
      (Source.evalE (G0 p) F0 (fuel+4) (sourceRhsAssign (.there .here) (.there (.there sj)) (.there (.there si)) .here)).run (rhsSource true)=
        (.error (.revert (Source.panicData .index)),ym) ∧
      (Source.execS (G0 p) F0 (fuel+5) RhsSΓ.length none
        (.expr (sourceRhsAssign (.there .here) (.there (.there sj)) (.there (.there si)) .here) : Source.RStmt E0 [] false .body RhsSΓ RhsSΓ)
        (rhsSource true).1).run (.nil,(rhsSource true).2)=(.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      (Source.evalLoc (G0 p) F0 (fuel+3) (.indexArray (.local (.there .here : Source.Idx RhsSΓ SB)) (by decide) (.local (.there (.there sj))) rfl)).run (rhsSource true)=
        (.error (.revert (Source.panicData .index)),rhsSource true) ∧
      Prog.run (rhsState true) (.cons (rhsNative (.there (.there tj))) (.cons (rhsNative (.there (.there ti))) .nil))=.error .revert ∧
      run (rhsCode (.there (.there tj))) (rhsWord true)=.ok (rhsMidWord true) 0 ∧
      run (rhsCode (.there (.there ti))) (rhsMidWord true)=.revert ∧
      run (rhsCode (.there (.there tj)) ++ rhsCode (.there (.there ti))) (rhsWord true)=.revert ∧
      rhsViews ym=rhsTables ∧ SourceBoolMemoryAt ym 0 rhsHeap left .dyn ∧ Source.MemOK E0 SH ym ∧
      StateRepr 1 1 8 rhsFrag ((rhsState true).withHeap rhsHeap) base (rhsMidWord true) ∧
      ym.1=(rhsSource true).1 ∧ ym.2.heap.get 0≠(rhsSource true).2.heap.get 0 ∧
      (∀ a,a≠0 → ym.2.heap.get a=(rhsSource true).2.heap.get a) ∧ ym.2.heap.next=5 ∧
      (ym.2.ex=(rhsSource true).2.ex ∧ ym.2.events=(rhsSource true).2.events ∧ ym.2.logs=(rhsSource true).2.logs ∧ ym.2.fnLocals=(rhsSource true).2.fnLocals) ∧
      StructAllocatorRepr rhsHeap base 8 ⟨48,by decide⟩ (rhsMidWord true) ∧ (rhsMidWord true).stack=[w[42]] := by
  first
  | solve | rfl | simp only [] | omega
  | obtain ⟨mid,ym,mm,hw,inner,expr,stmt,native₁,native₂,native,word₁,word₂,word,hr,mok,repr,locals,elems,other,addrs,next,effects,stack,alloc⟩ :=
      rhs_assign_late_bounds_word (G0 p) F0 fuel (rhsState true) left (rhsAt true) (.there .here) (.there (.there sj)) (.there (.there si)) .here
        (.there .here) (.there (.there ti)) (.there (.there tj)) .here (uintOfNat 3) (uintOfNat 1) true
        rfl rfl rfl rfl rfl rfl rfl rfl (by simp only [Heap.len,MObj.elems_dyn];decide) (by simp only [Heap.len,MObj.elems_dyn];decide)
        (rhsRepr true) SH (rhsOK true)
    have known : hp.writeAddr (.index left .dyn (uintOfNat 1)) true=some rhsHeap := by
      simp only [Heap.writeAddr,Heap.setIndex,uintOfNat_val (by decide : 1<2^256),Int.toNat_natCast,Heap.get,Objs.get,hp,left,MObj.elems_dyn];rfl
    have he : mid=rhsHeap := Option.some.inj (hw.symm.trans known)
    subst mid
    have hm : mm=rhsMidWord true := (Evm.Out.ok.inj (word₁.symm.trans (rhs_first_word true))).1
    subst mm
    have initialLeft := (rhsAt true).eval_index_bounds (G0 p) F0 (fuel+1) (.there .here) (.there (.there sj)) (uintOfNat 3) rfl rfl
      (by simp only [Heap.len,MObj.elems_dyn];decide)
    have leaf := hr
    unfold SourceBoolMemoryAt at leaf
    rw [elems] at leaf
    simp only [MObj.elems_dyn] at leaf
    change ym.2.heap.get 0=some ⟨SB,sourceBoolMemory [true,true,false]⟩ at leaf
    have tables : rhsViews ym=rhsTables := by
      unfold rhsViews rhsTables
      rw [leaf,addrs 1 (by decide),addrs 2 (by decide),addrs 3 (by decide),addrs 4 (by decide)];rfl
    refine ⟨ym,inner,expr,stmt,initialLeft,native,word₁,word₂,word,tables,hr,mok,repr,locals,?_,addrs,next,effects,alloc _ (by decide) (rhsAllocator true),rfl⟩
    intro he
    have oldAt : SourceBoolMemoryAt ym 0 hp left .dyn := by
      change ym.2.heap.get 0=some ⟨SB,sourceBoolMemory (MObj.elems .dyn (hp.get left))⟩
      rw [he];exact rhsAt true
    have nowIndex : rhsHeap.index left .dyn (uintOfNat 1)=some true := by
      change (MObj.elems .dyn (rhsHeap.get left))[(uintOfNat 1).val.toNat]?=some true
      rw [elems];simp only [MObj.elems_dyn];rfl
    have oldIndex : hp.index left .dyn (uintOfNat 1)=some false := by simp only [Heap.index,MObj.elems_dyn];rfl
    have nowRead := (hr.read_iff F0 (uintOfNat 1) true).mpr nowIndex
    have oldRead := (oldAt.read_iff F0 (uintOfNat 1) false).mpr oldIndex
    cases congrArg Prod.fst (nowRead.symm.trans oldRead)

/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.rhs_late_effect_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rhs_late_effect_client

private def rhsFinalHeap := rhsHeap.set left (MObj.setElem .dyn (rhsHeap.get left) 0 true)
private def rhsFinalWord := writeMachine (rhsMidWord false) 17 w[1]
private theorem rhs_second_word : run (rhsCode (.there (.there ti))) (rhsMidWord false)=.ok rhsFinalWord 0 := by
  have codes : rhsCode (.there (.there ti))=[.mload 7,.mload 6,.mload 5] ++ writeArrayStackCode := by rfl
  rw [codes]
  have load : run [.mload 7,.mload 6,.mload 5] (rhsMidWord false)=
      .ok ((((rhsMidWord false).push w[1]).push w[16]).push w[0]) 0 := rfl
  rw [Evm.run_append_ok load,writeArrayStackCode,arrayStack_append_eq ((rhsMidWord false).push w[1])
    (⟨16,by decide⟩ : Fin W) (⟨0,by decide⟩ : Fin W) 3 (by decide) rfl [.mstoreAt]]
  have addr := arrayAddr_run ((rhsMidWord false).push w[1]) (⟨16,by decide⟩ : Fin W) (⟨0,by decide⟩ : Fin W) 3 (by decide) rfl
  simp only [show (0 : Nat)<3 from by decide,if_pos] at addr
  rw [Evm.run_append_ok addr]
  rfl

/-- Successful ONE nested expression/statement, matched by reached nativeProg2
and complete word append. The second same-value write is actually executed,
not claimed materially different or needed to distinguish final-only ordering. -/
theorem rhs_success_effect_client (p : Roadmap.Pipeline) (fuel : Nat) :
    ∃ ym z : Source.EMState E0 RhsSΓ,
      (Source.evalE (G0 p) F0 (fuel+3) (sourceIndexedAssign (.there .here) (.there (.there si)) .here)).run (rhsSource false)=
        (.ok (.val (.bool true)),ym) ∧
      (Source.evalE (G0 p) F0 (fuel+4) (sourceRhsAssign (.there .here) (.there (.there sj)) (.there (.there si)) .here)).run (rhsSource false)=
        (.ok (.val (.bool true)),z) ∧
      (Source.execS (G0 p) F0 (fuel+5) RhsSΓ.length none
        (.expr (sourceRhsAssign (.there .here) (.there (.there sj)) (.there (.there si)) .here) : Source.RStmt E0 [] false .body RhsSΓ RhsSΓ)
        (rhsSource false).1).run (.nil,(rhsSource false).2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run (rhsState false) (.cons (rhsNative (.there (.there tj))) (.cons (rhsNative (.there (.there ti))) .nil))=
        .ok ⟨(rhsState false).withHeap rhsFinalHeap,List.prefix_refl _⟩ ∧
      run (rhsCode (.there (.there tj))) (rhsWord false)=.ok (rhsMidWord false) 0 ∧
      run (rhsCode (.there (.there ti))) (rhsMidWord false)=.ok rhsFinalWord 0 ∧
      run (rhsCode (.there (.there tj)) ++ rhsCode (.there (.there ti))) (rhsWord false)=.ok rhsFinalWord 0 ∧
      rhsViews ym=rhsTables ∧ rhsViews z=rhsTables ∧
      SourceBoolMemoryAt z 0 rhsFinalHeap left .dyn ∧ Source.MemOK E0 SH z ∧
      StateRepr 1 1 8 rhsFrag ((rhsState false).withHeap rhsFinalHeap) base rhsFinalWord ∧
      z.1=(rhsSource false).1 ∧ (∀ a,a≠0 → z.2.heap.get a=(rhsSource false).2.heap.get a) ∧ z.2.heap.next=5 ∧
      (z.2.ex=(rhsSource false).2.ex ∧ z.2.events=(rhsSource false).2.events ∧ z.2.logs=(rhsSource false).2.logs ∧ z.2.fnLocals=(rhsSource false).2.fnLocals) ∧
      StructAllocatorRepr rhsFinalHeap base 8 ⟨48,by decide⟩ rhsFinalWord ∧ rhsFinalWord.stack=[w[42]] := by
  first
  | solve | rfl | simp only [] | omega
  | obtain ⟨mid,out,ym,z,mm,target,hw₁,hw₂,inner,expr,stmt,native,word₁,word₂,word,hr₁,hr₂,mok₁,mok₂,hm₁,hm₂,
      locals₁,locals₂,elems,other,addrs,next,effects,stack,alloc⟩ :=
      rhs_assign_success_word (G0 p) F0 fuel (rhsState false) left (rhsAt false) (.there .here) (.there (.there sj)) (.there (.there si)) .here
        (.there .here) (.there (.there ti)) (.there (.there tj)) .here (uintOfNat 0) (uintOfNat 1) true
        rfl rfl rfl rfl rfl rfl rfl rfl (by simp only [Heap.len,MObj.elems_dyn];decide) (by simp only [Heap.len,MObj.elems_dyn];decide)
        (rhsRepr false) SH (rhsOK false)
    have known₁ : hp.writeAddr (.index left .dyn (uintOfNat 1)) true=some rhsHeap := by
      simp only [Heap.writeAddr,Heap.setIndex,uintOfNat_val (by decide : 1<2^256),Int.toNat_natCast,Heap.get,Objs.get,hp,left,MObj.elems_dyn];rfl
    have he₁ : mid=rhsHeap := Option.some.inj (hw₁.symm.trans known₁)
    subst mid
    have known₂ : rhsHeap.writeAddr (.index left .dyn (uintOfNat 0)) true=some rhsFinalHeap := by
      have pos : 0<(rhsHeap.get left).val.length := by
        simp only [rhsHeap,Heap.get_set_same,MObj.setElem_dyn,Heap.get,Objs.get,hp,left];decide
      simp only [Heap.writeAddr,Heap.setIndex,uintOfNat_val (by decide : 0<2^256),Int.toNat_natCast,MObj.elems_dyn,if_pos pos]
      rfl
    have he₂ : out=rhsFinalHeap := Option.some.inj (hw₂.symm.trans known₂)
    subst out
    have hm : mm=rhsMidWord false := (Evm.Out.ok.inj (word₁.symm.trans (rhs_first_word false))).1
    subst mm
    have ht : target=rhsFinalWord := (Evm.Out.ok.inj (word₂.symm.trans rhs_second_word)).1
    subst target
    have middleOther : ∀ a,a≠0 → ym.2.heap.get a=(rhsSource false).2.heap.get a := by
      obtain ⟨h,he⟩ := (rhsAt false).assign_state (G0 p) F0 fuel (.there .here) (.there (.there si)) .here (uintOfNat 1) true rfl rfl rfl
        (by simp only [Heap.len,MObj.elems_dyn];decide) inner
      intro a hn;rw [he];exact Source.Heap.write_other _ hn _ h
    have tables₁ : rhsViews ym=rhsTables := by
      have leaf := hr₁
      unfold SourceBoolMemoryAt at leaf
      simp only [rhsHeap,Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn] at leaf
      unfold rhsViews rhsTables
      rw [leaf,middleOther 1 (by decide),middleOther 2 (by decide),middleOther 3 (by decide),middleOther 4 (by decide)];rfl
    have tables₂ : rhsViews z=rhsTables := by
      have leaf := hr₂
      unfold SourceBoolMemoryAt at leaf
      rw [elems] at leaf
      simp only [MObj.elems_dyn] at leaf
      unfold rhsViews rhsTables
      rw [leaf,addrs 1 (by decide),addrs 2 (by decide),addrs 3 (by decide),addrs 4 (by decide)];rfl
    exact ⟨ym,z,inner,expr,stmt,native,word₁,word₂,word,tables₁,tables₂,hr₂,mok₂,hm₂,locals₂,addrs,next,effects,
      alloc _ (by decide) (rhsAllocator false),rfl⟩

/-- Every ordered Source/native object and all24 INITIAL/reached/final words.
Failure has only the real reached PREFIX vector, not a returned target machine.
Native and Source aliases/parents retain LEFT identity while its contents change. -/
theorem complete_rhs_effect_vectors (bad : Bool) :
    rhsViews (rhsSource bad)=[some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,
      some ⟨SR,pdata [left]⟩,some ⟨SR,pdata [left,right,left]⟩,some ⟨SR,pdata []⟩] ∧
    views (rhsState bad).heap=([true,false,false],[false,true,false],[0],[0,1,0],[]) ∧
    views rhsHeap=([true,true,false],[false,true,false],[0],[0,1,0],[]) ∧
    views rhsFinalHeap=([true,true,false],[false,true,false],[0],[0,1,0],[]) ∧
    words (rhsWord bad)=[w[48],w[32],w[32],w[36],w[1],(if bad then w[3] else w[0]),w[16],w[1],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[1],w[16],w[3],w[16],w[24],w[16],w[0],w[0]] ∧
    words (rhsMidWord bad)=[w[48],w[32],w[32],w[36],w[1],(if bad then w[3] else w[0]),w[16],w[1],w[3],w[1],w[1],w[0],w[3],w[0],w[1],w[0],w[1],w[16],w[3],w[16],w[24],w[16],w[0],w[0]] ∧
    words rhsFinalWord=[w[48],w[32],w[32],w[36],w[1],w[0],w[16],w[1],w[3],w[1],w[1],w[0],w[3],w[0],w[1],w[0],w[1],w[16],w[3],w[16],w[24],w[16],w[0],w[0]] ∧
    words (rhsMidWord bad)≠words (rhsWord bad) ∧
    (rhsWord bad).mem 0=w[48] ∧ (rhsMidWord bad).mem 0=w[48] ∧ rhsFinalWord.mem 0=w[48] ∧
    TEnv.get (.there .here : Idx RhsΓ (.mem B)) (rhsState bad).env=some left := by
  first
  | solve | rfl | simp only [] | omega
  | cases bad
    all_goals
      refine ⟨rfl,?_,?_,?_,rfl,rfl,rfl,by decide,rfl,rfl,rfl,rfl⟩
      all_goals first | change views hp = _ | skip
      all_goals simp only [views,rhsHeap,rhsFinalHeap,Heap.get_set_same,Heap.get_set_ne,Heap.get,Objs.get,
        Heap.set,Objs.set,hp,left,right,old,fresh,empty,MObj.elems_dyn,MObj.setElem_dyn,List.map_cons,List.map_nil] <;> rfl

/-- Low horizon prevents the inner write itself; this is not the late bounds
case and is not an admission cap or minimal-fuel claim. -/
theorem rhs_effect_low_horizon (p : Roadmap.Pipeline) (bad : Bool) :
    (Source.evalE (G0 p) F0 2 (sourceRhsAssign (.there .here) (.there (.there sj)) (.there (.there si)) .here)).run (rhsSource bad)=
      (.error .timeout,rhsSource bad) := by rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.rhs_success_effect_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rhs_success_effect_client
/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.complete_rhs_effect_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_rhs_effect_vectors
/-- info: 'Solidity.Backend.MemoryOps.SourceReferenceReadControls.rhs_effect_low_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rhs_effect_low_horizon

end Solidity.Backend.MemoryOps.SourceReferenceReadControls
