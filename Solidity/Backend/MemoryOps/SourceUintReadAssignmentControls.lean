import Solidity.Backend.MemoryOps.SourceUintReadAssignment
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.UintReadAssignmentControls
open Evm Evm.Memory
open Source.SemanticsExamples (E0 F0 G0 s0)
private def C : Contract := {vars := []}
private abbrev A : RefTy := .array (.prim .uint)
private abbrev H : HTy := [A,A,A]
private abbrev Δ : Ctx := [.val .uint,.val .uint,.mem A,.mem A,.mem A,.mem A]
private abbrev SA := Source.STy.array .memory (.int .u256) none
private abbrev Γ : Source.RCtx := [.int .u256,.int .u256,SA,SA,SA,SA]
private def u (n : Nat) : PrimTy.uint.Denote := indexValue (wmod n)
private def maximum : PrimTy.uint.Denote := indexValue wMax
private def left : HRef H A := ⟨0,rfl⟩
private def right : HRef H A := ⟨1,rfl⟩
private def neighbor : HRef H A := ⟨2,rfl⟩
private def old := [u 7,u 0,maximum]
private def rhs := [u 2,u 9,u 1]
private def next := [u 8,u 9]
private def hp : Heap H := (⟨old,by decide⟩,⟨rhs,by decide⟩,⟨next,by decide⟩,())
private def selected (alias : Bool) := if alias then left else right
private def state (alias : Bool) (i j : Nat) : State C Δ :=
  {storage := Storage.init C,H := H,heap := hp,env := (u i,u j,some (selected alias),some left,some left,some neighbor,())}
private def base (i : Nat) : Fin W := if i=0 then wmod 16 else if i=1 then wmod 24 else wmod 32
private def machine (alias : Bool) (i j : Nat) : Machine := {Machine.init with stack := [w[77],w[88]],mem := fun a =>
  if a=0 then w[40] else if a=1 then w[32] else if a=2 then w[16] else if a=3 then w[16]
  else if a=4 then (Word.val (base (selected alias).id)) else if a=5 then (Word.val (wmod j)) else if a=6 then (Word.val (wmod i))
  else if a=15 then w[99] else if a=16 then w[3] else if a=17 then w[7] else if a=18 then w[0] else if a=19 then (Word.val wMax)
  else if a=24 then w[3] else if a=25 then w[2] else if a=26 then w[9] else if a=27 then w[1]
  else if a=32 then w[2] else if a=33 then w[8] else if a=34 then w[9] else w[0]}
private theorem refs {R : RefTy} (q : HRef H R) :
    R=A ∧ (HEq q left ∨ HEq q right ∨ HEq q neighbor) := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi;exact ⟨rfl,.inl HEq.rfl⟩
  | succ i => cases i with
    | zero => cases hi;exact ⟨rfl,.inr (.inl HEq.rfl)⟩
    | succ i => cases i with
      | zero => cases hi;exact ⟨rfl,.inr (.inr HEq.rfl)⟩
      | succ i => cases hi
private theorem no_struct {s : Name} (q : HRef H (.struct s)) : False := by
  obtain ⟨ht,_⟩ := refs q
  cases ht
private theorem heap_repr (alias : Bool) (i j : Nat) : Objects.HeapRepr hp base 8 (machine alias i j) := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · intro R q
    obtain ⟨rfl,hq|hq|hq⟩ := refs q <;> cases hq
      <;> simp only [Objects.cells,Heap.len,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn] <;> decide
  · intro R q
    obtain ⟨rfl,hq|hq|hq⟩ := refs q <;> cases hq
      <;> simp only [Objects.cells,Heap.len,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn] <;> decide
  · intro R Q q r hn
    obtain ⟨rfl,hq|hq|hq⟩ := refs q <;> cases hq
      <;> obtain ⟨rfl,hr|hr|hr⟩ := refs r <;> cases hr
      <;> first | exact (hn rfl).elim | (simp only [Objects.cells,Heap.len,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn];decide)
  · intro A E a r
    obtain ⟨rfl,hr|hr|hr⟩ := refs r <;> cases hr <;> cases a
    all_goals
      refine ⟨?_,?_,?_⟩
      · simp only [Objects.cells,Objects.header,Heap.len,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn]
        decide
      · intro hh
        simp only [Heap.len,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn]
        rfl
      · intro k v hit
        simp only [Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn] at hit
        cases k with
        | zero => cases Option.some.inj hit;exact ReprV.uint_of rfl
        | succ k => cases k with
          | zero => cases Option.some.inj hit;exact ReprV.uint_of rfl
          | succ k => cases k with
            | zero => first | (cases Option.some.inj hit;exact ReprV.uint_of rfl) | cases hit
            | succ k => cases hit
  · intro s r
    exact (no_struct r).elim
  · intro s f R r hf
    exact (no_struct r).elim
private theorem initial_repr (alias : Bool) (i j : Nat) :
    Objects.StateRepr 1 1 8 (Frag.init Δ) (state alias i j) base (machine alias i j) := by
  have hc : Sim C 1 0 (Frag.init []) (freshT C 0 W_pos ⟨0,W_pos⟩) Machine.init :=
    Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨?_,heap_repr alias i j,?_,by decide⟩
  · refine ⟨hc.store,?_,?_,hc.net,hc.netSelf,hc.bound,?_,hc.env,hc.funds,hc.oracle⟩
    · intro p idx
      cases idx with
      | here => exact ReprV.uint_of rfl
      | there idx => cases idx with
        | here => exact ReprV.uint_of rfl
        | there idx => cases idx with | there idx => cases idx with | there idx => cases idx with | there idx => cases idx with | there idx => nomatch idx
    · intro R idx hi
      cases idx with | there idx => cases idx with | there idx => cases idx with | there idx => cases idx with | there idx => cases idx with | there idx => cases idx with | there idx => nomatch idx
    · intro R idx hi
      cases idx with | there idx => cases idx with | there idx => cases idx with | there idx => cases idx with | there idx => cases idx with | there idx => cases idx with | there idx => nomatch idx
  · intro R idx
    cases idx with | there idx => cases idx with
      | there idx => cases idx with
        | here => exact ⟨selected alias,rfl,rfl⟩
        | there idx => cases idx with
          | here => exact ⟨left,rfl,rfl⟩
          | there idx => cases idx with
            | here => exact ⟨left,rfl,rfl⟩
            | there idx => cases idx with
              | here => exact ⟨neighbor,rfl,rfl⟩
              | there idx => nomatch idx
private theorem allocator (alias : Bool) (i j : Nat) : Objects.AllocatorRepr hp base 8 ⟨40,by decide⟩ (machine alias i j) := by
  refine ⟨heap_repr alias i j,⟨by decide,by decide,rfl,?_⟩,?_⟩
  · intro a ha
    change 40≤a at ha
    simp only [machine,if_neg (show a≠0 by omega),if_neg (show a≠1 by omega),if_neg (show a≠2 by omega),
      if_neg (show a≠3 by omega),if_neg (show a≠4 by omega),if_neg (show a≠5 by omega),if_neg (show a≠6 by omega),
      if_neg (show a≠15 by omega),if_neg (show a≠16 by omega),if_neg (show a≠17 by omega),if_neg (show a≠18 by omega),
      if_neg (show a≠19 by omega),if_neg (show a≠24 by omega),if_neg (show a≠25 by omega),if_neg (show a≠26 by omega),
      if_neg (show a≠27 by omega),if_neg (show a≠32 by omega),if_neg (show a≠33 by omega),if_neg (show a≠34 by omega)]
  · intro R r
    obtain ⟨rfl,hr|hr|hr⟩ := refs r <;> cases hr
      <;> simp only [Objects.cells,Heap.len,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn] <;> decide
private def yi : Source.EMState E0 [] := (.nil,s0)
private def ya : Source.EMState E0 [] := ((Source.allocRef (sourceUintMemory old)).run yi).2
private def yb : Source.EMState E0 [] := ((Source.allocRef (sourceUintMemory rhs)).run ya).2
private def yc : Source.EMState E0 [] := ((Source.allocRef (sourceUintMemory next)).run yb).2
private def sy (alias : Bool) (i j : Nat) : Source.EMState E0 Γ :=
  (.cons (sourceUint (u i)) (.cons (sourceUint (u j)) (.cons (.memRef rfl (if alias then 0 else 1))
    (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (.memRef rfl 2) .nil))))),yc.2)
private abbrev SH := (Source.Heap.empty (D := E0.layout)).ty
private theorem memOK (alias : Bool) (i j : Nat) : Source.MemOK E0 SH (sy alias i j) := by
  have h0 : Source.MemOK E0 SH yi := ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have h1 := source_uint_alloc_memOK (E := E0) (Γ := []) SH old yi h0
  change Source.MemOK E0 SH ya ∧ _ at h1
  have h2 := source_uint_alloc_memOK (E := E0) (Γ := []) SH rhs ya h1.1
  change Source.MemOK E0 SH yb ∧ _ at h2
  have h3 := source_uint_alloc_memOK (E := E0) (Γ := []) SH next yb h2.1
  change Source.MemOK E0 SH yc ∧ _ at h3
  cases alias <;> exact ⟨⟨h3.1.1.1,⟨trivial,⟨trivial,⟨⟨SA,rfl,rfl⟩,⟨⟨SA,rfl,rfl⟩,⟨⟨SA,rfl,rfl⟩,⟨⟨SA,rfl,rfl⟩,trivial⟩⟩⟩⟩⟩⟩⟩,h3.1.2⟩
private theorem dst_at (alias : Bool) (i j : Nat) : SourceUintMemoryAt (sy alias i j) 0 hp left .dyn := by
  unfold SourceUintMemoryAt
  rw [MObj.elems_dyn]
  rfl
private theorem src_at (alias : Bool) (i j : Nat) : SourceUintMemoryAt (sy alias i j) (if alias then 0 else 1) hp (selected alias) .dyn := by
  cases alias <;> unfold SourceUintMemoryAt <;> rw [MObj.elems_dyn] <;> rfl
private def dr : Source.Idx Γ SA := .there (.there (.there .here))
private def sr : Source.Idx Γ SA := .there (.there .here)
private def di : Source.Idx Γ (.int .u256) := .here
private def si : Source.Idx Γ (.int .u256) := .there .here
private def dt : Idx Δ (.mem A) := .there (.there (.there .here))
private def st : Idx Δ (.mem A) := .there (.there .here)
private def it : Idx Δ (.val .uint) := .here
private def jt : Idx Δ (.val .uint) := .there .here
private def out (v : PrimTy.uint.Denote) := hp.set left (MObj.setElem .dyn (hp.get left) 0 v)
private def target (alias : Bool) (j : Nat) (v : PrimTy.uint.Denote) := writeMachine (machine alias 0 j) 17 (.val (wmod v.1.toNat))
private def z (alias : Bool) (j : Nat) (v : PrimTy.uint.Denote) : Source.EMState E0 Γ :=
  ((sy alias 0 j).1,{(sy alias 0 j).2 with heap := (sy alias 0 j).2.heap.write 0 (sourceUintMemory (old.set 0 v)) (by rfl)})

private theorem source_known (p : Roadmap.Pipeline) (fuel : Nat) (alias : Bool) :
    let j := if alias then 1 else 0
    let v := if alias then u 0 else u 2
    (Source.evalE (G0 p) F0 (fuel+4) (sourceUintReadAssign dr sr di si)).run (sy alias 0 j)=
      (.ok (.val (sourceUint v)),z alias j v) := by
  cases alias <;> simp only [Bool.false_eq_true,if_false,if_true]
  all_goals
    rw [sourceUintReadAssign,Source.evalE,Source.Hoare.run_bind]
  · rw [(src_at false 0 0).eval_index (G0 p) F0 (fuel+1) sr si (u 0) rfl rfl (by simp only [Heap.len,Heap.get,Objs.get,hp,left,right,MObj.elems_dyn];decide)]
    simp only [Heap.get,Objs.get,hp,left,right,MObj.elems_dyn]
    rw [Source.Hoare.run_bind,(dst_at false 0 0).eval_index_loc (G0 p) F0 (fuel+1) dr di (u 0) rfl rfl (by simp only [Heap.len,Heap.get,Objs.get,hp,left,right,MObj.elems_dyn];decide)]
    obtain ⟨ht,wr⟩ := source_uint_write (sy false 0 0) 0 old (by simpa only [SourceUintMemoryAt,Heap.get,Objs.get,hp,left,MObj.elems_dyn] using dst_at false 0 0) 0 (by decide) (u 2)
    change ((Source.memSet 0 0 (sourceUint (u 2))) >>= fun _ => pure (Source.RVal.val (sourceUint (u 2)))).run _=_
    rw [Source.Hoare.run_bind,wr]
    rfl
  · rw [(src_at true 0 1).eval_index (G0 p) F0 (fuel+1) sr si (u 1) rfl rfl (by simp only [Heap.len,Heap.get,Objs.get,hp,left,right,MObj.elems_dyn];decide)]
    simp only [Heap.get,Objs.get,hp,left,right,MObj.elems_dyn]
    rw [Source.Hoare.run_bind,(dst_at true 0 1).eval_index_loc (G0 p) F0 (fuel+1) dr di (u 0) rfl rfl (by simp only [Heap.len,Heap.get,Objs.get,hp,left,right,MObj.elems_dyn];decide)]
    obtain ⟨ht,wr⟩ := source_uint_write (sy true 0 1) 0 old (by simpa only [SourceUintMemoryAt,Heap.get,Objs.get,hp,left,MObj.elems_dyn] using dst_at true 0 1) 0 (by decide) (u 0)
    change ((Source.memSet 0 0 (sourceUint (u 0))) >>= fun _ => pure (Source.RVal.val (sourceUint (u 0)))).run _=_
    rw [Source.Hoare.run_bind,wr]
    rfl

private theorem read_run (m : Machine) (a k v : Fin W) (hk : k.val<3) (hs : a.val+1+k.val<W)
    (hp : m.mem 4=.val a) (hi : m.mem 5=.val k) (hh : m.mem a.val=w[3])
    (hv : m.mem (a.val+1+k.val)=.val v) :
    run ([.mload 4] ++ [.mload 5] ++ Objects.readCode (.dyn : ArrTy A (.prim .uint))) m=.ok (m.push (.val v)) 0 := by
  change run ([.mload 4] ++ ([.mload 5] ++ Objects.readCode (.dyn : ArrTy A (.prim .uint)))) m=_
  rw [run_append_ok (show run [.mload 4] m=.ok (m.push (.val a)) 0 from by change Out.ok (m.push (m.mem 4)) 0=_;rw [hp])]
  rw [run_append_ok (show run [.mload 5] (m.push (.val a))=.ok ((m.push (.val a)).push (.val k)) 0 from by change Out.ok ((m.push (.val a)).push (m.mem 5)) 0=_;rw [hi])]
  have addr := arrayAddrStack_run m a k 3 (by decide) hh
  rw [if_pos hk] at addr
  change run (arrayAddrStackCode ++ [.mloadAt]) ((m.push (.val a)).push (.val k))=_
  rw [run_append_ok addr]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt hs,Out.ok_bind,exec_nil,hv,Machine.next]

private theorem write_run (m : Machine) (v : Fin W) (hp : m.mem 3=w[16]) (hi : m.mem 6=w[0])
    (hh : m.mem 16=w[3]) :
    run ([.mload 3] ++ [.mload 6] ++ Objects.writeCode (.dyn : ArrTy A (.prim .uint))) (m.push (.val v))=
      .ok (writeMachine m 17 (.val v)) 0 := by
  change run ([.mload 3] ++ ([.mload 6] ++ Objects.writeCode (.dyn : ArrTy A (.prim .uint)))) _=_
  rw [run_append_ok (show run [.mload 3] (m.push (.val v))=.ok ((m.push (.val v)).push w[16]) 0 from by change Out.ok ((m.push (.val v)).push (m.mem 3)) 0=_;rw [hp])]
  rw [run_append_ok (show run [.mload 6] ((m.push (.val v)).push w[16])=.ok (((m.push (.val v)).push w[16]).push w[0]) 0 from by change Out.ok (((m.push (.val v)).push w[16]).push (m.mem 6)) 0=_;rw [hi])]
  have addr := arrayAddrStack_run (m.push (.val v)) ⟨16,by decide⟩ ⟨0,by decide⟩ 3 (by decide) hh
  rw [if_pos (by decide)] at addr
  change run (arrayAddrStackCode ++ [.mstoreAt]) (((m.push (.val v)).push w[16]).push w[0])=_
  rw [run_append_ok addr]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt (show 16+1+0<W from by decide),Out.ok_bind,exec_nil,writeMachine]

private theorem code_shape : uintReadAssignCode (C := C) 1 dt st it jt =
    ([.mload 4] ++ [.mload 5] ++ Objects.readCode (.dyn : ArrTy A (.prim .uint))) ++
      ([.mload 3] ++ [.mload 6] ++ Objects.writeCode (.dyn : ArrTy A (.prim .uint))) := by
  rfl

private theorem word_known (alias : Bool) :
    let j := if alias then 1 else 0
    let v := if alias then u 0 else u 2
    Evm.run (uintReadAssignCode (C := C) 1 dt st it jt) (machine alias 0 j)=.ok (target alias j v) 0 := by
  cases alias <;> simp only [Bool.false_eq_true,if_false,if_true]
  all_goals rw [code_shape]
  · rw [run_append_ok (read_run (machine false 0 0) (wmod 24) (wmod 0) (wmod 2) (by decide) (by decide) rfl rfl rfl rfl)]
    exact write_run _ _ rfl rfl rfl
  · rw [run_append_ok (read_run (machine true 0 1) (wmod 16) (wmod 1) (wmod 0) (by decide) (by decide) rfl rfl rfl rfl)]
    exact write_run _ _ rfl rfl rfl

/-- Distinct-root and same-object aliases instantiate the full actual
Source/intrinsic/word theorem. No initial RHS scalar local supplies the result. -/
theorem computed_rhs_client (p : Roadmap.Pipeline) (fuel nps : Nat) (alias : Bool) :
    let j := if alias then 1 else 0
    let v := if alias then u 0 else u 2
    (Source.evalE (G0 p) F0 (fuel+4) (sourceUintReadAssign dr sr di si)).run (sy alias 0 j)=
      (.ok (.val (sourceUint v)),z alias j v) ∧
    Stmt.run (state alias 0 j) (.assignMem (.index .dyn (.var dt rfl) (.simple (.local it)))
      (.val (.readMem (.index .dyn (.var st rfl) (.simple (.local jt))))))=
        .ok ⟨(state alias 0 j).withHeap (out v),List.prefix_refl _⟩ ∧
    Evm.run (uintReadAssignCode (C := C) 1 dt st it jt) (machine alias 0 j)=.ok (target alias j v) 0 ∧
    SourceUintMemoryAt (z alias j v) 0 (out v) left .dyn ∧
    Source.MemOK E0 SH (z alias j v) ∧
    Objects.StateRepr 1 1 8 (Frag.init Δ) ((state alias 0 j).withHeap (out v)) base (target alias j v) ∧
    Objects.AllocatorRepr (out v) base 8 ⟨40,by decide⟩ (target alias j v) ∧
    (target alias j v).stack=[w[77],w[88]] := by
  cases alias <;> simp only [Bool.false_eq_true,if_false,if_true]
  case false =>
    have result := source_uint_read_assign_word (G0 p) F0 fuel nps (sy false 0 0) (state false 0 0)
      left right 0 1 (dst_at false 0 0) (src_at false 0 0) dr sr di si dt st it jt (u 0) (u 0)
      rfl rfl rfl rfl rfl rfl rfl rfl (by simp only [Heap.len,state,Heap.get,Objs.get,hp,left,right,MObj.elems_dyn];decide) (by simp only [Heap.len,state,Heap.get,Objs.get,hp,left,right,MObj.elems_dyn];decide) (initial_repr false 0 0) rfl rfl SH (memOK false 0 0)
    obtain ⟨q,s,t,write,source,statement,native,word,new,mok,represented,stack,alloc,locals,oldframe,other,ex,ev,logs,fn⟩ := result
    simp only [state,Heap.get,Objs.get,hp,left,right,MObj.elems_dyn] at write source
    have knownWrite : hp.writeAddr (.index left .dyn (u 0)) (u 2)=some (out (u 2)) := by
      simp only [out,Heap.writeAddr,Heap.setIndex,Heap.len,Heap.get,Objs.get,hp,left,right,MObj.elems_dyn,MObj.setElem_dyn]
      rw [show (u 0).val.toNat=0 from by decide]
      simp only [show 0<old.length from by decide,↓reduceDIte,↓reduceIte]
    have qeq : q=out (u 2) := Option.some.inj (write.symm.trans knownWrite)
    subst q
    have seq : s=z false 0 (u 2) := by
      have known : (Source.evalE (G0 p) F0 (fuel+4) (sourceUintReadAssign dr sr di si)).run (sy false 0 0)=
          (.ok (.val (sourceUint (u 2))),z false 0 (u 2)) := source_known p fuel false
      exact congrArg Prod.snd (source.symm.trans known)
    subst s
    have expected : Evm.run (uintReadAssignCode (C := C) 1 dt st it jt) (machine false 0 0)=.ok (target false 0 (u 2)) 0 := word_known false
    have teq : t=target false 0 (u 2) := (Evm.Out.ok.inj (word.symm.trans expected)).1
    subst t
    exact ⟨source,native,word,new,mok,represented,alloc _ (by decide) (allocator false 0 0),rfl⟩
  case true =>
    have result := source_uint_read_assign_word (G0 p) F0 fuel nps (sy true 0 1) (state true 0 1)
      left left 0 0 (dst_at true 0 1) (src_at true 0 1) dr sr di si dt st it jt (u 0) (u 1)
      rfl rfl rfl rfl rfl rfl rfl rfl (by simp only [Heap.len,state,Heap.get,Objs.get,hp,left,right,MObj.elems_dyn];decide) (by simp only [Heap.len,state,Heap.get,Objs.get,hp,left,right,MObj.elems_dyn];decide) (initial_repr true 0 1) rfl rfl SH (memOK true 0 1)
    obtain ⟨q,s,t,write,source,statement,native,word,new,mok,represented,stack,alloc,locals,oldframe,other,ex,ev,logs,fn⟩ := result
    simp only [state,Heap.get,Objs.get,hp,left,right,MObj.elems_dyn] at write source
    have knownWrite : hp.writeAddr (.index left .dyn (u 0)) (u 0)=some (out (u 0)) := by
      simp only [out,Heap.writeAddr,Heap.setIndex,Heap.len,Heap.get,Objs.get,hp,left,right,MObj.elems_dyn,MObj.setElem_dyn]
      rw [show (u 0).val.toNat=0 from by decide]
      simp only [show 0<old.length from by decide,↓reduceDIte,↓reduceIte]
    have qeq : q=out (u 0) := Option.some.inj (write.symm.trans knownWrite)
    subst q
    have seq : s=z true 1 (u 0) := by
      have known : (Source.evalE (G0 p) F0 (fuel+4) (sourceUintReadAssign dr sr di si)).run (sy true 0 1)=
          (.ok (.val (sourceUint (u 0))),z true 1 (u 0)) := source_known p fuel true
      exact congrArg Prod.snd (source.symm.trans known)
    subst s
    have expected : Evm.run (uintReadAssignCode (C := C) 1 dt st it jt) (machine true 0 1)=.ok (target true 1 (u 0)) 0 := word_known true
    have teq : t=target true 1 (u 0) := (Evm.Out.ok.inj (word.symm.trans expected)).1
    subst t
    exact ⟨source,native,word,new,mok,represented,alloc _ (by decide) (allocator true 0 1),rfl⟩

/-- The actual expression certificate also yields an executed statement with
its original parameter count; Source local/context preservation is explicit. -/
theorem computed_rhs_statement (p : Roadmap.Pipeline) (fuel nps : Nat) (alias : Bool) :
    let j := if alias then 1 else 0
    let v := if alias then u 0 else u 2
    (Source.execS (G0 p) F0 (fuel+5) nps none (.expr (sourceUintReadAssign dr sr di si) :
      Source.RStmt E0 [] false .body Γ Γ) (sy alias 0 j).1).run (.nil,(sy alias 0 j).2)=
        (.ok (.normal (sy alias 0 j).1),(.nil,(z alias j v).2)) := by
  exact source_expr_statement_run (G0 p) F0 (fuel+4) nps _ _ _ _ (source_known p fuel alias)

private def cells : List Nat := [0,1,2,3,4,5,6,7,15,16,17,18,19,24,25,26,27,32,33,34]
private def words (m : Machine) := cells.map m.mem
private def objects (q : Heap H) := [MObj.elems .dyn (q.get left),MObj.elems .dyn (q.get right),MObj.elems .dyn (q.get neighbor)]
private def sourceObjects (y : Source.EMState E0 Γ) := [y.2.heap.get 0,y.2.heap.get 1,y.2.heap.get 2]

/-- Every represented word and all three object payloads are retained in order,
including the guard, free pointer, headers, maximum word and untouched cell7. -/
theorem complete_vectors (alias : Bool) :
    let j := if alias then 1 else 0
    let v := if alias then u 0 else u 2
    words (machine alias 0 j) =
      [w[40],w[32],w[16],w[16],(if alias then w[16] else w[24]),(if alias then w[1] else w[0]),w[0],w[0],w[99],w[3],w[7],w[0],.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],w[9]] ∧
    words (target alias j v) =
      [w[40],w[32],w[16],w[16],(if alias then w[16] else w[24]),(if alias then w[1] else w[0]),w[0],w[0],w[99],w[3],(if alias then w[0] else w[2]),w[0],.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],w[9]] ∧
    objects hp = [old,rhs,next] ∧ objects (out v) = [old.set 0 v,rhs,next] ∧
    sourceObjects (sy alias 0 j) = [some ⟨SA,sourceUintMemory old⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory next⟩] ∧
    sourceObjects (z alias j v) = [some ⟨SA,sourceUintMemory (old.set 0 v)⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory next⟩] ∧
    (z alias j v).1=(sy alias 0 j).1 ∧
    (z alias j v).2.ex=(sy alias 0 j).2.ex ∧
    (z alias j v).2.events=(sy alias 0 j).2.events ∧
    (z alias j v).2.logs=(sy alias 0 j).2.logs ∧
    (z alias j v).2.fnLocals=(sy alias 0 j).2.fnLocals := by
  cases alias <;> simp only [Bool.false_eq_true,if_false,if_true]
  all_goals
    refine ⟨rfl,rfl,?_,?_,rfl,?_,rfl,rfl,rfl,rfl,rfl⟩
    · simp only [objects,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn]
    · simp only [objects,out,Heap.set,Objs.set,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn,MObj.setElem_dyn]
    · simp only [sourceObjects,z,Source.Heap.write_get,Source.Heap.write_other _ (show 1≠0 by decide),Source.Heap.write_other _ (show 2≠0 by decide)]
      rfl

/-- Scalar substitution would supply zero, whereas actual RIGHT[0] supplies
two. The separate selector control below executes the stale LEFT read (seven). The
retained LEFT alias observes the write, and RIGHT/neighbor stay unchanged. -/
theorem stale_rhs_negative :
    (MObj.elems .dyn (hp.get right))[0]'(by simp only [Heap.get,Objs.get,hp,right,MObj.elems_dyn];decide) ≠ u 0 ∧
    words (target false 0 (u 2)) ≠ words (target false 0 (u 0)) ∧
    objects (out (u 2)) ≠ objects hp ∧
    TEnv.get dt (state false 0 0).env=some left ∧
    TEnv.get (.there (.there (.there (.there .here))) : Idx Δ (.mem A)) (state false 0 0).env=some left := by
  refine ⟨?_,?_,?_,rfl,rfl⟩
  · intro h
    simp only [Heap.get,Objs.get,hp,right,MObj.elems_dyn] at h
    have neq : (u 2).val ≠ (u 0).val := by decide
    exact neq (congrArg (fun v => v.val) h)
  · intro h
    have h17 := congrArg (fun x => x[10]?) h
    change some w[2]=some w[0] at h17
    cases h17
  · intro h
    have hv := congrArg (fun x => x[0]?) h
    simp only [objects,out,Heap.set,Objs.set,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn,MObj.setElem_dyn] at hv
    have h0 := congrArg (fun x => x.bind (fun y => y[0]?)) hv
    change some (u 2)=some (u 7) at h0
    have hh := congrArg (fun x => x.map (fun v => v.val)) h0
    contradiction

/-- Actual Source reads of the initial RHS pointer versus the stale destination
pointer disagree: RIGHT[0]=2 and LEFT[0]=7 in both declared pipelines. -/
theorem actual_selector_negative (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local sr) (.local si) rfl)).run (sy false 0 0)=
      (.ok (.val (sourceUint (u 2))),sy false 0 0) ∧
    (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local dr) (.local si) rfl)).run (sy false 0 0)=
      (.ok (.val (sourceUint (u 7))),sy false 0 0) ∧
    (u 2).val≠(u 7).val := by
  refine ⟨?_,?_,by decide⟩
  · have read := (src_at false 0 0).eval_index (G0 p) F0 fuel sr si (u 0) rfl rfl
      (by simp only [Heap.len,Heap.get,Objs.get,hp,right,MObj.elems_dyn];decide)
    simpa only [Heap.get,Objs.get,hp,right,MObj.elems_dyn] using read
  · have read := (dst_at false 0 0).eval_index (G0 p) F0 fuel dr si (u 0) rfl rfl
      (by simp only [Heap.len,Heap.get,Objs.get,hp,left,MObj.elems_dyn];decide)
    simpa only [Heap.get,Objs.get,hp,left,MObj.elems_dyn] using read

/-- At a low horizon Source times out before either read or write. No target
rollback or post-revert machine is inferred from this evaluator outcome. -/
theorem early_timeout (p : Roadmap.Pipeline) :
    (Source.evalE (G0 p) F0 2 (sourceUintReadAssign dr sr di si)).run (sy false 0 0)=
      (.error .timeout,sy false 0 0) := by
  cases p <;> rfl

/-- Independent source and destination endpoint failures use the actual RHS-
first program. Source retains its evaluator state; the word revert carries no
returned machine or panic payload and is not a rollback theorem. -/
theorem endpoint_rejection (p : Roadmap.Pipeline) (badRHS : Bool) :
    let i := if badRHS then 0 else 3
    let j := if badRHS then 3 else 0
    (Source.evalE (G0 p) F0 4 (sourceUintReadAssign dr sr di si)).run (sy false i j)=
      (.error (.revert (Source.panicData .index)),sy false i j) ∧
    Stmt.run (state false i j) (.assignMem (.index .dyn (.var dt rfl) (.simple (.local it)))
      (.val (.readMem (.index .dyn (.var st rfl) (.simple (.local jt))))))=.error .revert ∧
    Evm.run (uintReadAssignCode (C := C) 1 dt st it jt) (machine false i j)=.revert := by
  let i := if badRHS then 0 else 3
  let j := if badRHS then 3 else 0
  have native : TRun.assignMem (.index .dyn (.var dt rfl) (.simple (.local it)))
      (.val (.readMem (.index .dyn (.var st rfl) (.simple (.local jt))))) (state false i j)=.error .revert := by
    have hd : TEnv.get dt (state false i j).env=some left := rfl
    have hs : TEnv.get st (state false i j).env=some right := rfl
    have hi : TEnv.get it (state false i j).env=u i := rfl
    have hj : TEnv.get jt (state false i j).env=u j := rfl
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,hd,hs,hi,hj,Heap.readAddr,bind,Except.bind,pure,Except.pure]
    cases badRHS <;> simp only [i,j,Bool.false_eq_true,if_false,if_true,state,Heap.index,Heap.writeAddr,Heap.setIndex,Heap.len,Heap.get,Objs.get,hp,left,right,MObj.elems_dyn]
    · rw [show (u 0).val.toNat=0 from by decide,show (u 3).val.toNat=3 from by decide]
      simp only [rhs,List.getElem?_cons_zero,show ¬3<old.length from by decide,↓reduceIte,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    · rw [show (u 3).val.toNat=3 from by decide]
      rfl
  have source : (Source.evalE (G0 p) F0 4 (sourceUintReadAssign dr sr di si)).run (sy false i j)=
      (.error (.revert (Source.panicData .index)),sy false i j) := by
    cases badRHS <;> cases p <;> rfl
  have pointer : Objects.PtrFrag (C := C) 1 (Frag.init Δ) (.var dt rfl) [.mload (cellOf 1 dt)] := .local dt rfl
  have valueCode : Objects.ValFrag (C := C) 1 (Frag.init Δ)
      (.readMem (.index .dyn (.var st rfl) (.simple (.local jt))))
      ([.mload (cellOf 1 st)] ++ compileVal 1 (.simple (.local jt) : Val C Δ .uint) ++ Objects.readCode (.dyn : ArrTy A (.prim .uint))) :=
    .read .dyn (.var st rfl) _ (.local st rfl) _ rfl
  have targetResult := Objects.PtrFrag.write (initial_repr false i j) .dyn pointer (.val _ _ valueCode) (.simple (.local it)) rfl
  rw [native] at targetResult
  refine ⟨source,native,?_⟩
  rcases targetResult with ⟨o,target,impossible,_⟩ | ⟨_,run⟩
  · cases impossible
  · exact run

/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.computed_rhs_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms computed_rhs_client
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.computed_rhs_statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms computed_rhs_statement
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.complete_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_vectors
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.stale_rhs_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_rhs_negative
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.early_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms early_timeout
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.endpoint_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms endpoint_rejection
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.actual_selector_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_selector_negative
end Solidity.Backend.MemoryOps.UintReadAssignmentControls
