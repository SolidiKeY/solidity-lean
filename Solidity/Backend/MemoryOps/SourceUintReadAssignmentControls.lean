import Solidity.Backend.MemoryOps.SourceUintAliasWriteRead
import Solidity.Backend.MemoryOps.SourceUintAliasWriteDelete
import Solidity.Backend.MemoryOps.SourceUintSliceCompoundRead
import Solidity.Backend.MemoryOps.SourceUintAliasDelete
import Solidity.Backend.MemoryOps.SourceUintAliasWrite
import Solidity.Backend.MemoryOps.SourceUintAlias
import Solidity.Backend.MemoryOps.SourceUintReadSequence
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

private def chainOut : Heap H := (out (u 9)).set left (MObj.setElem .dyn ((out (u 9)).get left) 1 (u 9))
private def chainSource : Source.EMState E0 Γ :=
  ((z false 1 (u 9)).1,{(z false 1 (u 9)).2 with heap := (z false 1 (u 9)).2.heap.write 0 (sourceUintMemory ((old.set 0 (u 9)).set 1 (u 9))) (by rfl)})
private def chainTarget := writeMachine (target false 1 (u 9)) 18 w[9]

private theorem out_elems (v : PrimTy.uint.Denote) : MObj.elems .dyn ((out v).get left)=old.set 0 v := by
  unfold out
  rw [Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn]
  rfl

private theorem chain_mid_at : SourceUintMemoryAt (z false 1 (u 9)) 0 (out (u 9)) left .dyn := by
  unfold SourceUintMemoryAt z out
  rw [Source.Heap.write_get,Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn]
  rfl

private theorem chain_source_first (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) F0 (fuel+4) (sourceUintReadAssign dr sr di si)).run (sy false 0 1)=
      (.ok (.val (sourceUint (u 9))),z false 1 (u 9)) := by
  rw [sourceUintReadAssign,Source.evalE,Source.Hoare.run_bind]
  rw [(src_at false 0 1).eval_index (G0 p) F0 (fuel+1) sr si (u 1) rfl rfl
    (by simp only [Heap.len,Heap.get,Objs.get,hp,right,MObj.elems_dyn];decide)]
  simp only [Heap.get,Objs.get,hp,right,MObj.elems_dyn]
  rw [Source.Hoare.run_bind,(dst_at false 0 1).eval_index_loc (G0 p) F0 (fuel+1) dr di (u 0) rfl rfl
    (by simp only [Heap.len,Heap.get,Objs.get,hp,left,MObj.elems_dyn];decide)]
  obtain ⟨ht,wr⟩ := source_uint_write (sy false 0 1) 0 old
    (by simpa only [SourceUintMemoryAt,Heap.get,Objs.get,hp,left,MObj.elems_dyn] using dst_at false 0 1) 0 (by decide) (u 9)
  change ((Source.memSet 0 0 (sourceUint (u 9))) >>= fun _ => pure (Source.RVal.val (sourceUint (u 9)))).run _=_
  rw [Source.Hoare.run_bind,wr]
  rfl

private theorem chain_source_second (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) F0 (fuel+4) (sourceUintReadAssign dr dr si di)).run (z false 1 (u 9))=
      (.ok (.val (sourceUint (u 9))),chainSource) := by
  rw [sourceUintReadAssign,Source.evalE,Source.Hoare.run_bind]
  have hlen : (out (u 9)).len left .dyn=3 := by
    change (MObj.elems .dyn ((out (u 9)).get left)).length=3
    rw [out_elems,List.length_set]
    rfl
  rw [chain_mid_at.eval_index (G0 p) F0 (fuel+1) dr di (u 0) rfl rfl (by rw [hlen];decide)]
  simp only [out_elems,show (u 0).val.toNat=0 from by decide,old,List.set,List.getElem_cons_zero]
  rw [Source.Hoare.run_bind,chain_mid_at.eval_index_loc (G0 p) F0 (fuel+1) dr si (u 1) rfl rfl (by rw [hlen];decide)]
  obtain ⟨ht,wr⟩ := source_uint_write (z false 1 (u 9)) 0 (old.set 0 (u 9))
    (by unfold z;rw [Source.Heap.write_get]) 1 (by decide) (u 9)
  change ((Source.memSet 0 1 (sourceUint (u 9))) >>= fun _ => pure (Source.RVal.val (sourceUint (u 9)))).run _=_
  rw [Source.Hoare.run_bind,wr]
  rfl

private theorem chain_word_first :
    run (uintReadAssignCode (C := C) 1 dt st it jt) (machine false 0 1)=.ok (target false 1 (u 9)) 0 := by
  rw [code_shape,run_append_ok (read_run (machine false 0 1) (wmod 24) (wmod 1) (wmod 9)
    (by decide) (by decide) rfl rfl rfl rfl)]
  exact write_run _ _ rfl rfl rfl

private theorem chain_word_second_abstract (m : Machine)
    (hp : m.mem 3=w[16]) (hi : m.mem 6=w[0]) (hk : m.mem 5=w[1])
    (hh : m.mem 16=w[3]) (hv : m.mem 17=w[9]) :
    run (uintReadAssignCode (C := C) 1 dt dt jt it) m=.ok (writeMachine m 18 w[9]) 0 := by
  have shape : uintReadAssignCode (C := C) 1 dt dt jt it=
      ([.mload 3] ++ [.mload 6] ++ Objects.readCode (.dyn : ArrTy A (.prim .uint))) ++
      ([.mload 3] ++ [.mload 5] ++ Objects.writeCode (.dyn : ArrTy A (.prim .uint))) := rfl
  have read : run ([.mload 3] ++ [.mload 6] ++ Objects.readCode (.dyn : ArrTy A (.prim .uint))) m=
      .ok (m.push w[9]) 0 := by
    change run ([.mload 3] ++ ([.mload 6] ++ Objects.readCode (.dyn : ArrTy A (.prim .uint)))) m=_
    rw [run_append_ok (show run [.mload 3] m=.ok (m.push w[16]) 0 from by change Out.ok (m.push (m.mem 3)) 0=_;rw [hp])]
    rw [run_append_ok (show run [.mload 6] (m.push w[16])=.ok ((m.push w[16]).push w[0]) 0 from by change Out.ok ((m.push w[16]).push (m.mem 6)) 0=_;rw [hi])]
    have addr := arrayAddrStack_run m ⟨16,by decide⟩ ⟨0,by decide⟩ 3 (by decide) hh
    rw [if_pos (by decide)] at addr
    change run (arrayAddrStackCode ++ [.mloadAt]) ((m.push w[16]).push w[0])=_
    rw [run_append_ok addr]
    simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt (show 16+1+0<W from by decide),Out.ok_bind,exec_nil,hv,Machine.next]
  rw [shape,run_append_ok read]
  change run ([.mload 3] ++ ([.mload 5] ++ Objects.writeCode (.dyn : ArrTy A (.prim .uint)))) (m.push w[9])=_
  rw [run_append_ok (show run [.mload 3] (m.push w[9])=.ok ((m.push w[9]).push w[16]) 0 from by change Out.ok ((m.push w[9]).push (m.mem 3)) 0=_;rw [hp])]
  rw [run_append_ok (show run [.mload 5] ((m.push w[9]).push w[16])=.ok (((m.push w[9]).push w[16]).push w[1]) 0 from by change Out.ok (((m.push w[9]).push w[16]).push (m.mem 5)) 0=_;rw [hk])]
  have addr := arrayAddrStack_run (m.push w[9]) ⟨16,by decide⟩ ⟨1,by decide⟩ 3 (by decide) hh
  rw [if_pos (by decide)] at addr
  change run (arrayAddrStackCode ++ [.mstoreAt]) (((m.push w[9]).push w[16]).push w[1])=_
  rw [run_append_ok addr]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt (show 16+1+1<W from by decide),Out.ok_bind,exec_nil,writeMachine]

private theorem chain_word_second : run (uintReadAssignCode (C := C) 1 dt dt jt it) (target false 1 (u 9))=.ok chainTarget 0 :=
  chain_word_second_abstract _ rfl rfl rfl rfl rfl

/-- A materially changed INITIAL RHS (RIGHT[1]=9) first replaces LEFT[0]=7;
the second statement reads that actual reached nine into LEFT[1], not the old
seven. Both pipelines execute one Source Items, native Prog and word append. -/
theorem reached_chain_client (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.execS (G0 p) F0 (fuel+6) nps none (.expr (sourceUintReadAssign dr sr di si) :
      Source.RStmt E0 [] false .body Γ Γ) (sy false 0 1).1).run (.nil,(sy false 0 1).2)=
        (.ok (.normal (sy false 0 1).1),(.nil,(z false 1 (u 9)).2)) ∧
    (Source.execS (G0 p) F0 (fuel+5) nps none (.expr (sourceUintReadAssign dr dr si di) :
      Source.RStmt E0 [] false .body Γ Γ) (z false 1 (u 9)).1).run (.nil,(z false 1 (u 9)).2)=
        (.ok (.normal (z false 1 (u 9)).1),(.nil,chainSource.2)) ∧
    (Source.execItems (G0 p) F0 (fuel+7) nps none
      (.stmt (.expr (sourceUintReadAssign dr sr di si)) (.stmt (.expr (sourceUintReadAssign dr dr si di)) .nil) :
        Source.RItems E0 [] false .body Γ Γ) (sy false 0 1).1).run (.nil,(sy false 0 1).2)=
          (.ok (.normal (sy false 0 1).1),(.nil,chainSource.2)) ∧
    Prog.run (state false 0 1) (.cons (.assignMem (.index .dyn (.var dt rfl) (.simple (.local it)))
      (.val (.readMem (.index .dyn (.var st rfl) (.simple (.local jt))))))
      (.cons (.assignMem (.index .dyn (.var dt rfl) (.simple (.local jt)))
        (.val (.readMem (.index .dyn (.var dt rfl) (.simple (.local it)))))) .nil))=
          .ok ⟨(state false 0 1).withHeap chainOut,List.prefix_refl _⟩ ∧
    run (uintReadAssignCode (C := C) 1 dt st it jt) (machine false 0 1)=.ok (target false 1 (u 9)) 0 ∧
    run (uintReadAssignCode (C := C) 1 dt dt jt it) (target false 1 (u 9))=.ok chainTarget 0 ∧
    run (uintReadAssignCode (C := C) 1 dt st it jt ++ uintReadAssignCode (C := C) 1 dt dt jt it) (machine false 0 1)=.ok chainTarget 0 ∧
    SourceUintMemoryAt (z false 1 (u 9)) 0 (out (u 9)) left .dyn ∧
    SourceUintMemoryAt chainSource 0 chainOut left .dyn ∧
    Source.MemOK E0 SH (z false 1 (u 9)) ∧ Source.MemOK E0 SH chainSource ∧
    Objects.StateRepr 1 1 8 (Frag.init Δ) ((state false 0 1).withHeap (out (u 9))) base (target false 1 (u 9)) ∧
    Objects.StateRepr 1 1 8 (Frag.init Δ) ((state false 0 1).withHeap chainOut) base chainTarget ∧
    Objects.AllocatorRepr chainOut base 8 ⟨40,by decide⟩ chainTarget ∧
    chainTarget.stack=[w[77],w[88]] := by
  have result := source_uint_read_assign_chain_word (G0 p) F0 fuel nps (sy false 0 1) (state false 0 1)
    left right 0 1 (dst_at false 0 1) (src_at false 0 1) dr sr di si si dt st it jt jt (u 0) (u 1) (u 1)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by simp only [Heap.len,state,Heap.get,Objs.get,hp,left,MObj.elems_dyn];decide)
    (by simp only [Heap.len,state,Heap.get,Objs.get,hp,right,MObj.elems_dyn];decide)
    (by simp only [Heap.len,state,Heap.get,Objs.get,hp,left,MObj.elems_dyn];decide)
    (initial_repr false 0 1) rfl rfl rfl SH (memOK false 0 1)
  obtain ⟨mid,out',ym,z',mm,t,hw1,hit,hw2,ss1,ss2,items,prog,w1,w2,wapp,hr1,hr2,hm1,hm2,mok1,mok2,ly1,ly2,stack,alloc,el1,el2,other,addrs,ex,ev,logs,fn⟩ := result
  simp only [state,Heap.get,Objs.get,hp,right,MObj.elems_dyn,show (u 1).val.toNat=1 from by decide,rhs,List.getElem_cons_succ,List.getElem_cons_zero] at hw1 hw2
  have firstWrite : hp.writeAddr (.index left .dyn (u 0)) (u 9)=some (out (u 9)) := by
    simp only [out,Heap.writeAddr,Heap.setIndex,Heap.len,Heap.get,Objs.get,hp,left,MObj.elems_dyn,MObj.setElem_dyn]
    rw [show (u 0).val.toNat=0 from by decide]
    simp only [show 0<old.length from by decide,↓reduceIte]
  have midEq : mid=out (u 9) := Option.some.inj (hw1.symm.trans firstWrite)
  subst mid
  have secondWrite : (out (u 9)).writeAddr (.index left .dyn (u 1)) (u 9)=some chainOut := by
    change (out (u 9)).setIndex left .dyn (u 1) (u 9)=some chainOut
    unfold Heap.setIndex
    rw [out_elems,show (u 1).val.toNat=1 from by decide]
    simp only [show 1<(old.set 0 (u 9)).length from by decide,↓reduceIte]
    rfl
  have outEq : out'=chainOut := Option.some.inj (hw2.symm.trans secondWrite)
  subst out'
  have firstSource := source_expr_statement_run (G0 p) F0 (fuel+5) nps _ _ _ _ (chain_source_first p (fuel+1))
  have midSourceEq : ym=z false 1 (u 9) :=
    Prod.ext ly1 (congrArg (fun q => q.2.2) (ss1.symm.trans firstSource))
  subst ym
  have secondSource := source_expr_statement_run (G0 p) F0 (fuel+4) nps _ _ _ _ (chain_source_second p fuel)
  have outSourceEq : z'=chainSource :=
    Prod.ext ly2 (congrArg (fun q => q.2.2) (ss2.symm.trans secondSource))
  subst z'
  have midWordEq : mm=target false 1 (u 9) := (Evm.Out.ok.inj (w1.symm.trans chain_word_first)).1
  subst mm
  have outWordEq : t=chainTarget := (Evm.Out.ok.inj (w2.symm.trans chain_word_second)).1
  subst t
  exact ⟨ss1,ss2,items,prog,w1,w2,wapp,hr1,hr2,mok1,mok2,hm1,hm2,alloc _ (by decide) (allocator false 0 1),rfl⟩

/-- Complete INITIAL/intermediate/final Source tables, native objects and all
represented words; old reference identities/locals/world are not projected away. -/
theorem reached_chain_vectors :
    words (machine false 0 1)=[w[40],w[32],w[16],w[16],w[24],w[1],w[0],w[0],w[99],w[3],w[7],w[0],.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],w[9]] ∧
    words (target false 1 (u 9))=[w[40],w[32],w[16],w[16],w[24],w[1],w[0],w[0],w[99],w[3],w[9],w[0],.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],w[9]] ∧
    words chainTarget=[w[40],w[32],w[16],w[16],w[24],w[1],w[0],w[0],w[99],w[3],w[9],w[9],.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],w[9]] ∧
    objects hp=[old,rhs,next] ∧ objects (out (u 9))=[old.set 0 (u 9),rhs,next] ∧
    objects chainOut=[(old.set 0 (u 9)).set 1 (u 9),rhs,next] ∧
    sourceObjects (sy false 0 1)=[some ⟨SA,sourceUintMemory old⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory next⟩] ∧
    sourceObjects (z false 1 (u 9))=[some ⟨SA,sourceUintMemory (old.set 0 (u 9))⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory next⟩] ∧
    sourceObjects chainSource=[some ⟨SA,sourceUintMemory ((old.set 0 (u 9)).set 1 (u 9))⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory next⟩] ∧
    chainSource.1=(sy false 0 1).1 ∧ chainSource.2.ex=(sy false 0 1).2.ex ∧
    chainSource.2.events=(sy false 0 1).2.events ∧ chainSource.2.logs=(sy false 0 1).2.logs ∧
    chainSource.2.fnLocals=(sy false 0 1).2.fnLocals ∧
    (target false 1 (u 9)).stack=[w[77],w[88]] ∧ chainTarget.stack=[w[77],w[88]] ∧
    TEnv.get dt (state false 0 1).env=some left ∧
    TEnv.get (.there (.there (.there (.there .here))) : Idx Δ (.mem A)) (state false 0 1).env=some left := by
  refine ⟨rfl,rfl,rfl,?_,?_,?_,rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · simp only [objects,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn]
  · simp only [objects,out,Heap.set,Objs.set,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn,MObj.setElem_dyn]
  · simp only [objects,chainOut,out,Heap.set,Objs.set,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn,MObj.setElem_dyn]
  · simp only [sourceObjects,z,Source.Heap.write_get,Source.Heap.write_other _ (show 1≠0 by decide),Source.Heap.write_other _ (show 2≠0 by decide)]
    rfl
  · simp only [sourceObjects,chainSource,z,Source.Heap.write_get,Source.Heap.write_other _ (show 1≠0 by decide),Source.Heap.write_other _ (show 2≠0 by decide)]
    rfl

/-- The actual read of the selected cell changes from seven to nine. Skipping
propagation or using the frozen initial seven changes a complete output vector. -/
theorem reached_chain_frozen_negative (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local dr) (.local di) rfl)).run (sy false 0 1)=
      (.ok (.val (sourceUint (u 7))),sy false 0 1) ∧
    (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local dr) (.local di) rfl)).run (z false 1 (u 9))=
      (.ok (.val (sourceUint (u 9))),z false 1 (u 9)) ∧
    words chainTarget≠words (target false 1 (u 9)) ∧
    words chainTarget≠words (writeMachine (target false 1 (u 9)) 18 w[7]) := by
  refine ⟨?_,?_,?_,?_⟩
  · have rd := (dst_at false 0 1).eval_index (G0 p) F0 fuel dr di (u 0) rfl rfl
      (by simp only [Heap.len,Heap.get,Objs.get,hp,left,MObj.elems_dyn];decide)
    simpa only [Heap.get,Objs.get,hp,left,MObj.elems_dyn] using rd
  · have rd := chain_mid_at.eval_index (G0 p) F0 fuel dr di (u 0) rfl rfl
      (by change (u 0).val.toNat<(MObj.elems .dyn ((out (u 9)).get left)).length;rw [out_elems,List.length_set];decide)
    simpa only [out_elems,show (u 0).val.toNat=0 from by decide,old,List.set,List.getElem_cons_zero] using rd
  · intro h
    have h18 := congrArg (fun xs => xs[11]?) h
    change some w[9]=some w[0] at h18
    cases h18
  · intro h
    have h18 := congrArg (fun xs => xs[11]?) h
    change some w[9]=some w[7] at h18
    cases h18

private theorem chain_source_first_three (p : Roadmap.Pipeline) :
    (Source.evalE (G0 p) F0 3 (sourceUintReadAssign dr sr di si)).run (sy false 0 1)=
      (.ok (.val (sourceUint (u 9))),z false 1 (u 9)) := by
  rw [sourceUintReadAssign,Source.evalE,Source.Hoare.run_bind]
  rw [(src_at false 0 1).eval_index (G0 p) F0 0 sr si (u 1) rfl rfl
    (by simp only [Heap.len,Heap.get,Objs.get,hp,right,MObj.elems_dyn];decide)]
  simp only [Heap.get,Objs.get,hp,right,MObj.elems_dyn]
  rw [Source.Hoare.run_bind,(dst_at false 0 1).eval_index_loc (G0 p) F0 0 dr di (u 0) rfl rfl
    (by simp only [Heap.len,Heap.get,Objs.get,hp,left,MObj.elems_dyn];decide)]
  obtain ⟨ht,wr⟩ := source_uint_write (sy false 0 1) 0 old
    (by simpa only [SourceUintMemoryAt,Heap.get,Objs.get,hp,left,MObj.elems_dyn] using dst_at false 0 1) 0 (by decide) (u 9)
  change ((Source.memSet 0 0 (sourceUint (u 9))) >>= fun _ => pure (Source.RVal.val (sourceUint (u 9)))).run _=_
  rw [Source.Hoare.run_bind,wr]
  rfl

/-- Actual short Items horizon retains the materially changed first Source
heap before the second statement times out. This is not a transaction rollback
or a claim that the independently fueled native/word program also times out. -/
theorem reached_chain_prefix_timeout (p : Roadmap.Pipeline) (nps : Nat) :
    (Source.execS (G0 p) F0 4 nps none (.expr (sourceUintReadAssign dr sr di si) : Source.RStmt E0 [] false .body Γ Γ)
      (sy false 0 1).1).run (.nil,(sy false 0 1).2)=(.ok (.normal (sy false 0 1).1),(.nil,(z false 1 (u 9)).2)) ∧
    (Source.execItems (G0 p) F0 5 nps none
      (.stmt (.expr (sourceUintReadAssign dr sr di si)) (.stmt (.expr (sourceUintReadAssign dr dr si di)) .nil) :
        Source.RItems E0 [] false .body Γ Γ) (sy false 0 1).1).run (.nil,(sy false 0 1).2)=
          (.error .timeout,(.nil,(z false 1 (u 9)).2)) := by
  have first := source_expr_statement_run (G0 p) F0 3 nps _ _ _ _ (chain_source_first_three p)
  have late : (Source.evalE (G0 p) F0 2 (sourceUintReadAssign dr dr si di)).run (z false 1 (u 9))=
      (.error .timeout,z false 1 (u 9)) := by cases p <;> rfl
  have second := source_expr_statement_error (G0 p) F0 2 nps _ _ _ _ late
  have tail : (Source.execItems (G0 p) F0 4 nps none (.stmt (.expr (sourceUintReadAssign dr dr si di)) .nil :
      Source.RItems E0 [] false .body Γ Γ) (z false 1 (u 9)).1).run (.nil,(z false 1 (u 9)).2)=
        (.error .timeout,(.nil,(z false 1 (u 9)).2)) := by
    rw [Source.execItems,Source.Hoare.run_bind,second]
  refine ⟨first,?_⟩
  rw [Source.execItems,Source.Hoare.run_bind,first]
  change (Source.execItems (G0 p) F0 4 nps none (.stmt (.expr (sourceUintReadAssign dr dr si di)) .nil :
    Source.RItems E0 [] false .body Γ Γ) (z false 1 (u 9)).1 >>= fun o => Source.EM.lift (o.up Γ)).run (.nil,(z false 1 (u 9)).2)=_
  rw [Source.Hoare.run_bind,tail]

/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.reached_chain_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_chain_vectors
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.reached_chain_frozen_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_chain_frozen_negative
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.reached_chain_prefix_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_chain_prefix_timeout
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.reached_chain_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_chain_client

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
private def aliasSource (self : Bool) : Source.Idx Γ SA :=
  if self then dr else .there (.there (.there (.there (.there .here))))
private def aliasTarget (self : Bool) : Idx Δ (.mem A) :=
  if self then dt else .there (.there (.there (.there (.there .here))))
private def aliasRef (self : Bool) : HRef H A := if self then left else neighbor
private def aliasAddress (self : Bool) : Nat := if self then 0 else 2
private def aliasState (self : Bool) : State C Δ := (state false 2 0).setLocal dt (some (aliasRef self))
private def aliasSourceState (self : Bool) : Source.EMState E0 Γ :=
  ((sy false 2 0).1.set dr (.memRef rfl (aliasAddress self)),(sy false 2 0).2)
private def aliasMachine (self : Bool) : Machine :=
  writeMachine (machine false 2 0) 3 (.val (base (aliasRef self).id))
private theorem alias_at (self : Bool) : SourceUintMemoryAt (sy false 2 0) (aliasAddress self) hp (aliasRef self) .dyn := by
  cases self <;> unfold SourceUintMemoryAt <;> rw [MObj.elems_dyn] <;> rfl

/-- Both pipelines rebind to the actual existing object, retaining strong
Objects/allocator, complete Source/native heaps, aliases and saved stack. -/
theorem dynamic_uint_alias_client (p : Roadmap.Pipeline) (fuel : Nat) (self : Bool) :
    (Source.evalE (G0 p) F0 (fuel+2) (sourceLocalAlias dr (aliasSource self))).run (sy false 2 0)=
      (.ok (.val (.memRef rfl (aliasAddress self))),aliasSourceState self) ∧
    Stmt.run (state false 2 0) (.rebindMem dt (.alias (.var (aliasTarget self) rfl)))=
      .ok ⟨aliasState self,List.prefix_refl _⟩ ∧
    run (aliasLocalCode 1 dt (aliasTarget self)) (machine false 2 0)=.ok (aliasMachine self) 0 ∧
    SourceUintMemoryAt (aliasSourceState self) (aliasAddress self) (aliasState self).heap (aliasRef self) .dyn ∧
    Source.MemOK E0 SH (aliasSourceState self) ∧
    Objects.StateRepr 1 1 8 (Frag.init Δ) (aliasState self) base (aliasMachine self) ∧
    Objects.AllocatorRepr (aliasState self).heap base 8 ⟨40,by decide⟩ (aliasMachine self) ∧
    Objects.KeepsAllocator 1 8 (state false 2 0) base (machine false 2 0) (aliasState self) (aliasMachine self) ∧
    (aliasSourceState self).1.get dr=.memRef rfl (aliasAddress self) ∧
    TEnv.get dt (aliasState self).env=some (aliasRef self) ∧
    (aliasSourceState self).2=(sy false 2 0).2 ∧ (aliasState self).heap=hp ∧
    (aliasMachine self).stack=[w[77],w[88]] ∧ (aliasMachine self).mem 0=w[40] := by
  first
  | solve | simp only [] | omega
  | have result := source_uint_alias_word (G0 p) F0 fuel (sy false 2 0) dr (aliasSource self)
      (aliasAddress self) (by cases self <;> rfl) SH (memOK false 2 0)
      (state false 2 0) dt (aliasTarget self) (aliasRef self) (by cases self <;> rfl) (alias_at self)
      (initial_repr false 2 0) (allocator false 2 0) (by decide)
    obtain ⟨first,stmt,native,word,new,mok,repr,alloc,keeps,selected,targetSelected,globals,heap,stack,free,other,targetOther,objects,source⟩ := result
    exact ⟨first,native,word,new,mok,repr,alloc,keeps,selected,targetSelected,globals,heap,stack,free⟩

/-- Complete ordered word/object/local/world vectors, including header lengths,
free pointer, neighbor, maximum word, guard and saved stack. -/
theorem dynamic_uint_alias_vectors (self : Bool) :
    words (machine false 2 0)=
      [w[40],w[32],w[16],w[16],w[24],w[0],w[2],w[0],w[99],w[3],w[7],w[0],.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],w[9]] ∧
    words (aliasMachine self)=
      [w[40],w[32],w[16],(if self then w[16] else w[32]),w[24],w[0],w[2],w[0],w[99],w[3],w[7],w[0],.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],w[9]] ∧
    objects (aliasState self).heap=[old,rhs,next] ∧
    sourceObjects (sy false 2 0)=[some ⟨SA,sourceUintMemory old⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory next⟩] ∧
    sourceObjects (aliasSourceState self)=[some ⟨SA,sourceUintMemory old⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory next⟩] ∧
    (aliasSourceState self).1=.cons (sourceUint (u 2)) (.cons (sourceUint (u 0)) (.cons (.memRef rfl 1)
      (.cons (.memRef rfl (aliasAddress self)) (.cons (.memRef rfl 0) (.cons (.memRef rfl 2) .nil))))) ∧
    (aliasSourceState self).2.ex=(sy false 2 0).2.ex ∧ (aliasSourceState self).2.events=(sy false 2 0).2.events ∧
    (aliasSourceState self).2.logs=(sy false 2 0).2.logs ∧ (aliasSourceState self).2.fnLocals=(sy false 2 0).2.fnLocals := by
  first
  | solve | simp only [] | omega
  | cases self <;> refine ⟨rfl,rfl,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
    all_goals simp only [objects,aliasState,State.setLocal,state,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn]

/-- Actual alias->read Items and complete word append reject index2 on the
reached length2 neighbor. The old length3 alias still reads maximum at2. -/
theorem dynamic_uint_alias_bounds (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) F0 (fuel+3) (.indexArray (.local dr) (.local di) rfl)).run (aliasSourceState false)=
      (.error (.revert (Source.panicData .index)),aliasSourceState false) ∧
    (Source.execItems (G0 p) F0 (fuel+6) Γ.length none
      (.stmt (.expr (sourceLocalAlias dr (aliasSource false)))
        (.stmt (.expr (.indexArray (.local dr) (.local di) rfl)) .nil) : Source.RItems E0 [] false .body Γ Γ)
        (sy false 2 0).1).run (.nil,(sy false 2 0).2)=
      (.error (.revert (Source.panicData .index)),(.nil,(aliasSourceState false).2)) ∧
    (Val.readMem (.index .dyn (.var dt rfl) (.simple (.local it))) : Val C Δ .uint).evalT (aliasState false)=.error .revert ∧
    run (readLocalCode 1 dt (.simple (.local it) : Val C Δ .uint)) (aliasMachine false)=.revert ∧
    run (aliasLocalCode 1 dt (aliasTarget false)++readLocalCode 1 dt (.simple (.local it) : Val C Δ .uint)) (machine false 2 0)=.revert ∧
    (Source.evalE (G0 p) F0 (fuel+2)
      (.indexArray (.local (.there (.there (.there (.there .here)))) : Source.RExpr E0 Γ SA) (.local di) rfl)).run (aliasSourceState false)=
      (.ok (.val (sourceUint maximum)),aliasSourceState false) := by
  first
  | solve | simp only [] | omega
  | have selected := source_uint_alias_read_bounds_word (G0 p) F0 fuel (sy false 2 0) dr (aliasSource false) di 2 (u 2)
      rfl rfl SH (memOK false 2 0) (state false 2 0) dt (aliasTarget false) it neighbor rfl rfl
      (alias_at false) (by simp only [Heap.len,Heap.get,Objs.get,hp,neighbor,MObj.elems_dyn];decide)
      (initial_repr false 2 0) (allocator false 2 0) (by decide) rfl
    obtain ⟨first,native,word,second,items,invalid,readCode,whole,new,mok,repr,alloc,keeps,globals,heap,stack,free⟩ := selected
    have oldNative : MObj.elems .dyn (hp.get left)=old := by rw [MObj.elems_dyn];rfl
    have oldBound : (u 2).1.toNat<hp.len left .dyn := by
      change (u 2).1.toNat<(MObj.elems .dyn (hp.get left)).length
      rw [oldNative]
      decide
    have oldSource : SourceUintMemoryAt (aliasSourceState false) 0 hp left .dyn := dst_at false 2 0
    have read := oldSource.eval_index (G0 p) F0 fuel (.there (.there (.there (.there .here)))) di (u 2) rfl rfl oldBound
    simp only [oldNative] at read
    exact ⟨second,items,invalid,readCode,whole,read⟩

/-- Self-alias leaves actual locals/environment/memory untouched. Low Source
alias fuel returns timeout before rebinding; no word post-revert state exists. -/
theorem dynamic_uint_alias_self_timeout (p : Roadmap.Pipeline) :
    (aliasSourceState true).1=(sy false 2 0).1 ∧
    (aliasState true).env=(state false 2 0).env ∧
    (∀ a,(aliasMachine true).mem a=(machine false 2 0).mem a) ∧
    (Source.evalE (G0 p) F0 1 (sourceLocalAlias dr (aliasSource false))).run (sy false 2 0)=
      (.error .timeout,sy false 2 0) ∧
    words (aliasMachine false)≠words (machine false 2 0) := by
  first
  | solve | simp only [] | omega
  | refine ⟨rfl,rfl,?_,source_local_alias_low_horizon (G0 p) F0 (sy false 2 0) dr (aliasSource false) 1 (by decide),by decide⟩
    intro a
    by_cases h : a=3
    · subst a;rfl
    · simp only [aliasMachine,writeMachine,upd,if_neg h]

/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_client
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_vectors
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_bounds
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_self_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_self_timeout

/-- Actual successful word read through the retained old alias returns max;
reading the rebound pointer at the same index instead reverts. -/
theorem dynamic_uint_alias_stale_word :
    run (readLocalCode (C := C) 1 (.there (.there (.there (.there .here)))) (.simple (.local it)))
      (aliasMachine false)=.ok ((aliasMachine false).push (.val wMax)) 0 := by
  first
  | solve | simp only [] | omega
  | let oldAlias : Idx Δ (.mem A) := .there (.there (.there (.there .here)))
    have repr : Objects.StateRepr 1 1 8 (Frag.init Δ) (aliasState false) base (aliasMachine false) :=
      (dynamic_uint_alias_client .legacy 0 false).2.2.2.2.2.1
    have root : TEnv.get oldAlias (aliasState false).env=some left := rfl
    have index : TEnv.get it (aliasState false).env=u 2 := rfl
    have selected : (aliasState false).heap.readAddr (.index left .dyn (u 2))=some maximum := by
      change (MObj.elems .dyn (hp.get left))[(u 2).1.toNat]?=some maximum
      rw [MObj.elems_dyn]
      rfl
    have typed : (Val.readMem (.index .dyn (.var oldAlias rfl) (.simple (.local it))) : Val C Δ .uint).evalT (aliasState false)=.ok maximum := by
      simp only [Val.evalT,MLoc.addrT,MPath.mvalT,Simple.evalT,root,index,selected,
        TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have cert := Objects.PtrFrag.readPrimitive repr (Objects.PtrFrag.local oldAlias rfl)
      (.dyn : ArrTy A (.prim .uint)) (.simple (.local it) : Val C Δ .uint) rfl
    change ValOutT .uint _ (run (readLocalCode 1 oldAlias (.simple (.local it))) (aliasMachine false)) (aliasMachine false) at cert
    rw [typed] at cert
    rcases cert with ⟨v,w,value,representation,code⟩ | ⟨bad,_⟩
    · cases Except.ok.inj value
      obtain ⟨n,hn,number,word⟩ := representation.uint_inv
      have nMax : n=wMax.val := Int.ofNat.inj (number.symm.trans (rfl : maximum.1=(wMax.val : Int)))
      have wordMax : w=.val wMax := word.trans (congrArg Word.val (Fin.ext nMax))
      simpa only [wordMax] using code
    · cases bad

/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_stale_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_stale_word

/-- A populated existing shorter object is selected before the material write.
Both pipeline parameters and self-alias are actual clients, with the strong
word representation retained; no post-error target state is claimed. -/
theorem dynamic_uint_alias_write_client (p : Roadmap.Pipeline) (fuel : Nat) (self : Bool) :
    ∃ (out : Heap H) (z : Source.EMState E0 Γ) (target : Machine),
      (Source.execItems (G0 p) F0 (fuel+6) Γ.length none
        (.stmt (.expr (sourceLocalAlias dr (aliasSource self)))
          (.stmt (.expr (sourceUintIndexedAssign dr di si)) .nil) : Source.RItems E0 [] false .body Γ Γ)
          (sy false 1 42).1).run (.nil,(sy false 1 42).2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run (state false 1 42) (.cons (.rebindMem dt (.alias (.var (aliasTarget self) rfl)))
        (.cons (.assignMem (.index .dyn (.var dt rfl) (.simple (.local it))) (.val (.simple (.local jt)))) .nil))=
        .ok ⟨((state false 1 42).setLocal dt (some (aliasRef self))).withHeap out,List.prefix_refl _⟩ ∧
      run (aliasLocalCode 1 dt (aliasTarget self)++uintAliasWriteCode (C := C) 1 dt it jt)
        (machine false 1 42)=.ok target 0 ∧
      Objects.StateRepr 1 1 8 (Frag.init Δ)
        (((state false 1 42).setLocal dt (some (aliasRef self))).withHeap out) base target ∧
      Objects.AllocatorRepr out base 8 ⟨40,by decide⟩ target ∧
      SourceUintMemoryAt z (aliasAddress self) out (aliasRef self) .dyn ∧
      Source.MemOK E0 SH z ∧
      MObj.elems .dyn (out.get (aliasRef self))=(if self then old else next).set 1 (u 42) ∧
      out.get right=hp.get right ∧
      (self=false → out.get left=hp.get left ∧ z.2.heap.get 0=(sy false 1 42).2.heap.get 0) ∧
      z.1=(sy false 1 42).1.set dr (.memRef rfl (aliasAddress self)) ∧
      z.2.ex=(sy false 1 42).2.ex ∧ z.2.events=(sy false 1 42).2.events ∧
      z.2.logs=(sy false 1 42).2.logs ∧ z.2.fnLocals=(sy false 1 42).2.fnLocals ∧
      target.stack=[w[77],w[88]] ∧ target.mem 0=w[40] := by
  first
  | solve | simp only [] | omega
  | have initial : SourceUintMemoryAt (sy false 1 42) (aliasAddress self) hp (aliasRef self) .dyn := by
      cases self <;> unfold SourceUintMemoryAt <;> rw [MObj.elems_dyn] <;> rfl
    have sourceRoot : (sy false 1 42).1.get (aliasSource self)=.memRef rfl (aliasAddress self) := by cases self <;> rfl
    have targetRoot : TEnv.get (aliasTarget self) (state false 1 42).env=some (aliasRef self) := by cases self <;> rfl
    have bound : (u 1).1.toNat<hp.len (aliasRef self) .dyn := by
      cases self <;> simp only [aliasRef,if_false,if_true,Heap.len,Heap.get,Objs.get,hp,left,neighbor,MObj.elems_dyn] <;> decide
    obtain ⟨out,z,target,first,second,items,aliasNative,native,prog,write,selected,new,mok,aliasCode,code,whole,repr,alloc,keep,stack,free,values,locals,rootS,rootT,sourceOther,frames,sourceFrames,ex,events,logs,fn⟩ :=
      source_uint_alias_assign_word (G0 p) F0 fuel (sy false 1 42) dr (aliasSource self) di si
        (aliasAddress self) (u 1) (u 42) sourceRoot rfl rfl SH (memOK false 1 42)
        (state false 1 42) dt (aliasTarget self) it jt (aliasRef self) targetRoot rfl rfl initial bound
        (initial_repr false 1 42) (allocator false 1 42) (by decide) rfl rfl
    have contents : MObj.elems .dyn ((state false 1 42).heap.get (aliasRef self))=(if self then old else next) := by
      cases self <;> rw [MObj.elems_dyn] <;> rfl
    refine ⟨out,z,target,items,prog,whole,repr,alloc,new,mok,?_,?_,?_,locals,ex,events,logs,fn,stack,free⟩
    · simpa only [contents,show (u 1).1.toNat=1 from by decide] using values
    · exact frames _ right (by cases self <;> decide)
    · intro eq
      subst self
      exact ⟨frames _ left (by decide),sourceFrames 0 (by decide)⟩

/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_write_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_write_client

private def mutationMid (self : Bool) : Source.EMState E0 Γ :=
  ((sy false 1 42).1.set dr (.memRef rfl (aliasAddress self)),(sy false 1 42).2)
private def mutationNative (self : Bool) : Heap H :=
  hp.set (aliasRef self) (MObj.setElem .dyn (hp.get (aliasRef self)) 1 (u 42))
private def mutationFinal (self : Bool) : Source.EMState E0 Γ :=
  ((mutationMid self).1,{(mutationMid self).2 with heap := (mutationMid self).2.heap.write (aliasAddress self) (sourceUintMemory ((if self then old else next).set 1 (u 42))) (by cases self <;> rfl)})
private def mutationPointer (self : Bool) : Machine :=
  writeMachine (machine false 1 42) 3 (.val (base (aliasRef self).id))
private def mutationTarget (self : Bool) : Machine :=
  writeMachine (mutationPointer self) ((base (aliasRef self).id).val+2) w[42]

private theorem mutation_source (p : Roadmap.Pipeline) (fuel : Nat) (self : Bool) :
    (Source.evalE (G0 p) F0 (fuel+3) (sourceUintIndexedAssign dr di si)).run (mutationMid self)=
      (.ok (.val (sourceUint (u 42))),mutationFinal self) := by
  first
  | solve | simp only [] | omega
  | have initial : SourceUintMemoryAt (mutationMid self) (aliasAddress self) hp (aliasRef self) .dyn := by
      cases self <;> unfold SourceUintMemoryAt <;> rw [MObj.elems_dyn] <;> rfl
    have contents : (mutationMid self).2.heap.get (aliasAddress self)=
        some ⟨SA,sourceUintMemory (if self then old else next)⟩ := by cases self <;> rfl
    obtain ⟨ht,write⟩ := source_uint_write (mutationMid self) (aliasAddress self) (if self then old else next)
      contents 1 (by cases self <;> decide) (u 42)
    have actual : (Source.writeLoc F0 (fuel+2) (.mem (aliasAddress self) (u 1).1.toNat) (sourceUint (u 42))).run
        (mutationMid self)=(.ok (),mutationFinal self) := write
    exact initial.eval_assign_of_run (G0 p) F0 fuel dr di si (u 1) (u 42)
      (by cases self <;> rfl) rfl rfl
      (by cases self <;> simp only [aliasRef,if_true,Heap.len,Heap.get,Objs.get,hp,left,neighbor,MObj.elems_dyn] <;> decide) actual

private theorem write_one_run (m : Machine) (a : Fin W) (n : Nat) (hn : n<W) (hi : 1<n)
    (space : a.val+2<W) (hv : m.mem 5=w[42]) (hp : m.mem 3=.val a)
    (hx : m.mem 6=w[1]) (hh : m.mem a.val=.val (wmod n)) :
    run (uintAliasWriteCode (C := C) 1 dt it jt) m=.ok (writeMachine m (a.val+2) w[42]) 0 := by
  first
  | solve | simp only [] | omega
  | change run ([.mload 5]++([.mload 3]++([.mload 6]++Objects.writeCode (.dyn : ArrTy A (.prim .uint))))) m=_
    rw [run_append_ok (show run [.mload 5] m=.ok (m.push w[42]) 0 from by change Out.ok (m.push (m.mem 5)) 0=_;rw [hv])]
    rw [run_append_ok (show run [.mload 3] (m.push w[42])=.ok ((m.push w[42]).push (.val a)) 0 from by
      change Out.ok ((m.push w[42]).push (m.mem 3)) 0=_;rw [hp])]
    rw [run_append_ok (show run [.mload 6] ((m.push w[42]).push (.val a))=
        .ok (((m.push w[42]).push (.val a)).push w[1]) 0 from by
      change Out.ok (((m.push w[42]).push (.val a)).push (m.mem 6)) 0=_;rw [hx])]
    have addr := arrayAddrStack_run (m.push w[42]) a ⟨1,by decide⟩ n hn hh
    rw [if_pos hi] at addr
    change run (arrayAddrStackCode++[.mstoreAt]) (((m.push w[42]).push (.val a)).push w[1])=_
    rw [run_append_ok addr]
    simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt space,Out.ok_bind,exec_nil,writeMachine]

private theorem mutation_word (self : Bool) :
    run (uintAliasWriteCode (C := C) 1 dt it jt) (mutationPointer self)=.ok (mutationTarget self) 0 := by
  first
  | solve | simp only [] | omega
  | exact write_one_run (mutationPointer self) (base (aliasRef self).id) (if self then 3 else 2)
      (by cases self <;> decide) (by cases self <;> decide) (by cases self <;> decide)
      (by cases self <;> rfl) (by cases self <;> rfl) (by cases self <;> rfl) (by cases self <;> rfl)

/-- Concrete final identities come from determinism of the SAME Source,
native and word executions returned by the generic producer. -/
theorem dynamic_uint_alias_write_concrete (p : Roadmap.Pipeline) (fuel : Nat) (self : Bool) :
    (Source.execItems (G0 p) F0 (fuel+6) Γ.length none
      (.stmt (.expr (sourceLocalAlias dr (aliasSource self)))
        (.stmt (.expr (sourceUintIndexedAssign dr di si)) .nil) : Source.RItems E0 [] false .body Γ Γ)
        (sy false 1 42).1).run (.nil,(sy false 1 42).2)=
      (.ok (.normal (mutationFinal self).1),(.nil,(mutationFinal self).2)) ∧
    Prog.run (state false 1 42) (.cons (.rebindMem dt (.alias (.var (aliasTarget self) rfl)))
      (.cons (.assignMem (.index .dyn (.var dt rfl) (.simple (.local it))) (.val (.simple (.local jt)))) .nil))=
      .ok ⟨((state false 1 42).setLocal dt (some (aliasRef self))).withHeap (mutationNative self),List.prefix_refl _⟩ ∧
    run (aliasLocalCode 1 dt (aliasTarget self)++uintAliasWriteCode (C := C) 1 dt it jt)
      (machine false 1 42)=.ok (mutationTarget self) 0 ∧
    SourceUintMemoryAt (mutationFinal self) (aliasAddress self) (mutationNative self) (aliasRef self) .dyn ∧
    Objects.StateRepr 1 1 8 (Frag.init Δ)
      (((state false 1 42).setLocal dt (some (aliasRef self))).withHeap (mutationNative self)) base (mutationTarget self) ∧
    Objects.AllocatorRepr (mutationNative self) base 8 ⟨40,by decide⟩ (mutationTarget self) := by
  first
  | solve | simp only [] | omega
  | have initial : SourceUintMemoryAt (sy false 1 42) (aliasAddress self) hp (aliasRef self) .dyn := by
      cases self <;> unfold SourceUintMemoryAt <;> rw [MObj.elems_dyn] <;> rfl
    have sourceRoot : (sy false 1 42).1.get (aliasSource self)=.memRef rfl (aliasAddress self) := by cases self <;> rfl
    have targetRoot : TEnv.get (aliasTarget self) (state false 1 42).env=some (aliasRef self) := by cases self <;> rfl
    have bound : (u 1).1.toNat<hp.len (aliasRef self) .dyn := by
      cases self <;> simp only [aliasRef,if_true,Heap.len,Heap.get,Objs.get,hp,left,neighbor,MObj.elems_dyn] <;> decide
    obtain ⟨out,z,target,first,second,items,aliasNative,native,prog,write,selected,new,mok,aliasCode,code,whole,repr,alloc,rest⟩ :=
      source_uint_alias_assign_word (G0 p) F0 fuel (sy false 1 42) dr (aliasSource self) di si
        (aliasAddress self) (u 1) (u 42) sourceRoot rfl rfl SH (memOK false 1 42)
        (state false 1 42) dt (aliasTarget self) it jt (aliasRef self) targetRoot rfl rfl initial bound
        (initial_repr false 1 42) (allocator false 1 42) (by decide) rfl rfl
    have knownWrite : hp.writeAddr (.index (aliasRef self) .dyn (u 1)) (u 42)=some (mutationNative self) := by
      have hb : 1<(MObj.elems .dyn (hp.get (aliasRef self))).length := bound
      simp only [Heap.writeAddr,Heap.setIndex,show (u 1).1.toNat=1 from by decide,if_pos hb,mutationNative]
    have he : out=mutationNative self := Option.some.inj (write.symm.trans knownWrite)
    subst out
    have hz : z=mutationFinal self := congrArg Prod.snd (second.symm.trans (mutation_source p fuel self))
    subst z
    have ht : target=mutationTarget self := (Out.ok.inj (code.symm.trans (mutation_word self))).1
    subst target
    exact ⟨items,prog,whole,new,repr,alloc⟩

/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_write_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_write_concrete

/-- Complete ordered observations of the executions identified above, at
initial, alias-prefix and final stages. All twenty words and all three objects
are retained; the pipeline parameter is in the actual execution theorem. -/
theorem dynamic_uint_alias_write_vectors (self : Bool) :
    words (machine false 1 42)=
      [w[40],w[32],w[16],w[16],w[24],w[42],w[1],w[0],w[99],w[3],w[7],w[0],.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],w[9]] ∧
    words (mutationPointer self)=
      [w[40],w[32],w[16],(if self then w[16] else w[32]),w[24],w[42],w[1],w[0],w[99],w[3],w[7],w[0],.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],w[9]] ∧
    words (mutationTarget self)=
      [w[40],w[32],w[16],(if self then w[16] else w[32]),w[24],w[42],w[1],w[0],w[99],w[3],w[7],(if self then w[42] else w[0]),.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],(if self then w[9] else w[42])] ∧
    objects hp=[old,rhs,next] ∧
    objects (mutationNative self)=(if self then [old.set 1 (u 42),rhs,next] else [old,rhs,next.set 1 (u 42)]) ∧
    sourceObjects (sy false 1 42)=
      [some ⟨SA,sourceUintMemory old⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory next⟩] ∧
    sourceObjects (mutationMid self)=sourceObjects (sy false 1 42) ∧
    sourceObjects (mutationFinal self)=(if self then
      [some ⟨SA,sourceUintMemory (old.set 1 (u 42))⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory next⟩] else
      [some ⟨SA,sourceUintMemory old⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory (next.set 1 (u 42))⟩]) ∧
    (mutationMid self).1=.cons (sourceUint (u 1)) (.cons (sourceUint (u 42)) (.cons (.memRef rfl 1)
      (.cons (.memRef rfl (aliasAddress self)) (.cons (.memRef rfl 0) (.cons (.memRef rfl 2) .nil))))) ∧
    (mutationFinal self).1=(mutationMid self).1 ∧
    (((state false 1 42).setLocal dt (some (aliasRef self))).withHeap (mutationNative self)).env=
      (u 1,u 42,some right,some (aliasRef self),some left,some neighbor,()) ∧
    (mutationFinal self).2.ex=(sy false 1 42).2.ex ∧
    (mutationFinal self).2.events=(sy false 1 42).2.events ∧
    (mutationFinal self).2.logs=(sy false 1 42).2.logs ∧
    (mutationFinal self).2.fnLocals=(sy false 1 42).2.fnLocals ∧
    ({mutationTarget self with mem := (machine false 1 42).mem} : Machine)=machine false 1 42 ∧
    (mutationTarget self).stack=[w[77],w[88]] ∧ (mutationTarget self).mem 0=w[40] := by
  first
  | solve | simp only [] | omega
  | cases self <;> simp only [Bool.false_eq_true,if_false,if_true]
    all_goals
      refine ⟨rfl,rfl,rfl,?_,?_,rfl,rfl,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
      · simp only [objects,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn]
      · simp only [objects,mutationNative,aliasRef,Bool.false_eq_true,if_false,if_true,Heap.set,Objs.set,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn,MObj.setElem_dyn]
      · simp only [sourceObjects,mutationFinal,mutationMid,aliasAddress,Bool.false_eq_true,if_false,if_true,
          Source.Heap.write_get,Source.Heap.write_other _ (show 0≠2 by decide),
          Source.Heap.write_other _ (show 1≠2 by decide),Source.Heap.write_other _ (show 1≠0 by decide),
          Source.Heap.write_other _ (show 2≠0 by decide)]
        rfl

/-- Skipping rebinding writes LEFT, not the chosen shorter neighbour. Skipping
the write retains 9; the actual selected value is 42. Both are executable
observations, not an expected-output oracle or a rollback claim. -/
theorem dynamic_uint_alias_write_negatives (p : Roadmap.Pipeline) (fuel : Nat) :
    words (mutationTarget false)≠words (mutationTarget true) ∧
    words (mutationTarget false)≠words (mutationPointer false) ∧
    (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local dr) (.local di) rfl)).run (mutationFinal false)=
      (.ok (.val (sourceUint (u 42))),mutationFinal false) ∧
    (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local dr) (.local di) rfl)).run (mutationMid false)=
      (.ok (.val (sourceUint (u 9))),mutationMid false) ∧
    (Source.evalE (G0 p) F0 (fuel+3) (sourceUintIndexedAssign dr di si)).run (sy false 1 42)=
      (.ok (.val (sourceUint (u 42))),mutationFinal true) := by
  first
  | solve | simp only [] | omega
  | refine ⟨by decide,by decide,?_,?_,mutation_source p fuel true⟩
    · have represented := (dynamic_uint_alias_write_concrete p fuel false).2.2.2.1
      have contents : MObj.elems .dyn ((mutationNative false).get neighbor)=next.set 1 (u 42) := by
        change MObj.elems .dyn ((hp.set neighbor (MObj.setElem .dyn (hp.get neighbor) 1 (u 42))).get neighbor)=_
        rw [Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn]
        rfl
      have read := represented.eval_index (G0 p) F0 fuel dr di (u 1) rfl rfl
        (by change (u 1).1.toNat<(MObj.elems .dyn ((mutationNative false).get neighbor)).length
            rw [contents,List.length_set]
            decide)
      simpa only [show aliasRef false=neighbor from rfl,contents] using read
    · have represented : SourceUintMemoryAt (mutationMid false) 2 hp neighbor .dyn := by
        unfold SourceUintMemoryAt;rw [MObj.elems_dyn];rfl
      have read := represented.eval_index (G0 p) F0 fuel dr di (u 1) rfl rfl
        (by simp only [Heap.len,Heap.get,Objs.get,hp,neighbor,MObj.elems_dyn];decide)
      simpa only [Heap.get,Objs.get,hp,neighbor,MObj.elems_dyn] using read

/-- The short Items run retains the real alias prefix then times out before
writing. It exposes globals only; no inaccessible failed local output is added. -/
theorem dynamic_uint_alias_write_timeout (p : Roadmap.Pipeline) :
    (Source.execS (G0 p) F0 3 Γ.length none
      (.expr (sourceLocalAlias dr (aliasSource false)) : Source.RStmt E0 [] false .body Γ Γ)
      (sy false 1 42).1).run (.nil,(sy false 1 42).2)=
      (.ok (.normal (mutationMid false).1),(.nil,(mutationMid false).2)) ∧
    (Source.evalE (G0 p) F0 1 (sourceUintIndexedAssign dr di si)).run (mutationMid false)=
      (.error .timeout,mutationMid false) ∧
    (Source.execItems (G0 p) F0 4 Γ.length none
      (.stmt (.expr (sourceLocalAlias dr (aliasSource false)))
        (.stmt (.expr (sourceUintIndexedAssign dr di si)) .nil) : Source.RItems E0 [] false .body Γ Γ)
        (sy false 1 42).1).run (.nil,(sy false 1 42).2)=
      (.error .timeout,(.nil,(mutationMid false).2)) := by
  first
  | solve | simp only [] | omega | rfl
  | have alias := source_local_alias_run (G0 p) F0 0 (sy false 1 42) dr (aliasSource false)
      (.memRef rfl 2) rfl
    have first := source_expr_statement_run (G0 p) F0 2 Γ.length _ _ _ _ alias
    have late : (Source.evalE (G0 p) F0 1 (sourceUintIndexedAssign dr di si)).run (mutationMid false)=
        (.error .timeout,mutationMid false) := by cases p <;> rfl
    have second := source_expr_statement_error (G0 p) F0 1 Γ.length _ _ _ _ late
    refine ⟨first,late,?_⟩
    rw [Source.execItems,Source.Hoare.run_bind,first]
    change ((Source.execItems (G0 p) F0 3 Γ.length none
      (.stmt (.expr (sourceUintIndexedAssign dr di si)) .nil : Source.RItems E0 [] false .body Γ Γ)
      (mutationMid false).1) >>= fun o => Source.EM.lift (o.up Γ)).run (.nil,(mutationMid false).2)=_
    rw [Source.Hoare.run_bind,Source.execItems,Source.Hoare.run_bind,second]

/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_write_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_write_vectors
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_write_negatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_write_negatives
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_write_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_write_timeout

private def deletionNative (self : Bool) : Heap H :=
  hp.set (aliasRef self) (MObj.setElem .dyn (hp.get (aliasRef self)) 1 (u 0))
private def deletionFinal (self : Bool) : Source.EMState E0 Γ :=
  ((mutationMid self).1,{(mutationMid self).2 with heap := (mutationMid self).2.heap.write (aliasAddress self) (sourceUintMemory ((if self then old else next).set 1 (u 0))) (by cases self <;> rfl)})
private def deletionTarget (self : Bool) : Machine :=
  writeMachine (mutationPointer self) ((base (aliasRef self).id).val+2) w[0]

private theorem deletion_source (p : Roadmap.Pipeline) (fuel : Nat) (self : Bool) :
    (Source.evalE (G0 p) F0 (fuel+3) (sourceUintIndexedDelete dr di)).run (mutationMid self)=
      (.ok Source.RVal.unit,deletionFinal self) := by
  first
  | solve | simp only [] | omega
  | have initial : SourceUintMemoryAt (mutationMid self) (aliasAddress self) hp (aliasRef self) .dyn := by
      cases self <;> unfold SourceUintMemoryAt <;> rw [MObj.elems_dyn] <;> rfl
    have contents : (mutationMid self).2.heap.get (aliasAddress self)=
        some ⟨SA,sourceUintMemory (if self then old else next)⟩ := by cases self <;> rfl
    obtain ⟨ht,write⟩ := source_uint_write (mutationMid self) (aliasAddress self) (if self then old else next)
      contents 1 (by cases self <;> decide) (u 0)
    have actual : (Source.deleteLoc F0 (fuel+2) (τ := .int .u256) (.mem (aliasAddress self) (u 1).1.toNat)).run
        (mutationMid self)=(.ok (),deletionFinal self) := write
    exact initial.eval_delete_of_run (G0 p) F0 fuel dr di (u 1)
      (by cases self <;> rfl) rfl
      (by cases self <;> simp only [aliasRef,if_true,Heap.len,Heap.get,Objs.get,hp,left,neighbor,MObj.elems_dyn] <;> decide) actual

private theorem delete_one_run (m : Machine) (a : Fin W) (n : Nat) (hn : n<W) (hi : 1<n)
    (space : a.val+2<W) (hp : m.mem 3=.val a) (hx : m.mem 6=w[1])
    (hh : m.mem a.val=.val (wmod n)) :
    run (uintAliasDeleteCode (C := C) 1 dt it) m=.ok (writeMachine m (a.val+2) w[0]) 0 := by
  first
  | solve | simp only [] | omega
  | change run ([.push w[0]]++([.mload 3]++([.mload 6]++Objects.writeCode (.dyn : ArrTy A (.prim .uint))))) m=_
    rw [run_append_ok (show run [.push w[0]] m=.ok (m.push w[0]) 0 from rfl)]
    rw [run_append_ok (show run [.mload 3] (m.push w[0])=.ok ((m.push w[0]).push (.val a)) 0 from by
      change Out.ok ((m.push w[0]).push (m.mem 3)) 0=_;rw [hp])]
    rw [run_append_ok (show run [.mload 6] ((m.push w[0]).push (.val a))=
        .ok (((m.push w[0]).push (.val a)).push w[1]) 0 from by
      change Out.ok (((m.push w[0]).push (.val a)).push (m.mem 6)) 0=_;rw [hx])]
    have addr := arrayAddrStack_run (m.push w[0]) a ⟨1,by decide⟩ n hn hh
    rw [if_pos hi] at addr
    change run (arrayAddrStackCode++[.mstoreAt]) (((m.push w[0]).push (.val a)).push w[1])=_
    rw [run_append_ok addr]
    simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt space,Out.ok_bind,exec_nil,writeMachine]

private theorem deletion_word (self : Bool) :
    run (uintAliasDeleteCode (C := C) 1 dt it) (mutationPointer self)=.ok (deletionTarget self) 0 := by
  first
  | solve | simp only [] | omega
  | exact delete_one_run (mutationPointer self) (base (aliasRef self).id) (if self then 3 else 2)
      (by cases self <;> decide) (by cases self <;> decide) (by cases self <;> decide)
      (by cases self <;> rfl) (by cases self <;> rfl) (by cases self <;> rfl)

/-- Both original pipelines execute the real alias/deletion Source program,
native delete and complete existing word append, deriving the final identities. -/
theorem dynamic_uint_alias_delete_concrete (p : Roadmap.Pipeline) (fuel : Nat) (self : Bool) :
    (Source.execItems (G0 p) F0 (fuel+6) Γ.length none
      (.stmt (.expr (sourceLocalAlias dr (aliasSource self)))
        (.stmt (.expr (sourceUintIndexedDelete dr di)) .nil) : Source.RItems E0 [] false .body Γ Γ)
        (sy false 1 42).1).run (.nil,(sy false 1 42).2)=
      (.ok (.normal (deletionFinal self).1),(.nil,(deletionFinal self).2)) ∧
    Prog.run (state false 1 42) (.cons (.rebindMem dt (.alias (.var (aliasTarget self) rfl)))
      (.cons (.deleteMem (.loc (.index .dyn (.var dt rfl) (.simple (.local it)))) rfl) .nil))=
      .ok ⟨((state false 1 42).setLocal dt (some (aliasRef self))).withHeap (deletionNative self),List.prefix_refl _⟩ ∧
    run (aliasLocalCode 1 dt (aliasTarget self)++uintAliasDeleteCode (C := C) 1 dt it)
      (machine false 1 42)=.ok (deletionTarget self) 0 ∧
    SourceUintMemoryAt (deletionFinal self) (aliasAddress self) (deletionNative self) (aliasRef self) .dyn ∧
    Source.MemOK E0 SH (deletionFinal self) ∧
    Objects.StateRepr 1 1 8 (Frag.init Δ)
      (((state false 1 42).setLocal dt (some (aliasRef self))).withHeap (deletionNative self)) base (deletionTarget self) ∧
    Objects.AllocatorRepr (deletionNative self) base 8 ⟨40,by decide⟩ (deletionTarget self) := by
  first
  | solve | simp only [] | omega
  | have initial : SourceUintMemoryAt (sy false 1 42) (aliasAddress self) hp (aliasRef self) .dyn := by
      cases self <;> unfold SourceUintMemoryAt <;> rw [MObj.elems_dyn] <;> rfl
    have sourceRoot : (sy false 1 42).1.get (aliasSource self)=.memRef rfl (aliasAddress self) := by cases self <;> rfl
    have targetRoot : TEnv.get (aliasTarget self) (state false 1 42).env=some (aliasRef self) := by cases self <;> rfl
    have bound : (u 1).1.toNat<hp.len (aliasRef self) .dyn := by
      cases self <;> simp only [aliasRef,if_true,Heap.len,Heap.get,Objs.get,hp,left,neighbor,MObj.elems_dyn] <;> decide
    obtain ⟨out,z,target,first,second,items,aliasNative,native,prog,write,selected,new,mok,aliasCode,code,whole,repr,alloc,rest⟩ :=
      source_uint_alias_delete_word (G0 p) F0 fuel (sy false 1 42) dr (aliasSource self) di
        (aliasAddress self) (u 1) sourceRoot rfl SH (memOK false 1 42)
        (state false 1 42) dt (aliasTarget self) it (aliasRef self) targetRoot rfl initial bound
        (initial_repr false 1 42) (allocator false 1 42) (by decide) rfl
    have knownWrite : hp.writeAddr (.index (aliasRef self) .dyn (u 1)) (PrimTy.dflt .uint)=some (deletionNative self) := by
      have hb : 1<(MObj.elems .dyn (hp.get (aliasRef self))).length := bound
      simp only [Heap.writeAddr,Heap.setIndex,show (u 1).1.toNat=1 from by decide,if_pos hb,deletionNative]
      rfl
    have he : out=deletionNative self := Option.some.inj (write.symm.trans knownWrite)
    subst out
    have hz : z=deletionFinal self := congrArg Prod.snd (second.symm.trans (deletion_source p fuel self))
    subst z
    have ht : target=deletionTarget self := (Out.ok.inj (code.symm.trans (deletion_word self))).1
    subst target
    exact ⟨items,prog,whole,new,mok,repr,alloc⟩

/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_delete_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_delete_concrete

/-- Complete initial/alias-prefix/deletion observations of the actual
executions above, including all represented words, objects and local frames. -/
theorem dynamic_uint_alias_delete_vectors (self : Bool) :
    words (machine false 1 42)=
      [w[40],w[32],w[16],w[16],w[24],w[42],w[1],w[0],w[99],w[3],w[7],w[0],.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],w[9]] ∧
    words (mutationPointer self)=
      [w[40],w[32],w[16],(if self then w[16] else w[32]),w[24],w[42],w[1],w[0],w[99],w[3],w[7],w[0],.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],w[9]] ∧
    words (deletionTarget self)=
      [w[40],w[32],w[16],(if self then w[16] else w[32]),w[24],w[42],w[1],w[0],w[99],w[3],w[7],w[0],.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],(if self then w[9] else w[0])] ∧
    objects hp=[old,rhs,next] ∧
    objects (deletionNative self)=(if self then [old.set 1 (u 0),rhs,next] else [old,rhs,next.set 1 (u 0)]) ∧
    sourceObjects (sy false 1 42)=
      [some ⟨SA,sourceUintMemory old⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory next⟩] ∧
    sourceObjects (mutationMid self)=sourceObjects (sy false 1 42) ∧
    sourceObjects (deletionFinal self)=(if self then
      [some ⟨SA,sourceUintMemory (old.set 1 (u 0))⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory next⟩] else
      [some ⟨SA,sourceUintMemory old⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory (next.set 1 (u 0))⟩]) ∧
    (mutationMid self).1=.cons (sourceUint (u 1)) (.cons (sourceUint (u 42)) (.cons (.memRef rfl 1)
      (.cons (.memRef rfl (aliasAddress self)) (.cons (.memRef rfl 0) (.cons (.memRef rfl 2) .nil))))) ∧
    (deletionFinal self).1=(mutationMid self).1 ∧
    (((state false 1 42).setLocal dt (some (aliasRef self))).withHeap (deletionNative self)).env=
      (u 1,u 42,some right,some (aliasRef self),some left,some neighbor,()) ∧
    (deletionFinal self).2.ex=(sy false 1 42).2.ex ∧
    (deletionFinal self).2.events=(sy false 1 42).2.events ∧
    (deletionFinal self).2.logs=(sy false 1 42).2.logs ∧
    (deletionFinal self).2.fnLocals=(sy false 1 42).2.fnLocals ∧
    ({deletionTarget self with mem := (machine false 1 42).mem} : Machine)=machine false 1 42 ∧
    (deletionTarget self).stack=[w[77],w[88]] ∧ (deletionTarget self).mem 0=w[40] := by
  first
  | solve | simp only [] | omega
  | cases self <;> simp only [Bool.false_eq_true,if_false,if_true]
    all_goals
      refine ⟨rfl,rfl,rfl,?_,?_,rfl,rfl,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
      · simp only [objects,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn]
      · simp only [objects,deletionNative,aliasRef,Bool.false_eq_true,if_false,if_true,Heap.set,Objs.set,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn,MObj.setElem_dyn]
      · simp only [sourceObjects,deletionFinal,mutationMid,aliasAddress,Bool.false_eq_true,if_false,if_true,
          Source.Heap.write_get,Source.Heap.write_other _ (show 0≠2 by decide),
          Source.Heap.write_other _ (show 1≠2 by decide),Source.Heap.write_other _ (show 1≠0 by decide),
          Source.Heap.write_other _ (show 2≠0 by decide)]
        rfl

/-- Actual selected deletion reads zero; omitted deletion reads nine.
Deleting after self-rebinding and writing42 are discriminated by full words. -/
theorem dynamic_uint_alias_delete_negatives (p : Roadmap.Pipeline) (fuel : Nat) :
    words (deletionTarget false)≠words (mutationPointer false) ∧
    words (deletionTarget false)≠words (deletionTarget true) ∧
    words (deletionTarget false)≠words (mutationTarget false) ∧
    (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local dr) (.local di) rfl)).run (deletionFinal false)=
      (.ok (.val (sourceUint (u 0))),deletionFinal false) ∧
    (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local dr) (.local di) rfl)).run (mutationMid false)=
      (.ok (.val (sourceUint (u 9))),mutationMid false) := by
  first
  | solve | simp only [] | omega
  | refine ⟨by decide,by decide,by decide,?_,(dynamic_uint_alias_write_negatives p fuel).2.2.2.1⟩
    have represented := (dynamic_uint_alias_delete_concrete p fuel false).2.2.2.1
    have contents : MObj.elems .dyn ((deletionNative false).get neighbor)=next.set 1 (u 0) := by
      change MObj.elems .dyn ((hp.set neighbor (MObj.setElem .dyn (hp.get neighbor) 1 (u 0))).get neighbor)=_
      rw [Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn]
      rfl
    have read := represented.eval_index (G0 p) F0 fuel dr di (u 1) rfl rfl
      (by change (u 1).1.toNat<(MObj.elems .dyn ((deletionNative false).get neighbor)).length
          rw [contents,List.length_set]
          decide)
    simpa only [show aliasRef false=neighbor from rfl,contents] using read

/-- Short Source Items retains the actual alias prefix then times out before
deleting; no error-local output, rollback or failed target machine is invented. -/
theorem dynamic_uint_alias_delete_timeout (p : Roadmap.Pipeline) :
    (Source.execS (G0 p) F0 3 Γ.length none
      (.expr (sourceLocalAlias dr (aliasSource false)) : Source.RStmt E0 [] false .body Γ Γ)
      (sy false 1 42).1).run (.nil,(sy false 1 42).2)=
      (.ok (.normal (mutationMid false).1),(.nil,(mutationMid false).2)) ∧
    (Source.evalE (G0 p) F0 1 (sourceUintIndexedDelete dr di)).run (mutationMid false)=
      (.error .timeout,mutationMid false) ∧
    (Source.execItems (G0 p) F0 4 Γ.length none
      (.stmt (.expr (sourceLocalAlias dr (aliasSource false)))
        (.stmt (.expr (sourceUintIndexedDelete dr di)) .nil) : Source.RItems E0 [] false .body Γ Γ)
        (sy false 1 42).1).run (.nil,(sy false 1 42).2)=
      (.error .timeout,(.nil,(mutationMid false).2)) := by
  first
  | solve | simp only [] | omega | rfl
  | have first := (dynamic_uint_alias_write_timeout p).1
    have late : (Source.evalE (G0 p) F0 1 (sourceUintIndexedDelete dr di)).run (mutationMid false)=
        (.error .timeout,mutationMid false) := by cases p <;> rfl
    have second := source_expr_statement_error (G0 p) F0 1 Γ.length _ _ _ _ late
    refine ⟨first,late,?_⟩
    rw [Source.execItems,Source.Hoare.run_bind,first]
    change ((Source.execItems (G0 p) F0 3 Γ.length none
      (.stmt (.expr (sourceUintIndexedDelete dr di)) .nil : Source.RItems E0 [] false .body Γ Γ)
      (mutationMid false).1) >>= fun o => Source.EM.lift (o.up Γ)).run (.nil,(mutationMid false).2)=_
    rw [Source.Hoare.run_bind,Source.execItems,Source.Hoare.run_bind,second]

/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_delete_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_delete_vectors
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_delete_negatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_delete_negatives
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_delete_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_delete_timeout

/-- Selected neighbour length2 rejects index2 after the actual alias, while
retained LEFT length3 still returns max at the same index. Prefix vectors are
the complete existing dynamic_uint_alias_vectors, preserved verbatim. -/
theorem dynamic_uint_alias_delete_endpoint (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 p) F0 (fuel+3) (sourceUintIndexedDelete dr di)).run (aliasSourceState false)=
      (.error (.revert (Source.panicData .index)),aliasSourceState false) ∧
    (Source.execItems (G0 p) F0 (fuel+6) Γ.length none
      (.stmt (.expr (sourceLocalAlias dr (aliasSource false)))
        (.stmt (.expr (sourceUintIndexedDelete dr di)) .nil) : Source.RItems E0 [] false .body Γ Γ)
        (sy false 2 0).1).run (.nil,(sy false 2 0).2)=
      (.error (.revert (Source.panicData .index)),(.nil,(aliasSourceState false).2)) ∧
    Prog.run (state false 2 0) (.cons (.rebindMem dt (.alias (.var (aliasTarget false) rfl)))
      (.cons (.deleteMem (.loc (.index .dyn (.var dt rfl) (.simple (.local it)))) rfl) .nil))=.error .revert ∧
    run (uintAliasDeleteCode (C := C) 1 dt it) (aliasMachine false)=.revert ∧
    run (aliasLocalCode 1 dt (aliasTarget false)++uintAliasDeleteCode (C := C) 1 dt it)
      (machine false 2 0)=.revert ∧
    (Source.evalE (G0 p) F0 (fuel+2)
      (.indexArray (.local (.there (.there (.there (.there .here)))) : Source.RExpr E0 Γ SA) (.local di) rfl)).run (aliasSourceState false)=
      (.ok (.val (sourceUint maximum)),aliasSourceState false) := by
  first
  | solve | simp only [] | omega
  | obtain ⟨first,alias,second,items,invalid,prog,code,whole,rest⟩ :=
      source_uint_alias_delete_bounds_word (G0 p) F0 fuel (sy false 2 0) dr (aliasSource false) di 2 (u 2)
        rfl rfl SH (memOK false 2 0) (state false 2 0) dt (aliasTarget false) it neighbor rfl rfl
        (alias_at false) (by simp only [Heap.len,Heap.get,Objs.get,hp,neighbor,MObj.elems_dyn];decide)
        (initial_repr false 2 0) (allocator false 2 0) (by decide)
    exact ⟨second,items,prog,code,whole,(dynamic_uint_alias_bounds p fuel).2.2.2.2.2⟩

/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_delete_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_delete_endpoint

private theorem triple_contents (self : Bool) :
    (mutationFinal self).2.heap.get (aliasAddress self)=
      some ⟨SA,sourceUintMemory ((if self then old else next).set 1 (u 42))⟩ := by
  cases self <;> simp only [mutationFinal,mutationMid,aliasAddress,Bool.false_eq_true,if_false,if_true,Source.Heap.write_get]

private def tripleNative (self : Bool) : Heap H :=
  (mutationNative self).set (aliasRef self) (MObj.setElem .dyn ((mutationNative self).get (aliasRef self)) 1 (u 0))
private def tripleFinal (self : Bool) : Source.EMState E0 Γ :=
  ((mutationFinal self).1,{(mutationFinal self).2 with heap := (mutationFinal self).2.heap.write (aliasAddress self) (sourceUintMemory (((if self then old else next).set 1 (u 42)).set 1 (u 0))) (by
    change ((mutationFinal self).2.heap.get (aliasAddress self)).map Sigma.fst=some SA
    rw [triple_contents]
    rfl)})
private def tripleTarget (self : Bool) : Machine :=
  writeMachine (mutationTarget self) ((base (aliasRef self).id).val+2) w[0]

private theorem triple_source (p : Roadmap.Pipeline) (fuel : Nat) (self : Bool) :
    (Source.evalE (G0 p) F0 (fuel+3) (sourceUintIndexedDelete dr di)).run (mutationFinal self)=
      (.ok Source.RVal.unit,tripleFinal self) := by
  first
  | solve | simp only [] | omega
  | have initial := (dynamic_uint_alias_write_concrete p fuel self).2.2.2.1
    obtain ⟨ht,write⟩ := source_uint_write (mutationFinal self) (aliasAddress self)
      ((if self then old else next).set 1 (u 42)) (triple_contents self) 1
      (by rw [List.length_set];cases self <;> decide) (u 0)
    have actual : (Source.deleteLoc F0 (fuel+2) (τ := .int .u256) (.mem (aliasAddress self) (u 1).1.toNat)).run
        (mutationFinal self)=(.ok (),tripleFinal self) := write
    have bound : (u 1).1.toNat<(mutationNative self).len (aliasRef self) .dyn := by
      change (u 1).1.toNat<(MObj.elems .dyn ((mutationNative self).get (aliasRef self))).length
      rw [show MObj.elems .dyn ((mutationNative self).get (aliasRef self))=
        (MObj.elems .dyn (hp.get (aliasRef self))).set 1 (u 42) from by
          change MObj.elems .dyn ((hp.set (aliasRef self) _).get (aliasRef self))=_
          rw [Heap.get_set_same,MObj.elems_setElem]]
      rw [List.length_set]
      cases self <;> rw [MObj.elems_dyn] <;> decide
    exact initial.eval_delete_of_run (G0 p) F0 fuel dr di (u 1) (by cases self <;> rfl) rfl bound actual

private theorem triple_word (self : Bool) :
    run (uintAliasDeleteCode (C := C) 1 dt it) (mutationTarget self)=.ok (tripleTarget self) 0 := by
  first
  | solve | simp only [] | omega
  | exact delete_one_run (mutationTarget self) (base (aliasRef self).id) (if self then 3 else 2)
      (by cases self <;> decide) (by cases self <;> decide) (by cases self <;> decide)
      (by cases self <;> rfl) (by cases self <;> rfl) (by cases self <;> rfl)

/-- The three real executions consume the SAME materially changed prefix.
Both pipeline parameters and same/distinct reference identities are inhabited. -/
theorem dynamic_uint_alias_write_delete_concrete (p : Roadmap.Pipeline) (fuel : Nat) (self : Bool) :
    (Source.execItems (G0 p) F0 (fuel+7) Γ.length none
      (.stmt (.expr (sourceLocalAlias dr (aliasSource self)))
        (.stmt (.expr (sourceUintIndexedAssign dr di si)) (.stmt (.expr (sourceUintIndexedDelete dr di)) .nil)) :
          Source.RItems E0 [] false .body Γ Γ) (sy false 1 42).1).run (.nil,(sy false 1 42).2)=
      (.ok (.normal (tripleFinal self).1),(.nil,(tripleFinal self).2)) ∧
    Prog.run (state false 1 42) (.cons (.rebindMem dt (.alias (.var (aliasTarget self) rfl)))
      (.cons (.assignMem (.index .dyn (.var dt rfl) (.simple (.local it))) (.val (.simple (.local jt))))
        (.cons (.deleteMem (.loc (.index .dyn (.var dt rfl) (.simple (.local it)))) rfl) .nil)))=
      .ok ⟨((state false 1 42).setLocal dt (some (aliasRef self))).withHeap (tripleNative self),List.prefix_refl _⟩ ∧
    run ((aliasLocalCode 1 dt (aliasTarget self)++uintAliasWriteCode (C := C) 1 dt it jt)++uintAliasDeleteCode (C := C) 1 dt it)
      (machine false 1 42)=.ok (tripleTarget self) 0 ∧
    (Source.evalE (G0 p) F0 (fuel+4) (sourceUintIndexedAssign dr di si)).run (mutationMid self)=
      (.ok (.val (sourceUint (u 42))),mutationFinal self) ∧
    (Source.evalE (G0 p) F0 (fuel+3) (sourceUintIndexedDelete dr di)).run (mutationFinal self)=
      (.ok Source.RVal.unit,tripleFinal self) ∧
    SourceUintMemoryAt (tripleFinal self) (aliasAddress self) (tripleNative self) (aliasRef self) .dyn ∧
    Source.MemOK E0 SH (tripleFinal self) ∧
    Objects.StateRepr 1 1 8 (Frag.init Δ)
      (((state false 1 42).setLocal dt (some (aliasRef self))).withHeap (tripleNative self)) base (tripleTarget self) ∧
    Objects.AllocatorRepr (tripleNative self) base 8 ⟨40,by decide⟩ (tripleTarget self) := by
  first
  | solve | simp only [] | omega
  | have initial : SourceUintMemoryAt (sy false 1 42) (aliasAddress self) hp (aliasRef self) .dyn := by
      cases self <;> unfold SourceUintMemoryAt <;> rw [MObj.elems_dyn] <;> rfl
    have sourceRoot : (sy false 1 42).1.get (aliasSource self)=.memRef rfl (aliasAddress self) := by cases self <;> rfl
    have targetRoot : TEnv.get (aliasTarget self) (state false 1 42).env=some (aliasRef self) := by cases self <;> rfl
    have bound : (u 1).1.toNat<hp.len (aliasRef self) .dyn := by
      cases self <;> simp only [aliasRef,if_true,Heap.len,Heap.get,Objs.get,hp,left,neighbor,MObj.elems_dyn] <;> decide
    obtain ⟨mid,out,changed,z,mm,target,first,second,third,items,prog,prefixCode,code,whole,write,delwrite,read,new,final,
      mok,finalOK,repr,finalRepr,alloc,finalAlloc,rest⟩ :=
      source_uint_alias_write_delete_word (G0 p) F0 fuel (sy false 1 42) dr (aliasSource self) di si
        (aliasAddress self) (u 1) (u 42) sourceRoot rfl rfl SH (memOK false 1 42)
        (state false 1 42) dt (aliasTarget self) it jt (aliasRef self) targetRoot rfl rfl initial bound
        (initial_repr false 1 42) (allocator false 1 42) (by decide) rfl rfl
    have knownWrite : hp.writeAddr (.index (aliasRef self) .dyn (u 1)) (u 42)=some (mutationNative self) := by
      have hb : 1<(MObj.elems .dyn (hp.get (aliasRef self))).length := bound
      simp only [Heap.writeAddr,Heap.setIndex,show (u 1).1.toNat=1 from by decide,if_pos hb,mutationNative]
    have hm : mid=mutationNative self := Option.some.inj (write.symm.trans knownWrite)
    subst mid
    have hc : changed=mutationFinal self := congrArg Prod.snd (second.symm.trans (mutation_source p (fuel+1) self))
    subst changed
    have hmiddle : mm=mutationTarget self := (Out.ok.inj (prefixCode.symm.trans (dynamic_uint_alias_write_concrete p fuel self).2.2.1)).1
    subst mm
    have knownDelete : (mutationNative self).writeAddr (.index (aliasRef self) .dyn (u 1)) (PrimTy.dflt .uint)=some (tripleNative self) := by
      have hb : 1<(MObj.elems .dyn ((mutationNative self).get (aliasRef self))).length := by
        rw [show MObj.elems .dyn ((mutationNative self).get (aliasRef self))=
          (MObj.elems .dyn (hp.get (aliasRef self))).set 1 (u 42) from by
            change MObj.elems .dyn ((hp.set (aliasRef self) _).get (aliasRef self))=_
            rw [Heap.get_set_same,MObj.elems_setElem],List.length_set]
        exact bound
      simp only [Heap.writeAddr,Heap.setIndex,show (u 1).1.toNat=1 from by decide,if_pos hb,tripleNative]
      rfl
    have ho : out=tripleNative self := Option.some.inj (delwrite.symm.trans knownDelete)
    subst out
    have hz : z=tripleFinal self := congrArg Prod.snd (third.symm.trans (triple_source p fuel self))
    subst z
    have ht : target=tripleTarget self := (Out.ok.inj (code.symm.trans (triple_word self))).1
    subst target
    exact ⟨items,prog,whole,second,third,final,finalOK,finalRepr,finalAlloc⟩

/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_write_delete_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_write_delete_concrete

/-- All four stages retain complete ordered observations. The written42
stage is kept even though deleting afterward has the same final words as a
standalone deletion. The execution theorem supplies both pipeline instances. -/
theorem dynamic_uint_alias_write_delete_vectors (self : Bool) :
    words (machine false 1 42)=
      [w[40],w[32],w[16],w[16],w[24],w[42],w[1],w[0],w[99],w[3],w[7],w[0],.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],w[9]] ∧
    words (mutationPointer self)=
      [w[40],w[32],w[16],(if self then w[16] else w[32]),w[24],w[42],w[1],w[0],w[99],w[3],w[7],w[0],.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],w[9]] ∧
    words (mutationTarget self)=
      [w[40],w[32],w[16],(if self then w[16] else w[32]),w[24],w[42],w[1],w[0],w[99],w[3],w[7],(if self then w[42] else w[0]),.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],(if self then w[9] else w[42])] ∧
    words (tripleTarget self)=
      [w[40],w[32],w[16],(if self then w[16] else w[32]),w[24],w[42],w[1],w[0],w[99],w[3],w[7],w[0],.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],(if self then w[9] else w[0])] ∧
    objects hp=[old,rhs,next] ∧
    objects (mutationNative self)=(if self then [old.set 1 (u 42),rhs,next] else [old,rhs,next.set 1 (u 42)]) ∧
    objects (tripleNative self)=(if self then [(old.set 1 (u 42)).set 1 (u 0),rhs,next] else [old,rhs,(next.set 1 (u 42)).set 1 (u 0)]) ∧
    sourceObjects (sy false 1 42)=
      [some ⟨SA,sourceUintMemory old⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory next⟩] ∧
    sourceObjects (mutationMid self)=sourceObjects (sy false 1 42) ∧
    sourceObjects (mutationFinal self)=(if self then
      [some ⟨SA,sourceUintMemory (old.set 1 (u 42))⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory next⟩] else
      [some ⟨SA,sourceUintMemory old⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory (next.set 1 (u 42))⟩]) ∧
    sourceObjects (tripleFinal self)=(if self then
      [some ⟨SA,sourceUintMemory ((old.set 1 (u 42)).set 1 (u 0))⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory next⟩] else
      [some ⟨SA,sourceUintMemory old⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory ((next.set 1 (u 42)).set 1 (u 0))⟩]) ∧
    (tripleFinal self).1=(mutationMid self).1 ∧
    (((state false 1 42).setLocal dt (some (aliasRef self))).withHeap (tripleNative self)).env=
      (u 1,u 42,some right,some (aliasRef self),some left,some neighbor,()) ∧
    (tripleFinal self).2.ex=(sy false 1 42).2.ex ∧
    (tripleFinal self).2.events=(sy false 1 42).2.events ∧
    (tripleFinal self).2.logs=(sy false 1 42).2.logs ∧
    (tripleFinal self).2.fnLocals=(sy false 1 42).2.fnLocals ∧
    ({tripleTarget self with mem := (machine false 1 42).mem} : Machine)=machine false 1 42 ∧
    (tripleTarget self).stack=[w[77],w[88]] ∧ (tripleTarget self).mem 0=w[40] := by
  first
  | solve | simp only [] | omega
  | cases self <;> simp only [Bool.false_eq_true,if_false,if_true]
    all_goals
      refine ⟨rfl,rfl,rfl,rfl,?_,?_,?_,rfl,rfl,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
      · simp only [objects,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn]
      · simp only [objects,mutationNative,aliasRef,Bool.false_eq_true,if_false,if_true,Heap.set,Objs.set,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn,MObj.setElem_dyn]
      · simp only [objects,tripleNative,mutationNative,aliasRef,Bool.false_eq_true,if_false,if_true,Heap.set,Objs.set,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn,MObj.setElem_dyn]
      · simp only [sourceObjects,mutationFinal,mutationMid,aliasAddress,Bool.false_eq_true,if_false,if_true,
          Source.Heap.write_get,Source.Heap.write_other _ (show 0≠2 by decide),Source.Heap.write_other _ (show 1≠2 by decide),
          Source.Heap.write_other _ (show 1≠0 by decide),Source.Heap.write_other _ (show 2≠0 by decide)]
        rfl
      · simp only [sourceObjects,tripleFinal,mutationFinal,mutationMid,aliasAddress,Bool.false_eq_true,if_false,if_true,
          Source.Heap.write_get,Source.Heap.write_other _ (show 0≠2 by decide),Source.Heap.write_other _ (show 1≠2 by decide),
          Source.Heap.write_other _ (show 1≠0 by decide),Source.Heap.write_other _ (show 2≠0 by decide)]
        rfl

/-- The ordered history distinguishes a skipped write: the actual reached
read is42 before deletion and0 after. Final words alone cannot discriminate
it, and that equality is recorded rather than hidden. -/
theorem dynamic_uint_alias_write_delete_negatives (p : Roadmap.Pipeline) (fuel : Nat) :
    words (tripleTarget false)=words (deletionTarget false) ∧
    words (mutationTarget false)≠words (mutationPointer false) ∧
    words (tripleTarget false)≠words (mutationTarget false) ∧
    words (tripleTarget false)≠words (tripleTarget true) ∧
    (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local dr) (.local di) rfl)).run (mutationFinal false)=
      (.ok (.val (sourceUint (u 42))),mutationFinal false) ∧
    (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local dr) (.local di) rfl)).run (tripleFinal false)=
      (.ok (.val (sourceUint (u 0))),tripleFinal false) := by
  first
  | solve | simp only [] | omega
  | refine ⟨rfl,by decide,by decide,by decide,(dynamic_uint_alias_write_negatives p fuel).2.2.1,?_⟩
    have represented := (dynamic_uint_alias_write_delete_concrete p fuel false).2.2.2.2.2.1
    have contents : MObj.elems .dyn ((tripleNative false).get neighbor)=(next.set 1 (u 42)).set 1 (u 0) := by
      change MObj.elems .dyn (((mutationNative false).set neighbor _).get neighbor)=_
      rw [Heap.get_set_same,MObj.elems_setElem]
      have written : MObj.elems .dyn ((mutationNative false).get neighbor)=next.set 1 (u 42) := by
        change MObj.elems .dyn ((hp.set neighbor _).get neighbor)=_
        rw [Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn]
        rfl
      rw [show aliasRef false=neighbor from rfl,written]
    have read := represented.eval_index (G0 p) F0 fuel dr di (u 1) rfl rfl
      (by change (u 1).1.toNat<(MObj.elems .dyn ((tripleNative false).get neighbor)).length
          rw [contents,List.length_set,List.length_set]
          decide)
    simpa only [show aliasRef false=neighbor from rfl,contents] using read

/-- Low Items fuel keeps the actual42 write before the delete times out.
The error outcome returns globals only; prefix locals are proved separately. -/
theorem dynamic_uint_alias_write_delete_timeout (p : Roadmap.Pipeline) :
    (Source.execItems (G0 p) F0 6 Γ.length none
      (.stmt (.expr (sourceLocalAlias dr (aliasSource false)))
        (.stmt (.expr (sourceUintIndexedAssign dr di si)) .nil) : Source.RItems E0 [] false .body Γ Γ)
      (sy false 1 42).1).run (.nil,(sy false 1 42).2)=
      (.ok (.normal (mutationFinal false).1),(.nil,(mutationFinal false).2)) ∧
    (Source.evalE (G0 p) F0 2 (sourceUintIndexedDelete dr di)).run (mutationFinal false)=
      (.error .timeout,mutationFinal false) ∧
    (Source.execItems (G0 p) F0 6 Γ.length none
      (.stmt (.expr (sourceLocalAlias dr (aliasSource false)))
        (.stmt (.expr (sourceUintIndexedAssign dr di si)) (.stmt (.expr (sourceUintIndexedDelete dr di)) .nil)) :
          Source.RItems E0 [] false .body Γ Γ) (sy false 1 42).1).run (.nil,(sy false 1 42).2)=
      (.error .timeout,(.nil,(mutationFinal false).2)) := by
  first
  | solve | simp only [] | omega
  | have first := source_local_alias_run (G0 p) F0 2 (sy false 1 42) dr (aliasSource false) (.memRef rfl 2) rfl
    have second := mutation_source p 0 false
    have late : (Source.evalE (G0 p) F0 2 (sourceUintIndexedDelete dr di)).run (mutationFinal false)=
        (.error .timeout,mutationFinal false) := by cases p <;> rfl
    refine ⟨(dynamic_uint_alias_write_concrete p 0 false).1,late,?_⟩
    exact source_items_triple_error (G0 p) F0 2 Γ.length _ _ _ (sy false 1 42) (mutationMid false)
      (mutationFinal false) (mutationFinal false) .timeout
      (source_expr_statement_run (G0 p) F0 4 Γ.length _ _ _ _ first)
      (source_expr_statement_run (G0 p) F0 3 Γ.length _ _ _ _ second)
      (source_expr_statement_error (G0 p) F0 2 Γ.length _ _ _ _ late)

/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_write_delete_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_write_delete_vectors
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_write_delete_negatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_write_delete_negatives
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_write_delete_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_write_delete_timeout

private def readFinal (self : Bool) : Source.EMState E0 Γ :=
  ((mutationFinal self).1.set di (sourceUint (u 42)),(mutationFinal self).2)
private def readState (self : Bool) : State C Δ :=
  (((state false 1 42).setLocal dt (some (aliasRef self))).withHeap (mutationNative self)).setLocal it (u 42)
private def readTarget (self : Bool) : Machine := writeMachine (mutationTarget self) 6 w[42]

private theorem written_read_some (self : Bool) :
    (mutationNative self).readAddr (.index (aliasRef self) .dyn (u 1))=some (u 42) := by
  first
  | solve | simp only [] | omega
  | change (MObj.elems .dyn ((mutationNative self).get (aliasRef self)))[(u 1).1.toNat]?=some (u 42)
    change (MObj.elems .dyn ((hp.set (aliasRef self) _).get (aliasRef self)))[(u 1).1.toNat]?=some (u 42)
    rw [Heap.get_set_same,MObj.elems_setElem]
    exact List.getElem?_set_self (by cases self <;> rw [MObj.elems_dyn] <;> decide)

private theorem read_into_word (self : Bool) :
    run (uintReadIntoCode (C := C) 1 dt it it) (mutationTarget self)=.ok (readTarget self) 0 := by
  first
  | solve | simp only [] | omega
  | let σ := ((state false 1 42).setLocal dt (some (aliasRef self))).withHeap (mutationNative self)
    have repr : Objects.StateRepr 1 1 8 (Frag.init Δ) σ base (mutationTarget self) :=
      (dynamic_uint_alias_write_concrete .legacy 0 self).2.2.2.2.1
    have root : TEnv.get dt σ.env=some (aliasRef self) := by cases self <;> rfl
    have index : TEnv.get it σ.env=u 1 := rfl
    have nativeRead : (Val.readMem (.index .dyn (.var dt rfl) (.simple (.local it))) : Val C Δ .uint).evalT σ=.ok (u 42) := by
      simp only [Val.evalT,MLoc.addrT,MPath.mvalT,Simple.evalT,root,index,
        show σ.heap.readAddr (.index (aliasRef self) .dyn (u 1))=some (u 42) from written_read_some self,
        TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have cert := Objects.PtrFrag.readPrimitive repr (Objects.PtrFrag.local dt rfl)
      (.dyn : ArrTy A (.prim .uint)) (.simple (.local it) : Val C Δ .uint) rfl
    change ValOutT .uint _ (run (readLocalCode 1 dt (.simple (.local it))) (mutationTarget self)) (mutationTarget self) at cert
    rw [nativeRead] at cert
    rcases cert with ⟨v,w,equal,representation,code⟩ | ⟨bad,_⟩
    · cases Except.ok.inj equal
      obtain ⟨n,hn,number,word⟩ := representation.uint_inv
      have nw : n=(wmod 42).val := Int.ofNat.inj (number.symm.trans (rfl : (u 42).1=((wmod 42).val : Int)))
      have hw : w=w[42] := word.trans (congrArg Word.val (Fin.ext nw))
      rw [hw] at code
      change run (readLocalCode 1 dt (.simple (.local it) : Val C Δ .uint)++[.mstore 6]) (mutationTarget self)=_
      rw [run_append_ok code]
      rfl
    · cases bad

/-- Actual result/index aliasing: the read sees index1 and value42 before
storing42 into that index local. Both original pipeline programs are executed. -/
theorem dynamic_uint_alias_write_read_concrete (p : Roadmap.Pipeline) (fuel : Nat) (self : Bool) :
    (Source.execItems (G0 p) F0 (fuel+7) Γ.length none
      (.stmt (.expr (sourceLocalAlias dr (aliasSource self)))
        (.stmt (.expr (sourceUintIndexedAssign dr di si)) (.stmt (.expr (sourceUintReadInto dr di di)) .nil)) :
          Source.RItems E0 [] false .body Γ Γ) (sy false 1 42).1).run (.nil,(sy false 1 42).2)=
      (.ok (.normal (readFinal self).1),(.nil,(readFinal self).2)) ∧
    Prog.run (state false 1 42) (.cons (.rebindMem dt (.alias (.var (aliasTarget self) rfl)))
      (.cons (.assignMem (.index .dyn (.var dt rfl) (.simple (.local it))) (.val (.simple (.local jt))))
        (.cons (.assignLocal it (.readMem (.index .dyn (.var dt rfl) (.simple (.local it))))) .nil)))=
      .ok ⟨readState self,List.prefix_refl _⟩ ∧
    run ((aliasLocalCode 1 dt (aliasTarget self)++uintAliasWriteCode (C := C) 1 dt it jt)++uintReadIntoCode (C := C) 1 dt it it)
      (machine false 1 42)=.ok (readTarget self) 0 ∧
    (Source.evalE (G0 p) F0 (fuel+3) (sourceUintReadInto dr di di)).run (mutationFinal self)=
      (.ok (.val (sourceUint (u 42))),readFinal self) ∧
    SourceUintMemoryAt (readFinal self) (aliasAddress self) (mutationNative self) (aliasRef self) .dyn ∧
    Source.MemOK E0 SH (readFinal self) ∧
    Objects.StateRepr 1 1 8 (Frag.init Δ) (readState self) base (readTarget self) ∧
    Objects.AllocatorRepr (mutationNative self) base 8 ⟨40,by decide⟩ (readTarget self) := by
  first
  | solve | simp only [] | omega
  | have initial : SourceUintMemoryAt (sy false 1 42) (aliasAddress self) hp (aliasRef self) .dyn := by
      cases self <;> unfold SourceUintMemoryAt <;> rw [MObj.elems_dyn] <;> rfl
    have sr : (sy false 1 42).1.get (aliasSource self)=.memRef rfl (aliasAddress self) := by cases self <;> rfl
    have tr : TEnv.get (aliasTarget self) (state false 1 42).env=some (aliasRef self) := by cases self <;> rfl
    have bound : (u 1).1.toNat<hp.len (aliasRef self) .dyn := by
      cases self <;> simp only [aliasRef,if_true,Heap.len,Heap.get,Objs.get,hp,left,neighbor,MObj.elems_dyn] <;> decide
    obtain ⟨mid,changed,mm,target,first,second,readSource,third,items,prog,prefixCode,code,whole,write,read,new,final,
      mok,finalOK,finalRepr,finalAlloc,rest⟩ :=
      source_uint_alias_write_read_word (G0 p) F0 fuel (sy false 1 42) dr (aliasSource self) di si di
        (aliasAddress self) (u 1) (u 42) sr rfl rfl SH (memOK false 1 42)
        (state false 1 42) dt (aliasTarget self) it jt it (aliasRef self) tr rfl rfl initial bound
        (initial_repr false 1 42) (allocator false 1 42) (by decide) rfl rfl
    have knownWrite : hp.writeAddr (.index (aliasRef self) .dyn (u 1)) (u 42)=some (mutationNative self) := by
      have hb : 1<(MObj.elems .dyn (hp.get (aliasRef self))).length := bound
      simp only [Heap.writeAddr,Heap.setIndex,show (u 1).1.toNat=1 from by decide,if_pos hb,mutationNative]
    have hm : mid=mutationNative self := Option.some.inj (write.symm.trans knownWrite)
    subst mid
    have hc : changed=mutationFinal self := congrArg Prod.snd (second.symm.trans (mutation_source p (fuel+1) self))
    subst changed
    have hmiddle : mm=mutationTarget self := (Out.ok.inj (prefixCode.symm.trans (dynamic_uint_alias_write_concrete p fuel self).2.2.1)).1
    subst mm
    have ht : target=readTarget self := (Out.ok.inj (code.symm.trans (read_into_word self))).1
    subst target
    exact ⟨items,prog,whole,third,final,finalOK,finalRepr,finalAlloc⟩

/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_write_read_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_write_read_concrete

/-- Complete ordered observations show the scalar/index slot changing
only after the reached heap read. All earlier three-stage vectors remain. -/
theorem dynamic_uint_alias_write_read_vectors (self : Bool) :
    words (machine false 1 42)=
      [w[40],w[32],w[16],w[16],w[24],w[42],w[1],w[0],w[99],w[3],w[7],w[0],.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],w[9]] ∧
    words (mutationPointer self)=
      [w[40],w[32],w[16],(if self then w[16] else w[32]),w[24],w[42],w[1],w[0],w[99],w[3],w[7],w[0],.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],w[9]] ∧
    words (mutationTarget self)=
      [w[40],w[32],w[16],(if self then w[16] else w[32]),w[24],w[42],w[1],w[0],w[99],w[3],w[7],(if self then w[42] else w[0]),.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],(if self then w[9] else w[42])] ∧
    words (readTarget self)=
      [w[40],w[32],w[16],(if self then w[16] else w[32]),w[24],w[42],w[42],w[0],w[99],w[3],w[7],(if self then w[42] else w[0]),.val wMax,w[3],w[2],w[9],w[1],w[2],w[8],(if self then w[9] else w[42])] ∧
    objects hp=[old,rhs,next] ∧
    objects (mutationNative self)=(if self then [old.set 1 (u 42),rhs,next] else [old,rhs,next.set 1 (u 42)]) ∧
    objects (readState self).heap=objects (mutationNative self) ∧
    sourceObjects (sy false 1 42)=
      [some ⟨SA,sourceUintMemory old⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory next⟩] ∧
    sourceObjects (mutationMid self)=sourceObjects (sy false 1 42) ∧
    sourceObjects (mutationFinal self)=(if self then
      [some ⟨SA,sourceUintMemory (old.set 1 (u 42))⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory next⟩] else
      [some ⟨SA,sourceUintMemory old⟩,some ⟨SA,sourceUintMemory rhs⟩,some ⟨SA,sourceUintMemory (next.set 1 (u 42))⟩]) ∧
    sourceObjects (readFinal self)=sourceObjects (mutationFinal self) ∧
    (readFinal self).1=.cons (sourceUint (u 42)) (.cons (sourceUint (u 42)) (.cons (.memRef rfl 1)
      (.cons (.memRef rfl (aliasAddress self)) (.cons (.memRef rfl 0) (.cons (.memRef rfl 2) .nil))))) ∧
    (readState self).env=(u 42,u 42,some right,some (aliasRef self),some left,some neighbor,()) ∧
    (readFinal self).2=(mutationFinal self).2 ∧
    (readFinal self).2.ex=(sy false 1 42).2.ex ∧
    (readFinal self).2.events=(sy false 1 42).2.events ∧
    (readFinal self).2.logs=(sy false 1 42).2.logs ∧
    (readFinal self).2.fnLocals=(sy false 1 42).2.fnLocals ∧
    ({readTarget self with mem := (machine false 1 42).mem} : Machine)=machine false 1 42 ∧
    (readTarget self).stack=[w[77],w[88]] ∧ (readTarget self).mem 0=w[40] := by
  first
  | solve | simp only [] | omega
  | cases self <;> simp only [Bool.false_eq_true,if_false,if_true]
    all_goals
      refine ⟨rfl,rfl,rfl,rfl,?_,?_,rfl,rfl,rfl,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
      · simp only [objects,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn]
      · simp only [objects,mutationNative,aliasRef,Bool.false_eq_true,if_false,if_true,Heap.set,Objs.set,Heap.get,Objs.get,hp,left,right,neighbor,MObj.elems_dyn,MObj.setElem_dyn]
      · simp only [sourceObjects,mutationFinal,mutationMid,aliasAddress,Bool.false_eq_true,if_false,if_true,
          Source.Heap.write_get,Source.Heap.write_other _ (show 0≠2 by decide),Source.Heap.write_other _ (show 1≠2 by decide),
          Source.Heap.write_other _ (show 1≠0 by decide),Source.Heap.write_other _ (show 2≠0 by decide)]
        rfl

/-- The real scalar store changes the next access to index42. This is a
separate reached read boundary, not a claimed four-statement Source theorem.
A stale-old-object Source read stores0 instead of the actual reached42. -/
theorem dynamic_uint_alias_write_read_boundary (p : Roadmap.Pipeline) (fuel : Nat) :
    words (readTarget false)≠words (mutationTarget false) ∧
    words (readTarget false)≠words (writeMachine (mutationTarget false) 6 w[0]) ∧
    (Source.evalE (G0 p) F0 (fuel+3) (sourceUintReadInto (.there (.there (.there (.there .here)))) di di)).run
      (mutationFinal false)=(.ok (.val (sourceUint (u 0))),((mutationFinal false).1.set di (sourceUint (u 0)),(mutationFinal false).2)) ∧
    (Source.evalE (G0 p) F0 (fuel+2) (.indexArray (.local dr) (.local di) rfl)).run (readFinal false)=
      (.error (.revert (Source.panicData .index)),readFinal false) ∧
    (Val.readMem (.index .dyn (.var dt rfl) (.simple (.local it))) : Val C Δ .uint).evalT (readState false)=.error .revert ∧
    run (readLocalCode (C := C) 1 dt (.simple (.local it))) (readTarget false)=.revert ∧
    run (((aliasLocalCode 1 dt (aliasTarget false)++uintAliasWriteCode (C := C) 1 dt it jt)++uintReadIntoCode (C := C) 1 dt it it)++
      readLocalCode (C := C) 1 dt (.simple (.local it))) (machine false 1 42)=.revert := by
  first
  | solve | simp only [] | omega
  | have oldNative : MObj.elems .dyn ((mutationNative false).get left)=old := by
      simp only [mutationNative,aliasRef,Bool.false_eq_true,if_false,Heap.set,Objs.set,Heap.get,Objs.get,hp,left,neighbor,MObj.elems_dyn,MObj.setElem_dyn]
    have oldAt : SourceUintMemoryAt (mutationFinal false) 0 (mutationNative false) left .dyn := by
      unfold SourceUintMemoryAt
      rw [oldNative]
      change ((sy false 1 42).2.heap.write 2 (sourceUintMemory (next.set 1 (u 42))) (by rfl)).get 0=some _
      rw [Source.Heap.write_other _ (show 0≠2 by decide)]
      rfl
    have oldRead := oldAt.eval_index (G0 p) F0 fuel (.there (.there (.there (.there .here)))) di (u 1) rfl rfl
      (by change (u 1).1.toNat<(MObj.elems .dyn ((mutationNative false).get left)).length;rw [oldNative];decide)
    have oldValue : (Source.evalE (G0 p) F0 (fuel+2)
        (.indexArray (.local (.there (.there (.there (.there .here)))) : Source.RExpr E0 Γ SA) (.local di) rfl)).run (mutationFinal false)=
        (.ok (.val (sourceUint (u 0))),mutationFinal false) := by simpa only [oldNative] using oldRead
    have actual := dynamic_uint_alias_write_read_concrete p fuel false
    have represented := actual.2.2.2.2.2.2.1
    have sourceAt := actual.2.2.2.2.1
    have contents : MObj.elems .dyn ((mutationNative false).get neighbor)=next.set 1 (u 42) := by
      change MObj.elems .dyn ((hp.set neighbor _).get neighbor)=_
      rw [Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn]
      rfl
    have outside : (mutationNative false).len neighbor .dyn≤(u 42).1.toNat := by
      change (MObj.elems .dyn ((mutationNative false).get neighbor)).length≤(u 42).1.toNat
      rw [contents,List.length_set]
      decide
    have sourceError := sourceAt.eval_read_bounds (G0 p) F0 fuel dr di (u 42) rfl rfl outside
    have noRead : (readState false).heap.readAddr (.index neighbor .dyn (u 42))=none := List.getElem?_eq_none outside
    have invalid : (Val.readMem (.index .dyn (.var dt rfl) (.simple (.local it))) : Val C Δ .uint).evalT (readState false)=.error .revert := by
      simp only [Val.evalT,MLoc.addrT,MPath.mvalT,Simple.evalT,
        show TEnv.get dt (readState false).env=some neighbor from rfl,
        show TEnv.get it (readState false).env=u 42 from rfl,noRead,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    have cert := Objects.PtrFrag.readPrimitive represented (Objects.PtrFrag.local dt rfl)
      (.dyn : ArrTy A (.prim .uint)) (.simple (.local it) : Val C Δ .uint) rfl
    change ValOutT .uint _ (run (readLocalCode 1 dt (.simple (.local it))) (readTarget false)) (readTarget false) at cert
    have wordError : run (readLocalCode (C := C) 1 dt (.simple (.local it))) (readTarget false)=.revert := by
      rw [invalid] at cert
      rcases cert with ⟨v,w,bad,_⟩ | ⟨_,revert⟩
      · cases bad
      · exact revert
    refine ⟨by decide,by decide,source_uint_read_into_of_run (G0 p) F0 fuel _ _ _ _ _ oldValue,
      sourceError,invalid,wordError,?_⟩
    rw [run_append_ok actual.2.2.1,wordError]

/-- The short three-statement Source run retains the actual material write
before scalar assignment times out. It returns only exposed error globals. -/
theorem dynamic_uint_alias_write_read_timeout (p : Roadmap.Pipeline) :
    (Source.execItems (G0 p) F0 6 Γ.length none
      (.stmt (.expr (sourceLocalAlias dr (aliasSource false)))
        (.stmt (.expr (sourceUintIndexedAssign dr di si)) .nil) : Source.RItems E0 [] false .body Γ Γ)
      (sy false 1 42).1).run (.nil,(sy false 1 42).2)=
      (.ok (.normal (mutationFinal false).1),(.nil,(mutationFinal false).2)) ∧
    (Source.evalE (G0 p) F0 2 (sourceUintReadInto dr di di)).run (mutationFinal false)=
      (.error .timeout,mutationFinal false) ∧
    (Source.execItems (G0 p) F0 6 Γ.length none
      (.stmt (.expr (sourceLocalAlias dr (aliasSource false)))
        (.stmt (.expr (sourceUintIndexedAssign dr di si)) (.stmt (.expr (sourceUintReadInto dr di di)) .nil)) :
          Source.RItems E0 [] false .body Γ Γ) (sy false 1 42).1).run (.nil,(sy false 1 42).2)=
      (.error .timeout,(.nil,(mutationFinal false).2)) := by
  first
  | solve | simp only [] | omega
  | have first := source_local_alias_run (G0 p) F0 2 (sy false 1 42) dr (aliasSource false) (.memRef rfl 2) rfl
    have second := mutation_source p 0 false
    have late : (Source.evalE (G0 p) F0 2 (sourceUintReadInto dr di di)).run (mutationFinal false)=
        (.error .timeout,mutationFinal false) := by cases p <;> rfl
    refine ⟨(dynamic_uint_alias_write_concrete p 0 false).1,late,?_⟩
    exact source_items_triple_error (G0 p) F0 2 Γ.length _ _ _ (sy false 1 42) (mutationMid false)
      (mutationFinal false) (mutationFinal false) .timeout
      (source_expr_statement_run (G0 p) F0 4 Γ.length _ _ _ _ first)
      (source_expr_statement_run (G0 p) F0 3 Γ.length _ _ _ _ second)
      (source_expr_statement_error (G0 p) F0 2 Γ.length _ _ _ _ late)

/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_write_read_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_write_read_vectors
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_write_read_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_write_read_boundary
/-- info: 'Solidity.Backend.MemoryOps.UintReadAssignmentControls.dynamic_uint_alias_write_read_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dynamic_uint_alias_write_read_timeout

end Solidity.Backend.MemoryOps.UintReadAssignmentControls
