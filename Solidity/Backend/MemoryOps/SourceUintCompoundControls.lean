import Solidity.Backend.MemoryOps.SourceUintCompound
import Solidity.Backend.MemoryOps.SourceUintMutationControls
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceUintCompoundControls
open Evm Evm.Memory
open Source.SemanticsExamples (E0 F0 s0)
private def C : Contract := {vars := []}
private abbrev A : RefTy := .array (.prim .uint)
private abbrev H : HTy := [A,A]
private abbrev Γ : Ctx := [.val .uint,.val .uint,.val .uint,.mem A,.mem A]
private abbrev SA : Source.STy := .array .memory (.int .u256) none
private abbrev SΓ : Source.RCtx := [.int .u256,.int .u256,.int .u256,SA,SA]
private def r : HRef H A := ⟨0,rfl⟩
private def neighbor : HRef H A := ⟨1,rfl⟩
private def vals (xs : List (Fin W)) := xs.map indexValue
private def hp (xs : List (Fin W)) (hfit : 17+xs.length≤80) : Heap H :=
  (⟨vals xs,by
    simp only [vals,List.length_map]
    have h : 80<2^256 := by decide
    omega⟩,
    ⟨[indexValue ⟨8,by decide⟩,indexValue ⟨9,by decide⟩],by decide⟩,())
private def σ (xs : List (Fin W)) (hfit : 17+xs.length≤80) (k l v : Fin W) : State C Γ :=
  {storage := Storage.init C,H := H,heap := hp xs hfit,env := (indexValue k,indexValue l,indexValue v,some r,some r,())}
private def base (n : Nat) : Fin W := if n=0 then ⟨16,by decide⟩ else ⟨80,by decide⟩
private def machine (xs : List (Fin W)) (k l v : Fin W) : Machine :=
  {Machine.init with stack := [w[42]],mem := fun a =>
    if a=0 then w[96] else
    if a=1 then w[16] else
    if a=2 then w[16] else
    if a=3 then (Word.val v) else
    if a=4 then (Word.val l) else
    if a=5 then (Word.val k) else
    if a=7 then w[99] else
    if a=16 then Word.val (wmod xs.length) else
    if h : 17≤a ∧ a<17+xs.length then Word.val xs[a-17] else
    if a=80 then w[2] else
    if a=81 then w[8] else
    if a=82 then w[9] else w[0]}
private theorem elems (xs : List (Fin W)) (hf : 17+xs.length≤80) : MObj.elems .dyn ((hp xs hf).get r)=vals xs := by
  simp only [Heap.get,Objs.get,hp,r,MObj.elems_dyn]
private theorem neighbor_elems (xs : List (Fin W)) (hf : 17+xs.length≤80) : MObj.elems .dyn ((hp xs hf).get neighbor)=[indexValue ⟨8,by decide⟩,indexValue ⟨9,by decide⟩] := by
  simp only [Heap.get,Objs.get,hp,neighbor,MObj.elems_dyn]
private theorem refs {p : PrimTy} (q : HRef H (.array (.prim p))) : p=.uint ∧ (HEq q r ∨ HEq q neighbor) := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi;exact ⟨rfl,.inl HEq.rfl⟩
  | succ i => cases i with
    | zero => cases hi;exact ⟨rfl,.inr HEq.rfl⟩
    | succ i => cases hi
private def y0 : Source.EMState E0 [] := (.nil,s0)
private def ys (xs : List (Fin W)) : Source.EMState E0 [] :=
  ((Source.allocRef (sourceUintMemory [indexValue ⟨8,by decide⟩,indexValue ⟨9,by decide⟩])).run
    ((Source.allocRef (sourceUintMemory (vals xs))).run y0).2).2
private def sy (xs : List (Fin W)) (k l v : Fin W) : Source.EMState E0 SΓ :=
  (.cons (sourceUint (indexValue k)) (.cons (sourceUint (indexValue l)) (.cons (sourceUint (indexValue v))
    (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil)))),(ys xs).2)
private abbrev SH := (Source.Heap.empty (D := E0.layout)).ty
private def ti : Idx Γ (.val .uint) := .here
private def tj : Idx Γ (.val .uint) := .there .here
private def tv : Idx Γ (.val .uint) := .there (.there .here)
private def tr : Idx Γ (.mem A) := .there (.there (.there .here))
private def si : Source.Idx SΓ (.int .u256) := .here
private def sj : Source.Idx SΓ (.int .u256) := .there .here
private def sv : Source.Idx SΓ (.int .u256) := .there (.there .here)
private def sr : Source.Idx SΓ SA := .there (.there (.there .here))
private def salias : Source.Idx SΓ SA := .there (.there (.there (.there .here)))
private def assignCode := writeLocalCode (C := C) 1 tr (.simple (.local ti)) (.simple (.local tv))
private def deleteCode := deleteLocalCode 1 tr (compileVal 1 (.simple (.local tj) : Val C Γ .uint))
private def contentWords (m : Machine) (n : Nat) := List.ofFn (fun i : Fin n => m.mem (17+i.val))
private def frameWords (m : Machine) := [m.mem 0,m.mem 1,m.mem 2,m.mem 3,m.mem 4,m.mem 5,m.mem 6,m.mem 7,m.mem 8,m.mem 9,m.mem 10,m.mem 16,m.mem 80,m.mem 81,m.mem 82,m.mem 96]

private theorem views (xs : List (Fin W)) (hf : 17+xs.length≤80) (k l v : Fin W) :
    Source.MemOK E0 SH (sy xs k l v) ∧ SourceUintMemoryAt (sy xs k l v) 0 (hp xs hf) r .dyn ∧
    SourceUintMemoryAt (sy xs k l v) 1 (hp xs hf) neighbor .dyn ∧
    StateRepr 1 1 8 (Frag.init Γ) (σ xs hf k l v) base (machine xs k l v) :=
  SourceUintMutationControls.initial_views xs hf k l v
private theorem no_struct {s : Name} (q : HRef H (.struct s)) : False := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi
  | succ i => cases i with
    | zero => cases hi
    | succ i => cases hi
private theorem initial_allocator (xs : List (Fin W)) (hf : 17+xs.length≤80) (k l v : Fin W) : StructAllocatorRepr (hp xs hf) base 8 ⟨96,by decide⟩ (machine xs k l v) := by
  apply AllocatorRepr.withoutStructs (hn := fun q => no_struct q)
  refine ⟨((views xs hf k l v).2.2.2).heap,⟨by decide,by decide,rfl,?_⟩,?_⟩
  · intro a ha
    change 96≤a at ha
    change (machine xs k l v).mem a=w[0]
    simp only [machine]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),dif_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  · intro p q
    obtain ⟨rfl,hq|hq⟩ := refs q <;> cases hq
    · change 16+1+(hp xs hf).len r .dyn≤96
      simp only [Heap.len,elems,vals,List.length_map];omega
    · change 80+1+(hp xs hf).len neighbor .dyn≤96
      rw [Heap.len,neighbor_elems];decide
private theorem assign_run (m : Machine) (n : Nat) (k v : Fin W) (hf : 17+n≤80) (hk : k.val<n)
    (hptr : m.mem 2=w[16]) (hi : m.mem 5=.val k) (hv : m.mem 3=.val v) (hlen : m.mem 16=.val (wmod n)) :
    run assignCode m=.ok (writeMachine m (16+1+k.val) (.val v)) 0 := by
  change run ([.mload 3]++([.mload 2]++([.mload 5]++writeArrayStackCode))) m=_
  rw [run_append_ok (show run [.mload 3] m=.ok (m.push (.val v)) 0 from by change Out.ok (m.push (m.mem 3)) 0=_;rw [hv])]
  rw [run_append_ok (show run [.mload 2] (m.push (.val v))=.ok ((m.push (.val v)).push w[16]) 0 from by change Out.ok ((m.push (.val v)).push (m.mem 2)) 0=_;rw [hptr])]
  rw [run_append_ok (show run [.mload 5] ((m.push (.val v)).push w[16])=.ok (((m.push (.val v)).push w[16]).push (.val k)) 0 from by change Out.ok (((m.push (.val v)).push w[16]).push (m.mem 5)) 0=_;rw [hi])]
  have hn : n<W := by
    have h : 80<W := by decide
    omega
  have ha := arrayAddrStack_run (m.push (.val v)) ⟨16,by decide⟩ k n hn (by simpa only [Machine.push] using hlen)
  rw [if_pos hk] at ha
  rw [writeArrayStackCode,run_append_ok ha]
  have hw : 16+1+k.val<W := by
    have h : 80<W := by decide
    omega
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt hw,Out.ok_bind,exec_nil,writeMachine]
private def addCode := uintAddLocalCode (C := C) 1 tr ti tv
private theorem read_run (m : Machine) (n : Nat) (k old : Fin W) (hn : n<W) (hk : k.val<n)
    (ha : 17+k.val<W) (hptr : m.mem 2=w[16]) (hi : m.mem 5=.val k)
    (hlen : m.mem 16=.val (wmod n)) (hcell : m.mem (17+k.val)=.val old) :
    run (readLocalCode (C := C) 1 tr (.simple (.local ti))) m=.ok (m.push (.val old)) 0 := by
  change run ([.mload 2]++([.mload 5]++readArrayStackCode)) m=_
  rw [run_append_ok (show run [.mload 2] m=.ok (m.push w[16]) 0 from by change Out.ok (m.push (m.mem 2)) 0=_;rw [hptr])]
  rw [run_append_ok (show run [.mload 5] (m.push w[16])=.ok ((m.push w[16]).push (.val k)) 0 from by change Out.ok ((m.push w[16]).push (m.mem 5)) 0=_;rw [hi])]
  have haddr := arrayAddrStack_run m ⟨16,by decide⟩ k n hn hlen
  rw [if_pos hk] at haddr
  rw [readArrayStackCode,run_append_ok haddr]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt ha,Out.ok_bind,exec_nil,hcell,Machine.next]
private theorem add_run (m : Machine) (n : Nat) (k old v : Fin W) (hn : n<W) (hk : k.val<n)
    (ha : 17+k.val<W) (hptr : m.mem 2=w[16]) (hi : m.mem 5=.val k) (hv : m.mem 3=.val v)
    (hlen : m.mem 16=.val (wmod n)) (hcell : m.mem (17+k.val)=.val old)
    (hsum : old.val+v.val<W) :
    run addCode m=.ok (writeMachine m (17+k.val) (.val ⟨old.val+v.val,hsum⟩)) 0 := by
  have hr := read_run m n k old hn hk ha hptr hi hlen hcell
  have hvalue : run (binaryCode .uint .add (readLocalCode (C := C) 1 tr (.simple (.local ti))) [.mload 3]) m=
      .ok (m.push (.val ⟨old.val+v.val,hsum⟩)) 0 := by
    change run ((readLocalCode (C := C) 1 tr (.simple (.local ti)))++([.mload 3]++uTail .add)) m=_
    rw [run_append_ok hr]
    rw [run_append_ok (show run [.mload 3] (m.push (.val old))=.ok ((m.push (.val old)).push (.val v)) 0 from by change Out.ok ((m.push (.val old)).push (m.mem 3)) 0=_;rw [hv])]
    exact (add_tail m m.stack old.isLt v.isLt).trans (by rw [dif_pos hsum];rfl)
  change run ((binaryCode .uint .add (readLocalCode (C := C) 1 tr (.simple (.local ti))) [.mload 3])++([.mload 2]++([.mload 5]++writeArrayStackCode))) m=_
  rw [run_append_ok hvalue]
  rw [run_append_ok (show run [.mload 2] (m.push (.val ⟨old.val+v.val,hsum⟩))=.ok ((m.push (.val ⟨old.val+v.val,hsum⟩)).push w[16]) 0 from by change Out.ok ((m.push (.val ⟨old.val+v.val,hsum⟩)).push (m.mem 2)) 0=_;rw [hptr])]
  rw [run_append_ok (show run [.mload 5] ((m.push (.val ⟨old.val+v.val,hsum⟩)).push w[16])=.ok (((m.push (.val ⟨old.val+v.val,hsum⟩)).push w[16]).push (.val k)) 0 from by change Out.ok (((m.push (.val ⟨old.val+v.val,hsum⟩)).push w[16]).push (m.mem 5)) 0=_;rw [hi])]
  have haddr := arrayAddrStack_run (m.push (.val ⟨old.val+v.val,hsum⟩)) ⟨16,by decide⟩ k n hn hlen
  rw [if_pos hk] at haddr
  rw [writeArrayStackCode,run_append_ok haddr]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt ha,Out.ok_bind,exec_nil,writeMachine]

private def one : Fin W := ⟨1,by decide⟩
private def three : Fin W := ⟨3,by decide⟩
private def six : Fin W := ⟨6,by decide⟩
private def maximum : Fin W := ⟨W-1,Nat.sub_lt W_pos (by decide)⟩
private def xs : List (Fin W) := [⟨7,by decide⟩,⟨0,W_pos⟩,maximum]
private theorem fit : 17+xs.length≤80 := by decide
private def items : Source.RItems E0 [] false .body SΓ SΓ :=
  .stmt (.expr (sourceUintIndexedAssign sr si sv)) (.stmt (.expr (sourceUintIndexedAdd sr si sv)) .nil)
private def prog : Prog C Γ Γ := .cons (.assignMem (.index .dyn (.var tr rfl) (.simple (.local ti))) (.val (.simple (.local tv))))
  (.cons (.opAssign .add rfl rfl (.mindex .dyn (.var tr rfl) (.local ti)) (.simple (.local tv))) .nil)

/-- The numeric update reads the actual changed prefix (3), not the initial0.
Complete Source/intrinsic/word observations retain max, aliases and neighbor. -/
theorem changed_prefix (p : Roadmap.Pipeline) :
    ∃ (mid out : Heap H) (ym z : Source.EMState E0 SΓ) (mm mf : Machine),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none items (sy xs one one three).1).run (.nil,(sy xs one one three).2)=
        (.ok (.normal (sy xs one one three).1),(.nil,z.2)) ∧
      Prog.run (σ xs fit one one three) prog=.ok ⟨(σ xs fit one one three).withHeap out,List.prefix_refl _⟩ ∧
      run assignCode (machine xs one one three)=.ok mm 0 ∧
      run (assignCode++addCode) (machine xs one one three)=.ok mf 0 ∧
      [MObj.elems .dyn ((hp xs fit).get r),MObj.elems .dyn (mid.get r),MObj.elems .dyn (out.get r)]=
        [vals xs,vals [⟨7,by decide⟩,three,maximum],vals [⟨7,by decide⟩,six,maximum]] ∧
      [(sy xs one one three).2.heap.get 0,ym.2.heap.get 0,z.2.heap.get 0]=
        [some ⟨SA,sourceUintMemory (vals xs)⟩,some ⟨SA,sourceUintMemory (vals [⟨7,by decide⟩,three,maximum])⟩,
          some ⟨SA,sourceUintMemory (vals [⟨7,by decide⟩,six,maximum])⟩] ∧
      [contentWords (machine xs one one three) 3,contentWords mm 3,contentWords mf 3]=
        [[w[7],w[0],.val maximum],[w[7],w[3],.val maximum],[w[7],w[6],.val maximum]] ∧
      [frameWords (machine xs one one three),frameWords mm,frameWords mf]=
        List.replicate 3 [w[96],w[16],w[16],w[3],w[1],w[1],w[0],w[99],w[0],w[0],w[0],w[3],w[2],w[8],w[9],w[0]] ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local salias) (.local si) rfl)).run ym=
        (.ok (.val (sourceUint (indexValue three))),ym) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local salias) (.local si) rfl)).run z=
        (.ok (.val (sourceUint (indexValue six))),z) ∧
      z.2.heap.get 1=(sy xs one one three).2.heap.get 1 ∧ out.get neighbor=(hp xs fit).get neighbor ∧
      mf.stack=[w[42]] ∧ mf.mem 0=w[96] ∧ mf.mem 1=w[16] ∧ mf.mem 2=w[16] ∧
      [(sy xs one one three).2.heap.get 1,ym.2.heap.get 1,z.2.heap.get 1]=
        List.replicate 3 (some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩) ∧
      [(hp xs fit).get neighbor,mid.get neighbor,out.get neighbor]=List.replicate 3 ((hp xs fit).get neighbor) ∧
      z.1=(sy xs one one three).1 ∧
      z.2.ex=(sy xs one one three).2.ex ∧ z.2.events=(sy xs one one three).2.events ∧
      z.2.logs=(sy xs one one three).2.logs ∧ z.2.fnLocals=(sy xs one one three).2.fnLocals ∧
      StructAllocatorRepr out base 8 ⟨96,by decide⟩ mf ∧ Source.MemOK E0 SH z := by
  obtain ⟨hmem,hr,hn,hm⟩ := views xs fit one one three
  obtain ⟨mid,ym,mm,hw1,hsw1,he1,hs1,hi1,hc1,hr1,hm1,hmem1,hy1,hstack1,ha1⟩ :=
    resolved_uint_assign_word (Source.SemanticsExamples.G0 p) F0 1 (σ xs fit one one three) r hr
      sr si sv tr ti tv (indexValue one) (indexValue three) rfl rfl rfl rfl rfl rfl (by change (indexValue one).1.toNat<(hp xs fit).len r .dyn;rw [Heap.len,elems];decide) hm SH hmem
  have e1 : MObj.elems .dyn (mid.get r)=vals [⟨7,by decide⟩,three,maximum] := by
    rw [indexedWrite_elems _ _ r .dyn _ _ hw1];change ((MObj.elems .dyn ((hp xs fit).get r)).set (indexValue one).1.toNat (indexValue three))=_;rw [elems];rfl
  have hk : (indexValue one).1.toNat<mid.len r .dyn := by rw [Heap.len,e1];decide
  have hget : (MObj.elems .dyn (mid.get r))[(indexValue one).1.toNat]?=some (indexValue three) := by rw [e1];rfl
  have hold : (MObj.elems .dyn (mid.get r))[(indexValue one).1.toNat]=indexValue three :=
    Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hget)
  have hadd : PrimTy.uint.inRange ((MObj.elems .dyn (mid.get r))[(indexValue one).1.toNat].1+(indexValue three).1)=true := by rw [hold];decide
  obtain ⟨out,z,mf,hw2,hsw2,he2,hs2,hi2,hc2,hr2,hm2,hmem2,hy2,hstack2,ha2⟩ :=
    resolved_uint_add_word (Source.SemanticsExamples.G0 p) F0 0 ((σ xs fit one one three).withHeap mid) r hr1
      sr si sv tr ti tv (indexValue one) (indexValue three) (by rw [hy1];rfl) (by rw [hy1];rfl) (by rw [hy1];rfl)
      rfl rfl rfl hk hadd hm1 SH hmem1
  have hnew : (⟨(MObj.elems .dyn (mid.get r))[(indexValue one).1.toNat].1+(indexValue three).1,hadd⟩ : PrimTy.uint.Denote)=indexValue six := by
    apply Subtype.ext
    change (MObj.elems .dyn (mid.get r))[(indexValue one).1.toNat].1+(indexValue three).1=(indexValue six).1
    rw [hold]
    rfl
  change mid.writeAddr (.index r .dyn (indexValue one)) ⟨(MObj.elems .dyn (mid.get r))[(indexValue one).1.toNat].1+(indexValue three).1,hadd⟩=some out at hw2
  dsimp only [State.withHeap] at hsw2 he2
  rw [hnew] at hw2 hsw2 he2
  have e2 : MObj.elems .dyn (out.get r)=vals [⟨7,by decide⟩,six,maximum] := by
    rw [indexedWrite_elems _ _ r .dyn _ _ hw2,e1];rfl
  have hc1' : run assignCode (machine xs one one three)=.ok (writeMachine (machine xs one one three) 18 w[3]) 0 := assign_run _ 3 one three (by decide) (by decide) rfl rfl rfl rfl
  have hmm : mm=writeMachine (machine xs one one three) 18 w[3] := (Out.ok.inj (hc1.symm.trans hc1')).1
  subst mm
  have hc2' := add_run (writeMachine (machine xs one one three) 18 w[3]) 3 one three three (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl (by decide)
  have hmf : mf=writeMachine (writeMachine (machine xs one one three) 18 w[3]) 18 w[6] := (Out.ok.inj (hc2.symm.trans hc2')).1
  subst mf
  have hitems := source_items_pair_run (Source.SemanticsExamples.G0 p) F0 0 SΓ.length
    (.expr (sourceUintIndexedAssign sr si sv)) (.expr (sourceUintIndexedAdd sr si sv)) (sy xs one one three) ym z
    (by simpa only [hy1] using hs1) (by simpa only [hy2] using hs2)
  have hloc1 : ym.1.get salias=.memRef rfl 0 := by rw [hy1];rfl
  have hloc2 : z.1.get salias=.memRef rfl 0 := by rw [hy2,hy1];rfl
  have hidx1 : ym.1.get si=sourceUint (indexValue one) := by rw [hy1];rfl
  have hidx2 : z.1.get si=sourceUint (indexValue one) := by rw [hy2,hy1];rfl
  have hread1 := hr1.eval_index (Source.SemanticsExamples.G0 p) F0 0 salias si (indexValue one) hloc1 hidx1 hk
  have hread2 := hr2.eval_index (Source.SemanticsExamples.G0 p) F0 0 salias si (indexValue one) hloc2 hidx2 (by rw [Heap.len,e2];change 1<3;decide)
  have f1 := hr.write_frames F0 3 (indexValue one) (indexValue three) (by change (indexValue one).1.toNat<(hp xs fit).len r .dyn;rw [Heap.len,elems];decide) hw1 hsw1
  have f2 := hr1.write_frames F0 2 (indexValue one) (indexValue six) hk hw2 hsw2
  have hallocator := ha2 ⟨96,by decide⟩ (by decide) (ha1 ⟨96,by decide⟩ (by decide) (initial_allocator xs fit one one three))
  refine ⟨mid,out,ym,z,writeMachine (machine xs one one three) 18 w[3],writeMachine (writeMachine (machine xs one one three) 18 w[3]) 18 w[6],?_,intrinsic_heap_pair_run _ _ _ _ _ hi1 hi2,hc1,?_,?_,?_,rfl,rfl,?_,?_,?_,?_,rfl,rfl,rfl,rfl,?_,?_,hy2.trans hy1,?_,?_,?_,?_,hallocator,hmem2⟩
  · simpa only [items,hy2,hy1] using hitems
  · rw [assignCode,run_append_ok hc1];exact hc2
  · rw [e1,e2];change [MObj.elems .dyn ((hp xs fit).get r),_,_]=_;rw [elems]
  · change [(sy xs one one three).2.heap.get 0,ym.2.heap.get 0,z.2.heap.get 0]=_
    rw [hr,hr1,hr2,elems,e1,e2]
  · simpa only [e1,vals,List.getElem_cons_zero,List.getElem_cons_succ,SourceUintMemoryAt] using hread1
  · simpa only [e2,vals,List.getElem_cons_zero,List.getElem_cons_succ,SourceUintMemoryAt] using hread2
  · exact (f2.2.2.1 1 (by decide)).trans (f1.2.2.1 1 (by decide))
  · exact (indexedWrite_frame _ _ r .dyn _ _ hw2 neighbor (by decide)).trans (indexedWrite_frame _ _ r .dyn _ _ hw1 neighbor (by decide))

  · rw [f2.2.2.1 1 (by decide),f1.2.2.1 1 (by decide)];rfl
  · rw [indexedWrite_frame _ _ r .dyn _ _ hw2 neighbor (by decide),indexedWrite_frame _ _ r .dyn _ _ hw1 neighbor (by decide)];rfl
  · exact f2.2.2.2.2.1.trans f1.2.2.2.2.1
  · exact f2.2.2.2.2.2.1.trans f1.2.2.2.2.2.1
  · exact f2.2.2.2.2.2.2.1.trans f1.2.2.2.2.2.2.1
  · exact f2.2.2.2.2.2.2.2.trans f1.2.2.2.2.2.2.2

/-- A frozen INITIAL read would return3, while the actual reached update returns6. -/
theorem frozen_initial_negative (p : Roadmap.Pipeline) :
    ∃ (z : Source.EMState E0 SΓ),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none items (sy xs one one three).1).run (.nil,(sy xs one one three).2)=
        (.ok (.normal (sy xs one one three).1),(.nil,z.2)) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local salias) (.local si) rfl)).run z=
        (.ok (.val (sourceUint (indexValue six))),z) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local salias) (.local si) rfl)).run z≠
        (.ok (.val (sourceUint (indexValue three))),z) := by
  obtain ⟨mid,out,ym,z,mm,mf,hi,hip,hc1,hc,hvals,htables,hwords,hframes,hread1,hread2,tail⟩ := changed_prefix p
  refine ⟨z,hi,hread2,?_⟩
  intro he
  have h := Except.ok.inj (congrArg Prod.fst (hread2.symm.trans he))
  have hv := congrArg (fun v : Source.RVal E0.layout (.int .u256) => v.get.map (fun w => calldataUint (.val w))) h
  change (Except.ok (indexValue six) : Except Source.Halt PrimTy.uint.Denote)=Except.ok (indexValue three) at hv
  have hn := congrArg Subtype.val (Except.ok.inj hv)
  exact (by decide : (6 : Int)≠3) hn

private theorem add_revert (m : Machine) (n : Nat) (k old v : Fin W) (hn : n<W) (hk : k.val<n)
    (ha : 17+k.val<W) (hptr : m.mem 2=w[16]) (hi : m.mem 5=.val k) (hv : m.mem 3=.val v)
    (hlen : m.mem 16=.val (wmod n)) (hcell : m.mem (17+k.val)=.val old) (hsum : ¬old.val+v.val<W) :
    run addCode m=.revert := by
  have hr := read_run m n k old hn hk ha hptr hi hlen hcell
  have hvalue : run (binaryCode .uint .add (readLocalCode (C := C) 1 tr (.simple (.local ti))) [.mload 3]) m=.revert := by
    change run ((readLocalCode (C := C) 1 tr (.simple (.local ti)))++([.mload 3]++uTail .add)) m=_
    rw [run_append_ok hr]
    rw [run_append_ok (show run [.mload 3] (m.push (.val old))=.ok ((m.push (.val old)).push (.val v)) 0 from by change Out.ok ((m.push (.val old)).push (m.mem 3)) 0=_;rw [hv])]
    exact (add_tail m m.stack old.isLt v.isLt).trans (by rw [dif_neg hsum])
  change run ((binaryCode .uint .add (readLocalCode (C := C) 1 tr (.simple (.local ti))) [.mload 3])++([.mload 2]++([.mload 5]++writeArrayStackCode))) m=_
  exact run_append_revert hvalue

/-- The same INITIAL represented max cell yields real Source arithmetic panic
and raw complete-word revert, distinct observations with no suffix machine. -/
theorem max_overflow (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintIndexedAdd sr si sv)).run (sy xs ⟨2,by decide⟩ one one)=
      (.error (.revert (Source.panicData .arithmetic)),sy xs ⟨2,by decide⟩ one one) ∧
    run addCode (machine xs ⟨2,by decide⟩ one one)=.revert ∧
    [(sy xs ⟨2,by decide⟩ one one).2.heap.get 0,(sy xs ⟨2,by decide⟩ one one).2.heap.get 1]=
      [some ⟨SA,sourceUintMemory (vals xs)⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩] ∧
    contentWords (machine xs ⟨2,by decide⟩ one one) 3=[w[7],w[0],.val maximum] := by
  obtain ⟨hmem,hr,hn,hm⟩ := views xs fit ⟨2,by decide⟩ one one
  have hs : ¬maximum.val+one.val<W := by
    change ¬W-1+1<W
    have h := W_pos
    omega
  have hb : PrimTy.uint.inRange ((indexValue maximum).1+(indexValue one).1)≠true := by
    intro h
    have hv : 0≤(indexValue maximum).1+(indexValue one).1 ∧ (indexValue maximum).1+(indexValue one).1<((2^256 : Nat) : Int) := of_decide_eq_true h
    have hw : ((W-1 : Nat) : Int)+1=(W : Int) := by have h := W_pos;omega
    change 0≤((W-1 : Nat) : Int)+1 ∧ ((W-1 : Nat) : Int)+1<(W : Int) at hv
    omega
  have he := hr.compound_add_overflow (Source.SemanticsExamples.G0 p) F0 0 rfl sr si sv (indexValue ⟨2,by decide⟩) (indexValue one)
    rfl rfl rfl (by rw [Heap.len,elems];change 2<3;decide) (by simpa only [elems,vals,xs,List.getElem_map,List.getElem_cons_zero,List.getElem_cons_succ,indexValue,Int.toNat_natCast] using hb)
  exact ⟨he,add_revert _ 3 ⟨2,by decide⟩ maximum one (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl hs,rfl,rfl⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintCompoundControls.changed_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms changed_prefix
/-- info: 'Solidity.Backend.MemoryOps.SourceUintCompoundControls.frozen_initial_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frozen_initial_negative
/-- info: 'Solidity.Backend.MemoryOps.SourceUintCompoundControls.max_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms max_overflow
end Solidity.Backend.MemoryOps.SourceUintCompoundControls
