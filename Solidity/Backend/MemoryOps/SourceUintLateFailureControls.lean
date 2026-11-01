import Solidity.Backend.MemoryOps.SourceUintLateFailure
import Solidity.Backend.MemoryOps.SourceUintCompoundControls
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceUintLateFailureControls
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
private def addCode := uintAddLocalCode (C := C) 1 tr ti tj
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
    (ha : 17+k.val<W) (hptr : m.mem 2=w[16]) (hi : m.mem 5=.val k) (hv : m.mem 4=.val v)
    (hlen : m.mem 16=.val (wmod n)) (hcell : m.mem (17+k.val)=.val old)
    (hsum : old.val+v.val<W) :
    run addCode m=.ok (writeMachine m (17+k.val) (.val ⟨old.val+v.val,hsum⟩)) 0 := by
  have hr := read_run m n k old hn hk ha hptr hi hlen hcell
  have hvalue : run (binaryCode .uint .add (readLocalCode (C := C) 1 tr (.simple (.local ti))) [.mload 4]) m=
      .ok (m.push (.val ⟨old.val+v.val,hsum⟩)) 0 := by
    change run ((readLocalCode (C := C) 1 tr (.simple (.local ti)))++([.mload 4]++uTail .add)) m=_
    rw [run_append_ok hr]
    rw [run_append_ok (show run [.mload 4] (m.push (.val old))=.ok ((m.push (.val old)).push (.val v)) 0 from by change Out.ok ((m.push (.val old)).push (m.mem 4)) 0=_;rw [hv])]
    exact (add_tail m m.stack old.isLt v.isLt).trans (by rw [dif_pos hsum];rfl)
  change run ((binaryCode .uint .add (readLocalCode (C := C) 1 tr (.simple (.local ti))) [.mload 4])++([.mload 2]++([.mload 5]++writeArrayStackCode))) m=_
  rw [run_append_ok hvalue]
  rw [run_append_ok (show run [.mload 2] (m.push (.val ⟨old.val+v.val,hsum⟩))=.ok ((m.push (.val ⟨old.val+v.val,hsum⟩)).push w[16]) 0 from by change Out.ok ((m.push (.val ⟨old.val+v.val,hsum⟩)).push (m.mem 2)) 0=_;rw [hptr])]
  rw [run_append_ok (show run [.mload 5] ((m.push (.val ⟨old.val+v.val,hsum⟩)).push w[16])=.ok (((m.push (.val ⟨old.val+v.val,hsum⟩)).push w[16]).push (.val k)) 0 from by change Out.ok (((m.push (.val ⟨old.val+v.val,hsum⟩)).push w[16]).push (m.mem 5)) 0=_;rw [hi])]
  have haddr := arrayAddrStack_run (m.push (.val ⟨old.val+v.val,hsum⟩)) ⟨16,by decide⟩ k n hn hlen
  rw [if_pos hk] at haddr
  rw [writeArrayStackCode,run_append_ok haddr]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt ha,Out.ok_bind,exec_nil,writeMachine]

private theorem contents_initial (xs : List (Fin W)) (hf : 17+xs.length≤80) (k l v : Fin W) : contentWords (machine xs k l v) xs.length=xs.map Word.val := by
  apply List.ext_getElem
  · simp only [contentWords,List.length_ofFn,List.length_map]
  · intro i hi hj
    simp only [contentWords,List.getElem_ofFn,List.getElem_map]
    have hb : i<xs.length := by simpa only [contentWords,List.length_ofFn] using hi
    have he : (MObj.elems .dyn ((hp xs hf).get r))[i]?=some (indexValue xs[i]) := by
      rw [elems]
      simp only [vals,List.getElem?_map,List.getElem?_eq_getElem hb,Option.map_some]
    obtain ⟨a,hw,hv⟩ := (((views xs hf k l v).2.2.2).heap.arrays r).elements i _ he
    have ha : a=xs[i] := by
      apply Fin.ext
      change (xs[i].val : Int)=a.val at hv
      omega
    rw [ha] at hw
    exact hw
private theorem contents_write (m : Machine) (n k : Nat) (w : Word) (_hk : k<n) :
    contentWords (writeMachine m (17+k) w) n=(contentWords m n).set k w := by
  apply List.ext_getElem
  · simp only [contentWords,List.length_ofFn,List.length_set]
  · intro i hi hj
    simp only [contentWords,List.getElem_ofFn,List.getElem_set,writeMachine,upd]
    by_cases he : k=i
    · subst i;simp only [↓reduceIte]
    · rw [if_neg (by omega),if_neg he]
private theorem frame_write (m : Machine) (a : Nat) (w : Word) (ha : 17≤a ∧ a<80) : frameWords (writeMachine m a w)=frameWords m := by
  simp only [frameWords,writeMachine,upd]
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
private theorem frame_initial (xs : List (Fin W)) (hf : 17+xs.length≤80) (k l v : Fin W) :
    frameWords (machine xs k l v)=[w[96],w[16],w[16],.val v,.val l,.val k,w[0],w[99],w[0],w[0],w[0],.val (wmod xs.length),w[2],w[8],w[9],w[0]] := by
  simp only [frameWords,machine]
  rw [dif_neg (show ¬(17≤80 ∧ 80<17+xs.length) from by omega),
    dif_neg (show ¬(17≤81 ∧ 81<17+xs.length) from by omega),
    dif_neg (show ¬(17≤82 ∧ 82<17+xs.length) from by omega),
    dif_neg (show ¬(17≤96 ∧ 96<17+xs.length) from by omega)]
  rfl

private def zero : Fin W := ⟨0,W_pos⟩
private def one : Fin W := ⟨1,by decide⟩
private def maximum : Fin W := ⟨W-1,Nat.sub_lt W_pos (by decide)⟩
private theorem max_add_one_invalid : PrimTy.uint.inRange ((indexValue maximum).1+(indexValue one).1)≠true := by
  intro h
  have hv : 0≤(indexValue maximum).1+(indexValue one).1 ∧ (indexValue maximum).1+(indexValue one).1<((2^256 : Nat) : Int) := of_decide_eq_true h
  have hw : ((W-1 : Nat) : Int)+1=(W : Int) := by have h := W_pos;omega
  change 0≤((W-1 : Nat) : Int)+1 ∧ ((W-1 : Nat) : Int)+1<(W : Int) at hv
  omega
private theorem max_ne_zero : indexValue maximum≠indexValue zero := by
  intro h
  have hv := congrArg Subtype.val h
  change ((W-1 : Nat) : Int)=0 at hv
  have hw : 1<W := by decide
  omega
private def items : Source.RItems E0 [] false .body SΓ SΓ :=
  .stmt (.expr (sourceUintIndexedAssign sr si sv)) (.stmt (.expr (sourceUintIndexedAdd sr si sj)) .nil)
private def prog : Prog C Γ Γ :=
  .cons (.assignMem (.index .dyn (.var tr rfl) (.simple (.local ti))) (.val (.simple (.local tv))))
    (.cons (.opAssign .add rfl rfl (.mindex .dyn (.var tr rfl) (.local ti)) (.simple (.local tj))) .nil)
private def tables (y : Source.EMState E0 SΓ) := [y.2.heap.get 0,y.2.heap.get 1]

/-- A runtime-indexed populated family: first0-to-max really changes the cell;
the actual reached max-plus1 rejects. Every ordered prefix observation is kept.
The finite separated word-layout capacity is a witness condition, not admission. -/
theorem reached_overflow (p : Roadmap.Pipeline) (xs : List (Fin W)) (hf : 17+xs.length≤80)
    (k : Fin W) (hk : k.val<xs.length) (hz : xs[k.val]=zero) :
    ∃ (mid : Heap H) (ym : Source.EMState E0 SΓ) (mm : Machine),
      (Source.execS (Source.SemanticsExamples.G0 p) F0 5 SΓ.length none (.expr (sourceUintIndexedAssign sr si sv) : Source.RStmt E0 [] false .body SΓ SΓ) (sy xs k one maximum).1).run (.nil,(sy xs k one maximum).2)=
        (.ok (.normal (sy xs k one maximum).1),(.nil,ym.2)) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintIndexedAdd sr si sj)).run ym=
        (.error (.revert (Source.panicData .arithmetic)),ym) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none items (sy xs k one maximum).1).run (.nil,(sy xs k one maximum).2)=
        (.error (.revert (Source.panicData .arithmetic)),(.nil,ym.2)) ∧
      Prog.run (σ xs hf k one maximum) prog=.error .revert ∧
      run assignCode (machine xs k one maximum)=.ok mm 0 ∧ run addCode mm=.revert ∧
      run (assignCode++addCode) (machine xs k one maximum)=.revert ∧
      mm=writeMachine (machine xs k one maximum) (17+k.val) (.val maximum) ∧
      [[MObj.elems .dyn ((hp xs hf).get r),MObj.elems .dyn ((hp xs hf).get neighbor)],
        [MObj.elems .dyn (mid.get r),MObj.elems .dyn (mid.get neighbor)]]=
        [[vals xs,vals [⟨8,by decide⟩,⟨9,by decide⟩]],
          [(vals xs).set k.val (indexValue maximum),vals [⟨8,by decide⟩,⟨9,by decide⟩]]] ∧
      [tables (sy xs k one maximum),tables ym]=
        [[some ⟨SA,sourceUintMemory (vals xs)⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩],
          [some ⟨SA,sourceUintMemory ((vals xs).set k.val (indexValue maximum))⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩]] ∧
      [contentWords (machine xs k one maximum) xs.length,contentWords mm xs.length]=
        [xs.map Word.val,(xs.map Word.val).set k.val (.val maximum)] ∧
      [frameWords (machine xs k one maximum),frameWords mm]=
        List.replicate 2 [w[96],w[16],w[16],.val maximum,.val one,.val k,w[0],w[99],w[0],w[0],w[0],.val (wmod xs.length),w[2],w[8],w[9],w[0]] ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local salias) (.local si) rfl)).run (sy xs k one maximum)=
        (.ok (.val (sourceUint (indexValue zero))),sy xs k one maximum) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local salias) (.local si) rfl)).run ym=
        (.ok (.val (sourceUint (indexValue maximum))),ym) ∧
      MObj.elems .dyn (mid.get r)≠MObj.elems .dyn ((hp xs hf).get r) ∧
      SourceUintMemoryAt ym 0 mid r .dyn ∧ SourceUintMemoryAt ym 1 mid neighbor .dyn ∧
      StateRepr 1 1 8 (Frag.init Γ) ((σ xs hf k one maximum).withHeap mid) base mm ∧
      Source.MemOK E0 SH ym ∧ StructAllocatorRepr mid base 8 ⟨96,by decide⟩ mm ∧
      ym.1=(sy xs k one maximum).1 ∧ ym.1.get salias=.memRef rfl 0 ∧ mm.stack=[w[42]] ∧
      ym.2.ex=(sy xs k one maximum).2.ex ∧ ym.2.events=(sy xs k one maximum).2.events ∧
      ym.2.logs=(sy xs k one maximum).2.logs ∧ ym.2.fnLocals=(sy xs k one maximum).2.fnLocals := by
  obtain ⟨hmok0,hr0,hn0,hm0⟩ := views xs hf k one maximum
  have hki : (indexValue k).1.toNat<(hp xs hf).len r .dyn := by
    simpa only [Heap.len,elems,vals,List.length_map,indexValue,Int.toNat_natCast] using hk
  obtain ⟨mid,ym,mm,hw,hsw,hs1,hi1,hc1,he2,hs2,hi2,hc2,hitems,hip,hcode,hr1,hmok1,hm1,hy,hstack,halloc,hlen,hel,hq,hb,hex,hev,hlog,hfn⟩ :=
    resolved_uint_assign_add_reject (Source.SemanticsExamples.G0 p) F0 0 rfl (σ xs hf k one maximum) r hr0
      sr si sv sj tr ti tv tj (indexValue k) (indexValue maximum) (indexValue one)
      rfl rfl rfl rfl rfl rfl rfl rfl hki max_add_one_invalid hm0 SH hmok0
  have hrun := assign_run (machine xs k one maximum) xs.length k maximum hf hk rfl rfl rfl rfl
  have hmm : mm=writeMachine (machine xs k one maximum) (17+k.val) (.val maximum) := (Out.ok.inj (hc1.symm.trans hrun)).1
  subst mm
  have emid : MObj.elems .dyn (mid.get r)=(vals xs).set k.val (indexValue maximum) := by
    simpa only [σ,elems,indexValue,Int.toNat_natCast] using hel
  have hn : mid.get neighbor=(hp xs hf).get neighbor := hq neighbor (by change (0 : Nat)≠1;decide)
  have htab0 : (sy xs k one maximum).2.heap.get 0=some ⟨SA,sourceUintMemory (vals xs)⟩ := by simpa only [SourceUintMemoryAt,elems] using hr0
  have htab1 : ym.2.heap.get 0=some ⟨SA,sourceUintMemory ((vals xs).set k.val (indexValue maximum))⟩ := by simpa only [SourceUintMemoryAt,emid] using hr1
  have htabn := hb 1 (by decide)
  have hread0 := hr0.eval_index (Source.SemanticsExamples.G0 p) F0 0 salias si (indexValue k) rfl rfl hki
  have hkm : (indexValue k).1.toNat<mid.len r .dyn := by rw [hlen];exact hki
  have hread1 := hr1.eval_index (Source.SemanticsExamples.G0 p) F0 0 salias si (indexValue k) (by rw [hy];rfl) (by rw [hy];rfl) hkm
  have hget0 : (MObj.elems .dyn ((hp xs hf).get r))[k.val]?=some (indexValue zero) := by
    rw [elems]
    simp only [vals,List.getElem?_map,List.getElem?_eq_getElem hk,Option.map_some,hz]
  have hget1 : (MObj.elems .dyn (mid.get r))[k.val]?=some (indexValue maximum) := by
    rw [emid]
    exact List.getElem?_set_self (by simpa only [vals,List.length_map] using hk)
  have hchanged : MObj.elems .dyn (mid.get r)≠MObj.elems .dyn ((hp xs hf).get r) := by
    intro he
    have h := hget1.symm.trans ((congrArg (fun xs : List PrimTy.uint.Denote => xs[k.val]?) he).trans hget0)
    exact max_ne_zero (Option.some.inj h)
  have halloc := halloc ⟨96,by decide⟩ (by decide) (initial_allocator xs hf k one maximum)
  have hframe := frame_write (machine xs k one maximum) (17+k.val) (.val maximum) (by omega)
  refine ⟨mid,ym,_,hs1,he2,hitems,hip,hc1,hc2,hcode,rfl,?_,?_,?_,?_,?_,?_,hchanged,hr1,?_,hm1,hmok1,halloc,hy,?_,rfl,hex,hev,hlog,hfn⟩
  · rw [emid,hn,elems,neighbor_elems];rfl
  · simp only [tables,htab0,htab1,htabn];rfl
  · rw [contents_write _ _ _ _ hk,contents_initial xs hf k one maximum]
  · rw [hframe,frame_initial xs hf k one maximum];rfl
  · simpa only [elems,vals,indexValue,Int.toNat_natCast,List.getElem_map,hz] using hread0
  · simpa only [emid,indexValue,Int.toNat_natCast,List.getElem_set_self] using hread1
  · unfold SourceUintMemoryAt at hn0 ⊢
    rw [htabn,hn]
    exact hn0
  · rw [hy];rfl

private def xs : List (Fin W) := [⟨7,by decide⟩,zero,maximum]
private theorem fit : 17+xs.length≤80 := by decide

/-- Same decoded/local inputs, different actual memory epoch: INITIAL0-plus1
succeeds, whereas the real changed max prefix rejects. No frozen payload oracle. -/
theorem frozen_initial_disagrees (p : Roadmap.Pipeline) :
    ∃ (mid out : Heap H) (ym z : Source.EMState E0 SΓ) (mm mf : Machine),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none items (sy xs one one maximum).1).run (.nil,(sy xs one one maximum).2)=
        (.error (.revert (Source.panicData .arithmetic)),(.nil,ym.2)) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintIndexedAdd sr si sj)).run ym=
        (.error (.revert (Source.panicData .arithmetic)),ym) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintIndexedAdd sr si sj)).run (sy xs one one maximum)=
        (.ok (.val (sourceUint (indexValue one))),z) ∧
      Stmt.run (σ xs fit one one maximum) (.opAssign .add rfl rfl (.mindex .dyn (.var tr rfl) (.local ti)) (.simple (.local tj)))=
        .ok ⟨(σ xs fit one one maximum).withHeap out,List.prefix_refl _⟩ ∧
      run assignCode (machine xs one one maximum)=.ok mm 0 ∧ run addCode mm=.revert ∧
      run addCode (machine xs one one maximum)=.ok mf 0 ∧
      [MObj.elems .dyn ((hp xs fit).get r),MObj.elems .dyn (mid.get r),MObj.elems .dyn (out.get r)]=
        [vals xs,vals [⟨7,by decide⟩,maximum,maximum],vals [⟨7,by decide⟩,one,maximum]] ∧
      [tables (sy xs one one maximum),tables ym,tables z]=
        [[some ⟨SA,sourceUintMemory (vals xs)⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩],
         [some ⟨SA,sourceUintMemory (vals [⟨7,by decide⟩,maximum,maximum])⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩],
         [some ⟨SA,sourceUintMemory (vals [⟨7,by decide⟩,one,maximum])⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩]] ∧
      [contentWords (machine xs one one maximum) 3,contentWords mm 3,contentWords mf 3]=
        [[w[7],w[0],.val maximum],[w[7],.val maximum,.val maximum],[w[7],w[1],.val maximum]] ∧
      [frameWords (machine xs one one maximum),frameWords mm,frameWords mf]=
        List.replicate 3 [w[96],w[16],w[16],.val maximum,w[1],w[1],w[0],w[99],w[0],w[0],w[0],w[3],w[2],w[8],w[9],w[0]] ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local salias) (.local si) rfl)).run ym=
        (.ok (.val (sourceUint (indexValue maximum))),ym) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local salias) (.local si) rfl)).run z=
        (.ok (.val (sourceUint (indexValue one))),z) ∧ Source.MemOK E0 SH z := by
  obtain ⟨mid,ym,mm,hsfirst,hefail,hitems,hprog,hcfirst,hcfail,hcall,hmmeq,hvals,htables,hwords,hframes,hread0,hreadmax,tail⟩ :=
    reached_overflow p xs fit one (by decide) (by rfl)
  obtain ⟨hmok0,hr0,hn0,hm0⟩ := views xs fit one one maximum
  have hk : (indexValue one).1.toNat<(hp xs fit).len r .dyn := by rw [Heap.len,elems];change 1<3;decide
  have hget : (MObj.elems .dyn ((hp xs fit).get r))[(indexValue one).1.toNat]?=some (indexValue zero) := by rw [elems];rfl
  have hold : (MObj.elems .dyn ((hp xs fit).get r))[(indexValue one).1.toNat]=indexValue zero :=
    Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hget)
  have hadd : PrimTy.uint.inRange ((MObj.elems .dyn ((hp xs fit).get r))[(indexValue one).1.toNat].1+(indexValue one).1)=true := by rw [hold];rfl
  obtain ⟨out,z,mf,hw,hsw,he,hs,hi,hcode,hr,hm,hmok,hy,hstack,halloc⟩ :=
    resolved_uint_add_word (Source.SemanticsExamples.G0 p) F0 0 (σ xs fit one one maximum) r hr0
      sr si sj tr ti tj (indexValue one) (indexValue one) rfl rfl rfl rfl rfl rfl hk hadd hm0 SH hmok0
  have hnew : (⟨(MObj.elems .dyn ((hp xs fit).get r))[(indexValue one).1.toNat].1+(indexValue one).1,hadd⟩ : PrimTy.uint.Denote)=indexValue one := by
    apply Subtype.ext
    change (MObj.elems .dyn ((hp xs fit).get r))[(indexValue one).1.toNat].1+(indexValue one).1=(indexValue one).1
    rw [hold];rfl
  change (hp xs fit).writeAddr (.index r .dyn (indexValue one)) ⟨(MObj.elems .dyn ((hp xs fit).get r))[(indexValue one).1.toNat].1+(indexValue one).1,hadd⟩=some out at hw
  dsimp only [σ] at hsw he
  rw [hnew] at hw hsw he
  have eout : MObj.elems .dyn (out.get r)=vals [⟨7,by decide⟩,one,maximum] := by
    rw [indexedWrite_elems _ _ r .dyn _ _ hw,elems];rfl
  have hc := add_run (machine xs one one maximum) 3 one zero one (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl (by decide)
  have hmfeq : mf=writeMachine (machine xs one one maximum) 18 w[1] := (Out.ok.inj (hcode.symm.trans hc)).1
  subst mf
  subst mm
  have hmid : MObj.elems .dyn (mid.get r)=vals [⟨7,by decide⟩,maximum,maximum] := by
    exact (List.cons.inj (List.cons.inj (List.cons.inj hvals).2).1).1
  have htabmid : tables ym=[some ⟨SA,sourceUintMemory (vals [⟨7,by decide⟩,maximum,maximum])⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩] := by
    have h := (List.cons.inj (List.cons.inj htables).2).1
    exact h
  have fr := hr0.write_frames F0 2 (indexValue one) (indexValue one) hk hw hsw
  have hrread := hr.eval_index (Source.SemanticsExamples.G0 p) F0 0 salias si (indexValue one) (by rw [hy];rfl) (by rw [hy];rfl)
    (by rw [Heap.len,eout];change 1<3;decide)
  refine ⟨mid,out,ym,z,writeMachine (machine xs one one maximum) 18 (.val maximum),writeMachine (machine xs one one maximum) 18 w[1],hitems,hefail,he,hi,hcfirst,hcfail,hcode,?_,?_,rfl,rfl,hreadmax,?_,hmok⟩
  · rw [hmid,eout,elems]
  · simp only [tables,fr.2.2.1 1 (by decide)]
    rw [show z.2.heap.get 0=some ⟨SA,sourceUintMemory (vals [⟨7,by decide⟩,one,maximum])⟩ from by simpa only [SourceUintMemoryAt,eout] using hr]
    change [tables (sy xs one one maximum),tables ym,_]=_
    rw [htabmid];rfl
  · simpa only [eout,vals,indexValue,Int.toNat_natCast,List.getElem_cons_zero,List.getElem_cons_succ] using hrread

private def reverseItems : Source.RItems E0 [] false .body SΓ SΓ :=
  .stmt (.expr (sourceUintIndexedAdd sr si sj)) (.stmt (.expr (sourceUintIndexedAssign sr si sv)) .nil)
private def reverseProg : Prog C Γ Γ :=
  .cons (.opAssign .add rfl rfl (.mindex .dyn (.var tr rfl) (.local ti)) (.simple (.local tj)))
    (.cons (.assignMem (.index .dyn (.var tr rfl) (.simple (.local ti))) (.val (.simple (.local tv)))) .nil)

/-- Reversing the two actual operations succeeds (0-to1-to-max), whereas the
original order fails after0-to-max. Both real reached chains retain their data. -/
theorem reverse_succeeds (p : Roadmap.Pipeline) :
    ∃ (mid out : Heap H) (yf ym z : Source.EMState E0 SΓ) (mm mf : Machine),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none items (sy xs one one maximum).1).run (.nil,(sy xs one one maximum).2)=
        (.error (.revert (Source.panicData .arithmetic)),(.nil,yf.2)) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none reverseItems (sy xs one one maximum).1).run (.nil,(sy xs one one maximum).2)=
        (.ok (.normal (sy xs one one maximum).1),(.nil,z.2)) ∧
      Prog.run (σ xs fit one one maximum) prog=.error .revert ∧
      Prog.run (σ xs fit one one maximum) reverseProg=.ok ⟨(σ xs fit one one maximum).withHeap out,List.prefix_refl _⟩ ∧
      run (assignCode++addCode) (machine xs one one maximum)=.revert ∧
      run addCode (machine xs one one maximum)=.ok mm 0 ∧ run assignCode mm=.ok mf 0 ∧
      run (addCode++assignCode) (machine xs one one maximum)=.ok mf 0 ∧
      [MObj.elems .dyn ((hp xs fit).get r),MObj.elems .dyn (mid.get r),MObj.elems .dyn (out.get r)]=
        [vals xs,vals [⟨7,by decide⟩,one,maximum],vals [⟨7,by decide⟩,maximum,maximum]] ∧
      [MObj.elems .dyn ((hp xs fit).get neighbor),MObj.elems .dyn (mid.get neighbor),MObj.elems .dyn (out.get neighbor)]=
        List.replicate 3 (vals [⟨8,by decide⟩,⟨9,by decide⟩]) ∧
      [tables (sy xs one one maximum),tables yf,tables ym,tables z]=
        [[some ⟨SA,sourceUintMemory (vals xs)⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩],
         [some ⟨SA,sourceUintMemory (vals [⟨7,by decide⟩,maximum,maximum])⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩],
         [some ⟨SA,sourceUintMemory (vals [⟨7,by decide⟩,one,maximum])⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩],
         [some ⟨SA,sourceUintMemory (vals [⟨7,by decide⟩,maximum,maximum])⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩]] ∧
      [contentWords (machine xs one one maximum) 3,contentWords mm 3,contentWords mf 3]=
        [[w[7],w[0],.val maximum],[w[7],w[1],.val maximum],[w[7],.val maximum,.val maximum]] ∧
      [frameWords (machine xs one one maximum),frameWords mm,frameWords mf]=
        List.replicate 3 [w[96],w[16],w[16],.val maximum,w[1],w[1],w[0],w[99],w[0],w[0],w[0],w[3],w[2],w[8],w[9],w[0]] ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local salias) (.local si) rfl)).run ym=
        (.ok (.val (sourceUint (indexValue one))),ym) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local salias) (.local si) rfl)).run z=
        (.ok (.val (sourceUint (indexValue maximum))),z) ∧
      ym.1=(sy xs one one maximum).1 ∧ z.1=(sy xs one one maximum).1 ∧
      Source.MemOK E0 SH ym ∧ Source.MemOK E0 SH z ∧
      StructAllocatorRepr out base 8 ⟨96,by decide⟩ mf ∧ mf.stack=[w[42]] ∧
      z.2.ex=(sy xs one one maximum).2.ex ∧ z.2.events=(sy xs one one maximum).2.events ∧
      z.2.logs=(sy xs one one maximum).2.logs ∧ z.2.fnLocals=(sy xs one one maximum).2.fnLocals := by
  obtain ⟨fm,yf,mfwd,hsfirst,hefail,hforward,hpfwd,hcfwd,hcfail,hcall,hmeq,hvals,htables,hwords,hframes,hread0,hreadmax,tail⟩ :=
    reached_overflow p xs fit one (by decide) (by rfl)
  obtain ⟨hmok0,hr0,hn0,hm0⟩ := views xs fit one one maximum
  have hk : (indexValue one).1.toNat<(hp xs fit).len r .dyn := by rw [Heap.len,elems];change 1<3;decide
  have hget : (MObj.elems .dyn ((hp xs fit).get r))[(indexValue one).1.toNat]?=some (indexValue zero) := by rw [elems];rfl
  have hold : (MObj.elems .dyn ((hp xs fit).get r))[(indexValue one).1.toNat]=indexValue zero :=
    Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hget)
  have hadd : PrimTy.uint.inRange ((MObj.elems .dyn ((hp xs fit).get r))[(indexValue one).1.toNat].1+(indexValue one).1)=true := by rw [hold];rfl
  obtain ⟨mid,ym,mm,hw1,hsw1,he1,hs1,hi1,hc1,hr1,hm1,hmok1,hy1,hstack1,ha1⟩ :=
    resolved_uint_add_word (Source.SemanticsExamples.G0 p) F0 1 (σ xs fit one one maximum) r hr0
      sr si sj tr ti tj (indexValue one) (indexValue one) rfl rfl rfl rfl rfl rfl hk hadd hm0 SH hmok0
  have hnew : (⟨(MObj.elems .dyn ((hp xs fit).get r))[(indexValue one).1.toNat].1+(indexValue one).1,hadd⟩ : PrimTy.uint.Denote)=indexValue one := by
    apply Subtype.ext
    change (MObj.elems .dyn ((hp xs fit).get r))[(indexValue one).1.toNat].1+(indexValue one).1=(indexValue one).1
    rw [hold];rfl
  change (hp xs fit).writeAddr (.index r .dyn (indexValue one)) ⟨(MObj.elems .dyn ((hp xs fit).get r))[(indexValue one).1.toNat].1+(indexValue one).1,hadd⟩=some mid at hw1
  dsimp only [σ] at hsw1 he1
  rw [hnew] at hw1 hsw1 he1
  have emid : MObj.elems .dyn (mid.get r)=vals [⟨7,by decide⟩,one,maximum] := by rw [indexedWrite_elems _ _ r .dyn _ _ hw1,elems];rfl
  have hkm : (indexValue one).1.toNat<mid.len r .dyn := by rw [Heap.len,emid];change 1<3;decide
  obtain ⟨out,z,mf,hw2,hsw2,he2,hs2,hi2,hc2,hr2,hm2,hmok2,hy2,hstack2,ha2⟩ :=
    resolved_uint_assign_word (Source.SemanticsExamples.G0 p) F0 0 ((σ xs fit one one maximum).withHeap mid) r hr1
      sr si sv tr ti tv (indexValue one) (indexValue maximum) (by rw [hy1];rfl) (by rw [hy1];rfl) (by rw [hy1];rfl)
      rfl rfl rfl hkm hm1 SH hmok1
  have eout : MObj.elems .dyn (out.get r)=vals [⟨7,by decide⟩,maximum,maximum] := by
    rw [indexedWrite_elems _ _ r .dyn _ _ hw2];change (MObj.elems .dyn (mid.get r)).set (indexValue one).1.toNat (indexValue maximum)=_;rw [emid];rfl
  have hcr := add_run (machine xs one one maximum) 3 one zero one (by decide) (by decide) (by decide) rfl rfl rfl rfl rfl (by decide)
  have hmm : mm=writeMachine (machine xs one one maximum) 18 w[1] := (Out.ok.inj (hc1.symm.trans hcr)).1
  subst mm
  have hca := assign_run (writeMachine (machine xs one one maximum) 18 w[1]) 3 one maximum (by decide) (by decide) rfl rfl rfl rfl
  have hmf : mf=writeMachine (writeMachine (machine xs one one maximum) 18 w[1]) 18 (.val maximum) := (Out.ok.inj (hc2.symm.trans hca)).1
  subst mf
  have hitems := source_items_pair_run (Source.SemanticsExamples.G0 p) F0 0 SΓ.length
    (.expr (sourceUintIndexedAdd sr si sj)) (.expr (sourceUintIndexedAssign sr si sv)) (sy xs one one maximum) ym z
    (by simpa only [hy1] using hs1) (by simpa only [hy2] using hs2)
  have fr1 := hr0.write_frames F0 3 (indexValue one) (indexValue one) hk hw1 hsw1
  have fr2 := hr1.write_frames F0 2 (indexValue one) (indexValue maximum) hkm hw2 hsw2
  have htabf : tables yf=[some ⟨SA,sourceUintMemory (vals [⟨7,by decide⟩,maximum,maximum])⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩] := (List.cons.inj (List.cons.inj htables).2).1
  have htab1 : ym.2.heap.get 0=some ⟨SA,sourceUintMemory (vals [⟨7,by decide⟩,one,maximum])⟩ := by simpa only [SourceUintMemoryAt,emid] using hr1
  have htab2 : z.2.heap.get 0=some ⟨SA,sourceUintMemory (vals [⟨7,by decide⟩,maximum,maximum])⟩ := by simpa only [SourceUintMemoryAt,eout] using hr2
  have hrread1 := hr1.eval_index (Source.SemanticsExamples.G0 p) F0 0 salias si (indexValue one) (by rw [hy1];rfl) (by rw [hy1];rfl) hkm
  have hrread2 := hr2.eval_index (Source.SemanticsExamples.G0 p) F0 0 salias si (indexValue one) (by rw [hy2,hy1];rfl) (by rw [hy2,hy1];rfl) (by rw [Heap.len,eout];change 1<3;decide)
  have haa := ha2 ⟨96,by decide⟩ (by decide) (ha1 ⟨96,by decide⟩ (by decide) (initial_allocator xs fit one one maximum))
  refine ⟨mid,out,yf,ym,z,writeMachine (machine xs one one maximum) 18 w[1],writeMachine (writeMachine (machine xs one one maximum) 18 w[1]) 18 (.val maximum),hforward,?_,hpfwd,intrinsic_heap_pair_run _ _ _ _ _ hi1 hi2,hcall,hc1,hc2,?_,?_,?_,?_,rfl,rfl,?_,?_,hy1,hy2.trans hy1,hmok1,hmok2,haa,rfl,?_,?_,?_,?_⟩
  · simpa only [reverseItems,hy2,hy1] using hitems
  · rw [addCode,run_append_ok hc1];exact hc2
  · rw [elems,emid,eout]
  · have hn1 : mid.get neighbor=(hp xs fit).get neighbor := indexedWrite_frame _ _ r .dyn _ _ hw1 neighbor (by change (0 : Nat)≠1;decide)
    have hn2 : out.get neighbor=mid.get neighbor := indexedWrite_frame _ _ r .dyn _ _ hw2 neighbor (by change (0 : Nat)≠1;decide)
    simp only [hn2,hn1,neighbor_elems]
    rfl
  · rw [show tables yf=_ from htabf]
    simp only [tables,htab1,htab2,fr2.2.2.1 1 (by decide),fr1.2.2.1 1 (by decide)];rfl
  · simpa only [emid,vals,indexValue,Int.toNat_natCast,List.getElem_cons_zero,List.getElem_cons_succ] using hrread1
  · simpa only [eout,vals,indexValue,Int.toNat_natCast,List.getElem_cons_zero,List.getElem_cons_succ] using hrread2
  · exact fr2.2.2.2.2.1.trans fr1.2.2.2.2.1
  · exact fr2.2.2.2.2.2.1.trans fr1.2.2.2.2.2.1
  · exact fr2.2.2.2.2.2.2.1.trans fr1.2.2.2.2.2.2.1
  · exact fr2.2.2.2.2.2.2.2.trans fr1.2.2.2.2.2.2.2

/-- Lowering the actual Source block horizon still executes the material first
write, then times out before the compound write. Prefix state/word frame is real. -/
theorem low_horizon_prefix (p : Roadmap.Pipeline) :
    ∃ (mid : Heap H) (ym : Source.EMState E0 SΓ) (mm : Machine),
      (Source.execS (Source.SemanticsExamples.G0 p) F0 4 SΓ.length none (.expr (sourceUintIndexedAssign sr si sv) : Source.RStmt E0 [] false .body SΓ SΓ) (sy xs one one maximum).1).run (.nil,(sy xs one one maximum).2)=
        (.ok (.normal (sy xs one one maximum).1),(.nil,ym.2)) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 5 SΓ.length none items (sy xs one one maximum).1).run (.nil,(sy xs one one maximum).2)=
        (.error .timeout,(.nil,ym.2)) ∧
      run assignCode (machine xs one one maximum)=.ok mm 0 ∧
      mm=writeMachine (machine xs one one maximum) 18 (.val maximum) ∧
      MObj.elems .dyn (mid.get r)=vals [⟨7,by decide⟩,maximum,maximum] ∧
      [tables (sy xs one one maximum),tables ym]=
        [[some ⟨SA,sourceUintMemory (vals xs)⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩],
         [some ⟨SA,sourceUintMemory (vals [⟨7,by decide⟩,maximum,maximum])⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩]] ∧
      [contentWords (machine xs one one maximum) 3,contentWords mm 3]=
        [[w[7],w[0],.val maximum],[w[7],.val maximum,.val maximum]] ∧
      [frameWords (machine xs one one maximum),frameWords mm]=
        List.replicate 2 [w[96],w[16],w[16],.val maximum,w[1],w[1],w[0],w[99],w[0],w[0],w[0],w[3],w[2],w[8],w[9],w[0]] ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local salias) (.local si) rfl)).run ym=
        (.ok (.val (sourceUint (indexValue maximum))),ym) ∧
      Source.MemOK E0 SH ym ∧ StructAllocatorRepr mid base 8 ⟨96,by decide⟩ mm ∧ mm.stack=[w[42]] := by
  obtain ⟨hmok0,hr0,hn0,hm0⟩ := views xs fit one one maximum
  have hk : (indexValue one).1.toNat<(hp xs fit).len r .dyn := by rw [Heap.len,elems];change 1<3;decide
  obtain ⟨mid,ym,mm,hw,hsw,he,hs,hi,hc,hr,hm,hmok,hy,hstack,ha⟩ :=
    resolved_uint_assign_word (Source.SemanticsExamples.G0 p) F0 0 (σ xs fit one one maximum) r hr0
      sr si sv tr ti tv (indexValue one) (indexValue maximum) rfl rfl rfl rfl rfl rfl hk hm0 SH hmok0
  have hs' : (Source.execS (Source.SemanticsExamples.G0 p) F0 4 SΓ.length none (.expr (sourceUintIndexedAssign sr si sv) : Source.RStmt E0 [] false .body SΓ SΓ) (sy xs one one maximum).1).run (.nil,(sy xs one one maximum).2)=
      (.ok (.normal ym.1),(.nil,ym.2)) := by simpa only [hy] using hs
  have htimeout := source_uint_add_horizon_two (Source.SemanticsExamples.G0 p) F0 ym sr si sj
  have hstmt := source_expr_statement_error (Source.SemanticsExamples.G0 p) F0 2 SΓ.length (sourceUintIndexedAdd sr si sj) ym ym _ htimeout
  have htail : (Source.execItems (Source.SemanticsExamples.G0 p) F0 4 SΓ.length none
      (.stmt (.expr (sourceUintIndexedAdd sr si sj)) .nil : Source.RItems E0 [] false .body SΓ SΓ) ym.1).run (.nil,ym.2)=
      (.error .timeout,(.nil,ym.2)) := by rw [Source.execItems,Source.Hoare.run_bind,hstmt]
  have hitems : (Source.execItems (Source.SemanticsExamples.G0 p) F0 5 SΓ.length none items (sy xs one one maximum).1).run (.nil,(sy xs one one maximum).2)=
      (.error .timeout,(.nil,ym.2)) := by
    rw [items,Source.execItems,Source.Hoare.run_bind,hs']
    change (Source.execItems (Source.SemanticsExamples.G0 p) F0 4 SΓ.length none
      (.stmt (.expr (sourceUintIndexedAdd sr si sj)) .nil : Source.RItems E0 [] false .body SΓ SΓ) ym.1 >>= fun o => Source.EM.lift (o.up SΓ)).run (.nil,ym.2)=_
    rw [Source.Hoare.run_bind,htail]
  have hrun := assign_run (machine xs one one maximum) 3 one maximum (by decide) (by decide) rfl rfl rfl rfl
  have hmm : mm=writeMachine (machine xs one one maximum) 18 (.val maximum) := (Out.ok.inj (hc.symm.trans hrun)).1
  subst mm
  have emid : MObj.elems .dyn (mid.get r)=vals [⟨7,by decide⟩,maximum,maximum] := by rw [indexedWrite_elems _ _ r .dyn _ _ hw];change (MObj.elems .dyn ((hp xs fit).get r)).set (indexValue one).1.toNat (indexValue maximum)=_;rw [elems];rfl
  have fr := hr0.write_frames F0 2 (indexValue one) (indexValue maximum) hk hw hsw
  have hrread := hr.eval_index (Source.SemanticsExamples.G0 p) F0 0 salias si (indexValue one) (by rw [hy];rfl) (by rw [hy];rfl)
    (by rw [Heap.len,emid];change 1<3;decide)
  refine ⟨mid,ym,_,hs,hitems,hc,rfl,emid,?_,rfl,rfl,?_,hmok,ha _ (by decide) (initial_allocator xs fit one one maximum),rfl⟩
  · simp only [tables,fr.2.2.1 1 (by decide)]
    rw [show ym.2.heap.get 0=some ⟨SA,sourceUintMemory (vals [⟨7,by decide⟩,maximum,maximum])⟩ from by simpa only [SourceUintMemoryAt,emid] using hr];rfl
  · simpa only [emid,vals,indexValue,Int.toNat_natCast,List.getElem_cons_zero,List.getElem_cons_succ] using hrread

private theorem bounds_reject (p : Roadmap.Pipeline) (xs : List (Fin W)) (hf : 17+xs.length≤80)
    (k : Fin W) (hk : xs.length≤k.val) :
    (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none items (sy xs k one maximum).1).run (.nil,(sy xs k one maximum).2)=
      (.error (.revert (Source.panicData .index)),(.nil,(sy xs k one maximum).2)) ∧
    Prog.run (σ xs hf k one maximum) prog=.error .revert ∧
    run (assignCode++addCode) (machine xs k one maximum)=.revert := by
  obtain ⟨hmok0,hr0,hn0,hm0⟩ := views xs hf k one maximum
  have hki : (hp xs hf).len r .dyn≤(indexValue k).1.toNat := by simpa only [Heap.len,elems,vals,List.length_map,indexValue,Int.toNat_natCast] using hk
  have hb := resolved_uint_assign_word_bounds (Source.SemanticsExamples.G0 p) F0 1 (σ xs hf k one maximum) r hr0
    sr si sv tr ti tv (indexValue k) (indexValue maximum) rfl rfl rfl rfl rfl rfl hki hm0
  have hs := source_expr_statement_error (Source.SemanticsExamples.G0 p) F0 4 SΓ.length _ (sy xs k one maximum) (sy xs k one maximum) _ hb.1
  have hn : (σ xs hf k one maximum).heap.writeAddr (.index r .dyn (indexValue k)) (indexValue maximum)=none := by
    change (hp xs hf).writeAddr (.index r .dyn (indexValue k)) (indexValue maximum)=none
    simp only [Heap.writeAddr,Heap.setIndex,show ¬(indexValue k).1.toNat<(MObj.elems .dyn ((hp xs hf).get r)).length from Nat.not_lt.mpr hki,↓reduceIte]
  have hi : Stmt.run (σ xs hf k one maximum) (.assignMem (.index .dyn (.var tr rfl) (.simple (.local ti))) (.val (.simple (.local tv))))=.error .revert := by
    change TRun.assignMem (.index .dyn (.var tr rfl) (.simple (.local ti))) (.val (.simple (.local tv))) (σ xs hf k one maximum)=_
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,MPath.mvalT,Simple.evalT,Val.evalT,
      show TEnv.get tr (σ xs hf k one maximum).env=some r from rfl,
      show TEnv.get ti (σ xs hf k one maximum).env=indexValue k from rfl,
      show TEnv.get tv (σ xs hf k one maximum).env=indexValue maximum from rfl,
      hn,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  refine ⟨?_,Evm.Prog.run_cons_error hi,?_⟩
  · rw [items,Source.execItems,Source.Hoare.run_bind,hs]
  · exact run_append_revert hb.2

/-- Empty and exact-end inputs reject the FIRST statement, leaving no reached
arithmetic suffix. Their Source index panic is distinct from arithmetic panic. -/
theorem early_bounds (p : Roadmap.Pipeline) :
    (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none items (sy [] zero one maximum).1).run (.nil,(sy [] zero one maximum).2)=
      (.error (.revert (Source.panicData .index)),(.nil,(sy [] zero one maximum).2)) ∧
    Prog.run (σ [] (by decide) zero one maximum) prog=.error .revert ∧
    run (assignCode++addCode) (machine [] zero one maximum)=.revert ∧
    (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none items (sy xs ⟨3,by decide⟩ one maximum).1).run (.nil,(sy xs ⟨3,by decide⟩ one maximum).2)=
      (.error (.revert (Source.panicData .index)),(.nil,(sy xs ⟨3,by decide⟩ one maximum).2)) ∧
    Prog.run (σ xs fit ⟨3,by decide⟩ one maximum) prog=.error .revert ∧
    run (assignCode++addCode) (machine xs ⟨3,by decide⟩ one maximum)=.revert ∧
    [tables (sy [] zero one maximum),tables (sy xs ⟨3,by decide⟩ one maximum)]=
      [[some ⟨SA,sourceUintMemory []⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩],
       [some ⟨SA,sourceUintMemory (vals xs)⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩]] ∧
    [contentWords (machine [] zero one maximum) 0,contentWords (machine xs ⟨3,by decide⟩ one maximum) 3]=[[],[w[7],w[0],.val maximum]] ∧
    [frameWords (machine [] zero one maximum),frameWords (machine xs ⟨3,by decide⟩ one maximum)]=
      [[w[96],w[16],w[16],.val maximum,w[1],w[0],w[0],w[99],w[0],w[0],w[0],w[0],w[2],w[8],w[9],w[0]],
       [w[96],w[16],w[16],.val maximum,w[1],w[3],w[0],w[99],w[0],w[0],w[0],w[3],w[2],w[8],w[9],w[0]]] := by
  obtain ⟨h0,i0,w0⟩ := bounds_reject p [] (by decide) zero (by decide)
  obtain ⟨h3,i3,w3⟩ := bounds_reject p xs fit ⟨3,by decide⟩ (by decide)
  exact ⟨h0,i0,w0,h3,i3,w3,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintLateFailureControls.reached_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_overflow
/-- info: 'Solidity.Backend.MemoryOps.SourceUintLateFailureControls.frozen_initial_disagrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frozen_initial_disagrees
/-- info: 'Solidity.Backend.MemoryOps.SourceUintLateFailureControls.reverse_succeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reverse_succeeds
/-- info: 'Solidity.Backend.MemoryOps.SourceUintLateFailureControls.low_horizon_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms low_horizon_prefix
/-- info: 'Solidity.Backend.MemoryOps.SourceUintLateFailureControls.early_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms early_bounds
end Solidity.Backend.MemoryOps.SourceUintLateFailureControls
