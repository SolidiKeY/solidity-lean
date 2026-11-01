import Solidity.Backend.MemoryOps.SourceUintSequence
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceUintMutationControls
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
private theorem no_struct {s : Name} (q : HRef H (.struct s)) : False := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi
  | succ i => cases i with
    | zero => cases hi
    | succ i => cases hi
private theorem root_repr (xs : List (Fin W)) (hf : 17+xs.length≤80) (k l v : Fin W) : ArrayRepr (hp xs hf) r (base r.id) (machine xs k l v) := by
  refine ⟨?_,?_,?_⟩
  · change 16+1+(hp xs hf).len r .dyn≤W
    simp only [Heap.len,elems,vals,List.length_map]
    have h : 80<W := by decide
    omega
  · simp only [Heap.len,elems,vals,List.length_map]
    rfl
  · intro i value hi
    rw [elems] at hi
    have hb : i<xs.length := by
      have h := Evm.lt_of_getElem? hi
      simpa only [vals,List.length_map] using h
    have he : indexValue xs[i]=value := by
      have he := (List.getElem?_eq_some_iff.mp hi).choose_spec
      simpa only [vals,List.getElem_map] using he
    subst value
    change ReprV .uint (indexValue xs[i]) ((machine xs k l v).mem (cell (16+1+i)))
    simp only [cell,machine]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
    rw [dif_pos (by omega)]
    have he : 16+1+i-17=i := by omega
    simp only [he]
    exact ReprV.uint_of rfl
private theorem neighbor_repr (xs : List (Fin W)) (hf : 17+xs.length≤80) (k l v : Fin W) : ArrayRepr (hp xs hf) neighbor (base neighbor.id) (machine xs k l v) := by
  refine ⟨by rw [Heap.len,neighbor_elems];decide,?_,?_⟩
  · rw [Heap.len,neighbor_elems]
    change (machine xs k l v).mem 80=w[2]
    simp only [machine]
    rw [dif_neg (by omega)]
    rfl
  · intro i value hi
    rw [neighbor_elems] at hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      change ReprV .uint (indexValue ⟨8,by decide⟩) ((machine xs k l v).mem 81)
      simp only [machine]
      rw [dif_neg (by omega)]
      exact ReprV.uint_of rfl
    | succ i => cases i with
      | zero =>
        cases Option.some.inj hi
        change ReprV .uint (indexValue ⟨9,by decide⟩) ((machine xs k l v).mem 82)
        simp only [machine]
        rw [dif_neg (by omega)]
        exact ReprV.uint_of rfl
      | succ i => cases hi
private theorem initial_repr (xs : List (Fin W)) (hf : 17+xs.length≤80) (k l v : Fin W) :
    StateRepr 1 1 8 (Frag.init Γ) (σ xs hf k l v) base (machine xs k l v) := by
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨?_,?_,?_,by decide,?_,?_,RefFieldsRepr.withoutStructs _ _ _ (fun q => no_struct q)⟩
  · refine ⟨hc.store,?_,?_,hc.net,hc.netSelf,hc.bound,?_,hc.env,hc.funds,hc.oracle⟩
    · intro p i
      cases i with
      | here => exact ReprV.uint_of rfl
      | there i => cases i with
        | here => exact ReprV.uint_of rfl
        | there i => cases i with
          | here => exact ReprV.uint_of rfl
          | there i => cases i with | there i => cases i with | there i => nomatch i
    all_goals intro p i;cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
  · refine ⟨?_,?_,?_⟩
    · intro p q;obtain ⟨rfl,hq|hq⟩ := refs q <;> cases hq
      · exact root_repr xs hf k l v
      · exact neighbor_repr xs hf k l v
    · intro p q;obtain ⟨rfl,hq|hq⟩ := refs q <;> cases hq
      · change 8≤16;decide
      · change 8≤80;decide
    · intro p t q z hn
      obtain ⟨rfl,hq|hq⟩ := refs q
      · cases hq
        obtain ⟨rfl,hz|hz⟩ := refs z
        · cases hz;exact (hn rfl).elim
        · cases hz
          left
          change 16+1+(hp xs hf).len r .dyn≤80
          simpa only [Heap.len,elems,vals,List.length_map] using hf
      · cases hq
        obtain ⟨rfl,hz|hz⟩ := refs z
        · cases hz
          right
          change 16+1+(hp xs hf).len r .dyn≤80
          simpa only [Heap.len,elems,vals,List.length_map] using hf
        · cases hz;exact (hn rfl).elim
  · intro R i
    cases i with | there i => cases i with | there i => cases i with | there i => cases i with
      | here => exact ⟨r,rfl,rfl⟩
      | there i => cases i with | here => exact ⟨r,rfl,rfl⟩ | there i => nomatch i
  · exact ⟨fun q => (no_struct q).elim,fun q => (no_struct q).elim,fun q _ _ => (no_struct q).elim⟩
  · intro p s arr q
    exact (no_struct q).elim
private def y0 : Source.EMState E0 [] := (.nil,s0)
private def ys (xs : List (Fin W)) : Source.EMState E0 [] :=
  ((Source.allocRef (sourceUintMemory [indexValue ⟨8,by decide⟩,indexValue ⟨9,by decide⟩])).run
    ((Source.allocRef (sourceUintMemory (vals xs))).run y0).2).2
private def sy (xs : List (Fin W)) (k l v : Fin W) : Source.EMState E0 SΓ :=
  (.cons (sourceUint (indexValue k)) (.cons (sourceUint (indexValue l)) (.cons (sourceUint (indexValue v))
    (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil)))),(ys xs).2)
private abbrev SH := (Source.Heap.empty (D := E0.layout)).ty
private theorem source_memOK (xs : List (Fin W)) (k l v : Fin W) : Source.MemOK E0 SH (sy xs k l v) := by
  have h0 : Source.MemOK E0 SH y0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  let first : Source.EMState E0 [] := ((Source.allocRef (sourceUintMemory (vals xs))).run y0).2
  have h1 := source_uint_alloc_memOK (E := E0) (Γ := []) SH (vals xs) y0 h0
  rw [show (Source.allocRef (sourceUintMemory (vals xs))).run y0=(.ok (.memRef rfl 0),first) from rfl] at h1
  have h2 := source_uint_alloc_memOK (E := E0) (Γ := []) SH [indexValue ⟨8,by decide⟩,indexValue ⟨9,by decide⟩] first h1.1
  rw [show (Source.allocRef (sourceUintMemory [indexValue ⟨8,by decide⟩,indexValue ⟨9,by decide⟩])).run first=(.ok (.memRef rfl 1),ys xs) from rfl] at h2
  exact ⟨⟨h2.1.1.1,⟨trivial,⟨trivial,⟨trivial,⟨⟨SA,rfl,rfl⟩,⟨⟨SA,rfl,rfl⟩,trivial⟩⟩⟩⟩⟩⟩,h2.1.2⟩
private theorem represented (xs : List (Fin W)) (hf : 17+xs.length≤80) (k l v : Fin W) : SourceUintMemoryAt (sy xs k l v) 0 (hp xs hf) r .dyn := by
  unfold SourceUintMemoryAt;rw [elems];rfl
private theorem represented_neighbor (xs : List (Fin W)) (hf : 17+xs.length≤80) (k l v : Fin W) : SourceUintMemoryAt (sy xs k l v) 1 (hp xs hf) neighbor .dyn := by
  unfold SourceUintMemoryAt;rw [neighbor_elems];rfl

/-- Independently inhabited Source and word representations. The finite layout
space premise belongs to this fixture, never an admitted Source payload cap. -/
theorem initial_views (xs : List (Fin W)) (hf : 17+xs.length≤80) (k l v : Fin W) :
    Source.MemOK E0 SH (sy xs k l v) ∧ SourceUintMemoryAt (sy xs k l v) 0 (hp xs hf) r .dyn ∧
    SourceUintMemoryAt (sy xs k l v) 1 (hp xs hf) neighbor .dyn ∧
    StateRepr 1 1 8 (Frag.init Γ) (σ xs hf k l v) base (machine xs k l v) :=
  ⟨source_memOK xs k l v,represented xs hf k l v,represented_neighbor xs hf k l v,initial_repr xs hf k l v⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceUintMutationControls.initial_views' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial_views

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
private theorem delete_run (m : Machine) (n : Nat) (l : Fin W) (hf : 17+n≤80) (hl : l.val<n)
    (hptr : m.mem 2=w[16]) (hi : m.mem 4=.val l) (hlen : m.mem 16=.val (wmod n)) :
    run deleteCode m=.ok (writeMachine m (16+1+l.val) w[0]) 0 := by
  change run ([.push w[0]]++([.mload 2]++([.mload 4]++writeArrayStackCode))) m=_
  rw [run_append_ok (show run [.push w[0]] m=.ok (m.push w[0]) 0 from rfl)]
  rw [run_append_ok (show run [.mload 2] (m.push w[0])=.ok ((m.push w[0]).push w[16]) 0 from by change Out.ok ((m.push w[0]).push (m.mem 2)) 0=_;rw [hptr])]
  rw [run_append_ok (show run [.mload 4] ((m.push w[0]).push w[16])=.ok (((m.push w[0]).push w[16]).push (.val l)) 0 from by change Out.ok (((m.push w[0]).push w[16]).push (m.mem 4)) 0=_;rw [hi])]
  have hn : n<W := by
    have h : 80<W := by decide
    omega
  have ha := arrayAddrStack_run (m.push w[0]) ⟨16,by decide⟩ l n hn (by simpa only [Machine.push] using hlen)
  rw [if_pos hl] at ha
  rw [writeArrayStackCode,run_append_ok ha]
  have hw : 16+1+l.val<W := by
    have h : 80<W := by decide
    omega
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt hw,Out.ok_bind,exec_nil,writeMachine]
private def contentWords (m : Machine) (n : Nat) := List.ofFn (fun i : Fin n => m.mem (17+i.val))
private def frameWords (m : Machine) := [m.mem 0,m.mem 1,m.mem 2,m.mem 3,m.mem 4,m.mem 5,m.mem 6,m.mem 7,m.mem 8,m.mem 9,m.mem 10,m.mem 16,m.mem 80,m.mem 81,m.mem 82,m.mem 96]
private theorem contents_initial (xs : List (Fin W)) (hf : 17+xs.length≤80) (k l v : Fin W) : contentWords (machine xs k l v) xs.length=xs.map Word.val := by
  apply List.ext_getElem
  · simp only [contentWords,List.length_ofFn,List.length_map]
  · intro i hi hj
    simp only [contentWords,List.getElem_ofFn,List.getElem_map]
    have hb : i<xs.length := by simpa only [contentWords,List.length_ofFn] using hi
    have he : (MObj.elems .dyn ((hp xs hf).get r))[i]?=some (indexValue xs[i]) := by
      rw [elems]
      simp only [vals,List.getElem?_map,List.getElem?_eq_getElem hb,Option.map_some]
    obtain ⟨a,hw,hv⟩ := (root_repr xs hf k l v).elements i _ he
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
private theorem initial_allocator (xs : List (Fin W)) (hf : 17+xs.length≤80) (k l v : Fin W) : StructAllocatorRepr (hp xs hf) base 8 ⟨96,by decide⟩ (machine xs k l v) := by
  apply AllocatorRepr.withoutStructs (hn := fun q => no_struct q)
  refine ⟨(initial_repr xs hf k l v).heap,⟨by decide,by decide,rfl,?_⟩,?_⟩
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


private def midVals (xs : List (Fin W)) (k v : Fin W) := (vals xs).set k.val (indexValue v)
private def outVals (xs : List (Fin W)) (k l v : Fin W) := (midVals xs k v).set l.val (PrimTy.dflt .uint)
private def tables (y : Source.EMState E0 SΓ) := [y.2.heap.get 0,y.2.heap.get 1]
private def items : Source.RItems E0 [] false .body SΓ SΓ :=
  .stmt (.expr (sourceUintIndexedAssign sr si sv)) (.stmt (.expr (sourceUintIndexedDelete sr sj)) .nil)
private def prog : Prog C Γ Γ :=
  .cons (.assignMem (.index .dyn (.var tr rfl) (.simple (.local ti))) (.val (.simple (.local tv))))
    (.cons (.deleteMem (.loc (.index .dyn (.var tr rfl) (.simple (.local tj)))) rfl) .nil)

/-- Actual two-operation reached mutation, with shared-alias reads at all three
states and COMPLETE Source tables, intrinsic contents, dynamic word contents,
16-cell fixed frame, stack and allocator observations. The layout-space bound
is this witness's actual region capacity; generic operation laws have no cap. -/
theorem reached_assign_delete (p : Roadmap.Pipeline) (xs : List (Fin W)) (hf : 17+xs.length≤80)
    (k l v : Fin W) (hk : k.val<xs.length) (hl : l.val<xs.length) :
    ∃ (mid out : Heap H) (ym z : Source.EMState E0 SΓ) (mm target : Machine),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none items (sy xs k l v).1).run (.nil,(sy xs k l v).2)=
        (.ok (.normal (sy xs k l v).1),(.nil,z.2)) ∧
      Prog.run (σ xs hf k l v) prog=.ok ⟨(σ xs hf k l v).withHeap out,List.prefix_refl _⟩ ∧
      run assignCode (machine xs k l v)=.ok mm 0 ∧ run (assignCode++deleteCode) (machine xs k l v)=.ok target 0 ∧
      SourceUintMemoryAt ym 0 mid r .dyn ∧ SourceUintMemoryAt z 0 out r .dyn ∧
      SourceUintMemoryAt z 1 out neighbor .dyn ∧ Source.MemOK E0 SH ym ∧ Source.MemOK E0 SH z ∧
      StateRepr 1 1 8 (Frag.init Γ) ((σ xs hf k l v).withHeap out) base target ∧
      StructAllocatorRepr out base 8 ⟨96,by decide⟩ target ∧
      [MObj.elems .dyn ((hp xs hf).get r),MObj.elems .dyn (mid.get r),MObj.elems .dyn (out.get r)]=
        [vals xs,midVals xs k v,outVals xs k l v] ∧
      [tables (sy xs k l v),tables ym,tables z]=
        [[some ⟨SA,sourceUintMemory (vals xs)⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩],
         [some ⟨SA,sourceUintMemory (midVals xs k v)⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩],
         [some ⟨SA,sourceUintMemory (outVals xs k l v)⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩]] ∧
      [contentWords (machine xs k l v) xs.length,contentWords mm xs.length,contentWords target xs.length]=
        [xs.map Word.val,(xs.map Word.val).set k.val (.val v),((xs.map Word.val).set k.val (.val v)).set l.val w[0]] ∧
      [frameWords (machine xs k l v),frameWords mm,frameWords target]=
        List.replicate 3 [w[96],w[16],w[16],.val v,.val l,.val k,w[0],w[99],w[0],w[0],w[0],.val (wmod xs.length),w[2],w[8],w[9],w[0]] ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local salias) (.local si) rfl)).run (sy xs k l v)=
        (.ok (.val (sourceUint (indexValue xs[k.val]))),sy xs k l v) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local salias) (.local si) rfl)).run ym=
        (.ok (.val (sourceUint (indexValue v))),ym) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local salias) (.local si) rfl)).run z=
        (.ok (.val (sourceUint ((outVals xs k l v)[k.val]'(by simp only [outVals,midVals,List.length_set,vals,List.length_map];exact hk)))),z) ∧
      z.1=(sy xs k l v).1 ∧ z.1.get salias=.memRef rfl 0 ∧ target.stack=[w[42]] ∧
      z.2.ex=(sy xs k l v).2.ex ∧ z.2.events=(sy xs k l v).2.events ∧
      z.2.logs=(sy xs k l v).2.logs ∧ z.2.fnLocals=(sy xs k l v).2.fnLocals := by
  have hki : (indexValue k).1.toNat<(hp xs hf).len r .dyn := by simpa only [Heap.len,elems,vals,List.length_map,indexValue,Int.toNat_natCast] using hk
  have hli : (indexValue l).1.toNat<(hp xs hf).len r .dyn := by simpa only [Heap.len,elems,vals,List.length_map,indexValue,Int.toNat_natCast] using hl
  obtain ⟨mid,out,ym,z,mm,target,hw1,hw2,hsw1,hdel2,hs1,hs2,hitems,hip,hc1,hc2,hcode,hrm,hro,hm1,hm2,hmem1,hmem2,hy1,hy2,hstack,ha⟩ :=
    resolved_uint_assign_delete_word (Source.SemanticsExamples.G0 p) F0 0 (σ xs hf k l v) r (represented xs hf k l v)
      sr si sj sv tr ti tj tv (indexValue k) (indexValue l) (indexValue v) rfl rfl rfl rfl rfl rfl rfl rfl hki hli
      (initial_repr xs hf k l v) SH (source_memOK xs k l v)
  have hmc := assign_run (machine xs k l v) xs.length k v hf hk rfl rfl rfl rfl
  have hmm : mm=writeMachine (machine xs k l v) (17+k.val) (.val v) := (Out.ok.inj (hc1.symm.trans hmc)).1
  subst mm
  have htc := delete_run (writeMachine (machine xs k l v) (17+k.val) (.val v)) xs.length l hf hl
    (by change (if 2=17+k.val then _ else _)=_;rw [if_neg (by omega)];rfl)
    (by change (if 4=17+k.val then _ else _)=_;rw [if_neg (by omega)];rfl)
    (by change (if 16=17+k.val then _ else _)=_;rw [if_neg (by omega)];rfl)
  have htm : target=writeMachine (writeMachine (machine xs k l v) (17+k.val) (.val v)) (17+l.val) w[0] := (Out.ok.inj (hc2.symm.trans htc)).1
  subst target
  have emid : MObj.elems .dyn (mid.get r)=midVals xs k v := by
    rw [indexedWrite_elems (hp xs hf) mid r .dyn (indexValue k) (indexValue v) hw1,elems]
    rfl
  have eout : MObj.elems .dyn (out.get r)=outVals xs k l v := by
    rw [indexedWrite_elems mid out r .dyn (indexValue l) (PrimTy.dflt .uint) hw2,emid]
    rfl
  obtain ⟨_,ht1,hsrc1,hsrel1,hex1,hev1,hlog1,hfn1⟩ := (represented xs hf k l v).write_frames F0 3 (indexValue k) (indexValue v) hki hw1 hsw1
  have hlen : mid.len r .dyn=xs.length := by simp only [Heap.len,emid,midVals,List.length_set,vals,List.length_map]
  have hwrite2 : (Source.writeLoc (E := E0) (Γ := SΓ) F0 2 (.mem 0 (indexValue l).1.toNat) (sourceUint (PrimTy.dflt .uint))).run ym=(.ok (),z) := hdel2
  obtain ⟨_,ht2,hsrc2,hsrel2,hex2,hev2,hlog2,hfn2⟩ := hrm.write_frames F0 2 (indexValue l) (PrimTy.dflt .uint)
    (by change l.val<mid.len r .dyn;rw [hlen];exact hl) hw2 hwrite2
  have hnmid := hsrel1 neighbor .dyn 1 (by decide) (by decide) (represented_neighbor xs hf k l v)
  have hnout := hsrel2 neighbor .dyn 1 (by change (0 : Nat)≠1;decide) (by decide) hnmid
  have hj : k.val<mid.len r .dyn := by rw [hlen];exact hk
  have hj' : k.val<out.len r .dyn := by simpa only [Heap.len,eout,outVals,midVals,List.length_set,vals,List.length_map] using hk
  have hread0 := (represented xs hf k l v).eval_index (Source.SemanticsExamples.G0 p) F0 0 salias si (indexValue k) rfl rfl hki
  have hread1 := hrm.eval_index (Source.SemanticsExamples.G0 p) F0 0 salias si (indexValue k) (by rw [hy1];rfl) (by rw [hy1];rfl) hj
  have hread2 := hro.eval_index (Source.SemanticsExamples.G0 p) F0 0 salias si (indexValue k) (by rw [hy2];rfl) (by rw [hy2];rfl) hj'
  have hc0 := contents_initial xs hf k l v
  have hc₁ := contents_write (machine xs k l v) xs.length k.val (.val v) hk
  have hc₂ := contents_write (writeMachine (machine xs k l v) (17+k.val) (.val v)) xs.length l.val w[0] hl
  rw [hc0] at hc₁
  rw [hc₁] at hc₂
  have hf₁ := frame_write (machine xs k l v) (17+k.val) (.val v) (by omega)
  have hf₂ := frame_write (writeMachine (machine xs k l v) (17+k.val) (.val v)) (17+l.val) w[0] (by omega)
  have hs0 : (sy xs k l v).2.heap.get 1=some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩ := rfl
  have hsm : ym.2.heap.get 0=some ⟨SA,sourceUintMemory (midVals xs k v)⟩ := by simpa only [SourceUintMemoryAt,emid] using hrm
  have hso : z.2.heap.get 0=some ⟨SA,sourceUintMemory (outVals xs k l v)⟩ := by simpa only [SourceUintMemoryAt,eout] using hro
  refine ⟨mid,out,ym,z,_,_,hitems,hip,hc1,hcode,hrm,hro,hnout,hmem1,hmem2,hm2,ha _ (by decide) (initial_allocator xs hf k l v),?_,?_,?_,?_,?_,?_,?_,hy2,?_,hstack,hex2.trans hex1,hev2.trans hev1,hlog2.trans hlog1,hfn2.trans hfn1⟩
  · rw [elems,emid,eout]
  · unfold tables
    rw [hsm,hso,hsrc2 1 (by decide),hsrc1 1 (by decide)]
    rfl
  · rw [hc0,hc₁,hc₂]
  · rw [hf₂,hf₁,frame_initial xs hf k l v]
    rfl
  · simpa only [elems,vals,List.getElem_map] using hread0
  · simpa only [emid,midVals,indexValue,Int.toNat_natCast,List.getElem_set_self] using hread1
  · simpa only [eout] using hread2
  · rw [hy2];rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceUintMutationControls.reached_assign_delete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_assign_delete

private def zf : Fin W := ⟨0,W_pos⟩
private def one : Fin W := ⟨1,by decide⟩
private def two : Fin W := ⟨2,by decide⟩
private def three : Fin W := ⟨3,by decide⟩
private def maximum : Fin W := ⟨W-1,Nat.sub_lt W_pos (by decide)⟩
private def xs3 : List (Fin W) := [⟨7,by decide⟩,zf,maximum]
private theorem fit3 : 17+xs3.length≤80 := by decide
private def reverseItems : Source.RItems E0 [] false .body SΓ SΓ :=
  .stmt (.expr (sourceUintIndexedDelete sr sj)) (.stmt (.expr (sourceUintIndexedAssign sr si sv)) .nil)

/-- Both orders actually execute. A write-then-delete final vector alone equals
the initial vector, yet its changed middle is indispensable; reversing leaves
max instead of zero. This is a negative against dropping middle observations. -/
theorem order_and_dropped_middle (p : Roadmap.Pipeline) :
    ∃ (ym z zr : Source.EMState E0 SΓ) (mm mf mr : Machine),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none items (sy xs3 one one maximum).1).run (.nil,(sy xs3 one one maximum).2)=
        (.ok (.normal (sy xs3 one one maximum).1),(.nil,z.2)) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none reverseItems (sy xs3 one one maximum).1).run (.nil,(sy xs3 one one maximum).2)=
        (.ok (.normal (sy xs3 one one maximum).1),(.nil,zr.2)) ∧
      run assignCode (machine xs3 one one maximum)=.ok mm 0 ∧
      run (assignCode++deleteCode) (machine xs3 one one maximum)=.ok mf 0 ∧
      run (deleteCode++assignCode) (machine xs3 one one maximum)=.ok mr 0 ∧
      [contentWords (machine xs3 one one maximum) 3,contentWords mm 3,contentWords mf 3,contentWords mr 3]=
        [[w[7],w[0],.val maximum],[w[7],.val maximum,.val maximum],[w[7],w[0],.val maximum],[w[7],.val maximum,.val maximum]] ∧
      contentWords mf 3=contentWords (machine xs3 one one maximum) 3 ∧
      contentWords mm 3≠contentWords (machine xs3 one one maximum) 3 ∧ contentWords mf 3≠contentWords mr 3 ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local salias) (.local si) rfl)).run ym=
        (.ok (.val (sourceUint (indexValue maximum))),ym) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local salias) (.local si) rfl)).run z=
        (.ok (.val (sourceUint (PrimTy.dflt .uint))),z) ∧
      (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := .int .u256) (.mem 0 1)).run zr=
        (.ok (sourceUint (indexValue maximum)),zr) := by
  obtain ⟨mid,out,ym,z,mm,mf,hi,hipForward,hc,ha,hm,ho,hn,hmem1,hmem2,hword,halloc,hvals,htables,hwords,hframes,hr0,hrm,hro,tail⟩ :=
    reached_assign_delete p xs3 fit3 one one maximum (by decide) (by decide)
  obtain ⟨rmid,rout,yd,zr,md,mr,hw1,hw2,hs1,hs2,hir,hpr,hcd,hca,hcar,hrd,hrr,hmd,hmr,hdmem,hrmem,hyd,hyr,hstack,hallocR⟩ :=
    resolved_uint_delete_assign_word (Source.SemanticsExamples.G0 p) F0 0 (σ xs3 fit3 one one maximum) r (represented xs3 fit3 one one maximum)
      sr si sj sv tr ti tj tv (indexValue one) (indexValue one) (indexValue maximum) rfl rfl rfl rfl rfl rfl rfl rfl
      (by simpa only [σ,Heap.len,elems,vals,List.length_map,indexValue,Int.toNat_natCast] using (show one.val<xs3.length from by decide))
      (by simpa only [σ,Heap.len,elems,vals,List.length_map,indexValue,Int.toNat_natCast] using (show one.val<xs3.length from by decide))
      (initial_repr xs3 fit3 one one maximum) SH (source_memOK xs3 one one maximum)
  have hdknown := delete_run (machine xs3 one one maximum) 3 one fit3 (by decide) rfl rfl rfl
  have hmd' : md=writeMachine (machine xs3 one one maximum) 18 w[0] := (Out.ok.inj (hcd.symm.trans hdknown)).1
  subst md
  have haknown := assign_run (writeMachine (machine xs3 one one maximum) 18 w[0]) 3 one maximum fit3 (by decide) rfl rfl rfl rfl
  have hmr' : mr=writeMachine (writeMachine (machine xs3 one one maximum) 18 w[0]) 18 (.val maximum) := (Out.ok.inj (hca.symm.trans haknown)).1
  subst mr
  have hmknown := assign_run (machine xs3 one one maximum) 3 one maximum fit3 (by decide) rfl rfl rfl rfl
  have hmm : mm=writeMachine (machine xs3 one one maximum) 18 (.val maximum) := (Out.ok.inj (hc.symm.trans hmknown)).1
  subst mm
  have hfknown := delete_run (writeMachine (machine xs3 one one maximum) 18 (.val maximum)) 3 one fit3 (by decide) rfl rfl rfl
  have hmf' : mf=writeMachine (writeMachine (machine xs3 one one maximum) 18 (.val maximum)) 18 w[0] :=
    (Out.ok.inj (ha.symm.trans (by rw [run_append_ok hmknown];exact hfknown))).1
  subst mf
  have hrread : (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := .int .u256) (.mem 0 1)).run zr=(.ok (sourceUint (indexValue maximum)),zr) := by
    apply (hrr.read_nat_iff F0 1 (indexValue maximum)).mpr
    rw [indexedWrite_elems rmid rout r .dyn (indexValue one) (indexValue maximum) hw2]
    apply List.getElem?_set_self
    have hl0 := indexedWrite_elems (hp xs3 fit3) rmid r .dyn (indexValue one) (PrimTy.dflt .uint) hw1
    rw [hl0,List.length_set,elems]
    decide
  refine ⟨ym,z,zr,writeMachine (machine xs3 one one maximum) 18 (.val maximum),
    writeMachine (writeMachine (machine xs3 one one maximum) 18 (.val maximum)) 18 w[0],
    writeMachine (writeMachine (machine xs3 one one maximum) 18 w[0]) 18 (.val maximum),hi,hir,hc,ha,hcar,?_,?_,?_,?_,hrm,hro,hrread⟩
  · rfl
  · rfl
  · intro he
    have hi := congrArg (fun xs : List Word => xs[1]?) he
    change some (Word.val maximum) = some w[0] at hi
    have hv := congrArg Fin.val (Word.val.inj (Option.some.inj hi))
    change W - 1 = 0 at hv
    have hw : 1 < W := by decide
    omega
  · intro he
    have hi := congrArg (fun xs : List Word => xs[1]?) he
    change some w[0] = some (Word.val maximum) at hi
    have hv := congrArg Fin.val (Word.val.inj (Option.some.inj hi.symm))
    change W - 1 = 0 at hv
    have hw : 1 < W := by decide
    omega

/-- An actual changed prefix is retained when the second resolved index fails.
No suffix heap is invented for intrinsic/word errors, and no rollback is claimed. -/
theorem late_rejection (p : Roadmap.Pipeline) :
    ∃ (mid : Heap H) (ym : Source.EMState E0 SΓ) (mm : Machine),
      (Source.execS (Source.SemanticsExamples.G0 p) F0 5 SΓ.length none (.expr (sourceUintIndexedAssign sr si sv) : Source.RStmt E0 [] false .body SΓ SΓ) (sy xs3 one three maximum).1).run (.nil,(sy xs3 one three maximum).2)=
        (.ok (.normal (sy xs3 one three maximum).1),(.nil,ym.2)) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none items (sy xs3 one three maximum).1).run (.nil,(sy xs3 one three maximum).2)=
        (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      Prog.run (σ xs3 fit3 one three maximum) prog=.error .revert ∧
      run assignCode (machine xs3 one three maximum)=.ok mm 0 ∧
      run (assignCode++deleteCode) (machine xs3 one three maximum)=.revert ∧
      MObj.elems .dyn (mid.get r)=vals [⟨7,by decide⟩,maximum,maximum] ∧
      ym.2.heap.get 0=some ⟨SA,sourceUintMemory (vals [⟨7,by decide⟩,maximum,maximum])⟩ ∧
      contentWords mm 3=[w[7],.val maximum,.val maximum] ∧
      frameWords mm=frameWords (machine xs3 one three maximum) ∧ Source.MemOK E0 SH ym := by
  obtain ⟨mid,ym,mm,hw,hsw,hs,hc,hitems,hip,hbad,hall,hr,hm,hy⟩ :=
    resolved_uint_assign_delete_reject (Source.SemanticsExamples.G0 p) F0 0 (σ xs3 fit3 one three maximum) r (represented xs3 fit3 one three maximum)
      sr si sj sv tr ti tj tv (indexValue one) (indexValue three) (indexValue maximum) rfl rfl rfl rfl rfl rfl rfl rfl
      (by simpa only [σ,Heap.len,elems,vals,List.length_map,indexValue,Int.toNat_natCast] using (show one.val<xs3.length from by decide))
      (by simpa only [σ,Heap.len,elems,vals,List.length_map,indexValue,Int.toNat_natCast] using (show xs3.length≤three.val from by decide))
      (initial_repr xs3 fit3 one three maximum) SH (source_memOK xs3 one three maximum)
  have hc0 := assign_run (machine xs3 one three maximum) 3 one maximum fit3 (by decide) rfl rfl rfl rfl
  have hmm : mm=writeMachine (machine xs3 one three maximum) 18 (.val maximum) := (Out.ok.inj (hc.symm.trans hc0)).1
  subst mm
  have hv : MObj.elems .dyn (mid.get r)=vals [⟨7,by decide⟩,maximum,maximum] := by
    rw [indexedWrite_elems (hp xs3 fit3) mid r .dyn (indexValue one) (indexValue maximum) hw,elems]
    rfl
  refine ⟨mid,ym,_,hs,hitems,hip,hc,hall,hv,?_,rfl,frame_write _ 18 _ (by decide),hm⟩
  simpa only [SourceUintMemoryAt,hv] using hr

private def xs33 : List (Fin W) := List.replicate 31 zf++[⟨7,by decide⟩,maximum]
private theorem fit33 : 17+xs33.length≤80 := by decide
private def k31 : Fin W := ⟨31,by decide⟩
private def k32 : Fin W := ⟨32,by decide⟩
/-- Both logical boundary cells materially change: element31 receives max,
element32 deletes to zero; the complete length33 word arrays are observed. -/
theorem boundary_mutation (p : Roadmap.Pipeline) :
    ∃ (ym z : Source.EMState E0 SΓ) (mm mf : Machine),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none items (sy xs33 k31 k32 maximum).1).run (.nil,(sy xs33 k31 k32 maximum).2)=
        (.ok (.normal (sy xs33 k31 k32 maximum).1),(.nil,z.2)) ∧
      run (assignCode++deleteCode) (machine xs33 k31 k32 maximum)=.ok mf 0 ∧
      [contentWords (machine xs33 k31 k32 maximum) 33,contentWords mm 33,contentWords mf 33]=
        [List.replicate 31 w[0]++[w[7],.val maximum],List.replicate 31 w[0]++[.val maximum,.val maximum],List.replicate 31 w[0]++[.val maximum,w[0]]] ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local salias) (.local si) rfl)).run (sy xs33 k31 k32 maximum)=
        (.ok (.val (sourceUint (indexValue ⟨7,by decide⟩))),sy xs33 k31 k32 maximum) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (.indexArray (.local salias) (.local si) rfl)).run ym=
        (.ok (.val (sourceUint (indexValue maximum))),ym) ∧
      (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := .int .u256) (.mem 0 32)).run z=
        (.ok (sourceUint (PrimTy.dflt .uint)),z) := by
  obtain ⟨mid,out,ym,z,mm,mf,hi,hip,hc,ha,hrm,hro,hn,hm1,hm2,hword,halloc,hvals,htables,hwords,hframes,hread0,hread1,hread2,tail⟩ :=
    reached_assign_delete p xs33 fit33 k31 k32 maximum (by decide) (by decide)
  have hv : MObj.elems .dyn (out.get r)=outVals xs33 k31 k32 maximum := by
    have h := List.cons.inj (List.cons.inj hvals |>.2) |>.2
    exact (List.cons.inj h).1
  refine ⟨ym,z,mm,mf,hi,ha,?_,hread0,hread1,(hro.read_nat_iff F0 32 (PrimTy.dflt .uint)).mpr ?_⟩
  · simpa only [xs33,List.map_append,List.map_replicate,List.map_cons,List.map_nil] using hwords
  · rw [hv]
    rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceUintMutationControls.order_and_dropped_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms order_and_dropped_middle
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMutationControls.late_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms late_rejection
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMutationControls.boundary_mutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundary_mutation

private theorem fit0 : 17+([] : List (Fin W)).length≤80 := by decide
/-- Real empty/exact-end rejection, first-failure short circuiting, and Source
low horizon are independent observations. No target panic payload is invented. -/
theorem empty_endpoint_and_timeout (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 4 (sourceUintIndexedAssign sr si sv)).run (sy [] zf zf maximum)=
      (.error (.revert (Source.panicData .index)),sy [] zf zf maximum) ∧
    (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none items (sy [] zf zf maximum).1).run (.nil,(sy [] zf zf maximum).2)=
      (.error (.revert (Source.panicData .index)),(.nil,(sy [] zf zf maximum).2)) ∧
    run (assignCode++deleteCode) (machine [] zf zf maximum)=.revert ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintIndexedDelete sr sj)).run (sy xs3 one three maximum)=
      (.error (.revert (Source.panicData .index)),sy xs3 one three maximum) ∧
    run deleteCode (machine xs3 one three maximum)=.revert ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (sourceUintIndexedAssign sr si sv)).run (sy xs3 one one maximum)=
      (.error .timeout,sy xs3 one one maximum) ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (sourceUintIndexedDelete sr sj)).run (sy xs3 one one maximum)=
      (.error .timeout,sy xs3 one one maximum) := by
  have he := resolved_uint_assign_word_bounds (Source.SemanticsExamples.G0 p) F0 1 (σ [] fit0 zf zf maximum) r (represented [] fit0 zf zf maximum)
    sr si sv tr ti tv (indexValue zf) (indexValue maximum) rfl rfl rfl rfl rfl rfl
    (by change (hp [] fit0).len r .dyn≤0;rw [Heap.len,elems];decide) (initial_repr [] fit0 zf zf maximum)
  have hd := resolved_uint_delete_word_bounds (Source.SemanticsExamples.G0 p) F0 0 (σ xs3 fit3 one three maximum) r (represented xs3 fit3 one three maximum)
    sr sj tr tj (indexValue three) rfl rfl rfl rfl
    (by change (hp xs3 fit3).len r .dyn≤3;rw [Heap.len,elems];decide) (initial_repr xs3 fit3 one three maximum)
  refine ⟨he.1,?_,run_append_revert he.2,hd.1,hd.2,rfl,rfl⟩
  have hs := source_expr_statement_error (Source.SemanticsExamples.G0 p) F0 4 SΓ.length (sourceUintIndexedAssign sr si sv)
    (sy [] zf zf maximum) (sy [] zf zf maximum) _ he.1
  rw [items,Source.execItems,Source.Hoare.run_bind,hs]

private def stale := writeMachine (machine xs3 one one maximum) 2 w[80]
private theorem raw_assign_run (m : Machine) (b k v : Fin W) (n : Nat)
    (hn : n<W) (hk : k.val<n) (haddr : b.val+1+k.val<W)
    (hptr : m.mem 2=.val b) (hi : m.mem 5=.val k) (hv : m.mem 3=.val v)
    (hlen : m.mem b.val=.val (wmod n)) :
    run assignCode m=.ok (writeMachine m (b.val+1+k.val) (.val v)) 0 := by
  change run ([.mload 3]++([.mload 2]++([.mload 5]++writeArrayStackCode))) m=_
  rw [run_append_ok (show run [.mload 3] m=.ok (m.push (.val v)) 0 from by change Out.ok (m.push (m.mem 3)) 0=_;rw [hv])]
  rw [run_append_ok (show run [.mload 2] (m.push (.val v))=.ok ((m.push (.val v)).push (.val b)) 0 from by change Out.ok ((m.push (.val v)).push (m.mem 2)) 0=_;rw [hptr])]
  rw [run_append_ok (show run [.mload 5] ((m.push (.val v)).push (.val b))=.ok (((m.push (.val v)).push (.val b)).push (.val k)) 0 from by change Out.ok (((m.push (.val v)).push (.val b)).push (m.mem 5)) 0=_;rw [hi])]
  have ha := arrayAddrStack_run (m.push (.val v)) b k n hn (by simpa only [Machine.push] using hlen)
  rw [if_pos hk] at ha
  rw [writeArrayStackCode,run_append_ok ha]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt haddr,Out.ok_bind,exec_nil,writeMachine]
private theorem stale_run : run assignCode stale=.ok (writeMachine stale 82 (.val maximum)) 0 := by
  exact raw_assign_run stale ⟨80,by decide⟩ one maximum 2 (by decide) (by decide) (by decide) rfl rfl rfl rfl

/-- Wrong pointer-map initialization is OUTSIDE the initial StateRepr premise.
The raw program executes and changes the neighbor rather than the represented
root; this is not a typed compiler counterexample or new source exclusion. -/
theorem stale_map_negative :
    ¬ StateRepr 1 1 8 (Frag.init Γ) (σ xs3 fit3 one one maximum) base stale ∧
    run assignCode stale=.ok (writeMachine stale 82 (.val maximum)) 0 ∧
    [contentWords stale 3,contentWords (writeMachine stale 82 (.val maximum)) 3]=
      [[w[7],w[0],.val maximum],[w[7],w[0],.val maximum]] ∧
    [(writeMachine stale 82 (.val maximum)).mem 80,(writeMachine stale 82 (.val maximum)).mem 81,(writeMachine stale 82 (.val maximum)).mem 82]=
      [w[2],w[8],.val maximum] ∧
    [(writeMachine stale 82 (.val maximum)).mem 0,(writeMachine stale 82 (.val maximum)).mem 1,(writeMachine stale 82 (.val maximum)).mem 2]=[w[96],w[16],w[80]] := by
  refine ⟨?_,stale_run,rfl,rfl,rfl⟩
  intro hm
  obtain ⟨q,hq,hptr⟩ := hm.pointers tr
  have he : some r=some q := hq
  cases Option.some.inj he
  change w[80]=w[16] at hptr
  exact (by decide : (w[80] : Word)≠w[16]) hptr

/-- info: 'Solidity.Backend.MemoryOps.SourceUintMutationControls.empty_endpoint_and_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empty_endpoint_and_timeout
/-- info: 'Solidity.Backend.MemoryOps.SourceUintMutationControls.stale_map_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_map_negative
end Solidity.Backend.MemoryOps.SourceUintMutationControls
