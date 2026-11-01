import Solidity.Backend.MemoryOps.SourceUintDeclarationSequence
import Solidity.Backend.MemoryOps.SourceUintMutationControls
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceUintDeclarationSequenceControls
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

private def xs : List (Fin W) := [⟨7,by decide⟩,⟨0,W_pos⟩,⟨W-1,by have h := W_pos;omega⟩]
private def one : Fin W := ⟨1,by decide⟩
private def three : Fin W := ⟨3,by decide⟩
private theorem fit : 17+xs.length≤80 := by decide
private abbrev ctorState := (σ xs fit one one three).allocPush (defaultArray .uint ⟨0,W_pos⟩)
private abbrev rr := r.wk (List.prefix_append H [A])
private abbrev fresh := ((σ xs fit one one three).alloc (defaultArray .uint ⟨0,W_pos⟩)).2
private def ctorMachine := writeMachine (allocateMachine (machine xs one one three) ⟨96,by decide⟩ ⟨0,W_pos⟩) 6 w[96]
private def finalMachine := writeMachine ctorMachine 18 w[3]
private def wholeCode := declareNewCode 1 (.lit 0 rfl : Simple C Γ .uint) ++
  writeLocalCode (C := C) (Γ := .mem A::Γ) 1 (.there tr) (.simple (.local (.there ti))) (.simple (.local (.there tv)))

/-- Actual declaration CHANGES context before old-alias mutation. Both pipelines
execute the reached program; all initial/mid/final cells and word frames are tied
to its actual outputs, never a separately assumed second execution. -/
theorem reached_old_alias (p : Roadmap.Pipeline) :
    ∃ (mid z : Source.EMState E0 (SA::SΓ)) (out : Heap ctorState.H),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none
        (sourceUintDeclareAssign sr si sv) (sy xs one one three).1).run (.nil,(sy xs one one three).2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run (σ xs fit one one three) (.cons (.declMem A (.user "freshUint") none rfl rfl)
        (.cons (.assignMem (.index .dyn (.var (.there tr) rfl) (.simple (.local (.there ti))))
          (.val (.simple (.local (.there tv))))) .nil))=.ok ⟨ctorState.withHeap out,List.prefix_append _ _⟩ ∧
      run wholeCode (machine xs one one three)=.ok finalMachine 0 ∧
      [MObj.elems .dyn ((hp xs fit).get r),MObj.elems (H := ctorState.H) .dyn (ctorState.heap.get rr),MObj.elems (H := ctorState.H) .dyn (out.get rr)]=
        [vals xs,vals xs,vals [⟨7,by decide⟩,three,⟨W-1,by have h := W_pos;omega⟩]] ∧
      [(sy xs one one three).2.heap.get 0,mid.2.heap.get 0,z.2.heap.get 0]=
        [some ⟨SA,sourceUintMemory (vals xs)⟩,some ⟨SA,sourceUintMemory (vals xs)⟩,
         some ⟨SA,sourceUintMemory (vals [⟨7,by decide⟩,three,⟨W-1,by have h := W_pos;omega⟩])⟩] ∧
      z.2.heap.get 1=some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩ ∧
      z.2.heap.get 2=some ⟨SA,sourceUintMemory []⟩ ∧
      out.get fresh=ctorState.heap.get fresh ∧
      MObj.elems .dyn (out.get fresh)=[] ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2
        (.indexArray (.local (.there salias)) (.local (.there si)) rfl)).run z=
          (.ok (.val (sourceUint (indexValue three))),z) ∧
      (Source.memElem (E := E0) (Γ := SA::SΓ) 2 0 (.int .u256)).run z=
        (.error (.revert (Source.panicData .index)),z) ∧
      [frameWords (machine xs one one three),frameWords ctorMachine,frameWords finalMachine]=
        [[w[96],w[16],w[16],w[3],w[1],w[1],w[0],w[99],w[0],w[0],w[0],w[3],w[2],w[8],w[9],w[0]],
         [w[97],w[16],w[16],w[3],w[1],w[1],w[96],w[99],w[0],w[0],w[0],w[3],w[2],w[8],w[9],w[0]],
         [w[97],w[16],w[16],w[3],w[1],w[1],w[96],w[99],w[0],w[0],w[0],w[3],w[2],w[8],w[9],w[0]]] ∧
      [contentWords (machine xs one one three) 3,contentWords ctorMachine 3,contentWords finalMachine 3]=
        [xs.map Word.val,xs.map Word.val,[w[7],w[3],.val ⟨W-1,by have h := W_pos;omega⟩]] ∧
      z.1.get (.there salias)=.memRef rfl 0 ∧ z.1.get .here=.memRef rfl 2 ∧
      rr.id=0 ∧ fresh.id=2 ∧ finalMachine.stack=[w[42]] ∧
      StructAllocatorRepr out (upd base 2 ⟨96,by decide⟩) 8 ⟨97,by decide⟩ finalMachine ∧
      Source.MemOK E0 SH z := by
  obtain ⟨mid,z,out,target,hdecl,hs,hitems,hw,hip,hcode,hwrite,hwhole,hrm,hrz,hrf,hfresh,hother,hmem1,hmem2,hm,ha,hglob,hloc,hroot,hnew,hl,htail⟩ :=
    SourceUintMemoryAt.declare_assign_word (Source.SemanticsExamples.G0 p) F0 0
      (σ xs fit one one three) r (views xs fit one one three).2.1 sr si sv tr ti tv
      (indexValue one) (indexValue three) rfl rfl rfl rfl rfl rfl (by change (indexValue one).1.toNat<(hp xs fit).len r .dyn;rw [Heap.len,elems];decide)
      SH (views xs fit one one three).1 (views xs fit one one three).2.2.2
      (initial_allocator xs fit one one three) (by decide) (by decide) (by decide)
  have hc' : run assignCode ctorMachine=.ok finalMachine 0 :=
    assign_run ctorMachine 3 one three (by decide) (by decide) rfl rfl rfl rfl
  have he : target=finalMachine := (Out.ok.inj (hwrite.symm.trans hc')).1
  subst target
  have hk : Heap.Keeps (List.prefix_append H [A]) (hp xs fit) ctorState.heap := (hp xs fit).keeps_alloc _
  have em : MObj.elems (H := ctorState.H) .dyn (ctorState.heap.get rr)=vals xs := by
    change MObj.elems .dyn (ctorState.heap.get (r.wk (List.prefix_append H [A])))=_
    rw [hk r,MObj.elems_wk,List.map_id'' (f := MVal.wk (List.prefix_append H [A]) (.prim .uint)) (fun _ => rfl)]
    exact elems xs fit
  have eo : MObj.elems (H := ctorState.H) .dyn (out.get rr)=vals [⟨7,by decide⟩,three,⟨W-1,by have h := W_pos;omega⟩] := by
    rw [indexedWrite_elems _ _ rr .dyn _ _ hw,em]
    rfl
  have q1 : z.2.heap.get 1=some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩ := by
    rw [hother 1 (by decide),hglob];rfl
  have q2 : z.2.heap.get 2=some ⟨SA,sourceUintMemory []⟩ := by
    rw [hother 2 (by decide),hglob];rfl
  have ef : MObj.elems .dyn (out.get fresh)=[] := by
    rw [hfresh]
    rw [State.allocPush_get,MObj.elems_wk,MObj.elems_dyn]
    simp only [defaultArray,List.replicate_zero,List.map_nil]
  have hsa : z.1.get (.there salias)=.memRef rfl 0 := by rw [hl,hloc];rfl
  have hix : z.1.get (.there si)=sourceUint (indexValue one) := by rw [hl,hloc];rfl
  have hread := hrz.eval_index (Source.SemanticsExamples.G0 p) F0 0 (.there salias) (.there si)
    (indexValue one) hsa hix (by rw [Heap.len,eo];decide)
  refine ⟨mid,z,out,hitems,hip,hwhole,?_,?_,q1,q2,hfresh,ef,?_,source_uint_bounds z 2 [] q2 0 (by decide),?_,?_,hsa,?_,rfl,rfl,htail,ha,hmem2⟩
  · simp only [em,eo,elems]
  · rw [(views xs fit one one three).2.1,hrm,hrz]
    simp only [em,eo,elems]
  · simpa only [eo,vals,List.getElem_cons_zero,List.getElem_cons_succ] using hread
  · rfl
  · rfl
  · rw [hl,hloc];rfl

/-- The old-alias write cannot be replaced by writing the fresh empty root:
that root rejects index0, while the retained alias reaches the material value3. -/
theorem wrong_root_and_skipped_write :
    (ctorMachine.mem 6=w[96] ∧ ctorMachine.mem 2=w[16]) ∧
    ctorMachine.mem 18≠finalMachine.mem 18 ∧
    fresh.id≠rr.id ∧ finalMachine.mem 96=w[0] := by
  decide

/-- info: 'Solidity.Backend.MemoryOps.SourceUintDeclarationSequenceControls.reached_old_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_old_alias
/-- info: 'Solidity.Backend.MemoryOps.SourceUintDeclarationSequenceControls.wrong_root_and_skipped_write' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_root_and_skipped_write
end Solidity.Backend.MemoryOps.SourceUintDeclarationSequenceControls
