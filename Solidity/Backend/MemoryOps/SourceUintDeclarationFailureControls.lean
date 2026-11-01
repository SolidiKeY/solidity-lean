import Solidity.Backend.MemoryOps.SourceUintDeclarationFailure
import Solidity.Backend.MemoryOps.SourceUintDeclarationSequenceControls
import Solidity.Backend.MemoryOps.SourceUintMutationControls
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceUintDeclarationFailureControls
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

private def freshCode := writeLocalCode (C := C) (Γ := .mem A::Γ) 1 .here
  (.simple (.local (.there ti))) (.simple (.local (.there tv)))
private def wholeCode := declareNewCode 1 (.lit 0 rfl : Simple C Γ .uint) ++ freshCode

/-- Whole rejecting program plus all states ACTUALLY exposed: the word/intrinsic
suffix erases its state, so those frames are recorded only at the successful
constructor boundary. Source Items returns its reached globals on the error. -/
theorem reached_rejection (p : Roadmap.Pipeline) :
    ∃ mid : Source.EMState E0 (SA::SΓ),
      (Source.execS (Source.SemanticsExamples.G0 p) F0 5 SΓ.length none
        (.declVar SA : Source.RStmt E0 [] false .body SΓ (SA::SΓ)) (sy xs one one three).1).run (.nil,(sy xs one one three).2)=
          (.ok (.normal mid.1),(.nil,mid.2)) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintIndexedAssign .here (.there si) (.there sv))).run mid=
        (.error (.revert (Source.panicData .index)),mid) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none
        (sourceUintDeclareFreshAssign si sv) (sy xs one one three).1).run (.nil,(sy xs one one three).2)=
          (.error (.revert (Source.panicData .index)),(.nil,mid.2)) ∧
      TRun.declMem A none rfl (σ xs fit one one three)=.ok ⟨ctorState,List.prefix_append _ _⟩ ∧
      Prog.run (σ xs fit one one three) (.cons (.declMem A (.user "freshUint") none rfl rfl)
        (.cons (.assignMem (.index .dyn (.var .here rfl) (.simple (.local (.there ti))))
          (.val (.simple (.local (.there tv))))) .nil))=.error .revert ∧
      run (declareNewCode 1 (.lit 0 rfl : Simple C Γ .uint)) (machine xs one one three)=.ok ctorMachine 0 ∧
      run freshCode ctorMachine=.revert ∧ run wholeCode (machine xs one one three)=.revert ∧
      [(sy xs one one three).2.heap.get 0,(sy xs one one three).2.heap.get 1,(sy xs one one three).2.heap.get 2,mid.2.heap.get 0,mid.2.heap.get 1,mid.2.heap.get 2]=
        [some ⟨SA,sourceUintMemory (vals xs)⟩,some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩,none,some ⟨SA,sourceUintMemory (vals xs)⟩,
         some ⟨SA,sourceUintMemory (vals [⟨8,by decide⟩,⟨9,by decide⟩])⟩,some ⟨SA,sourceUintMemory []⟩] ∧
      [MObj.elems .dyn ((hp xs fit).get r),MObj.elems .dyn ((hp xs fit).get neighbor),MObj.elems (H := ctorState.H) .dyn (ctorState.heap.get rr),
        MObj.elems (H := ctorState.H) .dyn (ctorState.heap.get (neighbor.wk (List.prefix_append H [A]))),
        MObj.elems (H := ctorState.H) .dyn (ctorState.heap.get fresh)]= [vals xs,vals [⟨8,by decide⟩,⟨9,by decide⟩],vals xs,vals [⟨8,by decide⟩,⟨9,by decide⟩],[]] ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 2
        (.indexArray (.local (.there salias)) (.local (.there si)) rfl)).run mid=
          (.ok (.val (sourceUint (indexValue ⟨0,W_pos⟩))),mid) ∧
      [frameWords (machine xs one one three),frameWords ctorMachine]=
        [[w[96],w[16],w[16],w[3],w[1],w[1],w[0],w[99],w[0],w[0],w[0],w[3],w[2],w[8],w[9],w[0]],
         [w[97],w[16],w[16],w[3],w[1],w[1],w[96],w[99],w[0],w[0],w[0],w[3],w[2],w[8],w[9],w[0]]] ∧
      [contentWords (machine xs one one three) 3,contentWords ctorMachine 3]=[xs.map Word.val,xs.map Word.val] ∧
      [mid.1.get .here,mid.1.get (.there sr),mid.1.get (.there salias)]=[.memRef rfl 2,.memRef rfl 0,.memRef rfl 0] ∧
      [mid.1.get (.there si),mid.1.get (.there sj),mid.1.get (.there sv)]=
        [sourceUint (indexValue one),sourceUint (indexValue one),sourceUint (indexValue three)] ∧
      TEnv.get .here ctorState.env=some fresh ∧ TEnv.get (.there tr) ctorState.env=some rr ∧
      [(sy xs one one three).2.heap.next,mid.2.heap.next]=[2,3] ∧
      mid.2≠(sy xs one one three).2 ∧
      mid.2.ex=(sy xs one one three).2.ex ∧ mid.2.events=(sy xs one one three).2.events ∧
      mid.2.logs=(sy xs one one three).2.logs ∧ mid.2.fnLocals=(sy xs one one three).2.fnLocals ∧
      ctorMachine.stack=[w[42]] ∧ fresh.id=2 ∧ rr.id=0 ∧
      StructAllocatorRepr ctorState.heap (upd base 2 ⟨96,by decide⟩) 8 ⟨97,by decide⟩ ctorMachine ∧
      Source.MemOK E0 SH mid := by
  obtain ⟨mid,hdecl,he,hs,hitems,hd,hn,hi,hip,hcode,hbad,hwhole,hrf,ef,hmok,hmword,ha,hglob,hloc,htail,hid,hframes⟩ :=
    source_uint_declare_fresh_reject_word (Source.SemanticsExamples.G0 p) F0 0 (sy xs one one three)
      (σ xs fit one one three) si sv ti tv (indexValue one) (indexValue three) rfl rfl rfl rfl
      SH (views xs fit one one three).1 (views xs fit one one three).2.2.2
      (initial_allocator xs fit one one three) (by decide) (by decide) (by decide)
  have hrm := (hframes r .dyn 0 (views xs fit one one three).2.1).1
  have hkeep : Heap.Keeps (List.prefix_append H [A]) (hp xs fit) ctorState.heap := (hp xs fit).keeps_alloc _
  have em : MObj.elems (H := ctorState.H) .dyn (ctorState.heap.get rr)=vals xs := by
    change MObj.elems .dyn (ctorState.heap.get (r.wk (List.prefix_append H [A])))=_
    rw [hkeep r,MObj.elems_wk,List.map_id'' (f := MVal.wk (List.prefix_append H [A]) (.prim .uint)) (fun _ => rfl)]
    exact elems xs fit
  have en : MObj.elems (H := ctorState.H) .dyn (ctorState.heap.get (neighbor.wk (List.prefix_append H [A])))=
      vals [⟨8,by decide⟩,⟨9,by decide⟩] := by
    rw [hkeep neighbor,MObj.elems_wk,List.map_id'' (f := MVal.wk (List.prefix_append H [A]) (.prim .uint)) (fun _ => rfl)]
    exact neighbor_elems xs fit
  have hra : mid.1.get (.there salias)=.memRef rfl 0 := by rw [hloc];rfl
  have hsi : mid.1.get (.there si)=sourceUint (indexValue one) := by rw [hloc];rfl
  have hread := hrm.eval_index (Source.SemanticsExamples.G0 p) F0 0 (.there salias) (.there si)
    (indexValue one) hra hsi (by rw [Heap.len,em];decide)
  refine ⟨mid,hdecl,he,hitems,hd,hip,hcode,hbad,hwhole,?_,?_,?_,?_,?_,?_,?_,rfl,rfl,?_,?_,?_,?_,?_,?_,htail,hid,rfl,ha,hmok⟩
  · rw [(views xs fit one one three).2.1,(views xs fit one one three).2.2.1,hrm,em]
    simp only [elems,neighbor_elems]
    rw [hglob];rfl
  · simp only [em,en,ef,elems,neighbor_elems]
    rfl
  · simpa only [em,vals,List.getElem_cons_zero,List.getElem_cons_succ] using hread
  · rfl
  · rfl
  · rw [hloc];rfl
  · rw [hloc];rfl
  · rw [hglob];rfl
  · intro heq
    have hh := congrArg (fun q : Source.St E0 => q.heap.next) heq
    rw [hglob] at hh
    change (3 : Nat)=2 at hh
    omega
  · rw [hglob]
  · rw [hglob]
  · rw [hglob]
  · rw [hglob]

/-- Exact panic bytes are Source evidence only. Word `.revert` carries no bytes. -/
theorem index_panic_bytes : Source.panicData .index=
    [0x4e,0x48,0x7b,0x71] ++ List.replicate 31 0 ++ [0x32] := by
  decide

/-- Lower horizon still executes the actual declaration prefix. Its fresh
address remains allocated in Source's error globals; no rollback is inferred. -/
theorem reached_timeout (p : Roadmap.Pipeline) :
    let glob := {(sy xs one one three).2 with heap :=
      ((sy xs one one three).2.heap.alloc ⟨SA,sourceUintMemory []⟩).1}
    (Source.execItems (Source.SemanticsExamples.G0 p) F0 5 SΓ.length none
      (sourceUintDeclareFreshAssign si sv) (sy xs one one three).1).run (.nil,(sy xs one one three).2)=
        (.error .timeout,(.nil,glob)) ∧ glob.heap.next=3 ∧
    glob.heap.get 2=some ⟨SA,sourceUintMemory []⟩ := by
  exact ⟨source_uint_declare_fresh_timeout (Source.SemanticsExamples.G0 p) F0 (sy xs one one three) si sv,rfl,rfl⟩

/-- Skipping declaration reaches a valid old root. Wrong root/index pointers
are observed independently; no inaccessible word error-state is fabricated. -/
theorem skipped_declaration (p : Roadmap.Pipeline) :
    ∃ (out : Heap H) (z : Source.EMState E0 SΓ) (target : Machine),
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 (sourceUintIndexedAssign sr si sv)).run (sy xs one one three)=
        (.ok (.val (sourceUint (indexValue three))),z) ∧
      run assignCode (machine xs one one three)=.ok target 0 ∧
      MObj.elems .dyn (out.get r)=vals [⟨7,by decide⟩,three,⟨W-1,by have h := W_pos;omega⟩] ∧
      (machine xs one one three).mem 6=w[0] := by
  obtain ⟨out,z,target,hw,_,he,_,_,hc,_,_,_,_,_,_⟩ := resolved_uint_assign_word
    (Source.SemanticsExamples.G0 p) F0 0 (σ xs fit one one three) r (views xs fit one one three).2.1
    sr si sv tr ti tv (indexValue one) (indexValue three) rfl rfl rfl rfl rfl rfl
    (by change (indexValue one).1.toNat<(hp xs fit).len r .dyn;rw [Heap.len,elems];decide)
    (views xs fit one one three).2.2.2 SH (views xs fit one one three).1
  refine ⟨out,z,target,he,hc,?_,rfl⟩
  have hh := indexedWrite_elems (hp xs fit) out r .dyn (indexValue one) (indexValue three) hw
  rw [elems] at hh
  exact hh.trans rfl

/-- The same independent initial state has a successful OLD-root program,
whereas selecting the new local gives the actual combined rejection above. -/
theorem old_root_program_disagrees (p : Roadmap.Pipeline) :
    ∃ (mid old : Source.EMState E0 (SA::SΓ)),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none
        (sourceUintDeclareFreshAssign si sv) (sy xs one one three).1).run (.nil,(sy xs one one three).2)=
          (.error (.revert (Source.panicData .index)),(.nil,mid.2)) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 SΓ.length none
        (sourceUintDeclareAssign sr si sv) (sy xs one one three).1).run (.nil,(sy xs one one three).2)=
          (.ok (.normal old.1),(.nil,old.2)) := by
  obtain ⟨mid,h⟩ := reached_rejection p
  obtain ⟨_,old,_,ho⟩ := SourceUintDeclarationSequenceControls.reached_old_alias p
  exact ⟨mid,old,h.2.2.1,ho.1⟩

/-- Before declaration completes, the same program times out with initial globals. -/
theorem early_timeout (p : Roadmap.Pipeline) :
    (Source.execItems (Source.SemanticsExamples.G0 p) F0 3 SΓ.length none
      (sourceUintDeclareFreshAssign si sv) (sy xs one one three).1).run (.nil,(sy xs one one three).2)=
        (.error .timeout,(.nil,(sy xs one one three).2)) :=
  source_uint_declare_fresh_early_timeout (Source.SemanticsExamples.G0 p) F0 (sy xs one one three) si sv

/-- Every runtime horizon is classified against the actual reached globals.
No new bound on execution or admitted programs is imposed by this theorem. -/
theorem all_horizons (p : Roadmap.Pipeline) (fuel : Nat) :
    let globals := if fuel<4 then (sy xs one one three).2 else
      {(sy xs one one three).2 with heap := ((sy xs one one three).2.heap.alloc ⟨SA,sourceUintMemory []⟩).1}
    let halt : Source.Halt := if fuel<6 then .timeout else .revert (Source.panicData .index)
    (Source.execItems (Source.SemanticsExamples.G0 p) F0 fuel SΓ.length none
      (sourceUintDeclareFreshAssign si sv) (sy xs one one three).1).run (.nil,(sy xs one one three).2)=
        (.error halt,(.nil,globals)) := by
  by_cases hf : fuel<6
  · have h := source_uint_declare_fresh_low_horizons (Source.SemanticsExamples.G0 p) F0 (sy xs one one three) si sv fuel (by omega)
    simpa only [hf,↓reduceIte] using h
  · obtain ⟨n,rfl⟩ : ∃ n,fuel=n+6 := ⟨fuel-6,by omega⟩
    obtain ⟨mid,hdecl,he,hs,hitems,hd,hn,hi,hip,hcode,hbad,hwhole,hrf,ef,hmok,hmword,ha,hglob,hloc,htail,hid,hframes⟩ :=
      source_uint_declare_fresh_reject_word (Source.SemanticsExamples.G0 p) F0 n (sy xs one one three)
        (σ xs fit one one three) si sv ti tv (indexValue one) (indexValue three) rfl rfl rfl rfl
        SH (views xs fit one one three).1 (views xs fit one one three).2.2.2
        (initial_allocator xs fit one one three) (by decide) (by decide) (by decide)
    rw [hglob] at hitems
    simpa only [show ¬n+6<4 from by omega,show ¬n+6<6 from by omega,↓reduceIte] using hitems

/-- info: 'Solidity.Backend.MemoryOps.SourceUintDeclarationFailureControls.reached_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_rejection
/-- info: 'Solidity.Backend.MemoryOps.SourceUintDeclarationFailureControls.index_panic_bytes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms index_panic_bytes
/-- info: 'Solidity.Backend.MemoryOps.SourceUintDeclarationFailureControls.reached_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_timeout
/-- info: 'Solidity.Backend.MemoryOps.SourceUintDeclarationFailureControls.skipped_declaration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms skipped_declaration
/-- info: 'Solidity.Backend.MemoryOps.SourceUintDeclarationFailureControls.old_root_program_disagrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms old_root_program_disagrees
/-- info: 'Solidity.Backend.MemoryOps.SourceUintDeclarationFailureControls.early_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms early_timeout
/-- info: 'Solidity.Backend.MemoryOps.SourceUintDeclarationFailureControls.all_horizons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms all_horizons
end Solidity.Backend.MemoryOps.SourceUintDeclarationFailureControls
