import Solidity.Backend.MemoryOps.SourceUintFixedProgramFailure
import Solidity.Backend.MemoryOps.SourceUintFixedDefaultControls
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceUintFixedProgramControls
open Evm Evm.Memory
open Source.SemanticsExamples (E0 F0 s0)
private def C : Contract := {vars := []}
private abbrev A : RefTy := .fixed (.prim .uint) 1
private abbrev H : HTy := [A,A]
private abbrev Δ : Ctx := [.val .uint,.val .uint,.mem A,.mem A,.mem A]
private abbrev SA := Source.STy.array .memory (.int .u256) (some 1)
private abbrev Γ : Source.RCtx := [.int .u256,.int .u256,SA,SA,SA]
private def u (v : Nat) : PrimTy.uint.Denote := indexValue (wmod v)
private def left : HRef H A := ⟨0,rfl⟩
private def right : HRef H A := ⟨1,rfl⟩
private def hp : Heap H := (⟨[u 7],by decide⟩,⟨[u 9],by decide⟩,())
private def state (k l : Nat) : State C Δ := {storage := Storage.init C,H := H,heap := hp,env := (u l,u k,some right,some left,some left,())}
private def base (i : Nat) : Fin W := if i=0 then wmod 16 else wmod 24
private def machine (k l : Nat) : Machine := {Machine.init with stack := [w[77]],mem := fun a =>
  if a=0 then w[32] else if a=1 then w[16] else if a=2 then w[16] else if a=3 then w[24]
  else if a=5 then (Word.val (wmod l)) else if a=4 then (Word.val (wmod k)) else if a=15 then w[99] else if a=16 then w[7] else if a=24 then w[9] else w[0]}
private theorem refs {R : RefTy} (q : HRef H R) : R=A ∧ (HEq q left ∨ HEq q right) := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi;exact ⟨rfl,.inl HEq.rfl⟩
  | succ i => cases i with
    | zero => cases hi;exact ⟨rfl,.inr HEq.rfl⟩
    | succ i => cases hi
private theorem no_struct {s : Name} (q : HRef H (.struct s)) : False := by
  obtain ⟨ht,_⟩ := refs q
  cases ht
private theorem heap_repr (k l : Nat) : Objects.HeapRepr hp base 8 (machine k l) := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · intro R q
    obtain ⟨rfl,hq|hq⟩ := refs q <;> cases hq <;> decide
  · intro R q
    obtain ⟨rfl,hq|hq⟩ := refs q <;> cases hq <;> decide
  · intro R Q q r hn
    obtain ⟨rfl,hq|hq⟩ := refs q <;> cases hq
      <;> obtain ⟨rfl,hr|hr⟩ := refs r <;> cases hr
      <;> first | exact (hn rfl).elim | decide
  · intro A E a r
    obtain ⟨rfl,hr|hr⟩ := refs r <;> cases hr <;> cases a
    all_goals
      refine ⟨by decide,?_,?_⟩
      · intro hh
        cases (by simpa only [Objects.header] using hh : (0 : Nat)=1)
      · intro i v hv
        simp only [Heap.get,Objs.get,hp,left,right,MObj.elems_fixed] at hv
        cases i with
        | zero => cases Option.some.inj hv;exact ReprV.uint_of rfl
        | succ i => cases hv
  · intro s r
    exact (no_struct r).elim
  · intro s f R r hf
    exact (no_struct r).elim
private theorem initial_repr (k l : Nat) : Objects.StateRepr 1 1 8 (Frag.init Δ) (state k l) base (machine k l) := by
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨?_,heap_repr k l,?_,by decide⟩
  · refine ⟨hc.store,?_,?_,hc.net,hc.netSelf,hc.bound,?_,hc.env,hc.funds,hc.oracle⟩
    · intro p i
      cases i with
      | here => exact ReprV.uint_of rfl
      | there i => cases i with
        | here => exact ReprV.uint_of rfl
        | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro R i hi
      cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro R i hi
      cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
  · intro R i
    cases i with | there i => cases i with
      | there i => cases i with
        | here => exact ⟨right,rfl,rfl⟩
        | there i => cases i with
          | here => exact ⟨left,rfl,rfl⟩
          | there i => cases i with
            | here => exact ⟨left,rfl,rfl⟩
            | there i => nomatch i
private theorem initial_allocator (k l : Nat) : Objects.AllocatorRepr hp base 8 ⟨32,by decide⟩ (machine k l) := by
  refine ⟨heap_repr k l,⟨by decide,by decide,rfl,?_⟩,?_⟩
  · intro a ha
    change 32≤a at ha
    simp only [machine,if_neg (show a≠0 by omega),if_neg (show a≠1 by omega),if_neg (show a≠2 by omega),
      if_neg (show a≠3 by omega),if_neg (show a≠4 by omega),if_neg (show a≠5 by omega),if_neg (show a≠15 by omega),if_neg (show a≠16 by omega),if_neg (show a≠24 by omega)]
  · intro R q
    obtain ⟨rfl,hq|hq⟩ := refs q <;> cases hq <;> decide

private def sourceObject (v : PrimTy.uint.Denote) : Source.Data E0.layout SA :=
  .array 1 (fun _ h => by cases h;rfl) (fun _ => .val (sourceUint v))
private theorem one_conversion {K : HTy} (v : PrimTy.uint.Denote) :
    sourceUintFixedObject (D := E0.layout) (⟨[v],by rfl⟩ : MObj K A)=sourceObject v := by
  unfold sourceUintFixedObject sourceObject
  congr 1
  funext i
  have hi : i.val=0 := by have h := i.isLt;omega
  simp only [hi,List.getElem_cons_zero]
private def y0 : Source.EMState E0 [] := (.nil,s0)
private def y1 : Source.EMState E0 [] := ((Source.allocRef (sourceObject (u 7))).run y0).2
private def y2 : Source.EMState E0 [] := ((Source.allocRef (sourceObject (u 9))).run y1).2
private def sy (k l : Nat) : Source.EMState E0 Γ :=
  (.cons (sourceUint (u l)) (.cons (sourceUint (u k)) (.cons (.memRef rfl 1) (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil)))),y2.2)
private abbrev SH := (Source.Heap.empty (D := E0.layout)).ty
private def si : Source.Idx Γ (.int .u256) := .there .here
private def sj : Source.Idx Γ (.int .u256) := .here
private def sr : Source.Idx Γ SA := .there (.there (.there .here))
private def salias : Source.Idx Γ SA := .there (.there (.there (.there .here)))
private theorem represented_left (k l : Nat) : SourceUintFixedAt (sy k l) 0 hp left := by
  unfold SourceUintFixedAt
  change (sy k l).2.heap.get 0=some ⟨SA,sourceUintFixedObject (D := E0.layout) (⟨[u 7],by decide⟩ : MObj H A)⟩
  rw [one_conversion];rfl
private theorem represented_right (k l : Nat) : SourceUintFixedAt (sy k l) 1 hp right := by
  unfold SourceUintFixedAt
  change (sy k l).2.heap.get 1=some ⟨SA,sourceUintFixedObject (D := E0.layout) (⟨[u 9],by decide⟩ : MObj H A)⟩
  rw [one_conversion];rfl
private theorem source_memOK (k l : Nat) : Source.MemOK E0 SH (sy k l) := by
  have h0 : Source.MemOK E0 SH y0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have h1 := source_uint_fixed_alloc_memOK (E := E0) (Γ := []) SH (⟨[u 7],by decide⟩ : MObj H A) y0 h0
  rw [one_conversion] at h1
  change Source.MemOK E0 SH y1 ∧ _ at h1
  have h2 := source_uint_fixed_alloc_memOK (E := E0) (Γ := []) SH (⟨[u 9],by decide⟩ : MObj H A) y1 h1.1
  rw [one_conversion] at h2
  change Source.MemOK E0 SH y2 ∧ _ at h2
  exact ⟨⟨h2.1.1.1,⟨trivial,⟨trivial,⟨⟨SA,rfl,rfl⟩,⟨⟨SA,rfl,rfl⟩,⟨⟨SA,rfl,rfl⟩,trivial⟩⟩⟩⟩⟩⟩,h2.1.2⟩

private def g (n : Nat) := hp.allocDefault (.fixed (.prim .uint) n) rfl
private def fresh (n : Nat) := (g n).val
private def grownState (k l : Nat) (n : Nat) := ((state k l).adopt (g n)).1.push (t := .mem (.fixed (.prim .uint) n)) (some (fresh n))
private def post (k l : Nat) (n : Nat) : Source.EMState E0 ((.array .memory (.int .u256) (some n))::Γ) :=
  (.cons (.memRef rfl 2) (sy k l).1,{(sy k l).2 with heap := ((sy k l).2.heap.alloc ⟨.array .memory (.int .u256) (some n),sourceUintFixedZero n⟩).1})
private def wordPost (k l : Nat) (n : Nat) := writeMachine (allocateStructMachine (machine k l) ⟨32,by decide⟩ (max 1 n)) 6 w[32]
private def code (n : Nat) := Objects.defaultDeclareCode (Γ := Δ) (Objects.DefaultBuilder.fixedPrimitive .uint n).code 1
private def cells (m : Machine) := [m.mem 0,m.mem 1,m.mem 2,m.mem 3,m.mem 4,m.mem 5,m.mem 6,m.mem 15,
  m.mem 16,m.mem 24,m.mem 31,m.mem 32,m.mem 33,m.mem 34,m.mem 64,m.mem 65]
private theorem word_run (k l : Nat) (n : Nat) : run (code n) (machine k l)=.ok ((wordPost k l) n) 0 := by
  change run (allocateStructCode (max 1 n) ++ [.mstore 6]) (machine k l)=_
  rw [run_append_ok (allocateStruct_run (machine k l) ⟨32,by decide⟩ (max 1 n) rfl)]
  rfl



private def updateCode (n : Nat) : List Instr :=
  [.mload 4,.mload 6,.mload 4] ++ Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))
private def clearCode (n : Nat) : List Instr :=
  [.push w[0],.mload 6,.mload 4] ++ Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))
private def rejectCode (n : Nat) : List Instr :=
  [.push w[0],.mload 6,.mload 5] ++ Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))

/-- Independently inhabited populated original inputs with separate numeric
write and late-delete indices; both old aliases and neighbor are represented. -/
theorem initial_views (k l : Nat) : Source.MemOK E0 SH (sy k l) ∧
    SourceUintFixedAt (sy k l) 0 hp left ∧ SourceUintFixedAt (sy k l) 1 hp right ∧
    Objects.StateRepr 1 1 8 (Frag.init Δ) (state k l) base (machine k l) ∧
    Objects.AllocatorRepr hp base 8 ⟨32,by decide⟩ (machine k l) :=
  ⟨source_memOK k l,represented_left k l,represented_right k l,initial_repr k l,initial_allocator k l⟩
/-- Actual constructor followed by reached indexed mutation/deletion. The same
initial numeric local supplies the index and value, so length33/index32 is a
material32 write; length1/index0 remains the discriminating fixed endpoint case. -/
theorem program_runs (p : Roadmap.Pipeline) (n k l : Nat) (hn : 0<n) (hk : k<n)
    (hs : 32+max 1 n<W) :
    ∃ (base' : Nat → Fin W) (target0 target1 target2 : Machine) (out1 out2 : Heap (g n).H') (z1 z2 : Source.EMState E0 ((.array .memory (.int .u256) (some n))::Γ)),
      (Source.execS (Source.SemanticsExamples.G0 p) F0 (n+6) Γ.length none
        (.declVar (.array .memory (.int .u256) (some n)) : Source.RStmt E0 [] false .body Γ ((.array .memory (.int .u256) (some n))::Γ)) (sy k l).1).run (.nil,(sy k l).2)=
          (.ok (.normal (post k l n).1),(.nil,(post k l n).2)) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 (n+4)
        (sourceUintFixedIndexedAssign .here (.there si) (.there si))).run (post k l n)=
          (.ok (.val (sourceUint (u k))),z1) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 (n+3)
        (sourceUintFixedIndexedDelete .here (.there si))).run z1=(.ok Source.RVal.unit,z2) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 (n+7) Γ.length none (sourceUintFixedProgram n si si) (sy k l).1).run (.nil,(sy k l).2)=
        (.ok (.normal z2.1),(.nil,z2.2)) ∧
      Prog.run (state k l) (intrinsicUintFixedProgram n (.there .here) (.there .here))=
        .ok ⟨(grownState k l n).withHeap out2,(g n).ext⟩ ∧
      SourceUintFixedAt z1 2 out1 (fresh n) ∧ SourceUintFixedAt z2 2 out2 (fresh n) ∧
      [(out1.get (fresh n)).1,(out2.get (fresh n)).1]=
        [(List.replicate n (PrimTy.dflt .uint)).set k (u k),List.replicate n (PrimTy.dflt .uint)] ∧
      [out2.get (left.wk (g n).ext) |>.1,out2.get (right.wk (g n).ext) |>.1]=[[u 7],[u 9]] ∧
      [z1.2.heap.get 0,z1.2.heap.get 1,z2.2.heap.get 0,z2.2.heap.get 1]=
        [(sy k l).2.heap.get 0,(sy k l).2.heap.get 1,(sy k l).2.heap.get 0,(sy k l).2.heap.get 1] ∧
      SourceUintFixedAt z2 0 out2 (left.wk (g n).ext) ∧
      run (code n) (machine k l)=.ok target0 0 ∧
      run (updateCode n) target0=.ok target1 0 ∧ run (clearCode n) target1=.ok target2 0 ∧
      run (code n ++ updateCode n ++ clearCode n) (machine k l)=.ok target2 0 ∧
      Objects.StateRepr 1 1 8 ((Frag.init Δ).push (.mem (.fixed (.prim .uint) n)) .ok)
        ((grownState k l n).withHeap out2) base' target2 ∧
      Objects.AllocatorRepr out2 base' 8 ⟨32+max 1 n,hs⟩ target2 ∧
      Source.MemOK E0 SH z1 ∧ Source.MemOK E0 SH z2 ∧
      z1.1=(post k l n).1 ∧ z2.1=(post k l n).1 ∧
      z2.1.get .here=.memRef rfl 2 ∧ z2.1.get (.there sr)=.memRef rfl 0 ∧
      z2.1.get (.there salias)=.memRef rfl 0 ∧ z2.1.get (.there (.there (.there .here)))=.memRef rfl 1 ∧
      z2.1.get (.there si)=sourceUint (u k) ∧ z2.1.get (.there sj)=sourceUint (u l) ∧
      z2.2.ex=(sy k l).2.ex ∧ z2.2.events=(sy k l).2.events ∧
      z2.2.logs=(sy k l).2.logs ∧ z2.2.fnLocals=(sy k l).2.fnLocals ∧
      [target0.stack,target1.stack,target2.stack]=[[w[77]],[w[77]],[w[77]]] := by
  have hkw : k<W := by omega
  have hki : (u k).1.toNat=k := by change (wmod k).val=k;exact Nat.mod_eq_of_lt hkw
  obtain ⟨base',target0,target1,target2,out1,out2,z1,z2,hd,hstmt1,hstmt2,hitems,hprog,hw1,hw2,hr0,hr1,hr2,hc0,hc1,hc2,hwhole,hm2,ha2,hmok1,hmok2,hl1,hl2,hstack2,hs1,hs2,he1,he2,hstack0,hstack1,hother,hsource,hex,hev,hlog,hfn⟩ :=
    source_uint_fixed_program_word (Source.SemanticsExamples.G0 p) F0 (sy k l) (state k l) n hn si si (.there .here) (.there .here)
      (u k) (u k) rfl rfl rfl rfl (by rw [hki];exact hk) SH (source_memOK k l)
      (initial_repr k l) (initial_allocator k l) (by decide) hs (by decide)
  change (g n).heap.writeAddr (.index (fresh n) .fixed (u k)) (u k)=some out1 at hw1
  change out1.writeAddr (.index (fresh n) .fixed (u k)) (PrimTy.dflt .uint)=some out2 at hw2
  have ho1 : out1=(g n).heap.set (fresh n) (MObj.setElem .fixed ((g n).heap.get (fresh n)) k (u k)) := by
    simpa only [Heap.writeAddr,Heap.setIndex,MObj.elems_fixed,hki,((g n).heap.get (fresh n)).2,if_pos hk,Option.some.injEq] using hw1.symm
  have ho2 : out2=out1.set (fresh n) (MObj.setElem .fixed (out1.get (fresh n)) k (PrimTy.dflt .uint)) := by
    simpa only [Heap.writeAddr,Heap.setIndex,MObj.elems_fixed,hki,(out1.get (fresh n)).2,if_pos hk,Option.some.injEq] using hw2.symm
  have hz0 := (source_uint_fixed_intrinsic (sy k l) hp n hn).2.1
  have hv1 : (out1.get (fresh n)).1=(List.replicate n (PrimTy.dflt .uint)).set k (u k) := by
    rw [ho1,Heap.get_set_same,MObj.setElem_fixed]
    change ((g n).heap.get (fresh n)).1.set k (u k)=_
    rw [show ((g n).heap.get (fresh n)).1=List.replicate n (PrimTy.dflt .uint) from by simpa only [MObj.elems_fixed] using hz0]
  have hv2 : (out2.get (fresh n)).1=List.replicate n (PrimTy.dflt .uint) := by
    rw [ho2,Heap.get_set_same,MObj.setElem_fixed]
    change (out1.get (fresh n)).1.set k (PrimTy.dflt .uint)=_
    rw [hv1,List.set_set]
    apply List.ext_getElem
    · simp only [List.length_set]
    · intro j hj hj'
      rw [List.getElem_set]
      split <;> simp only [List.getElem_replicate]
  have hk0 : Heap.Keeps (g n).ext hp (g n).heap := (source_uint_fixed_intrinsic (sy k l) hp n hn).2.2.1
  change ∀ address,address≠2 → z2.2.heap.get address=(post k l n).2.heap.get address at hsource
  have hf1 := hr0.write_frames F0 (n+3) (u k) (u k) (by rw [hki];exact hk) hw1 hs1
  have hleft : SourceUintFixedAt z2 0 out2 (left.wk (g n).ext) := by
    unfold SourceUintFixedAt
    rw [hsource 0 (by decide),hother left]
    change (post k l n).2.heap.get 0=some ⟨SA,sourceUintFixedObject ((g n).heap.get (left.wk (g n).ext))⟩
    rw [hk0 left]
    change (post k l n).2.heap.get 0=some _
    change ((sy k l).2.heap.alloc ⟨.array .memory (.int .u256) (some n),sourceUintFixedZero n⟩).1.get 0=_
    rw [Source.Heap.alloc_other _ _ (by change (0 : Nat)≠2;decide)]
    exact represented_left k l
  refine ⟨base',target0,target1,target2,out1,out2,z1,z2,hd,he1,he2,hitems,hprog,hr1,hr2,by rw [hv1,hv2],?_,?_,hleft,hc0,hc1,hc2,hwhole,hm2,ha2,hmok1,hmok2,hl1,hl2,by rw [hl2];rfl,by rw [hl2];rfl,by rw [hl2];rfl,by rw [hl2];rfl,by rw [hl2];rfl,by rw [hl2];rfl,hex,hev,hlog,hfn,?_⟩
  · rw [hother left,hother right]
    change [((g n).heap.get (left.wk (g n).ext)).1,((g n).heap.get (right.wk (g n).ext)).1]=_
    rw [hk0 left,hk0 right]
    rfl
  · rw [hf1.2.2.1 0 (by change (0 : Nat)≠2;decide),hf1.2.2.1 1 (by change (1 : Nat)≠2;decide),hsource 0 (by decide),hsource 1 (by decide)]
    rfl
  · rw [hstack0,hstack1,hstack2]
    rfl

/-- A real valid write precedes the reached delete rejection. Source retains
exact changed globals; intrinsic and word errors expose no final heap/machine. -/
theorem late_rejection (p : Roadmap.Pipeline) (n k l : Nat) (hn : 0<n) (hk : k<n)
    (hl : n≤l) (hlw : l<W) (hs : 32+max 1 n<W) :
    ∃ (base' : Nat → Fin W) (target0 target1 : Machine) (out : Heap (g n).H')
      (z : Source.EMState E0 ((.array .memory (.int .u256) (some n))::Γ)),
      (Source.execS (Source.SemanticsExamples.G0 p) F0 (n+6) Γ.length none
        (.declVar (.array .memory (.int .u256) (some n)) : Source.RStmt E0 [] false .body Γ ((.array .memory (.int .u256) (some n))::Γ)) (sy k l).1).run (.nil,(sy k l).2)=
          (.ok (.normal (post k l n).1),(.nil,(post k l n).2)) ∧
      (Source.execS (Source.SemanticsExamples.G0 p) F0 (n+5) Γ.length none
        (.expr (sourceUintFixedIndexedAssign .here (.there si) (.there si)) : Source.RStmt E0 [] false .body ((.array .memory (.int .u256) (some n))::Γ) ((.array .memory (.int .u256) (some n))::Γ)) (post k l n).1).run (.nil,(post k l n).2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 (n+7) Γ.length none (sourceUintFixedRejectProgram n si si sj) (sy k l).1).run (.nil,(sy k l).2)=
        (.error (.revert (Source.panicData .index)),(.nil,z.2)) ∧
      Prog.run (state k l) (intrinsicUintFixedRejectProgram n (.there .here) (.there .here) .here)=.error .revert ∧
      (out.get (fresh n)).1=(List.replicate n (PrimTy.dflt .uint)).set k (u k) ∧
      SourceUintFixedAt z 2 out (fresh n) ∧
      [out.get (left.wk (g n).ext) |>.1,out.get (right.wk (g n).ext) |>.1]=[[u 7],[u 9]] ∧
      [z.2.heap.get 0,z.2.heap.get 1]=[(sy k l).2.heap.get 0,(sy k l).2.heap.get 1] ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 (n+3)
        (sourceUintFixedIndexedDelete .here (.there sj))).run z=(.error (.revert (Source.panicData .index)),z) ∧
      run (code n) (machine k l)=.ok target0 0 ∧ run (updateCode n) target0=.ok target1 0 ∧
      run (rejectCode n) target1=.revert ∧ run (code n ++ updateCode n ++ rejectCode n) (machine k l)=.revert ∧
      Objects.StateRepr 1 1 8 ((Frag.init Δ).push (.mem (.fixed (.prim .uint) n)) .ok)
        ((grownState k l n).withHeap out) base' target1 ∧
      Objects.AllocatorRepr out base' 8 ⟨32+max 1 n,hs⟩ target1 ∧
      Source.MemOK E0 SH z ∧ z.1=(post k l n).1 ∧ target1.stack=[w[77]] ∧
      z.2.ex=(sy k l).2.ex ∧ z.2.events=(sy k l).2.events ∧
      z.2.logs=(sy k l).2.logs ∧ z.2.fnLocals=(sy k l).2.fnLocals := by
  have hkw : k<W := by omega
  have hki : (u k).1.toNat=k := by change (wmod k).val=k;exact Nat.mod_eq_of_lt hkw
  have hli : (u l).1.toNat=l := by change (wmod l).val=l;exact Nat.mod_eq_of_lt hlw
  obtain ⟨base',target0,target1,out,z,hd,hs1,hbad,hitems,hprog,hw,hnone,hr0,hr1,hc0,hc1,hbr,whole,hm1,ha1,hmok,hl1,hstack,hother,hsource,hex,hev,hlog,hfn⟩ :=
    source_uint_fixed_program_reject (Source.SemanticsExamples.G0 p) F0 (sy k l) (state k l) n hn si si sj (.there .here) (.there .here) .here
      (u k) (u k) (u l) rfl rfl rfl rfl (by rw [hli];exact hl) rfl rfl (by rw [hki];exact hk)
      SH (source_memOK k l) (initial_repr k l) (initial_allocator k l) (by decide) hs (by decide)
  change (g n).heap.writeAddr (.index (fresh n) .fixed (u k)) (u k)=some out at hw
  have hout : out=(g n).heap.set (fresh n) (MObj.setElem .fixed ((g n).heap.get (fresh n)) k (u k)) := by
    simpa only [Heap.writeAddr,Heap.setIndex,MObj.elems_fixed,hki,((g n).heap.get (fresh n)).2,if_pos hk,Option.some.injEq] using hw.symm
  have hz0 : ((g n).heap.get (fresh n)).1=List.replicate n (PrimTy.dflt .uint) := by
    simpa only [MObj.elems_fixed] using (source_uint_fixed_intrinsic (sy k l) hp n hn).2.1
  have hv : (out.get (fresh n)).1=(List.replicate n (PrimTy.dflt .uint)).set k (u k) := by
    rw [hout,Heap.get_set_same,MObj.setElem_fixed]
    change ((g n).heap.get (fresh n)).1.set k (u k)=_
    rw [hz0]
  change ∀ address,address≠2 → z.2.heap.get address=(post k l n).2.heap.get address at hsource
  have hk0 : Heap.Keeps (g n).ext hp (g n).heap := (source_uint_fixed_intrinsic (sy k l) hp n hn).2.2.1
  refine ⟨base',target0,target1,out,z,hd,hs1,hitems,hprog,hv,hr1,?_,?_,hbad,hc0,hc1,hbr,whole,hm1,ha1,hmok,hl1,hstack,hex,hev,hlog,hfn⟩
  · rw [hother left,hother right]
    change [((g n).heap.get (left.wk (g n).ext)).1,((g n).heap.get (right.wk (g n).ext)).1]=_
    rw [hk0 left,hk0 right]
    rfl
  · rw [hsource 0 (by decide),hsource 1 (by decide)]
    rfl
private theorem update_run (m : Machine) (n k : Nat) (hk : k<n) (hkw : k<W) (ha : 32+k<W)
    (h4 : m.mem 4=Word.val (wmod k)) (h5 : m.mem 6=w[32]) :
    run (updateCode n) m=.ok (writeMachine m (32+k) (.val (wmod k))) 0 := by
  change run ([.mload 4,.mload 6,.mload 4] ++ Objects.fixedAddrCode n ++ [.mstoreAt]) m=_
  have hp : run [.mload 4,.mload 6,.mload 4] m=
      .ok (((m.push (.val (wmod k))).push w[32]).push (.val (wmod k))) 0 := by
    simp only [run,exec_cons_zero,Instr.step,Machine.next,Machine.push,Out.ok_bind,exec_nil,h4,h5]
  have hc := Objects.fixedAddr_run (m.push (.val (wmod k))) ⟨32,by decide⟩ (wmod k) n
  rw [if_pos (by simpa only [wmod_of_lt hkw] using hk)] at hc
  rw [List.append_assoc,run_append_ok hp,run_append_ok hc]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,Out.ok_bind,exec_nil,
    wmod_of_lt hkw,wmod_of_lt ha,writeMachine]

private theorem clear_run (m : Machine) (n k : Nat) (hk : k<n) (hkw : k<W) (ha : 32+k<W)
    (h4 : m.mem 4=Word.val (wmod k)) (h5 : m.mem 6=w[32]) :
    run (clearCode n) m=.ok (writeMachine m (32+k) w[0]) 0 := by
  change run ([.push w[0],.mload 6,.mload 4] ++ Objects.fixedAddrCode n ++ [.mstoreAt]) m=_
  have hp : run [.push w[0],.mload 6,.mload 4] m=
      .ok (((m.push w[0]).push w[32]).push (.val (wmod k))) 0 := by
    simp only [run,exec_cons_zero,Instr.step,Machine.next,Machine.push,Out.ok_bind,exec_nil,h4,h5]
  have hc := Objects.fixedAddr_run (m.push w[0]) ⟨32,by decide⟩ (wmod k) n
  rw [if_pos (by simpa only [wmod_of_lt hkw] using hk)] at hc
  rw [List.append_assoc,run_append_ok hp,run_append_ok hc]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,Out.ok_bind,exec_nil,
    wmod_of_lt hkw,wmod_of_lt ha,writeMachine]

private theorem update_reject (m : Machine) (n k : Nat) (hk : n≤k) (hkw : k<W)
    (h4 : m.mem 4=Word.val (wmod k)) (h5 : m.mem 6=w[32]) : run (updateCode n) m=.revert := by
  change run ([.mload 4,.mload 6,.mload 4] ++ Objects.fixedAddrCode n ++ [.mstoreAt]) m=_
  have hp : run [.mload 4,.mload 6,.mload 4] m=
      .ok (((m.push (.val (wmod k))).push w[32]).push (.val (wmod k))) 0 := by
    simp only [run,exec_cons_zero,Instr.step,Machine.next,Machine.push,Out.ok_bind,exec_nil,h4,h5]
  have hc := Objects.fixedAddr_run (m.push (.val (wmod k))) ⟨32,by decide⟩ (wmod k) n
  rw [if_neg (by simpa only [wmod_of_lt hkw] using Nat.not_lt.mpr hk)] at hc
  rw [List.append_assoc,run_append_ok hp,run_append_revert hc]


private theorem reject_run (m : Machine) (n l : Nat) (hl : n≤l) (hlw : l<W)
    (h5 : m.mem 5=Word.val (wmod l)) (h6 : m.mem 6=w[32]) : run (rejectCode n) m=.revert := by
  change run ([.push w[0],.mload 6,.mload 5] ++ Objects.fixedAddrCode n ++ [.mstoreAt]) m=_
  have hp : run [.push w[0],.mload 6,.mload 5] m=
      .ok (((m.push w[0]).push w[32]).push (.val (wmod l))) 0 := by
    simp only [run,exec_cons_zero,Instr.step,Machine.next,Machine.push,Out.ok_bind,exec_nil,h5,h6]
  have hc := Objects.fixedAddr_run (m.push w[0]) ⟨32,by decide⟩ (wmod l) n
  rw [if_neg (by simpa only [wmod_of_lt hlw] using Nat.not_lt.mpr hl)] at hc
  rw [List.append_assoc,run_append_ok hp,run_append_revert hc]

private def observed (code : List Instr) (m : Machine) : Option (List Word × List Word) :=
  match run code m with | .ok out 0 => some (cells out,out.stack) | _ => none
private theorem observed_ok {code : List Instr} {m out : Machine} (h : run code m=.ok out 0) :
    observed code m=some (cells out,out.stack) := by
  unfold observed
  rw [h]

/-- Complete actual prefix/success vectors; late error has no final word state.
The reversed word order remains materially different, not a Source rollback. -/
theorem word_vectors :
    [cells (machine 2 3),cells (wordPost 2 3 3)]=
      [[w[32],w[16],w[16],w[24],w[2],w[3],w[0],w[99],w[7],w[9],w[0],w[0],w[0],w[0],w[0],w[0]],
       [w[35],w[16],w[16],w[24],w[2],w[3],w[32],w[99],w[7],w[9],w[0],w[0],w[0],w[0],w[0],w[0]]] ∧
    observed (code 3 ++ updateCode 3) (machine 2 3)=
      some ([w[35],w[16],w[16],w[24],w[2],w[3],w[32],w[99],w[7],w[9],w[0],w[0],w[0],w[2],w[0],w[0]],[w[77]]) ∧
    observed (code 3 ++ updateCode 3 ++ clearCode 3) (machine 2 3)=
      some ([w[35],w[16],w[16],w[24],w[2],w[3],w[32],w[99],w[7],w[9],w[0],w[0],w[0],w[0],w[0],w[0]],[w[77]]) ∧
    observed (code 3 ++ clearCode 3 ++ updateCode 3) (machine 2 3)=
      some ([w[35],w[16],w[16],w[24],w[2],w[3],w[32],w[99],w[7],w[9],w[0],w[0],w[0],w[2],w[0],w[0]],[w[77]]) ∧
    run (code 3 ++ updateCode 3 ++ rejectCode 3) (machine 2 3)=.revert ∧
    observed (code 33 ++ updateCode 33) (machine 32 33)=
      some ([w[65],w[16],w[16],w[24],w[32],w[33],w[32],w[99],w[7],w[9],w[0],w[0],w[0],w[0],w[32],w[0]],[w[77]]) := by
  have hu := update_run (wordPost 2 3 3) 3 2 (by decide) (by decide) (by decide) rfl rfl
  have hc := clear_run (writeMachine (wordPost 2 3 3) 34 w[2]) 3 2 (by decide) (by decide) (by decide) rfl rfl
  have hc0 := clear_run (wordPost 2 3 3) 3 2 (by decide) (by decide) (by decide) rfl rfl
  have hu0 := update_run (writeMachine (wordPost 2 3 3) 34 w[0]) 3 2 (by decide) (by decide) (by decide) rfl rfl
  have hb := reject_run (writeMachine (wordPost 2 3 3) 34 w[2]) 3 3 (by decide) (by decide) rfl rfl
  have hu33 := update_run (wordPost 32 33 33) 33 32 (by decide) (by decide) (by decide) rfl rfl
  have hru : run (code 3 ++ updateCode 3) (machine 2 3)=.ok (writeMachine (wordPost 2 3 3) 34 w[2]) 0 := by
    rw [run_append_ok (word_run 2 3 3)];exact hu
  have hruc : run (code 3 ++ updateCode 3 ++ clearCode 3) (machine 2 3)=.ok (writeMachine (writeMachine (wordPost 2 3 3) 34 w[2]) 34 w[0]) 0 := by
    rw [run_append_ok hru];exact hc
  have hrc : run (code 3 ++ clearCode 3) (machine 2 3)=.ok (writeMachine (wordPost 2 3 3) 34 w[0]) 0 := by
    rw [run_append_ok (word_run 2 3 3)];exact hc0
  have hrcu : run (code 3 ++ clearCode 3 ++ updateCode 3) (machine 2 3)=.ok (writeMachine (writeMachine (wordPost 2 3 3) 34 w[0]) 34 w[2]) 0 := by
    rw [run_append_ok hrc];exact hu0
  have hr33 : run (code 33 ++ updateCode 33) (machine 32 33)=.ok (writeMachine (wordPost 32 33 33) 64 w[32]) 0 := by
    rw [run_append_ok (word_run 32 33 33)];exact hu33
  rw [observed_ok hru,observed_ok hruc,observed_ok hrcu,run_append_ok hru,hb,observed_ok hr33]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- RAW zero-length kernel syntax allocates then rejects its first index.
This is not Source zero-length type admission or a successful suffix. -/
theorem raw_zero (p : Roadmap.Pipeline) :
    (Source.execItems (Source.SemanticsExamples.G0 p) F0 7 Γ.length none (sourceUintFixedProgram 0 si si) (sy 0 0).1).run (.nil,(sy 0 0).2)=
      (.error (.revert (Source.panicData .index)),(.nil,(post 0 0 0).2)) ∧
    (post 0 0 0).2.heap.get 2=some ⟨.array .memory (.int .u256) (some 0),sourceUintFixedZero 0⟩ ∧
    run (code 0) (machine 0 0)=.ok (wordPost 0 0 0) 0 ∧
    (wordPost 0 0 0).mem 0=w[33] ∧
    run (code 0 ++ updateCode 0 ++ clearCode 0) (machine 0 0)=.revert := by
  have he0 : sourceUintFixedObject (D := E0.layout) ((g 0).heap.get (fresh 0))=sourceUintFixedZero 0 :=
    sourceUintFixedObject_zero _ (List.eq_nil_of_length_eq_zero ((g 0).heap.get (fresh 0)).2)
  have hr : SourceUintFixedAt (post 0 0 0) 2 (g 0).heap (fresh 0) := by
    unfold SourceUintFixedAt
    rw [he0]
    exact Source.Heap.alloc_get _ _
  let z0 : Source.EMState E0 Γ := ((sy 0 0).1,(post 0 0 0).2)
  have hz : (Source.zeroVal (E := E0) (Γ := Γ) 5 (.array .memory (.int .u256) (some 0))).run (sy 0 0)=
      (.ok (.memRef rfl 2),z0) := source_uint_fixed_zeroVal_slack (sy 0 0) 0 2
  have hd := source_decl_statement_run (Source.SemanticsExamples.G0 p) F0 5 Γ.length (sy 0 0) z0 (.memRef rfl 2) hz
  have he := hr.eval_assign_bounds (Source.SemanticsExamples.G0 p) F0 1 .here (.there si) (.there si)
    (u 0) (u 0) rfl rfl rfl (by decide)
  have hs := source_expr_statement_error (Source.SemanticsExamples.G0 p) F0 4 Γ.length
    (sourceUintFixedIndexedAssign .here (.there si) (.there si)) (post 0 0 0) (post 0 0 0) _ he
  have hu := update_reject (wordPost 0 0 0) 0 0 (by decide) (by decide) rfl rfl
  refine ⟨?_,rfl,word_run 0 0 0,rfl,?_⟩
  · rw [sourceUintFixedProgram,Source.execItems,Source.Hoare.run_bind,hd]
    have htail : (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 Γ.length none
        (.stmt (.expr (sourceUintFixedIndexedAssign .here (.there si) (.there si)))
          (.stmt (.expr (sourceUintFixedIndexedDelete .here (.there si))) .nil) : Source.RItems E0 [] false .body ((.array .memory (.int .u256) (some 0))::Γ) ((.array .memory (.int .u256) (some 0))::Γ)) (post 0 0 0).1).run (.nil,(post 0 0 0).2)=
        (.error (.revert (Source.panicData .index)),(.nil,(post 0 0 0).2)) := by
      rw [Source.execItems,Source.Hoare.run_bind,hs]
    change (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 Γ.length none
      (.stmt (.expr (sourceUintFixedIndexedAssign .here (.there si) (.there si)))
        (.stmt (.expr (sourceUintFixedIndexedDelete .here (.there si))) .nil) : Source.RItems E0 [] false .body ((.array .memory (.int .u256) (some 0))::Γ) ((.array .memory (.int .u256) (some 0))::Γ)) (post 0 0 0).1 >>=
      fun o => Source.EM.lift (o.up Γ)).run (.nil,(post 0 0 0).2)=_
    rw [Source.Hoare.run_bind,htail]
  · rw [List.append_assoc,run_append_ok (word_run 0 0 0),run_append_revert hu]

/-- Direct finite cases retain actual program executions and the independently
observed last element, not merely an existential representation certificate. -/
theorem selected_cases (p : Roadmap.Pipeline) (n k : Nat)
    (hcase : (n=1 ∧ k=0) ∨ (n=3 ∧ k=2) ∨ (n=33 ∧ k=32)) :
    ∃ (out : Heap (g n).H') (z : Source.EMState E0 ((.array .memory (.int .u256) (some n))::Γ)),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 (n+7) Γ.length none (sourceUintFixedProgram n si si) (sy k n).1).run (.nil,(sy k n).2)=
        (.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run (state k n) (intrinsicUintFixedProgram n (.there .here) (.there .here))=
        .ok ⟨(grownState k n n).withHeap out,(g n).ext⟩ ∧
      (Source.memElem (E := E0) (Γ := (.array .memory (.int .u256) (some n))::Γ) 2 k (.int .u256)).run z=
        (.ok (sourceUint (PrimTy.dflt .uint)),z) ∧
      [(out.get (fresh n)).1,(out.get (left.wk (g n).ext)).1,(out.get (right.wk (g n).ext)).1]=
        [List.replicate n (PrimTy.dflt .uint),[u 7],[u 9]] := by
  have hn : 0<n := by rcases hcase with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  have hk : k<n := by rcases hcase with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  have hs : 32+max 1 n<W := by rcases hcase with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  obtain ⟨_,_,_,_,out1,out,z1,z,hd,he1,he2,hitems,hprog,hr1,hr2,hvals,hold,_⟩ := program_runs p n k n hn hk hs
  have hv : (out.get (fresh n)).1=List.replicate n (PrimTy.dflt .uint) := (List.cons.inj (List.cons.inj hvals).2).1
  refine ⟨out,z,hitems,hprog,?_,?_⟩
  · simpa only [hv,List.getElem_replicate] using hr2.read k hk
  · rw [hv]
    exact congrArg (List.cons (List.replicate n (PrimTy.dflt .uint))) hold

/-- Material prefix retained at a late failure: error globals contain2 rather
than initial0 or a cleared suffix, while old child/neighbor remain7/9. -/
theorem changed_prefix_panic (p : Roadmap.Pipeline) :
    ∃ (out : Heap (g 3).H') (z : Source.EMState E0 ((.array .memory (.int .u256) (some 3))::Γ)),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 10 Γ.length none (sourceUintFixedRejectProgram 3 si si sj) (sy 2 3).1).run (.nil,(sy 2 3).2)=
        (.error (.revert (Source.panicData .index)),(.nil,z.2)) ∧
      Prog.run (state 2 3) (intrinsicUintFixedRejectProgram 3 (.there .here) (.there .here) .here)=.error .revert ∧
      (Source.memElem (E := E0) (Γ := (.array .memory (.int .u256) (some 3))::Γ) 2 2 (.int .u256)).run z=
        (.ok (sourceUint (u 2)),z) ∧
      (out.get (fresh 3)).1=[u 0,u 0,u 2] ∧
      [z.2.heap.get 0,z.2.heap.get 1]=[(sy 2 3).2.heap.get 0,(sy 2 3).2.heap.get 1] := by
  obtain ⟨_,_,_,out,z,hd,hs,hitems,hprog,hv,hr,hold,hsrc,_⟩ := late_rejection p 3 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨out,z,hitems,hprog,?_,hv,hsrc⟩
  simpa only [hv,List.getElem_set,↓reduceIte] using hr.read 2 (by decide)

/-- Insufficient horizon executes declaration and materially writes7, then
Source delete times out. Only actual Source error globals are retained. -/
theorem changed_prefix_timeout (p : Roadmap.Pipeline) :
    ∃ (out : Heap (g 1).H') (z : Source.EMState E0 ((.array .memory (.int .u256) (some 1))::Γ)),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 Γ.length none (sourceUintFixedProgram 1 si sj) (sy 0 7).1).run (.nil,(sy 0 7).2)=
        (.error .timeout,(.nil,z.2)) ∧
      SourceUintFixedAt z 2 out (fresh 1) ∧
      (Source.memElem (E := E0) (Γ := (.array .memory (.int .u256) (some 1))::Γ) 2 0 (.int .u256)).run z=
        (.ok (sourceUint (u 7)),z) ∧
      [z.2.heap.get 0,z.2.heap.get 1]=[(sy 0 7).2.heap.get 0,(sy 0 7).2.heap.get 1] := by
  have hr : SourceUintFixedAt (post 0 7 1) 2 (g 1).heap (fresh 1) :=
    (source_uint_fixed_declaration (Source.SemanticsExamples.G0 p) F0 (sy 0 7) hp 1 (by decide) SH (source_memOK 0 7)).2.1
  let z0 : Source.EMState E0 Γ := ((sy 0 7).1,(post 0 7 1).2)
  have hz : (Source.zeroVal (E := E0) (Γ := Γ) 4 (.array .memory (.int .u256) (some 1))).run (sy 0 7)=
      (.ok (.memRef rfl 2),z0) := source_uint_fixed_zeroVal (sy 0 7) 1
  have hd := source_decl_statement_run (Source.SemanticsExamples.G0 p) F0 4 Γ.length (sy 0 7) z0 (.memRef rfl 2) hz
  obtain ⟨out,z,hw,hs,hr'⟩ := hr.write_addr F0 2 (u 0) (u 7) (by decide)
  have he := hr.eval_assign_of_run (Source.SemanticsExamples.G0 p) F0 0 .here (.there si) (.there sj)
    (u 0) (u 7) rfl rfl rfl (by decide) hs
  have hsw := source_expr_statement_run (Source.SemanticsExamples.G0 p) F0 3 Γ.length _ (post 0 7 1) z (.val (sourceUint (u 7))) he
  have htimeout : (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (sourceUintFixedIndexedDelete .here (.there si))).run z=(.error .timeout,z) := rfl
  have hsd := source_expr_statement_error (Source.SemanticsExamples.G0 p) F0 2 Γ.length _ z z .timeout htimeout
  have hf := hr.write_frames F0 2 (u 0) (u 7) (by decide) hw hs
  have hv : (out.get (fresh 1)).1=[u 7] := by
    have ho : out=(g 1).heap.set (fresh 1) (MObj.setElem .fixed ((g 1).heap.get (fresh 1)) 0 (u 7)) := by
      simpa only [Heap.writeAddr,Heap.setIndex,MObj.elems_fixed,((g 1).heap.get (fresh 1)).2,
        show (u 0).1.toNat=0 from rfl,if_pos (by decide : 0<1),Option.some.injEq] using hw.symm
    rw [ho,Heap.get_set_same,MObj.setElem_fixed]
    have hz' : ((g 1).heap.get (fresh 1)).1=[PrimTy.dflt .uint] := by
      simpa only [MObj.elems_fixed,List.replicate_succ,List.replicate_zero] using (source_uint_fixed_intrinsic (sy 0 7) hp 1 (by decide)).2.1
    change ((g 1).heap.get (fresh 1)).1.set 0 (u 7)=_
    rw [hz'];rfl
  refine ⟨out,z,?_,hr',?_,?_⟩
  · have hlast : (Source.execItems (Source.SemanticsExamples.G0 p) F0 4 Γ.length none
        (.stmt (.expr (sourceUintFixedIndexedDelete .here (.there si))) .nil : Source.RItems E0 [] false .body ((.array .memory (.int .u256) (some 1))::Γ) ((.array .memory (.int .u256) (some 1))::Γ)) z.1).run (.nil,z.2)=
        (.error .timeout,(.nil,z.2)) := by
      rw [Source.execItems,Source.Hoare.run_bind,hsd]
    have htail : (Source.execItems (Source.SemanticsExamples.G0 p) F0 5 Γ.length none
        (.stmt (.expr (sourceUintFixedIndexedAssign .here (.there si) (.there sj)))
          (.stmt (.expr (sourceUintFixedIndexedDelete .here (.there si))) .nil) : Source.RItems E0 [] false .body ((.array .memory (.int .u256) (some 1))::Γ) ((.array .memory (.int .u256) (some 1))::Γ)) (post 0 7 1).1).run (.nil,(post 0 7 1).2)=
        (.error .timeout,(.nil,z.2)) := by
      rw [Source.execItems,Source.Hoare.run_bind,hsw]
      change (Source.execItems (Source.SemanticsExamples.G0 p) F0 4 Γ.length none
        (.stmt (.expr (sourceUintFixedIndexedDelete .here (.there si))) .nil : Source.RItems E0 [] false .body ((.array .memory (.int .u256) (some 1))::Γ) ((.array .memory (.int .u256) (some 1))::Γ)) z.1 >>=
        fun o => Source.EM.lift (o.up ((.array .memory (.int .u256) (some 1))::Γ))).run (.nil,z.2)=_
      rw [Source.Hoare.run_bind,hlast]
    rw [sourceUintFixedProgram,Source.execItems,Source.Hoare.run_bind,hd]
    change (Source.execItems (Source.SemanticsExamples.G0 p) F0 5 Γ.length none
      (.stmt (.expr (sourceUintFixedIndexedAssign .here (.there si) (.there sj)))
        (.stmt (.expr (sourceUintFixedIndexedDelete .here (.there si))) .nil) : Source.RItems E0 [] false .body ((.array .memory (.int .u256) (some 1))::Γ) ((.array .memory (.int .u256) (some 1))::Γ)) (post 0 7 1).1 >>=
      fun o => Source.EM.lift (o.up Γ)).run (.nil,(post 0 7 1).2)=_
    rw [Source.Hoare.run_bind,htail]
  · simpa only [hv,List.getElem_cons_zero] using hr'.read 0 (by decide)
  · rw [hf.2.2.1 0 (by decide),hf.2.2.1 1 (by decide)]
    rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedProgramControls.initial_views' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial_views
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedProgramControls.program_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms program_runs
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedProgramControls.late_rejection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms late_rejection
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedProgramControls.word_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_vectors
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedProgramControls.raw_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_zero
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedProgramControls.selected_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected_cases
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedProgramControls.changed_prefix_panic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms changed_prefix_panic
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedProgramControls.changed_prefix_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms changed_prefix_timeout
end Solidity.Backend.MemoryOps.SourceUintFixedProgramControls
