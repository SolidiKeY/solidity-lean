import Solidity.Backend.MemoryOps.SourceUintFixedMutationSequence
import Solidity.Backend.MemoryOps.SourceUintFixedDefaultControls
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceUintFixedMutationControls
open Evm Evm.Memory
open Source.SemanticsExamples (E0 F0 s0)
private def C : Contract := {vars := []}
private abbrev A : RefTy := .fixed (.prim .uint) 1
private abbrev H : HTy := [A,A]
private abbrev Δ : Ctx := [.val .uint,.mem A,.mem A,.mem A]
private abbrev SA := Source.STy.array .memory (.int .u256) (some 1)
private abbrev Γ : Source.RCtx := [.int .u256,SA,SA,SA]
private def u (v : Nat) : PrimTy.uint.Denote := indexValue (wmod v)
private def left : HRef H A := ⟨0,rfl⟩
private def right : HRef H A := ⟨1,rfl⟩
private def hp : Heap H := (⟨[u 7],by decide⟩,⟨[u 9],by decide⟩,())
private def state (k : Nat) : State C Δ := {storage := Storage.init C,H := H,heap := hp,env := (u k,some right,some left,some left,())}
private def base (i : Nat) : Fin W := if i=0 then wmod 16 else wmod 24
private def machine (k : Nat) : Machine := {Machine.init with stack := [w[77]],mem := fun a =>
  if a=0 then w[32] else if a=1 then w[16] else if a=2 then w[16] else if a=3 then w[24]
  else if a=4 then (Word.val (wmod k)) else if a=15 then w[99] else if a=16 then w[7] else if a=24 then w[9] else w[0]}
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
private theorem heap_repr (k : Nat) : Objects.HeapRepr hp base 8 (machine k) := by
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
private theorem initial_repr (k : Nat) : Objects.StateRepr 1 1 8 (Frag.init Δ) (state k) base (machine k) := by
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨?_,heap_repr k,?_,by decide⟩
  · refine ⟨hc.store,?_,?_,hc.net,hc.netSelf,hc.bound,?_,hc.env,hc.funds,hc.oracle⟩
    · intro p i
      cases i with
      | here => exact ReprV.uint_of rfl
      | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro R i hi
      cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro R i hi
      cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
  · intro R i
    cases i with
    | there i => cases i with
      | here => exact ⟨right,rfl,rfl⟩
      | there i => cases i with
        | here => exact ⟨left,rfl,rfl⟩
        | there i => cases i with
          | here => exact ⟨left,rfl,rfl⟩
          | there i => nomatch i
private theorem initial_allocator (k : Nat) : Objects.AllocatorRepr hp base 8 ⟨32,by decide⟩ (machine k) := by
  refine ⟨heap_repr k,⟨by decide,by decide,rfl,?_⟩,?_⟩
  · intro a ha
    change 32≤a at ha
    simp only [machine,if_neg (show a≠0 by omega),if_neg (show a≠1 by omega),if_neg (show a≠2 by omega),
      if_neg (show a≠3 by omega),if_neg (show a≠4 by omega),if_neg (show a≠15 by omega),if_neg (show a≠16 by omega),if_neg (show a≠24 by omega)]
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
private def sy (k : Nat) : Source.EMState E0 Γ :=
  (.cons (sourceUint (u k)) (.cons (.memRef rfl 1) (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil))),y2.2)
private abbrev SH := (Source.Heap.empty (D := E0.layout)).ty
private def si : Source.Idx Γ (.int .u256) := .here
private def sr : Source.Idx Γ SA := .there (.there .here)
private def salias : Source.Idx Γ SA := .there (.there (.there .here))
private theorem represented_left (k : Nat) : SourceUintFixedAt (sy k) 0 hp left := by
  unfold SourceUintFixedAt
  change (sy k).2.heap.get 0=some ⟨SA,sourceUintFixedObject (D := E0.layout) (⟨[u 7],by decide⟩ : MObj H A)⟩
  rw [one_conversion];rfl
private theorem represented_right (k : Nat) : SourceUintFixedAt (sy k) 1 hp right := by
  unfold SourceUintFixedAt
  change (sy k).2.heap.get 1=some ⟨SA,sourceUintFixedObject (D := E0.layout) (⟨[u 9],by decide⟩ : MObj H A)⟩
  rw [one_conversion];rfl
private theorem source_memOK (k : Nat) : Source.MemOK E0 SH (sy k) := by
  have h0 : Source.MemOK E0 SH y0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have h1 := source_uint_fixed_alloc_memOK (E := E0) (Γ := []) SH (⟨[u 7],by decide⟩ : MObj H A) y0 h0
  rw [one_conversion] at h1
  change Source.MemOK E0 SH y1 ∧ _ at h1
  have h2 := source_uint_fixed_alloc_memOK (E := E0) (Γ := []) SH (⟨[u 9],by decide⟩ : MObj H A) y1 h1.1
  rw [one_conversion] at h2
  change Source.MemOK E0 SH y2 ∧ _ at h2
  exact ⟨⟨h2.1.1.1,⟨trivial,⟨⟨SA,rfl,rfl⟩,⟨⟨SA,rfl,rfl⟩,⟨⟨SA,rfl,rfl⟩,trivial⟩⟩⟩⟩⟩,h2.1.2⟩

private def g (n : Nat) := hp.allocDefault (.fixed (.prim .uint) n) rfl
private def fresh (n : Nat) := (g n).val
private def grownState (k : Nat) (n : Nat) := ((state k).adopt (g n)).1.push (t := .mem (.fixed (.prim .uint) n)) (some (fresh n))
private def post (k : Nat) (n : Nat) : Source.EMState E0 ((.array .memory (.int .u256) (some n))::Γ) :=
  (.cons (.memRef rfl 2) (sy k).1,{(sy k).2 with heap := ((sy k).2.heap.alloc ⟨.array .memory (.int .u256) (some n),sourceUintFixedZero n⟩).1})
private def wordPost (k : Nat) (n : Nat) := writeMachine (allocateStructMachine (machine k) ⟨32,by decide⟩ (max 1 n)) 5 w[32]
private def code (n : Nat) := Objects.defaultDeclareCode (Γ := Δ) (Objects.DefaultBuilder.fixedPrimitive .uint n).code 1
private def cells (m : Machine) := [m.mem 0,m.mem 1,m.mem 2,m.mem 3,m.mem 4,m.mem 5,m.mem 7,m.mem 15,
  m.mem 16,m.mem 24,m.mem 31,m.mem 32,m.mem 33,m.mem 34,m.mem 35,m.mem 40]
private theorem word_run (k : Nat) (n : Nat) : run (code n) (machine k)=.ok ((wordPost k) n) 0 := by
  change run (allocateStructCode (max 1 n) ++ [.mstore 5]) (machine k)=_
  rw [run_append_ok (allocateStruct_run (machine k) ⟨32,by decide⟩ (max 1 n) rfl)]
  rfl


/-- Actual constructor followed by reached indexed mutation/deletion. The same
initial numeric local supplies the index and value, so length33/index32 is a
material32 write; length1/index0 remains the discriminating fixed endpoint case. -/
theorem reached_operations (p : Roadmap.Pipeline) (n k : Nat) (hn : 0<n) (hk : k<n)
    (hs : 32+max 1 n<W) :
    ∃ (base' : Nat → Fin W) (target0 target1 target2 : Machine) (out1 out2 : Heap (g n).H') (z1 z2 : Source.EMState E0 ((.array .memory (.int .u256) (some n))::Γ)),
      (Source.execS (Source.SemanticsExamples.G0 p) F0 (n+4) Γ.length none
        (.declVar (.array .memory (.int .u256) (some n)) : Source.RStmt E0 [] false .body Γ ((.array .memory (.int .u256) (some n))::Γ)) (sy k).1).run (.nil,(sy k).2)=
          (.ok (.normal (post k n).1),(.nil,(post k n).2)) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3
        (sourceUintFixedIndexedAssign .here (.there si) (.there si))).run (post k n)=
          (.ok (.val (sourceUint (u k))),z1) ∧
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3
        (sourceUintFixedIndexedDelete .here (.there si))).run z1=(.ok Source.RVal.unit,z2) ∧
      SourceUintFixedAt z1 2 out1 (fresh n) ∧ SourceUintFixedAt z2 2 out2 (fresh n) ∧
      [(out1.get (fresh n)).1,(out2.get (fresh n)).1]=
        [(List.replicate n (PrimTy.dflt .uint)).set k (u k),List.replicate n (PrimTy.dflt .uint)] ∧
      [out2.get (left.wk (g n).ext) |>.1,out2.get (right.wk (g n).ext) |>.1]=[[u 7],[u 9]] ∧
      [z1.2.heap.get 0,z1.2.heap.get 1,z2.2.heap.get 0,z2.2.heap.get 1]=
        [(sy k).2.heap.get 0,(sy k).2.heap.get 1,(sy k).2.heap.get 0,(sy k).2.heap.get 1] ∧
      SourceUintFixedAt z2 0 out2 (left.wk (g n).ext) ∧
      run (code n) (machine k)=.ok target0 0 ∧
      Objects.StateRepr 1 1 8 ((Frag.init Δ).push (.mem (.fixed (.prim .uint) n)) .ok)
        ((grownState k n).withHeap out2) base' target2 ∧
      Objects.AllocatorRepr out2 base' 8 ⟨32+max 1 n,hs⟩ target2 ∧
      Source.MemOK E0 SH z1 ∧ Source.MemOK E0 SH z2 ∧
      z1.1=(post k n).1 ∧ z2.1=(post k n).1 ∧
      [target0.stack,target1.stack,target2.stack]=[[w[77]],[w[77]],[w[77]]] := by
  have hkw : k<W := by omega
  have hki : (u k).1.toNat=k := by change (wmod k).val=k;exact Nat.mod_eq_of_lt hkw
  obtain ⟨base',target0,target1,target2,out1,out2,z1,z2,hd,hstmt1,hstmt2,hw1,hw2,hr0,hr1,hr2,hc0,hc1,hc2,hwhole,hm2,ha2,hmok1,hmok2,hl1,hl2,hstack2,hs1,hs2,he1,he2,hstack0,hstack1,hother,hsource⟩ :=
    source_uint_fixed_declare_write_delete (Source.SemanticsExamples.G0 p) F0 (sy k) (state k) n hn si si .here .here
      (u k) (u k) rfl rfl rfl rfl (by rw [hki];exact hk) SH (source_memOK k)
      (initial_repr k) (initial_allocator k) (by decide) hs (by decide)
  change (g n).heap.writeAddr (.index (fresh n) .fixed (u k)) (u k)=some out1 at hw1
  change out1.writeAddr (.index (fresh n) .fixed (u k)) (PrimTy.dflt .uint)=some out2 at hw2
  have ho1 : out1=(g n).heap.set (fresh n) (MObj.setElem .fixed ((g n).heap.get (fresh n)) k (u k)) := by
    simpa only [Heap.writeAddr,Heap.setIndex,MObj.elems_fixed,hki,((g n).heap.get (fresh n)).2,if_pos hk,Option.some.injEq] using hw1.symm
  have ho2 : out2=out1.set (fresh n) (MObj.setElem .fixed (out1.get (fresh n)) k (PrimTy.dflt .uint)) := by
    simpa only [Heap.writeAddr,Heap.setIndex,MObj.elems_fixed,hki,(out1.get (fresh n)).2,if_pos hk,Option.some.injEq] using hw2.symm
  have hz0 := (source_uint_fixed_intrinsic (sy k) hp n hn).2.1
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
  have hk0 : Heap.Keeps (g n).ext hp (g n).heap := (source_uint_fixed_intrinsic (sy k) hp n hn).2.2.1
  change ∀ address,address≠2 → z2.2.heap.get address=(post k n).2.heap.get address at hsource
  have hf1 := hr0.write_frames F0 2 (u k) (u k) (by rw [hki];exact hk) hw1 hs1
  have hleft : SourceUintFixedAt z2 0 out2 (left.wk (g n).ext) := by
    unfold SourceUintFixedAt
    rw [hsource 0 (by decide),hother left]
    change (post k n).2.heap.get 0=some ⟨SA,sourceUintFixedObject ((g n).heap.get (left.wk (g n).ext))⟩
    rw [hk0 left]
    change (post k n).2.heap.get 0=some _
    change ((sy k).2.heap.alloc ⟨.array .memory (.int .u256) (some n),sourceUintFixedZero n⟩).1.get 0=_
    rw [Source.Heap.alloc_other _ _ (by change (0 : Nat)≠2;decide)]
    exact represented_left k
  refine ⟨base',target0,target1,target2,out1,out2,z1,z2,hd,he1,he2,hr1,hr2,by rw [hv1,hv2],?_,?_,hleft,hc0,hm2,ha2,hmok1,hmok2,hl1,hl2,?_⟩
  · rw [hother left,hother right]
    change [((g n).heap.get (left.wk (g n).ext)).1,((g n).heap.get (right.wk (g n).ext)).1]=_
    rw [hk0 left,hk0 right]
    rfl
  · rw [hf1.2.2.1 0 (by change (0 : Nat)≠2;decide),hf1.2.2.1 1 (by change (1 : Nat)≠2;decide),hsource 0 (by decide),hsource 1 (by decide)]
    rfl
  · rw [hstack0,hstack1,hstack2]
    rfl

private def updateCode (n : Nat) : List Instr :=
  Evm.compileVal 1 (.simple (.local (.there (.here : Idx Δ (.val .uint)))) : Val C (.mem (.fixed (.prim .uint) n)::Δ) .uint) ++
    [.mload (Evm.cellOf 1 (.here : Idx (.mem (.fixed (.prim .uint) n)::Δ) (.mem (.fixed (.prim .uint) n))))] ++
    Evm.compileVal 1 (.simple (.local (.there (.here : Idx Δ (.val .uint)))) : Val C (.mem (.fixed (.prim .uint) n)::Δ) .uint) ++
    Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))
private def clearCode (n : Nat) : List Instr :=
  Evm.compileVal 1 (Evm.Memory.deleteDefaultValue .uint : Val C (.mem (.fixed (.prim .uint) n)::Δ) .uint) ++
    [.mload (Evm.cellOf 1 (.here : Idx (.mem (.fixed (.prim .uint) n)::Δ) (.mem (.fixed (.prim .uint) n))))] ++
    Evm.compileVal 1 (.simple (.local (.there (.here : Idx Δ (.val .uint)))) : Val C (.mem (.fixed (.prim .uint) n)::Δ) .uint) ++
    Objects.writeCode (.fixed : ArrTy (.fixed (.prim .uint) n) (.prim .uint))
private def observed (code : List Instr) (m : Machine) : Option (List Word × List Word) :=
  match run code m with
  | .ok out 0 => some (cells out,out.stack)
  | _ => none

private theorem update_run (m : Machine) (n k : Nat) (hk : k<n) (hkw : k<W) (ha : 32+k<W)
    (h4 : m.mem 4=Word.val (wmod k)) (h5 : m.mem 5=w[32]) :
    run (updateCode n) m=.ok (writeMachine m (32+k) (.val (wmod k))) 0 := by
  change run ([.mload 4,.mload 5,.mload 4] ++ Objects.fixedAddrCode n ++ [.mstoreAt]) m=_
  have hp : run [.mload 4,.mload 5,.mload 4] m=
      .ok (((m.push (.val (wmod k))).push w[32]).push (.val (wmod k))) 0 := by
    simp only [run,exec_cons_zero,Instr.step,Machine.next,Machine.push,Out.ok_bind,exec_nil,h4,h5]
  have hc := Objects.fixedAddr_run (m.push (.val (wmod k))) ⟨32,by decide⟩ (wmod k) n
  rw [if_pos (by simpa only [wmod_of_lt hkw] using hk)] at hc
  rw [List.append_assoc,run_append_ok hp,run_append_ok hc]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,Out.ok_bind,exec_nil,
    wmod_of_lt hkw,wmod_of_lt ha,writeMachine]

private theorem clear_run (m : Machine) (n k : Nat) (hk : k<n) (hkw : k<W) (ha : 32+k<W)
    (h4 : m.mem 4=Word.val (wmod k)) (h5 : m.mem 5=w[32]) :
    run (clearCode n) m=.ok (writeMachine m (32+k) w[0]) 0 := by
  change run ([.push w[0],.mload 5,.mload 4] ++ Objects.fixedAddrCode n ++ [.mstoreAt]) m=_
  have hp : run [.push w[0],.mload 5,.mload 4] m=
      .ok (((m.push w[0]).push w[32]).push (.val (wmod k))) 0 := by
    simp only [run,exec_cons_zero,Instr.step,Machine.next,Machine.push,Out.ok_bind,exec_nil,h4,h5]
  have hc := Objects.fixedAddr_run (m.push w[0]) ⟨32,by decide⟩ (wmod k) n
  rw [if_pos (by simpa only [wmod_of_lt hkw] using hk)] at hc
  rw [List.append_assoc,run_append_ok hp,run_append_ok hc]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,Out.ok_bind,exec_nil,
    wmod_of_lt hkw,wmod_of_lt ha,writeMachine]

private theorem update_reject (m : Machine) (n k : Nat) (hk : n≤k) (hkw : k<W)
    (h4 : m.mem 4=Word.val (wmod k)) (h5 : m.mem 5=w[32]) : run (updateCode n) m=.revert := by
  change run ([.mload 4,.mload 5,.mload 4] ++ Objects.fixedAddrCode n ++ [.mstoreAt]) m=_
  have hp : run [.mload 4,.mload 5,.mload 4] m=
      .ok (((m.push (.val (wmod k))).push w[32]).push (.val (wmod k))) 0 := by
    simp only [run,exec_cons_zero,Instr.step,Machine.next,Machine.push,Out.ok_bind,exec_nil,h4,h5]
  have hc := Objects.fixedAddr_run (m.push (.val (wmod k))) ⟨32,by decide⟩ (wmod k) n
  rw [if_neg (by simpa only [wmod_of_lt hkw] using Nat.not_lt.mpr hk)] at hc
  rw [List.append_assoc,run_append_ok hp,run_append_revert hc]

private theorem observed_ok {code : List Instr} {m out : Machine} (h : run code m=.ok out 0) :
    observed code m=some (cells out,out.stack) := by
  unfold observed
  rw [h]

/-- Complete16word vectors from actual entire declaration/write/delete appends.
The last element32 is also explicitly observed separately below. -/
theorem word_vectors :
    observed (code 3 ++ updateCode 3) (machine 2)=
      some ([w[35],w[16],w[16],w[24],w[2],w[32],w[0],w[99],w[7],w[9],w[0],w[0],w[0],w[2],w[0],w[0]],[w[77]]) ∧
    observed (code 3 ++ updateCode 3 ++ clearCode 3) (machine 2)=
      some ([w[35],w[16],w[16],w[24],w[2],w[32],w[0],w[99],w[7],w[9],w[0],w[0],w[0],w[0],w[0],w[0]],[w[77]]) ∧
    observed (code 33 ++ updateCode 33 ++ clearCode 33) (machine 32)=
      some ([w[65],w[16],w[16],w[24],w[32],w[32],w[0],w[99],w[7],w[9],w[0],w[0],w[0],w[0],w[0],w[0]],[w[77]]) := by
  have h3 := update_run (wordPost 2 3) 3 2 (by decide) (by decide) (by decide) rfl rfl
  have h33 := update_run (wordPost 32 33) 33 32 (by decide) (by decide) (by decide) rfl rfl
  have hc3 := clear_run (writeMachine (wordPost 2 3) 34 w[2]) 3 2 (by decide) (by decide) (by decide) rfl rfl
  have hc33 := clear_run (writeMachine (wordPost 32 33) 64 w[32]) 33 32 (by decide) (by decide) (by decide) rfl rfl
  have h3' : run (code 3 ++ updateCode 3) (machine 2)=.ok (writeMachine (wordPost 2 3) 34 w[2]) 0 := by
    rw [run_append_ok (word_run 2 3)];exact h3
  have h3'' : run (code 3 ++ updateCode 3 ++ clearCode 3) (machine 2)=.ok (writeMachine (writeMachine (wordPost 2 3) 34 w[2]) 34 w[0]) 0 := by
    rw [run_append_ok h3'];exact hc3
  have h33' : run (code 33 ++ updateCode 33) (machine 32)=.ok (writeMachine (wordPost 32 33) 64 w[32]) 0 := by
    rw [run_append_ok (word_run 32 33)];exact h33
  have h33'' : run (code 33 ++ updateCode 33 ++ clearCode 33) (machine 32)=.ok (writeMachine (writeMachine (wordPost 32 33) 64 w[32]) 64 w[0]) 0 := by
    rw [run_append_ok h33'];exact hc33
  rw [observed_ok h3',observed_ok h3'',observed_ok h33'']
  exact ⟨rfl,rfl,rfl⟩

/-- Actual nonzero reached value followed by default zero, and exact endpoint
Source panic vs the existing word revert. No rollback or word panic payload. -/
theorem boundary_and_order (p : Roadmap.Pipeline) :
    (match run (code 33 ++ updateCode 33) (machine 32) with
      | .ok out 0 => some [out.mem 64,out.mem 16,out.mem 24,out.mem 0]
      | _ => none)=some [w[32],w[7],w[9],w[65]] ∧
    (match run (code 33 ++ updateCode 33 ++ clearCode 33) (machine 32) with
      | .ok out 0 => some [out.mem 64,out.mem 16,out.mem 24,out.mem 0]
      | _ => none)=some [w[0],w[7],w[9],w[65]] ∧
    (match run (code 33 ++ clearCode 33 ++ updateCode 33) (machine 32) with
      | .ok out 0 => some (out.mem 64)
      | _ => none)=some w[32] ∧
    run (code 33 ++ updateCode 33) (machine 33)=.revert ∧
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 3
      (sourceUintFixedIndexedAssign .here (.there si) (.there si))).run (post 33 33)=
        (.error (.revert (Source.panicData .index)),post 33 33) := by
  have hu := update_run (wordPost 32 33) 33 32 (by decide) (by decide) (by decide) rfl rfl
  have hc := clear_run (writeMachine (wordPost 32 33) 64 w[32]) 33 32 (by decide) (by decide) (by decide) rfl rfl
  have hc0 := clear_run (wordPost 32 33) 33 32 (by decide) (by decide) (by decide) rfl rfl
  have hu0 := update_run (writeMachine (wordPost 32 33) 64 w[0]) 33 32 (by decide) (by decide) (by decide) rfl rfl
  have hb := update_reject (wordPost 33 33) 33 33 (by decide) (by decide) rfl rfl
  have hru : run (code 33 ++ updateCode 33) (machine 32)=.ok (writeMachine (wordPost 32 33) 64 w[32]) 0 := by
    rw [run_append_ok (word_run 32 33)];exact hu
  have hruc : run (code 33 ++ updateCode 33 ++ clearCode 33) (machine 32)=.ok (writeMachine (writeMachine (wordPost 32 33) 64 w[32]) 64 w[0]) 0 := by
    rw [run_append_ok hru];exact hc
  have hrc : run (code 33 ++ clearCode 33) (machine 32)=.ok (writeMachine (wordPost 32 33) 64 w[0]) 0 := by
    rw [run_append_ok (word_run 32 33)];exact hc0
  have hrcu : run (code 33 ++ clearCode 33 ++ updateCode 33) (machine 32)=.ok (writeMachine (writeMachine (wordPost 32 33) 64 w[0]) 64 w[32]) 0 := by
    rw [run_append_ok hrc];exact hu0
  rw [hru,hruc,hrcu,run_append_ok (word_run 33 33),hb]
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  have hr : SourceUintFixedAt (post 33 33) 2 (g 33).heap (fresh 33) :=
    (source_uint_fixed_declaration (Source.SemanticsExamples.G0 p) F0 (sy 33) hp 33 (by decide) SH (source_memOK 33)).2.1
  exact hr.eval_assign_bounds
    (Source.SemanticsExamples.G0 p) F0 0 .here (.there si) (.there si) (u 33) (u 33) rfl rfl rfl (by decide)

/-- Directly instantiate the general reached producer at positive lengths1/3/33. -/
theorem positive_instances (p : Roadmap.Pipeline) :
    (∃ (out1 out2 : Heap (g 1).H') (z1 z2 : Source.EMState E0 ((.array .memory (.int .u256) (some 1))::Γ)),
      SourceUintFixedAt z1 2 out1 (fresh 1) ∧ SourceUintFixedAt z2 2 out2 (fresh 1)) ∧
    (∃ (out1 out2 : Heap (g 3).H') (z1 z2 : Source.EMState E0 ((.array .memory (.int .u256) (some 3))::Γ)),
      SourceUintFixedAt z1 2 out1 (fresh 3) ∧ SourceUintFixedAt z2 2 out2 (fresh 3)) ∧
    (∃ (out1 out2 : Heap (g 33).H') (z1 z2 : Source.EMState E0 ((.array .memory (.int .u256) (some 33))::Γ)),
      SourceUintFixedAt z1 2 out1 (fresh 33) ∧ SourceUintFixedAt z2 2 out2 (fresh 33)) := by
  constructor
  · obtain ⟨_,_,_,_,a,b,x,y,_,_,_,ha,hb,_⟩ := reached_operations p 1 0 (by decide) (by decide) (by decide)
    exact ⟨a,b,x,y,ha,hb⟩
  · constructor
    · obtain ⟨_,_,_,_,a,b,x,y,_,_,_,ha,hb,_⟩ := reached_operations p 3 2 (by decide) (by decide) (by decide)
      exact ⟨a,b,x,y,ha,hb⟩
    · obtain ⟨_,_,_,_,a,b,x,y,_,_,_,ha,hb,_⟩ := reached_operations p 33 32 (by decide) (by decide) (by decide)
      exact ⟨a,b,x,y,ha,hb⟩

/-- Endpoint deletion uses actual constructor output and the existing typed word
certificate, not an assumed empty suffix machine. -/
theorem endpoint_delete (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 3
      (sourceUintFixedIndexedDelete .here (.there si))).run (post 33 33)=
        (.error (.revert (Source.panicData .index)),post 33 33) ∧
    TRun.deleteMem (.loc (.index .fixed (.var (.here : Idx (.mem (.fixed (.prim .uint) 33)::Δ) (.mem (.fixed (.prim .uint) 33))) rfl)
      (.simple (.local (.there (.here : Idx Δ (.val .uint))))))) (grownState 33 33)=.error .revert ∧
    run (code 33 ++ clearCode 33) (machine 33)=.revert := by
  obtain ⟨base',target,hd,ht,hc,hr,hmok,hm,ha,hbase,hstack,hid,hne,hsource⟩ :=
    source_uint_fixed_declaration_word (Source.SemanticsExamples.G0 p) F0 (sy 33) (state 33) 33 (by decide)
      SH (source_memOK 33) (initial_repr 33) (initial_allocator 33) (by decide) (by decide) (by decide)
  have hb := resolved_uint_fixed_delete_word_bounds (Source.SemanticsExamples.G0 p) F0 0 (grownState 33 33)
    (fresh 33) hr .here (.there si) .here (.there (.here : Idx Δ (.val .uint))) (u 33) rfl rfl rfl rfl (by decide) hm
  refine ⟨hb.1,?_,?_⟩
  · have hn := (hr.write_bounds F0 2 (u 33) (PrimTy.dflt .uint) (by decide)).2
    change (grownState 33 33).heap.writeAddr (.index (fresh 33) .fixed (u 33)) (PrimTy.dflt .uint)=none at hn
    have hi : TEnv.get (.there (.here : Idx Δ (.val .uint))) (grownState 33 33).env=u 33 := by
      change TEnv.get (.here : Idx Δ (.val .uint)) (TEnv.wk (g 33).ext Δ (state 33).env)=_
      rw [TEnv.get_wk];rfl
    simp only [TRun.deleteMem,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,
      show TEnv.get (.here : Idx (.mem (.fixed (.prim .uint) 33)::Δ) (.mem (.fixed (.prim .uint) 33))) (grownState 33 33).env=some (fresh 33) from rfl,
      hi,TRun.clearT,hn,bind,Except.bind,pure,Except.pure,TRes.ofOpt]
  · have hc' : run (code 33) (machine 33)=.ok target 0 := hc
    rw [run_append_ok hc']
    exact hb.2

/-- Same intrinsic shape cannot turn the produced fresh zero object into the
old alias with content7; genuine fixed and dynamic Source types also differ. -/
theorem stale_wrong_fixed :
    ¬ SourceUintFixedAt (post 0 1) 2 (g 1).heap (left.wk (g 1).ext) ∧
    (post 0 3).2.heap.ty 2≠some (.array .memory (.int .u256) none) ∧
    (post 0 3).2.heap.ty 2≠some (.array .memory (.int .u256) (some 1)) := by
  constructor
  · intro h
    have hkeep : Heap.Keeps (g 1).ext hp (g 1).heap := (source_uint_fixed_intrinsic (sy 0) hp 1 (by decide)).2.2.1
    have hbad : SourceUintFixedAt (post 0 1) 2 hp left := by
      unfold SourceUintFixedAt at h ⊢
      rw [hkeep left] at h
      exact h
    exact SourceUintFixedDefaultControls.wrong_type_length_identity.2.2.1 hbad

  · exact ⟨by decide,by decide⟩

theorem index_panic_bytes : Source.panicData .index=
    [0x4e,0x48,0x7b,0x71] ++ List.replicate 31 0 ++ [0x32] := by
  decide

/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedMutationControls.reached_operations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_operations
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedMutationControls.word_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms word_vectors
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedMutationControls.boundary_and_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundary_and_order
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedMutationControls.positive_instances' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms positive_instances
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedMutationControls.endpoint_delete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms endpoint_delete
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedMutationControls.stale_wrong_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_wrong_fixed
/-- info: 'Solidity.Backend.MemoryOps.SourceUintFixedMutationControls.index_panic_bytes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms index_panic_bytes
end Solidity.Backend.MemoryOps.SourceUintFixedMutationControls
