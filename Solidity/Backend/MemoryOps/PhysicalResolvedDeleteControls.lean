import Solidity.Backend.MemoryOps.PhysicalUintSequence
import Solidity.Backend.MemoryOps.PhysicalLocalDeleteGoal
import Solidity.Evm.Correct
import Solidity.Evm.MemoryObjects
import Solidity.Source.SemanticsExamples

/-! Populated initial and reached witnesses for the existing full local-delete
assembly. Dynamic Source objects remain dynamic; pointer locals and both heap
objects sit in their actual separated word frame. No Source/word world encoding
or bytecode/compiler adequacy is inferred from these component executions. -/
namespace Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls
open Evm Evm.Memory
open Source.SemanticsExamples (E0 G0 F0 s0)
private def C : Contract := {vars:=[]}
private abbrev U : RefTy := .array (.prim .uint)
private abbrev H : HTy := [U,U]
private abbrev Δ : Ctx := [.val .uint,.mem U,.mem U]
private abbrev SA : Source.STy := .array .memory (.int .u256) none
private abbrev Γ : Source.RCtx := [.int .u256,SA,SA]
private def u (n : Nat) : PrimTy.uint.Denote := indexValue (wmod n)
private def largest : PrimTy.uint.Denote := indexValue wMax
private def root : HRef H U := ⟨0,rfl⟩
private def neighbor : HRef H U := ⟨1,rfl⟩
private def hp : Heap H := (⟨[u 7,u 0,largest],by decide⟩,⟨[u 8,u 9],by decide⟩,())
private def state (k : Fin W) : State C Δ :=
  {storage:=Storage.init C,H:=H,heap:=hp,env:=(indexValue k,some root,some root,())}
private def base (id : Nat) : Fin W := if id=0 then wmod 8 else wmod 16
private def machine (k : Fin W) : Machine :=
  {Machine.init with stack:=[.val (wmod 77),.val (wmod 88)],mem:=fun a =>
    if a=0 then Word.val (wmod 24) else if a=1 ∨ a=2 then Word.val (wmod 8)
    else if a=3 then Word.val k else if a=7 then Word.val (wmod 99)
    else if a=8 then Word.val (wmod 3) else if a=9 then Word.val (wmod 7)
    else if a=11 then Word.val wMax else if a=15 then Word.val (wmod 55)
    else if a=16 then Word.val (wmod 2) else if a=17 then Word.val (wmod 8)
    else if a=18 then Word.val (wmod 9) else Word.val (wmod 0)}
private def bytes (k : Fin W) : Environment.Memory :=
  [(0,768),(1,256),(2,256),(3,k.val),(7,99),(8,3),(9,7),(10,0),(11,wMax.val),
    (15,55),(16,2),(17,8),(18,9)].foldl
      (fun m pair => Environment.writeBytes m (32*pair.1) (Semantics.wordBytes pair.2)) (fun _ => 0)
private def y0 : Source.EMState E0 [] := (.nil,s0)
private def y1 : Source.EMState E0 [] := ((Source.allocRef (sourceUintMemory [u 7,u 0,largest])).run y0).2
private def y2 : Source.EMState E0 [] := ((Source.allocRef (sourceUintMemory [u 8,u 9])).run y1).2
private def input (k : Fin W) : Source.EMState E0 Γ :=
  (.cons (sourceUint (indexValue k)) (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil)),y2.2)
private def SH : Source.HeapTy := fun _ => none
private def si : Source.Idx Γ (.int .u256) := .here
private def sr : Source.Idx Γ SA := .there .here
private def sa : Source.Idx Γ SA := .there (.there .here)
private def ti : Idx Δ (.val .uint) := .here
private def tr : Idx Δ (.mem U) := .there .here
private def ta : Idx Δ (.mem U) := .there (.there .here)

private theorem refs {R : RefTy} (q : HRef H R) : R=U ∧ (HEq q root ∨ HEq q neighbor) := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi;exact ⟨rfl,.inl HEq.rfl⟩
  | succ i => cases i with
    | zero => cases hi;exact ⟨rfl,.inr HEq.rfl⟩
    | succ i => cases hi

private theorem no_struct {s : Name} (q : HRef H (.struct s)) : False := by
  obtain ⟨ht,_⟩ := refs q
  cases ht

private theorem root_length : hp.len root .dyn=3 := by
  simp only [Heap.len,MObj.elems_dyn]
  rfl
private theorem neighbor_length : hp.len neighbor .dyn=2 := by
  simp only [Heap.len,MObj.elems_dyn]
  rfl

private theorem heap_repr (k : Fin W) : Objects.HeapRepr hp base 8 (machine k) := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · intro R q
    rcases refs q with ⟨rfl,hq|hq⟩ <;> cases hq <;> decide
  · intro R q
    rcases refs q with ⟨rfl,hq|hq⟩ <;> cases hq
      <;> simp only [Objects.cells,root_length,neighbor_length] <;> decide
  · intro R Q q r hn
    rcases refs q with ⟨rfl,hq|hq⟩ <;> cases hq
      <;> rcases refs r with ⟨rfl,hr|hr⟩ <;> cases hr
      <;> first | exact (hn rfl).elim | (simp only [Objects.cells,root_length,neighbor_length];decide)
  · intro A E a r
    rcases refs r with ⟨rfl,hr|hr⟩ <;> cases hr <;> cases a
    all_goals
      refine ⟨?_,?_,?_⟩
      · simp only [Objects.cells,root_length,neighbor_length]
        decide
      · intro _
        first | rw [root_length] | rw [neighbor_length]
        rfl
      intro i v hv
      simp only [Heap.get,Objs.get,hp,root,neighbor,MObj.elems_dyn] at hv
      cases i with
      | zero => cases Option.some.inj hv;exact ReprV.uint_of rfl
      | succ i => cases i with
        | zero => cases Option.some.inj hv;exact ReprV.uint_of rfl
        | succ i => cases i with
          | zero => first | (cases Option.some.inj hv;exact ReprV.uint_of rfl) | cases hv
          | succ i => cases hv
  · intro s r
    exact (no_struct r).elim
  · intro s f R r hf
    exact (no_struct r).elim

private theorem initial_repr (k : Fin W) : Objects.StateRepr 1 1 8 (Frag.init Δ) (state k) base (machine k) := by
  have hc : Sim C 1 0 (Frag.init []) (freshT C 0 W_pos ⟨0,W_pos⟩) Machine.init :=
    Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨?_,heap_repr k,?_,by decide⟩
  · refine ⟨hc.store,?_,?_,hc.net,hc.netSelf,hc.bound,?_,hc.env,hc.funds,hc.oracle⟩
    · intro p i
      cases i with
      | here => exact ReprV.uint_of rfl
      | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro R i hi
      cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
    · intro R i hi
      cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
  · intro R i
    cases i with | there i => cases i with
      | here => exact ⟨root,rfl,rfl⟩
      | there i => cases i with
        | here => exact ⟨root,rfl,rfl⟩
        | there i => nomatch i

private theorem initial_allocator (k : Fin W) : StructAllocatorRepr hp base 8 (wmod 24) (machine k) := by
  refine ⟨⟨(heap_repr k).primitive,⟨by decide,by decide,rfl,?_⟩,?_⟩,
    (heap_repr k).structHeap,(heap_repr k).structArraySeparated,?_⟩
  · intro a ha
    change 24≤a at ha
    simp only [machine,if_neg (show a≠0 by omega),if_neg (show ¬(a=1 ∨ a=2) by omega),
      if_neg (show a≠3 by omega),if_neg (show a≠7 by omega),if_neg (show a≠8 by omega),
      if_neg (show a≠9 by omega),if_neg (show a≠11 by omega),if_neg (show a≠15 by omega),
      if_neg (show a≠16 by omega),if_neg (show a≠17 by omega),if_neg (show a≠18 by omega)]
    rfl
  · intro p r
    have room : ∀ {R : RefTy} (q : HRef H R), (base q.id).val+Objects.cells hp q≤(wmod 24).val := by
      intro R q
      rcases refs q with ⟨rfl,hq|hq⟩ <;> cases hq
        <;> simp only [Objects.cells,root_length,neighbor_length] <;> decide
    simpa only [Objects.cells,Nat.add_assoc] using room r
  · intro s r
    exact (no_struct r).elim

private theorem source_repr (k : Fin W) : SourceUintMemoryAt (input k) 0 hp root .dyn := by
  unfold SourceUintMemoryAt
  simp only [MObj.elems_dyn]
  rfl

private theorem source_memOK (k : Fin W) : Source.MemOK E0 SH (input k) := by
  have h0 : Source.MemOK E0 SH y0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have h1 := source_uint_alloc_memOK (E := E0) (Γ := []) SH [u 7,u 0,largest] y0 h0
  change Source.MemOK E0 SH y1 ∧ _ at h1
  have h2 := source_uint_alloc_memOK (E := E0) (Γ := []) SH [u 8,u 9] y1 h1.1
  change Source.MemOK E0 SH y2 ∧ _ at h2
  exact ⟨⟨h2.1.1.1,⟨trivial,⟨⟨SA,rfl,rfl⟩,⟨⟨SA,rfl,rfl⟩,trivial⟩⟩⟩⟩,h2.1.2⟩

/-- INITIAL full word/Source premises are independently inhabited for every
canonical runtime index, including aliases; no successful deletion is assumed. -/
theorem initial_views (k : Fin W) :
    Objects.StateRepr 1 1 8 (Frag.init Δ) (state k) base (machine k) ∧
    SourceUintMemoryAt (input k) 0 hp root .dyn ∧ Source.MemOK E0 SH (input k) :=
  ⟨initial_repr k,source_repr k,source_memOK k⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.initial_views' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial_views
private def numericCells (c : Nat) : Prop := (8≤c ∧ c<12) ∨ (16≤c ∧ c<19)

private theorem written_read (m : Environment.Memory) (a w : Nat) :
    Environment.readMemory (Environment.writeBytes m a (Semantics.wordBytes w)) a 32=Semantics.wordBytes w := by
  simpa only [Environment.wordBytes_length] using Environment.read_written (Semantics.wordBytes w) a m

private theorem numeric_frame (k : Fin W) : WordFrame (machine k) (bytes k) numericCells := by
  constructor
  · intro c hc
    unfold numericCells at hc
    omega
  · intro c hc
    have which : c=8 ∨ c=9 ∨ c=10 ∨ c=11 ∨ c=16 ∨ c=17 ∨ c=18 := by
      unfold numericCells at hc
      omega
    rcases which with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      first
      | refine ⟨wmod 3,rfl,?_⟩
      | refine ⟨wmod 7,rfl,?_⟩
      | refine ⟨wmod 0,rfl,?_⟩
      | refine ⟨wMax,rfl,?_⟩
      | refine ⟨wmod 2,rfl,?_⟩
      | refine ⟨wmod 8,rfl,?_⟩
      | refine ⟨wmod 9,rfl,?_⟩
      simp only [bytes,List.foldl_cons,List.foldl_nil]
      repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length];omega)
      exact written_read _ _ _

private theorem initial (k : Fin W) : UintArrayAt (input k) 0 hp root (base root.id) (machine k) (bytes k) := by
  refine ⟨source_repr k,(initial_repr k).legacy.heap.arrays root,?_,?_⟩
  · intro c hc
    apply (numeric_frame k).fits c
    left
    rw [root_length] at hc
    exact hc
  · intro c hc
    apply (numeric_frame k).cells c
    left
    rw [root_length] at hc
    exact hc

/-- The FULL input bundle for the compiled-local-delete assembly is inhabited,
with an actual dynamic Source type, old alias, separated neighbor and nonempty
physical numeric footprint. Runtime indices have no additional admission cap. -/
theorem complete_initial (k : Fin W) :
    UintArrayAt (input k) 0 hp root (base root.id) (machine k) (bytes k) ∧
    Evm.Memory.StateRepr 1 1 8 (Frag.init Δ) (state k) base (machine k) ∧
    Source.MemOK E0 SH (input k) ∧
    (input k).1.get sr=.memRef rfl 0 ∧ (input k).1.get sa=.memRef rfl 0 ∧
    (input k).1.get si=sourceUint (indexValue k) ∧
    TEnv.get tr (state k).env=some root ∧ TEnv.get ta (state k).env=some root ∧
    TEnv.get ti (state k).env=indexValue k :=
  ⟨initial k,(initial_repr k).legacy,source_memOK k,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.complete_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_initial

private def nextHeap : Heap H := hp.set root (MObj.setElem .dyn (hp.get root) 0 (u 0))
private def nextWord : Machine := writeMachine (machine (wmod 0)) 9 (.val (wmod 0))
private def nextBytes : Environment.Memory := Environment.writeBytes (bytes (wmod 0)) 288 (List.replicate 32 (0 : UInt8))
private def deleteCode : List Evm.Instr := deleteLocalCode 1 tr (Evm.compileVal 1 (.simple (.local ti) : Val C Δ .uint))
private def typedDelete : Stmt C Δ Δ := .deleteMem (.loc (.index .dyn (.var tr rfl) (.simple (.local ti)))) rfl

/-- Apply the full assembly to independently proved INITIAL premises in both
pipelines. Its real expression, statement with ORIGINAL nps, intrinsic deletion,
whole compiled-local word program, byte relation and full reached frames are
conclusions. No representation or successful output is a caller premise. -/
theorem resolved_delete_physical_client (pipeline : Roadmap.Pipeline) (fuel nps : Nat) :
    ∃ (out : Heap H) (z : Source.EMState E0 Γ) (target : Machine),
      (Source.evalE (G0 pipeline) F0 (fuel+3) (sourceUintIndexedDelete sr si)).run (input (wmod 0))=
        (.ok Source.RVal.unit,z) ∧
      (Source.execS (G0 pipeline) F0 (fuel+4) nps none
        (.expr (sourceUintIndexedDelete sr si) : Source.RStmt E0 [] false .body Γ Γ)
        (input (wmod 0)).1).run (.nil,(input (wmod 0)).2)=
          (.ok (.normal (input (wmod 0)).1),(.nil,z.2)) ∧
      Stmt.run (state (wmod 0)) typedDelete=.ok ⟨(state (wmod 0)).withHeap out,List.prefix_refl _⟩ ∧
      Evm.run deleteCode (machine (wmod 0))=.ok target 0 ∧
      UintArrayAt z 0 out root (base root.id) target nextBytes ∧
      Evm.Memory.StateRepr 1 1 8 (Frag.init Δ) ((state (wmod 0)).withHeap out) base target ∧
      Source.MemOK E0 SH z ∧ z.1=(input (wmod 0)).1 ∧
      z.2={(input (wmod 0)).2 with heap:=z.2.heap} ∧ target.stack=(machine (wmod 0)).stack ∧
      KeepsAllocator 1 8 (state (wmod 0)) base (machine (wmod 0)) ((state (wmod 0)).withHeap out) target := by
  exact resolved_delete_physical (E := E0) (Γ := Γ) (C := C) (Δ := Δ) (input (wmod 0)) 0 (G0 pipeline) F0 fuel nps
    (state (wmod 0)) root sr si tr ti (wmod 0) 1 1 8 (Frag.init Δ) base (machine (wmod 0))
    (bytes (wmod 0)) SH (initial (wmod 0)) rfl rfl rfl rfl
    (by change (wmod 0).val<hp.len root .dyn;rw [root_length];decide) (initial_repr (wmod 0)).legacy (source_memOK (wmod 0))

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.resolved_delete_physical_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_delete_physical_client


private theorem expected_heap_write : hp.writeAddr (.index root .dyn (indexValue (wmod 0)))
    (PrimTy.dflt .uint)=some nextHeap := by
  have hi : (indexValue (wmod 0)).1.toNat<hp.len root .dyn := by rw [root_length];decide
  change (if (indexValue (wmod 0)).1.toNat<hp.len root .dyn then some _ else none)=_
  rw [if_pos hi]
  rfl

private theorem expected_word_run : Evm.run deleteCode (machine (wmod 0))=.ok nextWord 0 := by
  have prefixRun : Evm.run ([.push (.val (wmod 0)),.mload 2,.mload 3] : List Evm.Instr)
      (machine (wmod 0))=.ok ((((machine (wmod 0)).push (.val (wmod 0))).push
        (.val (wmod 8))).push (.val (wmod 0))) 0 := by
    have hr : (machine (wmod 0)).mem 2=.val (wmod 8) := rfl
    have hi : (machine (wmod 0)).mem 3=.val (wmod 0) := rfl
    simp only [Evm.run,exec_cons_zero,Evm.Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,hr,hi]
  have arr : Evm.Memory.ArrayRepr hp root (base root.id) (machine (wmod 0)) :=
    (initial_repr (wmod 0)).legacy.heap.arrays root
  rcases writeArray_correct arr (wmod 0) (PrimTy.dflt .uint) (.val (wmod 0))
      (ReprV.dflt_zero .uint) with ⟨out,ht,hw,_⟩ | ⟨bad,_⟩
  · change Evm.run (([.push (.val (wmod 0)),.mload 2,.mload 3] : List Evm.Instr) ++
      writeArrayStackCode) (machine (wmod 0))=_
    rw [run_append_ok prefixRun,writeArrayStackCode,
      arrayStack_append_eq ((machine (wmod 0)).push (.val (wmod 0))) (wmod 8) (wmod 0) 3 (by decide)
        (by rfl),←writeArrayCode]
    exact hw
  · rw [expected_heap_write] at bad
    cases bad

private theorem expected_typed_run : Stmt.run (state (wmod 0)) typedDelete=
    .ok ⟨(state (wmod 0)).withHeap nextHeap,List.prefix_refl _⟩ := by
  have hr : TEnv.get tr (state (wmod 0)).env=some root := rfl
  have hi : TEnv.get ti (state (wmod 0)).env=indexValue (wmod 0) := rfl
  have hw : (state (wmod 0)).heap.writeAddr (.index root .dyn (indexValue (wmod 0)))
      (PrimTy.dflt .uint)=some nextHeap := expected_heap_write
  change TRun.deleteMem (.loc (.index .dyn (.var tr rfl) (.simple (.local ti)))) (state (wmod 0))=_
  simp only [TRun.deleteMem,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,
    hr,hi,bind,Except.bind,pure,Except.pure,TRun.clearT,hw,TRes.ofOpt]

private theorem withHeap_injective (a b : Heap H)
    (h : (state (wmod 0)).withHeap a=(state (wmod 0)).withHeap b) : a=b := by
  have hs := congrArg (fun st : State C Δ => (⟨st.H,st.heap⟩ : Sigma Heap)) h
  injection hs with ht hh

/-- The concrete reached heap and WHOLE word machine are identified from the
actual full client executions; none is supplied as an agreement premise. -/
theorem reached_identity (pipeline : Roadmap.Pipeline) (fuel nps : Nat) :
    ∃ z : Source.EMState E0 Γ,
      (Source.evalE (G0 pipeline) F0 (fuel+3) (sourceUintIndexedDelete sr si)).run (input (wmod 0))=
        (.ok Source.RVal.unit,z) ∧
      (Source.execS (G0 pipeline) F0 (fuel+4) nps none
        (.expr (sourceUintIndexedDelete sr si) : Source.RStmt E0 [] false .body Γ Γ)
        (input (wmod 0)).1).run (.nil,(input (wmod 0)).2)=
          (.ok (.normal (input (wmod 0)).1),(.nil,z.2)) ∧
      Stmt.run (state (wmod 0)) typedDelete=.ok ⟨(state (wmod 0)).withHeap nextHeap,List.prefix_refl _⟩ ∧
      Evm.run deleteCode (machine (wmod 0))=.ok nextWord 0 ∧
      UintArrayAt z 0 nextHeap root (base root.id) nextWord nextBytes ∧
      Evm.Memory.StateRepr 1 1 8 (Frag.init Δ) ((state (wmod 0)).withHeap nextHeap) base nextWord ∧
      Source.MemOK E0 SH z ∧ z.1=(input (wmod 0)).1 ∧
      z.2={(input (wmod 0)).2 with heap:=z.2.heap} ∧
      nextWord.stack=(machine (wmod 0)).stack ∧
      KeepsAllocator 1 8 (state (wmod 0)) base (machine (wmod 0))
        ((state (wmod 0)).withHeap nextHeap) nextWord := by
  obtain ⟨out,z,target,he,hs,ht,hw,represented,words,mem,locals,frame,stack,alloc⟩ :=
    resolved_delete_physical_client pipeline fuel nps
  have typedEq := congrArg Solidity.Out.st (Except.ok.inj (ht.symm.trans expected_typed_run))
  have heapEq : out=nextHeap := withHeap_injective _ _ typedEq
  have targetEq : target=nextWord := (Evm.Out.ok.inj (hw.symm.trans expected_word_run)).1
  subst out
  subst target
  exact ⟨z,he,hs,ht,hw,represented,words,mem,locals,frame,stack,alloc⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.reached_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_identity

private theorem source_reached_fields (pipeline : Roadmap.Pipeline) (fuel : Nat)
    (z : Source.EMState E0 Γ)
    (he : (Source.evalE (G0 pipeline) F0 (fuel+3) (sourceUintIndexedDelete sr si)).run (input (wmod 0))=
      (.ok Source.RVal.unit,z)) :
    z.2.heap.get 0=some ⟨SA,sourceUintMemory [u 0,u 0,largest]⟩ ∧
    z.2.heap.get 1=(input (wmod 0)).2.heap.get 1 ∧ z.2.heap.next=2 ∧
    z.1=(input (wmod 0)).1 ∧ z.2.ex=(input (wmod 0)).2.ex ∧
    z.2.events=(input (wmod 0)).2.events ∧ z.2.logs=(input (wmod 0)).2.logs ∧
    z.2.fnLocals=(input (wmod 0)).2.fnLocals := by
  have hr : (input (wmod 0)).2.heap.get 0=some ⟨SA,sourceUintMemory [u 7,u 0,largest]⟩ := by
    simpa only [SourceUintMemoryAt,MObj.elems_dyn] using source_repr (wmod 0)
  obtain ⟨ht,known⟩ := source_uint_write (input (wmod 0)) 0 [u 7,u 0,largest] hr 0 (by decide) (u 0)
  let next : Source.EMState E0 Γ := ((input (wmod 0)).1,
    {(input (wmod 0)).2 with heap:=((input (wmod 0)).2.heap.write 0
      (sourceUintMemory ([u 7,u 0,largest].set 0 (u 0))) ht)})
  have hd : (Source.deleteLoc (E := E0) (Γ := Γ) F0 (fuel+2) (τ := .int .u256) (.mem 0 0)).run
      (input (wmod 0))=(.ok (),next) := known
  have typedBound : (indexValue (wmod 0)).1.toNat<hp.len root .dyn := by rw [root_length];decide
  have expression := (source_repr (wmod 0)).eval_delete_of_run (G0 pipeline) F0 fuel sr si
    (indexValue (wmod 0)) rfl rfl typedBound hd
  have same : z=next := congrArg Prod.snd (he.symm.trans expression)
  subst z
  refine ⟨?_,?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact Source.Heap.write_get _ _ _ ht
  · exact Source.Heap.write_other _ (by decide) _ ht

private theorem alias_word_read
    (words : Evm.Memory.StateRepr 1 1 8 (Frag.init Δ) ((state (wmod 0)).withHeap nextHeap) base nextWord) :
    Evm.run (readLocalCode 1 ta (.simple (.local ti) : Val C Δ .uint)) nextWord=
      .ok (nextWord.push (.val (wmod 0))) 0 := by
  have typed : ((Val.readMem (.index .dyn (.var ta rfl) (.simple (.local ti))) : Val C Δ .uint).evalT
      ((state (wmod 0)).withHeap nextHeap))=.ok (u 0) := by
    simp only [Val.evalT,MLoc.addrT,MPath.mvalT,Simple.evalT,
      show TEnv.get ta ((state (wmod 0)).withHeap nextHeap).env=some root from rfl,
      show TEnv.get ti ((state (wmod 0)).withHeap nextHeap).env=indexValue (wmod 0) from rfl,
      bind,Except.bind,pure,Except.pure]
    change TRes.ofOpt (nextHeap.index root .dyn (indexValue (wmod 0)))=.ok (u 0)
    simp only [Heap.index,nextHeap,Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn,indexValue,Int.toNat_natCast]
    rfl
  have cert := readLocal_correct words ta (.simple (.local ti) : Val C Δ .uint) rfl
  rw [typed] at cert
  rcases cert with ⟨v,w,hv,repr,run⟩ | ⟨bad,_⟩
  · cases Except.ok.inj hv
    obtain ⟨a,ha,hvalue,hw⟩ := repr.uint_inv
    have hz : a=0 := by change (0 : Int)=(a : Int) at hvalue;omega
    subst a
    simpa only [hw] using run
  · cases bad


private def wordView (m : Machine) := [0,1,2,3,4,7,8,9,10,11,15,16,17,18,19,20].map m.mem
private def byteView (m : Environment.Memory) :=
  [0,1,2,3,4,7,8,9,10,11,15,16,17,18,19,20].map (fun c => Environment.readMemory m (32*c) 32)

private theorem next_length : nextHeap.len root .dyn=3 := by
  simp only [Heap.len,nextHeap,Heap.get_set_same,MObj.elems_setElem,List.length_set]
  exact root_length

/-- The SAME actual full program has complete Source tables, typed objects,
all16 word/byte observations, retained-alias reads and nonvacuous allocator
frames. The appended target read is an expression producing zero, not a claim
that a discarded Source expression-statement compiler was executed. -/
theorem complete_observations (pipeline : Roadmap.Pipeline) (fuel nps : Nat) :
    StructAllocatorRepr hp base 8 (wmod 24) (machine (wmod 0)) ∧
    ∃ z : Source.EMState E0 Γ,
      (Source.evalE (G0 pipeline) F0 (fuel+3) (sourceUintIndexedDelete sr si)).run (input (wmod 0))=
        (.ok Source.RVal.unit,z) ∧
      (Source.execS (G0 pipeline) F0 (fuel+4) nps none
        (.expr (sourceUintIndexedDelete sr si) : Source.RStmt E0 [] false .body Γ Γ)
        (input (wmod 0)).1).run (.nil,(input (wmod 0)).2)=
          (.ok (.normal (input (wmod 0)).1),(.nil,z.2)) ∧
      Stmt.run (state (wmod 0)) typedDelete=.ok ⟨(state (wmod 0)).withHeap nextHeap,List.prefix_refl _⟩ ∧
      Evm.run deleteCode (machine (wmod 0))=.ok nextWord 0 ∧
      UintArrayAt z 0 nextHeap root (base root.id) nextWord nextBytes ∧
      Evm.Memory.StateRepr 1 1 8 (Frag.init Δ) ((state (wmod 0)).withHeap nextHeap) base nextWord ∧
      Source.MemOK E0 SH z ∧ z.1=(input (wmod 0)).1 ∧
      [(input (wmod 0)).2.heap.get 0,(input (wmod 0)).2.heap.get 1,z.2.heap.get 0,z.2.heap.get 1]=
        [some ⟨SA,sourceUintMemory [u 7,u 0,largest]⟩,some ⟨SA,sourceUintMemory [u 8,u 9]⟩,
         some ⟨SA,sourceUintMemory [u 0,u 0,largest]⟩,some ⟨SA,sourceUintMemory [u 8,u 9]⟩] ∧
      z.2.heap.next=2 ∧
      (Source.evalE (G0 pipeline) F0 (fuel+2) (.indexArray (.local sa) (.local si) rfl)).run z=
        (.ok (.val (sourceUint (u 0))),z) ∧
      Evm.run (deleteCode ++ readLocalCode 1 ta (.simple (.local ti) : Val C Δ .uint)) (machine (wmod 0))=
        .ok (nextWord.push (.val (wmod 0))) 0 ∧
      [MObj.elems .dyn (hp.get root),MObj.elems .dyn (hp.get neighbor),
        MObj.elems .dyn (nextHeap.get root),MObj.elems .dyn (nextHeap.get neighbor)]=
          [[u 7,u 0,largest],[u 8,u 9],[u 0,u 0,largest],[u 8,u 9]] ∧
      [wordView (machine (wmod 0)),wordView nextWord]=
        [[.val (wmod 24),.val (wmod 8),.val (wmod 8),.val (wmod 0),.val (wmod 0),.val (wmod 99),
          .val (wmod 3),.val (wmod 7),.val (wmod 0),.val wMax,.val (wmod 55),.val (wmod 2),
          .val (wmod 8),.val (wmod 9),.val (wmod 0),.val (wmod 0)],
         [.val (wmod 24),.val (wmod 8),.val (wmod 8),.val (wmod 0),.val (wmod 0),.val (wmod 99),
          .val (wmod 3),.val (wmod 0),.val (wmod 0),.val wMax,.val (wmod 55),.val (wmod 2),
          .val (wmod 8),.val (wmod 9),.val (wmod 0),.val (wmod 0)]] ∧
      [byteView (bytes (wmod 0)),byteView nextBytes]=
        [[768,256,256,0,0,99,3,7,0,wMax.val,55,2,8,9,0,0].map Semantics.wordBytes,
         [768,256,256,0,0,99,3,0,0,wMax.val,55,2,8,9,0,0].map Semantics.wordBytes] ∧
      Environment.cryptoStep (.op .MSTORE)
        ⟨lenU 288 (by decide)::lenU 0 (by decide)::[lenU 11 (by decide),lenU 22 (by decide)],bytes (wmod 0)⟩=
          some ⟨[lenU 11 (by decide),lenU 22 (by decide)],nextBytes⟩ ∧
      z.2.ex=(input (wmod 0)).2.ex ∧ z.2.events=(input (wmod 0)).2.events ∧
      z.2.logs=(input (wmod 0)).2.logs ∧ z.2.fnLocals=(input (wmod 0)).2.fnLocals ∧
      StructAllocatorRepr nextHeap base 8 (wmod 24) nextWord ∧
      nextWord.stack=[.val (wmod 77),.val (wmod 88)] ∧
      (∀ c,c≠9 → nextWord.mem c=(machine (wmod 0)).mem c) ∧
      (∀ a,a<288 ∨ 320≤a → nextBytes a=bytes (wmod 0) a) := by
  obtain ⟨z,he,hs,ht,hw,represented,words,mem,locals,frame,stack,alloc⟩ := reached_identity pipeline fuel nps
  obtain ⟨table,other,hnext,_,world,events,logs,fn⟩ := source_reached_fields pipeline fuel z he
  have hzroot : z.1.get sa=.memRef rfl 0 := by rw [locals];rfl
  have hzindex : z.1.get si=sourceUint (indexValue (wmod 0)) := by rw [locals];rfl
  have bound : (indexValue (wmod 0)).1.toNat<nextHeap.len root .dyn := by rw [next_length];decide
  have read := represented.source.eval_index (G0 pipeline) F0 fuel sa si (indexValue (wmod 0)) hzroot hzindex bound
  have sourceRead : (Source.evalE (G0 pipeline) F0 (fuel+2) (.indexArray (.local sa) (.local si) rfl)).run z=
      (.ok (.val (sourceUint (u 0))),z) := by
    simpa only [nextHeap,Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn] using read
  have appended : Evm.run (deleteCode ++ readLocalCode 1 ta (.simple (.local ti) : Val C Δ .uint))
      (machine (wmod 0))=.ok (nextWord.push (.val (wmod 0))) 0 := by
    rw [run_append_ok hw]
    exact alias_word_read words
  refine ⟨initial_allocator (wmod 0),z,he,hs,ht,hw,represented,words,mem,locals,?_,hnext,
    sourceRead,appended,?_,?_,?_,?_,world,events,logs,fn,alloc (wmod 24) (by decide)
      (initial_allocator (wmod 0)),rfl,?_,?_⟩
  · rw [table,other]
    rfl
  · simp only [nextHeap,Heap.get_set_same,Heap.get_set_ne hp root neighbor (by decide),MObj.elems_setElem,MObj.elems_dyn]
    rfl
  · rfl
  · simp only [byteView,List.map_cons,List.map_nil,List.cons.injEq,and_true]
    repeat' apply And.intro
    all_goals
      simp only [bytes,nextBytes,List.foldl_cons,List.foldl_nil,←uint_delete_bytes]
      repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length];omega)
      first | exact written_read _ _ _ | rfl
  · simpa only [uint_delete_bytes] using byte_mstore (bytes (wmod 0))
      [lenU 11 (by decide),lenU 22 (by decide)] (wmod 9) (wmod 0) (by decide)
  · intro c hc
    exact Evm.upd_other _ _ hc
  · intro a ha
    exact Environment.writeBytes_frame _ _ a _ (by simp only [List.length_replicate];omega)

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.complete_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_observations

/-- Exact endpoint failures in both pipelines, with the real Source index
panic, typed None/error and whole-word revert kept distinct. No symbolic word
panic payload or post-error target state is invented. -/
theorem endpoint (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 pipeline) F0 (fuel+3) (sourceUintIndexedDelete sr si)).run (input (wmod 3))=
      (.error (.revert (Source.panicData .index)),input (wmod 3)) ∧
    hp.writeAddr (.index root .dyn (indexValue (wmod 3))) (PrimTy.dflt .uint)=none ∧
    Stmt.run (state (wmod 3)) typedDelete=.error .revert ∧
    Evm.run deleteCode (machine (wmod 3))=.revert := by
  have bound : hp.len root .dyn≤(indexValue (wmod 3)).1.toNat := by rw [root_length];decide
  obtain ⟨sourceRun,wordRun⟩ := resolved_uint_delete_word_bounds (G0 pipeline) F0 fuel
    (state (wmod 3)) root (source_repr (wmod 3)) sr si tr ti (indexValue (wmod 3))
    rfl rfl rfl rfl bound (initial_repr (wmod 3)).legacy
  have noneRun : hp.writeAddr (.index root .dyn (indexValue (wmod 3))) (PrimTy.dflt .uint)=none :=
    ((source_repr (wmod 3)).delete_bounds F0 fuel (indexValue (wmod 3)) bound).2
  refine ⟨sourceRun,noneRun,?_,wordRun⟩
  change TRun.deleteMem (.loc (.index .dyn (.var tr rfl) (.simple (.local ti)))) (state (wmod 3))=_
  have hr : TEnv.get tr (state (wmod 3)).env=some root := rfl
  have hi : TEnv.get ti (state (wmod 3)).env=indexValue (wmod 3) := rfl
  have bad : (state (wmod 3)).heap.writeAddr (.index root .dyn (indexValue (wmod 3)))
      (PrimTy.dflt .uint)=none := noneRun
  simp only [TRun.deleteMem,MLoc.addrT,MPath.mvalT,Val.evalT,Simple.evalT,hr,hi,
    bind,Except.bind,pure,Except.pure,TRun.clearT,bad,TRes.ofOpt]

/-- Source's actual exhausted horizon retains its input; this does not assign
a horizon or timeout state to the separate word machine. -/
theorem low_horizon (pipeline : Roadmap.Pipeline) (nps : Nat) :
    (Source.evalE (G0 pipeline) F0 0 (sourceUintIndexedDelete sr si)).run (input (wmod 0))=
      (.error .timeout,input (wmod 0)) ∧
    (Source.execS (G0 pipeline) F0 0 nps none
      (.expr (sourceUintIndexedDelete sr si) : Source.RStmt E0 [] false .body Γ Γ)
      (input (wmod 0)).1).run (.nil,(input (wmod 0)).2)=
        (.error .timeout,(.nil,(input (wmod 0)).2)) := by
  exact ⟨rfl,rfl⟩

/-- A skipped delete reads7 through the retained alias, whereas the actual
reached read is0. Both complete word images and the selected physical span
also discriminate that stale input. -/
theorem stale_inputs (pipeline : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G0 pipeline) F0 (fuel+2) (.indexArray (.local sa) (.local si) rfl)).run (input (wmod 0))=
      (.ok (.val (sourceUint (u 7))),input (wmod 0)) ∧
    sourceUint (D := E0.layout) (u 7)≠sourceUint (u 0) ∧
    wordView (machine (wmod 0))≠wordView nextWord ∧
    Environment.readMemory (bytes (wmod 0)) 288 32≠Environment.readMemory nextBytes 288 32 := by
  have bound : (indexValue (wmod 0)).1.toNat<hp.len root .dyn := by rw [root_length];decide
  have read := (source_repr (wmod 0)).eval_index (G0 pipeline) F0 fuel sa si
    (indexValue (wmod 0)) rfl rfl bound
  refine ⟨?_,?_,by decide,?_⟩
  · simpa only [MObj.elems_dyn] using read
  · intro same
    have converted := congrArg (fun v : Source.Val E0.layout (.int .u256) => calldataUint (.val v)) same
    have unequal : u 7=u 0 := by simpa only [calldataUint_sourceUint] using converted
    have impossible : (7 : Int)=0 := congrArg Subtype.val unequal
    omega
  · obtain ⟨w,hw,hb⟩ := (numeric_frame (wmod 0)).cells 9 (by left;decide)
    have same : w=wmod 7 := Evm.Word.val.inj (hw.symm.trans rfl)
    have old : Environment.readMemory (bytes (wmod 0)) 288 32=Semantics.wordBytes 7 := by
      simpa only [same] using hb
    have next : Environment.readMemory nextBytes 288 32=Semantics.wordBytes 0 := by
      change Environment.readMemory (Environment.writeBytes (bytes (wmod 0)) 288
        (List.replicate 32 (0 : UInt8))) 288 32=_
      rw [←uint_delete_bytes]
      exact written_read _ _ _
    rw [old,next]
    decide

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms endpoint
/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.low_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms low_horizon
/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.stale_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_inputs

/-- A populated same-cell client: the first actual write changes zero to one;
the second actual reached delete restores zero. Both physical postrelations
come from the actual sequence theorem, not assumed postconditions. -/
theorem assignment_delete_physical_client (pipeline : Roadmap.Pipeline) (fuel nps : Nat) :
    let first := Environment.writeBytes (bytes (wmod 1)) 320 (Semantics.wordBytes 1)
    let final := Environment.writeBytes first 320 (Semantics.wordBytes 0)
    ∃ (mid out : Heap H) (ym z : Source.EMState E0 Γ) (mm target : Machine),
      hp.writeAddr (.index root .dyn (u 1)) (u 1)=some mid ∧
      mid.writeAddr (.index root .dyn (u 1)) (PrimTy.dflt .uint)=some out ∧
      UintArrayAt ym 0 mid root (base root.id) mm first ∧
      UintArrayAt z 0 out root (base root.id) target final ∧
      StateRepr 1 1 8 (Frag.init Δ) ((state (wmod 1)).withHeap out) base target ∧
      (Source.execItems (G0 pipeline) F0 (fuel+6) nps none
        (.stmt (.expr (sourceUintIndexedAssign sr si si))
          (.stmt (.expr (sourceUintIndexedDelete sr si)) .nil) : Source.RItems E0 [] false .body Γ Γ)
        (input (wmod 1)).1).run (.nil,(input (wmod 1)).2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      Evm.run (writeLocalCode (C := C) 1 tr (.simple (.local ti)) (.simple (.local ti)) ++
        deleteLocalCode 1 tr (Evm.compileVal 1 (.simple (.local ti) : Val C Δ .uint)))
        (machine (wmod 1))=.ok target 0 := by
  have bound : (wmod 1).val<(state (wmod 1)).heap.len root .dyn := by
    change (wmod 1).val<hp.len root .dyn
    rw [root_length]
    decide
  obtain ⟨mid,out,ym,z,mm,target,offset1,offset2,typed1,typed2,sw1,sw2,stmt1,stmt2,items,
    typed,code1,code2,append,physical1,physical2,words1,words2,mem1,mem2,locals1,locals2,stack,alloc,
    offsetEq1,offsetEq2,byte1,byte2,exterior⟩ :=
    resolved_uint_assign_delete_physical (G0 pipeline) F0 fuel nps (state (wmod 1)) root
      sr si si si tr ti ti ti (wmod 1) (wmod 1) (wmod 1)
      rfl rfl rfl rfl rfl rfl rfl rfl bound bound (initial (wmod 1))
      (initial_repr (wmod 1)).legacy SH (source_memOK (wmod 1))
  exact ⟨mid,out,ym,z,mm,target,typed1,typed2,physical1,physical2,words2,items,append⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.assignment_delete_physical_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assignment_delete_physical_client

/-- Complete selected-object vectors at the actual first and second output.
The first operation changes the cell; deleting from the reached heap restores it. -/
theorem assignment_delete_values (pipeline : Roadmap.Pipeline) (fuel nps : Nat) :
    ∃ (mid out : Heap H),
      hp.writeAddr (.index root .dyn (u 1)) (u 1)=some mid ∧
      mid.writeAddr (.index root .dyn (u 1)) (PrimTy.dflt .uint)=some out ∧
      MObj.elems .dyn (hp.get root)=[u 7,u 0,largest] ∧
      MObj.elems .dyn (mid.get root)=[u 7,u 1,largest] ∧
      MObj.elems .dyn (out.get root)=[u 7,u 0,largest] := by
  obtain ⟨mid,out,ym,z,mm,target,h1,h2,physical1,physical2,words,items,append⟩ :=
    assignment_delete_physical_client pipeline fuel nps
  have first := indexedWrite_elems hp mid root .dyn (u 1) (u 1) h1
  have second := indexedWrite_elems mid out root .dyn (u 1) (PrimTy.dflt .uint) h2
  have initial : MObj.elems .dyn (hp.get root)=[u 7,u 0,largest] := by
    simp only [Heap.get,Objs.get,hp,root,MObj.elems_dyn]
  have reached : MObj.elems .dyn (mid.get root)=[u 7,u 1,largest] := by
    rw [first,initial]
    rfl
  refine ⟨mid,out,h1,h2,initial,reached,?_⟩
  rw [second,reached]
  rfl

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.assignment_delete_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assignment_delete_values

private def pairMid : Heap H := hp.set root (MObj.setElem .dyn (hp.get root) 1 (u 1))
private def pairOut : Heap H := pairMid.set root (MObj.setElem .dyn (pairMid.get root) 1 (u 0))
private def pairWord : Machine := writeMachine (machine (wmod 1)) 10 (.val (wmod 1))
private def pairWordOut : Machine := writeMachine pairWord 10 (.val (wmod 0))
private def pairBytes : Environment.Memory := Environment.writeBytes (bytes (wmod 1)) 320 (Semantics.wordBytes 1)
private def pairBytesOut : Environment.Memory := Environment.writeBytes pairBytes 320 (Semantics.wordBytes 0)
private def pairAssignCode : List Evm.Instr := writeLocalCode (C := C) 1 tr (.simple (.local ti)) (.simple (.local ti))
private def pairDeleteCode : List Evm.Instr := deleteLocalCode 1 tr (Evm.compileVal 1 (.simple (.local ti) : Val C Δ .uint))

private theorem pair_write : hp.writeAddr (.index root .dyn (u 1)) (u 1)=some pairMid := by
  have hi : (u 1).1.toNat<hp.len root .dyn := by rw [root_length];decide
  change (if (u 1).1.toNat<hp.len root .dyn then some _ else none)=_
  rw [if_pos hi]
  rfl

private theorem pair_length : pairMid.len root .dyn=3 := by
  simp only [Heap.len,pairMid,Heap.get_set_same,MObj.elems_setElem,List.length_set]
  exact root_length

private theorem pair_delete : pairMid.writeAddr (.index root .dyn (u 1)) (u 0)=some pairOut := by
  have hi : (u 1).1.toNat<pairMid.len root .dyn := by rw [pair_length];decide
  change (if (u 1).1.toNat<pairMid.len root .dyn then some _ else none)=_
  rw [if_pos hi]
  rfl

private theorem pair_array : ArrayRepr pairMid root (base root.id) pairWord :=
  ((initial_repr (wmod 1)).legacy.heap.arrays root).set 1
    (by change 1<hp.len root .dyn;rw [root_length];decide) (u 1) (.val (wmod 1)) (ReprV.uint_of rfl)

private theorem pair_stack_run {hp' : Heap H} {m : Machine}
    (arr : ArrayRepr hp' root (base root.id) m) (hlen : hp'.len root .dyn=3)
    (w : Fin W) :
    Evm.run writeArrayStackCode (((m.push (.val w)).push (.val (wmod 8))).push (.val (wmod 1)))=
      .ok (writeMachine m 10 (.val w)) 0 := by
  rcases writeArray_correct arr (wmod 1) (indexValue w) (.val w)
      (ReprV.uint_of rfl) with ⟨out,ht,hw,_⟩ | ⟨bad,_⟩
  · rw [writeArrayStackCode,
      arrayStack_append_eq (m.push (.val w)) (wmod 8) (wmod 1) 3 (by decide)
        (by simpa only [hlen] using arr.length),←writeArrayCode]
    exact hw
  · have hi : (indexValue (wmod 1)).1.toNat<hp'.len root .dyn := by rw [hlen];decide
    change (if (indexValue (wmod 1)).1.toNat<hp'.len root .dyn then some _ else none)=none at bad
    rw [if_pos hi] at bad
    cases bad

private theorem pair_assign_run : Evm.run pairAssignCode (machine (wmod 1))=.ok pairWord 0 := by
  have headRun : Evm.run ([.mload 3,.mload 2,.mload 3] : List Evm.Instr) (machine (wmod 1))=
      .ok ((((machine (wmod 1)).push (.val (wmod 1))).push (.val (wmod 8))).push (.val (wmod 1))) 0 := by
    have hr : (machine (wmod 1)).mem 2=.val (wmod 8) := rfl
    have hi : (machine (wmod 1)).mem 3=.val (wmod 1) := rfl
    simp only [Evm.run,exec_cons_zero,Evm.Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,hr,hi]
  change Evm.run (([.mload 3,.mload 2,.mload 3] : List Evm.Instr) ++ writeArrayStackCode) _=_
  rw [run_append_ok headRun]
  exact pair_stack_run ((initial_repr (wmod 1)).legacy.heap.arrays root) root_length (wmod 1)

private theorem pair_delete_run : Evm.run pairDeleteCode pairWord=.ok pairWordOut 0 := by
  have headRun : Evm.run ([.push (.val (wmod 0)),.mload 2,.mload 3] : List Evm.Instr) pairWord=
      .ok (((pairWord.push (.val (wmod 0))).push (.val (wmod 8))).push (.val (wmod 1))) 0 := by
    have hr : pairWord.mem 2=.val (wmod 8) := rfl
    have hi : pairWord.mem 3=.val (wmod 1) := rfl
    simp only [Evm.run,exec_cons_zero,Evm.Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,hr,hi]
  change Evm.run (([.push (.val (wmod 0)),.mload 2,.mload 3] : List Evm.Instr) ++ writeArrayStackCode) _=_
  rw [run_append_ok headRun]
  exact pair_stack_run pair_array pair_length (wmod 0)

private theorem pair_source_frames (fuel : Nat) (ym z : Source.EMState E0 Γ)
    (first : (Source.writeLoc (E := E0) (Γ := Γ) F0 (fuel+3) (.mem 0 1) (sourceUint (u 1))).run
      (input (wmod 1))=(.ok (),ym))
    (second : (Source.deleteLoc (E := E0) (Γ := Γ) F0 (fuel+2) (τ := .int .u256) (.mem 0 1)).run
      ym=(.ok (),z)) :
    ym.1=(input (wmod 1)).1 ∧ z.1=(input (wmod 1)).1 ∧
    ym.2={(input (wmod 1)).2 with heap:=ym.2.heap} ∧
    z.2={(input (wmod 1)).2 with heap:=z.2.heap} ∧
    ym.2.heap.next=2 ∧ z.2.heap.next=2 ∧
    ym.2.heap.get 1=(input (wmod 1)).2.heap.get 1 ∧
    z.2.heap.get 1=(input (wmod 1)).2.heap.get 1 := by
  have hr : (input (wmod 1)).2.heap.get 0=some ⟨SA,sourceUintMemory [u 7,u 0,largest]⟩ := by
    simpa only [SourceUintMemoryAt,MObj.elems_dyn] using source_repr (wmod 1)
  obtain ⟨ht1,known1⟩ := source_uint_write (input (wmod 1)) 0 [u 7,u 0,largest] hr 1 (by decide) (u 1)
  have same1 := congrArg Prod.snd (first.symm.trans known1)
  dsimp only at same1
  subst ym
  have reached : ((input (wmod 1)).2.heap.write 0
      (sourceUintMemory ([u 7,u 0,largest].set 1 (u 1))) ht1).get 0=
        some ⟨SA,sourceUintMemory [u 7,u 1,largest]⟩ := Source.Heap.write_get _ _ _ ht1
  obtain ⟨ht2,known2⟩ := source_uint_write
    ((input (wmod 1)).1,{(input (wmod 1)).2 with heap:=((input (wmod 1)).2.heap.write 0
      (sourceUintMemory ([u 7,u 0,largest].set 1 (u 1))) ht1)})
    0 [u 7,u 1,largest] reached 1 (by decide) (u 0)
  have same2 := congrArg Prod.snd (second.symm.trans known2)
  dsimp only at same2
  subst z
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · exact Source.Heap.write_other _ (by decide) _ ht1
  · rw [Source.Heap.write_other _ (by decide) _ ht2]
    exact Source.Heap.write_other _ (by decide) _ ht1

/-- Ordered whole fixture images, including both heap objects, every retained
word/byte observation, and both actual intermediate/final word machines. -/
theorem assignment_delete_images :
    [MObj.elems .dyn (hp.get root),MObj.elems .dyn (hp.get neighbor),
     MObj.elems .dyn (pairMid.get root),MObj.elems .dyn (pairMid.get neighbor),
     MObj.elems .dyn (pairOut.get root),MObj.elems .dyn (pairOut.get neighbor)]=
      [[u 7,u 0,largest],[u 8,u 9],[u 7,u 1,largest],[u 8,u 9],[u 7,u 0,largest],[u 8,u 9]] ∧
    [wordView (machine (wmod 1)),wordView pairWord,wordView pairWordOut]=
      [[.val (wmod 24),.val (wmod 8),.val (wmod 8),.val (wmod 1),.val (wmod 0),.val (wmod 99),
        .val (wmod 3),.val (wmod 7),.val (wmod 0),.val wMax,.val (wmod 55),.val (wmod 2),
        .val (wmod 8),.val (wmod 9),.val (wmod 0),.val (wmod 0)],
       [.val (wmod 24),.val (wmod 8),.val (wmod 8),.val (wmod 1),.val (wmod 0),.val (wmod 99),
        .val (wmod 3),.val (wmod 7),.val (wmod 1),.val wMax,.val (wmod 55),.val (wmod 2),
        .val (wmod 8),.val (wmod 9),.val (wmod 0),.val (wmod 0)],
       [.val (wmod 24),.val (wmod 8),.val (wmod 8),.val (wmod 1),.val (wmod 0),.val (wmod 99),
        .val (wmod 3),.val (wmod 7),.val (wmod 0),.val wMax,.val (wmod 55),.val (wmod 2),
        .val (wmod 8),.val (wmod 9),.val (wmod 0),.val (wmod 0)]] ∧
    [byteView (bytes (wmod 1)),byteView pairBytes,byteView pairBytesOut]=
      [[768,256,256,1,0,99,3,7,0,wMax.val,55,2,8,9,0,0].map Semantics.wordBytes,
       [768,256,256,1,0,99,3,7,1,wMax.val,55,2,8,9,0,0].map Semantics.wordBytes,
       [768,256,256,1,0,99,3,7,0,wMax.val,55,2,8,9,0,0].map Semantics.wordBytes] := by
  refine ⟨?_,rfl,?_⟩
  · simp only [pairOut,pairMid,Heap.get_set_same,Heap.get_set_ne _ root neighbor (by decide),
      MObj.elems_setElem,MObj.elems_dyn]
    rfl
  · simp only [byteView,List.map_cons,List.map_nil,List.cons.injEq,and_true]
    repeat' apply And.intro
    all_goals
      simp only [bytes,pairBytes,pairBytesOut,List.foldl_cons,List.foldl_nil]
      repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length];omega)
      first | exact written_read _ _ _ | rfl

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.assignment_delete_images' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assignment_delete_images

/-- The actual same-cell sequence in both pipelines, now linked to its
complete ordered Source objects and both physical/word reached states. Source
locals and every nonheap state field are framed, not assumed postconditions.
The scaled byte image is a component relation, not a whole bytecode compiler. -/
theorem assignment_delete_complete (pipeline : Roadmap.Pipeline) (fuel nps : Nat) :
    ∃ (ym z : Source.EMState E0 Γ),
      (Source.writeLoc (E := E0) (Γ := Γ) F0 (fuel+3) (.mem 0 1) (sourceUint (u 1))).run
        (input (wmod 1))=(.ok (),ym) ∧
      (Source.deleteLoc (E := E0) (Γ := Γ) F0 (fuel+2) (τ := .int .u256) (.mem 0 1)).run
        ym=(.ok (),z) ∧
      (Source.execItems (G0 pipeline) F0 (fuel+6) nps none
        (.stmt (.expr (sourceUintIndexedAssign sr si si))
          (.stmt (.expr (sourceUintIndexedDelete sr si)) .nil) : Source.RItems E0 [] false .body Γ Γ)
        (input (wmod 1)).1).run (.nil,(input (wmod 1)).2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      Evm.run pairAssignCode (machine (wmod 1))=.ok pairWord 0 ∧
      Evm.run pairDeleteCode pairWord=.ok pairWordOut 0 ∧
      Evm.run (pairAssignCode ++ pairDeleteCode) (machine (wmod 1))=.ok pairWordOut 0 ∧
      UintArrayAt ym 0 pairMid root (base root.id) pairWord pairBytes ∧
      UintArrayAt z 0 pairOut root (base root.id) pairWordOut pairBytesOut ∧
      StateRepr 1 1 8 (Frag.init Δ) ((state (wmod 1)).withHeap pairMid) base pairWord ∧
      StateRepr 1 1 8 (Frag.init Δ) ((state (wmod 1)).withHeap pairOut) base pairWordOut ∧
      Source.MemOK E0 SH ym ∧ Source.MemOK E0 SH z ∧
      ym.1=(input (wmod 1)).1 ∧ z.1=(input (wmod 1)).1 ∧
      ym.2={(input (wmod 1)).2 with heap:=ym.2.heap} ∧
      z.2={(input (wmod 1)).2 with heap:=z.2.heap} ∧
      [ym.2.heap.next,z.2.heap.next]=[2,2] ∧
      [(input (wmod 1)).2.heap.get 0,(input (wmod 1)).2.heap.get 1,
       ym.2.heap.get 0,ym.2.heap.get 1,z.2.heap.get 0,z.2.heap.get 1]=
        [some ⟨SA,sourceUintMemory [u 7,u 0,largest]⟩,some ⟨SA,sourceUintMemory [u 8,u 9]⟩,
         some ⟨SA,sourceUintMemory [u 7,u 1,largest]⟩,some ⟨SA,sourceUintMemory [u 8,u 9]⟩,
         some ⟨SA,sourceUintMemory [u 7,u 0,largest]⟩,some ⟨SA,sourceUintMemory [u 8,u 9]⟩] ∧
      (Source.evalE (G0 pipeline) F0 (fuel+2) (.indexArray (.local sa) (.local si) rfl)).run ym=
        (.ok (.val (sourceUint (u 1))),ym) ∧
      (Source.evalE (G0 pipeline) F0 (fuel+2) (.indexArray (.local sa) (.local si) rfl)).run z=
        (.ok (.val (sourceUint (u 0))),z) ∧
      StructAllocatorRepr pairOut base 8 (wmod 24) pairWordOut ∧
      pairWord.stack=[.val (wmod 77),.val (wmod 88)] ∧
      pairWordOut.stack=[.val (wmod 77),.val (wmod 88)] := by
  have bound : (wmod 1).val<(state (wmod 1)).heap.len root .dyn := by
    change (wmod 1).val<hp.len root .dyn
    rw [root_length]
    decide
  obtain ⟨mid,out,ym,z,mm,target,offset1,offset2,typed1,typed2,sw1,sw2,stmt1,stmt2,items,
    typed,code1,code2,append,physical1,physical2,words1,words2,mem1,mem2,locals1,locals2,stack,alloc,
    offsetEq1,offsetEq2,byte1,byte2,exterior⟩ :=
    resolved_uint_assign_delete_physical (G0 pipeline) F0 fuel nps (state (wmod 1)) root
      sr si si si tr ti ti ti (wmod 1) (wmod 1) (wmod 1)
      rfl rfl rfl rfl rfl rfl rfl rfl bound bound (initial (wmod 1))
      (initial_repr (wmod 1)).legacy SH (source_memOK (wmod 1))
  have midEq : mid=pairMid := Option.some.inj (typed1.symm.trans pair_write)
  subst mid
  have outEq : out=pairOut := Option.some.inj (typed2.symm.trans pair_delete)
  subst out
  have mmEq : mm=pairWord := (Evm.Out.ok.inj (code1.symm.trans pair_assign_run)).1
  subst mm
  have targetEq : target=pairWordOut := (Evm.Out.ok.inj (code2.symm.trans pair_delete_run)).1
  subst target
  obtain ⟨_,_,frame1,frame2,next1,next2,other1,other2⟩ := pair_source_frames fuel ym z sw1 sw2
  have initialTable : (input (wmod 1)).2.heap.get 0=some ⟨SA,sourceUintMemory [u 7,u 0,largest]⟩ := by
    simpa only [SourceUintMemoryAt,MObj.elems_dyn] using source_repr (wmod 1)
  have midTable : ym.2.heap.get 0=some ⟨SA,sourceUintMemory [u 7,u 1,largest]⟩ := by
    simpa only [SourceUintMemoryAt,pairMid,Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn] using physical1.source
  have finalTable : z.2.heap.get 0=some ⟨SA,sourceUintMemory [u 7,u 0,largest]⟩ := by
    simpa only [SourceUintMemoryAt,pairOut,pairMid,Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn] using physical2.source
  have read1 := physical1.source.eval_index (G0 pipeline) F0 fuel sa si (indexValue (wmod 1))
    (by rw [locals1];rfl) (by rw [locals1];rfl) (by rw [pair_length];decide)
  have outLength : pairOut.len root .dyn=3 := by
    simp only [Heap.len,pairOut,Heap.get_set_same,MObj.elems_setElem,List.length_set]
    exact pair_length
  have read2 := physical2.source.eval_index (G0 pipeline) F0 fuel sa si (indexValue (wmod 1))
    (by rw [locals2];rfl) (by rw [locals2];rfl) (by rw [outLength];decide)
  refine ⟨ym,z,sw1,sw2,items,code1,code2,append,physical1,physical2,words1,words2,mem1,mem2,
    locals1,locals2,frame1,frame2,?_,?_,?_,?_,alloc (wmod 24) (by decide) (initial_allocator (wmod 1)),rfl,rfl⟩
  · rw [next1,next2]
  · rw [initialTable,midTable,finalTable,other1,other2]
    rfl
  · simpa only [pairMid,Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn] using read1
  · simpa only [pairOut,pairMid,Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn] using read2

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.assignment_delete_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assignment_delete_complete

/-- Dropping the reached deletion cannot preserve these observations: the
actual Source alias reads and whole word/byte observation vectors distinguish
its material first output from its real final output. Midpoint reads here are
separate observations, not instructions inserted into the paired target code. -/
theorem assignment_delete_discriminates (pipeline : Roadmap.Pipeline) (fuel nps : Nat) :
    ∃ (ym z : Source.EMState E0 Γ),
      (Source.writeLoc (E := E0) (Γ := Γ) F0 (fuel+3) (.mem 0 1) (sourceUint (u 1))).run
        (input (wmod 1))=(.ok (),ym) ∧
      (Source.deleteLoc (E := E0) (Γ := Γ) F0 (fuel+2) (τ := .int .u256) (.mem 0 1)).run
        ym=(.ok (),z) ∧
      Evm.run pairDeleteCode pairWord=.ok pairWordOut 0 ∧
      Evm.run pairAssignCode (machine (wmod 1))=.ok pairWord 0 ∧
      (Source.execItems (G0 pipeline) F0 (fuel+6) nps none
        (.stmt (.expr (sourceUintIndexedAssign sr si si))
          (.stmt (.expr (sourceUintIndexedDelete sr si)) .nil) : Source.RItems E0 [] false .body Γ Γ)
        (input (wmod 1)).1).run (.nil,(input (wmod 1)).2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      Evm.run (pairAssignCode ++ pairDeleteCode) (machine (wmod 1))=.ok pairWordOut 0 ∧
      (Source.evalE (G0 pipeline) F0 (fuel+2) (.indexArray (.local sa) (.local si) rfl)).run ym=
        (.ok (.val (sourceUint (u 1))),ym) ∧
      (Source.evalE (G0 pipeline) F0 (fuel+2) (.indexArray (.local sa) (.local si) rfl)).run z=
        (.ok (.val (sourceUint (u 0))),z) ∧
      sourceUint (D := E0.layout) (u 1)≠sourceUint (u 0) ∧
      wordView pairWord≠wordView pairWordOut ∧ byteView pairBytes≠byteView pairBytesOut := by
  obtain ⟨ym,z,sw1,sw2,items,code1,code2,append,physical1,physical2,words1,words2,
    mem1,mem2,locals1,locals2,frame1,frame2,next,table,read1,read2,alloc,stack1,stack2⟩ :=
    assignment_delete_complete pipeline fuel nps
  refine ⟨ym,z,sw1,sw2,code2,code1,items,append,read1,read2,?_,by decide,?_⟩
  · intro same
    have converted := congrArg (fun v : Source.Val E0.layout (.int .u256) => calldataUint (.val v)) same
    have unequal : u 1=u 0 := by simpa only [calldataUint_sourceUint] using converted
    have impossible : (1 : Int)=0 := congrArg Subtype.val unequal
    omega
  · have first : Environment.readMemory pairBytes 320 32=Semantics.wordBytes 1 := written_read _ _ _
    have final : Environment.readMemory pairBytesOut 320 32=Semantics.wordBytes 0 := written_read _ _ _
    intro same
    have cell := congrArg (fun xs : List (List UInt8) => xs[8]?) same
    change some (Environment.readMemory pairBytes 320 32)=some (Environment.readMemory pairBytesOut 320 32) at cell
    have equal := Option.some.inj cell
    rw [first,final] at equal
    have different : Semantics.wordBytes 1≠Semantics.wordBytes 0 := by decide
    exact different equal

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.assignment_delete_discriminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assignment_delete_discriminates

/-- Concrete scaled byte-store trace uses the real first byte output for the
second step. Pointer-path and numeric-store programs remain separate models;
this is not an assertion that the entire compiled word prefix was byte-executed. -/
theorem assignment_delete_byte_steps (tail : List Environment.Word) :
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU 320 (by decide)::lenU 1 (by decide)::tail,bytes (wmod 1)⟩=some ⟨tail,pairBytes⟩ ∧
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU 320 (by decide)::lenU 0 (by decide)::tail,pairBytes⟩=some ⟨tail,pairBytesOut⟩ ∧
    (∀ a,a<320 ∨ 352≤a → pairBytesOut a=bytes (wmod 1) a) := by
  refine ⟨?_,?_,?_⟩
  · exact byte_mstore (bytes (wmod 1)) tail (wmod 10) (wmod 1) (by decide)
  · exact byte_mstore pairBytes tail (wmod 10) (wmod 0) (by decide)
  · intro a outside
    have second : pairBytesOut a=pairBytes a :=
      Environment.writeBytes_frame _ _ a _ (by simp only [Environment.wordBytes_length];omega)
    have first : pairBytes a=bytes (wmod 1) a :=
      Environment.writeBytes_frame _ _ a _ (by simp only [Environment.wordBytes_length];omega)
    exact second.trans first

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.assignment_delete_byte_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assignment_delete_byte_steps

private abbrev RejectΓ : Source.RCtx := .int .u256 :: Γ
private abbrev RejectΔ : Ctx := .val .uint :: Δ
private def rejectInput : Source.EMState E0 RejectΓ :=
  (.cons (sourceUint (u 3)) (input (wmod 1)).1,(input (wmod 1)).2)
private def rejectState : State C RejectΔ := (state (wmod 1)).push (t := .val .uint) (u 3)
private def rejectWord : Machine := writeMachine (machine (wmod 1)) 4 (.val (wmod 3))
private def rejectBytes : Environment.Memory := Environment.writeBytes (bytes (wmod 1)) 128 (Semantics.wordBytes 3)
private def rejectFrag : Frag RejectΔ := (Frag.init Δ).push (.val .uint) .ok
private def rejectSourceRoot : Source.Idx RejectΓ SA := .there sr
private def rejectSourceIndex : Source.Idx RejectΓ (.int .u256) := .there si
private def rejectSourceAlias : Source.Idx RejectΓ SA := .there sa
private def rejectTypedRoot : Idx RejectΔ (.mem U) := .there tr
private def rejectTypedIndex : Idx RejectΔ (.val .uint) := .there ti
private def rejectTypedAlias : Idx RejectΔ (.mem U) := .there ta

private theorem reject_repr : StateRepr 1 1 8 rejectFrag rejectState base rejectWord :=
  (initial_repr (wmod 1)).legacy.consVal (u 3) (.val (wmod 3)) (ReprV.uint_of rfl) (by decide)

private theorem reject_source : SourceUintMemoryAt rejectInput 0 hp root .dyn := source_repr (wmod 1)

private theorem reject_memOK : Source.MemOK E0 SH rejectInput := by
  have previous := source_memOK (wmod 1)
  exact ⟨⟨previous.1.1,⟨trivial,previous.1.2⟩⟩,previous.2⟩

private theorem reject_initial : UintArrayAt rejectInput 0 hp root (base root.id) rejectWord rejectBytes := by
  have frame := (initial (wmod 1)).physical.write 4 (wmod 3) (by decide)
  exact ⟨reject_source,reject_repr.heap.arrays root,
    ⟨fun c hc => frame.fits c (.inl hc),fun c hc => frame.cells c (.inl hc)⟩⟩

/-- The late-rejection fixture has two independently typed scalar locals:
old index/RHS1 is valid, new index3 is the exact endpoint. Context extension
uses the published local-cons representation law, with old aliases intact. -/
theorem rejected_suffix_initial :
    UintArrayAt rejectInput 0 hp root (base root.id) rejectWord rejectBytes ∧
    StateRepr 1 1 8 rejectFrag rejectState base rejectWord ∧ Source.MemOK E0 SH rejectInput ∧
    rejectInput.1.get rejectSourceRoot=.memRef rfl 0 ∧
    rejectInput.1.get rejectSourceAlias=.memRef rfl 0 ∧
    rejectInput.1.get rejectSourceIndex=sourceUint (u 1) ∧
    rejectInput.1.get (.here : Source.Idx RejectΓ (.int .u256))=sourceUint (u 3) ∧
    TEnv.get rejectTypedRoot rejectState.env=some root ∧
    TEnv.get rejectTypedAlias rejectState.env=some root ∧
    TEnv.get rejectTypedIndex rejectState.env=u 1 ∧
    TEnv.get (.here : Idx RejectΔ (.val .uint)) rejectState.env=u 3 :=
  ⟨reject_initial,reject_repr,reject_memOK,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.rejected_suffix_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejected_suffix_initial

private def rejectMidWord : Machine := writeMachine rejectWord 10 (.val (wmod 1))
private def rejectMidBytes : Environment.Memory := Environment.writeBytes rejectBytes 320 (Semantics.wordBytes 1)
private def rejectAssignCode : List Evm.Instr := writeLocalCode (C := C) 1 rejectTypedRoot
  (.simple (.local rejectTypedIndex)) (.simple (.local rejectTypedIndex))
private def rejectDeleteCode : List Evm.Instr := deleteLocalCode 1 rejectTypedRoot
  (Evm.compileVal 1 (.simple (.local (.here : Idx RejectΔ (.val .uint))) : Val C RejectΔ .uint))
private def rejectTypedAssign : Stmt C RejectΔ RejectΔ :=
  .assignMem (.index .dyn (.var rejectTypedRoot rfl) (.simple (.local rejectTypedIndex)))
    (.val (.simple (.local rejectTypedIndex)))
private def rejectTypedDelete : Stmt C RejectΔ RejectΔ :=
  .deleteMem (.loc (.index .dyn (.var rejectTypedRoot rfl) (.simple (.local (.here : Idx RejectΔ (.val .uint)))))) rfl

private theorem reject_allocator : StructAllocatorRepr hp base 8 (wmod 24) rejectWord :=
  (initial_allocator (wmod 1)).localWrite 4 (by decide) (by decide) (.val (wmod 3))

private theorem reject_assign_run : Evm.run rejectAssignCode rejectWord=.ok rejectMidWord 0 := by
  have headRun : Evm.run ([.mload 3,.mload 2,.mload 3] : List Evm.Instr) rejectWord=
      .ok (((rejectWord.push (.val (wmod 1))).push (.val (wmod 8))).push (.val (wmod 1))) 0 := by
    have hr : rejectWord.mem 2=.val (wmod 8) := rfl
    have hi : rejectWord.mem 3=.val (wmod 1) := rfl
    simp only [Evm.run,exec_cons_zero,Evm.Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,hr,hi]
  change Evm.run (([.mload 3,.mload 2,.mload 3] : List Evm.Instr) ++ writeArrayStackCode) rejectWord=_
  rw [run_append_ok headRun]
  exact pair_stack_run (reject_repr.heap.arrays root) root_length (wmod 1)

/-- Inhabited late rejection after a MATERIAL prefix, at original runtime nps.
The Source error exposes the changed prefix state; typed/word outcomes erase
suffix state, so none is fabricated. The actual prefix keeps its byte image. -/
theorem rejected_suffix_client (pipeline : Roadmap.Pipeline) (fuel nps : Nat) :
    ∃ (ym : Source.EMState E0 RejectΓ),
      hp.writeAddr (.index root .dyn (u 1)) (u 1)=some pairMid ∧
      (Source.writeLoc (E := E0) (Γ := RejectΓ) F0 (fuel+3) (.mem 0 1) (sourceUint (u 1))).run
        rejectInput=(.ok (),ym) ∧
      (Source.execS (G0 pipeline) F0 (fuel+5) nps none
        (.expr (sourceUintIndexedAssign rejectSourceRoot rejectSourceIndex rejectSourceIndex) :
          Source.RStmt E0 [] false .body RejectΓ RejectΓ) rejectInput.1).run (.nil,rejectInput.2)=
            (.ok (.normal ym.1),(.nil,ym.2)) ∧
      Evm.run rejectAssignCode rejectWord=.ok rejectMidWord 0 ∧
      UintArrayAt ym 0 pairMid root (base root.id) rejectMidWord rejectMidBytes ∧
      StateRepr 1 1 8 rejectFrag (rejectState.withHeap pairMid) base rejectMidWord ∧
      Source.MemOK E0 SH ym ∧ ym.1=rejectInput.1 ∧
      (Source.evalE (G0 pipeline) F0 (fuel+3)
        (sourceUintIndexedDelete rejectSourceRoot (.here : Source.Idx RejectΓ (.int .u256)))).run ym=
          (.error (.revert (Source.panicData .index)),ym) ∧
      (Source.execItems (G0 pipeline) F0 (fuel+6) nps none
        (.stmt (.expr (sourceUintIndexedAssign rejectSourceRoot rejectSourceIndex rejectSourceIndex))
          (.stmt (.expr (sourceUintIndexedDelete rejectSourceRoot (.here : Source.Idx RejectΓ (.int .u256)))) .nil) :
            Source.RItems E0 [] false .body RejectΓ RejectΓ) rejectInput.1).run (.nil,rejectInput.2)=
              (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      pairMid.writeAddr (.index root .dyn (u 3)) (PrimTy.dflt .uint)=none ∧
      Stmt.run (rejectState.withHeap pairMid) rejectTypedDelete=.error .revert ∧
      Prog.run rejectState (.cons rejectTypedAssign (.cons rejectTypedDelete .nil))=.error .revert ∧
      Evm.run rejectDeleteCode rejectMidWord=.revert ∧
      Evm.run (rejectAssignCode ++ rejectDeleteCode) rejectWord=.revert ∧
      (∀ a,a≠0 → ym.2.heap.get a=rejectInput.2.heap.get a) ∧
      ym.2.ex=rejectInput.2.ex ∧ ym.2.events=rejectInput.2.events ∧
      ym.2.logs=rejectInput.2.logs ∧ ym.2.fnLocals=rejectInput.2.fnLocals ∧
      StructAllocatorRepr pairMid base 8 (wmod 24) rejectMidWord ∧
      rejectMidWord.stack=[.val (wmod 77),.val (wmod 88)] := by
  have good : (wmod 1).val<rejectState.heap.len root .dyn := by
    change (wmod 1).val<hp.len root .dyn
    rw [root_length]
    decide
  have bad : rejectState.heap.len root .dyn≤(wmod 3).val := by
    change hp.len root .dyn≤(wmod 3).val
    rw [root_length]
    decide
  obtain ⟨mid,ym,mm,offset,hw,sw,stmt,code,physical,words,mem,locals,stack,alloc,
    exprFail,stmtFail,items,noWrite,typedFail,typedPair,wordFail,append,hoff,byte,exterior,
    typedOther,sourceOther,world,events,logs,fn⟩ :=
    resolved_uint_assign_delete_physical_reject (G0 pipeline) F0 fuel nps rejectState root
      rejectSourceRoot rejectSourceIndex .here rejectSourceIndex
      rejectTypedRoot rejectTypedIndex .here rejectTypedIndex (wmod 1) (wmod 3) (wmod 1)
      rfl rfl rfl rfl rfl rfl rfl rfl good bad reject_initial reject_repr SH reject_memOK
  have midEq : mid=pairMid := Option.some.inj (hw.symm.trans pair_write)
  subst mid
  have wordEq : mm=rejectMidWord := (Evm.Out.ok.inj (code.symm.trans reject_assign_run)).1
  subst mm
  exact ⟨ym,hw,sw,stmt,code,physical,words,mem,locals,exprFail,items,noWrite,typedFail,typedPair,
    wordFail,append,sourceOther,world,events,logs,fn,
    alloc (wmod 24) (by decide) reject_allocator,rfl⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.rejected_suffix_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejected_suffix_client

/-- Complete ordered initial/prefix images. No third image is claimed for
the word revert outcome, which does not return a machine. -/
theorem rejected_suffix_images :
    [MObj.elems .dyn (hp.get root),MObj.elems .dyn (hp.get neighbor),
      MObj.elems .dyn (pairMid.get root),MObj.elems .dyn (pairMid.get neighbor)]=
      [[u 7,u 0,largest],[u 8,u 9],[u 7,u 1,largest],[u 8,u 9]] ∧
    [wordView rejectWord,wordView rejectMidWord]=
      [[.val (wmod 24),.val (wmod 8),.val (wmod 8),.val (wmod 1),.val (wmod 3),.val (wmod 99),
        .val (wmod 3),.val (wmod 7),.val (wmod 0),.val wMax,.val (wmod 55),.val (wmod 2),
        .val (wmod 8),.val (wmod 9),.val (wmod 0),.val (wmod 0)],
       [.val (wmod 24),.val (wmod 8),.val (wmod 8),.val (wmod 1),.val (wmod 3),.val (wmod 99),
        .val (wmod 3),.val (wmod 7),.val (wmod 1),.val wMax,.val (wmod 55),.val (wmod 2),
        .val (wmod 8),.val (wmod 9),.val (wmod 0),.val (wmod 0)]] ∧
    [byteView rejectBytes,byteView rejectMidBytes]=
      [[768,256,256,1,3,99,3,7,0,wMax.val,55,2,8,9,0,0].map Semantics.wordBytes,
       [768,256,256,1,3,99,3,7,1,wMax.val,55,2,8,9,0,0].map Semantics.wordBytes] := by
  refine ⟨?_,rfl,?_⟩
  · simp only [pairMid,Heap.get_set_same,Heap.get_set_ne _ root neighbor (by decide),
      MObj.elems_setElem,MObj.elems_dyn]
    rfl
  · simp only [byteView,List.map_cons,List.map_nil,List.cons.injEq,and_true]
    repeat' apply And.intro
    all_goals
      simp only [bytes,rejectBytes,rejectMidBytes,List.foldl_cons,List.foldl_nil]
      repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length];omega)
      first | exact written_read _ _ _ | rfl

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.rejected_suffix_images' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejected_suffix_images

/-- The actual failed Items program retains exactly its material first Source
state. Full initial/prefix object tables and independent valid alias reads
contrast with the endpoint panic; this is evaluator retention, not rollback. -/
theorem rejected_suffix_observations (pipeline : Roadmap.Pipeline) (fuel nps : Nat) :
    ∃ (ym : Source.EMState E0 RejectΓ),
      (Source.writeLoc (E := E0) (Γ := RejectΓ) F0 (fuel+3) (.mem 0 1) (sourceUint (u 1))).run
        rejectInput=(.ok (),ym) ∧
      (Source.execItems (G0 pipeline) F0 (fuel+6) nps none
        (.stmt (.expr (sourceUintIndexedAssign rejectSourceRoot rejectSourceIndex rejectSourceIndex))
          (.stmt (.expr (sourceUintIndexedDelete rejectSourceRoot (.here : Source.Idx RejectΓ (.int .u256)))) .nil) :
            Source.RItems E0 [] false .body RejectΓ RejectΓ) rejectInput.1).run (.nil,rejectInput.2)=
              (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      Evm.run rejectAssignCode rejectWord=.ok rejectMidWord 0 ∧
      Evm.run (rejectAssignCode ++ rejectDeleteCode) rejectWord=.revert ∧
      UintArrayAt ym 0 pairMid root (base root.id) rejectMidWord rejectMidBytes ∧
      [rejectInput.2.heap.get 0,rejectInput.2.heap.get 1,ym.2.heap.get 0,ym.2.heap.get 1]=
        [some ⟨SA,sourceUintMemory [u 7,u 0,largest]⟩,some ⟨SA,sourceUintMemory [u 8,u 9]⟩,
         some ⟨SA,sourceUintMemory [u 7,u 1,largest]⟩,some ⟨SA,sourceUintMemory [u 8,u 9]⟩] ∧
      ym.1=rejectInput.1 ∧ ym.2={rejectInput.2 with heap:=ym.2.heap} ∧ ym.2.heap.next=2 ∧
      (Source.evalE (G0 pipeline) F0 (fuel+2)
        (.indexArray (.local rejectSourceAlias) (.local rejectSourceIndex) rfl)).run rejectInput=
          (.ok (.val (sourceUint (u 0))),rejectInput) ∧
      (Source.evalE (G0 pipeline) F0 (fuel+2)
        (.indexArray (.local rejectSourceAlias) (.local rejectSourceIndex) rfl)).run ym=
          (.ok (.val (sourceUint (u 1))),ym) ∧
      wordView rejectWord≠wordView rejectMidWord ∧
      Evm.run rejectAssignCode rejectWord≠.ok rejectWord 0 := by
  obtain ⟨ym,hw,sw,stmt,code,physical,words,mem,locals,exprFail,items,noWrite,typedFail,typedPair,
    wordFail,append,other,world,events,logs,fn,alloc,stack⟩ := rejected_suffix_client pipeline fuel nps
  have initialTable : rejectInput.2.heap.get 0=some ⟨SA,sourceUintMemory [u 7,u 0,largest]⟩ := by
    simpa only [SourceUintMemoryAt,MObj.elems_dyn] using reject_source
  have midTable : ym.2.heap.get 0=some ⟨SA,sourceUintMemory [u 7,u 1,largest]⟩ := by
    simpa only [SourceUintMemoryAt,pairMid,Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn] using physical.source
  obtain ⟨ht,known⟩ := source_uint_write rejectInput 0 [u 7,u 0,largest] initialTable 1 (by decide) (u 1)
  have sourceEq := congrArg Prod.snd (sw.symm.trans known)
  dsimp only at sourceEq
  have frame : ym.2={rejectInput.2 with heap:=ym.2.heap} := by rw [sourceEq]
  have next : ym.2.heap.next=2 := by rw [sourceEq];rfl
  have read0 := reject_source.eval_index (G0 pipeline) F0 fuel rejectSourceAlias rejectSourceIndex
    (indexValue (wmod 1)) rfl rfl (by rw [root_length];decide)
  have read1 := physical.source.eval_index (G0 pipeline) F0 fuel rejectSourceAlias rejectSourceIndex
    (indexValue (wmod 1)) (by rw [locals];rfl) (by rw [locals];rfl) (by rw [pair_length];decide)
  refine ⟨ym,sw,items,code,append,physical,?_,locals,frame,next,?_,?_,by decide,?_⟩
  · rw [initialTable,midTable,other 1 (by decide)]
    rfl
  · simpa only [MObj.elems_dyn] using read0
  · simpa only [pairMid,Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn] using read1
  · intro wrong
    have stateEq : rejectWord=rejectMidWord := (Evm.Out.ok.inj (wrong.symm.trans code)).1
    have cell := congrArg (fun m : Machine => m.mem 10) stateEq
    have different : rejectWord.mem 10≠rejectMidWord.mem 10 := by decide
    exact different cell

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.rejected_suffix_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejected_suffix_observations

/-- Only the successful prefix has a byte-store execution. The failed
word suffix supplies no byte machine to restore, and no such state is claimed. -/
theorem rejected_suffix_byte_prefix (tail : List Environment.Word) :
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU 320 (by decide)::lenU 1 (by decide)::tail,rejectBytes⟩=some ⟨tail,rejectMidBytes⟩ ∧
    Environment.readMemory rejectMidBytes 320 32=Semantics.wordBytes 1 ∧
    (∀ a,a<320 ∨ 352≤a → rejectMidBytes a=rejectBytes a) := by
  refine ⟨byte_mstore rejectBytes tail (wmod 10) (wmod 1) (by decide),written_read _ _ _,?_⟩
  intro a outside
  exact Environment.writeBytes_frame _ _ a _ (by simp only [Environment.wordBytes_length];omega)

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.rejected_suffix_byte_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejected_suffix_byte_prefix

private def reverseMid : Heap H := hp.set root (MObj.setElem .dyn (hp.get root) 1 (u 0))
private def reverseOut : Heap H := reverseMid.set root (MObj.setElem .dyn (reverseMid.get root) 1 (u 1))
private def reverseWord : Machine := writeMachine (machine (wmod 1)) 10 (.val (wmod 0))
private def reverseWordOut : Machine := writeMachine reverseWord 10 (.val (wmod 1))
private def reverseBytes : Environment.Memory := Environment.writeBytes (bytes (wmod 1)) 320 (Semantics.wordBytes 0)
private def reverseBytesOut : Environment.Memory := Environment.writeBytes reverseBytes 320 (Semantics.wordBytes 1)

private theorem reverse_delete : hp.writeAddr (.index root .dyn (u 1)) (u 0)=some reverseMid := by
  have hi : (u 1).1.toNat<hp.len root .dyn := by rw [root_length];decide
  change (if (u 1).1.toNat<hp.len root .dyn then some _ else none)=_
  rw [if_pos hi]
  rfl

private theorem reverse_length : reverseMid.len root .dyn=3 := by
  simp only [Heap.len,reverseMid,Heap.get_set_same,MObj.elems_setElem,List.length_set]
  exact root_length

private theorem reverse_write : reverseMid.writeAddr (.index root .dyn (u 1)) (u 1)=some reverseOut := by
  have hi : (u 1).1.toNat<reverseMid.len root .dyn := by rw [reverse_length];decide
  change (if (u 1).1.toNat<reverseMid.len root .dyn then some _ else none)=_
  rw [if_pos hi]
  rfl

private theorem reverse_array : ArrayRepr reverseMid root (base root.id) reverseWord :=
  ((initial_repr (wmod 1)).legacy.heap.arrays root).set 1
    (by change 1<hp.len root .dyn;rw [root_length];decide) (u 0) (.val (wmod 0)) (ReprV.uint_of rfl)

private theorem reverse_delete_run : Evm.run pairDeleteCode (machine (wmod 1))=.ok reverseWord 0 := by
  have headRun : Evm.run ([.push (.val (wmod 0)),.mload 2,.mload 3] : List Evm.Instr) (machine (wmod 1))=
      .ok ((((machine (wmod 1)).push (.val (wmod 0))).push (.val (wmod 8))).push (.val (wmod 1))) 0 := by
    have hr : (machine (wmod 1)).mem 2=.val (wmod 8) := rfl
    have hi : (machine (wmod 1)).mem 3=.val (wmod 1) := rfl
    simp only [Evm.run,exec_cons_zero,Evm.Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,hr,hi]
  change Evm.run (([.push (.val (wmod 0)),.mload 2,.mload 3] : List Evm.Instr) ++ writeArrayStackCode) _=_
  rw [run_append_ok headRun]
  exact pair_stack_run ((initial_repr (wmod 1)).legacy.heap.arrays root) root_length (wmod 0)

private theorem reverse_assign_run : Evm.run pairAssignCode reverseWord=.ok reverseWordOut 0 := by
  have headRun : Evm.run ([.mload 3,.mload 2,.mload 3] : List Evm.Instr) reverseWord=
      .ok (((reverseWord.push (.val (wmod 1))).push (.val (wmod 8))).push (.val (wmod 1))) 0 := by
    have hr : reverseWord.mem 2=.val (wmod 8) := rfl
    have hi : reverseWord.mem 3=.val (wmod 1) := rfl
    simp only [Evm.run,exec_cons_zero,Evm.Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,hr,hi]
  change Evm.run (([.mload 3,.mload 2,.mload 3] : List Evm.Instr) ++ writeArrayStackCode) _=_
  rw [run_append_ok headRun]
  exact pair_stack_run reverse_array reverse_length (wmod 1)

private theorem reverse_source_frames (fuel : Nat) (ym z : Source.EMState E0 Γ)
    (first : (Source.deleteLoc (E := E0) (Γ := Γ) F0 (fuel+3) (τ := .int .u256) (.mem 0 1)).run
      (input (wmod 1))=(.ok (),ym))
    (second : (Source.writeLoc (E := E0) (Γ := Γ) F0 (fuel+2) (.mem 0 1) (sourceUint (u 1))).run ym=(.ok (),z)) :
    ym.1=(input (wmod 1)).1 ∧ z.1=(input (wmod 1)).1 ∧
    ym.2={(input (wmod 1)).2 with heap:=ym.2.heap} ∧
    z.2={(input (wmod 1)).2 with heap:=z.2.heap} ∧
    ym.2.heap.next=2 ∧ z.2.heap.next=2 ∧
    ym.2.heap.get 1=(input (wmod 1)).2.heap.get 1 ∧ z.2.heap.get 1=(input (wmod 1)).2.heap.get 1 := by
  have hr : (input (wmod 1)).2.heap.get 0=some ⟨SA,sourceUintMemory [u 7,u 0,largest]⟩ := by
    simpa only [SourceUintMemoryAt,MObj.elems_dyn] using source_repr (wmod 1)
  obtain ⟨ht1,known1⟩ := source_uint_write (input (wmod 1)) 0 [u 7,u 0,largest] hr 1 (by decide) (u 0)
  have same1 := congrArg Prod.snd (first.symm.trans known1)
  dsimp only at same1
  subst ym
  have reached : ((input (wmod 1)).2.heap.write 0
      (sourceUintMemory ([u 7,u 0,largest].set 1 (u 0))) ht1).get 0=
        some ⟨SA,sourceUintMemory [u 7,u 0,largest]⟩ := Source.Heap.write_get _ _ _ ht1
  obtain ⟨ht2,known2⟩ := source_uint_write
    ((input (wmod 1)).1,{(input (wmod 1)).2 with heap:=((input (wmod 1)).2.heap.write 0
      (sourceUintMemory ([u 7,u 0,largest].set 1 (u 0))) ht1)})
    0 [u 7,u 0,largest] reached 1 (by decide) (u 1)
  have same2 := congrArg Prod.snd (second.symm.trans known2)
  dsimp only at same2
  subst z
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · exact Source.Heap.write_other _ (by decide) _ ht1
  · rw [Source.Heap.write_other _ (by decide) _ ht2]
    exact Source.Heap.write_other _ (by decide) _ ht1

/-- The reverse actual Items/typed/word sequence from the SAME populated
initial heap. Deleting an already-zero slot executes before the assignment;
its final aliased value is one. No stagewise desired relation is a premise. -/
theorem delete_assign_complete (pipeline : Roadmap.Pipeline) (fuel nps : Nat) :
    ∃ (ym z : Source.EMState E0 Γ),
      (Source.deleteLoc (E := E0) (Γ := Γ) F0 (fuel+3) (τ := .int .u256) (.mem 0 1)).run
        (input (wmod 1))=(.ok (),ym) ∧
      (Source.writeLoc (E := E0) (Γ := Γ) F0 (fuel+2) (.mem 0 1) (sourceUint (u 1))).run
        ym=(.ok (),z) ∧
      (Source.execItems (G0 pipeline) F0 (fuel+6) nps none
        (.stmt (.expr (sourceUintIndexedDelete sr si))
          (.stmt (.expr (sourceUintIndexedAssign sr si si)) .nil) : Source.RItems E0 [] false .body Γ Γ)
        (input (wmod 1)).1).run (.nil,(input (wmod 1)).2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      Evm.run pairDeleteCode (machine (wmod 1))=.ok reverseWord 0 ∧
      Evm.run pairAssignCode reverseWord=.ok reverseWordOut 0 ∧
      Evm.run (pairDeleteCode ++ pairAssignCode) (machine (wmod 1))=.ok reverseWordOut 0 ∧
      UintArrayAt ym 0 reverseMid root (base root.id) reverseWord reverseBytes ∧
      UintArrayAt z 0 reverseOut root (base root.id) reverseWordOut reverseBytesOut ∧
      StateRepr 1 1 8 (Frag.init Δ) ((state (wmod 1)).withHeap reverseMid) base reverseWord ∧
      StateRepr 1 1 8 (Frag.init Δ) ((state (wmod 1)).withHeap reverseOut) base reverseWordOut ∧
      Source.MemOK E0 SH ym ∧ Source.MemOK E0 SH z ∧
      ym.1=(input (wmod 1)).1 ∧ z.1=(input (wmod 1)).1 ∧
      ym.2={(input (wmod 1)).2 with heap:=ym.2.heap} ∧
      z.2={(input (wmod 1)).2 with heap:=z.2.heap} ∧
      [ym.2.heap.next,z.2.heap.next]=[2,2] ∧
      [(input (wmod 1)).2.heap.get 0,(input (wmod 1)).2.heap.get 1,
       ym.2.heap.get 0,ym.2.heap.get 1,z.2.heap.get 0,z.2.heap.get 1]=
        [some ⟨SA,sourceUintMemory [u 7,u 0,largest]⟩,some ⟨SA,sourceUintMemory [u 8,u 9]⟩,
         some ⟨SA,sourceUintMemory [u 7,u 0,largest]⟩,some ⟨SA,sourceUintMemory [u 8,u 9]⟩,
         some ⟨SA,sourceUintMemory [u 7,u 1,largest]⟩,some ⟨SA,sourceUintMemory [u 8,u 9]⟩] ∧
      (Source.evalE (G0 pipeline) F0 (fuel+2) (.indexArray (.local sa) (.local si) rfl)).run ym=
        (.ok (.val (sourceUint (u 0))),ym) ∧
      (Source.evalE (G0 pipeline) F0 (fuel+2) (.indexArray (.local sa) (.local si) rfl)).run z=
        (.ok (.val (sourceUint (u 1))),z) ∧
      StructAllocatorRepr reverseOut base 8 (wmod 24) reverseWordOut ∧
      reverseWord.stack=[.val (wmod 77),.val (wmod 88)] ∧
      reverseWordOut.stack=[.val (wmod 77),.val (wmod 88)] := by
  have bound : (wmod 1).val<(state (wmod 1)).heap.len root .dyn := by
    change (wmod 1).val<hp.len root .dyn
    rw [root_length]
    decide
  obtain ⟨mid,out,ym,z,mm,target,offset1,offset2,typed1,typed2,sw1,sw2,stmt1,stmt2,items,
    typed,code1,code2,append,physical1,physical2,words1,words2,mem1,mem2,locals1,locals2,stack,alloc,
    offsetEq1,offsetEq2,byte1,byte2,exterior⟩ :=
    resolved_uint_delete_assign_physical (G0 pipeline) F0 fuel nps (state (wmod 1)) root
      sr si si si tr ti ti ti (wmod 1) (wmod 1) (wmod 1)
      rfl rfl rfl rfl rfl rfl rfl rfl bound bound (initial (wmod 1))
      (initial_repr (wmod 1)).legacy SH (source_memOK (wmod 1))
  have midEq : mid=reverseMid := Option.some.inj (typed1.symm.trans reverse_delete)
  subst mid
  have outEq : out=reverseOut := Option.some.inj (typed2.symm.trans reverse_write)
  subst out
  have mmEq : mm=reverseWord := (Evm.Out.ok.inj (code1.symm.trans reverse_delete_run)).1
  subst mm
  have targetEq : target=reverseWordOut := (Evm.Out.ok.inj (code2.symm.trans reverse_assign_run)).1
  subst target
  obtain ⟨_,_,frame1,frame2,next1,next2,other1,other2⟩ := reverse_source_frames fuel ym z sw1 sw2
  have initialTable : (input (wmod 1)).2.heap.get 0=some ⟨SA,sourceUintMemory [u 7,u 0,largest]⟩ := by
    simpa only [SourceUintMemoryAt,MObj.elems_dyn] using source_repr (wmod 1)
  have midTable : ym.2.heap.get 0=some ⟨SA,sourceUintMemory [u 7,u 0,largest]⟩ := by
    simpa only [SourceUintMemoryAt,reverseMid,Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn] using physical1.source
  have finalTable : z.2.heap.get 0=some ⟨SA,sourceUintMemory [u 7,u 1,largest]⟩ := by
    simpa only [SourceUintMemoryAt,reverseOut,reverseMid,Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn] using physical2.source
  have read1 := physical1.source.eval_index (G0 pipeline) F0 fuel sa si (indexValue (wmod 1))
    (by rw [locals1];rfl) (by rw [locals1];rfl) (by rw [reverse_length];decide)
  have outLength : reverseOut.len root .dyn=3 := by
    simp only [Heap.len,reverseOut,Heap.get_set_same,MObj.elems_setElem,List.length_set]
    exact reverse_length
  have read2 := physical2.source.eval_index (G0 pipeline) F0 fuel sa si (indexValue (wmod 1))
    (by rw [locals2];rfl) (by rw [locals2];rfl) (by rw [outLength];decide)
  refine ⟨ym,z,sw1,sw2,items,code1,code2,append,physical1,physical2,words1,words2,mem1,mem2,
    locals1,locals2,frame1,frame2,?_,?_,?_,?_,alloc (wmod 24) (by decide) (initial_allocator (wmod 1)),rfl,rfl⟩
  · rw [next1,next2]
  · rw [initialTable,midTable,finalTable,other1,other2]
    rfl
  · simpa only [reverseMid,Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn] using read1
  · simpa only [reverseOut,reverseMid,Heap.get_set_same,MObj.elems_setElem,MObj.elems_dyn] using read2

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.delete_assign_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms delete_assign_complete

/-- Complete reverse execution images, including the no-op zero deletion
and the material later assignment, both objects and all16 word/byte cells. -/
theorem delete_assign_images :
    [MObj.elems .dyn (hp.get root),MObj.elems .dyn (hp.get neighbor),
     MObj.elems .dyn (reverseMid.get root),MObj.elems .dyn (reverseMid.get neighbor),
     MObj.elems .dyn (reverseOut.get root),MObj.elems .dyn (reverseOut.get neighbor)]=
      [[u 7,u 0,largest],[u 8,u 9],[u 7,u 0,largest],[u 8,u 9],[u 7,u 1,largest],[u 8,u 9]] ∧
    [wordView (machine (wmod 1)),wordView reverseWord,wordView reverseWordOut]=
      [[.val (wmod 24),.val (wmod 8),.val (wmod 8),.val (wmod 1),.val (wmod 0),.val (wmod 99),
        .val (wmod 3),.val (wmod 7),.val (wmod 0),.val wMax,.val (wmod 55),.val (wmod 2),
        .val (wmod 8),.val (wmod 9),.val (wmod 0),.val (wmod 0)],
       [.val (wmod 24),.val (wmod 8),.val (wmod 8),.val (wmod 1),.val (wmod 0),.val (wmod 99),
        .val (wmod 3),.val (wmod 7),.val (wmod 0),.val wMax,.val (wmod 55),.val (wmod 2),
        .val (wmod 8),.val (wmod 9),.val (wmod 0),.val (wmod 0)],
       [.val (wmod 24),.val (wmod 8),.val (wmod 8),.val (wmod 1),.val (wmod 0),.val (wmod 99),
        .val (wmod 3),.val (wmod 7),.val (wmod 1),.val wMax,.val (wmod 55),.val (wmod 2),
        .val (wmod 8),.val (wmod 9),.val (wmod 0),.val (wmod 0)]] ∧
    [byteView (bytes (wmod 1)),byteView reverseBytes,byteView reverseBytesOut]=
      [[768,256,256,1,0,99,3,7,0,wMax.val,55,2,8,9,0,0].map Semantics.wordBytes,
       [768,256,256,1,0,99,3,7,0,wMax.val,55,2,8,9,0,0].map Semantics.wordBytes,
       [768,256,256,1,0,99,3,7,1,wMax.val,55,2,8,9,0,0].map Semantics.wordBytes] := by
  refine ⟨?_,rfl,?_⟩
  · simp only [reverseOut,reverseMid,Heap.get_set_same,Heap.get_set_ne _ root neighbor (by decide),
      MObj.elems_setElem,MObj.elems_dyn]
    rfl
  · simp only [byteView,List.map_cons,List.map_nil,List.cons.injEq,and_true]
    repeat' apply And.intro
    all_goals
      simp only [bytes,reverseBytes,reverseBytesOut,List.foldl_cons,List.foldl_nil]
      repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length];omega)
      first | exact written_read _ _ _ | rfl

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.delete_assign_images' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms delete_assign_images

/-- Both actual whole programs start from the SAME full input bundle, but
reversing their order changes the old-alias read and complete target/byte image.
This refutes an unconditional commutation claim, not a Source admission rule. -/
theorem actual_order_discriminates (pipeline : Roadmap.Pipeline) (fuel nps : Nat) :
    ∃ (zf zr : Source.EMState E0 Γ),
      (Source.execItems (G0 pipeline) F0 (fuel+6) nps none
        (.stmt (.expr (sourceUintIndexedAssign sr si si))
          (.stmt (.expr (sourceUintIndexedDelete sr si)) .nil) : Source.RItems E0 [] false .body Γ Γ)
        (input (wmod 1)).1).run (.nil,(input (wmod 1)).2)=(.ok (.normal zf.1),(.nil,zf.2)) ∧
      (Source.execItems (G0 pipeline) F0 (fuel+6) nps none
        (.stmt (.expr (sourceUintIndexedDelete sr si))
          (.stmt (.expr (sourceUintIndexedAssign sr si si)) .nil) : Source.RItems E0 [] false .body Γ Γ)
        (input (wmod 1)).1).run (.nil,(input (wmod 1)).2)=(.ok (.normal zr.1),(.nil,zr.2)) ∧
      Evm.run (pairAssignCode ++ pairDeleteCode) (machine (wmod 1))=.ok pairWordOut 0 ∧
      Evm.run (pairDeleteCode ++ pairAssignCode) (machine (wmod 1))=.ok reverseWordOut 0 ∧
      UintArrayAt zf 0 pairOut root (base root.id) pairWordOut pairBytesOut ∧
      UintArrayAt zr 0 reverseOut root (base root.id) reverseWordOut reverseBytesOut ∧
      (Source.evalE (G0 pipeline) F0 (fuel+2) (.indexArray (.local sa) (.local si) rfl)).run zf=
        (.ok (.val (sourceUint (u 0))),zf) ∧
      (Source.evalE (G0 pipeline) F0 (fuel+2) (.indexArray (.local sa) (.local si) rfl)).run zr=
        (.ok (.val (sourceUint (u 1))),zr) ∧
      sourceUint (D := E0.layout) (u 0)≠sourceUint (u 1) ∧
      wordView pairWordOut≠wordView reverseWordOut ∧ byteView pairBytesOut≠byteView reverseBytesOut := by
  obtain ⟨ymf,zf,swf1,swf2,itemsf,codef1,codef2,appendf,physicalf1,physicalf2,wordsf1,wordsf2,
    memf1,memf2,localsf1,localsf2,framef1,framef2,nextf,tablef,readf1,readf2,allocf,stackf1,stackf2⟩ :=
    assignment_delete_complete pipeline fuel nps
  obtain ⟨ymr,zr,swr1,swr2,itemsr,coder1,coder2,appendr,physicalr1,physicalr2,wordsr1,wordsr2,
    memr1,memr2,localsr1,localsr2,framer1,framer2,nextr,tabler,readr1,readr2,allocr,stackr1,stackr2⟩ :=
    delete_assign_complete pipeline fuel nps
  refine ⟨zf,zr,itemsf,itemsr,appendf,appendr,physicalf2,physicalr2,readf2,readr2,?_,by decide,?_⟩
  · intro same
    have converted := congrArg (fun v : Source.Val E0.layout (.int .u256) => calldataUint (.val v)) same
    have unequal : u 0=u 1 := by simpa only [calldataUint_sourceUint] using converted
    have impossible : (0 : Int)=1 := congrArg Subtype.val unequal
    omega
  · have forward : Environment.readMemory pairBytesOut 320 32=Semantics.wordBytes 0 := written_read _ _ _
    have reverse : Environment.readMemory reverseBytesOut 320 32=Semantics.wordBytes 1 := written_read _ _ _
    intro same
    have cell := congrArg (fun xs : List (List UInt8) => xs[8]?) same
    change some (Environment.readMemory pairBytesOut 320 32)=some (Environment.readMemory reverseBytesOut 320 32) at cell
    have equal := Option.some.inj cell
    rw [forward,reverse] at equal
    have different : Semantics.wordBytes 0≠Semantics.wordBytes 1 := by decide
    exact different equal

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.actual_order_discriminates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms actual_order_discriminates

/-- Both actual scaled stores for the reverse operation, using its reached
first byte image; this is not a whole word-pointer-to-byte compiler theorem. -/
theorem delete_assign_byte_steps (tail : List Environment.Word) :
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU 320 (by decide)::lenU 0 (by decide)::tail,bytes (wmod 1)⟩=some ⟨tail,reverseBytes⟩ ∧
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU 320 (by decide)::lenU 1 (by decide)::tail,reverseBytes⟩=some ⟨tail,reverseBytesOut⟩ ∧
    (∀ a,a<320 ∨ 352≤a → reverseBytesOut a=bytes (wmod 1) a) := by
  refine ⟨byte_mstore (bytes (wmod 1)) tail (wmod 10) (wmod 0) (by decide),
    byte_mstore reverseBytes tail (wmod 10) (wmod 1) (by decide),?_⟩
  intro a outside
  have second : reverseBytesOut a=reverseBytes a :=
    Environment.writeBytes_frame _ _ a _ (by simp only [Environment.wordBytes_length];omega)
  have first : reverseBytes a=bytes (wmod 1) a :=
    Environment.writeBytes_frame _ _ a _ (by simp only [Environment.wordBytes_length];omega)
  exact second.trans first

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.delete_assign_byte_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms delete_assign_byte_steps

private def disjointInput : Source.EMState E0 RejectΓ :=
  (.cons (sourceUint (u 0)) (input (wmod 1)).1,(input (wmod 1)).2)
private def disjointState : State C RejectΔ := (state (wmod 1)).push (t := .val .uint) (u 0)
private def disjointWord : Machine := writeMachine (machine (wmod 1)) 4 (.val (wmod 0))
private def disjointBytes : Environment.Memory := Environment.writeBytes (bytes (wmod 1)) 128 (Semantics.wordBytes 0)
private def disjointFWord : Machine := writeMachine disjointWord 10 (.val (wmod 1))
private def disjointFOut : Machine := writeMachine disjointFWord 9 (.val (wmod 0))
private def disjointRWord : Machine := writeMachine disjointWord 9 (.val (wmod 0))
private def disjointROut : Machine := writeMachine disjointRWord 10 (.val (wmod 1))
private def disjointFBytes : Environment.Memory := Environment.writeBytes disjointBytes 320 (Semantics.wordBytes 1)
private def disjointRBytes : Environment.Memory := Environment.writeBytes disjointBytes 288 (Semantics.wordBytes 0)
private def disjointOutBytes : Environment.Memory := Environment.writeBytes disjointFBytes 288 (Semantics.wordBytes 0)

private theorem disjoint_repr : StateRepr 1 1 8 rejectFrag disjointState base disjointWord :=
  (initial_repr (wmod 1)).legacy.consVal (u 0) (.val (wmod 0)) (ReprV.uint_of rfl) (by decide)
private theorem disjoint_source : SourceUintMemoryAt disjointInput 0 hp root .dyn := source_repr (wmod 1)
private theorem disjoint_memOK : Source.MemOK E0 SH disjointInput := by
  have previous := source_memOK (wmod 1)
  exact ⟨⟨previous.1.1,⟨trivial,previous.1.2⟩⟩,previous.2⟩
private theorem disjoint_initial : UintArrayAt disjointInput 0 hp root (base root.id) disjointWord disjointBytes := by
  have frame := (initial (wmod 1)).physical.write 4 (wmod 0) (by decide)
  exact ⟨disjoint_source,disjoint_repr.heap.arrays root,
    ⟨fun c hc => frame.fits c (.inl hc),fun c hc => frame.cells c (.inl hc)⟩⟩
private theorem disjoint_allocator : StructAllocatorRepr hp base 8 (wmod 24) disjointWord :=
  (initial_allocator (wmod 1)).localWrite 4 (by decide) (by decide) (.val (wmod 0))

private theorem disjoint_assign_run {hp' : Heap H} {m : Machine}
    (arr : ArrayRepr hp' root (base root.id) m) (hlen : hp'.len root .dyn=3)
    (hroot : m.mem 2=.val (wmod 8)) (hindex : m.mem 3=.val (wmod 1)) :
    Evm.run rejectAssignCode m=.ok (writeMachine m 10 (.val (wmod 1))) 0 := by
  have headRun : Evm.run ([.mload 3,.mload 2,.mload 3] : List Evm.Instr) m=
      .ok (((m.push (.val (wmod 1))).push (.val (wmod 8))).push (.val (wmod 1))) 0 := by
    simp only [Evm.run,exec_cons_zero,Evm.Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,hroot,hindex]
  change Evm.run (([.mload 3,.mload 2,.mload 3] : List Evm.Instr) ++ writeArrayStackCode) m=_
  rw [run_append_ok headRun]
  exact pair_stack_run arr hlen (wmod 1)

private theorem disjoint_zero_stack {hp' : Heap H} {m : Machine}
    (arr : ArrayRepr hp' root (base root.id) m) (hlen : hp'.len root .dyn=3) :
    Evm.run writeArrayStackCode (((m.push (.val (wmod 0))).push (.val (wmod 8))).push (.val (wmod 0)))=
      .ok (writeMachine m 9 (.val (wmod 0))) 0 := by
  rcases writeArray_correct arr (wmod 0) (u 0) (.val (wmod 0))
      (ReprV.uint_of rfl) with ⟨out,ht,hw,_⟩ | ⟨bad,_⟩
  · rw [writeArrayStackCode,
      arrayStack_append_eq (m.push (.val (wmod 0))) (wmod 8) (wmod 0) 3 (by decide)
        (by simpa only [hlen] using arr.length),←writeArrayCode]
    exact hw
  · have hi : (u 0).1.toNat<hp'.len root .dyn := by rw [hlen];decide
    change (if (u 0).1.toNat<hp'.len root .dyn then some _ else none)=none at bad
    rw [if_pos hi] at bad
    cases bad

private theorem disjoint_delete_run {hp' : Heap H} {m : Machine}
    (arr : ArrayRepr hp' root (base root.id) m) (hlen : hp'.len root .dyn=3)
    (hroot : m.mem 2=.val (wmod 8)) (hindex : m.mem 4=.val (wmod 0)) :
    Evm.run rejectDeleteCode m=.ok (writeMachine m 9 (.val (wmod 0))) 0 := by
  have headRun : Evm.run ([.push (.val (wmod 0)),.mload 2,.mload 4] : List Evm.Instr) m=
      .ok (((m.push (.val (wmod 0))).push (.val (wmod 8))).push (.val (wmod 0))) 0 := by
    simp only [Evm.run,exec_cons_zero,Evm.Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,hroot,hindex]
  change Evm.run (([.push (.val (wmod 0)),.mload 2,.mload 4] : List Evm.Instr) ++ writeArrayStackCode) m=_
  rw [run_append_ok headRun]
  exact disjoint_zero_stack arr hlen

private theorem disjoint_source_frame {Γx : Source.RCtx} {y z : Source.EMState E0 Γx}
    {hp' : Heap H} (hr : SourceUintMemoryAt y 0 hp' root .dyn) (fuel : Nat)
    (i v : PrimTy.uint.Denote) (bound : i.1.toNat<hp'.len root .dyn)
    (run : (Source.writeLoc (E := E0) (Γ := Γx) F0 fuel (.mem 0 i.1.toNat) (sourceUint v)).run y=(.ok (),z)) :
    z.2={y.2 with heap:=z.2.heap} ∧ z.2.heap.next=y.2.heap.next := by
  obtain ⟨ht,known⟩ := source_uint_write y 0 _ hr i.1.toNat bound v
  have same := congrArg Prod.snd (run.symm.trans known)
  dsimp only at same
  constructor
  · rw [same]
  · rw [same];rfl

/-- Both operations materially change DIFFERENT cells (index1 and index0).
Both complete Source/typed/word programs execute from the SAME represented
input; their physical finals use one derived common byte buffer. -/
theorem disjoint_orders_complete (pipeline : Roadmap.Pipeline) (fuel nps : Nat) :
    ∃ (midF outF midR outR : Heap H) (ymF zF ymR zR : Source.EMState E0 RejectΓ),
      (Source.writeLoc (E := E0) (Γ := RejectΓ) F0 (fuel+3) (.mem 0 1) (sourceUint (u 1))).run disjointInput=(.ok (),ymF) ∧
      (Source.deleteLoc (E := E0) (Γ := RejectΓ) F0 (fuel+2) (τ := .int .u256) (.mem 0 0)).run ymF=(.ok (),zF) ∧
      (Source.deleteLoc (E := E0) (Γ := RejectΓ) F0 (fuel+3) (τ := .int .u256) (.mem 0 0)).run disjointInput=(.ok (),ymR) ∧
      (Source.writeLoc (E := E0) (Γ := RejectΓ) F0 (fuel+2) (.mem 0 1) (sourceUint (u 1))).run ymR=(.ok (),zR) ∧
      (Source.execItems (G0 pipeline) F0 (fuel+6) nps none
        (.stmt (.expr (sourceUintIndexedAssign rejectSourceRoot rejectSourceIndex rejectSourceIndex))
          (.stmt (.expr (sourceUintIndexedDelete rejectSourceRoot (.here : Source.Idx RejectΓ (.int .u256)))) .nil) :
            Source.RItems E0 [] false .body RejectΓ RejectΓ) disjointInput.1).run (.nil,disjointInput.2)=
              (.ok (.normal zF.1),(.nil,zF.2)) ∧
      (Source.execItems (G0 pipeline) F0 (fuel+6) nps none
        (.stmt (.expr (sourceUintIndexedDelete rejectSourceRoot (.here : Source.Idx RejectΓ (.int .u256))))
          (.stmt (.expr (sourceUintIndexedAssign rejectSourceRoot rejectSourceIndex rejectSourceIndex)) .nil) :
            Source.RItems E0 [] false .body RejectΓ RejectΓ) disjointInput.1).run (.nil,disjointInput.2)=
              (.ok (.normal zR.1),(.nil,zR.2)) ∧
      Prog.run disjointState (.cons rejectTypedAssign (.cons rejectTypedDelete .nil))=.ok ⟨disjointState.withHeap outF,List.prefix_refl _⟩ ∧
      Prog.run disjointState (.cons rejectTypedDelete (.cons rejectTypedAssign .nil))=.ok ⟨disjointState.withHeap outR,List.prefix_refl _⟩ ∧
      Evm.run rejectAssignCode disjointWord=.ok disjointFWord 0 ∧
      Evm.run rejectDeleteCode disjointFWord=.ok disjointFOut 0 ∧
      Evm.run rejectDeleteCode disjointWord=.ok disjointRWord 0 ∧
      Evm.run rejectAssignCode disjointRWord=.ok disjointROut 0 ∧
      Evm.run (rejectAssignCode ++ rejectDeleteCode) disjointWord=.ok disjointFOut 0 ∧
      Evm.run (rejectDeleteCode ++ rejectAssignCode) disjointWord=.ok disjointROut 0 ∧
      UintArrayAt ymF 0 midF root (base root.id) disjointFWord disjointFBytes ∧
      UintArrayAt zF 0 outF root (base root.id) disjointFOut disjointOutBytes ∧
      UintArrayAt ymR 0 midR root (base root.id) disjointRWord disjointRBytes ∧
      UintArrayAt zR 0 outR root (base root.id) disjointROut disjointOutBytes ∧
      StateRepr 1 1 8 rejectFrag (disjointState.withHeap midF) base disjointFWord ∧
      StateRepr 1 1 8 rejectFrag (disjointState.withHeap outF) base disjointFOut ∧
      StateRepr 1 1 8 rejectFrag (disjointState.withHeap midR) base disjointRWord ∧
      StateRepr 1 1 8 rejectFrag (disjointState.withHeap outR) base disjointROut ∧
      Source.MemOK E0 SH ymF ∧ Source.MemOK E0 SH zF ∧ Source.MemOK E0 SH ymR ∧ Source.MemOK E0 SH zR ∧
      ymF.1=disjointInput.1 ∧ zF.1=disjointInput.1 ∧ ymR.1=disjointInput.1 ∧ zR.1=disjointInput.1 ∧
      ymF.2={disjointInput.2 with heap:=ymF.2.heap} ∧ zF.2={disjointInput.2 with heap:=zF.2.heap} ∧
      ymR.2={disjointInput.2 with heap:=ymR.2.heap} ∧ zR.2={disjointInput.2 with heap:=zR.2.heap} ∧
      [ymF.2.heap.next,zF.2.heap.next,ymR.2.heap.next,zR.2.heap.next]=[2,2,2,2] ∧
      [MObj.elems .dyn (hp.get root),MObj.elems .dyn (hp.get neighbor),
       MObj.elems .dyn (midF.get root),MObj.elems .dyn (midF.get neighbor),
       MObj.elems .dyn (outF.get root),MObj.elems .dyn (outF.get neighbor),
       MObj.elems .dyn (midR.get root),MObj.elems .dyn (midR.get neighbor),
       MObj.elems .dyn (outR.get root),MObj.elems .dyn (outR.get neighbor)]=
        [[u 7,u 0,largest],[u 8,u 9],[u 7,u 1,largest],[u 8,u 9],[u 0,u 1,largest],[u 8,u 9],
         [u 0,u 0,largest],[u 8,u 9],[u 0,u 1,largest],[u 8,u 9]] ∧
      [disjointInput.2.heap.get 0,disjointInput.2.heap.get 1,ymF.2.heap.get 0,ymF.2.heap.get 1,zF.2.heap.get 0,zF.2.heap.get 1,
       ymR.2.heap.get 0,ymR.2.heap.get 1,zR.2.heap.get 0,zR.2.heap.get 1]=
        [some ⟨SA,sourceUintMemory [u 7,u 0,largest]⟩,some ⟨SA,sourceUintMemory [u 8,u 9]⟩,
         some ⟨SA,sourceUintMemory [u 7,u 1,largest]⟩,some ⟨SA,sourceUintMemory [u 8,u 9]⟩,
         some ⟨SA,sourceUintMemory [u 0,u 1,largest]⟩,some ⟨SA,sourceUintMemory [u 8,u 9]⟩,
         some ⟨SA,sourceUintMemory [u 0,u 0,largest]⟩,some ⟨SA,sourceUintMemory [u 8,u 9]⟩,
         some ⟨SA,sourceUintMemory [u 0,u 1,largest]⟩,some ⟨SA,sourceUintMemory [u 8,u 9]⟩] ∧
      (Source.evalE (G0 pipeline) F0 (fuel+2) (.indexArray (.local rejectSourceAlias) (.local rejectSourceIndex) rfl)).run zF=
        (.ok (.val (sourceUint (u 1))),zF) ∧
      (Source.evalE (G0 pipeline) F0 (fuel+2) (.indexArray (.local rejectSourceAlias) (.local rejectSourceIndex) rfl)).run zR=
        (.ok (.val (sourceUint (u 1))),zR) ∧
      (∀ {Q : RefTy} (q : HRef H Q),root.id≠q.id → outF.get q=hp.get q ∧ outR.get q=hp.get q) ∧
      (∀ a,a≠0 → zF.2.heap.get a=disjointInput.2.heap.get a ∧ zR.2.heap.get a=disjointInput.2.heap.get a) ∧
      StructAllocatorRepr outF base 8 (wmod 24) disjointFOut ∧ StructAllocatorRepr outR base 8 (wmod 24) disjointROut := by
  have good1 : (wmod 1).val<disjointState.heap.len root .dyn := by change (wmod 1).val<hp.len root .dyn;rw [root_length];decide
  have good0 : (wmod 0).val<disjointState.heap.len root .dyn := by change (wmod 0).val<hp.len root .dyn;rw [root_length];decide
  obtain ⟨midF,outF,midR,outR,ymF,zF,ymR,zR,mmF,tF,mmR,tR,
    fw1,fw2,rw1,rw2,swF1,swF2,swR1,swR2,itemsF,itemsR,typedF,typedR,
    codeF1,codeF2,codeR1,codeR2,appendF,appendR,physicalF1,physicalF2,physicalR1,physicalR2,
    wordsF1,wordsF2,wordsR1,wordsR2,memF1,memF2,memR1,memR2,locF1,locF2,locR1,locR2,stackF,stackR,allocF,allocR⟩ :=
    resolved_uint_disjoint_orders (G0 pipeline) F0 fuel nps disjointState root
      rejectSourceRoot rejectSourceIndex .here rejectSourceIndex rejectTypedRoot rejectTypedIndex .here rejectTypedIndex
      (wmod 1) (wmod 0) (wmod 1) rfl rfl rfl rfl rfl rfl rfl rfl good1 good0
      disjoint_initial disjoint_repr SH disjoint_memOK (by decide)
  have lenF : midF.len root .dyn=3 := by
    change (MObj.elems .dyn (midF.get root)).length=3
    rw [indexedWrite_elems hp midF root .dyn (u 1) (u 1) fw1,List.length_set]
    exact root_length
  have lenR : midR.len root .dyn=3 := by
    change (MObj.elems .dyn (midR.get root)).length=3
    rw [indexedWrite_elems hp midR root .dyn (u 0) (u 0) rw1,List.length_set]
    exact root_length
  have firstF : mmF=disjointFWord := (Evm.Out.ok.inj (codeF1.symm.trans
    (disjoint_assign_run (disjoint_repr.heap.arrays root) root_length rfl rfl))).1
  subst mmF
  have finalF : tF=disjointFOut := (Evm.Out.ok.inj (codeF2.symm.trans
    (disjoint_delete_run (wordsF1.heap.arrays root) lenF rfl rfl))).1
  subst tF
  have firstR : mmR=disjointRWord := (Evm.Out.ok.inj (codeR1.symm.trans
    (disjoint_delete_run (disjoint_repr.heap.arrays root) root_length rfl rfl))).1
  subst mmR
  have finalR : tR=disjointROut := (Evm.Out.ok.inj (codeR2.symm.trans
    (disjoint_assign_run (wordsR1.heap.arrays root) lenR rfl rfl))).1
  subst tR
  have f1 := disjoint_source_frame disjoint_source (fuel+3) (u 1) (u 1) good1 swF1
  have f2 := disjoint_source_frame physicalF1.source (fuel+2) (u 0) (u 0) (by rw [lenF];decide) swF2
  have r1 := disjoint_source_frame disjoint_source (fuel+3) (u 0) (u 0) good0 swR1
  have r2 := disjoint_source_frame physicalR1.source (fuel+2) (u 1) (u 1) (by rw [lenR];decide) swR2
  have frameF : zF.2={disjointInput.2 with heap:=zF.2.heap} := by rw [f2.1,f1.1]
  have frameR : zR.2={disjointInput.2 with heap:=zR.2.heap} := by rw [r2.1,r1.1]
  have root0 : MObj.elems .dyn (hp.get root)=[u 7,u 0,largest] := by simp only [Heap.get,Objs.get,hp,root,MObj.elems_dyn]
  have n0 : MObj.elems .dyn (hp.get neighbor)=[u 8,u 9] := by simp only [Heap.get,Objs.get,hp,neighbor,MObj.elems_dyn]
  have mf : MObj.elems .dyn (midF.get root)=[u 7,u 1,largest] := by rw [indexedWrite_elems hp midF root .dyn (u 1) (u 1) fw1,root0];rfl
  have finalElemsF : MObj.elems .dyn (outF.get root)=[u 0,u 1,largest] := by rw [indexedWrite_elems midF outF root .dyn (u 0) (u 0) fw2,mf];rfl
  have mr : MObj.elems .dyn (midR.get root)=[u 0,u 0,largest] := by rw [indexedWrite_elems hp midR root .dyn (u 0) (u 0) rw1,root0];rfl
  have finalElemsR : MObj.elems .dyn (outR.get root)=[u 0,u 1,largest] := by rw [indexedWrite_elems midR outR root .dyn (u 1) (u 1) rw2,mr];rfl
  have nf1 := indexedWrite_frame hp midF root .dyn (u 1) (u 1) fw1 neighbor (by decide)
  have nf2 := (indexedWrite_frame midF outF root .dyn (u 0) (u 0) fw2 neighbor (by decide)).trans nf1
  have nr1 := indexedWrite_frame hp midR root .dyn (u 0) (u 0) rw1 neighbor (by decide)
  have nr2 := (indexedWrite_frame midR outR root .dyn (u 1) (u 1) rw2 neighbor (by decide)).trans nr1
  have sf1 := disjoint_source.write_frames F0 (fuel+3) (u 1) (u 1) good1 fw1 swF1
  have sf2 := physicalF1.source.write_frames F0 (fuel+2) (u 0) (u 0) (by rw [lenF];decide) fw2 swF2
  have sr1 := disjoint_source.write_frames F0 (fuel+3) (u 0) (u 0) good0 rw1 swR1
  have sr2 := physicalR1.source.write_frames F0 (fuel+2) (u 1) (u 1) (by rw [lenR];decide) rw2 swR2
  have source0 : disjointInput.2.heap.get 0=some ⟨SA,sourceUintMemory [u 7,u 0,largest]⟩ := by simpa only [SourceUintMemoryAt,root0] using disjoint_source
  have sourceMF : ymF.2.heap.get 0=some ⟨SA,sourceUintMemory [u 7,u 1,largest]⟩ := by simpa only [SourceUintMemoryAt,mf] using physicalF1.source
  have sourceOF : zF.2.heap.get 0=some ⟨SA,sourceUintMemory [u 0,u 1,largest]⟩ := by simpa only [SourceUintMemoryAt,finalElemsF] using physicalF2.source
  have sourceMR : ymR.2.heap.get 0=some ⟨SA,sourceUintMemory [u 0,u 0,largest]⟩ := by simpa only [SourceUintMemoryAt,mr] using physicalR1.source
  have sourceOR : zR.2.heap.get 0=some ⟨SA,sourceUintMemory [u 0,u 1,largest]⟩ := by simpa only [SourceUintMemoryAt,finalElemsR] using physicalR2.source
  have boundF : (u 1).1.toNat<outF.len root .dyn := by change (u 1).1.toNat<(MObj.elems .dyn (outF.get root)).length;rw [finalElemsF];decide
  have boundR : (u 1).1.toNat<outR.len root .dyn := by change (u 1).1.toNat<(MObj.elems .dyn (outR.get root)).length;rw [finalElemsR];decide
  have readF := physicalF2.source.eval_index (G0 pipeline) F0 fuel rejectSourceAlias rejectSourceIndex (u 1) (by rw [locF2];rfl) (by rw [locF2];rfl) boundF
  have readR := physicalR2.source.eval_index (G0 pipeline) F0 fuel rejectSourceAlias rejectSourceIndex (u 1) (by rw [locR2];rfl) (by rw [locR2];rfl) boundR
  refine ⟨midF,outF,midR,outR,ymF,zF,ymR,zR,swF1,swF2,swR1,swR2,itemsF,itemsR,typedF,typedR,
    codeF1,codeF2,codeR1,codeR2,appendF,appendR,physicalF1,physicalF2,physicalR1,physicalR2,
    wordsF1,wordsF2,wordsR1,wordsR2,memF1,memF2,memR1,memR2,locF1,locF2,locR1,locR2,f1.1,frameF,r1.1,frameR,?_,?_,?_,?_,?_,?_,?_,
    allocF (wmod 24) (by decide) disjoint_allocator,allocR (wmod 24) (by decide) disjoint_allocator⟩
  · rw [f2.2,f1.2,r2.2,r1.2]
    rfl
  · rw [root0,nf1,nf2,nr1,nr2,n0,mf,finalElemsF,mr,finalElemsR]
  · rw [source0,sourceMF,sourceOF,sourceMR,sourceOR,sf2.2.2.1 1 (by decide),sf1.2.2.1 1 (by decide),
      sr2.2.2.1 1 (by decide),sr1.2.2.1 1 (by decide)]
    rfl
  · simpa only [finalElemsF] using readF
  · simpa only [finalElemsR] using readR
  · intro Q q separated
    exact ⟨(sf2.2.1 q separated).trans (sf1.2.1 q separated),(sr2.2.1 q separated).trans (sr1.2.1 q separated)⟩
  · intro a separated
    exact ⟨(sf2.2.2.1 a separated).trans (sf1.2.2.1 a separated),(sr2.2.2.1 a separated).trans (sr1.2.2.1 a separated)⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.disjoint_orders_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms disjoint_orders_complete

private def disjointReverseOutBytes : Environment.Memory := Environment.writeBytes disjointRBytes 320 (Semantics.wordBytes 1)

/-- Both actual orders have complete5-stage word/byte image vectors. Every
single operation is material; final equality is derived for the entire byte
function, while whole Source/word-machine equality is deliberately not claimed. -/
theorem disjoint_order_images :
    disjointOutBytes=disjointReverseOutBytes ∧
    [wordView disjointWord,wordView disjointFWord,wordView disjointFOut,wordView disjointRWord,wordView disjointROut]=
      [
        [.val (wmod 24),.val (wmod 8),.val (wmod 8),.val (wmod 1),.val (wmod 0),.val (wmod 99),.val (wmod 3),.val (wmod 7),.val (wmod 0),.val wMax,.val (wmod 55),.val (wmod 2),.val (wmod 8),.val (wmod 9),.val (wmod 0),.val (wmod 0)],
        [.val (wmod 24),.val (wmod 8),.val (wmod 8),.val (wmod 1),.val (wmod 0),.val (wmod 99),.val (wmod 3),.val (wmod 7),.val (wmod 1),.val wMax,.val (wmod 55),.val (wmod 2),.val (wmod 8),.val (wmod 9),.val (wmod 0),.val (wmod 0)],
        [.val (wmod 24),.val (wmod 8),.val (wmod 8),.val (wmod 1),.val (wmod 0),.val (wmod 99),.val (wmod 3),.val (wmod 0),.val (wmod 1),.val wMax,.val (wmod 55),.val (wmod 2),.val (wmod 8),.val (wmod 9),.val (wmod 0),.val (wmod 0)],
        [.val (wmod 24),.val (wmod 8),.val (wmod 8),.val (wmod 1),.val (wmod 0),.val (wmod 99),.val (wmod 3),.val (wmod 0),.val (wmod 0),.val wMax,.val (wmod 55),.val (wmod 2),.val (wmod 8),.val (wmod 9),.val (wmod 0),.val (wmod 0)],
        [.val (wmod 24),.val (wmod 8),.val (wmod 8),.val (wmod 1),.val (wmod 0),.val (wmod 99),.val (wmod 3),.val (wmod 0),.val (wmod 1),.val wMax,.val (wmod 55),.val (wmod 2),.val (wmod 8),.val (wmod 9),.val (wmod 0),.val (wmod 0)]] ∧
    [byteView disjointBytes,byteView disjointFBytes,byteView disjointOutBytes,byteView disjointRBytes,byteView disjointReverseOutBytes]=
      [
        [768,256,256,1,0,99,3,7,0,wMax.val,55,2,8,9,0,0].map Semantics.wordBytes,
        [768,256,256,1,0,99,3,7,1,wMax.val,55,2,8,9,0,0].map Semantics.wordBytes,
        [768,256,256,1,0,99,3,0,1,wMax.val,55,2,8,9,0,0].map Semantics.wordBytes,
        [768,256,256,1,0,99,3,0,0,wMax.val,55,2,8,9,0,0].map Semantics.wordBytes,
        [768,256,256,1,0,99,3,0,1,wMax.val,55,2,8,9,0,0].map Semantics.wordBytes] ∧
    wordView disjointWord≠wordView disjointFWord ∧ wordView disjointFWord≠wordView disjointFOut ∧
    wordView disjointWord≠wordView disjointRWord ∧ wordView disjointRWord≠wordView disjointROut ∧
    disjointFOut.stack=[.val (wmod 77),.val (wmod 88)] ∧ disjointROut.stack=[.val (wmod 77),.val (wmod 88)] := by
  refine ⟨word_stores_commute disjointBytes 10 9 (wmod 1) (wmod 0) (by decide),rfl,?_,
    by decide,by decide,by decide,by decide,rfl,rfl⟩
  simp only [byteView,List.map_cons,List.map_nil,List.cons.injEq,and_true]
  repeat' apply And.intro
  all_goals
    simp only [bytes,disjointBytes,disjointFBytes,disjointOutBytes,disjointRBytes,disjointReverseOutBytes,List.foldl_cons,List.foldl_nil]
    repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length];omega)
    first | exact written_read _ _ _ | rfl

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.disjoint_order_images' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms disjoint_order_images

/-- Both real scaled byte traces at touching-but-disjoint word spans. Each
second store consumes its own actual first image, and their finals agree. -/
theorem disjoint_order_byte_steps (tail : List Environment.Word) :
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU 320 (by decide)::lenU 1 (by decide)::tail,disjointBytes⟩=some ⟨tail,disjointFBytes⟩ ∧
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU 288 (by decide)::lenU 0 (by decide)::tail,disjointFBytes⟩=some ⟨tail,disjointOutBytes⟩ ∧
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU 288 (by decide)::lenU 0 (by decide)::tail,disjointBytes⟩=some ⟨tail,disjointRBytes⟩ ∧
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU 320 (by decide)::lenU 1 (by decide)::tail,disjointRBytes⟩=some ⟨tail,disjointReverseOutBytes⟩ ∧
    disjointOutBytes=disjointReverseOutBytes ∧
    (∀ a,a<288 ∨ 352≤a → disjointOutBytes a=disjointBytes a) := by
  refine ⟨byte_mstore disjointBytes tail (wmod 10) (wmod 1) (by decide),
    byte_mstore disjointFBytes tail (wmod 9) (wmod 0) (by decide),
    byte_mstore disjointBytes tail (wmod 9) (wmod 0) (by decide),
    byte_mstore disjointRBytes tail (wmod 10) (wmod 1) (by decide),
    word_stores_commute disjointBytes 10 9 (wmod 1) (wmod 0) (by decide),?_⟩
  intro a outside
  have second : disjointOutBytes a=disjointFBytes a :=
    Environment.writeBytes_frame _ _ a _ (by simp only [Environment.wordBytes_length];omega)
  have first : disjointFBytes a=disjointBytes a :=
    Environment.writeBytes_frame _ _ a _ (by simp only [Environment.wordBytes_length];omega)
  exact second.trans first

/-- info: 'Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls.disjoint_order_byte_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms disjoint_order_byte_steps

end Solidity.Backend.MemoryOps.Physical.ResolvedDeleteControls
