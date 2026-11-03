import Solidity.Backend.MemoryOps.PhysicalStructChild
import Solidity.Backend.MemoryOps.PhysicalStructReference
import Solidity.Backend.MemoryOps.PhysicalStructSequence
import Solidity.Backend.MemoryOps.PhysicalStructDelete
import Solidity.Backend.MemoryOps.PhysicalStructAlias
import Solidity.Backend.MemoryOps.SourceCalldataCopy
import Solidity.Backend.MemoryOps.SourceCalldataTransfer
import Solidity.Backend.MemoryOps.SourceCalldataBinding
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

/-! Populated named-struct/Boolean-child physical controls. INITIAL fixture
objects and proofs are reused from this task's preserved original checkpoint;
only published interfaces are imported, and no constructor/compiler is added. -/
namespace Solidity.Backend.MemoryOps.Physical.StructChildControls
open Semantics Evm Evm.Memory
open Source.SemanticsExamples (F0)
private def C : Contract := {vars := []}
private def S : Name := "FlagBox{tag:uint;items:bool[]}"
private abbrev B : RefTy := .array (.prim .bool)
private abbrev H : HTy := [B,B,.struct S]
private def left : HRef H B := ⟨0,rfl⟩
private def right : HRef H B := ⟨1,rfl⟩
private def parent : HRef H (.struct S) := ⟨2,rfl⟩
private def u7 : PrimTy.uint.Denote := indexValue ⟨7,by decide⟩
private def hp : Heap H := (⟨[true,false,false],by decide⟩,(⟨[false,true,false],by decide⟩,((u7,(left,())),())))
private abbrev Γ : Ctx := [.mem (.struct S),.mem B,.mem B,.mem (.struct S)]
private def σ : State C Γ := {storage := Storage.init C,H := H,heap := hp,env := (some parent,(some right,(some left,(some parent,()))))}
private def base (i : Nat) : Fin W := if i=0 then ⟨16,by decide⟩ else if i=1 then ⟨24,by decide⟩ else ⟨32,by decide⟩
private def machine : Machine := {Machine.init with stack := [w[42]],mem := fun a =>
  if a=0 then w[48] else if a=1 then w[32] else if a=2 then w[16] else if a=3 then w[24] else if a=4 then w[32] else if a=7 then w[99]
  else if a=16 then w[3] else if a=17 then w[1] else if a=24 then w[3] else if a=26 then w[1]
  else if a=32 then w[7] else if a=33 then w[16] else w[0]}
private def dn : Source.DeclName := ⟨none,"FlagBox"⟩
private def decl : Source.Decl :=
  ⟨.struct,"FlagBox",none,true,.struct "FlagBox"
    (.structMember (.elem (.int false 256 (by decide))) "tag")
    (.cons (.structMember (.array (.elem .bool) .none) "items") .nil)⟩
private def E : Source.Env := ⟨[decl]⟩
private def layout : SourceBoolStructLayout E dn S "tag" "items" := ⟨rfl,rfl,by decide⟩
private abbrev SB : Source.STy := SourceBoolArrayTy
private abbrev SS : Source.STy := .struct .memory dn
private abbrev SΓ : Source.RCtx := [SS,SB,SB,SS]
private def G (p : Roadmap.Pipeline) : Source.Glob E :=
  ⟨{body _ := none,consts _ := none,inits _ := [],ctor _ := none,ctorLocals _ := [],baseArgs _ := [],contracts := []},
    p,Source.SemanticsExamples.toyFixed,fun _ => Source.SemanticsExamples.word 0,fun _ _ => false,
    fun _ => .answer (.success []),Source.SemanticsExamples.word 0⟩
private def y0 : Source.EMState E [] := (.nil,Source.St.init E)
private def yl : Source.EMState E [] := ((Source.allocRef (sourceBoolMemory [true,false,false])).run y0).2
private def yr : Source.EMState E [] := ((Source.allocRef (sourceBoolMemory [false,true,false])).run yl).2
private def data (a : Nat) : Source.Data E.layout SS := sourceBoolStructData dn layout.source_types u7 a
private def yp : Source.EMState E [] := ((Source.allocRef (data 0)).run yr).2
private def sy : Source.EMState E SΓ :=
  (.cons (.memRef rfl 2) (.cons (.memRef rfl 1) (.cons (.memRef rfl 0) (.cons (.memRef rfl 2) .nil))),yp.2)
private def addresses (i : Nat) := i
private def SH : Source.HeapTy := (Source.Heap.empty : Source.Heap E.layout).ty
private theorem prim_refs {p : PrimTy} (q : HRef H (.array (.prim p))) : p=.bool ∧ (HEq q left ∨ HEq q right) := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi;exact ⟨rfl,.inl HEq.rfl⟩
  | succ i => cases i with
    | zero => cases hi;exact ⟨rfl,.inr HEq.rfl⟩
    | succ i => cases i with
      | zero => cases hi
      | succ i => cases hi
private theorem struct_refs {s : Name} (q : HRef H (.struct s)) : s=S ∧ HEq q parent := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi
  | succ i => cases i with
    | zero => cases hi
    | succ i => cases i with
      | zero => cases hi;exact ⟨rfl,HEq.rfl⟩
      | succ i => cases hi
private theorem left_repr : ArrayRepr hp left (base left.id) machine := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Heap.len,Heap.get,Objs.get,hp,left,MObj.elems_dyn] using (show 16+1+3≤W from by decide)
  · simpa only [Heap.len,Heap.get,Objs.get,hp,left,MObj.elems_dyn] using (show machine.mem 16=.val (wmod 3) from rfl)
  · intro i v hi
    simp only [Heap.get,Objs.get,hp,left,MObj.elems_dyn] at hi
    cases i with
    | zero => cases Option.some.inj hi;rfl
    | succ i => cases i with
      | zero => cases Option.some.inj hi;rfl
      | succ i => cases i with
        | zero => cases Option.some.inj hi;rfl
        | succ i => cases hi
private theorem right_repr : ArrayRepr hp right (base right.id) machine := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Heap.len,Heap.get,Objs.get,hp,right,MObj.elems_dyn] using (show 24+1+3≤W from by decide)
  · simpa only [Heap.len,Heap.get,Objs.get,hp,right,MObj.elems_dyn] using (show machine.mem 24=.val (wmod 3) from rfl)
  · intro i v hi
    simp only [Heap.get,Objs.get,hp,right,MObj.elems_dyn] at hi
    cases i with
    | zero => cases Option.some.inj hi;rfl
    | succ i => cases i with
      | zero => cases Option.some.inj hi;rfl
      | succ i => cases i with
        | zero => cases Option.some.inj hi;rfl
        | succ i => cases hi
private theorem parent_repr : StructRepr hp parent (base parent.id) machine := by
  refine ⟨by change 32+2≤W;decide,?_⟩
  intro f p hf
  rw [layout.target_fields] at hf
  by_cases he : f="tag"
  · subst f
    cases hf
    exact ReprV.uint_of rfl
  · by_cases hc : f="items"
    · subst f
      simp only [lookupBy,he,↓reduceIte] at hf
      cases hf
    · simp only [lookupBy,he,hc,↓reduceIte] at hf
      cases hf
private theorem initial_repr : StateRepr 1 1 8 (Frag.init Γ) σ base machine := by
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨?_,?_,?_,by decide,?_,?_,?_⟩
  · refine ⟨hc.store,?_,?_,hc.net,hc.netSelf,hc.bound,?_,hc.env,hc.funds,hc.oracle⟩
    all_goals intro p i;cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
  · refine ⟨?_,?_,?_⟩
    · intro p q;obtain ⟨rfl,hq|hq⟩ := prim_refs q <;> cases hq
      · exact left_repr
      · exact right_repr
    · intro p q;obtain ⟨rfl,hq|hq⟩ := prim_refs q <;> cases hq <;> decide
    · intro p t q z hne
      obtain ⟨rfl,hq|hq⟩ := prim_refs q <;> cases hq
      all_goals obtain ⟨rfl,hz|hz⟩ := prim_refs z <;> cases hz
      all_goals first | exact (hne rfl).elim | (simp only [Heap.len,Heap.get,left,right,MObj.elems_dyn] <;> decide)
  · intro Q i
    cases i with
    | here => exact ⟨parent,rfl,rfl⟩
    | there i => cases i with
      | here => exact ⟨right,rfl,rfl⟩
      | there i => cases i with
        | here => exact ⟨left,rfl,rfl⟩
        | there i => cases i with
          | here => exact ⟨parent,rfl,rfl⟩
          | there i => nomatch i
  · refine ⟨?_,?_,?_⟩
    · intro s q;obtain ⟨rfl,hq⟩ := struct_refs q;cases hq;exact parent_repr
    · intro s q;obtain ⟨rfl,hq⟩ := struct_refs q;cases hq;decide
    · intro s t q r hne
      obtain ⟨rfl,hq⟩ := struct_refs q;cases hq
      obtain ⟨rfl,hr⟩ := struct_refs r;cases hr
      exact (hne rfl).elim
  · intro p s q r
    obtain ⟨rfl,hq|hq⟩ := prim_refs q <;> cases hq
    all_goals obtain ⟨rfl,hr⟩ := struct_refs r;cases hr
    all_goals exact .inl (by simp only [Heap.len,Heap.get,left,right,MObj.elems_dyn];decide)
  · intro s f R q hf
    obtain ⟨rfl,hq⟩ := struct_refs q;cases hq
    rw [layout.target_fields] at hf
    by_cases ht : f="tag"
    · subst f;cases hf
    · by_cases he : f="items"
      · subst f
        simp only [lookupBy,ht,↓reduceIte] at hf
        cases hf
        rfl
      · simp only [lookupBy,ht,he,↓reduceIte] at hf
        cases hf
private theorem source_memOK : Source.MemOK E SH sy := by
  have h0 : Source.MemOK E SH y0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have hl := source_bool_alloc_memOK (E := E) (Γ := []) SH [true,false,false] y0 h0
  rw [show (Source.allocRef (E := E) (Γ := []) (sourceBoolMemory [true,false,false])).run y0=(.ok (.memRef rfl 0),yl) from rfl] at hl
  have hr := source_bool_alloc_memOK (E := E) (Γ := []) SH [false,true,false] yl hl.1
  rw [show (Source.allocRef (E := E) (Γ := []) (sourceBoolMemory [false,true,false])).run yl=(.ok (.memRef rfl 1),yr) from rfl] at hr
  have hd : Source.DataOK E yr.2.heap.ty (data 0) := by
    change Source.DataOK E yr.2.heap.ty (Source.Data.struct (D := E.layout) (l := .memory) (d := dn) (.cons (.val (sourceUint u7)) (.cons (.val (.memRef (τ := SB) rfl 0)) .nil)))
    exact .struct (.cons (.val (Source.Val.refOK_of_loc (τ := .int .u256) rfl _)) (.cons (.val ⟨SB,rfl,rfl⟩) .nil))
  have hi : Source.Data.Inner (E := E) (data 0) := by
    change (∃ v,Source.Data.val (sourceUint (D := E.layout) u7)=.val v) ∧
      (∃ v,Source.Data.val (Source.Val.memRef (D := E.layout) (τ := SB) rfl 0)=.val v) ∧ True
    exact ⟨⟨_,rfl⟩,⟨_,rfl⟩,trivial⟩
  have ha := Source.allocRef_mem' (E := E) (Γ := []) (H := SH) (data 0) (by trivial) hi yr ⟨hr.1,hd⟩
  rw [show (Source.allocRef (E := E) (Γ := []) (data 0)).run yr=(.ok (.memRef rfl 2),yp) from rfl] at ha
  exact ⟨⟨ha.1.1.1,⟨⟨SS,rfl,rfl⟩,⟨⟨SB,rfl,rfl⟩,⟨⟨SB,rfl,rfl⟩,⟨⟨SS,rfl,rfl⟩,trivial⟩⟩⟩⟩⟩,ha.1.2⟩
private theorem left_at : SourceBoolMemoryAt sy 0 hp left .dyn := by
  unfold SourceBoolMemoryAt;simp only [Heap.get,Objs.get,hp,left,MObj.elems_dyn];rfl
private theorem right_at : SourceBoolMemoryAt sy 1 hp right .dyn := by
  unfold SourceBoolMemoryAt;simp only [Heap.get,Objs.get,hp,right,MObj.elems_dyn];rfl
private theorem initial_at : SourceBoolStructAt sy 2 hp parent addresses layout := by
  refine ⟨?_,?_⟩
  · rfl
  · exact left_at

private theorem initial_allocator : StructAllocatorRepr hp base 8 ⟨48,by decide⟩ machine := by
  refine ⟨⟨initial_repr.heap,⟨by decide,by decide,rfl,?_⟩,?_⟩,
    initial_repr.structs,initial_repr.separated,?_⟩
  · intro addr ha
    change 48≤addr at ha
    change (if addr=0 then w[48] else if addr=1 then w[32] else if addr=2 then w[16] else if addr=3 then w[24] else if addr=4 then w[32] else if addr=7 then w[99]
      else if addr=16 then w[3] else if addr=17 then w[1] else if addr=24 then w[3] else if addr=26 then w[1]
      else if addr=32 then w[7] else if addr=33 then w[16] else w[0])=w[0]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),
      if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  · intro p q
    obtain ⟨rfl,hq|hq⟩ := prim_refs q <;> cases hq
    all_goals simp only [Heap.len,Heap.get,Objs.get,hp,left,right,base,MObj.elems_dyn] <;> decide
  · intro s q
    obtain ⟨rfl,hq⟩ := struct_refs q;cases hq
    change 32+2≤48;decide

private abbrev Δ : Ctx := .val .bool :: .val .uint :: Γ
private abbrev SourceCtx : Source.RCtx := .bool :: .int .u256 :: SΓ
private def withIndex : State C (.val .uint :: Γ) := σ.push (t := .val .uint) (Evm.Memory.indexValue (wmod 1))
private def inputState : State C Δ := withIndex.push (t := .val .bool) true
private def wordIndex : Machine := writeMachine machine 5 (.val (wmod 1))
private def inputWord : Machine := writeMachine wordIndex 6 (.val (bword true))
private def inputSource : Source.EMState E SourceCtx := (.cons (.bool true) (.cons (sourceUint (indexValue (wmod 1))) sy.1),sy.2)
private def sroot : Source.Idx SourceCtx SS := .there (.there .here)
private def si : Source.Idx SourceCtx (.int .u256) := .there .here
private def sv : Source.Idx SourceCtx .bool := .here
private def troot : Idx Δ (.mem (.struct S)) := .there (.there .here)
private def ti : Idx Δ (.val .uint) := .there .here
private def tv : Idx Δ (.val .bool) := .here
private def salias : Source.Idx SourceCtx SB := .there (.there (.there (.there .here)))
private def bytes : Environment.Memory :=
  [(0,1536),(1,1024),(2,512),(3,768),(4,1024),(5,1),(6,1),(7,99),
    (16,3),(17,1),(18,0),(19,0),(24,3),(25,0),(26,1),(27,0),(32,7),(33,512)].foldl
    (fun m p => Environment.writeBytes m (32*p.1) (Semantics.wordBytes p.2)) (fun _ => 0)

private theorem repr : StateRepr 1 1 8 ((Frag.init Γ).push (.val .uint) .ok |>.push (.val .bool) .ok)
    inputState base inputWord :=
  (initial_repr.consVal (indexValue (wmod 1)) (.val (wmod 1)) (ReprV.uint_of rfl) (by decide)).consVal (p := .bool)
    true (.val (bword true)) rfl (by decide)
private theorem source_at : SourceBoolStructAt inputSource 2 hp parent addresses layout := initial_at.same_heaps rfl rfl
private theorem memOK : Source.MemOK E SH inputSource :=
  ⟨⟨source_memOK.1.1,⟨trivial,⟨trivial,source_memOK.1.2⟩⟩⟩,source_memOK.2⟩
private theorem allocator : StructAllocatorRepr hp base 8 ⟨48,by decide⟩ inputWord :=
  ((initial_allocator.localWrite 5 (by decide) (by decide) (.val (wmod 1))).localWrite 6
    (by decide) (by decide) (.val (bword true)))
private theorem written_read (m : Environment.Memory) (a w : Nat) :
    Environment.readMemory (Environment.writeBytes m a (Semantics.wordBytes w)) a 32=Semantics.wordBytes w := by
  simpa only [Environment.wordBytes_length] using Environment.read_written (Semantics.wordBytes w) a m

private theorem child_frame : WordFrame inputWord bytes
    (fun c => (base left.id).val≤c ∧ c<(base left.id).val+1+hp.len left .dyn) := by
  have lenLeft : hp.len left .dyn=3 := by simp only [Heap.len,Heap.get,Objs.get,hp,left,MObj.elems_dyn,List.length_cons,List.length_nil]
  constructor
  · intro c hc
    rw [lenLeft] at hc
    change 16≤c ∧ c<16+1+3 at hc
    change 32*c+32≤2^256
    omega
  · intro c hc
    rw [lenLeft] at hc
    change 16≤c ∧ c<16+1+3 at hc
    have casesC : c=16 ∨ c=17 ∨ c=18 ∨ c=19 := by omega
    rcases casesC with rfl | rfl | rfl | rfl
    all_goals
      refine ⟨_,rfl,?_⟩
      simp only [bytes,List.foldl_cons,List.foldl_nil]
      repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length];omega)
      exact written_read _ _ _

/-- Existing named parent/tag and two nonuniform children, repeated old
aliases, actual scalar locals, word allocator and physical child are inhabited. -/
theorem initial_bundle : SourceBoolStructAt inputSource 2 hp parent addresses layout ∧
    Source.MemOK E SH inputSource ∧
    StateRepr 1 1 8 ((Frag.init Γ).push (.val .uint) .ok |>.push (.val .bool) .ok) inputState base inputWord ∧
    StructAllocatorRepr hp base 8 ⟨48,by decide⟩ inputWord ∧
    WordFrame inputWord bytes (fun c => (base left.id).val≤c ∧ c<(base left.id).val+1+hp.len left .dyn) :=
  ⟨source_at,memOK,repr,allocator,child_frame⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.initial_bundle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial_bundle

private def index : PrimTy.uint.Denote := indexValue (wmod 1)
private def outputHeap : Heap H := hp.set left (MObj.setElem .dyn (hp.get left) 1 true)
private def outputWord : Machine := writeMachine inputWord 18 (.val (bword true))
private def outputBytes : Environment.Memory := Environment.writeBytes bytes 576 (Semantics.wordBytes 1)
private def code : List Evm.Instr := structChildWriteCode (C := C) 1 troot "items" (.simple (.local ti)) (.simple (.local tv))
private theorem left_length : hp.len left .dyn=3 := by
  simp only [Heap.len,Heap.get,Objs.get,hp,left,MObj.elems_dyn,List.length_cons,List.length_nil]
private theorem expected_write : hp.writeAddr (.index left .dyn index) true=some outputHeap := by
  have bound : index.1.toNat<hp.len left .dyn := by rw [left_length];decide
  change (if index.1.toNat<hp.len left .dyn then some _ else none)=_
  rw [if_pos bound]
  rfl

private theorem firstRun : Evm.run ([.mload 6,.mload 4] : List Evm.Instr) inputWord=
    .ok ((inputWord.push (.val (bword true))).push (.val (wmod 32))) 0 := by
  have hv : inputWord.mem 6=.val (bword true) := rfl
  have hp : inputWord.mem 4=.val (wmod 32) := rfl
  simp only [Evm.run,exec_cons_zero,Evm.Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,hv,hp]

private theorem fieldRun : Evm.run (readFieldCode 1) ((inputWord.push (.val (bword true))).push (.val (wmod 32)))=
    .ok ((inputWord.push (.val (bword true))).push (.val (wmod 16))) 0 := by
  rw [readFieldCode,run_append_ok (fieldAddr_run (inputWord.push (.val (bword true))) (wmod 32) 1)]
  rfl

private theorem pointerRun : Evm.run (([.mload 6,.mload 4] : List Evm.Instr) ++ readFieldCode 1) inputWord=
    .ok ((inputWord.push (.val (bword true))).push (.val (wmod 16))) 0 := by
  rw [run_append_ok firstRun]
  exact fieldRun

private theorem headRun : Evm.run ((([.mload 6,.mload 4] : List Evm.Instr) ++ readFieldCode 1) ++ [.mload 5]) inputWord=
    .ok (((inputWord.push (.val (bword true))).push (.val (wmod 16))).push (.val (wmod 1))) 0 := by
  rw [run_append_ok pointerRun]
  rfl

private theorem code_eq : code=((([.mload 6,.mload 4] : List Evm.Instr) ++ readFieldCode 1) ++ [.mload 5]) ++ writeArrayStackCode := by
  unfold code structChildWriteCode
  have offset : fieldOffset (structDef S) "items"=1 := by rw [layout.target_fields];decide
  rw [offset]
  rfl

private theorem expected_word_run : Evm.run code inputWord=.ok outputWord 0 := by
  rw [code_eq,run_append_ok headRun]
  rcases writeArray_correct (repr.heap.arrays left) (wmod 1) true (.val (bword true)) rfl with
    ⟨out,ht,hw,_⟩ | ⟨bad,_⟩
  · rw [writeArrayStackCode,
      arrayStack_append_eq (inputWord.push (.val (bword true))) (wmod 16) (wmod 1) 3 (by decide) (by rfl),←writeArrayCode]
    exact hw
  · change hp.writeAddr (.index left .dyn index) true=none at bad
    rw [expected_write] at bad
    cases bad

private theorem map_free : (Ty.ref (.struct S)).mapFree=true := by decide

/-- Independently inhabited INITIAL inputs derive the actual named-member
assignment and complete word-pointer path, with the physical child frame at
that SAME returned machine. Both original pipelines and runtime nps are kept. -/
theorem named_child_client (p : Roadmap.Pipeline) (fuel nps : Nat) :
    ∃ (z : Source.EMState E SourceCtx),
      (Source.writeLoc (E := E) (Γ := SourceCtx) F0 (fuel+3) (.mem 0 1) (.bool true)).run inputSource=(.ok (),z) ∧
      (Source.evalE (G p) F0 (fuel+4) (sourceStructChildAssign layout sroot si sv)).run inputSource=(.ok (.val (.bool true)),z) ∧
      (Source.execS (G p) F0 (fuel+5) nps none
        (.expr (sourceStructChildAssign layout sroot si sv) : Source.RStmt E [] false .body SourceCtx SourceCtx)
        inputSource.1).run (.nil,inputSource.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      Stmt.run inputState (.assignMem (.index .dyn (.loc (.field (.var troot map_free) "items" layout.child_type))
        (.simple (.local ti))) (.val (.simple (.local tv))))=.ok ⟨inputState.withHeap outputHeap,List.prefix_refl _⟩ ∧
      Evm.run code inputWord=.ok outputWord 0 ∧
      SourceBoolStructAt z 2 outputHeap parent addresses layout ∧ Source.MemOK E SH z ∧
      StateRepr 1 1 8 ((Frag.init Γ).push (.val .uint) .ok |>.push (.val .bool) .ok)
        (inputState.withHeap outputHeap) base outputWord ∧
      WordFrame outputWord outputBytes (fun c => (base left.id).val≤c ∧ c<(base left.id).val+1+outputHeap.len left .dyn) ∧
      Environment.cryptoStep (.op .MSTORE)
        ⟨lenU 576 (by decide)::lenU 1 (by decide)::[lenU 11 (by decide),lenU 22 (by decide)],bytes⟩=
          some ⟨[lenU 11 (by decide),lenU 22 (by decide)],outputBytes⟩ ∧
      (∀ j,j<576 ∨ 608≤j → outputBytes j=bytes j) ∧
      outputHeap.get parent=hp.get parent ∧ outputHeap.field parent layout.child_type=left ∧
      outputHeap.field parent layout.tag_type=u7 ∧ z.2.heap.get 2=inputSource.2.heap.get 2 ∧
      z.1=inputSource.1 ∧ outputWord.stack=inputWord.stack ∧
      StructAllocatorRepr outputHeap base 8 ⟨48,by decide⟩ outputWord ∧
      (∀ {R : RefTy} (q : HRef H R),left.id≠q.id → outputHeap.get q=hp.get q) ∧
      (∀ a,a≠0 → z.2.heap.get a=inputSource.2.heap.get a) ∧
      z.2.ex=inputSource.2.ex ∧ z.2.events=inputSource.2.events ∧ z.2.logs=inputSource.2.logs ∧ z.2.fnLocals=inputSource.2.fnLocals := by
  have bound : index.1.toNat<hp.len left .dyn := by rw [left_length];decide
  obtain ⟨out,z,target,offset,ht,hs,he,hstmt,typed,hword,hsource,hm,hrepr,hphysical,hoff,hbyte,hread,hexterior,
    hparent,hchild,htag,hsourceParent,hloc,hstack,halloc,hother,hsourceOther,hworld,hevents,hlogs,hfn⟩ :=
    assign_struct_child_physical layout (G p) F0 fuel nps inputState parent addresses source_at
      sroot si sv troot (.simple (.local ti)) (.simple (.local tv)) index true
      rfl rfl rfl rfl rfl rfl map_free bound SH memOK repr rfl rfl bytes child_frame
  have sameHeap : out=outputHeap := Option.some.inj (ht.symm.trans expected_write)
  subst out
  have sameWord : target=outputWord := (Out.ok.inj (hword.symm.trans expected_word_run)).1
  subst target
  have offsetEq : offset=⟨576,by decide⟩ := Fin.ext hoff
  subst offset
  refine ⟨z,hs,he,hstmt,typed,hword,hsource,hm,hrepr,hphysical,?_,hexterior,hparent,hchild,htag,hsourceParent,hloc,hstack,
    halloc ⟨48,by decide⟩ (by decide) allocator,hother,hsourceOther,hworld,hevents,hlogs,hfn⟩
  exact hbyte [lenU 11 (by decide),lenU 22 (by decide)]

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_child_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_child_client

/-- Complete represented word-cell vectors, including locals, free pointer,
neighbor, both headers/all payload cells, tag and selected pointer. -/
theorem complete_word_vectors :
    [0,1,2,3,4,5,6,7,16,17,18,19,24,25,26,27,32,33].map inputWord.mem=
      [w[48],w[32],w[16],w[24],w[32],w[1],w[1],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[16]] ∧
    [0,1,2,3,4,5,6,7,16,17,18,19,24,25,26,27,32,33].map outputWord.mem=
      [w[48],w[32],w[16],w[24],w[32],w[1],w[1],w[99],w[3],w[1],w[1],w[0],w[3],w[0],w[1],w[0],w[7],w[16]] := by
  first | rfl | decide

private theorem left_values : MObj.elems .dyn (hp.get left)=[true,false,false] := by
  simp only [Heap.get,Objs.get,hp,left,MObj.elems_dyn]
private theorem right_values : MObj.elems .dyn (hp.get right)=[false,true,false] := by
  simp only [Heap.get,Objs.get,hp,right,MObj.elems_dyn]
private theorem final_left : MObj.elems .dyn (outputHeap.get left)=[true,true,false] := by
  simp only [outputHeap,Heap.get_set_same,MObj.elems_setElem,left_values,List.set]
private theorem final_right : MObj.elems .dyn (outputHeap.get right)=[false,true,false] := by
  rw [outputHeap,Heap.get_set_ne hp left right (by decide),right_values]

/-- The full Source object table and retained alias are observed at the SAME
state returned by the actual assignment, not an independently chosen heap. -/
theorem reached_source_observations (p : Roadmap.Pipeline) (fuel nps : Nat) :
    ∃ z : Source.EMState E SourceCtx,
      (Source.execS (G p) F0 (fuel+5) nps none
        (.expr (sourceStructChildAssign layout sroot si sv) : Source.RStmt E [] false .body SourceCtx SourceCtx)
        inputSource.1).run (.nil,inputSource.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      [inputSource.2.heap.get 0,inputSource.2.heap.get 1,inputSource.2.heap.get 2]=
        [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 0⟩] ∧
      [z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2]=
        [some ⟨SB,sourceBoolMemory [true,true,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 0⟩] ∧
      z.1.get salias=.memRef rfl 0 ∧
      (Source.readLoc (E := E) (Γ := SourceCtx) F0 (τ := .bool) (.mem 0 1)).run z=(.ok (.bool true),z) ∧
      (Source.evalE (G p) F0 (fuel+3) (sourceStructChildRead layout sroot si)).run z=(.ok (.val (.bool true)),z) ∧
      Evm.run (code ++ structChildReadCode (C := C) 1 troot "items" (.simple (.local ti))) inputWord=
        .ok (outputWord.push (.val (bword true))) 0 ∧
      ¬ SourceBoolMemoryAt z 0 hp left .dyn := by
  obtain ⟨z,_,_,hs,_,hw,hr,_,hm,_,_,_,_,_,_,_,hloc,_,_,_,hother,_,_,_,_⟩ := named_child_client p fuel nps
  have hz0 : z.2.heap.get 0=some ⟨SB,sourceBoolMemory [true,true,false]⟩ := by
    have h := hr.leaf
    change z.2.heap.get 0=some ⟨SB,sourceBoolMemory (MObj.elems .dyn (outputHeap.get left))⟩ at h
    simpa only [final_left] using h
  have hz1 : z.2.heap.get 1=some ⟨SB,sourceBoolMemory [false,true,false]⟩ := by rw [hother 1 (by decide)];rfl
  have hz2 : z.2.heap.get 2=some ⟨SS,data 0⟩ := by rw [hother 2 (by decide)];rfl
  have hit : outputHeap.index left .dyn index=some true := by
    change (MObj.elems .dyn (outputHeap.get left))[index.1.toNat]?=some true
    rw [final_left];rfl
  have hrRead := hr.read_child_word layout (G p) F0 fuel (inputState.withHeap outputHeap) parent addresses
    sroot si troot (.simple (.local ti)) index true
    (by rw [hloc];rfl) (by rw [hloc];rfl) rfl rfl map_free hit hm rfl
  have oldRead : hp.index left .dyn index=some false := by
    change (MObj.elems .dyn (hp.get left))[index.1.toNat]?=some false
    rw [left_values];rfl
  refine ⟨z,hs,?_,?_,?_,?_,hrRead.1,?_,?_⟩
  · first | rfl | decide
  · rw [hz0,hz1,hz2]
  · rw [hloc];rfl
  · exact (hr.leaf.read_iff F0 index true).mpr hit
  · rw [run_append_ok hw];exact hrRead.2
  · intro stale
    have hn := (stale.read_iff F0 index false).mpr oldRead
    have ht := (hr.leaf.read_iff F0 index true).mpr hit
    have he := congrArg Prod.fst (hn.symm.trans ht)
    cases he

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.complete_word_vectors' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms complete_word_vectors
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.reached_source_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reached_source_observations

private def byteTable : List (Nat × Nat) :=
  [(0,1536),(1,1024),(2,512),(3,768),(4,1024),(5,1),(6,1),(7,99),
    (16,3),(17,1),(18,0),(19,0),(24,3),(25,0),(26,1),(27,0),(32,7),(33,512)]

private theorem initial_byte_cell (entry : Nat × Nat) (h : entry∈byteTable) :
    Environment.readMemory bytes (32*entry.1) 32=Semantics.wordBytes entry.2 := by
  simp only [byteTable,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    simp only [bytes,List.foldl_cons,List.foldl_nil]
    repeat (rw [readMemory_write_frame]; case sep => simp only [Environment.wordBytes_length];omega)
    exact written_read _ _ _

/-- All eighteen physical cell images, including scaled POINTER words.
The final image changes exactly the selected child cell18. This does not
identify pointer-word scaling with emitted byte-address execution. -/
theorem complete_byte_vectors :
    byteTable.map (fun e => Environment.readMemory bytes (32*e.1) 32)=
      byteTable.map (fun e => Semantics.wordBytes e.2) ∧
    byteTable.map (fun e => Environment.readMemory outputBytes (32*e.1) 32)=
      byteTable.map (fun e => Semantics.wordBytes (if e.1=18 then 1 else e.2)) := by
  constructor
  · apply List.map_congr_left
    intro e he
    exact initial_byte_cell e he
  · apply List.map_congr_left
    intro e he
    by_cases hx : e.1=18
    · rw [if_pos hx,hx]
      exact written_read bytes 576 1
    · rw [if_neg hx]
      unfold outputBytes
      rw [readMemory_write_frame]
      · exact initial_byte_cell e he
      · simp only [Environment.wordBytes_length];omega

/-- Every typed payload and logical identity, before and after the material
write; the other child and the parent fields remain unchanged. -/
theorem complete_typed_vectors :
    MObj.elems .dyn (hp.get left)=[true,false,false] ∧
    MObj.elems .dyn (hp.get right)=[false,true,false] ∧
    MObj.elems .dyn (outputHeap.get left)=[true,true,false] ∧
    MObj.elems .dyn (outputHeap.get right)=[false,true,false] ∧
    hp.field parent layout.tag_type=u7 ∧ outputHeap.field parent layout.tag_type=u7 ∧
    hp.field parent layout.child_type=left ∧ outputHeap.field parent layout.child_type=left ∧
    [left.id,right.id,parent.id]=[0,1,2] := by
  exact ⟨left_values,right_values,final_left,final_right,rfl,rfl,rfl,rfl,rfl⟩

private def endpointSource : Source.EMState E SourceCtx :=
  (.cons (.bool true) (.cons (sourceUint (indexValue (wmod 3))) sy.1),sy.2)
private def endpointState : State C Δ :=
  (σ.push (t := .val .uint) (indexValue (wmod 3))).push (t := .val .bool) true
private def endpointWord : Machine := writeMachine (writeMachine machine 5 (.val (wmod 3))) 6 (.val (bword true))
private theorem endpoint_repr : StateRepr 1 1 8
    ((Frag.init Γ).push (.val .uint) .ok |>.push (.val .bool) .ok) endpointState base endpointWord :=
  (initial_repr.consVal (indexValue (wmod 3)) (.val (wmod 3)) (ReprV.uint_of rfl) (by decide)).consVal (p := .bool)
    true (.val (bword true)) rfl (by decide)

/-- Endpoint rejection is independently derived in Source, intrinsic and
whole word code. The Source panic retains its state; word revert exposes NO
posterror machine or panic payload. Low read horizons time out separately. -/
theorem endpoint_and_timeout (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalLoc (G p) F0 (fuel+3) (sourceStructChildLoc layout sroot si)).run endpointSource=
      (.error (.revert (Source.panicData .index)),endpointSource) ∧
    (Source.evalE (G p) F0 (fuel+4) (sourceStructChildAssign layout sroot si sv)).run endpointSource=
      (.error (.revert (Source.panicData .index)),endpointSource) ∧
    Stmt.run endpointState (.assignMem (.index .dyn (.loc (.field (.var troot map_free) "items" layout.child_type))
      (.simple (.local ti))) (.val (.simple (.local tv))))=.error .revert ∧
    Evm.run code endpointWord=.revert ∧
    (∀ n,n≤2 → (Source.evalE (G p) F0 n (sourceStructChildRead layout sroot si)).run inputSource=(.error .timeout,inputSource)) := by
  have hr : SourceBoolStructAt endpointSource 2 hp parent addresses layout := initial_at.same_heaps rfl rfl
  have hb : hp.len (hp.field parent layout.child_type) .dyn≤(indexValue (wmod 3)).1.toNat := by
    change hp.len left .dyn≤3
    rw [left_length]
    exact Nat.le_refl _
  have hs := hr.child_bounds (G p) F0 fuel sroot si sv (indexValue (wmod 3)) true rfl rfl rfl hb
  let path : MPath C Δ (.ref (.array (.prim .bool))) := .loc (.field (.var troot map_free) "items" layout.child_type)
  let pointer : List Evm.Instr := [.mload (cellOf 1 troot)] ++ readFieldCode (fieldOffset (structDef S) "items")
  have hpath : PtrFrag 1 path pointer := .field _ _ _ (.local troot map_free)
  have hselected : path.mvalT endpointState=.ok left := by
    simp only [path,MPath.mvalT,MLoc.addrT]
    rfl
  have hi : (Val.simple (.local ti) : Val C Δ .uint).evalT endpointState=.ok (indexValue (wmod 3)) := rfl
  have hv : (Val.simple (.local tv) : Val C Δ .bool).evalT endpointState=.ok true := rfl
  have hnone : endpointState.heap.writeAddr (.index left .dyn (indexValue (wmod 3))) true=none := by
    change (if 3<hp.len left .dyn then some _ else none)=none
    rw [left_length]
    rfl
  have ht : TRun.assignMem (.index .dyn path (.simple (.local ti))) (.val (.simple (.local tv))) endpointState=.error .revert := by
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,hselected,hi,hv,hnone,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have hw := hpath.writeArray endpoint_repr (.simple (.local ti)) (.simple (.local tv))
    (Evm.compileVal 1 (.simple (.local ti))) (Evm.compileVal 1 (.simple (.local tv)))
    (fun h' => Evm.val_sim (.simple (.local ti)) h'.core rfl)
    (Evm.val_sim (.simple (.local tv)) endpoint_repr.core rfl)
  rw [ht] at hw
  refine ⟨hs.1,hs.2,ht,?_,?_⟩
  · rcases hw with ⟨o,_,bad,_⟩ | ⟨_,good⟩
    · cases bad
    · exact good
  · exact source_struct_child_low_horizon layout (G p) F0 inputSource sroot si

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.complete_byte_vectors' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_byte_vectors
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.complete_typed_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_typed_vectors
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.endpoint_and_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms endpoint_and_timeout

/-- Actual INITIAL reads distinguish skipped mutation and selecting the other
child. The named layout cannot treat the numeric tag as a Boolean reference. -/
theorem initial_read_and_selection_controls (p : Roadmap.Pipeline) (fuel : Nat) :
    (Source.evalE (G p) F0 (fuel+3) (sourceStructChildRead layout sroot si)).run inputSource=
      (.ok (.val (.bool false)),inputSource) ∧
    Evm.run (structChildReadCode (C := C) 1 troot "items" (.simple (.local ti))) inputWord=
      .ok (inputWord.push (.val (bword false))) 0 ∧
    (Source.readLoc (E := E) (Γ := SourceCtx) F0 (τ := .bool) (.mem 0 0)).run inputSource=(.ok (.bool true),inputSource) ∧
    (Source.readLoc (E := E) (Γ := SourceCtx) F0 (τ := .bool) (.mem 1 0)).run inputSource=(.ok (.bool false),inputSource) ∧
    (Source.readLoc (E := E) (Γ := SourceCtx) F0 (τ := .bool) (.mem 1 1)).run inputSource=(.ok (.bool true),inputSource) ∧
    lookupBy "tag" (structDef S)≠some (.ref (.array (.prim .bool))) ∧
    E.structFields dn .memory=some [("tag",.int .u256),("items",SourceBoolArrayTy)] := by
  have hit : hp.index left .dyn index=some false := by
    change (MObj.elems .dyn (hp.get left))[index.1.toNat]?=some false
    rw [left_values];rfl
  have hr := source_at.read_child_word layout (G p) F0 fuel inputState parent addresses
    sroot si troot (.simple (.local ti)) index false rfl rfl rfl rfl map_free hit repr rfl
  have hrRight : SourceBoolMemoryAt inputSource 1 hp right .dyn := right_at
  have left0 : hp.index left .dyn (indexValue (wmod 0))=some true := by
    change (MObj.elems .dyn (hp.get left))[0]?=some true
    rw [left_values];rfl
  have right0 : hp.index right .dyn (indexValue (wmod 0))=some false := by
    change (MObj.elems .dyn (hp.get right))[0]?=some false
    rw [right_values];rfl
  have right1 : hp.index right .dyn index=some true := by
    change (MObj.elems .dyn (hp.get right))[index.1.toNat]?=some true
    rw [right_values];rfl
  refine ⟨hr.1,hr.2,(source_at.leaf.read_iff F0 (indexValue (wmod 0)) true).mpr left0,
    (hrRight.read_iff F0 (indexValue (wmod 0)) false).mpr right0,
    (hrRight.read_iff F0 index true).mpr right1,?_,layout.source_fields⟩
  rw [layout.tag_type]
  intro bad
  cases bad

/-- The complete Source local vector is unchanged by the client, including
self/root and old retained aliases; the original saved word tail is nonempty. -/
theorem complete_initial_locals :
    inputSource.1=.cons (.bool true) (.cons (sourceUint (indexValue (wmod 1)))
      (.cons (.memRef rfl 2) (.cons (.memRef rfl 1) (.cons (.memRef rfl 0) (.cons (.memRef rfl 2) .nil))))) ∧
    inputWord.stack=[w[42]] ∧ outputWord.stack=[w[42]] := by
  exact ⟨rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.initial_read_and_selection_controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initial_read_and_selection_controls
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.complete_initial_locals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms complete_initial_locals

private def srhs : Source.Idx SourceCtx SB := .there (.there (.there .here))
private def trhs : Idx Δ (.mem B) := .there (.there (.there .here))
private def redirectHeap : Heap H := hp.setField parent layout.child_type right
private def redirectWord : Machine := writeMachine inputWord 33 (.val (wmod 24))
private def redirectBytes : Environment.Memory := Environment.writeBytes bytes 1056 (Semantics.wordBytes 768)
private def redirectCode : List Evm.Instr := structReferenceWriteCode 1 troot trhs "items"
private theorem child_offset : fieldOffset (structDef S) "items"=1 := by rw [layout.target_fields];decide
private theorem named_pointer_frame : PointerFrame inputWord bytes (fun c => c=33) := by
  constructor
  · intro c hc;subst c;decide
  · intro c hc;subst c
    exact ⟨wmod 16,rfl,by decide,initial_byte_cell (33,512) (by decide)⟩

/-- Actual named reference redirection changes the parent pointer from LEFT
16 to RIGHT24 (physical512 to768), not either child. The same reached states
carry Source/intrinsic/whole-word execution, allocator and both local frames. -/
theorem named_reference_client (p : Roadmap.Pipeline) (fuel nps : Nat) :
    Environment.readMemory bytes 1056 32=Semantics.wordBytes 512 ∧
    ∃ z : Source.EMState E SourceCtx,
      (Source.evalE (G p) F0 (fuel+3) (sourceStructAssign layout sroot srhs)).run inputSource=
        (.ok (.val (.memRef rfl 1)),z) ∧
      (Source.execS (G p) F0 (fuel+4) nps none
        (.expr (sourceStructAssign layout sroot srhs) : Source.RStmt E [] false .body SourceCtx SourceCtx)
        inputSource.1).run (.nil,inputSource.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      Stmt.run inputState (.assignMem (.field (.var troot map_free) "items" layout.child_type) (.ref (.var trhs rfl)))=
        .ok ⟨inputState.withHeap redirectHeap,List.prefix_refl _⟩ ∧
      Evm.run redirectCode inputWord=.ok redirectWord 0 ∧
      SourceBoolStructAt z 2 redirectHeap parent addresses layout ∧ Source.MemOK E SH z ∧
      StateRepr 1 1 8 ((Frag.init Γ).push (.val .uint) .ok |>.push (.val .bool) .ok)
        (inputState.withHeap redirectHeap) base redirectWord ∧
      PointerFrame redirectWord redirectBytes (fun c => c=33) ∧
      WordFrame redirectWord redirectBytes (fun c => (base left.id).val≤c ∧ c<(base left.id).val+1+hp.len left .dyn) ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU 1056 (by decide)::lenU 768 (by decide)::tail,bytes⟩=some ⟨tail,redirectBytes⟩) ∧
      Environment.readMemory redirectBytes 1056 32=Semantics.wordBytes 768 ∧
      (∀ j,j<1056 ∨ 1088≤j → redirectBytes j=bytes j) ∧
      z.1=inputSource.1 ∧ redirectWord.stack=inputWord.stack ∧
      StructAllocatorRepr redirectHeap base 8 ⟨48,by decide⟩ redirectWord ∧
      redirectHeap.field parent layout.tag_type=u7 ∧ redirectHeap.field parent layout.child_type=right ∧
      (∀ q : HRef H B,redirectHeap.get q=hp.get q) ∧
      (∀ q,SourceBoolMemoryAt inputSource (addresses q.id) hp q .dyn →
        SourceBoolMemoryAt z (addresses q.id) redirectHeap q .dyn) ∧
      (z.2.ex=inputSource.2.ex ∧ z.2.events=inputSource.2.events ∧ z.2.logs=inputSource.2.logs ∧ z.2.fnLocals=inputSource.2.fnLocals) := by
  have hright : SourceBoolMemoryAt inputSource 1 hp right .dyn := right_at
  have sep : ∀ c,(base left.id).val≤c ∧ c<(base left.id).val+1+hp.len left .dyn →
      c≠(base parent.id).val+fieldOffset (structDef S) "items" := by
    intro c hc
    rw [left_length] at hc
    change 16≤c ∧ c<20 at hc
    rw [child_offset]
    change c≠33
    omega
  obtain ⟨hinit,z,target,offset,_,he,hs,hi,hw,hr,hmk,hstate,ht,hptr,hnum,hoff,hbyte,hread,hext,hl,hstack,halloc,htag,hchild,hchildren,hsource,heffects⟩ :=
    assign_struct_reference_physical layout (G p) F0 fuel nps inputState parent right addresses source_at hright
      sroot srhs troot trhs rfl rfl rfl rfl map_free SH memOK repr bytes (fun c => c=33)
      (fun c => (base left.id).val≤c ∧ c<(base left.id).val+1+hp.len left .dyn)
      named_pointer_frame child_frame (by rw [child_offset];rfl) (by decide) sep
  rw [child_offset] at ht hoff hptr
  change target=redirectWord at ht
  subst target
  have offsetEq : offset=⟨1056,by decide⟩ := Fin.ext hoff
  subst offset
  refine ⟨hinit,z,he,hs,hi,hw,hr,hmk,hstate,?_,hnum,hbyte,hread,hext,hl,hstack,
    halloc ⟨48,by decide⟩ (by decide) allocator,htag,hchild,hchildren,hsource,heffects⟩
  exact ⟨fun c hc => hptr.fits c (.inl hc),fun c hc => hptr.cells c (.inl hc)⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_reference_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_reference_client

/-- The changed named binding selects RIGHT at the actual reached heap;
retained LEFT aliases still see their OLD payload, excluding accidental copy
or primitive mutation. Actual Source and whole-word appended reads agree. -/
theorem named_reference_observations (p : Roadmap.Pipeline) (fuel nps : Nat) :
    ∃ z : Source.EMState E SourceCtx,
      (Source.execS (G p) F0 (fuel+4) nps none
        (.expr (sourceStructAssign layout sroot srhs) : Source.RStmt E [] false .body SourceCtx SourceCtx)
        inputSource.1).run (.nil,inputSource.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      [z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2]=
        [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 1⟩] ∧
      z.1=inputSource.1 ∧ z.1.get salias=.memRef rfl 0 ∧
      (Source.readLoc (E := E) (Γ := SourceCtx) F0 (τ := .bool) (.mem 0 1)).run z=(.ok (.bool false),z) ∧
      (Source.evalE (G p) F0 (fuel+3) (sourceStructChildRead layout sroot si)).run z=(.ok (.val (.bool true)),z) ∧
      Evm.run (redirectCode ++ structChildReadCode (C := C) 1 troot "items" (.simple (.local ti))) inputWord=
        .ok (redirectWord.push (.val (bword true))) 0 ∧
      ¬ SourceBoolStructAt z 2 hp parent addresses layout := by
  obtain ⟨_,z,_,hs,_,hw,hr,_,hm,_,_,_,_,_,hl,_,_,htag,hchild,hchildren,hsource,_⟩ := named_reference_client p fuel nps
  have hlRep := hsource left source_at.leaf
  have hrRep := hsource right (show SourceBoolMemoryAt inputSource 1 hp right .dyn from right_at)
  have hz0 : z.2.heap.get 0=some ⟨SB,sourceBoolMemory [true,false,false]⟩ := by
    change z.2.heap.get 0=some ⟨SB,sourceBoolMemory (MObj.elems .dyn (redirectHeap.get left))⟩ at hlRep
    simpa only [hchildren,left_values] using hlRep
  have hz1 : z.2.heap.get 1=some ⟨SB,sourceBoolMemory [false,true,false]⟩ := by
    change z.2.heap.get 1=some ⟨SB,sourceBoolMemory (MObj.elems .dyn (redirectHeap.get right))⟩ at hrRep
    simpa only [hchildren,right_values] using hrRep
  have hz2 : z.2.heap.get 2=some ⟨SS,data 1⟩ := by
    have h := hr.parent
    simpa only [htag,hchild] using h
  have hit : redirectHeap.index right .dyn index=some true := by
    change (MObj.elems .dyn (redirectHeap.get right))[index.1.toNat]?=some true
    rw [hchildren,right_values];rfl
  have hold : redirectHeap.index left .dyn index=some false := by
    change (MObj.elems .dyn (redirectHeap.get left))[index.1.toNat]?=some false
    rw [hchildren,left_values];rfl
  have hread := hr.read_child_word layout (G p) F0 fuel (inputState.withHeap redirectHeap) parent addresses
    sroot si troot (.simple (.local ti)) index true
    (by rw [hl];rfl) (by rw [hl];rfl) rfl rfl map_free (by change redirectHeap.index (redirectHeap.field parent layout.child_type) .dyn index=some true;rw [hchild];exact hit) hm rfl
  refine ⟨z,hs,?_,hl,?_,(hsource left source_at.leaf).read_iff F0 index false |>.mpr hold,hread.1,?_,?_⟩
  · rw [hz0,hz1,hz2]
  · rw [hl];rfl
  · rw [run_append_ok hw];exact hread.2
  · intro stale
    have oldRead : hp.index left .dyn index=some false := by
      change (MObj.elems .dyn (hp.get left))[index.1.toNat]?=some false
      rw [left_values];rfl
    have wrong := stale.eval_child_read (G p) F0 fuel sroot si index false (by rw [hl];rfl) (by rw [hl];rfl) oldRead
    have bad := congrArg Prod.fst (wrong.symm.trans hread.1)
    cases bad

/-- All represented cells and both typed child payloads are retained except
the named pointer slot. Byte pointers are SCALED, unlike numeric data cells. -/
theorem named_reference_vectors :
    [0,1,2,3,4,5,6,7,16,17,18,19,24,25,26,27,32,33].map redirectWord.mem=
      [w[48],w[32],w[16],w[24],w[32],w[1],w[1],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[24]] ∧
    byteTable.map (fun e => Environment.readMemory redirectBytes (32*e.1) 32)=
      byteTable.map (fun e => Semantics.wordBytes (if e.1=33 then 768 else e.2)) ∧
    MObj.elems .dyn (redirectHeap.get left)=[true,false,false] ∧
    MObj.elems .dyn (redirectHeap.get right)=[false,true,false] ∧
    redirectHeap.field parent layout.tag_type=u7 ∧ redirectHeap.field parent layout.child_type=right ∧
    [left.id,right.id,parent.id]=[0,1,2] := by
  refine ⟨?_,?_,?_,?_,rfl,rfl,rfl⟩
  · first | rfl | decide
  · apply List.map_congr_left
    intro e he
    by_cases hx : e.1=33
    · rw [if_pos hx,hx];exact written_read bytes 1056 768
    · rw [if_neg hx]
      unfold redirectBytes
      rw [readMemory_write_frame]
      · exact initial_byte_cell e he
      · simp only [Environment.wordBytes_length];omega
  · rw [redirectHeap,Heap.setField,Heap.get_set_ne hp parent left (by decide),left_values]
  · rw [redirectHeap,Heap.setField,Heap.get_set_ne hp parent right (by decide),right_values]

/-- Incorrectly storing the unscaled logical24 cannot supply the actual
physical pointer image768. The published low horizon times out before write. -/
theorem named_reference_encoding_and_timeout (p : Roadmap.Pipeline) :
    Environment.readMemory (Environment.writeBytes bytes 1056 (Semantics.wordBytes 24)) 1056 32≠
      Environment.readMemory redirectBytes 1056 32 ∧
    redirectWord.mem 33≠inputWord.mem 33 ∧
    (∀ n,n≤2 → (Source.evalE (G p) F0 n (sourceStructAssign layout sroot srhs)).run inputSource=(.error .timeout,inputSource)) := by
  refine ⟨?_,?_,source_struct_assign_low_horizon layout (G p) F0 inputSource sroot srhs⟩
  · rw [written_read]
    change Semantics.wordBytes 24≠Environment.readMemory (Environment.writeBytes bytes 1056 (Semantics.wordBytes 768)) 1056 32
    rw [written_read]
    decide
  · first | decide | simp only [redirectWord,writeMachine,upd_same];decide

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_reference_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_reference_observations
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_reference_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_reference_vectors
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_reference_encoding_and_timeout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_reference_encoding_and_timeout

private def tleftAlias : Idx Δ (.mem B) := .there (.there (.there (.there .here)))

/-- Assigning the already-selected OLD alias is supported too: actual Source
execution remains represented by the original heap, and the WHOLE word run
returns its original machine. No literal Source poststate equality is assumed. -/
theorem named_reference_self (p : Roadmap.Pipeline) (fuel nps : Nat) :
    Evm.run (structReferenceWriteCode 1 troot tleftAlias "items") inputWord=.ok inputWord 0 ∧
    ∃ z : Source.EMState E SourceCtx,
      (Source.evalE (G p) F0 (fuel+3) (sourceStructAssign layout sroot salias)).run inputSource=
        (.ok (.val (.memRef rfl 0)),z) ∧
      (Source.execS (G p) F0 (fuel+4) nps none
        (.expr (sourceStructAssign layout sroot salias) : Source.RStmt E [] false .body SourceCtx SourceCtx)
        inputSource.1).run (.nil,inputSource.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      SourceBoolStructAt z 2 hp parent addresses layout ∧ Source.MemOK E SH z ∧ z.1=inputSource.1 := by
  have sep : ∀ c,(base left.id).val≤c ∧ c<(base left.id).val+1+hp.len left .dyn →
      c≠(base parent.id).val+fieldOffset (structDef S) "items" := by
    intro c hc
    rw [left_length] at hc
    change 16≤c ∧ c<20 at hc
    rw [child_offset]
    change c≠33
    omega
  obtain ⟨_,z,target,_,_,he,hs,_,hw,hr,hmk,_,ht,_,_,_,_,_,_,hl,_⟩ :=
    assign_struct_reference_physical layout (G p) F0 fuel nps inputState parent left addresses source_at source_at.leaf
      sroot salias troot tleftAlias rfl rfl rfl rfl map_free SH memOK repr bytes (fun c => c=33)
      (fun c => (base left.id).val≤c ∧ c<(base left.id).val+1+hp.len left .dyn)
      named_pointer_frame child_frame (by rw [child_offset];rfl) (by decide) sep
  rw [child_offset] at ht
  change target=writeMachine inputWord 33 (.val (wmod 16)) at ht
  have memSame : upd inputWord.mem 33 (.val (wmod 16))=inputWord.mem := by
    funext c
    by_cases hc : c=33
    · subst c;rfl
    · exact upd_other _ _ hc
  have wordSame : writeMachine inputWord 33 (.val (wmod 16))=inputWord := by
    simp only [writeMachine,memSame]
  rw [wordSame] at ht
  subst target
  refine ⟨hw,z,he,hs,?_,hmk,hl⟩
  exact hr

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_reference_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_reference_self

private def seqIndex : PrimTy.uint.Denote := indexValue (wmod 0)
private def seqState : State C Δ := (σ.push (t := .val .uint) seqIndex).push (t := .val .bool) true
private def seqSource : Source.EMState E SourceCtx := (.cons (.bool true) (.cons (sourceUint seqIndex) sy.1),sy.2)
private def seqWord : Machine := writeMachine (writeMachine machine 5 (.val (wmod 0))) 6 (.val (bword true))
private def seqBytes : Environment.Memory := Environment.writeBytes bytes 160 (Semantics.wordBytes 0)
private def seqFirstWord : Machine := writeMachine seqWord 33 (.val (wmod 24))
private def seqFinalHeap : Heap H := redirectHeap.set right (MObj.setElem .dyn (redirectHeap.get right) 0 true)
private def seqFinalWord : Machine := writeMachine seqFirstWord 25 (.val (bword true))
private def seqFirstBytes : Environment.Memory := Environment.writeBytes seqBytes 1056 (Semantics.wordBytes 768)
private def seqFinalBytes : Environment.Memory := Environment.writeBytes seqFirstBytes 800 (Semantics.wordBytes 1)
private theorem seq_repr : StateRepr 1 1 8 ((Frag.init Γ).push (.val .uint) .ok |>.push (.val .bool) .ok) seqState base seqWord :=
  (initial_repr.consVal seqIndex (.val (wmod 0)) (ReprV.uint_of rfl) (by decide)).consVal (p := .bool) true (.val (bword true)) rfl (by decide)
private theorem seq_source : SourceBoolStructAt seqSource 2 hp parent addresses layout := initial_at.same_heaps rfl rfl
private theorem seq_memOK : Source.MemOK E SH seqSource :=
  ⟨⟨source_memOK.1.1,⟨trivial,⟨trivial,source_memOK.1.2⟩⟩⟩,source_memOK.2⟩
private theorem seq_allocator : StructAllocatorRepr hp base 8 ⟨48,by decide⟩ seqWord :=
  ((initial_allocator.localWrite 5 (by decide) (by decide) (.val (wmod 0))).localWrite 6 (by decide) (by decide) (.val (bword true)))
private theorem seq_pointers : PointerFrame seqWord seqBytes (fun c => c=33) := by
  constructor
  · intro c hc;subst c;decide
  · intro c hc;subst c
    refine ⟨wmod 16,rfl,by decide,?_⟩
    rw [seqBytes,readMemory_write_frame]
    · exact initial_byte_cell (33,512) (by decide)
    · simp only [Environment.wordBytes_length];decide
private theorem right_length : hp.len right .dyn=3 := by
  change (MObj.elems .dyn (hp.get right)).length=3
  rw [right_values];rfl
private theorem seq_cell (c : Nat) (w : Fin W) (hw : seqWord.mem c=.val w)
    (hb : Environment.readMemory bytes (32*c) 32=Semantics.wordBytes w.val) (sep : 192≤32*c) :
    CellAt seqWord seqBytes c := by
  refine ⟨w,hw,?_⟩
  rw [seqBytes,readMemory_write_frame]
  · exact hb
  · simp only [Environment.wordBytes_length];exact Or.inr sep
private theorem seq_numbers : WordFrame seqWord seqBytes (fun c => (base right.id).val≤c ∧ c<(base right.id).val+1+hp.len right .dyn) := by
  constructor
  · intro c hc
    rw [right_length] at hc
    change 24≤c ∧ c<28 at hc
    change 32*c+32≤2^256
    omega
  · intro c hc
    rw [right_length] at hc
    change 24≤c ∧ c<28 at hc
    have hcases : c=24 ∨ c=25 ∨ c=26 ∨ c=27 := by omega
    rcases hcases with rfl|rfl|rfl|rfl
    · exact seq_cell 24 ⟨3,by decide⟩ rfl (initial_byte_cell (24,3) (by decide)) (by decide)
    · exact seq_cell 25 ⟨0,by decide⟩ rfl (initial_byte_cell (25,0) (by decide)) (by decide)
    · exact seq_cell 26 ⟨1,by decide⟩ rfl (initial_byte_cell (26,1) (by decide)) (by decide)
    · exact seq_cell 27 ⟨0,by decide⟩ rfl (initial_byte_cell (27,0) (by decide)) (by decide)
private theorem seq_write : redirectHeap.writeAddr (.index right .dyn seqIndex) true=some seqFinalHeap := by
  have length : redirectHeap.len right .dyn=3 := by
    change (MObj.elems .dyn (redirectHeap.get right)).length=3
    rw [redirectHeap,Heap.setField,Heap.get_set_ne hp parent right (by decide),right_values];rfl
  change (if 0<redirectHeap.len right .dyn then some _ else none)=_
  rw [length]
  rfl
private theorem seq_head : Evm.run ((([.mload 6,.mload 4] : List Evm.Instr) ++ readFieldCode 1) ++ [.mload 5]) seqFirstWord=
    .ok (((seqFirstWord.push (.val (bword true))).push (.val (wmod 24))).push (.val (wmod 0))) 0 := by
  have loads : Evm.run ([.mload 6,.mload 4] : List Evm.Instr) seqFirstWord=
      .ok ((seqFirstWord.push (.val (bword true))).push (.val (wmod 32))) 0 := by
    have hv : seqFirstWord.mem 6=.val (bword true) := rfl
    have hp : seqFirstWord.mem 4=.val (wmod 32) := rfl
    simp only [Evm.run,exec_cons_zero,Evm.Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,hv,hp]
  have field : Evm.run (readFieldCode 1) ((seqFirstWord.push (.val (bword true))).push (.val (wmod 32)))=
      .ok ((seqFirstWord.push (.val (bword true))).push (.val (wmod 24))) 0 := by
    rw [readFieldCode,run_append_ok (fieldAddr_run (seqFirstWord.push (.val (bword true))) (wmod 32) 1)]
    rfl
  rw [run_append_ok (by rw [run_append_ok loads];exact field)]
  rfl
private theorem seq_expected_run
    (repr : StateRepr 1 1 8 ((Frag.init Γ).push (.val .uint) .ok |>.push (.val .bool) .ok)
      (seqState.withHeap redirectHeap) base seqFirstWord) :
    Evm.run code seqFirstWord=.ok seqFinalWord 0 := by
  rw [code_eq,run_append_ok seq_head]
  rcases writeArray_correct (repr.heap.arrays right) (wmod 0) true (.val (bword true)) rfl with
    ⟨out,ht,hw,_⟩ | ⟨bad,_⟩
  · rw [writeArrayStackCode,arrayStack_append_eq (seqFirstWord.push (.val (bword true))) (wmod 24) (wmod 0) 3 (by decide) (by rfl),←writeArrayCode]
    exact hw
  · change redirectHeap.writeAddr (.index right .dyn seqIndex) true=none at bad
    rw [seq_write] at bad
    cases bad

/-- One ACTUAL Source Items/Prog/full-word program first selects RIGHT, then
materially changes its first cell false->true. The old LEFT is not the write
endpoint; all stages, physical prefixes and allocator facts are retained. -/
theorem named_sequence_client (p : Roadmap.Pipeline) (fuel nps : Nat) :
    ∃ ym z : Source.EMState E SourceCtx,
      (Source.execS (G p) F0 (fuel+6) nps none
        (.expr (sourceStructAssign layout sroot srhs) : Source.RStmt E [] false .body SourceCtx SourceCtx) seqSource.1).run (.nil,seqSource.2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS (G p) F0 (fuel+5) nps none
        (.expr (sourceStructChildAssign layout sroot si sv) : Source.RStmt E [] false .body SourceCtx SourceCtx) ym.1).run (.nil,ym.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems (G p) F0 (fuel+7) nps none
        (.stmt (.expr (sourceStructAssign layout sroot srhs)) (.stmt (.expr (sourceStructChildAssign layout sroot si sv)) .nil) : Source.RItems E [] false .body SourceCtx SourceCtx) seqSource.1).run (.nil,seqSource.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run seqState (.cons (.assignMem (.field (.var troot map_free) "items" layout.child_type) (.ref (.var trhs rfl)))
        (.cons (.assignMem (.index .dyn (.loc (.field (.var troot map_free) "items" layout.child_type)) (.simple (.local ti))) (.val (.simple (.local tv)))) .nil))=
          .ok ⟨seqState.withHeap seqFinalHeap,List.prefix_refl _⟩ ∧
      Evm.run redirectCode seqWord=.ok seqFirstWord 0 ∧
      Evm.run code seqFirstWord=.ok seqFinalWord 0 ∧
      Evm.run (redirectCode ++ code) seqWord=.ok seqFinalWord 0 ∧
      SourceBoolStructAt ym 2 redirectHeap parent addresses layout ∧ SourceBoolStructAt z 2 seqFinalHeap parent addresses layout ∧
      StateRepr 1 1 8 ((Frag.init Γ).push (.val .uint) .ok |>.push (.val .bool) .ok) (seqState.withHeap seqFinalHeap) base seqFinalWord ∧
      Source.MemOK E SH ym ∧ Source.MemOK E SH z ∧
      WordFrame seqFinalWord seqFinalBytes (fun c => (base right.id).val≤c ∧ c<(base right.id).val+1+seqFinalHeap.len right .dyn) ∧
      PointerFrame seqFinalWord seqFinalBytes (fun c => c=33) ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU 1056 (by decide)::lenU 768 (by decide)::tail,seqBytes⟩=some ⟨tail,seqFirstBytes⟩) ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU 800 (by decide)::lenU 1 (by decide)::tail,seqFirstBytes⟩=some ⟨tail,seqFinalBytes⟩) ∧
      ym.1=seqSource.1 ∧ z.1=seqSource.1 ∧ seqFinalWord.stack=seqWord.stack ∧
      StructAllocatorRepr seqFinalHeap base 8 ⟨48,by decide⟩ seqFinalWord ∧
      (∀ q : HRef H B,right.id≠q.id → seqFinalHeap.get q=hp.get q) ∧
      (∀ q,SourceBoolMemoryAt seqSource (addresses q.id) hp q .dyn → SourceBoolMemoryAt ym (addresses q.id) redirectHeap q .dyn) ∧
      (∀ d,d≠1 → z.2.heap.get d=ym.2.heap.get d) ∧
      (z.2.ex=seqSource.2.ex ∧ z.2.events=seqSource.2.events ∧ z.2.logs=seqSource.2.logs ∧ z.2.fnLocals=seqSource.2.fnLocals) := by
  have sep : ∀ c,(base right.id).val≤c ∧ c<(base right.id).val+1+hp.len right .dyn →
      c≠(base parent.id).val+fieldOffset (structDef S) "items" := by
    intro c hc;rw [right_length] at hc
    change 24≤c ∧ c<28 at hc
    rw [child_offset]
    change c≠33
    omega
  obtain ⟨ym,z,out,mm,target,o1,o2,hs1,hs2,items,write2,_,_,typed,word1Eq,code1,code2,whole,hr1,hr2,mem1,mem2,hm1,hm2,physical,ptr,off1,off2,byte1,byte2,_,_,_,other,source1,source2,hl1,hl2,hstack,halloc,effects⟩ :=
    assign_struct_reference_child_physical layout (G p) F0 fuel nps seqState parent right addresses seq_source
      (show SourceBoolMemoryAt seqSource 1 hp right .dyn from right_at) sroot srhs si sv troot trhs ti tv seqIndex true
      rfl rfl rfl rfl rfl rfl rfl rfl map_free (by change seqIndex.1.toNat<hp.len right .dyn;rw [right_length];decide) SH seq_memOK seq_repr rfl rfl
      seqBytes (fun c => c=33) seq_pointers (by rw [child_offset];rfl) (by decide) seq_numbers sep
  have sameHeap : out=seqFinalHeap := Option.some.inj (write2.symm.trans seq_write)
  subst out
  rw [child_offset] at word1Eq off1 ptr
  change mm=seqFirstWord at word1Eq
  subst mm
  have sameWord : target=seqFinalWord := (Out.ok.inj (code2.symm.trans (seq_expected_run hm1))).1
  subst target
  have offset1 : o1=⟨1056,by decide⟩ := Fin.ext off1
  have offset2 : o2=⟨800,by decide⟩ := Fin.ext off2
  subst o1;subst o2
  exact ⟨ym,z,hs1,hs2,items,typed,code1,code2,whole,hr1,hr2,hm2,mem1,mem2,physical,ptr,byte1,byte2,
    hl1,hl2,hstack,halloc ⟨48,by decide⟩ (by decide) seq_allocator,other,source1,source2,effects⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_sequence_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_sequence_client

private theorem seq_mid_values : MObj.elems .dyn (redirectHeap.get right)=[false,true,false] := by
  rw [redirectHeap,Heap.setField,Heap.get_set_ne hp parent right (by decide),right_values]
private theorem seq_final_values : MObj.elems .dyn (seqFinalHeap.get right)=[true,true,false] := by
  simp only [seqFinalHeap,Heap.get_set_same,MObj.elems_setElem,seq_mid_values,List.set]

/-- Full represented Source tables at INITIAL, rebound and mutated heaps,
with actual reached selected reads and retained OLD alias contents. -/
theorem named_sequence_observations (p : Roadmap.Pipeline) (fuel nps : Nat) :
    ∃ ym z : Source.EMState E SourceCtx,
      (Source.execS (G p) F0 (fuel+6) nps none
        (.expr (sourceStructAssign layout sroot srhs) : Source.RStmt E [] false .body SourceCtx SourceCtx) seqSource.1).run (.nil,seqSource.2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.execS (G p) F0 (fuel+5) nps none
        (.expr (sourceStructChildAssign layout sroot si sv) : Source.RStmt E [] false .body SourceCtx SourceCtx) ym.1).run (.nil,ym.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems (G p) F0 (fuel+7) nps none
        (.stmt (.expr (sourceStructAssign layout sroot srhs)) (.stmt (.expr (sourceStructChildAssign layout sroot si sv)) .nil) : Source.RItems E [] false .body SourceCtx SourceCtx) seqSource.1).run (.nil,seqSource.2)=
          (.ok (.normal z.1),(.nil,z.2)) ∧
      [seqSource.2.heap.get 0,seqSource.2.heap.get 1,seqSource.2.heap.get 2]=
        [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 0⟩] ∧
      [ym.2.heap.get 0,ym.2.heap.get 1,ym.2.heap.get 2]=
        [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 1⟩] ∧
      [z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2]=
        [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [true,true,false]⟩,some ⟨SS,data 1⟩] ∧
      (Source.evalE (G p) F0 (fuel+3) (sourceStructChildRead layout sroot si)).run ym=(.ok (.val (.bool false)),ym) ∧
      (Source.evalE (G p) F0 (fuel+3) (sourceStructChildRead layout sroot si)).run z=(.ok (.val (.bool true)),z) ∧
      z.1.get salias=.memRef rfl 0 ∧
      (Source.readLoc (E := E) (Γ := SourceCtx) F0 (τ := .bool) (.mem 0 1)).run z=(.ok (.bool false),z) ∧
      Evm.run ((redirectCode ++ code) ++ structChildReadCode (C := C) 1 troot "items" (.simple (.local ti))) seqWord=
        .ok (seqFinalWord.push (.val (bword true))) 0 ∧
      ¬ SourceBoolStructAt z 2 redirectHeap parent addresses layout := by
  obtain ⟨ym,z,hs1,hs2,items,_,_,_,whole,hr1,hr2,hm2,_,_,_,_,_,_,hl1,hl2,_,_,other,source1,source2,_⟩ := named_sequence_client p fuel nps
  have oldLeaf := source1 left seq_source.leaf
  have hm0 : ym.2.heap.get 0=some ⟨SB,sourceBoolMemory [true,false,false]⟩ := by
    change ym.2.heap.get 0=some ⟨SB,sourceBoolMemory (MObj.elems .dyn (redirectHeap.get left))⟩ at oldLeaf
    simpa only [redirectHeap,Heap.setField,Heap.get_set_ne hp parent left (by decide),left_values] using oldLeaf
  have hm1 : ym.2.heap.get 1=some ⟨SB,sourceBoolMemory [false,true,false]⟩ := by
    have h := hr1.leaf
    change ym.2.heap.get 1=some ⟨SB,sourceBoolMemory (MObj.elems .dyn (redirectHeap.get right))⟩ at h
    simpa only [seq_mid_values] using h
  have hm2parent : ym.2.heap.get 2=some ⟨SS,data 1⟩ := hr1.parent
  have hz0 : z.2.heap.get 0=some ⟨SB,sourceBoolMemory [true,false,false]⟩ := by rw [source2 0 (by decide),hm0]
  have hz1 : z.2.heap.get 1=some ⟨SB,sourceBoolMemory [true,true,false]⟩ := by
    have h := hr2.leaf
    change z.2.heap.get 1=some ⟨SB,sourceBoolMemory (MObj.elems .dyn (seqFinalHeap.get right))⟩ at h
    simpa only [seq_final_values] using h
  have hz2 : z.2.heap.get 2=some ⟨SS,data 1⟩ := by rw [source2 2 (by decide),hm2parent]
  have midRead : redirectHeap.index (redirectHeap.field parent layout.child_type) .dyn seqIndex=some false := by
    change (MObj.elems .dyn (redirectHeap.get right))[0]?=some false
    rw [seq_mid_values];rfl
  have finalRead : seqFinalHeap.index (seqFinalHeap.field parent layout.child_type) .dyn seqIndex=some true := by
    change (MObj.elems .dyn (seqFinalHeap.get right))[0]?=some true
    rw [seq_final_values];rfl
  have read1 := hr1.eval_child_read (G p) F0 fuel sroot si seqIndex false (by rw [hl1];rfl) (by rw [hl1];rfl) midRead
  have read2 := hr2.read_child_word layout (G p) F0 fuel (seqState.withHeap seqFinalHeap) parent addresses
    sroot si troot (.simple (.local ti)) seqIndex true (by rw [hl2];rfl) (by rw [hl2];rfl) rfl rfl map_free finalRead hm2 rfl
  refine ⟨ym,z,hs1,hs2,items,?_,?_,?_,read1,read2.1,?_,?_,?_,?_⟩
  · first | rfl | decide
  · rw [hm0,hm1,hm2parent]
  · rw [hz0,hz1,hz2]
  · rw [hl2];rfl
  · exact source_bool_read z 0 [true,false,false] hz0 1 (by decide)
  · rw [run_append_ok whole];exact read2.2
  · intro skipped
    have wrong := skipped.eval_child_read (G p) F0 fuel sroot si seqIndex false (by rw [hl2];rfl) (by rw [hl2];rfl) midRead
    have bad := congrArg Prod.fst (wrong.symm.trans read2.1)
    cases bad

/-- All eighteen INITIAL/intermediate/final word cells, and complete typed
payloads. Reference redirection and later mutation affect DIFFERENT cells. -/
theorem named_sequence_vectors :
    [0,1,2,3,4,5,6,7,16,17,18,19,24,25,26,27,32,33].map seqWord.mem=
      [w[48],w[32],w[16],w[24],w[32],w[0],w[1],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[16]] ∧
    [0,1,2,3,4,5,6,7,16,17,18,19,24,25,26,27,32,33].map seqFirstWord.mem=
      [w[48],w[32],w[16],w[24],w[32],w[0],w[1],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[24]] ∧
    [0,1,2,3,4,5,6,7,16,17,18,19,24,25,26,27,32,33].map seqFinalWord.mem=
      [w[48],w[32],w[16],w[24],w[32],w[0],w[1],w[99],w[3],w[1],w[0],w[0],w[3],w[1],w[1],w[0],w[7],w[24]] ∧
    MObj.elems .dyn (seqFinalHeap.get left)=[true,false,false] ∧
    MObj.elems .dyn (seqFinalHeap.get right)=[true,true,false] ∧
    seqFinalHeap.field parent layout.tag_type=u7 ∧ seqFinalHeap.field parent layout.child_type=right ∧
    [left.id,right.id,parent.id]=[0,1,2] := by
  refine ⟨?_,?_,?_,?_,seq_final_values,rfl,rfl,rfl⟩
  · first | rfl | decide
  · first | rfl | decide
  · first | rfl | decide
  · rw [seqFinalHeap,Heap.get_set_ne redirectHeap right left (by decide),redirectHeap,Heap.setField,
      Heap.get_set_ne hp parent left (by decide),left_values]

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_sequence_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_sequence_observations
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_sequence_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_sequence_vectors

private theorem seq_initial_byte (e : Nat × Nat) (he : e∈byteTable) :
    Environment.readMemory seqBytes (32*e.1) 32=Semantics.wordBytes (if e.1=5 then 0 else e.2) := by
  by_cases hx : e.1=5
  · rw [if_pos hx,hx];exact written_read bytes 160 0
  · rw [if_neg hx]
    unfold seqBytes
    rw [readMemory_write_frame]
    · exact initial_byte_cell e he
    · simp only [Environment.wordBytes_length];omega
private theorem seq_mid_byte (e : Nat × Nat) (he : e∈byteTable) :
    Environment.readMemory seqFirstBytes (32*e.1) 32=Semantics.wordBytes (if e.1=33 then 768 else if e.1=5 then 0 else e.2) := by
  by_cases hx : e.1=33
  · rw [if_pos hx,hx];exact written_read seqBytes 1056 768
  · rw [if_neg hx]
    unfold seqFirstBytes
    rw [readMemory_write_frame]
    · exact seq_initial_byte e he
    · simp only [Environment.wordBytes_length];omega

/-- Full eighteen physical cell images at all three actual stage heaps.
The local index, parent pointer and selected payload changes stay distinct. -/
theorem named_sequence_byte_vectors :
    byteTable.map (fun e => Environment.readMemory seqBytes (32*e.1) 32)=
      byteTable.map (fun e => Semantics.wordBytes (if e.1=5 then 0 else e.2)) ∧
    byteTable.map (fun e => Environment.readMemory seqFirstBytes (32*e.1) 32)=
      byteTable.map (fun e => Semantics.wordBytes (if e.1=33 then 768 else if e.1=5 then 0 else e.2)) ∧
    byteTable.map (fun e => Environment.readMemory seqFinalBytes (32*e.1) 32)=
      byteTable.map (fun e => Semantics.wordBytes (if e.1=25 then 1 else if e.1=33 then 768 else if e.1=5 then 0 else e.2)) := by
  refine ⟨List.map_congr_left (fun e he => seq_initial_byte e he),List.map_congr_left (fun e he => seq_mid_byte e he),?_⟩
  apply List.map_congr_left
  intro e he
  by_cases hx : e.1=25
  · rw [if_pos hx,hx];exact written_read seqFirstBytes 800 1
  · rw [if_neg hx]
    unfold seqFinalBytes
    rw [readMemory_write_frame]
    · exact seq_mid_byte e he
    · simp only [Environment.wordBytes_length];omega

private theorem seq_left_word : Evm.run code seqWord=.ok seqWord 0 := by
  have loads : Evm.run ([.mload 6,.mload 4] : List Evm.Instr) seqWord=
      .ok ((seqWord.push (.val (bword true))).push (.val (wmod 32))) 0 := by
    have hv : seqWord.mem 6=.val (bword true) := rfl
    have hp : seqWord.mem 4=.val (wmod 32) := rfl
    simp only [Evm.run,exec_cons_zero,Evm.Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,hv,hp]
  have field : Evm.run (readFieldCode 1) ((seqWord.push (.val (bword true))).push (.val (wmod 32)))=
      .ok ((seqWord.push (.val (bword true))).push (.val (wmod 16))) 0 := by
    rw [readFieldCode,run_append_ok (fieldAddr_run (seqWord.push (.val (bword true))) (wmod 32) 1)]
    rfl
  have head : Evm.run ((([.mload 6,.mload 4] : List Evm.Instr) ++ readFieldCode 1) ++ [.mload 5]) seqWord=
      .ok (((seqWord.push (.val (bword true))).push (.val (wmod 16))).push (.val (wmod 0))) 0 := by
    rw [run_append_ok (by rw [run_append_ok loads];exact field)]
    rfl
  have oldWrite : hp.writeAddr (.index left .dyn seqIndex) true=some (hp.set left (MObj.setElem .dyn (hp.get left) seqIndex.1.toNat true)) := by
    change (if 0<hp.len left .dyn then some _ else none)=_
    rw [left_length];rfl
  have memSame : upd seqWord.mem 17 (.val (bword true))=seqWord.mem := by
    funext c
    by_cases hc : c=17
    · subst c;rfl
    · exact upd_other _ _ hc
  have unchanged : writeMachine seqWord 17 (.val (bword true))=seqWord := by simp only [writeMachine,memSame]
  rw [code_eq,run_append_ok head]
  rcases writeArray_correct (seq_repr.heap.arrays left) (wmod 0) true (.val (bword true)) rfl with
    ⟨out,ht,hw,_⟩ | ⟨bad,_⟩
  · rw [writeArrayStackCode,arrayStack_append_eq (seqWord.push (.val (bword true))) (wmod 16) (wmod 0) 3 (by decide) (by rfl),←writeArrayCode]
    change Evm.run (writeArrayCode (wmod 16)) ((seqWord.push (.val (bword true))).push (.val (wmod 0)))=
      .ok (writeMachine seqWord 17 (.val (bword true))) 0 at hw
    rw [unchanged] at hw
    exact hw
  · change hp.writeAddr (.index left .dyn seqIndex) true=none at bad
    rw [oldWrite] at bad
    cases bad

/-- An ACTUALLY executed reversed WORD append writes through OLD LEFT before
rebinding. It leaves RIGHT's first cell0, whereas the forward run makes it1.
This control does not assert a reverse Source Items or byte-prefix theorem. -/
theorem named_sequence_order_control (p : Roadmap.Pipeline) (fuel nps : Nat) :
    Evm.run (code ++ redirectCode) seqWord=.ok seqFirstWord 0 ∧
    Evm.run (redirectCode ++ code) seqWord=.ok seqFinalWord 0 ∧
    seqFirstWord.mem 25≠seqFinalWord.mem 25 := by
  obtain ⟨_,_,_,_,_,_,first,_,whole,_⟩ := named_sequence_client p fuel nps
  refine ⟨?_,whole,by decide⟩
  rw [run_append_ok seq_left_word]
  exact first

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_sequence_byte_vectors' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_sequence_byte_vectors
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_sequence_order_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_sequence_order_control

private def rejectBytes : Environment.Memory := Environment.writeBytes bytes 160 (Semantics.wordBytes 3)
private def rejectFirstBytes : Environment.Memory := Environment.writeBytes rejectBytes 1056 (Semantics.wordBytes 768)
private def rejectFirstWord : Machine := writeMachine endpointWord 33 (.val (wmod 24))
private theorem reject_pointers : PointerFrame endpointWord rejectBytes (fun c => c=33) := by
  constructor
  · intro c hc;subst c;decide
  · intro c hc;subst c
    refine ⟨wmod 16,rfl,by decide,?_⟩
    rw [rejectBytes,readMemory_write_frame]
    · exact initial_byte_cell (33,512) (by decide)
    · simp only [Environment.wordBytes_length];decide

/-- The actual first named rebind succeeds before the reached index3 failure.
Source Items retains that changed prefix; word revert has no poststate/panic
payload claim, and byte execution is ONLY the successful first MSTORE. -/
theorem named_sequence_late_reject (p : Roadmap.Pipeline) (fuel nps : Nat) :
    ∃ ym : Source.EMState E SourceCtx,
      (Source.execS (G p) F0 (fuel+6) nps none
        (.expr (sourceStructAssign layout sroot srhs) : Source.RStmt E [] false .body SourceCtx SourceCtx) endpointSource.1).run (.nil,endpointSource.2)=
          (.ok (.normal ym.1),(.nil,ym.2)) ∧
      (Source.evalE (G p) F0 (fuel+4) (sourceStructChildAssign layout sroot si sv)).run ym=
        (.error (.revert (Source.panicData .index)),ym) ∧
      (Source.execItems (G p) F0 (fuel+7) nps none
        (.stmt (.expr (sourceStructAssign layout sroot srhs)) (.stmt (.expr (sourceStructChildAssign layout sroot si sv)) .nil) : Source.RItems E [] false .body SourceCtx SourceCtx) endpointSource.1).run (.nil,endpointSource.2)=
          (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      Prog.run endpointState (.cons (.assignMem (.field (.var troot map_free) "items" layout.child_type) (.ref (.var trhs rfl)))
        (.cons (.assignMem (.index .dyn (.loc (.field (.var troot map_free) "items" layout.child_type)) (.simple (.local ti))) (.val (.simple (.local tv)))) .nil))=.error .revert ∧
      Evm.run redirectCode endpointWord=.ok rejectFirstWord 0 ∧ Evm.run code rejectFirstWord=.revert ∧
      Evm.run (redirectCode ++ code) endpointWord=.revert ∧
      SourceBoolStructAt ym 2 redirectHeap parent addresses layout ∧
      [ym.2.heap.get 0,ym.2.heap.get 1,ym.2.heap.get 2]=
        [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 1⟩] ∧
      (Source.readLoc (E := E) (Γ := SourceCtx) F0 (τ := SB) (.mem 2 1)).run ym=(.ok (.memRef rfl 1),ym) ∧
      ¬ SourceBoolStructAt ym 2 hp parent addresses layout ∧
      (∀ tail : List Environment.Word,Environment.cryptoStep (.op .MSTORE)
        ⟨lenU 1056 (by decide)::lenU 768 (by decide)::tail,rejectBytes⟩=some ⟨tail,rejectFirstBytes⟩) ∧
      ym.1=endpointSource.1 ∧ rejectFirstWord.stack=endpointWord.stack ∧
      Source.MemOK E SH ym ∧
      StateRepr 1 1 8 ((Frag.init Γ).push (.val .uint) .ok |>.push (.val .bool) .ok) (endpointState.withHeap redirectHeap) base rejectFirstWord ∧
      StructAllocatorRepr redirectHeap base 8 ⟨48,by decide⟩ rejectFirstWord ∧
      (ym.2.ex=endpointSource.2.ex ∧ ym.2.events=endpointSource.2.events ∧ ym.2.logs=endpointSource.2.logs ∧ ym.2.fnLocals=endpointSource.2.fnLocals) := by
  have initial : SourceBoolStructAt endpointSource 2 hp parent addresses layout := initial_at.same_heaps rfl rfl
  have initialMem : Source.MemOK E SH endpointSource :=
    ⟨⟨source_memOK.1.1,⟨trivial,⟨trivial,source_memOK.1.2⟩⟩⟩,source_memOK.2⟩
  obtain ⟨ym,mm,offset,hs1,_,he2,items,_,_,typed,code1,code2,whole,hr,mem1,words1,middle,_,hoff,byte,children,sourceChildren,hl,hstack,halloc,effects⟩ :=
    assign_struct_reference_child_reject layout (G p) F0 fuel nps endpointState parent right addresses initial
      (show SourceBoolMemoryAt endpointSource 1 hp right .dyn from right_at) sroot srhs si sv troot trhs ti tv
      (indexValue (wmod 3)) true rfl rfl rfl rfl rfl rfl rfl rfl map_free
      (by change hp.len right .dyn≤3;rw [right_length];exact Nat.le_refl _) SH initialMem endpoint_repr rfl rfl rejectBytes
      (fun c => c=33) reject_pointers (by rw [child_offset];rfl) (by decide)
  rw [child_offset] at middle hoff
  change mm=rejectFirstWord at middle
  subst mm
  have offsetEq : offset=⟨1056,by decide⟩ := Fin.ext hoff
  subst offset
  have hrLeft := sourceChildren left initial.leaf
  have h0 : ym.2.heap.get 0=some ⟨SB,sourceBoolMemory [true,false,false]⟩ := by
    change ym.2.heap.get 0=some ⟨SB,sourceBoolMemory (MObj.elems .dyn (redirectHeap.get left))⟩ at hrLeft
    simpa only [redirectHeap,Heap.setField,Heap.get_set_ne hp parent left (by decide),left_values] using hrLeft
  have h1 : ym.2.heap.get 1=some ⟨SB,sourceBoolMemory [false,true,false]⟩ := by
    have h := hr.leaf
    change ym.2.heap.get 1=some ⟨SB,sourceBoolMemory (MObj.elems .dyn (redirectHeap.get right))⟩ at h
    simpa only [seq_mid_values] using h
  have h2 : ym.2.heap.get 2=some ⟨SS,data 1⟩ := hr.parent
  have pointerRead : (Source.readLoc (E := E) (Γ := SourceCtx) F0 (τ := SB) (.mem 2 1)).run ym=(.ok (.memRef rfl 1),ym) := hr.read_child F0
  refine ⟨ym,hs1,he2,items,typed,code1,code2,whole,hr,?_,pointerRead,?_,byte,hl,hstack,mem1,words1,?_,effects⟩
  · rw [h0,h1,h2]
  · intro rollback
    have old := rollback.read_child F0
    have bad := congrArg Prod.fst (old.symm.trans pointerRead)
    cases bad
  · exact halloc ⟨48,by decide⟩ (by decide)
      ((initial_allocator.localWrite 5 (by decide) (by decide) (.val (wmod 3))).localWrite 6 (by decide) (by decide) (.val (bword true)))

/-- Complete OLD and actual successful-prefix word vectors for the rejecting
program. No failed-suffix target state is invented. -/
theorem named_sequence_reject_vectors :
    [0,1,2,3,4,5,6,7,16,17,18,19,24,25,26,27,32,33].map endpointWord.mem=
      [w[48],w[32],w[16],w[24],w[32],w[3],w[1],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[16]] ∧
    [0,1,2,3,4,5,6,7,16,17,18,19,24,25,26,27,32,33].map rejectFirstWord.mem=
      [w[48],w[32],w[16],w[24],w[32],w[3],w[1],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[24]] := by
  first | rfl | decide

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_sequence_late_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_sequence_late_reject
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_sequence_reject_vectors' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms named_sequence_reject_vectors

private theorem reject_initial_byte (e : Nat × Nat) (he : e∈byteTable) :
    Environment.readMemory rejectBytes (32*e.1) 32=Semantics.wordBytes (if e.1=5 then 3 else e.2) := by
  by_cases hx : e.1=5
  · rw [if_pos hx,hx];exact written_read bytes 160 3
  · rw [if_neg hx]
    unfold rejectBytes
    rw [readMemory_write_frame]
    · exact initial_byte_cell e he
    · simp only [Environment.wordBytes_length];omega

/-- Complete physical INITIAL/prefix images for the rejected suffix. No
post-revert byte buffer is asserted: the suffix did not execute a store. -/
theorem named_sequence_reject_byte_vectors :
    byteTable.map (fun e => Environment.readMemory rejectBytes (32*e.1) 32)=
      byteTable.map (fun e => Semantics.wordBytes (if e.1=5 then 3 else e.2)) ∧
    byteTable.map (fun e => Environment.readMemory rejectFirstBytes (32*e.1) 32)=
      byteTable.map (fun e => Semantics.wordBytes (if e.1=33 then 768 else if e.1=5 then 3 else e.2)) := by
  refine ⟨List.map_congr_left (fun e he => reject_initial_byte e he),?_⟩
  apply List.map_congr_left
  intro e he
  by_cases hx : e.1=33
  · rw [if_pos hx,hx];exact written_read rejectBytes 1056 768
  · rw [if_neg hx]
    unfold rejectFirstBytes
    rw [readMemory_write_frame]
    · exact reject_initial_byte e he
    · simp only [Environment.wordBytes_length];omega

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_sequence_reject_byte_vectors' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_sequence_reject_byte_vectors


private def deleteCode : List Evm.Instr := structChildDeleteCode (C := C) 1 troot "items" (.simple (.local ti))
private def deletedWord : Machine := writeMachine outputWord 18 (.val (bword false))
private def deletedBytes : Environment.Memory := Environment.writeBytes outputBytes 576 (Semantics.wordBytes 0)
private theorem delete_expected_write : outputHeap.writeAddr (.index left .dyn index) false=some hp := by
  have len : outputHeap.len left .dyn=3 := by
    simp only [Heap.len,outputHeap,Heap.get_set_same,MObj.elems_setElem,List.length_set]
    exact left_length
  change (if index.1.toNat<outputHeap.len left .dyn then some _ else none)=_
  rw [if_pos (by rw [len];decide)]
  simp only [outputHeap,Heap.get_set_same,MObj.setElem_dyn]
  rfl
private theorem delete_head : Evm.run
    ((([.push (.val (bword false)),.mload 4] : List Evm.Instr) ++ readFieldCode 1) ++ [.mload 5]) outputWord=
    .ok (((outputWord.push (.val (bword false))).push (.val (wmod 16))).push (.val (wmod 1))) 0 := by
  have firstRun : Evm.run ([.push (.val (bword false)),.mload 4] : List Evm.Instr) outputWord=
      .ok ((outputWord.push (.val (bword false))).push (.val (wmod 32))) 0 := by
    simp only [Evm.run,exec_cons_zero,Evm.Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil]
    rfl
  have fieldRun : Evm.run (readFieldCode 1) ((outputWord.push (.val (bword false))).push (.val (wmod 32)))=
      .ok ((outputWord.push (.val (bword false))).push (.val (wmod 16))) 0 := by
    rw [readFieldCode,run_append_ok (fieldAddr_run (outputWord.push (.val (bword false))) (wmod 32) 1)]
    rfl
  rw [run_append_ok (run_append_ok firstRun ▸ fieldRun)]
  rfl
private theorem delete_expected_word : Evm.run deleteCode outputWord=.ok deletedWord 0 := by
  have codeEq : deleteCode=((([.push (.val (bword false)),.mload 4] : List Evm.Instr) ++ readFieldCode 1) ++ [.mload 5]) ++ writeArrayStackCode := by
    unfold deleteCode structChildDeleteCode structChildWriteCode
    have offset : fieldOffset (structDef S) "items"=1 := by rw [layout.target_fields];decide
    rw [offset]
    rfl
  have arr : ArrayRepr outputHeap left (base left.id) outputWord :=
    (repr.heap.arrays left).set 1 (by change 1<hp.len left .dyn;rw [left_length];decide) true (.val (bword true)) rfl
  rw [codeEq,run_append_ok delete_head]
  rcases writeArray_correct arr (wmod 1) false (.val (bword false)) rfl with
    ⟨out,ht,hw,_⟩ | ⟨bad,_⟩
  · rw [writeArrayStackCode,
      arrayStack_append_eq (outputWord.push (.val (bword false))) (wmod 16) (wmod 1) 3 (by decide) (by rfl),←writeArrayCode]
    exact hw
  · change outputHeap.writeAddr (.index left .dyn index) false=none at bad
    rw [delete_expected_write] at bad
    cases bad


/-- A materially changed FIRST named-child assignment supplies every reached
input to actual delete. Both Source pipelines execute one RItems program;
old aliases/parent/tag/neighbor and the saved stack/allocator remain framed. -/
theorem named_child_delete_client (p : Roadmap.Pipeline) (fuel nps : Nat) :
    ∃ mid z : Source.EMState E SourceCtx,
      (Source.execS (G p) F0 (fuel+6) nps none
        (.expr (sourceStructChildAssign layout sroot si sv) : Source.RStmt E [] false .body SourceCtx SourceCtx)
        inputSource.1).run (.nil,inputSource.2)=(.ok (.normal mid.1),(.nil,mid.2)) ∧
      (Source.execS (G p) F0 (fuel+5) nps none
        (.expr (sourceStructChildDelete layout sroot si) : Source.RStmt E [] false .body SourceCtx SourceCtx)
        mid.1).run (.nil,mid.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      (Source.execItems (G p) F0 (fuel+7) nps none
        (.stmt (.expr (sourceStructChildAssign layout sroot si sv))
          (.stmt (.expr (sourceStructChildDelete layout sroot si)) .nil) : Source.RItems E [] false .body SourceCtx SourceCtx)
        inputSource.1).run (.nil,inputSource.2)=(.ok (.normal z.1),(.nil,z.2)) ∧
      Prog.run inputState (.cons (.assignMem (.index .dyn (.loc (.field (.var troot map_free) "items" layout.child_type)) (.simple (.local ti))) (.val (.simple (.local tv))))
        (.cons (.deleteMem (.loc (.index .dyn (.loc (.field (.var troot map_free) "items" layout.child_type)) (.simple (.local ti)))) rfl) .nil))=
          .ok ⟨inputState.withHeap hp,List.prefix_refl _⟩ ∧
      Evm.run (code++deleteCode) inputWord=.ok deletedWord 0 ∧
      SourceBoolStructAt z 2 hp parent addresses layout ∧ Source.MemOK E SH z ∧
      StateRepr 1 1 8 ((Frag.init Γ).push (.val .uint) .ok |>.push (.val .bool) .ok) (inputState.withHeap hp) base deletedWord ∧
      WordFrame deletedWord deletedBytes (fun c => (base left.id).val≤c ∧ c<(base left.id).val+1+hp.len left .dyn) ∧
      Environment.cryptoStep (.op .MSTORE)
        ⟨lenU 576 (by decide)::lenU 1 (by decide)::[lenU 11 (by decide),lenU 22 (by decide)],bytes⟩=
          some ⟨[lenU 11 (by decide),lenU 22 (by decide)],outputBytes⟩ ∧
      Environment.cryptoStep (.op .MSTORE)
        ⟨lenU 576 (by decide)::lenU 0 (by decide)::[lenU 11 (by decide),lenU 22 (by decide)],outputBytes⟩=
          some ⟨[lenU 11 (by decide),lenU 22 (by decide)],deletedBytes⟩ ∧
      StructAllocatorRepr hp base 8 ⟨48,by decide⟩ deletedWord ∧
      [mid.2.heap.get 0,mid.2.heap.get 1,mid.2.heap.get 2]=
        [some ⟨SB,sourceBoolMemory [true,true,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 0⟩] ∧
      z.1=inputSource.1 ∧ deletedWord.stack=[w[42]] ∧
      [z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2]=
        [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 0⟩] ∧
      z.1.get salias=.memRef rfl 0 ∧
      (Source.readLoc (E := E) (Γ := SourceCtx) F0 (τ := .bool) (.mem 0 1)).run mid=(.ok (.bool true),mid) ∧
      (Source.readLoc (E := E) (Γ := SourceCtx) F0 (τ := .bool) (.mem 0 1)).run z=(.ok (.bool false),z) ∧
      z.2.ex=inputSource.2.ex ∧ z.2.events=inputSource.2.events ∧
      z.2.logs=inputSource.2.logs ∧ z.2.fnLocals=inputSource.2.fnLocals := by
  obtain ⟨mid,_,_,hs1,ht1,hc1,obs,mok,rep,phys,byte1,_,_,_,_,_,locals,_,alloc,_,sourceOther,ex1,ev1,logs1,fn1⟩ :=
    named_child_client p (fuel+1) nps
  have bound : index.1.toNat<outputHeap.len left .dyn := by
    change index.1.toNat<(MObj.elems .dyn (outputHeap.get left)).length
    rw [final_left];decide
  obtain ⟨out,z,target,offset,ht2,_,_,hs2,typed,hcode,hr,hm,hmword,hphys,hoff,hbyte2,_,_,_,_,_,_,hloc,_,halloc,_,hsource,hex,hev,hlog,hfn⟩ :=
    delete_struct_child_physical layout (G p) F0 fuel nps (inputState.withHeap outputHeap) parent addresses obs
      sroot si troot (.simple (.local ti)) index (by rw [locals];rfl) (by rw [locals];rfl)
      rfl rfl map_free bound SH mok rep rfl outputBytes phys
  have sameHeap : out=hp := Option.some.inj (ht2.symm.trans delete_expected_write)
  subst out
  have sameWord : target=deletedWord := (Out.ok.inj (hcode.symm.trans delete_expected_word)).1
  subst target
  have offsetEq : offset=⟨576,by decide⟩ := Fin.ext hoff
  subst offset
  have midIndex : outputHeap.index left .dyn index=some true := by
    change (MObj.elems .dyn (outputHeap.get left))[index.1.toNat]?=some true
    rw [final_left];rfl
  have finalIndex : hp.index left .dyn index=some false := by
    change (MObj.elems .dyn (hp.get left))[index.1.toNat]?=some false
    rw [left_values];rfl
  have s0 : z.2.heap.get 0=some ⟨SB,sourceBoolMemory [true,false,false]⟩ := by
    have h := hr.leaf
    change z.2.heap.get 0=some ⟨SB,sourceBoolMemory (MObj.elems .dyn (hp.get left))⟩ at h
    simpa only [left_values] using h
  have s1 : z.2.heap.get 1=some ⟨SB,sourceBoolMemory [false,true,false]⟩ := by
    rw [hsource 1 (by decide),sourceOther 1 (by decide)];rfl
  have s2 : z.2.heap.get 2=some ⟨SS,data 0⟩ := by
    rw [hsource 2 (by decide),sourceOther 2 (by decide)];rfl
  have m0 : mid.2.heap.get 0=some ⟨SB,sourceBoolMemory [true,true,false]⟩ := by
    have h := obs.leaf
    change mid.2.heap.get 0=some ⟨SB,sourceBoolMemory (MObj.elems .dyn (outputHeap.get left))⟩ at h
    simpa only [final_left] using h
  have m1 : mid.2.heap.get 1=some ⟨SB,sourceBoolMemory [false,true,false]⟩ := by rw [sourceOther 1 (by decide)];rfl
  have m2 : mid.2.heap.get 2=some ⟨SS,data 0⟩ := by rw [sourceOther 2 (by decide)];rfl
  refine ⟨mid,z,hs1,hs2,source_items_pair_run (G p) F0 (fuel+1) nps _ _ inputSource mid z hs1 hs2,
    intrinsic_heap_pair_run inputState _ _ outputHeap hp ht1 typed,?_,hr,hm,hmword,hphys,
    byte1,hbyte2 [lenU 11 (by decide),lenU 22 (by decide)],halloc ⟨48,by decide⟩ (by decide) alloc,?_,hloc.trans locals,?_,?_,?_,(obs.leaf.read_iff F0 index true).mpr midIndex,(hr.leaf.read_iff F0 index false).mpr finalIndex,hex.trans ex1,hev.trans ev1,hlog.trans logs1,hfn.trans fn1⟩
  · rw [run_append_ok hc1];exact hcode
  · rw [m0,m1,m2]
  · rfl
  · rw [s0,s1,s2]
  · rw [hloc,locals];rfl

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_child_delete_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_child_delete_client


/-- Complete final word vector and skipped-delete discrimination. -/
theorem named_delete_word_vectors :
    [0,1,2,3,4,5,6,7,16,17,18,19,24,25,26,27,32,33].map deletedWord.mem=
      [w[48],w[32],w[16],w[24],w[32],w[1],w[1],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[16]] ∧
    deletedWord.mem 18≠outputWord.mem 18 ∧
    [MObj.elems .dyn (hp.get left),MObj.elems .dyn (outputHeap.get left),MObj.elems .dyn (hp.get left)]=
      [[true,false,false],[true,true,false],[true,false,false]] := by
  constructor
  · rfl
  · constructor
    · decide
    · rw [left_values,final_left]

/-- ALL eighteen full32-byte cell images after the second component store. -/
theorem named_delete_byte_vectors :
    byteTable.map (fun e => Environment.readMemory deletedBytes (32*e.1) 32)=
      byteTable.map (fun e => Semantics.wordBytes e.2) := by
  apply List.map_congr_left
  intro e he
  by_cases hx : e.1=18
  · have hv : e.2=0 := by
      simp only [byteTable,List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all
    rw [hx,hv]
    exact written_read outputBytes 576 0
  · unfold deletedBytes outputBytes
    rw [readMemory_write_frame,readMemory_write_frame]
    · exact initial_byte_cell e he
    all_goals simp only [Environment.wordBytes_length];omega

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_delete_word_vectors' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms named_delete_word_vectors
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_delete_byte_vectors' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_delete_byte_vectors


private def aliasDst : Source.Idx SourceCtx SB := .there (.there (.there .here))
private def aliasTarget : Idx Δ (.mem B) := .there (.there (.there .here))
private def aliasSource : Source.EMState E SourceCtx := (inputSource.1.set aliasDst (.memRef rfl 0),inputSource.2)
private def aliasState : State C Δ := inputState.setLocal aliasTarget (some left)
private def aliasWord : Machine := writeMachine inputWord 3 (.val (wmod 16))
private def aliasBytes : Environment.Memory := Environment.writeBytes bytes 96 (Semantics.wordBytes 512)
private def aliasCode : List Evm.Instr := structSelectedAliasCode 1 aliasTarget troot "items"
private theorem alias_pointers : PointerFrame inputWord bytes (fun c => c=3) := by
  constructor
  · intro c hc;subst c;decide
  · intro c hc;subst c
    refine ⟨wmod 24,rfl,by decide,?_⟩
    exact initial_byte_cell (3,768) (by decide)

/-- Existing RIGHT local is rebound to the INITIAL named member LEFT, with
retained old aliases/objects and concrete scaled local-pointer bytes. Both
Source pipelines execute; no constructor or child copy is performed. -/
theorem named_selected_alias_client (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G p) F0 (fuel+3) (sourceStructSelectedAlias layout aliasDst sroot)).run inputSource=
      (.ok (.val (.memRef rfl 0)),aliasSource) ∧
    (Source.execS (G p) F0 (fuel+4) nps none
      (.expr (sourceStructSelectedAlias layout aliasDst sroot) : Source.RStmt E [] false .body SourceCtx SourceCtx)
      inputSource.1).run (.nil,inputSource.2)=(.ok (.normal aliasSource.1),(.nil,aliasSource.2)) ∧
    Stmt.run inputState (.rebindMem aliasTarget (.alias (.loc (.field (.var troot map_free) "items" layout.child_type))))=
      .ok ⟨aliasState,List.prefix_refl _⟩ ∧
    Evm.run aliasCode inputWord=.ok aliasWord 0 ∧
    SourceBoolStructAt aliasSource 2 aliasState.heap parent addresses layout ∧
    Source.MemOK E SH aliasSource ∧
    StateRepr 1 1 8 ((Frag.init Γ).push (.val .uint) .ok |>.push (.val .bool) .ok) aliasState base aliasWord ∧
    PointerFrame aliasWord aliasBytes (fun c => c=3 ∨ c=3) ∧
    WordFrame aliasWord aliasBytes (fun c => (base left.id).val≤c ∧ c<(base left.id).val+1+hp.len left .dyn) ∧
    Environment.cryptoStep (.op .MSTORE)
      ⟨lenU 96 (by decide)::lenU 512 (by decide)::[lenU 11 (by decide),lenU 22 (by decide)],bytes⟩=
        some ⟨[lenU 11 (by decide),lenU 22 (by decide)],aliasBytes⟩ ∧
    (∀ j,j<96 ∨ 128≤j → aliasBytes j=bytes j) ∧
    aliasSource.2=inputSource.2 ∧ aliasState.heap=hp ∧
    [inputSource.1.get aliasDst,aliasSource.1.get aliasDst,aliasSource.1.get salias]=
      [.memRef rfl 1,.memRef rfl 0,.memRef rfl 0] ∧
    TEnv.get aliasTarget aliasState.env=some left ∧ aliasWord.stack=[w[42]] ∧
    StructAllocatorRepr hp base 8 ⟨48,by decide⟩ aliasWord ∧
    (Source.readLoc (E := E) (Γ := SourceCtx) F0 (τ := .bool) (.mem 0 1)).run aliasSource=(.ok (.bool false),aliasSource) ∧
    (Source.readLoc (E := E) (Γ := SourceCtx) F0 (τ := .bool) (.mem 1 1)).run aliasSource=(.ok (.bool true),aliasSource) := by
  have separate : ∀ c,(base left.id).val≤c ∧ c<(base left.id).val+1+hp.len left .dyn → c≠cellOf 1 aliasTarget := by
    intro c hc
    change 16≤c ∧ c<16+1+hp.len left .dyn at hc
    change c≠3
    omega
  obtain ⟨he,hs,ht,hw,hr,hchild,hm,hwords,hptr,hnum,⟨offset,hoff,hbyte⟩,_,houtside,_,_,_,hlocal,hstack,halloc⟩ :=
    select_struct_alias_physical layout (G p) F0 fuel nps inputState parent addresses source_at
      aliasDst sroot aliasTarget troot rfl rfl map_free SH memOK repr bytes (fun c => c=3)
      (fun c => (base left.id).val≤c ∧ c<(base left.id).val+1+hp.len left .dyn)
      alias_pointers child_frame rfl (by decide) separate
  have offsetEq : offset=⟨96,by decide⟩ := Fin.ext hoff
  subst offset
  have hit : hp.index left .dyn index=some false := by
    change (MObj.elems .dyn (hp.get left))[index.1.toNat]?=some false
    rw [left_values];rfl
  have oldHit : hp.index right .dyn index=some true := by
    change (MObj.elems .dyn (hp.get right))[index.1.toNat]?=some true
    rw [right_values];rfl
  have oldLeaf : SourceBoolMemoryAt aliasSource 1 hp right .dyn := right_at
  refine ⟨he,hs,ht,hw,hr,hm,hwords,hptr,hnum,hbyte [lenU 11 (by decide),lenU 22 (by decide)],houtside,rfl,rfl,?_,hlocal,?_,
    halloc ⟨48,by decide⟩ (by decide) allocator,(hchild.read_iff F0 index false).mpr hit,(oldLeaf.read_iff F0 index true).mpr oldHit⟩
  · rfl
  · rfl

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_selected_alias_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_selected_alias_client


/-- Complete local/object/word observations, not selected cells alone. The
old RIGHT object is retained, but that local now shares LEFT with the old alias. -/
theorem named_selected_alias_vectors :
    [0,1,2,3,4,5,6,7,16,17,18,19,24,25,26,27,32,33].map aliasWord.mem=
      [w[48],w[32],w[16],w[16],w[32],w[1],w[1],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[16]] ∧
    aliasSource.1=.cons (.bool true) (.cons (sourceUint index) (.cons (.memRef rfl 2)
      (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) (.cons (.memRef rfl 2) .nil))))) ∧
    [aliasSource.2.heap.get 0,aliasSource.2.heap.get 1,aliasSource.2.heap.get 2]=
      [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 0⟩] ∧
    [MObj.elems .dyn (aliasState.heap.get left),MObj.elems .dyn (aliasState.heap.get right)]=
      [[true,false,false],[false,true,false]] ∧
    aliasWord.mem 3≠inputWord.mem 3 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · first | rfl | decide
  · rfl
  · rfl
  · change [MObj.elems .dyn (hp.get left),MObj.elems .dyn (hp.get right)]=_
    rw [left_values,right_values]
  · decide

/-- All18complete32-byte images retain scaled pointer addresses. -/
theorem named_selected_alias_byte_vectors :
    byteTable.map (fun e => Environment.readMemory aliasBytes (32*e.1) 32)=
      byteTable.map (fun e => Semantics.wordBytes (if e.1=3 then 512 else e.2)) := by
  apply List.map_congr_left
  intro e he
  by_cases hx : e.1=3
  · rw [if_pos hx,hx]
    exact written_read bytes 96 512
  · rw [if_neg hx]
    unfold aliasBytes
    rw [readMemory_write_frame]
    · exact initial_byte_cell e he
    · simp only [Environment.wordBytes_length];omega

/-- Actual wrong unscaled encoding cannot represent the reached pointer,
and the existing Source evaluator rejects an insufficient horizon unchanged. -/
theorem named_selected_alias_controls (p : Roadmap.Pipeline) :
    ¬ PointerCellAt aliasWord (Environment.writeBytes bytes 96 (Semantics.wordBytes 16)) 3 ∧
    (∀ n,n≤2 → (Source.evalE (G p) F0 n (sourceStructSelectedAlias layout aliasDst sroot)).run inputSource=
      (.error .timeout,inputSource)) := by
  constructor
  · intro h
    obtain ⟨v,hw,_,hb⟩ := h
    have actual : aliasWord.mem 3=.val (wmod 16) := rfl
    have same : v=wmod 16 := Evm.Word.val.inj (hw.symm.trans actual)
    subst v
    have read := written_read bytes 96 16
    have bad : Semantics.wordBytes 16=Semantics.wordBytes 512 := read.symm.trans hb
    have different : Semantics.wordBytes 16≠Semantics.wordBytes 512 := by decide
    exact different bad
  · exact source_struct_select_low_horizon layout (G p) F0 inputSource aliasDst sroot

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_selected_alias_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_selected_alias_vectors
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_selected_alias_byte_vectors' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_selected_alias_byte_vectors
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.named_selected_alias_controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_selected_alias_controls


private def copyFrame : Source.Fr :=
  { F0 with cd := (List.replicate 31 0++[1])++(List.replicate 32 0)++(List.replicate 31 0++[1]) }
private def copyVals : List (Source.Val E.layout .bool) := [.bool true,.bool false,.bool true]
private def copyObject : MObj H B := ⟨[true,false,true],by decide⟩
private def copyHeap := hp.alloc copyObject
private def copyExt : H <+: H++[B] := List.prefix_append H [B]
private def copyAddresses := allocatedSourceAddress addresses H.length inputSource.2.heap.next
private def copySource : Source.EMState E SourceCtx :=
  (inputSource.1,{inputSource.2 with heap := (inputSource.2.heap.alloc ⟨SB,sourceBoolMemory [true,false,true]⟩).1})
private theorem copy_decoded : sourceCalldataBoolValues E copyFrame 0 3=.ok copyVals := by
  first | rfl | decide

/-- ACTUAL Source raw-word copy reaches a fresh represented intrinsic object.
The existing populated named parent and both old children survive; no target
copy/allocator code or ABI entry validity is inferred. -/
theorem source_calldata_copy_client :
    (Source.cdToMem copyFrame SB 0 3).run inputSource=(.ok (.val (.memRef rfl 3)),copySource) ∧
    Heap.Keeps copyExt hp copyHeap.1 ∧
    SourceBoolStructAt copySource 2 copyHeap.1 (parent.wk copyExt) copyAddresses layout ∧
    SourceBoolMemoryAt copySource 3 copyHeap.1 copyHeap.2 .dyn ∧ Source.MemOK E SH copySource ∧
    [copyHeap.2.id,(parent.wk copyExt).id,(left.wk copyExt).id,(right.wk copyExt).id]=[3,2,0,1] ∧
    MObj.elems .dyn (copyHeap.1.get copyHeap.2)=[true,false,true] ∧
    [copySource.2.heap.get 0,copySource.2.heap.get 1,copySource.2.heap.get 2,copySource.2.heap.get 3]=
      [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,
       some ⟨SS,data 0⟩,some ⟨SB,sourceBoolMemory [true,false,true]⟩] ∧
    copySource.1=inputSource.1 ∧ copySource.2.ex=inputSource.2.ex ∧ copySource.2.events=inputSource.2.events ∧
    copySource.2.logs=inputSource.2.logs ∧ copySource.2.fnLocals=inputSource.2.fnLocals := by
  have result := source_at.cd_bool_copy copyFrame 0 3 (by decide) SH memOK
  rw [copy_decoded] at result
  obtain ⟨valid,run,keep,old,new,mok,_⟩ := result
  refine ⟨run,keep,old,new,mok,rfl,?_,?_,rfl,rfl,rfl,rfl,rfl⟩
  · change MObj.elems .dyn ((hp.alloc copyObject).1.get (hp.alloc copyObject).2)=_
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
    rfl
  · rfl

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_calldata_copy_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_calldata_copy_client


private abbrev CopyCtx : Source.RCtx := .array .calldata .bool none::SourceCtx
private def copyExprInput : Source.EMState E CopyCtx := (.cons (.cdRef rfl 0 3) inputSource.1,inputSource.2)
private def copyExprOutput : Source.EMState E CopyCtx := (copyExprInput.1,copySource.2)

/-- Actual resolved conversion in BOTH Source pipelines, with original nps;
insufficient horizons retain the real input rather than an invented copy. -/
theorem source_calldata_copy_expression (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G p) copyFrame (fuel+2) (sourceBoolCalldataCopy (Source.Idx.here : Source.Idx CopyCtx (.array .calldata .bool none)))).run copyExprInput=
      (.ok (.val (.memRef rfl 3)),copyExprOutput) ∧
    (Source.execS (G p) copyFrame (fuel+3) nps none
      (.expr (sourceBoolCalldataCopy Source.Idx.here) : Source.RStmt E [] false .body CopyCtx CopyCtx) copyExprInput.1).run (.nil,copyExprInput.2)=
        (.ok (.normal copyExprOutput.1),(.nil,copyExprOutput.2)) ∧
    (∀ n,n≤1 → (Source.evalE (G p) copyFrame n (sourceBoolCalldataCopy (Source.Idx.here : Source.Idx CopyCtx (.array .calldata .bool none)))).run copyExprInput=
      (.error .timeout,copyExprInput)) := by
  have run : (Source.evalE (G p) copyFrame (fuel+2) (sourceBoolCalldataCopy (Source.Idx.here : Source.Idx CopyCtx (.array .calldata .bool none)))).run copyExprInput=
      (.ok (.val (.memRef rfl 3)),copyExprOutput) := by
    rw [source_cd_bool_eval (G p) copyFrame fuel copyExprInput Source.Idx.here 0 3 rfl,source_cd_bool_run,copy_decoded]
    rfl
  refine ⟨run,source_expr_statement_run (G p) copyFrame (fuel+2) nps _ copyExprInput copyExprOutput _ run,?_⟩
  intro n hn
  match n with
  | 0 => rfl
  | 1 => rfl
  | n+2 => omega

private def badCopyFrame : Source.Fr :=
  { F0 with cd := (List.replicate 31 0++[1])++(List.replicate 31 0++[2])++(List.replicate 32 0) }

/-- Real first word validates TRUE, then word2 is rejected BEFORE allocation.
The old populated source heap/state survives; this is not transaction rollback. -/
theorem source_calldata_copy_late_error :
    ([0].mapM (fun j => Source.EM.lift (E := E) (Γ := SourceCtx)
      (Source.decodeWord E.layout (Source.cdWordAt badCopyFrame (32*j)) .bool))).run inputSource=
        (.ok [.bool true],inputSource) ∧
    (Source.EM.lift (E := E) (Γ := SourceCtx) (Source.decodeWord E.layout (Source.cdWordAt badCopyFrame 32) .bool)).run inputSource=
      (.error (.revert []),inputSource) ∧
    (Source.cdToMem badCopyFrame SB 0 3).run inputSource=(.error (.revert []),inputSource) := by
  exact source_cd_bool_first_error badCopyFrame 0 3 inputSource [0] [2] 1 [.bool true] (.revert []) rfl (by rfl) (by rfl)

private def zeroCopyFrame : Source.Fr := {F0 with cd := []}
private def zeroCopySource (n : Nat) : Source.EMState E SourceCtx :=
  (inputSource.1,{inputSource.2 with heap := (inputSource.2.heap.alloc ⟨SB,sourceBoolMemory (List.replicate n false)⟩).1})

/-- Arbitrary runtime length, including literal zero and element31/32/33.
Positive empty-input reads here are Source zero-padding, NOT valid ABI entry. -/
theorem source_calldata_copy_zero_family (off n : Nat) :
    (Source.cdToMem zeroCopyFrame SB off n).run inputSource=(.ok (.val (.memRef rfl 3)),zeroCopySource n) ∧
    [ (zeroCopySource n).2.heap.get 0,(zeroCopySource n).2.heap.get 1,
      (zeroCopySource n).2.heap.get 2,(zeroCopySource n).2.heap.get 3]=
      [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,
       some ⟨SS,data 0⟩,some ⟨SB,sourceBoolMemory (List.replicate n false)⟩] ∧
    (∀ i,i<n → (Source.memElem (E := E) (Γ := SourceCtx) 3 i .bool).run (zeroCopySource n)=
      (.ok (.bool false),zeroCopySource n)) ∧
    (Source.memElem (E := E) (Γ := SourceCtx) 3 n .bool).run (zeroCopySource n)=
      (.error (.revert (Source.panicData .index)),zeroCopySource n) := by
  have object : (zeroCopySource n).2.heap.get 3=some ⟨SB,sourceBoolMemory (List.replicate n false)⟩ := rfl
  refine ⟨source_cd_bool_empty_run zeroCopyFrame rfl off n inputSource,?_,?_,?_⟩
  · rfl
  · intro i hi
    have read := source_bool_read (zeroCopySource n) 3 (List.replicate n false) object i (by simpa only [List.length_replicate] using hi)
    rw [List.getElem_replicate] at read
    exact read
  · exact source_bool_bounds (zeroCopySource n) 3 (List.replicate n false) object n (by simpa only [List.length_replicate] using Nat.le_refl n)

/-- Old aliases do not become the fresh copy, and source order is not rotated. -/
theorem source_calldata_copy_order_and_alias :
    copyHeap.2.id≠(left.wk copyExt).id ∧
    MObj.elems .dyn (copyHeap.1.get copyHeap.2)≠[false,true,true] ∧
    (Source.memElem (E := E) (Γ := SourceCtx) 3 2 .bool).run copySource=(.ok (.bool true),copySource) ∧
    (Source.memElem (E := E) (Γ := SourceCtx) 0 2 .bool).run copySource=(.ok (.bool false),copySource) := by
  obtain ⟨_,_,_,_,_,_,contents,_⟩ := source_calldata_copy_client
  refine ⟨by decide,?_,?_,?_⟩
  · rw [contents];decide
  · exact source_bool_read copySource 3 [true,false,true] rfl 2 (by decide)
  · exact source_bool_read copySource 0 [true,false,false] rfl 2 (by decide)

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_calldata_copy_expression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_calldata_copy_expression
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_calldata_copy_late_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_calldata_copy_late_error
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_calldata_copy_zero_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_calldata_copy_zero_family
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_calldata_copy_order_and_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_calldata_copy_order_and_alias


private def zeroCopyObject (n : Nat) (cap : n<2^256) : MObj H B :=
  ⟨List.replicate n false,by rw [List.length_replicate];exact cap⟩
private def zeroCopyHeap (n : Nat) (cap : n<2^256) := hp.alloc (zeroCopyObject n cap)

/-- A paired typed witness for EVERY intrinsically valid runtime length,
including literal zero and the element32 boundary. Reuses the real raw-input
copy result and published allocation observer, not a second constructor. -/
theorem source_calldata_copy_zero_pair (n : Nat) (cap : n<2^256) :
    Heap.Keeps copyExt hp (zeroCopyHeap n cap).1 ∧
    SourceBoolStructAt (zeroCopySource n) 2 (zeroCopyHeap n cap).1 (parent.wk copyExt) copyAddresses layout ∧
    SourceBoolMemoryAt (zeroCopySource n) 3 (zeroCopyHeap n cap).1 (zeroCopyHeap n cap).2 .dyn ∧
    Source.MemOK E SH (zeroCopySource n) ∧
    (zeroCopyHeap n cap).1.len (zeroCopyHeap n cap).2 .dyn=n ∧
    (∀ i : PrimTy.uint.Denote,i.1.toNat<n →
      (zeroCopyHeap n cap).1.index (zeroCopyHeap n cap).2 .dyn i=some false) ∧
    (zeroCopyHeap n cap).1.index (zeroCopyHeap n cap).2 .dyn (indexValue (wmod n))=none := by
  have result := source_at.cd_bool_copy zeroCopyFrame 0 n cap SH memOK
  rw [sourceCalldataBoolValues_empty zeroCopyFrame rfl] at result
  obtain ⟨valid,_,keep,old,new,mok,_⟩ := result
  have contents : MObj.elems .dyn ((zeroCopyHeap n cap).1.get (zeroCopyHeap n cap).2)=List.replicate n false := by
    change MObj.elems .dyn ((hp.alloc (zeroCopyObject n cap)).1.get (hp.alloc (zeroCopyObject n cap)).2)=_
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
    exact List.map_id'' (fun _ => rfl) _
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro R q
    simpa only [sourceBoolValuePayload,List.map_replicate] using keep q
  · simpa only [sourceBoolValuePayload,List.map_replicate] using old
  · simpa only [sourceBoolValuePayload,List.map_replicate] using new
  · simpa only [sourceBoolValuePayload,List.map_replicate] using mok
  · simp only [Heap.len,contents,List.length_replicate]
  · intro i hi
    change (MObj.elems .dyn ((zeroCopyHeap n cap).1.get (zeroCopyHeap n cap).2))[i.1.toNat]?=some false
    rw [contents]
    exact List.getElem?_replicate_of_lt hi
  · change (MObj.elems .dyn ((zeroCopyHeap n cap).1.get (zeroCopyHeap n cap).2))[(indexValue (wmod n)).1.toNat]?=none
    rw [contents]
    simp only [indexValue,Int.toNat_natCast,wmod,List.getElem?_replicate]
    rw [Nat.mod_eq_of_lt (show n<W from cap)]
    exact if_neg (Nat.lt_irrefl n)

/-- Explicit typed empty endpoint and actual valid element31/32 versus end33. -/
theorem source_calldata_copy_typed_boundaries :
    (zeroCopyHeap 0 (by decide)).1.index (zeroCopyHeap 0 (by decide)).2 .dyn (indexValue (wmod 0))=none ∧
    (zeroCopyHeap 33 (by decide)).1.index (zeroCopyHeap 33 (by decide)).2 .dyn (indexValue (wmod 31))=some false ∧
    (zeroCopyHeap 33 (by decide)).1.index (zeroCopyHeap 33 (by decide)).2 .dyn (indexValue (wmod 32))=some false ∧
    (zeroCopyHeap 33 (by decide)).1.index (zeroCopyHeap 33 (by decide)).2 .dyn (indexValue (wmod 33))=none := by
  obtain ⟨_,_,_,_,_,zeroReads,zeroEnd⟩ := source_calldata_copy_zero_pair 0 (by decide)
  obtain ⟨_,_,_,_,_,reads,last⟩ := source_calldata_copy_zero_pair 33 (by decide)
  exact ⟨zeroEnd,reads (indexValue (wmod 31)) (by decide),reads (indexValue (wmod 32)) (by decide),last⟩

/-- The same invalid second word rejects the actual resolved conversion and
statement in BOTH Source pipelines; no target post-revert state is claimed. -/
theorem source_calldata_copy_expression_error (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G p) badCopyFrame (fuel+2) (sourceBoolCalldataCopy (Source.Idx.here : Source.Idx CopyCtx (.array .calldata .bool none)))).run copyExprInput=
      (.error (.revert []),copyExprInput) ∧
    (Source.execS (G p) badCopyFrame (fuel+3) nps none
      (.expr (sourceBoolCalldataCopy Source.Idx.here) : Source.RStmt E [] false .body CopyCtx CopyCtx) copyExprInput.1).run (.nil,copyExprInput.2)=
        (.error (.revert []),(.nil,copyExprInput.2)) := by
  have decoded : sourceCalldataBoolValues E badCopyFrame 0 3=.error (.revert []) := rfl
  have run : (Source.evalE (G p) badCopyFrame (fuel+2) (sourceBoolCalldataCopy (Source.Idx.here : Source.Idx CopyCtx (.array .calldata .bool none)))).run copyExprInput=
      (.error (.revert []),copyExprInput) := by
    rw [source_cd_bool_eval (G p) badCopyFrame fuel copyExprInput Source.Idx.here 0 3 rfl,source_cd_bool_run,decoded]
  exact ⟨run,source_expr_statement_error (G p) badCopyFrame (fuel+2) nps _ copyExprInput copyExprInput (.revert []) run⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_calldata_copy_zero_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_calldata_copy_zero_pair
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_calldata_copy_typed_boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_calldata_copy_typed_boundaries
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_calldata_copy_expression_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_calldata_copy_expression_error

private def checkedCopyZeros : MObj H B := ⟨[false,false,false],by decide⟩
private def checkedCopyMid := hp.alloc checkedCopyZeros

/-- Actual raw decoding fills the fresh ZERO destination with nonuniform TFT.
All old Source objects, intrinsic identities, and observer/world frames are
retained. The successful checked write is an explicit reached operation. -/
theorem source_checked_copy_client :
    checkedSourceFreshBools (E := E) copyFrame 0 3 hp (by decide)=.ok (some copyHeap.1) ∧
    checkedCalldataBools (sourceBoolTable copyFrame 0 copyVals) 0 checkedCopyMid.1 checkedCopyMid.2 .dyn 0 3 0=some copyHeap.1 ∧
    (Source.cdToMem copyFrame SB 0 3).run inputSource=(.ok (.val (.memRef rfl 3)),copySource) ∧
    Heap.Keeps copyExt hp copyHeap.1 ∧
    SourceBoolStructAt copySource 2 copyHeap.1 (parent.wk copyExt) copyAddresses layout ∧
    SourceBoolMemoryAt copySource 3 copyHeap.1 copyHeap.2 .dyn ∧ Source.MemOK E SH copySource ∧
    [copyHeap.2.id,(parent.wk copyExt).id,(left.wk copyExt).id,(right.wk copyExt).id]=[3,2,0,1] ∧
    [MObj.elems .dyn (checkedCopyMid.1.get checkedCopyMid.2),MObj.elems .dyn (copyHeap.1.get copyHeap.2),
     MObj.elems .dyn (copyHeap.1.get (left.wk copyExt)),MObj.elems .dyn (copyHeap.1.get (right.wk copyExt))]=
      [[false,false,false],[true,false,true],[true,false,false],[false,true,false]] ∧
    [copySource.2.heap.get 0,copySource.2.heap.get 1,copySource.2.heap.get 2,copySource.2.heap.get 3]=
      [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,
       some ⟨SS,data 0⟩,some ⟨SB,sourceBoolMemory [true,false,true]⟩] ∧
    copySource.1=inputSource.1 ∧ copySource.2.ex=inputSource.2.ex ∧ copySource.2.events=inputSource.2.events ∧
    copySource.2.logs=inputSource.2.logs ∧ copySource.2.fnLocals=inputSource.2.fnLocals := by
  have paired := source_at.checked_cd_bool_copy copyFrame 0 3 (by decide) SH memOK
  rw [copy_decoded] at paired
  obtain ⟨_,adapter,sourceRun,keep,old,new,mok,_⟩ := paired
  obtain ⟨_,trace,_⟩ := checkedSourceFreshBools_some copyFrame 0 3 hp (by decide) copyVals copy_decoded
  obtain ⟨_,_,_,_,_,ids,contents,tables,loc,ex,ev,logs,fn⟩ := source_calldata_copy_client
  refine ⟨adapter,trace,sourceRun,keep,old,new,mok,ids,?_,tables,loc,ex,ev,logs,fn⟩
  have mid : MObj.elems .dyn (checkedCopyMid.1.get checkedCopyMid.2)=[false,false,false] := by
    change MObj.elems .dyn ((hp.alloc checkedCopyZeros).1.get (hp.alloc checkedCopyZeros).2)=_
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
    rfl
  change Heap.Keeps copyExt hp copyHeap.1 at keep
  rw [mid,contents,keep left,keep right,MObj.elems_wk,MObj.elems_wk,left_values,right_values]
  rfl

/-- Identical real conversion/statement in BOTH published Source pipelines,
paired with the actual existing checked transfer, not emitted copy code. -/
theorem source_checked_copy_pipelines (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G p) copyFrame (fuel+2) (sourceBoolCalldataCopy (Source.Idx.here : Source.Idx CopyCtx (.array .calldata .bool none)))).run copyExprInput=
      (.ok (.val (.memRef rfl 3)),copyExprOutput) ∧
    (Source.execS (G p) copyFrame (fuel+3) nps none
      (.expr (sourceBoolCalldataCopy Source.Idx.here) : Source.RStmt E [] false .body CopyCtx CopyCtx) copyExprInput.1).run (.nil,copyExprInput.2)=
        (.ok (.normal copyExprOutput.1),(.nil,copyExprOutput.2)) ∧
    checkedSourceFreshBools (E := E) copyFrame 0 3 hp (by decide)=.ok (some copyHeap.1) := by
  obtain ⟨expression,statement,_⟩ := source_calldata_copy_expression p fuel nps
  exact ⟨expression,statement,source_checked_copy_client.1⟩

/-- Actual insufficient destination capacity is Option None, while Source
allocation/copy still succeeds. Bad word2 is instead a real decoder error. -/
theorem source_checked_copy_rejections :
    checkedSourceBools (E := E) copyFrame 0 3 hp left .dyn 1=.ok none ∧
    (Source.cdToMem copyFrame SB 0 3).run inputSource=(.ok (.val (.memRef rfl 3)),copySource) ∧
    checkedSourceFreshBools (E := E) badCopyFrame 0 3 hp (by decide)=.error (.revert []) ∧
    (Source.cdToMem badCopyFrame SB 0 3).run inputSource=(.error (.revert []),inputSource) ∧
    (sourceBoolTable copyFrame 0 copyVals).input=copyFrame.cd ∧
    (sourceBoolTable copyFrame 0 copyVals).objects 1=none := by
  refine ⟨?_,source_calldata_copy_client.1,?_,source_calldata_copy_late_error.2.2,?_,?_⟩
  · apply (checkedSourceBools_none_iff copyFrame 0 3 hp left .dyn 1 copyVals copy_decoded).2
    rw [left_length]
    decide
  · exact checkedSourceFreshBools_error badCopyFrame 0 3 hp (by decide) (.revert []) rfl
  · exact sourceBoolTable_input copyFrame 0 copyVals
  · exact sourceBoolTable_other copyFrame 0 1 copyVals (by decide)

/-- Every intrinsically valid runtime length uses the actual zero-padded
Source decode and actual checked write; literal empty is included. -/
theorem source_checked_copy_zero_family (n : Nat) (cap : n<2^256) :
    checkedSourceFreshBools (E := E) zeroCopyFrame 0 n hp cap=.ok (some (zeroCopyHeap n cap).1) ∧
    (Source.cdToMem zeroCopyFrame SB 0 n).run inputSource=(.ok (.val (.memRef rfl 3)),zeroCopySource n) ∧
    (zeroCopyHeap n cap).1.len (zeroCopyHeap n cap).2 .dyn=n ∧
    (zeroCopyHeap n cap).1.index (zeroCopyHeap n cap).2 .dyn (indexValue (wmod n))=none := by
  have decoded := sourceCalldataBoolValues_empty (E := E) zeroCopyFrame rfl 0 n
  obtain ⟨_,_,run⟩ := checkedSourceFreshBools_some zeroCopyFrame 0 n hp cap _ decoded
  obtain ⟨_,_,_,_,length,_,last⟩ := source_calldata_copy_zero_pair n cap
  refine ⟨?_,(source_calldata_copy_zero_family 0 n).1,length,last⟩
  simpa only [sourceBoolValuePayload,List.map_replicate] using run

/-- Stale/rotated substitution would produce different contents; the real
transfer changes FFF to TFT, preserving the separate old left alias TFF. -/
theorem source_checked_copy_negative :
    MObj.elems .dyn (copyHeap.1.get copyHeap.2)≠MObj.elems .dyn (checkedCopyMid.1.get checkedCopyMid.2) ∧
    MObj.elems .dyn (copyHeap.1.get copyHeap.2)≠[false,true,true] ∧
    MObj.elems .dyn (copyHeap.1.get copyHeap.2)≠MObj.elems .dyn (copyHeap.1.get (left.wk copyExt)) := by
  have fresh : MObj.elems .dyn (copyHeap.1.get copyHeap.2)=[true,false,true] :=
    source_calldata_copy_client.2.2.2.2.2.2.1
  have mid : MObj.elems .dyn (checkedCopyMid.1.get checkedCopyMid.2)=[false,false,false] := by
    change MObj.elems .dyn ((hp.alloc checkedCopyZeros).1.get (hp.alloc checkedCopyZeros).2)=_
    rw [Heap.get_alloc,MObj.elems_wk,MObj.elems_dyn]
    rfl
  have old : MObj.elems .dyn (copyHeap.1.get (left.wk copyExt))=[true,false,false] := by
    rw [source_calldata_copy_client.2.1 left,MObj.elems_wk,left_values]
    rfl
  rw [fresh,mid,old]
  decide

/-- Literal empty success and length33 complete endpoint witnesses consume the
same arbitrary-runtime checked-copy law, retaining the earlier read vectors. -/
theorem source_checked_copy_boundaries :
    checkedSourceFreshBools (E := E) zeroCopyFrame 0 0 hp (by decide)=.ok (some (zeroCopyHeap 0 (by decide)).1) ∧
    checkedSourceFreshBools (E := E) zeroCopyFrame 0 33 hp (by decide)=.ok (some (zeroCopyHeap 33 (by decide)).1) ∧
    (zeroCopyHeap 0 (by decide)).1.index (zeroCopyHeap 0 (by decide)).2 .dyn (indexValue (wmod 0))=none ∧
    (zeroCopyHeap 33 (by decide)).1.index (zeroCopyHeap 33 (by decide)).2 .dyn (indexValue (wmod 31))=some false ∧
    (zeroCopyHeap 33 (by decide)).1.index (zeroCopyHeap 33 (by decide)).2 .dyn (indexValue (wmod 32))=some false ∧
    (zeroCopyHeap 33 (by decide)).1.index (zeroCopyHeap 33 (by decide)).2 .dyn (indexValue (wmod 33))=none := by
  exact ⟨(source_checked_copy_zero_family 0 (by decide)).1,
    (source_checked_copy_zero_family 33 (by decide)).1,source_calldata_copy_typed_boundaries⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_checked_copy_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_checked_copy_client
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_checked_copy_pipelines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_checked_copy_pipelines
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_checked_copy_rejections' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_checked_copy_rejections
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_checked_copy_zero_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_checked_copy_zero_family
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_checked_copy_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_checked_copy_negative

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_checked_copy_boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_checked_copy_boundaries
private abbrev BindingCtx : Source.RCtx := SB::CopyCtx
private def bindingDst : Source.Idx BindingCtx SB := .there (.there salias)
private def bindingSrc : Source.Idx BindingCtx (.array .calldata .bool none) := .there .here
private def bindingIndex : Source.Idx BindingCtx (.int .u256) := .there (.there si)
private def bindingInput (n : Nat) : Source.EMState E BindingCtx :=
  (.cons (.memRef rfl 0) (.cons (.cdRef rfl 0 n)
    (inputSource.1.set si (sourceUint (indexValue (wmod 2))))),inputSource.2)
private def bindingMid (n : Nat) (bs : List Bool) : Source.EMState E BindingCtx :=
  ((bindingInput n).1,{inputSource.2 with heap := (inputSource.2.heap.alloc ⟨SB,sourceBoolMemory bs⟩).1})
private def bindingOutput (n : Nat) (bs : List Bool) : Source.EMState E BindingCtx :=
  ((bindingInput n).1.set bindingDst (.memRef rfl 3),(bindingMid n bs).2)
private def bindingRead (root : Source.Idx BindingCtx SB) : Source.RExpr E BindingCtx .bool :=
  .indexArray (.local root) (.local bindingIndex) rfl
private theorem binding_at (n : Nat) : SourceBoolStructAt (bindingInput n) 2 hp parent addresses layout :=
  ⟨source_at.parent,source_at.leaf⟩
private theorem binding_memOK (n : Nat) : Source.MemOK E SH (bindingInput n) := by
  have old : Source.Val.RefOK E inputSource.2.heap.ty (.memRef rfl 0 : Source.Val E.layout SB) := ⟨SB,rfl,rfl⟩
  have locals := Source.LocalsOK.set inputSource.1 si memOK.1.2
    (v := sourceUint (indexValue (wmod 2))) trivial
  exact ⟨⟨memOK.1.1,old, trivial,locals⟩,memOK.2⟩

/-- Actual allocating RHS, binding and statement in both pipelines, with the
same computed checked heap, derived old/fresh observers and retained aliases. -/
theorem source_copy_binding_client (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G p) copyFrame (fuel+2) (sourceBoolCalldataCopy bindingSrc)).run (bindingInput 3)=
      (.ok (.val (.memRef rfl 3)),bindingMid 3 [true,false,true]) ∧
    (Source.evalE (G p) copyFrame (fuel+3) (sourceBoolCalldataBind bindingDst bindingSrc)).run (bindingInput 3)=
      (.ok (.val (.memRef rfl 3)),bindingOutput 3 [true,false,true]) ∧
    (Source.execS (G p) copyFrame (fuel+4) nps none
      (.expr (sourceBoolCalldataBind bindingDst bindingSrc) : Source.RStmt E [] false .body BindingCtx BindingCtx)
      (bindingInput 3).1).run (.nil,(bindingInput 3).2)=
        (.ok (.normal (bindingOutput 3 [true,false,true]).1),(.nil,(bindingOutput 3 [true,false,true]).2)) ∧
    checkedSourceFreshBools (E := E) copyFrame 0 3 hp (by decide)=.ok (some copyHeap.1) ∧
    SourceBoolStructAt (bindingOutput 3 [true,false,true]) 2 copyHeap.1 (parent.wk copyExt) copyAddresses layout ∧
    SourceBoolMemoryAt (bindingOutput 3 [true,false,true]) 3 copyHeap.1 copyHeap.2 .dyn ∧
    Source.MemOK E SH (bindingOutput 3 [true,false,true]) ∧
    (bindingOutput 3 [true,false,true]).1.get bindingDst=.memRef rfl 3 ∧
    (bindingOutput 3 [true,false,true]).1.get .here=.memRef rfl 0 ∧
    (bindingOutput 3 [true,false,true]).1.get bindingIndex=sourceUint (indexValue (wmod 2)) := by
  have result := (binding_at 3).bind_cd_bool_copy (G p) copyFrame fuel nps bindingDst bindingSrc 0 3 rfl
    (by decide) SH (binding_memOK 3)
  rw [copy_decoded] at result
  obtain ⟨_,run,statement,adapter,_,old,new,mok,selected,other,_⟩ := result
  refine ⟨?_,run,statement,adapter,old,new,mok,selected,other SB .here (by decide),
    other (.int .u256) bindingIndex (by decide)⟩
  rw [source_cd_bool_eval (G p) copyFrame fuel (bindingInput 3) bindingSrc 0 3 rfl,source_cd_bool_run,copy_decoded]
  rfl

/-- Complete ordered local and Source heap tables; fresh and retained old
identities differ while all old intrinsic contents and parent fields survive. -/
theorem source_copy_binding_vectors :
    (bindingOutput 3 [true,false,true]).1=
      .cons (.memRef rfl 0) (.cons (.cdRef rfl 0 3) (.cons (.bool true)
        (.cons (sourceUint (indexValue (wmod 2))) (.cons (.memRef rfl 2)
          (.cons (.memRef rfl 1) (.cons (.memRef rfl 3) (.cons (.memRef rfl 2) .nil))))))) ∧
    [(bindingInput 3).1.get bindingDst,(bindingMid 3 [true,false,true]).1.get bindingDst,
      (bindingOutput 3 [true,false,true]).1.get bindingDst]=[.memRef rfl 0,.memRef rfl 0,.memRef rfl 3] ∧
    [(bindingOutput 3 [true,false,true]).2.heap.get 0,(bindingOutput 3 [true,false,true]).2.heap.get 1,
      (bindingOutput 3 [true,false,true]).2.heap.get 2,(bindingOutput 3 [true,false,true]).2.heap.get 3]=
      [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,
       some ⟨SS,data 0⟩,some ⟨SB,sourceBoolMemory [true,false,true]⟩] ∧
    [MObj.elems .dyn (copyHeap.1.get copyHeap.2),MObj.elems .dyn (copyHeap.1.get (left.wk copyExt)),
      MObj.elems .dyn (copyHeap.1.get (right.wk copyExt))]=[[true,false,true],[true,false,false],[false,true,false]] ∧
    [copyHeap.2.id,(left.wk copyExt).id,(right.wk copyExt).id,(parent.wk copyExt).id]=[3,0,1,2] ∧
    copyHeap.1.field (parent.wk copyExt) layout.tag_type=u7 ∧
    copyHeap.1.field (parent.wk copyExt) layout.child_type=left.wk copyExt ∧
    (bindingOutput 3 [true,false,true]).2.ex=(bindingInput 3).2.ex ∧
    (bindingOutput 3 [true,false,true]).2.events=(bindingInput 3).2.events ∧
    (bindingOutput 3 [true,false,true]).2.logs=(bindingInput 3).2.logs ∧
    (bindingOutput 3 [true,false,true]).2.fnLocals=(bindingInput 3).2.fnLocals := by
  have keep : Heap.Keeps copyExt hp copyHeap.1 := source_calldata_copy_client.2.1
  have fresh := source_calldata_copy_client.2.2.2.2.2.2.1
  refine ⟨rfl,rfl,rfl,?_,rfl,?_,?_,rfl,rfl,rfl,rfl⟩
  · rw [fresh,keep left,keep right,MObj.elems_wk,MObj.elems_wk,left_values,right_values]
    rfl
  · rw [keep.field parent layout.tag_type]
    rfl
  · rw [keep.field parent layout.child_type]
    rfl

/-- Reading through the actual reached binding differs from the retained old
alias and from reading before/skipping binding. The real RItems pair runs. -/
theorem source_copy_binding_reads (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G p) copyFrame (fuel+2) (bindingRead bindingDst)).run (bindingOutput 3 [true,false,true])=
      (.ok (.val (.bool true)),bindingOutput 3 [true,false,true]) ∧
    (Source.evalE (G p) copyFrame (fuel+2) (bindingRead .here)).run (bindingOutput 3 [true,false,true])=
      (.ok (.val (.bool false)),bindingOutput 3 [true,false,true]) ∧
    (Source.evalE (G p) copyFrame (fuel+2) (bindingRead bindingDst)).run (bindingInput 3)=
      (.ok (.val (.bool false)),bindingInput 3) ∧
    (Source.evalE (G p) copyFrame (fuel+2) (bindingRead bindingDst)).run (bindingMid 3 [true,false,true])=
      (.ok (.val (.bool false)),bindingMid 3 [true,false,true]) ∧
    (Source.execItems (G p) copyFrame (fuel+6) nps none
      (.stmt (.expr (sourceBoolCalldataBind bindingDst bindingSrc)) (.stmt (.expr (bindingRead bindingDst)) .nil) :
        Source.RItems E [] false .body BindingCtx BindingCtx) (bindingInput 3).1).run (.nil,(bindingInput 3).2)=
          (.ok (.normal (bindingOutput 3 [true,false,true]).1),(.nil,(bindingOutput 3 [true,false,true]).2)) := by
  obtain ⟨_,_,_,_,_,fresh,_,dst,ret,index⟩ := source_copy_binding_client p fuel nps
  have keep : Heap.Keeps copyExt hp copyHeap.1 := source_calldata_copy_client.2.1
  have contents := source_calldata_copy_client.2.2.2.2.2.2.1
  have old : SourceBoolMemoryAt (bindingOutput 3 [true,false,true]) 0 copyHeap.1 (left.wk copyExt) .dyn := by
    unfold SourceBoolMemoryAt
    rw [keep left,MObj.elems_wk,left_values]
    rfl
  have initial : SourceBoolMemoryAt (bindingInput 3) 0 hp left .dyn := by
    unfold SourceBoolMemoryAt
    rw [left_values]
    rfl
  have hit : copyHeap.1.index copyHeap.2 .dyn (indexValue (wmod 2))=some true := by
    change (MObj.elems .dyn (copyHeap.1.get copyHeap.2))[2]?=some true
    rw [contents]
    rfl
  have oldHit : copyHeap.1.index (left.wk copyExt) .dyn (indexValue (wmod 2))=some false := by
    change (MObj.elems .dyn (copyHeap.1.get (left.wk copyExt)))[2]?=some false
    rw [keep left,MObj.elems_wk,left_values]
    rfl
  have initialHit : hp.index left .dyn (indexValue (wmod 2))=some false := by
    change (MObj.elems .dyn (hp.get left))[2]?=some false
    rw [left_values]
    rfl
  have read := fresh.eval_local_read (G p) copyFrame fuel bindingDst bindingIndex _ true dst index hit
  refine ⟨read,old.eval_local_read (G p) copyFrame fuel .here bindingIndex _ false ret index oldHit,
    initial.eval_local_read (G p) copyFrame fuel bindingDst bindingIndex _ false rfl rfl initialHit,
    old.eval_local_read (y := bindingMid 3 [true,false,true]) (G p) copyFrame fuel bindingDst bindingIndex _ false rfl rfl oldHit,?_⟩
  have nextRead := fresh.eval_local_read (G p) copyFrame (fuel+1) bindingDst bindingIndex _ true dst index hit
  have nextStatement := source_expr_statement_run (G p) copyFrame (fuel+3) nps _ _ _ _ nextRead
  have first := (source_copy_binding_client p (fuel+1) nps).2.2.1
  exact source_items_pair_run (G p) copyFrame fuel nps _ _ _ _ _ first nextStatement

/-- Decoder failure does not replace the old local or allocate. Low horizons
also retain the actual whole input; no invented rollback is asserted. -/
theorem source_copy_binding_failures (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G p) badCopyFrame (fuel+3) (sourceBoolCalldataBind bindingDst bindingSrc)).run (bindingInput 3)=
      (.error (.revert []),bindingInput 3) ∧
    (Source.execS (G p) badCopyFrame (fuel+4) nps none
      (.expr (sourceBoolCalldataBind bindingDst bindingSrc) : Source.RStmt E [] false .body BindingCtx BindingCtx)
      (bindingInput 3).1).run (.nil,(bindingInput 3).2)=(.error (.revert []),(.nil,(bindingInput 3).2)) ∧
    (∀ n,n≤2 → (Source.evalE (G p) copyFrame n (sourceBoolCalldataBind bindingDst bindingSrc)).run (bindingInput 3)=
      (.error .timeout,bindingInput 3)) := by
  have run := source_cd_bool_bind_run (G p) badCopyFrame fuel (bindingInput 3) bindingDst bindingSrc 0 3 rfl
  have bad : sourceCalldataBoolValues E badCopyFrame 0 3=.error (.revert []) := rfl
  rw [bad] at run
  exact ⟨run,source_expr_statement_error (G p) badCopyFrame (fuel+3) nps _ _ _ (.revert []) run,
    source_cd_bool_bind_low (G p) copyFrame (bindingInput 3) bindingDst bindingSrc⟩

/-- A genuine successful EMPTY copy/bind prefix precedes a second-statement
bounds panic. Its allocated Source heap is retained, not transaction rollback.
Reversing the statements instead succeeds by reading the old nonempty alias. -/
theorem source_copy_binding_empty_late (p : Roadmap.Pipeline) (fuel nps : Nat) :
    (Source.evalE (G p) copyFrame (fuel+3) (sourceBoolCalldataBind bindingDst bindingSrc)).run (bindingInput 0)=
      (.ok (.val (.memRef rfl 3)),bindingOutput 0 []) ∧
    SourceBoolMemoryAt (bindingOutput 0 []) 3 (zeroCopyHeap 0 (by decide)).1 (zeroCopyHeap 0 (by decide)).2 .dyn ∧
    (Source.evalE (G p) copyFrame (fuel+2) (bindingRead bindingDst)).run (bindingOutput 0 [])=
      (.error (.revert (Source.panicData .index)),bindingOutput 0 []) ∧
    (Source.execItems (G p) copyFrame (fuel+6) nps none
      (.stmt (.expr (sourceBoolCalldataBind bindingDst bindingSrc)) (.stmt (.expr (bindingRead bindingDst)) .nil) :
        Source.RItems E [] false .body BindingCtx BindingCtx) (bindingInput 0).1).run (.nil,(bindingInput 0).2)=
          (.error (.revert (Source.panicData .index)),(.nil,(bindingOutput 0 []).2)) ∧
    (Source.execItems (G p) copyFrame (fuel+7) nps none
      (.stmt (.expr (bindingRead bindingDst)) (.stmt (.expr (sourceBoolCalldataBind bindingDst bindingSrc)) .nil) :
        Source.RItems E [] false .body BindingCtx BindingCtx) (bindingInput 0).1).run (.nil,(bindingInput 0).2)=
          (.ok (.normal (bindingOutput 0 []).1),(.nil,(bindingOutput 0 []).2)) ∧
    (bindingOutput 0 []).2.heap.get 3=some ⟨SB,sourceBoolMemory []⟩ := by
  have decoded : sourceCalldataBoolValues E copyFrame 0 0=.ok [] := rfl
  have result := (binding_at 0).bind_cd_bool_copy (G p) copyFrame fuel nps bindingDst bindingSrc 0 0 rfl
    (by decide) SH (binding_memOK 0)
  rw [decoded] at result
  obtain ⟨_,run,statement,_,_,_,fresh,_,dst,other,_⟩ := result
  change SourceBoolMemoryAt (bindingOutput 0 []) 3 (zeroCopyHeap 0 (by decide)).1 (zeroCopyHeap 0 (by decide)).2 .dyn at fresh
  obtain ⟨_,_,_,_,length,_⟩ := source_calldata_copy_zero_pair 0 (by decide)
  have bound : (zeroCopyHeap 0 (by decide)).1.len (zeroCopyHeap 0 (by decide)).2 .dyn≤(indexValue (wmod 2)).1.toNat := by
    rw [length]
    decide
  have index := other (.int .u256) bindingIndex (by decide)
  have miss := fresh.eval_local_bounds (G p) copyFrame fuel bindingDst bindingIndex _ dst index bound
  have nextMiss := fresh.eval_local_bounds (G p) copyFrame (fuel+1) bindingDst bindingIndex _ dst index bound
  have late := source_expr_statement_error (G p) copyFrame (fuel+3) nps _ _ _ (.revert (Source.panicData .index)) nextMiss
  have first := (binding_at 0).bind_cd_bool_copy (G p) copyFrame (fuel+1) nps bindingDst bindingSrc 0 0 rfl
    (by decide) SH (binding_memOK 0)
  rw [decoded] at first
  obtain ⟨_,_,firstStatement,_⟩ := first
  have old : SourceBoolMemoryAt (bindingInput 0) 0 hp left .dyn := by
    unfold SourceBoolMemoryAt
    rw [left_values]
    rfl
  have oldHit : hp.index left .dyn (indexValue (wmod 2))=some false := by
    change (MObj.elems .dyn (hp.get left))[2]?=some false
    rw [left_values]
    rfl
  have before := old.eval_local_read (G p) copyFrame (fuel+3) bindingDst bindingIndex _ false rfl rfl oldHit
  have beforeStatement := source_expr_statement_run (G p) copyFrame (fuel+5) nps _ _ _ _ before
  exact ⟨run,fresh,miss,source_items_pair_error (G p) copyFrame fuel nps _ _ _ _ _ _ firstStatement late,
    source_items_pair_run (G p) copyFrame (fuel+1) nps _ _ _ _ _ beforeStatement firstStatement,rfl⟩

/-- Whole initial/mid local and heap tables make the allocating prefix
observable independently of the later local binding and late bounds error. -/
theorem source_copy_binding_prefix_tables :
    (bindingInput 3).1=
      .cons (.memRef rfl 0) (.cons (.cdRef rfl 0 3) (.cons (.bool true)
        (.cons (sourceUint (indexValue (wmod 2))) (.cons (.memRef rfl 2)
          (.cons (.memRef rfl 1) (.cons (.memRef rfl 0) (.cons (.memRef rfl 2) .nil))))))) ∧
    (bindingMid 3 [true,false,true]).1=(bindingInput 3).1 ∧
    [(bindingInput 3).2.heap.get 0,(bindingInput 3).2.heap.get 1,
      (bindingInput 3).2.heap.get 2,(bindingInput 3).2.heap.get 3]=
      [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 0⟩,none] ∧
    [(bindingMid 3 [true,false,true]).2.heap.get 0,(bindingMid 3 [true,false,true]).2.heap.get 1,
      (bindingMid 3 [true,false,true]).2.heap.get 2,(bindingMid 3 [true,false,true]).2.heap.get 3]=
      [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,
       some ⟨SS,data 0⟩,some ⟨SB,sourceBoolMemory [true,false,true]⟩] ∧
    (bindingMid 3 [true,false,true]).2=(bindingOutput 3 [true,false,true]).2 ∧
    [(bindingOutput 0 []).2.heap.get 0,(bindingOutput 0 []).2.heap.get 1,
      (bindingOutput 0 []).2.heap.get 2,(bindingOutput 0 []).2.heap.get 3]=
      [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,
       some ⟨SS,data 0⟩,some ⟨SB,sourceBoolMemory []⟩] := by
  first | simp only [] | decide | omega | rfl | exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_copy_binding_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_copy_binding_client
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_copy_binding_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_copy_binding_vectors
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_copy_binding_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_copy_binding_reads
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_copy_binding_failures' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_copy_binding_failures

/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_copy_binding_empty_late' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_copy_binding_empty_late
/-- info: 'Solidity.Backend.MemoryOps.Physical.StructChildControls.source_copy_binding_prefix_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms source_copy_binding_prefix_tables
end Solidity.Backend.MemoryOps.Physical.StructChildControls
