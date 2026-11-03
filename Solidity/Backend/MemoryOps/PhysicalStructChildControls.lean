import Solidity.Backend.MemoryOps.PhysicalStructChild
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

end Solidity.Backend.MemoryOps.Physical.StructChildControls
