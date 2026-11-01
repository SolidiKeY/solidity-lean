import Solidity.Backend.MemoryOps.SourceStructDeclaration
import Solidity.Backend.MemoryOps.SourceStructGrowth
import Solidity.Backend.MemoryOps.SourceStructRedirect
import Solidity.Backend.MemoryOps.SourceStructSequence
import Solidity.Backend.MemoryOps.SourceStructDelete
import Solidity.Backend.MemoryOps.SourceStructChild
import Solidity.Backend.MemoryOps.SourceStructAlias
import Solidity.Backend.MemoryOps.SourceStructAssignment
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

/-! Populated, independently constructed Source/intrinsic/word struct controls.
Existing objects only. No constructor/compiler or physical-byte claim. -/
namespace Solidity.Backend.MemoryOps.SourceStructControls
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
    all_goals exact .inl (by simp only [Heap.len,Heap.get,Objs.get,hp,left,right,MObj.elems_dyn];decide)
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

/-- Independently inhabited actual declared layout, typed struct and two
materially different existing child tables, with shared parent aliases. -/
theorem initial_views (p : Roadmap.Pipeline) :
    Source.MemOK E SH sy ∧ SourceBoolStructAt sy 2 hp parent addresses layout ∧
    StateRepr 1 1 8 (Frag.init Γ) σ base machine ∧
    (Source.evalE (G p) F0 2 (.member (.local (.here : Source.Idx SΓ SS)) 0 layout.source_tag_type)).run sy=
      (.ok (.val (sourceUint u7)),sy) ∧
    (Source.evalE (G p) F0 2 (.member (.local (.here : Source.Idx SΓ SS)) 1 layout.source_child_type)).run sy=
      (.ok (.val (.memRef rfl 0)),sy) ∧
    [MObj.elems .dyn (hp.get left),MObj.elems .dyn (hp.get right)]=[[true,false,false],[false,true,false]] := by
  refine ⟨source_memOK,initial_at,initial_repr,initial_at.eval_member_tag (G p) F0 0 .here rfl,
    initial_at.eval_member_child (G p) F0 0 .here rfl,?_⟩
  simp only [Heap.get,Objs.get,hp,left,right,MObj.elems_dyn]

private def sroot : Source.Idx SΓ SS := .here
private def srhs : Source.Idx SΓ SB := .there .here
private def sself : Source.Idx SΓ SS := .there (.there (.there .here))
private def root : Idx Γ (.mem (.struct S)) := .here
private def rhs : Idx Γ (.mem B) := .there .here
private def oldAlias : Idx Γ (.mem B) := .there (.there .here)
private def self : Idx Γ (.mem (.struct S)) := .there (.there (.there .here))
private def out := hp.setField parent layout.child_type right
private def reached : Source.EMState E SΓ := (sy.1,{sy.2 with heap := sy.2.heap.write 2 (data 1) (by rfl)})
private def target := writeMachine machine 33 w[24]
private def term : Source.RExpr E SΓ SB := sourceStructAssign layout sroot srhs
private def code : List Instr := structReferenceWriteCode 1 root rhs "items"
private def cells (m : Machine) :=
  [m.mem 0,m.mem 1,m.mem 2,m.mem 3,m.mem 4,m.mem 7,m.mem 16,m.mem 17,m.mem 18,m.mem 19,
    m.mem 24,m.mem 25,m.mem 26,m.mem 27,m.mem 32,m.mem 33]
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

/-- Actual RHS-first Source member assignment and the independent intrinsic/
word pointer replacement. Both parent aliases observe the new child; old child
contents, tag, locals, allocator and all other cells stay unchanged. -/
theorem redirected_views (p : Roadmap.Pipeline) :
    (Source.evalE (G p) F0 3 term).run sy=(.ok (.val (.memRef rfl 1)),reached) ∧
    (Source.execS (G p) F0 4 SΓ.length none (.expr term : Source.RStmt E [] false .body SΓ SΓ) sy.1).run (.nil,sy.2)=
      (.ok (.normal sy.1),(.nil,reached.2)) ∧
    Stmt.run σ (.assignMem (.field (.var root (by decide)) "items" layout.child_type) (.ref (.var rhs rfl)))=
      .ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧ run code machine=.ok target 0 ∧
    SourceBoolStructAt reached 2 out parent addresses layout ∧ Source.MemOK E SH reached ∧
    StateRepr 1 1 8 (Frag.init Γ) (σ.withHeap out) base target ∧
    (Source.evalE (G p) F0 2 (.member (.local sroot) 1 layout.source_child_type)).run reached=
      (.ok (.val (.memRef rfl 1)),reached) ∧
    (Source.evalE (G p) F0 2 (.member (.local sself) 1 layout.source_child_type)).run reached=
      (.ok (.val (.memRef rfl 1)),reached) ∧
    (Source.evalE (G p) F0 2 (.member (.local sroot) 0 layout.source_tag_type)).run reached=
      (.ok (.val (sourceUint u7)),reached) ∧
    (Source.readLoc (E := E) (Γ := SΓ) F0 (τ := .bool) (.mem 0 0)).run reached=(.ok (.bool true),reached) ∧
    (Source.readLoc (E := E) (Γ := SΓ) F0 (τ := .bool) (.mem 1 0)).run reached=(.ok (.bool false),reached) ∧
    [hp.field parent layout.child_type |>.id,out.field parent layout.child_type |>.id]=[0,1] ∧
    [hp.field parent layout.tag_type,out.field parent layout.tag_type]=[u7,u7] ∧
    [MObj.elems .dyn (hp.get left),MObj.elems .dyn (hp.get right),MObj.elems .dyn (out.get left),MObj.elems .dyn (out.get right)]=
      [[true,false,false],[false,true,false],[true,false,false],[false,true,false]] ∧
    [sy.2.heap.get 0,sy.2.heap.get 1,sy.2.heap.get 2,reached.2.heap.get 0,reached.2.heap.get 1,reached.2.heap.get 2]=
      [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 0⟩,
       some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 1⟩] ∧
    [cells machine,cells target]=
      [[w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[16]],
       [w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[24]]] ∧
    [(TEnv.get oldAlias σ.env).map HRef.id,(TEnv.get oldAlias (σ.withHeap out).env).map HRef.id,
      (TEnv.get root (σ.withHeap out).env).map HRef.id,(TEnv.get self (σ.withHeap out).env).map HRef.id]=[some 0,some 0,some 2,some 2] ∧
    reached.1=sy.1 ∧ reached.2.ex=sy.2.ex ∧ reached.2.events=sy.2.events ∧ reached.2.logs=sy.2.logs ∧
    target.stack=[w[42]] ∧ StructAllocatorRepr out base 8 ⟨48,by decide⟩ target := by
  obtain ⟨z,m',hw,he,hs,hi,hc,hr,hm,hrepr,hl,hstack,ht,halloc,htag,hchild,hchildren,hsource,heffects⟩ :=
    SourceBoolStructAt.resolved_assign_word layout (G p) F0 0 σ parent right addresses initial_at right_at
      sroot srhs root rhs rfl rfl rfl rfl (by decide) SH source_memOK initial_repr
  have hknown : (Source.writeLoc (E := E) (Γ := SΓ) F0 2 (.mem (τ := SB) 2 1) (.memRef rfl 1)).run sy=(.ok (),reached) := by
    obtain ⟨ht,hw⟩ := source_struct_write sy 2 dn layout.source_types u7 0 1 initial_at.parent
    exact hw
  have hz : z=reached := congrArg Prod.snd (hw.symm.trans hknown)
  subst z
  change m'=target at ht
  subst m'
  have hold := hsource left left_at
  have hnew := hsource right right_at
  have hread := hr.eval_member_child (G p) F0 0 sroot rfl
  have hself := hr.eval_member_child (G p) F0 0 sself rfl
  have htagread := hr.eval_member_tag (G p) F0 0 sroot rfl
  rw [hchild] at hread hself
  rw [htag] at htagread
  change out.field parent layout.child_type=right at hchild
  change out.field parent layout.tag_type=hp.field parent layout.tag_type at htag
  have hleft : out.get left=hp.get left := hchildren left
  have hright : out.get right=hp.get right := hchildren right
  refine ⟨he,hs,hi,hc,hr,hm,hrepr,hread,hself,htagread,?_,?_,?_,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hstack,halloc _ (by decide) initial_allocator⟩
  · exact hold.read_iff F0 (indexValue ⟨0,by decide⟩) true |>.mpr (by simp only [out,Heap.index,Heap.setField,Heap.get_set_ne hp parent left (by decide),Heap.get,Objs.get,hp,left,MObj.elems_dyn,indexValue,Int.toNat_natCast];rfl)
  · exact hnew.read_iff F0 (indexValue ⟨0,by decide⟩) false |>.mpr (by simp only [out,Heap.index,Heap.setField,Heap.get_set_ne hp parent right (by decide),Heap.get,Objs.get,hp,right,MObj.elems_dyn,indexValue,Int.toNat_natCast];rfl)
  · rw [hchild];rfl
  · rw [htag];rfl
  · rw [hleft,hright]
    simp only [Heap.get,Objs.get,hp,left,right,MObj.elems_dyn]

/-- Incorrect source declaration positions/names or intrinsic field types
cannot be used as typed member evidence. Raw wrong-type/missing reads are stuck,
not a fabricated index panic or target revert. -/
theorem layout_and_failure_views (p : Roadmap.Pipeline) :
    E.fieldAt dn .memory "tag"=some (0,.int .u256) ∧ E.fieldAt dn .memory "items"=some (1,SB) ∧
    E.fieldAt dn .memory "absent"=none ∧
    ¬SourceBoolStructLayout E dn S "items" "tag" ∧ E.fieldTy? dn .memory 0≠some SB ∧
    lookupBy "tag" (structDef S)≠some (.ref B) ∧
    (Source.readLoc (E := E) (Γ := SΓ) F0 (τ := SB) (.mem 2 0)).run sy=
      (.error (.stuck "field type"),sy) ∧
    (Source.readLoc (E := E) (Γ := SΓ) F0 (τ := SB) (.mem 2 2)).run sy=
      (.error (.stuck "no field"),sy) ∧
    (∀ n,n≤2 → (Source.evalE (G p) F0 n term).run sy=(.error .timeout,sy)) ∧
    out.field parent layout.child_type≠hp.field parent layout.child_type ∧
    target.mem 33≠machine.mem 33 ∧ target.mem 32=machine.mem 32 ∧ target.mem 17=machine.mem 17 ∧
    out.index right .dyn (indexValue ⟨0,by decide⟩)≠out.index left .dyn (indexValue ⟨0,by decide⟩) := by
  refine ⟨rfl,rfl,rfl,?_,by decide,by decide,rfl,rfl,source_struct_assign_low_horizon layout (G p) F0 sy sroot srhs,?_,?_,rfl,rfl,?_⟩
  · intro hbad
    have hn : E.structFields dn .memory≠some [("items",.int .u256),("tag",SB)] := by decide
    exact hn hbad.source_fields
  · intro he
    have hids := congrArg HRef.id he
    change 1=0 at hids;cases hids
  · change w[24]≠w[16];decide
  · simp only [out,Heap.index,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,left,right,parent,MObj.elems_dyn,indexValue,Int.toNat_natCast]
    change (some false : Option Bool)≠some true;decide


private def pointerCode (x : Idx Γ (.mem (.struct S))) : List Instr :=
  [.mload (cellOf 1 x)] ++ readFieldCode (fieldOffset (structDef S) "items")
private def fieldPath (x : Idx Γ (.mem (.struct S))) : MPath C Γ (.ref B) :=
  .loc (.field (.var x (by decide)) "items" layout.child_type)

/-- Actual published typed word member reads follow the same old/new child
as Source members, including the retained self alias of the parent. -/
theorem field_pointer_reads (p : Roadmap.Pipeline) :
    run (pointerCode root) machine=.ok (machine.push w[16]) 0 ∧
    run (pointerCode root) target=.ok (target.push w[24]) 0 ∧
    run (pointerCode self) target=.ok (target.push w[24]) 0 ∧
    machine.mem 2=target.mem 2 ∧ machine.mem 1=target.mem 1 ∧ machine.mem 4=target.mem 4 := by
  obtain ⟨_,_,_,_,hr,hm,hrepr,tail⟩ := redirected_views p
  have croot : PtrFrag 1 (fieldPath root) (pointerCode root) :=
    .field (.var root (by decide)) layout.child_type _ (.local root (by decide))
  have cself : PtrFrag 1 (fieldPath self) (pointerCode self) :=
    .field (.var self (by decide)) layout.child_type _ (.local self (by decide))
  have hp₀ : (fieldPath root).mvalT σ=.ok left := by
    simp only [fieldPath,MPath.mvalT,MLoc.addrT,
      show TEnv.get root σ.env=some parent from rfl,Heap.readAddr,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    rfl
  have hfield : out.field parent layout.child_type=right := by
    simp only [out,Heap.field,Heap.setField,Heap.get_set_same,MFields.get_set_same]
  have hp₁ : (fieldPath root).mvalT (σ.withHeap out)=.ok right := by
    simp only [fieldPath,MPath.mvalT,MLoc.addrT,
      show TEnv.get root (σ.withHeap out).env=some parent from rfl,Heap.readAddr,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    change Except.ok (out.field parent layout.child_type)=Except.ok right
    rw [hfield]
  have hp₂ : (fieldPath self).mvalT (σ.withHeap out)=.ok right := by
    simp only [fieldPath,MPath.mvalT,MLoc.addrT,
      show TEnv.get self (σ.withHeap out).env=some parent from rfl,Heap.readAddr,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    change Except.ok (out.field parent layout.child_type)=Except.ok right
    rw [hfield]
  exact ⟨croot.run_of_eval initial_repr hp₀,croot.run_of_eval hrepr hp₁,cself.run_of_eval hrepr hp₂,rfl,rfl,rfl⟩

private def out2 := out.setField parent layout.child_type right
private def repeated : Source.EMState E SΓ := (reached.1,{reached.2 with heap := reached.2.heap.write 2 (data 1) (by rfl)})
private def target2 := writeMachine target 33 w[24]
private def termSelf : Source.RExpr E SΓ SB := sourceStructAssign layout sself srhs
private def codeSelf : List Instr := structReferenceWriteCode 1 self rhs "items"

/-- Executed second assignment THROUGH the retained parent alias. It stores
the already current pointer, so tag/children/identities and complete word vectors
stay unchanged. Source writes its existing object again; no fresh child appears. -/
theorem repeated_self_assignment (p : Roadmap.Pipeline) :
    (Source.evalE (G p) F0 3 termSelf).run reached=(.ok (.val (.memRef rfl 1)),repeated) ∧
    (Source.execS (G p) F0 4 SΓ.length none (.expr termSelf : Source.RStmt E [] false .body SΓ SΓ) reached.1).run (.nil,reached.2)=
      (.ok (.normal reached.1),(.nil,repeated.2)) ∧
    Stmt.run (σ.withHeap out) (.assignMem (.field (.var self (by decide)) "items" layout.child_type) (.ref (.var rhs rfl)))=
      .ok ⟨σ.withHeap out2,List.prefix_refl _⟩ ∧ run codeSelf target=.ok target2 0 ∧
    run (code++codeSelf) machine=.ok target2 0 ∧
    SourceBoolStructAt repeated 2 out2 parent addresses layout ∧ Source.MemOK E SH repeated ∧
    StateRepr 1 1 8 (Frag.init Γ) (σ.withHeap out2) base target2 ∧
    [(hp.field parent layout.child_type).id,(out.field parent layout.child_type).id,(out2.field parent layout.child_type).id]=[0,1,1] ∧
    [sy.2.heap.next,reached.2.heap.next,repeated.2.heap.next]=[3,3,3] ∧
    [MObj.elems .dyn (hp.get left),MObj.elems .dyn (hp.get right),MObj.elems .dyn (out.get left),MObj.elems .dyn (out.get right),
      MObj.elems .dyn (out2.get left),MObj.elems .dyn (out2.get right)]=
      [[true,false,false],[false,true,false],[true,false,false],[false,true,false],[true,false,false],[false,true,false]] ∧
    [sy.2.heap.get 2,reached.2.heap.get 2,repeated.2.heap.get 2]=[some ⟨SS,data 0⟩,some ⟨SS,data 1⟩,some ⟨SS,data 1⟩] ∧
    [cells machine,cells target,cells target2]=
      [[w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[16]],
       [w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[24]],
       [w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[24]]] ∧
    repeated.1=sy.1 ∧ repeated.2.ex=sy.2.ex ∧ target2.stack=[w[42]] ∧
    StructAllocatorRepr out2 base 8 ⟨48,by decide⟩ target2 := by
  obtain ⟨_,_,_,hc₀,hr,hm,hrepr,tail⟩ := redirected_views p
  have hfield : out.field parent layout.child_type=right := by
    simp only [out,Heap.field,Heap.setField,Heap.get_set_same,MFields.get_set_same]
  have hv : SourceBoolMemoryAt reached 1 out right .dyn := by simpa only [hfield] using hr.leaf
  obtain ⟨z,m',hw,he,hs,hi,hc,hr',hm',hrepr',hl,hstack,ht,halloc,htag,hchild,hchildren,hsource,heffects⟩ :=
    SourceBoolStructAt.resolved_assign_word layout (G p) F0 0 (σ.withHeap out) parent right addresses hr hv
      sself srhs self rhs rfl rfl rfl rfl (by decide) SH hm hrepr
  have hknown : (Source.writeLoc (E := E) (Γ := SΓ) F0 2 (.mem (τ := SB) 2 1) (.memRef rfl 1)).run reached=(.ok (),repeated) := by
    obtain ⟨ht,hw⟩ := source_struct_write reached 2 dn layout.source_types u7 1 1 (by rfl)
    exact hw
  have hz : z=repeated := congrArg Prod.snd (hw.symm.trans hknown)
  subst z
  change m'=target2 at ht
  subst m'
  have hleft : out2.get left=out.get left := hchildren left
  have hright : out2.get right=out.get right := hchildren right
  refine ⟨he,hs,hi,hc,run_append_ok hc₀ |>.trans hc,hr',hm',hrepr',?_,rfl,?_,rfl,rfl,rfl,rfl,hstack,
    halloc _ (by decide) (initial_allocator.setReference parent layout.child_type right)⟩
  · change out2.field parent layout.child_type=right at hchild
    rw [hfield,hchild];rfl
  · rw [hleft,hright]
    simp only [out,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,parent,left,right,MObj.elems_dyn]


private def runtimeHp (xs ys : List Bool) (hx : xs.length<2^256) (hy : ys.length<2^256) : Heap H :=
  (⟨xs,hx⟩,(⟨ys,hy⟩,((u7,(left,())),())))
private def runtimeYL (xs : List Bool) : Source.EMState E [] := ((Source.allocRef (sourceBoolMemory xs)).run y0).2
private def runtimeYR (xs ys : List Bool) : Source.EMState E [] := ((Source.allocRef (sourceBoolMemory ys)).run (runtimeYL xs)).2
private def runtimeYP (xs ys : List Bool) : Source.EMState E [] := ((Source.allocRef (data 0)).run (runtimeYR xs ys)).2
private def runtimeSource (xs ys : List Bool) : Source.EMState E SΓ := (sy.1,(runtimeYP xs ys).2)
private theorem runtime_memOK (xs ys : List Bool) : Source.MemOK E SH (runtimeSource xs ys) := by
  have h0 : Source.MemOK E SH y0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have hl := source_bool_alloc_memOK (E := E) (Γ := []) SH xs y0 h0
  rw [show (Source.allocRef (E := E) (Γ := []) (sourceBoolMemory xs)).run y0=(.ok (.memRef rfl 0),runtimeYL xs) from rfl] at hl
  have hr := source_bool_alloc_memOK (E := E) (Γ := []) SH ys (runtimeYL xs) hl.1
  rw [show (Source.allocRef (E := E) (Γ := []) (sourceBoolMemory ys)).run (runtimeYL xs)=(.ok (.memRef rfl 1),runtimeYR xs ys) from rfl] at hr
  have hd : Source.DataOK E (runtimeYR xs ys).2.heap.ty (data 0) := by
    change Source.DataOK E (runtimeYR xs ys).2.heap.ty (Source.Data.struct (D := E.layout) (l := .memory) (d := dn)
      (.cons (.val (sourceUint u7)) (.cons (.val (.memRef (τ := SB) rfl 0)) .nil)))
    exact .struct (.cons (.val (Source.Val.refOK_of_loc (τ := .int .u256) rfl _)) (.cons (.val ⟨SB,rfl,rfl⟩) .nil))
  have hi : Source.Data.Inner (E := E) (data 0) := by
    change (∃ v,Source.Data.val (sourceUint (D := E.layout) u7)=.val v) ∧
      (∃ v,Source.Data.val (Source.Val.memRef (D := E.layout) (τ := SB) rfl 0)=.val v) ∧ True
    exact ⟨⟨_,rfl⟩,⟨_,rfl⟩,trivial⟩
  have ha := Source.allocRef_mem' (E := E) (Γ := []) (H := SH) (data 0) (by trivial) hi (runtimeYR xs ys) ⟨hr.1,hd⟩
  rw [show (Source.allocRef (E := E) (Γ := []) (data 0)).run (runtimeYR xs ys)=(.ok (.memRef rfl 2),runtimeYP xs ys) from rfl] at ha
  exact ⟨⟨ha.1.1.1,⟨⟨SS,rfl,rfl⟩,⟨⟨SB,rfl,rfl⟩,⟨⟨SB,rfl,rfl⟩,⟨⟨SS,rfl,rfl⟩,trivial⟩⟩⟩⟩⟩,ha.1.2⟩

/-- Actual logical Source/intrinsic transfer for arbitrary runtime children,
including empty and element32 cases. Full word transport separately retains its
real ownership/space premise; no fixed-size word layout is asserted for all xs. -/
theorem runtime_children (xs ys : List Bool) (hx : xs.length<2^256) (hy : ys.length<2^256) :
    ∃ z : Source.EMState E SΓ,
      (Source.writeLoc (E := E) (Γ := SΓ) F0 0 (.mem (τ := SB) 2 1) (.memRef rfl 1)).run
        (runtimeSource xs ys)=(.ok (),z) ∧
      SourceBoolStructAt z 2 ((runtimeHp xs ys hx hy).setField parent layout.child_type right) parent addresses layout ∧
      Source.MemOK E SH z ∧
      (∀ i : Fin xs.length,(Source.readLoc (E := E) (Γ := SΓ) F0 (τ := .bool) (.mem 0 i.val)).run z=(.ok (.bool xs[i.val]),z)) ∧
      (∀ i : Fin ys.length,(Source.readLoc (E := E) (Γ := SΓ) F0 (τ := .bool) (.mem 1 i.val)).run z=(.ok (.bool ys[i.val]),z)) := by
  let hp := runtimeHp xs ys hx hy
  let y := runtimeSource xs ys
  have hleft : SourceBoolMemoryAt y 0 hp left .dyn := by
    unfold SourceBoolMemoryAt;simp only [hp,runtimeHp,Heap.get,Objs.get,left,MObj.elems_dyn];rfl
  have hright : SourceBoolMemoryAt y 1 hp right .dyn := by
    unfold SourceBoolMemoryAt;simp only [hp,runtimeHp,Heap.get,Objs.get,right,MObj.elems_dyn];rfl
  have hr : SourceBoolStructAt y 2 hp parent addresses layout := ⟨by rfl,hleft⟩
  obtain ⟨z,hw,hr',hm,hl,htag,hchild,hchildren,hsource,heffects⟩ := hr.write_reference right hright F0 0 SH (runtime_memOK xs ys)
  have hleft' := hsource left hleft
  have hright' := hsource right hright
  refine ⟨z,hw,hr',hm,?_,?_⟩
  · intro i
    have hiw : i.val<W := by have h := i.isLt;change i.val<2^256;omega
    have hread := (hleft'.read_iff F0 (indexValue ⟨i.val,hiw⟩) xs[i.val]).mpr ?_
    · simpa only [indexValue,Int.toNat_natCast] using hread
    · change (MObj.elems .dyn ((hp.setField parent layout.child_type right).get left))[i.val]?=some xs[i.val]
      rw [hchildren left]
      simpa only [hp,runtimeHp,Heap.get,Objs.get,left,MObj.elems_dyn] using
        (List.getElem?_eq_some_iff.mpr ⟨i.isLt,rfl⟩ : xs[i.val]?=some xs[i.val])
  · intro i
    have hiw : i.val<W := by have h := i.isLt;change i.val<2^256;omega
    have hread := (hright'.read_iff F0 (indexValue ⟨i.val,hiw⟩) ys[i.val]).mpr ?_
    · simpa only [indexValue,Int.toNat_natCast] using hread
    · change (MObj.elems .dyn ((hp.setField parent layout.child_type right).get right))[i.val]?=some ys[i.val]
      rw [hchildren right]
      simpa only [hp,runtimeHp,Heap.get,Objs.get,right,MObj.elems_dyn] using
        (List.getElem?_eq_some_iff.mpr ⟨i.isLt,rfl⟩ : ys[i.val]?=some ys[i.val])

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.initial_views' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms initial_views

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.redirected_views' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms redirected_views

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.layout_and_failure_views' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms layout_and_failure_views

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.field_pointer_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms field_pointer_reads

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.repeated_self_assignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms repeated_self_assignment

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.runtime_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms runtime_children


private def aliasInitial : Source.EMState E SΓ := (sy.1.set srhs (.memRef rfl 0),sy.2)
private def aliasInitialState := σ.setLocal rhs (some left)
private def aliasInitialMachine := writeMachine machine 3 w[16]
private def initialSelect : Source.RExpr E SΓ SB := sourceStructSelectedAlias layout srhs sroot
private def initialSelectCode : List Instr := structSelectedAliasCode 1 rhs root "items"
private def soldAlias : Source.Idx SΓ SB := .there (.there .here)
private def aliasReached : Source.EMState E SΓ := (reached.1.set soldAlias (.memRef rfl 1),reached.2)
private def aliasReachedState := (σ.withHeap out).setLocal oldAlias (some right)
private def aliasReachedMachine := writeMachine target 2 w[24]
private def reachedSelect : Source.RExpr E SΓ SB := sourceStructSelectedAlias layout soldAlias sroot
private def reachedSelectCode : List Instr := structSelectedAliasCode 1 oldAlias root "items"

/-- The initial member selects LEFT despite the destination local initially
holding RIGHT. Both heaps stay unchanged and the new alias reads actual TFF. -/
theorem initial_member_alias (p : Roadmap.Pipeline) :
    (Source.evalE (G p) F0 3 initialSelect).run sy=(.ok (.val (.memRef rfl 0)),aliasInitial) ∧
    (Source.execS (G p) F0 4 SΓ.length none (.expr initialSelect : Source.RStmt E [] false .body SΓ SΓ) sy.1).run (.nil,sy.2)=
      (.ok (.normal aliasInitial.1),(.nil,sy.2)) ∧
    Stmt.run σ (.rebindMem rhs (.alias (fieldPath root)))=.ok ⟨aliasInitialState,List.prefix_refl _⟩ ∧
    run initialSelectCode machine=.ok aliasInitialMachine 0 ∧
    SourceBoolStructAt aliasInitial 2 hp parent addresses layout ∧ SourceBoolMemoryAt aliasInitial 0 hp left .dyn ∧
    Source.MemOK E SH aliasInitial ∧ StateRepr 1 1 8 (Frag.init Γ) aliasInitialState base aliasInitialMachine ∧
    [sy.1.get srhs,aliasInitial.1.get srhs]=[.memRef rfl 1,.memRef rfl 0] ∧
    [(TEnv.get rhs σ.env).map HRef.id,(TEnv.get rhs aliasInitialState.env).map HRef.id]=[some 1,some 0] ∧
    [cells machine,cells aliasInitialMachine]=
      [[w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[16]],
       [w[48],w[32],w[16],w[16],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[16]]] ∧
    (Source.readLoc (E := E) (Γ := SΓ) F0 (τ := .bool) (.mem 0 0)).run aliasInitial=(.ok (.bool true),aliasInitial) ∧
    aliasInitial.2.heap=sy.2.heap ∧ aliasInitialState.heap=hp ∧ aliasInitialMachine.stack=[w[42]] ∧
    StructAllocatorRepr hp base 8 ⟨48,by decide⟩ aliasInitialMachine := by
  obtain ⟨he,hs,hi,hc,hr,hchild,hm,hrepr,hsh,hth,hget,htget,hstack,halloc⟩ :=
    SourceBoolStructAt.selected_alias_word layout (G p) F0 0 σ parent addresses initial_at srhs sroot rhs root
      rfl rfl (by decide) SH source_memOK initial_repr
  refine ⟨he,hs,hi,hc,hr,hchild,hm,hrepr,rfl,rfl,rfl,?_,hsh,hth,hstack,halloc _ (by decide) initial_allocator⟩
  exact hchild.read_iff F0 (indexValue ⟨0,by decide⟩) true |>.mpr
    (by simp only [Heap.index,Heap.get,Objs.get,hp,left,MObj.elems_dyn,indexValue,Int.toNat_natCast];rfl)

private def memberAliasItems : Source.RItems E [] false .body SΓ SΓ :=
  .stmt (.expr term) (.stmt (.expr reachedSelect) .nil)
private def memberAliasProg : Prog C Γ Γ :=
  .cons (.assignMem (.field (.var root (by decide)) "items" layout.child_type) (.ref (.var rhs rfl)))
    (.cons (.rebindMem oldAlias (.alias (fieldPath root))) .nil)

/-- Actual field write THEN member-selected local alias, in Source RItems,
intrinsic Prog and appended word code. The second selection comes from the
reached parent (RIGHT), differing from the original parent (LEFT). -/
theorem reached_member_alias_program (p : Roadmap.Pipeline) :
    (Source.execItems (G p) F0 6 SΓ.length none memberAliasItems sy.1).run (.nil,sy.2)=
      (.ok (.normal aliasReached.1),(.nil,reached.2)) ∧
    Prog.run σ memberAliasProg=.ok ⟨aliasReachedState,List.prefix_refl _⟩ ∧
    run (code++reachedSelectCode) machine=.ok aliasReachedMachine 0 ∧
    (Source.evalE (G p) F0 3 reachedSelect).run reached=(.ok (.val (.memRef rfl 1)),aliasReached) ∧
    SourceBoolStructAt aliasReached 2 out parent addresses layout ∧ SourceBoolMemoryAt aliasReached 1 out right .dyn ∧
    Source.MemOK E SH aliasReached ∧ StateRepr 1 1 8 (Frag.init Γ) aliasReachedState base aliasReachedMachine ∧
    [sy.1.get soldAlias,reached.1.get soldAlias,aliasReached.1.get soldAlias]=[.memRef rfl 0,.memRef rfl 0,.memRef rfl 1] ∧
    [(TEnv.get oldAlias σ.env).map HRef.id,(TEnv.get oldAlias (σ.withHeap out).env).map HRef.id,
      (TEnv.get oldAlias aliasReachedState.env).map HRef.id]=[some 0,some 0,some 1] ∧
    [cells machine,cells target,cells aliasReachedMachine]=
      [[w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[16]],
       [w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[24]],
       [w[48],w[32],w[24],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[24]]] ∧
    [MObj.elems .dyn (hp.get left),MObj.elems .dyn (hp.get right),MObj.elems .dyn (out.get left),MObj.elems .dyn (out.get right),
      MObj.elems .dyn (aliasReachedState.heap.get left),MObj.elems .dyn (aliasReachedState.heap.get right)]=
      [[true,false,false],[false,true,false],[true,false,false],[false,true,false],[true,false,false],[false,true,false]] ∧
    (Source.readLoc (E := E) (Γ := SΓ) F0 (τ := .bool) (.mem 1 0)).run aliasReached=(.ok (.bool false),aliasReached) ∧
    (Source.readLoc (E := E) (Γ := SΓ) F0 (τ := .bool) (.mem 0 0)).run aliasReached=(.ok (.bool true),aliasReached) ∧
    aliasReached.2.heap=reached.2.heap ∧ aliasReachedState.heap=out ∧ aliasReached.2.ex=sy.2.ex ∧
    aliasReachedMachine.stack=[w[42]] ∧ StructAllocatorRepr out base 8 ⟨48,by decide⟩ aliasReachedMachine := by
  obtain ⟨z,m',hw,he₀,hs₀,hi₀,hc₀,hr,hm,hrepr,hl,hstack₀,ht,halloc₀,htag,hchild,hchildren,hsource,heffects⟩ :=
    SourceBoolStructAt.resolved_assign_word layout (G p) F0 1 σ parent right addresses initial_at right_at
      sroot srhs root rhs rfl rfl rfl rfl (by decide) SH source_memOK initial_repr
  have hknown : (Source.writeLoc (E := E) (Γ := SΓ) F0 3 (.mem (τ := SB) 2 1) (.memRef rfl 1)).run sy=(.ok (),reached) := by
    obtain ⟨ht,hw⟩ := source_struct_write sy 2 dn layout.source_types u7 0 1 initial_at.parent
    exact hw
  have hz : z=reached := congrArg Prod.snd (hw.symm.trans hknown)
  subst z
  change m'=target at ht
  subst m'
  obtain ⟨he,hs,hi,hc,hr',hselected,hm',hrepr',hsh,hth,hget,htget,hstack,halloc⟩ :=
    SourceBoolStructAt.selected_alias_word layout (G p) F0 0 (σ.withHeap out) parent addresses hr
      soldAlias sroot oldAlias root rfl rfl (by decide) SH hm hrepr
  change out.field parent layout.child_type=right at hchild
  have hqReached : (σ.withHeap out).heap.field parent layout.child_type=right := hchild
  simp only [hqReached] at he hs hi hc hr' hselected hm' hrepr' hsh hth hget htget hstack halloc
  have hitems := source_items_pair_run (G p) F0 0 SΓ.length _ _ sy reached aliasReached hs₀ hs
  have htail : Prog.run (σ.withHeap out) (.cons (.rebindMem oldAlias (.alias (fieldPath root))) .nil)=
      .ok ⟨aliasReachedState,List.prefix_refl _⟩ := by
    unfold fieldPath
    rw [Prog.run_cons_ok hi,Prog.run_nil]
    rfl
  have hprog : Prog.run σ memberAliasProg=.ok ⟨aliasReachedState,List.prefix_refl _⟩ := by
    rw [memberAliasProg,Prog.run_cons_ok hi₀]
    change Except.map _ (Prog.run (σ.withHeap out) (.cons (.rebindMem oldAlias (.alias (fieldPath root))) .nil))=_
    rw [htail]
    rfl
  have hold : SourceBoolMemoryAt aliasReached 0 out left .dyn := hsource left left_at
  have hleft : out.get left=hp.get left := hchildren left
  have hright : out.get right=hp.get right := hchildren right
  refine ⟨hitems,hprog,run_append_ok hc₀ |>.trans hc,he,hr',hselected,hm',hrepr',rfl,rfl,rfl,?_,?_,?_,rfl,rfl,rfl,rfl,
    halloc _ (by decide) (halloc₀ _ (by decide) initial_allocator)⟩
  · change [MObj.elems .dyn (hp.get left),MObj.elems .dyn (hp.get right),MObj.elems .dyn (out.get left),MObj.elems .dyn (out.get right),MObj.elems .dyn (out.get left),MObj.elems .dyn (out.get right)]=_
    rw [hleft,hright]
    simp only [Heap.get,Objs.get,hp,left,right,MObj.elems_dyn]
  · exact hselected.read_iff F0 (indexValue ⟨0,by decide⟩) false |>.mpr
      (by simp only [out,Heap.index,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,parent,right,MObj.elems_dyn,indexValue,Int.toNat_natCast];rfl)
  · exact hold.read_iff F0 (indexValue ⟨0,by decide⟩) true |>.mpr
      (by simp only [out,Heap.index,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,parent,left,MObj.elems_dyn,indexValue,Int.toNat_natCast];rfl)


/-- Distinguishing stale selected identity/content and low Source horizon.
Neither failure is silently equated with target reversion. -/
theorem member_alias_negative_views (p : Roadmap.Pipeline) :
    (∀ n,n≤2 → (Source.evalE (G p) F0 n reachedSelect).run reached=(.error .timeout,reached)) ∧
    aliasInitial.1.get srhs≠aliasReached.1.get soldAlias ∧
    aliasInitialMachine.mem 3≠aliasReachedMachine.mem 2 ∧
    out.index left .dyn (indexValue ⟨0,by decide⟩)≠out.index right .dyn (indexValue ⟨0,by decide⟩) := by
  refine ⟨source_struct_select_low_horizon layout (G p) F0 reached soldAlias sroot,?_,?_,?_⟩
  · intro h
    cases h
  · change w[16]≠w[24];decide
  · simp only [out,Heap.index,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,parent,left,right,MObj.elems_dyn,indexValue,Int.toNat_natCast]
    change (some true : Option Bool)≠some false;decide

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.initial_member_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms initial_member_alias

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.reached_member_alias_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reached_member_alias_program

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.member_alias_negative_views' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms member_alias_negative_views


private abbrev XΓ : Source.RCtx := [.int .u256,.bool]++SΓ
private def withArgs (y : Source.EMState E SΓ) (k : PrimTy.uint.Denote) (v : Bool) : Source.EMState E XΓ :=
  (.cons (sourceUint k) (.cons (.bool v) y.1),y.2)
private def xroot : Source.Idx XΓ SS := .there (.there sroot)
private def xi : Source.Idx XΓ (.int .u256) := .here
private def xv : Source.Idx XΓ .bool := .there .here
private def zeroWord : Val C Γ .uint := .simple (.lit 0 rfl)
private def trueWord : Val C Γ .bool := .simple (.bool true)
private def k0 : PrimTy.uint.Denote := indexValue ⟨0,by decide⟩
private theorem withArgs_memOK (y : Source.EMState E SΓ) (k : PrimTy.uint.Denote) (v : Bool)
    (hm : Source.MemOK E SH y) : Source.MemOK E SH (withArgs y k v) := by
  exact ⟨⟨hm.1.1,⟨trivial,⟨trivial,hm.1.2⟩⟩⟩,hm.2⟩

/-- Actual member-index reads before and after the actual reference assignment.
The same Source syntax and target code see materially different selected data. -/
theorem member_child_reads (p : Roadmap.Pipeline) :
    (Source.evalE (G p) F0 3 (sourceStructChildRead layout xroot xi)).run (withArgs sy k0 true)=
      (.ok (.val (.bool true)),withArgs sy k0 true) ∧
    (Source.evalE (G p) F0 3 (sourceStructChildRead layout xroot xi)).run (withArgs reached k0 true)=
      (.ok (.val (.bool false)),withArgs reached k0 true) ∧
    run (structChildReadCode (C := C) 1 root "items" zeroWord) machine=.ok (machine.push w[1]) 0 ∧
    run (structChildReadCode (C := C) 1 root "items" zeroWord) target=.ok (target.push w[0]) 0 := by
  have hinit : SourceBoolStructAt (withArgs sy k0 true) 2 hp parent addresses layout := initial_at.same_heaps rfl rfl
  obtain ⟨z,m',hw,he,hs,hi,hc,hr,hm,hrepr,hl,hstack,ht,halloc,htag,hchild,hchildren,hsource,heffects⟩ :=
    SourceBoolStructAt.resolved_assign_word layout (G p) F0 0 σ parent right addresses initial_at right_at
      sroot srhs root rhs rfl rfl rfl rfl (by decide) SH source_memOK initial_repr
  have hknown : (Source.writeLoc (E := E) (Γ := SΓ) F0 2 (.mem (τ := SB) 2 1) (.memRef rfl 1)).run sy=(.ok (),reached) := by
    obtain ⟨ht,hw⟩ := source_struct_write sy 2 dn layout.source_types u7 0 1 initial_at.parent
    exact hw
  have hz : z=reached := congrArg Prod.snd (hw.symm.trans hknown)
  subst z
  change m'=target at ht
  subst m'
  have hreach : SourceBoolStructAt (withArgs reached k0 true) 2 out parent addresses layout := hr.same_heaps rfl rfl
  have ha := hinit.read_child_word layout (G p) F0 0 σ parent addresses xroot xi root zeroWord k0 true
    rfl rfl rfl rfl (by decide) (by change hp.index left .dyn k0=some true; simp only [Heap.index,Heap.get,Objs.get,hp,left,k0,indexValue,Int.toNat_natCast,MObj.elems_dyn];rfl) initial_repr rfl
  have hb := hreach.read_child_word layout (G p) F0 0 (σ.withHeap out) parent addresses xroot xi root zeroWord k0 false
    rfl rfl rfl rfl (by decide) (by change out.index right .dyn k0=some false; simp only [out,Heap.index,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,parent,right,k0,indexValue,Int.toNat_natCast,MObj.elems_dyn];rfl) hrepr rfl
  exact ⟨ha.1,hb.1,ha.2,hb.2⟩

private def selectedAgain : Source.EMState E SΓ := (reached.1.set srhs (.memRef rfl 1),reached.2)
private def selectedState := (σ.withHeap out).setLocal rhs (some right)
private def selectedMachine := writeMachine target 3 w[24]
private def selectedCode := structSelectedAliasCode 1 rhs root "items"
private def mutatedHp := out.set right (MObj.setElem .dyn (out.get right) 0 true)
private def mutatedSource : Source.EMState E XΓ :=
  ((withArgs selectedAgain k0 true).1,{selectedAgain.2 with heap := selectedAgain.2.heap.write 1 (sourceBoolMemory [true,true,false]) (by rfl)})
private def mutatedMachine := writeMachine selectedMachine 25 w[1]
private def childTerm : Source.RExpr E XΓ .bool := sourceStructChildAssign layout xroot xi xv
private def childCode := structChildWriteCode (C := C) 1 root "items" zeroWord trueWord

/-- Actual assignment, reached member selection, then member-index mutation.
The old LEFT local remains LEFT; the selected RIGHT leaf alone changes. -/
theorem reached_member_child_write (p : Roadmap.Pipeline) :
    (Source.evalE (G p) F0 3 term).run sy=(.ok (.val (.memRef rfl 1)),reached) ∧
    (Source.evalE (G p) F0 3 (sourceStructSelectedAlias layout srhs sroot)).run reached=(.ok (.val (.memRef rfl 1)),selectedAgain) ∧
    run (code++selectedCode++childCode) machine=.ok mutatedMachine 0 ∧
    (Source.evalE (G p) F0 4 childTerm).run (withArgs selectedAgain k0 true)=(.ok (.val (.bool true)),mutatedSource) ∧
    (Source.execS (G p) F0 5 XΓ.length none (.expr childTerm : Source.RStmt E [] false .body XΓ XΓ)
      (withArgs selectedAgain k0 true).1).run (.nil,selectedAgain.2)=(.ok (.normal mutatedSource.1),(.nil,mutatedSource.2)) ∧
    Stmt.run selectedState (.assignMem (.index .dyn (.loc (.field (.var root (by decide)) "items" layout.child_type)) zeroWord) (.val trueWord))=
      .ok ⟨selectedState.withHeap mutatedHp,List.prefix_refl _⟩ ∧
    SourceBoolStructAt mutatedSource 2 mutatedHp parent addresses layout ∧ Source.MemOK E SH mutatedSource ∧
    StateRepr 1 1 8 (Frag.init Γ) (selectedState.withHeap mutatedHp) base mutatedMachine ∧
    [MObj.elems .dyn (hp.get left),MObj.elems .dyn (hp.get right),MObj.elems .dyn (out.get left),MObj.elems .dyn (out.get right),
      MObj.elems .dyn (mutatedHp.get left),MObj.elems .dyn (mutatedHp.get right)]=
      [[true,false,false],[false,true,false],[true,false,false],[false,true,false],[true,false,false],[true,true,false]] ∧
    [cells machine,cells target,cells selectedMachine,cells mutatedMachine]=
      [[w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[16]],
       [w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[24]],
       [w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[24]],
       [w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[1],w[1],w[0],w[7],w[24]]] ∧
    mutatedSource.2.heap.get 0=some ⟨SB,sourceBoolMemory [true,false,false]⟩ ∧
    mutatedSource.2.heap.get 1=some ⟨SB,sourceBoolMemory [true,true,false]⟩ ∧
    mutatedSource.2.heap.get 2=some ⟨SS,data 1⟩ ∧
    [sy.1.get soldAlias,reached.1.get soldAlias,selectedAgain.1.get soldAlias]=[.memRef rfl 0,.memRef rfl 0,.memRef rfl 0] ∧
    [(TEnv.get oldAlias σ.env).map HRef.id,(TEnv.get oldAlias selectedState.env).map HRef.id]=[some 0,some 0] ∧
    mutatedHp.field parent layout.tag_type=u7 ∧ (mutatedHp.field parent layout.child_type).id=1 ∧
    mutatedSource.2.ex=sy.2.ex ∧ mutatedSource.2.events=sy.2.events ∧ mutatedSource.2.logs=sy.2.logs ∧
    mutatedMachine.stack=[w[42]] ∧ StructAllocatorRepr mutatedHp base 8 ⟨48,by decide⟩ mutatedMachine := by
  obtain ⟨z,m',hw,he,hs,hi,hc,hr,hm,hrepr,hl,hstack,ht,halloc,htag,hchild,hchildren,hsource,heffects⟩ :=
    SourceBoolStructAt.resolved_assign_word layout (G p) F0 0 σ parent right addresses initial_at right_at
      sroot srhs root rhs rfl rfl rfl rfl (by decide) SH source_memOK initial_repr
  have hknown : (Source.writeLoc (E := E) (Γ := SΓ) F0 2 (.mem (τ := SB) 2 1) (.memRef rfl 1)).run sy=(.ok (),reached) := by
    obtain ⟨ht,hw⟩ := source_struct_write sy 2 dn layout.source_types u7 0 1 initial_at.parent
    exact hw
  have hz : z=reached := congrArg Prod.snd (hw.symm.trans hknown)
  subst z
  change m'=target at ht
  subst m'
  obtain ⟨he₁,hs₁,hi₁,hc₁,hr₁,hselected,hm₁,hrepr₁,hsh,hth,hget,htget,hstack₁,halloc₁⟩ :=
    SourceBoolStructAt.selected_alias_word layout (G p) F0 0 (σ.withHeap out) parent addresses hr
      srhs sroot rhs root rfl rfl (by decide) SH hm hrepr
  have hqr : (σ.withHeap out).heap.field parent layout.child_type=right := by rfl
  simp only [hqr] at he₁ hs₁ hi₁ hc₁ hr₁ hselected hm₁ hrepr₁ hsh hth hget htget hstack₁ halloc₁
  have hrx : SourceBoolStructAt (withArgs selectedAgain k0 true) 2 selectedState.heap parent addresses layout := hr₁.same_heaps rfl rfl
  have hqrSelected : selectedState.heap.field parent layout.child_type=right := hqr
  have hrget : selectedState.heap.get right=hp.get right := hchildren right
  have hkSelected : k0.1.toNat<selectedState.heap.len (selectedState.heap.field parent layout.child_type) .dyn := by
    rw [hqrSelected]
    change k0.1.toNat<(MObj.elems .dyn (selectedState.heap.get right)).length
    rw [hrget]
    simp only [Heap.get,Objs.get,hp,right,MObj.elems_dyn,k0,indexValue,Int.toNat_natCast,List.length_cons,List.length_nil]
    decide
  obtain ⟨out',z',target',hw',hwrite',he',hs',hi',hc',hr',hm',hrepr',hl',hstack',halloc',hp',ho',hso',hex',hev',hlog',hfn'⟩ :=
    hrx.assign_child_word layout (G p) F0 0 selectedState parent addresses xroot xi xv root zeroWord trueWord k0 true
      rfl rfl rfl rfl rfl rfl (by decide) hkSelected SH (withArgs_memOK _ _ _ hm₁) hrepr₁ rfl rfl
  have ho : out'=mutatedHp := Option.some.inj (hw'.symm.trans (show selectedState.heap.writeAddr (.index (selectedState.heap.field parent layout.child_type) .dyn k0) true=some mutatedHp from by
      rw [hqrSelected]
      simp only [Heap.writeAddr,Heap.setIndex]
      rw [if_pos (by simpa only [hqrSelected] using hkSelected)]
      rfl))
  subst out'
  have hz' : z'=mutatedSource := by
    obtain ⟨ht,hw⟩ := source_bool_write (withArgs selectedAgain k0 true) 1 [false,true,false] (by rfl) 0 (by decide) true
    have hwr : (Source.writeLoc (E := E) (Γ := XΓ) F0 3 (.mem (τ := .bool) 1 0) (.bool true)).run (withArgs selectedAgain k0 true)=(.ok (),mutatedSource) := hw
    rw [hqrSelected] at hwrite'
    exact congrArg Prod.snd (hwrite'.symm.trans hwr)
  subst z'
  have ht' : target'=mutatedMachine := by
    let ptr := [.mload (cellOf 1 root)]++readFieldCode (fieldOffset (structDef S) "items")
    have hp : PtrFrag 1 (fieldPath root) ptr := .field _ _ _ (.local root (by decide))
    have hpath : (fieldPath root).mvalT selectedState=.ok right := by
      simp only [fieldPath,MPath.mvalT,MLoc.addrT,Heap.readAddr,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
      rfl
    have hptr := hp.run_of_eval (hrepr₁.push w[1]) hpath
    change run ptr (selectedMachine.push w[1])=.ok ((selectedMachine.push w[1]).push (.val (base right.id))) 0 at hptr
    have hraw : run (writeArrayCode (base right.id)) ((selectedMachine.push w[1]).push w[0])=.ok mutatedMachine 0 := by
      obtain ⟨_,_,hc,_⟩ | ⟨hn,_⟩ := writeArray_correct (hrepr₁.heap.arrays right) ⟨0,by decide⟩ true w[1] rfl
      · exact hc
      · have hwKnown : selectedState.heap.writeAddr (.index right .dyn k0) true=some mutatedHp := by
          rw [←hqrSelected];exact hw'
        change selectedState.heap.writeAddr (.index right .dyn k0) true=none at hn
        rw [hwKnown] at hn;cases hn
    have hcalc : run childCode selectedMachine=.ok mutatedMachine 0 := by
      change run ((compileVal 1 trueWord)++ptr++compileVal 1 zeroWord++writeArrayStackCode) selectedMachine=_
      rw [List.append_assoc,List.append_assoc,run_append_ok (show run (compileVal 1 trueWord) selectedMachine=.ok (selectedMachine.push w[1]) 0 from rfl),
        run_append_ok hptr,run_append_ok (show run (compileVal 1 zeroWord) ((selectedMachine.push w[1]).push (.val (base right.id)))=
          .ok (((selectedMachine.push w[1]).push (.val (base right.id))).push w[0]) 0 from rfl)]
      rw [writeArrayStackCode,arrayStack_append_eq (selectedMachine.push w[1]) (base right.id) ⟨0,by decide⟩ _
        (selectedState.heap.len_dyn_lt right) (hrepr₁.heap.arrays right).length,←writeArrayCode]
      exact hraw
    exact (Evm.Out.ok.inj (hc'.symm.trans hcalc)).1
  subst target'
  refine ⟨he,he₁,?_,he',hs',hi',hr',hm',hrepr',?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hstack',?_⟩
  · exact (run_append_ok (run_append_ok hc |>.trans hc₁)).trans hc'
  · simp only [mutatedHp,out,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,left,right,parent,MObj.elems_dyn,MObj.setElem]
    rfl
  · rfl
  · exact halloc' _ (by decide) (halloc₁ _ (by decide) (halloc _ (by decide) initial_allocator))


private def endpointWord : Val C Γ .uint := .simple (.lit 3 (by decide))
private def k3 : PrimTy.uint.Denote := indexValue ⟨3,by decide⟩

/-- Exact Source index panic, intrinsic failure and symbolic-word reversion
are separate observations. No target panic bytes or rollback is asserted. -/
theorem member_child_failure_views (p : Roadmap.Pipeline) :
    (Source.evalLoc (G p) F0 3 (sourceStructChildLoc layout xroot xi)).run (withArgs sy k3 true)=
      (.error (.revert (Source.panicData .index)),withArgs sy k3 true) ∧
    (Source.evalE (G p) F0 4 childTerm).run (withArgs sy k3 true)=
      (.error (.revert (Source.panicData .index)),withArgs sy k3 true) ∧
    (∀ n,n≤2 → (Source.evalE (G p) F0 n (sourceStructChildRead layout xroot xi)).run (withArgs sy k0 true)=
      (.error .timeout,withArgs sy k0 true)) ∧
    hp.writeAddr (.index left .dyn k3) true=none ∧
    run (structChildWriteCode (C := C) 1 root "items" endpointWord trueWord) machine=.revert ∧
    MObj.elems .dyn (out.get right)≠MObj.elems .dyn (mutatedHp.get right) ∧
    MObj.elems .dyn ((out.set left (MObj.setElem .dyn (out.get left) 0 true)).get right)≠
      MObj.elems .dyn (mutatedHp.get right) ∧
    (Source.evalE (G p) F0 3 (sourceStructChildRead layout xroot xi)).run (withArgs reached k0 true)≠
      (.ok (.val (.bool true)),withArgs reached k0 true) := by
  have hr : SourceBoolStructAt (withArgs sy k3 true) 2 hp parent addresses layout := initial_at.same_heaps rfl rfl
  have hb := hr.child_bounds (G p) F0 0 xroot xi xv k3 true rfl rfl rfl (by
    change (MObj.elems .dyn (hp.get left)).length≤k3.1.toNat
    simp only [Heap.get,Objs.get,hp,left,MObj.elems_dyn,k3,indexValue,Int.toNat_natCast,List.length_cons,List.length_nil]
    decide)
  have hn : hp.writeAddr (.index left .dyn k3) true=none := by
    have hcond : ¬k3.1.toNat<(MObj.elems .dyn (hp.get left)).length := by
      simp only [k3,indexValue,Int.toNat_natCast,Heap.get,Objs.get,hp,left,MObj.elems_dyn,List.length_cons,List.length_nil]
      decide
    unfold Heap.writeAddr Heap.setIndex
    exact if_neg hcond
  have hnσ : σ.heap.writeAddr (.index left .dyn k3) true=none := hn
  have hpath : (fieldPath root).mvalT σ=.ok left := by
    simp only [fieldPath,MPath.mvalT,MLoc.addrT,Heap.readAddr,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    rfl
  have hi : TRun.assignMem (.index .dyn (fieldPath root) endpointWord) (.val trueWord) σ=.error .revert := by
    simp only [TRun.assignMem,MSrc.mvalT,MLoc.addrT,hpath,
      show trueWord.evalT σ=.ok true from rfl,show endpointWord.evalT σ=.ok k3 from rfl,
      hnσ,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
  have hptrCert : PtrFrag 1 (fieldPath root)
      ([.mload (cellOf 1 root)]++readFieldCode (fieldOffset (structDef S) "items")) := .field _ _ _ (.local root (by decide))
  have hc := hptrCert.writeArray initial_repr endpointWord trueWord (compileVal 1 endpointWord) (compileVal 1 trueWord)
    (fun h' => Evm.val_sim endpointWord h'.core rfl) (Evm.val_sim trueWord initial_repr.core rfl)
  rw [hi] at hc
  have hrun : run (structChildWriteCode (C := C) 1 root "items" endpointWord trueWord) machine=.revert := by
    rcases hc with ⟨o,_,he,_⟩ | ⟨_,hc⟩
    · cases he
    · exact hc
  refine ⟨hb.1,hb.2,source_struct_child_low_horizon layout (G p) F0 _ xroot xi,?_,hrun,?_,?_,?_⟩
  · exact hn
  · simp only [mutatedHp,out,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,left,right,parent,MObj.elems_dyn,MObj.setElem]
    change ([false,true,false] : List Bool)≠[true,true,false]
    decide
  · simp only [mutatedHp,out,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,left,right,parent,MObj.elems_dyn,MObj.setElem]
    change ([false,true,false] : List Bool)≠[true,true,false]
    decide
  · rw [(member_child_reads p).2.1]
    intro he
    cases he

/-- All runtime-valid indices of arbitrary initial child lists execute actual
member-index syntax. The second family consumes the REAL reference-write result. -/
theorem member_child_runtime_reads (p : Roadmap.Pipeline) (xs ys : List Bool)
    (hx : xs.length<2^256) (hy : ys.length<2^256) :
    (∀ j : Fin xs.length, (Source.evalE (G p) F0 3 (sourceStructChildRead layout xroot xi)).run
      (withArgs (runtimeSource xs ys) (indexValue ⟨j.val,by have h := j.isLt;change j.val<2^256;omega⟩) true)=
        (.ok (.val (.bool xs[j.val])),withArgs (runtimeSource xs ys) (indexValue ⟨j.val,by have h := j.isLt;change j.val<2^256;omega⟩) true)) ∧
    ∃ z : Source.EMState E SΓ,
      (Source.writeLoc (E := E) (Γ := SΓ) F0 0 (.mem (τ := SB) 2 1) (.memRef rfl 1)).run (runtimeSource xs ys)=(.ok (),z) ∧
      (∀ j : Fin ys.length,(Source.evalE (G p) F0 3 (sourceStructChildRead layout xroot xi)).run
        (withArgs z (indexValue ⟨j.val,by have h := j.isLt;change j.val<2^256;omega⟩) true)=
          (.ok (.val (.bool ys[j.val])),withArgs z (indexValue ⟨j.val,by have h := j.isLt;change j.val<2^256;omega⟩) true)) := by
  let hp := runtimeHp xs ys hx hy
  have hinit : SourceBoolStructAt (runtimeSource xs ys) 2 hp parent addresses layout := by
    refine ⟨rfl,?_⟩
    unfold SourceBoolMemoryAt
    simp only [hp,runtimeHp,Heap.get,Objs.get,left,MObj.elems_dyn];rfl
  constructor
  · intro j
    have hr : SourceBoolStructAt (withArgs (runtimeSource xs ys) (indexValue ⟨j.val,by have h := j.isLt;change j.val<2^256;omega⟩) true) 2 hp parent addresses layout := hinit.same_heaps rfl rfl
    apply hr.eval_child_read (G p) F0 0 xroot xi _ _ rfl rfl
    change (MObj.elems .dyn (hp.get left))[j.val]?=some xs[j.val]
    simpa only [hp,runtimeHp,Heap.get,Objs.get,left,MObj.elems_dyn] using
      (List.getElem?_eq_some_iff.mpr ⟨j.isLt,rfl⟩ : xs[j.val]?=some xs[j.val])
  · obtain ⟨z,hw,hr,hm,hleft,hright⟩ := runtime_children xs ys hx hy
    obtain ⟨ht,hknown⟩ := source_struct_write (runtimeSource xs ys) 2 dn layout.source_types u7 0 1 hinit.parent
    have hz : z.1=(runtimeSource xs ys).1 := congrArg (fun x : Except Source.Halt Unit × Source.EMState E SΓ => x.2.1) (hw.symm.trans hknown)
    refine ⟨z,hw,?_⟩
    intro j
    have hrx : SourceBoolStructAt (withArgs z (indexValue ⟨j.val,by have h := j.isLt;change j.val<2^256;omega⟩) true) 2 (hp.setField parent layout.child_type right) parent addresses layout := hr.same_heaps rfl rfl
    apply hrx.eval_child_read (G p) F0 0 xroot xi _ _ (by change z.1.get sroot=_;rw [hz];rfl) rfl
    change (MObj.elems .dyn ((hp.setField parent layout.child_type right).get right))[j.val]?=some ys[j.val]
    simpa only [hp,runtimeHp,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,parent,right,MObj.elems_dyn] using
      (List.getElem?_eq_some_iff.mpr ⟨j.isLt,rfl⟩ : ys[j.val]?=some ys[j.val])


/-- Actual exact-end rejection for arbitrary runtime lengths, including an
EMPTY selected child. Unlike valid-index quantification this executes a call. -/
theorem member_child_runtime_endpoint (p : Roadmap.Pipeline) (xs ys : List Bool)
    (hx : xs.length<2^256) (hy : ys.length<2^256) :
    let k := indexValue ⟨xs.length,hx⟩
    let y := withArgs (runtimeSource xs ys) k true
    (Source.evalLoc (G p) F0 3 (sourceStructChildLoc layout xroot xi)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
    (Source.evalE (G p) F0 4 childTerm).run y=(.error (.revert (Source.panicData .index)),y) := by
  dsimp only
  let hp := runtimeHp xs ys hx hy
  have hinit : SourceBoolStructAt (runtimeSource xs ys) 2 hp parent addresses layout := by
    refine ⟨rfl,?_⟩
    unfold SourceBoolMemoryAt
    simp only [hp,runtimeHp,Heap.get,Objs.get,left,MObj.elems_dyn];rfl
  have hr : SourceBoolStructAt (withArgs (runtimeSource xs ys) (indexValue ⟨xs.length,hx⟩) true) 2 hp parent addresses layout := hinit.same_heaps rfl rfl
  apply hr.child_bounds (G p) F0 0 xroot xi xv _ true rfl rfl rfl
  change (MObj.elems .dyn (hp.get left)).length≤(indexValue ⟨xs.length,hx⟩).1.toNat
  simp only [hp,runtimeHp,Heap.get,Objs.get,left,MObj.elems_dyn,indexValue,Int.toNat_natCast]
  exact Nat.le_refl _


/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.member_child_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms member_child_reads

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.reached_member_child_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reached_member_child_write

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.member_child_failure_views' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms member_child_failure_views

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.member_child_runtime_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms member_child_runtime_reads

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.member_child_runtime_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms member_child_runtime_endpoint


private def deletedInitial := selectedState.withHeap mutatedHp
private def deletedHp := mutatedHp.set right (MObj.setElem .dyn (mutatedHp.get right) 0 false)
private def deletedSource : Source.EMState E XΓ :=
  (mutatedSource.1,{mutatedSource.2 with heap := mutatedSource.2.heap.write 1 (sourceBoolMemory [false,true,false]) (by rfl)})
private def deletedMachine := writeMachine mutatedMachine 25 w[0]
private def deleteTerm : Source.RExpr E XΓ (.tuple []) := sourceStructChildDelete layout xroot xi
private def deleteCode := structChildDeleteCode (C := C) 1 root "items" zeroWord

/-- Consume C51's actual reached changed state, not a separately initial run.
The existing reference-write/selection/content-write prefix makes deletion
material; old LEFT aliases remain LEFT while selected RIGHT is cleared. -/
theorem reached_member_child_delete (p : Roadmap.Pipeline) :
    (Source.evalE (G p) F0 3 term).run sy=(.ok (.val (.memRef rfl 1)),reached) ∧
    (Source.evalE (G p) F0 3 (sourceStructSelectedAlias layout srhs sroot)).run reached=(.ok (.val (.memRef rfl 1)),selectedAgain) ∧
    (Source.evalE (G p) F0 4 childTerm).run (withArgs selectedAgain k0 true)=(.ok (.val (.bool true)),mutatedSource) ∧
    (Source.evalE (G p) F0 4 deleteTerm).run mutatedSource=(.ok Source.RVal.unit,deletedSource) ∧
    (Source.execS (G p) F0 5 XΓ.length none (.expr deleteTerm : Source.RStmt E [] false .body XΓ XΓ)
      mutatedSource.1).run (.nil,mutatedSource.2)=(.ok (.normal mutatedSource.1),(.nil,deletedSource.2)) ∧
    Stmt.run deletedInitial (.deleteMem (.loc (.index .dyn (fieldPath root) zeroWord)) rfl)=
      .ok ⟨deletedInitial.withHeap deletedHp,List.prefix_refl _⟩ ∧
    run ((code++selectedCode++childCode)++deleteCode) machine=.ok deletedMachine 0 ∧
    SourceBoolStructAt deletedSource 2 deletedHp parent addresses layout ∧ Source.MemOK E SH deletedSource ∧
    StateRepr 1 1 8 (Frag.init Γ) (deletedInitial.withHeap deletedHp) base deletedMachine ∧
    [MObj.elems .dyn (hp.get left),MObj.elems .dyn (hp.get right),MObj.elems .dyn (out.get left),MObj.elems .dyn (out.get right),
      MObj.elems .dyn (mutatedHp.get left),MObj.elems .dyn (mutatedHp.get right),MObj.elems .dyn (deletedHp.get left),MObj.elems .dyn (deletedHp.get right)]=
      [[true,false,false],[false,true,false],[true,false,false],[false,true,false],[true,false,false],[true,true,false],[true,false,false],[false,true,false]] ∧
    [cells machine,cells target,cells selectedMachine,cells mutatedMachine,cells deletedMachine]=
      [[w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[16]],
       [w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[24]],
       [w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[24]],
       [w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[1],w[1],w[0],w[7],w[24]],
       [w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[24]]] ∧
    deletedSource.2.heap.get 0=some ⟨SB,sourceBoolMemory [true,false,false]⟩ ∧
    deletedSource.2.heap.get 1=some ⟨SB,sourceBoolMemory [false,true,false]⟩ ∧
    deletedSource.2.heap.get 2=some ⟨SS,data 1⟩ ∧
    (Source.readLoc (E := E) (Γ := XΓ) F0 (τ := .bool) (.mem 1 0)).run deletedSource=(.ok (.bool false),deletedSource) ∧
    (Source.readLoc (E := E) (Γ := XΓ) F0 (τ := .bool) (.mem 0 0)).run deletedSource=(.ok (.bool true),deletedSource) ∧
    deletedSource.1.get (.there (.there soldAlias))=.memRef rfl 0 ∧
    (TEnv.get oldAlias (deletedInitial.withHeap deletedHp).env).map HRef.id=some 0 ∧
    deletedHp.field parent layout.tag_type=u7 ∧ (deletedHp.field parent layout.child_type).id=1 ∧
    deletedSource.2.ex=sy.2.ex ∧ deletedSource.2.events=sy.2.events ∧ deletedSource.2.logs=sy.2.logs ∧
    deletedMachine.stack=[w[42]] ∧ StructAllocatorRepr deletedHp base 8 ⟨48,by decide⟩ deletedMachine := by
  obtain ⟨he₀,he₁,hprefix,hewrite,hswrite,hiwrite,hr,hm,hrepr,hvectors,hcells,hsource₀,hsource₁,hsource₂,
    hlocals,htlocals,htag,hid,hex,hev,hlog,hstack,halloc⟩ := reached_member_child_write p
  have hqr : deletedInitial.heap.field parent layout.child_type=right := by
    simp only [deletedInitial,mutatedHp,selectedState,State.withHeap,State.setLocal,Heap.field,
      Heap.get_set_ne out right parent (by decide)]
    rfl
  have hk : k0.1.toNat<deletedInitial.heap.len (deletedInitial.heap.field parent layout.child_type) .dyn := by
    rw [hqr]
    change k0.1.toNat<(MObj.elems .dyn (mutatedHp.get right)).length
    simp only [mutatedHp,Heap.get_set_same,MObj.elems_setElem,List.length_set]
    change k0.1.toNat<(MObj.elems .dyn (out.get right)).length
    simp only [out,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,parent,right,MObj.elems_dyn,k0,indexValue,Int.toNat_natCast,List.length_cons,List.length_nil]
    decide
  obtain ⟨out',z',target',hw,hdel,he,hs,hi,hc,hr',hm',hrepr',hl,hstack',halloc',hparent,hother,hsource,hex',hev',hlog',hfn'⟩ :=
    hr.delete_child_word layout (G p) F0 0 deletedInitial parent addresses xroot xi root zeroWord k0
      rfl rfl rfl rfl (by decide) hk SH hm hrepr rfl
  have ho : out'=deletedHp := Option.some.inj (hw.symm.trans (show deletedInitial.heap.writeAddr
      (.index (deletedInitial.heap.field parent layout.child_type) .dyn k0) false=some deletedHp from by
        rw [hqr]
        simp only [Heap.writeAddr,Heap.setIndex]
        rw [if_pos (by simpa only [hqr] using hk)]
        rfl))
  subst out'
  have hz : z'=deletedSource := by
    obtain ⟨ht,hw⟩ := source_bool_write mutatedSource 1 [true,true,false] hsource₁ 0 (by decide) false
    have hknown : (Source.deleteLoc (E := E) (Γ := XΓ) F0 3 (τ := .bool) (.mem 1 0)).run mutatedSource=(.ok (),deletedSource) := hw
    rw [hqr] at hdel
    exact congrArg Prod.snd (hdel.symm.trans hknown)
  subst z'
  have ht : target'=deletedMachine := by
    let ptr := [.mload (cellOf 1 root)]++readFieldCode (fieldOffset (structDef S) "items")
    have hptrCert : PtrFrag 1 (fieldPath root) ptr := .field _ _ _ (.local root (by decide))
    have hpath : (fieldPath root).mvalT deletedInitial=.ok right := by
      simp only [fieldPath,MPath.mvalT,MLoc.addrT,Heap.readAddr,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
      exact congrArg Except.ok hqr
    have hptr := hptrCert.run_of_eval (hrepr.push w[0]) hpath
    change run ptr (mutatedMachine.push w[0])=.ok ((mutatedMachine.push w[0]).push (.val (base right.id))) 0 at hptr
    have hraw : run (writeArrayCode (base right.id)) ((mutatedMachine.push w[0]).push w[0])=.ok deletedMachine 0 := by
      obtain ⟨_,_,hc,_⟩ | ⟨hn,_⟩ := writeArray_correct (hrepr.heap.arrays right) ⟨0,by decide⟩ false w[0] rfl
      · exact hc
      · change deletedInitial.heap.writeAddr (.index right .dyn k0) false=none at hn
        have hwKnown : deletedInitial.heap.writeAddr (.index right .dyn k0) false=some deletedHp := by
          rw [←hqr];exact hw
        rw [hwKnown] at hn;cases hn
    have hcalc : run deleteCode mutatedMachine=.ok deletedMachine 0 := by
      change run ((compileVal 1 (deleteDefaultValue .bool))++ptr++compileVal 1 zeroWord++writeArrayStackCode) mutatedMachine=_
      rw [List.append_assoc,List.append_assoc,
        run_append_ok (show run (compileVal 1 (deleteDefaultValue .bool)) mutatedMachine=.ok (mutatedMachine.push w[0]) 0 from rfl),
        run_append_ok hptr,
        run_append_ok (show run (compileVal 1 zeroWord) ((mutatedMachine.push w[0]).push (.val (base right.id)))=
          .ok (((mutatedMachine.push w[0]).push (.val (base right.id))).push w[0]) 0 from rfl)]
      rw [writeArrayStackCode,arrayStack_append_eq (mutatedMachine.push w[0]) (base right.id) ⟨0,by decide⟩ _
        (deletedInitial.heap.len_dyn_lt right) (hrepr.heap.arrays right).length,←writeArrayCode]
      exact hraw
    exact (Evm.Out.ok.inj (hc.symm.trans hcalc)).1
  subst target'
  refine ⟨he₀,he₁,hewrite,he,hs,hi,(run_append_ok hprefix).trans hc,hr',hm',hrepr',?_,?_,rfl,rfl,rfl,?_,?_,rfl,rfl,?_,?_,rfl,rfl,rfl,hstack',?_⟩
  · simp only [deletedHp,mutatedHp,out,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,left,right,parent,MObj.elems_dyn,MObj.setElem]
    rfl
  · rfl
  · exact source_bool_read deletedSource 1 [false,true,false] rfl 0 (by decide)
  · exact source_bool_read deletedSource 0 [true,false,false] rfl 0 (by decide)
  · change deletedHp.field parent layout.tag_type=u7
    simp only [Heap.field,hparent]
    exact htag
  · change (deletedHp.field parent layout.child_type).id=1
    simp only [Heap.field,hparent]
    exact hid
  · exact halloc' _ (by decide) halloc


private def wrongDeletedSource : Source.EMState E XΓ :=
  (mutatedSource.1,{mutatedSource.2 with heap := mutatedSource.2.heap.write 0 (sourceBoolMemory [false,false,false]) (by rfl)})
private def wrongDeletedHp := mutatedHp.set left (MObj.setElem .dyn (mutatedHp.get left) 0 false)

/-- Actual wrong retained-local deletion changes LEFT, unlike member-selected
RIGHT deletion. Source panic, intrinsic rejection and word revert stay separate. -/
theorem member_delete_failure_views (p : Roadmap.Pipeline) :
    (Source.evalE (G p) F0 4 deleteTerm).run (withArgs sy k3 true)=
      (.error (.revert (Source.panicData .index)),withArgs sy k3 true) ∧
    (∀ n,n≤3 → (Source.evalE (G p) F0 n deleteTerm).run (withArgs sy k0 true)=(.error .timeout,withArgs sy k0 true)) ∧
    hp.writeAddr (.index left .dyn k3) (PrimTy.dflt .bool)=none ∧
    Stmt.run σ (.deleteMem (.loc (.index .dyn (fieldPath root) endpointWord)) rfl)=.error .revert ∧
    run (structChildDeleteCode (C := C) 1 root "items" endpointWord) machine=.revert ∧
    (Source.evalE (G p) F0 3 (sourceIndexedDelete (.there (.there soldAlias)) xi)).run mutatedSource=
      (.ok Source.RVal.unit,wrongDeletedSource) ∧
    mutatedHp.writeAddr (.index left .dyn k0) (PrimTy.dflt .bool)=some wrongDeletedHp ∧
    wrongDeletedSource.2.heap.get 0=some ⟨SB,sourceBoolMemory [false,false,false]⟩ ∧
    wrongDeletedSource.2.heap.get 1=some ⟨SB,sourceBoolMemory [true,true,false]⟩ ∧
    MObj.elems .dyn (mutatedHp.get right)≠MObj.elems .dyn (deletedHp.get right) ∧
    MObj.elems .dyn (wrongDeletedHp.get right)≠MObj.elems .dyn (deletedHp.get right) ∧
    wrongDeletedSource.2.heap.get 1≠deletedSource.2.heap.get 1 := by
  have hr : SourceBoolStructAt (withArgs sy k3 true) 2 hp parent addresses layout := initial_at.same_heaps rfl rfl
  have hge : σ.heap.len (σ.heap.field parent layout.child_type) .dyn≤k3.1.toNat := by
    change (MObj.elems .dyn (hp.get left)).length≤k3.1.toNat
    simp only [Heap.get,Objs.get,hp,left,MObj.elems_dyn,k3,indexValue,Int.toNat_natCast,List.length_cons,List.length_nil]
    decide
  obtain ⟨hb,hn,hd,hrun⟩ := hr.delete_child_word_bounds layout (G p) F0 0 σ parent addresses xroot xi root endpointWord k3
    rfl rfl rfl rfl (by decide) hge initial_repr rfl
  have hold : SourceBoolMemoryAt mutatedSource 0 mutatedHp left .dyn := by
    unfold SourceBoolMemoryAt
    simp only [mutatedHp,out,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,left,right,parent,MObj.elems_dyn]
    rfl
  obtain ⟨ht,hw⟩ := source_bool_write mutatedSource 0 [true,false,false] rfl 0 (by decide) false
  have hraw : (Source.deleteLoc (E := E) (Γ := XΓ) F0 2 (τ := .bool) (.mem 0 0)).run mutatedSource=(.ok (),wrongDeletedSource) := hw
  have hwrong := hold.eval_delete_of_run (G p) F0 0 (.there (.there soldAlias)) xi k0 rfl rfl (by
    simp only [mutatedHp,out,Heap.setField,Heap.len,Heap.get,Heap.set,Objs.get,Objs.set,hp,left,right,parent,MObj.elems_dyn,k0,indexValue,Int.toNat_natCast,List.length_cons,List.length_nil]
    decide) hraw
  refine ⟨hb,source_struct_delete_low_horizon layout (G p) F0 _ xroot xi,hn,hd,hrun,hwrong,?_,rfl,rfl,?_,?_,?_⟩
  · change mutatedHp.writeAddr (.index left .dyn k0) false=some wrongDeletedHp
    have hlt : k0.1.toNat<(MObj.elems .dyn (mutatedHp.get left)).length := by
      simp only [mutatedHp,out,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,left,right,parent,MObj.elems_dyn,k0,indexValue,Int.toNat_natCast,List.length_cons,List.length_nil]
      decide
    simp only [Heap.writeAddr,Heap.setIndex]
    rw [if_pos hlt]
    rfl
  · simp only [deletedHp,mutatedHp,out,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,left,right,parent,MObj.elems_dyn,MObj.setElem]
    change ([true,true,false] : List Bool)≠[false,true,false];decide
  · simp only [wrongDeletedHp,deletedHp,mutatedHp,out,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,left,right,parent,MObj.elems_dyn,MObj.setElem]
    change ([true,true,false] : List Bool)≠[false,true,false];decide
  · intro he
    have hwrongtable : wrongDeletedSource.2.heap.get 1=some ⟨SB,sourceBoolMemory [false,true,false]⟩ := he.trans rfl
    have hread₁ := source_bool_read wrongDeletedSource 1 [true,true,false] rfl 0 (by decide)
    have hread₂ := source_bool_read wrongDeletedSource 1 [false,true,false] hwrongtable 0 (by decide)
    have hbad := hread₁.symm.trans hread₂
    cases hbad


/-- Arbitrary runtime valid indices consume the ACTUAL reference-write output.
Logical Source execution requires no invented fixed word layout for the lists. -/
theorem member_delete_runtime_valid (p : Roadmap.Pipeline) (xs ys : List Bool)
    (hx : xs.length<2^256) (hy : ys.length<2^256) (j : Fin ys.length) :
    let k := indexValue ⟨j.val,by have h := j.isLt;change j.val<2^256;omega⟩
    ∃ (mid : Source.EMState E SΓ) (out' : Heap H) (z : Source.EMState E XΓ),
      (Source.writeLoc (E := E) (Γ := SΓ) F0 0 (.mem (τ := SB) 2 1) (.memRef rfl 1)).run (runtimeSource xs ys)=(.ok (),mid) ∧
      (Source.evalE (G p) F0 4 deleteTerm).run (withArgs mid k true)=(.ok Source.RVal.unit,z) ∧
      SourceBoolStructAt z 2 out' parent addresses layout ∧ Source.MemOK E SH z ∧
      (Source.readLoc (E := E) (Γ := XΓ) F0 (τ := .bool) (.mem 1 j.val)).run z=(.ok (.bool false),z) := by
  dsimp only
  let hp := runtimeHp xs ys hx hy
  let hp' := hp.setField parent layout.child_type right
  let k := indexValue ⟨j.val,by have h := j.isLt;change j.val<2^256;omega⟩
  have hinit : SourceBoolStructAt (runtimeSource xs ys) 2 hp parent addresses layout := by
    refine ⟨rfl,?_⟩
    unfold SourceBoolMemoryAt
    simp only [hp,runtimeHp,Heap.get,Objs.get,left,MObj.elems_dyn];rfl
  obtain ⟨mid,hwref,hr,hm,hleft,hright⟩ := runtime_children xs ys hx hy
  obtain ⟨ht,hknown⟩ := source_struct_write (runtimeSource xs ys) 2 dn layout.source_types u7 0 1 hinit.parent
  have hlocals : mid.1=(runtimeSource xs ys).1 := congrArg (fun x : Except Source.Halt Unit × Source.EMState E SΓ => x.2.1) (hwref.symm.trans hknown)
  have hrx : SourceBoolStructAt (withArgs mid k true) 2 hp' parent addresses layout := hr.same_heaps rfl rfl
  have hq : hp'.field parent layout.child_type=right := by rfl
  have hk : k.1.toNat<hp'.len (hp'.field parent layout.child_type) .dyn := by
    rw [hq]
    simpa only [hp',hp,runtimeHp,Heap.setField,Heap.len,Heap.get,Heap.set,Objs.get,Objs.set,parent,right,MObj.elems_dyn,k,indexValue,Int.toNat_natCast] using j.isLt
  obtain ⟨out',z,hw,he,hr',hm',hl,hparent⟩ := hrx.delete_child_source (G p) F0 0 xroot xi k
    (by change mid.1.get sroot=_;rw [hlocals];rfl) rfl hk SH (withArgs_memOK _ _ _ hm)
  have ho : out'=hp'.set right (MObj.setElem .dyn (hp'.get right) k.1.toNat false) :=
    Option.some.inj (hw.symm.trans (show hp'.writeAddr (.index (hp'.field parent layout.child_type) .dyn k) false=
      some (hp'.set right (MObj.setElem .dyn (hp'.get right) k.1.toNat false)) from by
        rw [hq]
        simp only [Heap.writeAddr,Heap.setIndex]
        exact if_pos (by simpa only [hq] using hk)))
  have hqout : out'.field parent layout.child_type=right := by
    unfold Heap.field
    rw [hparent]
    exact hq
  have hleaf := hr'.leaf
  rw [hqout] at hleaf
  have hindex : out'.index right .dyn k=some false := by
    rw [ho]
    simp only [Heap.index,Heap.get_set_same,MObj.elems_setElem]
    exact List.getElem?_set_self (by simpa only [hq,Heap.len] using hk)
  have hread := (hleaf.read_iff F0 k false).mpr hindex
  refine ⟨mid,out',z,hwref,he,hr',hm',?_⟩
  simpa only [k,indexValue,Int.toNat_natCast] using hread

/-- Actual runtime endpoint deletion rejection, including an EMPTY child.
The independent intrinsic None observation has no word-space assumption. -/
theorem member_delete_runtime_endpoint (p : Roadmap.Pipeline) (xs ys : List Bool)
    (hx : xs.length<2^256) (hy : ys.length<2^256) :
    let k := indexValue ⟨xs.length,hx⟩
    let y := withArgs (runtimeSource xs ys) k true
    (Source.evalE (G p) F0 4 deleteTerm).run y=(.error (.revert (Source.panicData .index)),y) ∧
      (runtimeHp xs ys hx hy).writeAddr (.index left .dyn k) (PrimTy.dflt .bool)=none := by
  dsimp only
  have hloc := (member_child_runtime_endpoint p xs ys hx hy).1
  constructor
  · rw [deleteTerm,sourceStructChildDelete,Source.evalE,Source.Hoare.run_bind,hloc]
  · change (runtimeHp xs ys hx hy).writeAddr (.index left .dyn (indexValue ⟨xs.length,hx⟩)) false=none
    have hn : ¬(indexValue ⟨xs.length,hx⟩).1.toNat <
        (MObj.elems .dyn ((runtimeHp xs ys hx hy).get left)).length := by
      simp only [runtimeHp,Heap.get,Objs.get,left,MObj.elems_dyn,indexValue,Int.toNat_natCast]
      exact Nat.not_lt.mpr (Nat.le_refl _)
    simp only [Heap.writeAddr,Heap.setIndex]
    exact if_neg hn


/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.reached_member_child_delete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reached_member_child_delete

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.member_delete_failure_views' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms member_delete_failure_views

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.member_delete_runtime_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms member_delete_runtime_valid

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.member_delete_runtime_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms member_delete_runtime_endpoint


private def cycleInitial := selectedState.withHeap deletedHp
private def cycleMidHp := deletedHp.set right (MObj.setElem .dyn (deletedHp.get right) 0 true)
private def cycleFinalHp := cycleMidHp.set right (MObj.setElem .dyn (cycleMidHp.get right) 0 false)
private def cycleMidSource : Source.EMState E XΓ :=
  (deletedSource.1,{deletedSource.2 with heap := deletedSource.2.heap.write 1 (sourceBoolMemory [true,true,false]) (by rfl)})
private def cycleFinalSource : Source.EMState E XΓ :=
  (cycleMidSource.1,{cycleMidSource.2 with heap := cycleMidSource.2.heap.write 1 (sourceBoolMemory [false,true,false]) (by rfl)})
private def cycleMidMachine := writeMachine deletedMachine 25 w[1]
private def cycleFinalMachine := writeMachine cycleMidMachine 25 w[0]
private def cycleItems := sourceStructWriteDelete layout xroot xi xv
private def cycleProg : Prog C Γ Γ := .cons (.assignMem (.index .dyn (fieldPath root) zeroWord) (.val trueWord))
  (.cons (.deleteMem (.loc (.index .dyn (fieldPath root) zeroWord)) rfl) .nil)

private theorem cycle_word_write {hp' : Heap H} {m : Machine}
    (hm : StateRepr 1 1 8 (Frag.init Γ) (selectedState.withHeap hp') base m)
    (hq : hp'.field parent layout.child_type=right) (hpos : 0<hp'.len right .dyn) (v : Bool) :
    run (structChildWriteCode (C := C) 1 root "items" zeroWord (.simple (.bool v))) m=
      .ok (writeMachine m 25 (.val (bword v))) 0 := by
  let ptr := [.mload (cellOf 1 root)]++readFieldCode (fieldOffset (structDef S) "items")
  have hp : PtrFrag 1 (fieldPath root) ptr := .field _ _ _ (.local root (by decide))
  have hpath : (fieldPath root).mvalT (selectedState.withHeap hp')=.ok right := by
    simp only [fieldPath,MPath.mvalT,MLoc.addrT,Heap.readAddr,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    exact congrArg Except.ok hq
  have hptr := hp.run_of_eval (hm.push (.val (bword v))) hpath
  have hraw : run (writeArrayCode (base right.id)) ((m.push (.val (bword v))).push w[0])=
      .ok (writeMachine m 25 (.val (bword v))) 0 := by
    obtain ⟨_,_,hc,_⟩ | ⟨hn,_⟩ := writeArray_correct (hm.heap.arrays right) ⟨0,by decide⟩ v (.val (bword v)) rfl
    · exact hc
    · have hw : hp'.writeAddr (.index right .dyn k0) v=some (hp'.set right (MObj.setElem .dyn (hp'.get right) 0 v)) := by
        simp only [Heap.writeAddr,Heap.setIndex,k0,indexValue,Int.toNat_natCast]
        exact if_pos hpos
      change hp'.writeAddr (.index right .dyn k0) v=none at hn
      rw [hw] at hn;cases hn
  change run ((compileVal 1 (.simple (.bool v) : Val C Γ .bool))++ptr++compileVal 1 zeroWord++writeArrayStackCode) m=_
  rw [List.append_assoc,List.append_assoc,
    run_append_ok (show run (compileVal 1 (.simple (.bool v) : Val C Γ .bool)) m=.ok (m.push (.val (bword v))) 0 from rfl),
    run_append_ok hptr,
    run_append_ok (show run (compileVal 1 zeroWord) ((m.push (.val (bword v))).push (.val (base right.id)))=
      .ok (((m.push (.val (bword v))).push (.val (base right.id))).push w[0]) 0 from rfl)]
  rw [writeArrayStackCode,arrayStack_append_eq (m.push (.val (bword v))) (base right.id) ⟨0,by decide⟩ _
    (hp'.len_dyn_lt right) (hm.heap.arrays right).length,←writeArrayCode]
  exact hraw

/-- ACTUAL two-statement Source program, not independent initial-state runs.
The first write changes FTF to TTF; its reached output supplies deletion. -/
theorem member_write_delete_program (p : Roadmap.Pipeline) :
    (Source.execItems (G p) F0 7 XΓ.length none cycleItems deletedSource.1).run (.nil,deletedSource.2)=
      (.ok (.normal cycleFinalSource.1),(.nil,cycleFinalSource.2)) ∧
    Prog.run cycleInitial cycleProg=.ok ⟨cycleInitial.withHeap cycleFinalHp,List.prefix_refl _⟩ ∧
    run (childCode++deleteCode) deletedMachine=.ok cycleFinalMachine 0 ∧
    (Source.execS (G p) F0 6 XΓ.length none (.expr childTerm : Source.RStmt E [] false .body XΓ XΓ) deletedSource.1).run (.nil,deletedSource.2)=
      (.ok (.normal cycleMidSource.1),(.nil,cycleMidSource.2)) ∧
    (Source.execS (G p) F0 5 XΓ.length none (.expr deleteTerm : Source.RStmt E [] false .body XΓ XΓ) cycleMidSource.1).run (.nil,cycleMidSource.2)=
      (.ok (.normal cycleFinalSource.1),(.nil,cycleFinalSource.2)) ∧
    SourceBoolStructAt cycleFinalSource 2 cycleFinalHp parent addresses layout ∧ Source.MemOK E SH cycleFinalSource ∧
    StateRepr 1 1 8 (Frag.init Γ) (cycleInitial.withHeap cycleFinalHp) base cycleFinalMachine ∧
    [MObj.elems .dyn (deletedHp.get left),MObj.elems .dyn (deletedHp.get right),MObj.elems .dyn (cycleMidHp.get left),
      MObj.elems .dyn (cycleMidHp.get right),MObj.elems .dyn (cycleFinalHp.get left),MObj.elems .dyn (cycleFinalHp.get right)]=
      [[true,false,false],[false,true,false],[true,false,false],[true,true,false],[true,false,false],[false,true,false]] ∧
    [cells deletedMachine,cells cycleMidMachine,cells cycleFinalMachine]=
      [[w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[24]],
       [w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[1],w[1],w[0],w[7],w[24]],
       [w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[24]]] ∧
    cycleMidSource.2.heap.get 1=some ⟨SB,sourceBoolMemory [true,true,false]⟩ ∧
    cycleFinalSource.2.heap.get 1=some ⟨SB,sourceBoolMemory [false,true,false]⟩ ∧
    cycleFinalSource.2.heap.get 0=some ⟨SB,sourceBoolMemory [true,false,false]⟩ ∧
    cycleFinalSource.2.heap.get 2=some ⟨SS,data 1⟩ ∧
    cycleFinalSource.1.get (.there (.there soldAlias))=.memRef rfl 0 ∧
    (TEnv.get oldAlias (cycleInitial.withHeap cycleFinalHp).env).map HRef.id=some 0 ∧
    cycleFinalMachine.stack=[w[42]] ∧ StructAllocatorRepr cycleFinalHp base 8 ⟨48,by decide⟩ cycleFinalMachine := by
  obtain ⟨he₀,he₁,hew,hed,hsd,hid,hprefix,hr,hm,hrepr,hvec,hcells,h0,h1,h2,hreadright,hreadleft,
    hsalias,htalias,htag,hchildid,hex,hev,hlog,hstack,halloc⟩ := reached_member_child_delete p
  have hq0 : cycleInitial.heap.field parent layout.child_type=right := by
    simp only [cycleInitial,deletedHp,mutatedHp,Heap.field,Heap.get_set_ne mutatedHp right parent (by decide),Heap.get_set_ne out right parent (by decide)]
    rfl
  have hlenInitial : deletedHp.len right .dyn=3 := by
    unfold deletedHp
    simp only [Heap.len,Heap.get_set_same,MObj.elems_setElem,List.length_set]
    change mutatedHp.len right .dyn=3
    unfold mutatedHp
    simp only [Heap.len,Heap.get_set_same,MObj.elems_setElem,List.length_set]
    change out.len right .dyn=3
    rw [out,arrayLen_setRefField]
    simp only [Heap.len,Heap.get,Objs.get,hp,right,MObj.elems_dyn,List.length_cons,List.length_nil]
  have hlen0 : cycleInitial.heap.len right .dyn=3 := hlenInitial
  have hk : k0.1.toNat<cycleInitial.heap.len (cycleInitial.heap.field parent layout.child_type) .dyn := by
    rw [hq0,hlen0];decide
  obtain ⟨mid,out',ym,z,mm,target,hw₁,hw₂,hs₁,hs₂,hitems,hprog,hc₁,hc₂,hcode,hr₁,hr₂,hm₁,hm₂,hrepr₁,hrepr₂,hy₁,hy₂,hlen,hparent,hread,hstack',halloc'⟩ :=
    hr.write_delete_program layout (G p) F0 0 cycleInitial parent addresses xroot xi xv root (.lit 0 rfl) (.bool true) k0 true
      rfl rfl rfl rfl rfl rfl (by decide) hk SH hm hrepr rfl rfl
  have hmid : mid=cycleMidHp := Option.some.inj (hw₁.symm.trans (show cycleInitial.heap.writeAddr (.index (cycleInitial.heap.field parent layout.child_type) .dyn k0) true=some cycleMidHp from by
    rw [hq0];simp only [Heap.writeAddr,Heap.setIndex];rw [if_pos (by simpa only [hq0] using hk)];rfl))
  subst mid
  have hqmid : cycleMidHp.field parent layout.child_type=right := by
    simp only [cycleMidHp,Heap.field,Heap.get_set_ne deletedHp right parent (by decide)]
    exact hq0
  have hmidLen : cycleMidHp.len right .dyn=3 := by
    rw [cycleMidHp,Heap.len,Heap.get_set_same,MObj.elems_setElem,List.length_set]
    exact hlenInitial
  have hout : out'=cycleFinalHp := Option.some.inj (hw₂.symm.trans (show cycleMidHp.writeAddr (.index (cycleInitial.heap.field parent layout.child_type) .dyn k0) false=some cycleFinalHp from by
    rw [hq0];simp only [Heap.writeAddr,Heap.setIndex];rw [if_pos (by change k0.1.toNat<cycleMidHp.len right .dyn;rw [hmidLen];decide)];rfl))
  subst out'
  obtain ⟨ht₁,hwrite₁⟩ := source_bool_write deletedSource 1 [false,true,false] h1 0 (by decide) true
  have hraw₁ : (Source.writeLoc (E := E) (Γ := XΓ) F0 4 (τ := .bool) (.mem 1 0) (.bool true)).run deletedSource=(.ok (),cycleMidSource) := hwrite₁
  have hSourceExpr₁ : (Source.evalE (G p) F0 5 childTerm).run deletedSource=(.ok (.val (.bool true)),cycleMidSource) := by
    rw [childTerm,sourceStructChildAssign,Source.evalE,Source.Hoare.run_bind,source_local_value_run (G p) F0 3 deletedSource xv (.bool true) rfl]
    change ((Source.evalLoc (G p) F0 4 (sourceStructChildLoc layout xroot xi)) >>= fun loc => Source.writeLoc F0 4 loc (.bool true) >>= fun _ => pure (Source.RVal.val (.bool true))).run deletedSource=_
    rw [Source.Hoare.run_bind,hr.eval_child_loc (G p) F0 1 xroot xi k0 rfl rfl hk]
    change (Source.writeLoc F0 4 (τ := .bool) (.mem 1 0) (.bool true) >>= fun _ => pure (Source.RVal.val (.bool true))).run deletedSource=_
    rw [Source.Hoare.run_bind,hraw₁];rfl
  have hKnownStmt₁ := source_expr_statement_run (G p) F0 5 XΓ.length childTerm deletedSource cycleMidSource (.val (.bool true)) hSourceExpr₁
  have hym : ym=cycleMidSource := Prod.ext hy₁ (congrArg (fun x => x.2.2) (hs₁.symm.trans hKnownStmt₁))
  subst ym
  obtain ⟨ht₂,hwrite₂⟩ := source_bool_write cycleMidSource 1 [true,true,false] rfl 0 (by decide) false
  have hSourceExpr₂ : (Source.evalE (G p) F0 4 deleteTerm).run cycleMidSource=(.ok Source.RVal.unit,cycleFinalSource) := by
    rw [deleteTerm,sourceStructChildDelete,Source.evalE,Source.Hoare.run_bind,hr₁.eval_child_loc (G p) F0 0 xroot xi k0 rfl rfl (by rw [hqmid,hmidLen];decide)]
    change (Source.deleteLoc F0 3 (τ := .bool) (.mem 1 0) >>= fun _ => pure Source.RVal.unit).run cycleMidSource=_
    have hd : (Source.deleteLoc (E := E) (Γ := XΓ) F0 3 (τ := .bool) (.mem 1 0)).run cycleMidSource=(.ok (),cycleFinalSource) := hwrite₂
    rw [Source.Hoare.run_bind,hd];rfl
  have hKnownStmt₂ := source_expr_statement_run (G p) F0 4 XΓ.length deleteTerm cycleMidSource cycleFinalSource Source.RVal.unit hSourceExpr₂
  have hz : z=cycleFinalSource := Prod.ext hy₂ (congrArg (fun x => x.2.2) (hs₂.symm.trans hKnownStmt₂))
  subst z
  have hcmid := cycle_word_write hrepr hq0 (by rw [hlenInitial];decide) true
  have hmm : mm=cycleMidMachine := (Evm.Out.ok.inj (hc₁.symm.trans hcmid)).1
  subst mm
  have hcfinal := cycle_word_write hrepr₁ hqmid (by rw [hmidLen];decide) false
  have ht : target=cycleFinalMachine := (Evm.Out.ok.inj (hc₂.symm.trans hcfinal)).1
  subst target
  refine ⟨hitems,hprog,hcode,hs₁,hs₂,hr₂,hm₂,hrepr₂,?_,?_,rfl,rfl,rfl,rfl,rfl,rfl,hstack',halloc' _ (by decide) halloc⟩
  · simp only [cycleFinalHp,cycleMidHp,deletedHp,mutatedHp,out,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,left,right,parent,MObj.elems_dyn,MObj.setElem]
    rfl
  · rfl


/-- The same Source program at horizon6 executes a material first statement
then times out before deletion, retaining the actual reached changed heap.
No successful suffix or rollback state is invented. -/
theorem member_write_delete_timeout (p : Roadmap.Pipeline) :
    (Source.execItems (G p) F0 6 XΓ.length none cycleItems deletedSource.1).run (.nil,deletedSource.2)=
      (.error .timeout,(.nil,cycleMidSource.2)) ∧
    (Source.execItems (G p) F0 0 XΓ.length none cycleItems deletedSource.1).run (.nil,deletedSource.2)=
      (.error .timeout,(.nil,deletedSource.2)) ∧
    (Source.readLoc (E := E) (Γ := XΓ) F0 (τ := .bool) (.mem 1 0)).run cycleMidSource=(.ok (.bool true),cycleMidSource) ∧
    (Source.readLoc (E := E) (Γ := XΓ) F0 (τ := .bool) (.mem 1 0)).run cycleFinalSource=(.ok (.bool false),cycleFinalSource) ∧
    cycleMidMachine.mem 25=w[1] ∧ cycleFinalMachine.mem 25=w[0] ∧
    MObj.elems .dyn (cycleMidHp.get right)≠MObj.elems .dyn (cycleFinalHp.get right) := by
  obtain ⟨he₀,he₁,hew,hed,hsd,hid,hprefix,hr,hm,hrepr,hvec,hcells,h0,h1,h2,tail⟩ := reached_member_child_delete p
  have hk : k0.1.toNat<deletedHp.len (deletedHp.field parent layout.child_type) .dyn := by
    simp only [deletedHp,mutatedHp,out,Heap.setField,Heap.len,Heap.field,Heap.get,Heap.set,Objs.get,Objs.set,hp,parent,right,left,
      MObj.elems_dyn,MObj.setElem,k0,indexValue,Int.toNat_natCast,List.length_set,List.length_cons,List.length_nil]
    decide
  obtain ⟨ht,hw⟩ := source_bool_write deletedSource 1 [false,true,false] h1 0 (by decide) true
  have hraw : (Source.writeLoc (E := E) (Γ := XΓ) F0 3 (τ := .bool) (.mem 1 0) (.bool true)).run deletedSource=(.ok (),cycleMidSource) := hw
  have he : (Source.evalE (G p) F0 4 childTerm).run deletedSource=(.ok (.val (.bool true)),cycleMidSource) := by
    rw [childTerm,sourceStructChildAssign,Source.evalE,Source.Hoare.run_bind,source_local_value_run (G p) F0 2 deletedSource xv (.bool true) rfl]
    change ((Source.evalLoc (G p) F0 3 (sourceStructChildLoc layout xroot xi)) >>= fun loc => Source.writeLoc F0 3 loc (.bool true) >>= fun _ => pure (Source.RVal.val (.bool true))).run deletedSource=_
    rw [Source.Hoare.run_bind,hr.eval_child_loc (G p) F0 0 xroot xi k0 rfl rfl hk]
    change (Source.writeLoc F0 3 (τ := .bool) (.mem 1 0) (.bool true) >>= fun _ => pure (Source.RVal.val (.bool true))).run deletedSource=_
    rw [Source.Hoare.run_bind,hraw];rfl
  have hs₁ := source_expr_statement_run (G p) F0 4 XΓ.length childTerm deletedSource cycleMidSource (.val (.bool true)) he
  have hb := source_struct_delete_low_horizon layout (G p) F0 cycleMidSource xroot xi 3 (by decide)
  have hs₂ := source_expr_statement_error (G p) F0 3 XΓ.length deleteTerm cycleMidSource cycleMidSource .timeout hb
  have hseq := source_items_pair_error (G p) F0 0 XΓ.length (.expr childTerm) (.expr deleteTerm)
    deletedSource cycleMidSource cycleMidSource .timeout hs₁ hs₂
  refine ⟨hseq,rfl,source_bool_read cycleMidSource 1 [true,true,false] rfl 0 (by decide),
    source_bool_read cycleFinalSource 1 [false,true,false] rfl 0 (by decide),rfl,rfl,?_⟩
  simp only [cycleFinalHp,cycleMidHp,deletedHp,mutatedHp,out,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,left,right,parent,MObj.elems_dyn,MObj.setElem]
  change ([true,true,false] : List Bool)≠[false,true,false]
  decide


/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.member_write_delete_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms member_write_delete_program

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.member_write_delete_timeout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms member_write_delete_timeout


private def k1 : PrimTy.uint.Denote := indexValue ⟨1,by decide⟩
private def oneWord : Val C Γ .uint := .simple (.lit 1 (by decide))
private def xrhs : Source.Idx XΓ SB := .there (.there srhs)
private def redirectInput := withArgs sy k1 true
private def redirectMid := withArgs reached k1 true
private def redirectHp := out.set right (MObj.setElem .dyn (out.get right) 1 false)
private def redirectSource : Source.EMState E XΓ :=
  (redirectMid.1,{redirectMid.2 with heap := redirectMid.2.heap.write 1 (sourceBoolMemory [false,false,false]) (by rfl)})
private def redirectMachine := writeMachine target 26 w[0]
private def redirectItems := sourceStructReferenceDelete layout xroot xrhs xi
private def redirectProg : Prog C Γ Γ :=
  .cons (.assignMem (.field (.var root (by decide)) "items" layout.child_type) (.ref (.var rhs rfl)))
    (.cons (.deleteMem (.loc (.index .dyn (fieldPath root) oneWord)) rfl) .nil)
private def redirectCode := structChildDeleteCode (C := C) 1 root "items" oneWord

private theorem clear_right_one {m : Machine} (hm : StateRepr 1 1 8 (Frag.init Γ) (σ.withHeap out) base m) :
    run redirectCode m=.ok (writeMachine m 26 w[0]) 0 := by
  let ptr := [.mload (cellOf 1 root)]++readFieldCode (fieldOffset (structDef S) "items")
  have hptrCert : PtrFrag 1 (fieldPath root) ptr := .field _ _ _ (.local root (by decide))
  have hpath : (fieldPath root).mvalT (σ.withHeap out)=.ok right := by
    simp only [fieldPath,MPath.mvalT,MLoc.addrT,Heap.readAddr,TRes.ofOpt,bind,Except.bind,pure,Except.pure]
    rfl
  have hptr := hptrCert.run_of_eval (hm.push w[0]) hpath
  have hk : 1<out.len right .dyn := by
    rw [out,arrayLen_setRefField]
    simp only [Heap.len,Heap.get,Objs.get,hp,right,MObj.elems_dyn,List.length_cons,List.length_nil]
    decide
  have hraw : run (writeArrayCode (base right.id)) ((m.push w[0]).push w[1])=.ok (writeMachine m 26 w[0]) 0 := by
    obtain ⟨_,_,hc,_⟩ | ⟨hn,_⟩ := writeArray_correct (hm.heap.arrays right) ⟨1,by decide⟩ false w[0] rfl
    · exact hc
    · have hw : out.writeAddr (.index right .dyn k1) false=some redirectHp := by
        simp only [Heap.writeAddr,Heap.setIndex,k1,indexValue,Int.toNat_natCast]
        exact if_pos hk
      change out.writeAddr (.index right .dyn k1) false=none at hn
      rw [hw] at hn;cases hn
  change run ((compileVal 1 (deleteDefaultValue .bool))++ptr++compileVal 1 oneWord++writeArrayStackCode) m=_
  rw [List.append_assoc,List.append_assoc,
    run_append_ok (show run (compileVal 1 (deleteDefaultValue .bool)) m=.ok (m.push w[0]) 0 from rfl),
    run_append_ok hptr,
    run_append_ok (show run (compileVal 1 oneWord) ((m.push w[0]).push (.val (base right.id)))=
      .ok (((m.push w[0]).push (.val (base right.id))).push w[1]) 0 from rfl)]
  rw [writeArrayStackCode,arrayStack_append_eq (m.push w[0]) (base right.id) ⟨1,by decide⟩ _
    (out.len_dyn_lt right) (hm.heap.arrays right).length,←writeArrayCode]
  exact hraw

/-- ONE actual Source RItems program changes selected identity LEFT→RIGHT,
then materially clears RIGHT[1]. Its old LEFT local remains independent. -/
theorem reference_then_delete_program (p : Roadmap.Pipeline) :
    (Source.execItems (G p) F0 7 XΓ.length none redirectItems redirectInput.1).run (.nil,redirectInput.2)=
      (.ok (.normal redirectSource.1),(.nil,redirectSource.2)) ∧
    Prog.run σ redirectProg=.ok ⟨σ.withHeap redirectHp,List.prefix_refl _⟩ ∧
    run (code++redirectCode) machine=.ok redirectMachine 0 ∧
    (Source.execS (G p) F0 6 XΓ.length none (.expr (sourceStructAssign layout xroot xrhs) : Source.RStmt E [] false .body XΓ XΓ) redirectInput.1).run (.nil,redirectInput.2)=
      (.ok (.normal redirectMid.1),(.nil,redirectMid.2)) ∧
    (Source.execS (G p) F0 5 XΓ.length none (.expr (sourceStructChildDelete layout xroot xi) : Source.RStmt E [] false .body XΓ XΓ) redirectMid.1).run (.nil,redirectMid.2)=
      (.ok (.normal redirectSource.1),(.nil,redirectSource.2)) ∧
    SourceBoolStructAt redirectSource 2 redirectHp parent addresses layout ∧ Source.MemOK E SH redirectSource ∧
    SourceBoolMemoryAt redirectSource 0 redirectHp left .dyn ∧
    StateRepr 1 1 8 (Frag.init Γ) (σ.withHeap redirectHp) base redirectMachine ∧
    [MObj.elems .dyn (hp.get left),MObj.elems .dyn (hp.get right),MObj.elems .dyn (out.get left),
      MObj.elems .dyn (out.get right),MObj.elems .dyn (redirectHp.get left),MObj.elems .dyn (redirectHp.get right)]=
      [[true,false,false],[false,true,false],[true,false,false],[false,true,false],[true,false,false],[false,false,false]] ∧
    [cells machine,cells target,cells redirectMachine]=
      [[w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[16]],
       [w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[24]],
       [w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[0],w[0],w[7],w[24]]] ∧
    [redirectInput.2.heap.get 0,redirectMid.2.heap.get 0,redirectSource.2.heap.get 0]=
      [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [true,false,false]⟩] ∧
    [redirectInput.2.heap.get 1,redirectMid.2.heap.get 1,redirectSource.2.heap.get 1]=
      [some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SB,sourceBoolMemory [false,false,false]⟩] ∧
    [redirectInput.2.heap.get 2,redirectMid.2.heap.get 2,redirectSource.2.heap.get 2]=[some ⟨SS,data 0⟩,some ⟨SS,data 1⟩,some ⟨SS,data 1⟩] ∧
    [(hp.field parent layout.child_type).id,(out.field parent layout.child_type).id,(redirectHp.field parent layout.child_type).id]=[0,1,1] ∧
    redirectSource.1.get (.there (.there soldAlias))=.memRef rfl 0 ∧
    (TEnv.get oldAlias (σ.withHeap redirectHp).env).map HRef.id=some 0 ∧
    redirectHp.field parent layout.tag_type=u7 ∧ redirectMachine.stack=[w[42]] ∧
    StructAllocatorRepr redirectHp base 8 ⟨48,by decide⟩ redirectMachine := by
  have hr : SourceBoolStructAt redirectInput 2 hp parent addresses layout := initial_at.same_heaps rfl rfl
  have hv : SourceBoolMemoryAt redirectInput 1 hp right .dyn := right_at
  have hk : k1.1.toNat<σ.heap.len right .dyn := by
    simp only [σ,Heap.len,Heap.get,Objs.get,hp,right,MObj.elems_dyn,k1,indexValue,Int.toNat_natCast,List.length_cons,List.length_nil]
    decide
  obtain ⟨ym,z,hout,mm,m',hw₁,hs₁,hs₂,hitems,hprog,hc₁,hc₂,hcode,hsel,hlen,hw₂,hr₁,hv₁,hr₂,hm₁,hm₂,hrepr₁,hrepr₂,hy₁,hy₂,htag,hselfinal,hread,hother,hsource,hstack,halloc⟩ :=
    hr.reference_delete_program layout (G p) F0 0 σ parent right addresses hv xroot xrhs xi root rhs (.lit 1 (by decide)) k1
      rfl rfl rfl rfl rfl rfl (by decide) hk SH (withArgs_memOK _ _ _ source_memOK) initial_repr rfl
  have hknown : (Source.writeLoc (E := E) (Γ := XΓ) F0 4 (.mem (τ := SB) 2 1) (.memRef rfl 1)).run redirectInput=(.ok (),redirectMid) := by
    obtain ⟨ht,hw⟩ := source_struct_write redirectInput 2 dn layout.source_types u7 0 1 hr.parent
    exact hw
  have hym : ym=redirectMid := congrArg Prod.snd (hw₁.symm.trans hknown)
  subst ym
  have hmm : mm=target := (Evm.Out.ok.inj (hc₁.symm.trans (redirected_views p).2.2.2.1)).1
  subst mm
  have ho : hout=redirectHp := Option.some.inj (hw₂.symm.trans (show out.writeAddr (.index right .dyn k1) false=some redirectHp from by
    simp only [Heap.writeAddr,Heap.setIndex]
    exact if_pos (by change k1.1.toNat<out.len right .dyn;rw [out,arrayLen_setRefField];exact hk)))
  subst hout
  obtain ⟨ht,hwrite⟩ := source_bool_write redirectMid 1 [false,true,false] rfl 1 (by decide) false
  have hdel : (Source.deleteLoc (E := E) (Γ := XΓ) F0 3 (τ := .bool) (.mem 1 1)).run redirectMid=(.ok (),redirectSource) := hwrite
  have he : (Source.evalE (G p) F0 4 (sourceStructChildDelete layout xroot xi)).run redirectMid=(.ok Source.RVal.unit,redirectSource) := by
    rw [sourceStructChildDelete,Source.evalE,Source.Hoare.run_bind,hr₁.eval_child_loc (G p) F0 0 xroot xi k1 rfl rfl (by rw [hsel,hlen];exact hk)]
    change (Source.deleteLoc F0 3 (τ := .bool) (.mem 1 1) >>= fun _ => pure Source.RVal.unit).run redirectMid=_
    rw [Source.Hoare.run_bind,hdel];rfl
  have hstmt := source_expr_statement_run (G p) F0 4 XΓ.length _ redirectMid redirectSource Source.RVal.unit he
  have hz : z=redirectSource := Prod.ext hy₂ (congrArg (fun x => x.2.2) (hs₂.symm.trans hstmt))
  subst z
  have htarg : m'=redirectMachine := (Evm.Out.ok.inj (hc₂.symm.trans (clear_right_one hrepr₁))).1
  subst m'
  have hold : SourceBoolMemoryAt redirectInput 0 hp left .dyn := left_at
  refine ⟨hitems,hprog,hcode,hs₁,hs₂,hr₂,hm₂,hsource left hold (by decide) (by decide),hrepr₂,?_,?_,rfl,rfl,rfl,?_,rfl,rfl,?_,hstack,halloc _ (by decide) initial_allocator⟩
  · simp only [redirectHp,out,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,left,right,parent,MObj.elems_dyn,MObj.setElem]
    rfl
  · rfl
  · simp only [Heap.field,hselfinal]
    rfl
  · exact htag


private def emptyHp : Heap H := runtimeHp [true,false,false] [] (by decide) (by decide)
private def emptyState := σ.withHeap emptyHp
private def emptyMachine := writeMachine machine 24 w[0]
private def emptySource := withArgs (runtimeSource [true,false,false] []) k0 true
private def emptyMidHp := emptyHp.setField parent layout.child_type right
private def emptyMidSource : Source.EMState E XΓ :=
  (emptySource.1,{emptySource.2 with heap := emptySource.2.heap.write 2 (data 1) (by rfl)})
private def emptyMidMachine := writeMachine emptyMachine 33 w[24]
private def emptyItems := sourceStructReferenceDelete layout xroot xrhs xi
private def emptyProg : Prog C Γ Γ :=
  .cons (.assignMem (.field (.var root (by decide)) "items" layout.child_type) (.ref (.var rhs rfl)))
    (.cons (.deleteMem (.loc (.index .dyn (fieldPath root) zeroWord)) rfl) .nil)
private theorem empty_left_repr : ArrayRepr emptyHp left (base left.id) emptyMachine := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Heap.len,Heap.get,Objs.get,emptyHp,runtimeHp,left,MObj.elems_dyn] using (show 16+1+3≤W from by decide)
  · simpa only [Heap.len,Heap.get,Objs.get,emptyHp,runtimeHp,left,MObj.elems_dyn] using (show emptyMachine.mem 16=.val (wmod 3) from rfl)
  · intro i v hi
    simp only [Heap.get,Objs.get,emptyHp,runtimeHp,left,MObj.elems_dyn] at hi
    cases i with
    | zero => cases Option.some.inj hi;rfl
    | succ i => cases i with
      | zero => cases Option.some.inj hi;rfl
      | succ i => cases i with
        | zero => cases Option.some.inj hi;rfl
        | succ i => cases hi
private theorem empty_right_repr : ArrayRepr emptyHp right (base right.id) emptyMachine := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Heap.len,Heap.get,Objs.get,emptyHp,runtimeHp,right,MObj.elems_dyn] using (show 24+1+0≤W from by decide)
  · simpa only [Heap.len,Heap.get,Objs.get,emptyHp,runtimeHp,right,MObj.elems_dyn] using (show emptyMachine.mem 24=.val (wmod 0) from rfl)
  · intro i v hi
    simp only [Heap.get,Objs.get,emptyHp,runtimeHp,right,MObj.elems_dyn,List.getElem?_nil] at hi
    cases hi
private theorem empty_parent_repr : StructRepr emptyHp parent (base parent.id) emptyMachine := by
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
private theorem empty_repr : StateRepr 1 1 8 (Frag.init Γ) emptyState base emptyMachine := by
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨?_,?_,?_,by decide,?_,?_,?_⟩
  · refine ⟨hc.store,?_,?_,hc.net,hc.netSelf,hc.bound,?_,hc.env,hc.funds,hc.oracle⟩
    all_goals intro p i;cases i with | there i => cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
  · refine ⟨?_,?_,?_⟩
    · intro p q;obtain ⟨rfl,hq|hq⟩ := prim_refs q <;> cases hq
      · exact empty_left_repr
      · exact empty_right_repr
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
    · intro s q;obtain ⟨rfl,hq⟩ := struct_refs q;cases hq;exact empty_parent_repr
    · intro s q;obtain ⟨rfl,hq⟩ := struct_refs q;cases hq;decide
    · intro s t q r hne
      obtain ⟨rfl,hq⟩ := struct_refs q;cases hq
      obtain ⟨rfl,hr⟩ := struct_refs r;cases hr
      exact (hne rfl).elim
  · intro p s q r
    obtain ⟨rfl,hq|hq⟩ := prim_refs q <;> cases hq
    all_goals obtain ⟨rfl,hr⟩ := struct_refs r;cases hr
    all_goals exact .inl (by simp only [Heap.len,Heap.get,Objs.get,emptyHp,runtimeHp,left,right,MObj.elems_dyn];decide)
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

private theorem empty_allocator : StructAllocatorRepr emptyHp base 8 ⟨48,by decide⟩ emptyMachine := by
  refine ⟨⟨empty_repr.heap,⟨by decide,by decide,rfl,?_⟩,?_⟩,empty_repr.structs,empty_repr.separated,?_⟩
  · intro addr ha
    change upd machine.mem 24 w[0] addr=w[0]
    rw [upd_other _ _ (by change 48≤addr at ha;omega)]
    exact initial_allocator.arrays.free.zero addr ha
  · intro p q
    obtain ⟨rfl,hq|hq⟩ := prim_refs q <;> cases hq
    all_goals simp only [Heap.len,Heap.get,Objs.get,emptyHp,runtimeHp,left,right,base,MObj.elems_dyn] <;> decide
  · intro s q
    obtain ⟨rfl,hq⟩ := struct_refs q;cases hq
    change 32+2≤48;decide

private theorem empty_source_at : SourceBoolStructAt emptySource 2 emptyHp parent addresses layout := by
  refine ⟨rfl,?_⟩
  unfold SourceBoolMemoryAt
  simp only [emptyHp,runtimeHp,Heap.get,Objs.get,left,MObj.elems_dyn]
  rfl
private theorem empty_source_right : SourceBoolMemoryAt emptySource 1 emptyHp right .dyn := by
  unfold SourceBoolMemoryAt
  simp only [emptyHp,runtimeHp,Heap.get,Objs.get,right,MObj.elems_dyn]
  rfl
private theorem empty_memOK : Source.MemOK E SH emptySource :=
  withArgs_memOK _ _ _ (runtime_memOK [true,false,false] [])

/-- Old LEFT[0] is valid and true, but new RIGHT is empty. The REAL first
reference replacement remains in the Source panic result, while Prog and whole
word append reject the NEW capacity. No target rollback/panic-data claim. -/
theorem reference_delete_new_capacity (p : Roadmap.Pipeline) :
    hp.index left .dyn k0=some true ∧
    emptyHp.index left .dyn k0=some true ∧ emptyHp.len right .dyn=0 ∧
    (Source.execItems (G p) F0 7 XΓ.length none emptyItems emptySource.1).run (.nil,emptySource.2)=
      (.error (.revert (Source.panicData .index)),(.nil,emptyMidSource.2)) ∧
    Prog.run emptyState emptyProg=.error .revert ∧
    run (code++structChildDeleteCode (C := C) 1 root "items" zeroWord) emptyMachine=.revert ∧
    run code emptyMachine=.ok emptyMidMachine 0 ∧
    SourceBoolStructAt emptyMidSource 2 emptyMidHp parent addresses layout ∧ Source.MemOK E SH emptyMidSource ∧
    StateRepr 1 1 8 (Frag.init Γ) (emptyState.withHeap emptyMidHp) base emptyMidMachine ∧
    [emptySource.2.heap.get 0,emptyMidSource.2.heap.get 0]=[some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [true,false,false]⟩] ∧
    [emptySource.2.heap.get 1,emptyMidSource.2.heap.get 1]=[some ⟨SB,sourceBoolMemory []⟩,some ⟨SB,sourceBoolMemory []⟩] ∧
    [emptySource.2.heap.get 2,emptyMidSource.2.heap.get 2]=[some ⟨SS,data 0⟩,some ⟨SS,data 1⟩] ∧
    [cells emptyMachine,cells emptyMidMachine]=
      [[w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[0],w[0],w[1],w[0],w[7],w[16]],
       [w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[0],w[0],w[1],w[0],w[7],w[24]]] ∧
    emptyMidSource.1.get (.there (.there soldAlias))=.memRef rfl 0 ∧
    emptyMidMachine.stack=[w[42]] ∧ emptyMidMachine.mem 0=w[48] ∧
    StructAllocatorRepr emptyMidHp base 8 ⟨48,by decide⟩ emptyMidMachine := by
  have hge : emptyState.heap.len right .dyn≤k0.1.toNat := by
    simp only [emptyState,State.withHeap,Heap.len,Heap.get,Objs.get,emptyHp,runtimeHp,right,MObj.elems_dyn,k0,indexValue,Int.toNat_natCast,List.length_nil]
    decide
  obtain ⟨ym,mm,hs,hitems,hprog,hc,hword,hr,hm,hrepr,hl,hsel,hlen,hn,hstack,halloc⟩ :=
    empty_source_at.reference_delete_reject layout (G p) F0 0 emptyState parent right addresses empty_source_right
      xroot xrhs xi root rhs (.lit 0 rfl) k0 rfl rfl rfl rfl rfl rfl (by decide) hge SH empty_memOK empty_repr rfl
  have hknown : (Source.writeLoc (E := E) (Γ := XΓ) F0 4 (.mem (τ := SB) 2 1) (.memRef rfl 1)).run emptySource=(.ok (),emptyMidSource) := by
    obtain ⟨ht,hw⟩ := source_struct_write emptySource 2 dn layout.source_types u7 0 1 empty_source_at.parent
    exact hw
  have href := empty_source_at.resolved_assign_word layout (G p) F0 2 emptyState parent right addresses empty_source_right
      xroot xrhs root rhs rfl rfl rfl rfl (by decide) SH empty_memOK empty_repr
  obtain ⟨ym',mm',hw',he',hs',hi',hc',hr',hm',hrep',hyl,hst,htarg,ha,tail⟩ := href
  have hym' : ym'=emptyMidSource := congrArg Prod.snd (hw'.symm.trans hknown)
  subst ym'
  have hmm' : mm'=emptyMidMachine := htarg
  subst mm'
  have hy : ym=emptyMidSource := Prod.ext hl (congrArg (fun x => x.2.2) (hs.symm.trans hs'))
  subst ym
  have hmmeq : mm=emptyMidMachine := (Evm.Out.ok.inj (hc.symm.trans hc')).1
  subst mm
  refine ⟨?_,?_,?_,hitems,hprog,hword,hc,hr,hm,hrepr,rfl,rfl,rfl,?_,rfl,hstack,rfl,halloc _ (by decide) empty_allocator⟩
  · simp only [Heap.index,Heap.get,Objs.get,hp,left,MObj.elems_dyn,k0,indexValue,Int.toNat_natCast];rfl
  · simp only [Heap.index,Heap.get,Objs.get,emptyHp,runtimeHp,left,MObj.elems_dyn,k0,indexValue,Int.toNat_natCast];rfl
  · simp only [Heap.len,Heap.get,Objs.get,emptyHp,runtimeHp,right,MObj.elems_dyn,List.length_nil]
  · rfl


/-- Insufficient Source horizon preserves the ACTUAL changed reference prefix.
The child has not been deleted; this is distinct from Source panic and from
successful final clearing, with no target-timeout/rollback equivalence. -/
theorem reference_delete_timeout (p : Roadmap.Pipeline) :
    (Source.execItems (G p) F0 6 XΓ.length none redirectItems redirectInput.1).run (.nil,redirectInput.2)=
      (.error .timeout,(.nil,redirectMid.2)) ∧
    (Source.execItems (G p) F0 0 XΓ.length none redirectItems redirectInput.1).run (.nil,redirectInput.2)=
      (.error .timeout,(.nil,redirectInput.2)) ∧
    redirectMid.2.heap.get 2=some ⟨SS,data 1⟩ ∧ redirectInput.2.heap.get 2=some ⟨SS,data 0⟩ ∧
    (Source.readLoc (E := E) (Γ := XΓ) F0 (τ := .bool) (.mem 1 1)).run redirectMid=(.ok (.bool true),redirectMid) ∧
    (Source.readLoc (E := E) (Γ := XΓ) F0 (τ := .bool) (.mem 1 1)).run redirectSource=(.ok (.bool false),redirectSource) ∧
    target.mem 26=w[1] ∧ redirectMachine.mem 26=w[0] ∧
    hp.index left .dyn k1=some false ∧ hp.index right .dyn k1=some true ∧
    MObj.elems .dyn ((out.set left (MObj.setElem .dyn (out.get left) 1 false)).get right)≠MObj.elems .dyn (redirectHp.get right) := by
  have hr : SourceBoolStructAt redirectInput 2 hp parent addresses layout := initial_at.same_heaps rfl rfl
  have hv : SourceBoolMemoryAt redirectInput 1 hp right .dyn := right_at
  obtain ⟨ym,mm,hw,he,hs,hi,hc,hr',hm,hrepr,hy,hstack,hmm,halloc,tail⟩ :=
    hr.resolved_assign_word layout (G p) F0 1 σ parent right addresses hv xroot xrhs root rhs
      rfl rfl rfl rfl (by decide) SH (withArgs_memOK _ _ _ source_memOK) initial_repr
  have hknown : (Source.writeLoc (E := E) (Γ := XΓ) F0 3 (.mem (τ := SB) 2 1) (.memRef rfl 1)).run redirectInput=(.ok (),redirectMid) := by
    obtain ⟨ht,hw⟩ := source_struct_write redirectInput 2 dn layout.source_types u7 0 1 hr.parent
    exact hw
  have hym : ym=redirectMid := congrArg Prod.snd (hw.symm.trans hknown)
  subst ym
  have hs₁ : (Source.execS (G p) F0 5 XΓ.length none (.expr (sourceStructAssign layout xroot xrhs) : Source.RStmt E [] false .body XΓ XΓ) redirectInput.1).run (.nil,redirectInput.2)=
      (.ok (.normal redirectMid.1),(.nil,redirectMid.2)) := hs
  have hb := source_struct_delete_low_horizon layout (G p) F0 redirectMid xroot xi 3 (by decide)
  have hs₂ := source_expr_statement_error (G p) F0 3 XΓ.length (sourceStructChildDelete layout xroot xi) redirectMid redirectMid .timeout hb
  have hitems := source_items_pair_error (G p) F0 0 XΓ.length (.expr (sourceStructAssign layout xroot xrhs))
    (.expr (sourceStructChildDelete layout xroot xi)) redirectInput redirectMid redirectMid .timeout hs₁ hs₂
  refine ⟨hitems,rfl,rfl,rfl,source_bool_read redirectMid 1 [false,true,false] rfl 1 (by decide),
    source_bool_read redirectSource 1 [false,false,false] rfl 1 (by decide),rfl,rfl,?_,?_,?_⟩
  · simp only [Heap.index,Heap.get,Objs.get,hp,left,MObj.elems_dyn,k1,indexValue,Int.toNat_natCast];rfl
  · simp only [Heap.index,Heap.get,Objs.get,hp,right,MObj.elems_dyn,k1,indexValue,Int.toNat_natCast];rfl
  · simp only [redirectHp,out,Heap.setField,Heap.get,Heap.set,Objs.get,Objs.set,hp,left,right,parent,MObj.elems_dyn,MObj.setElem]
    change ([false,true,false] : List Bool)≠[false,false,false]
    decide

/-- Nonempty exact end is separately rejected after successful reference
replacement. All complete preexisting endpoint/fuel vectors remain intact. -/
theorem reference_delete_exact_end (p : Roadmap.Pipeline) :
    ∃ (ym : Source.EMState E XΓ) (mm : Machine),
      (Source.execItems (G p) F0 7 XΓ.length none (sourceStructReferenceDelete layout xroot xrhs xi)
        (withArgs sy k3 true).1).run (.nil,sy.2)=(.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      Prog.run σ (.cons (.assignMem (.field (.var root (by decide)) "items" layout.child_type) (.ref (.var rhs rfl)))
        (.cons (.deleteMem (.loc (.index .dyn (fieldPath root) endpointWord)) rfl) .nil))=.error .revert ∧
      run (code++structChildDeleteCode (C := C) 1 root "items" endpointWord) machine=.revert ∧
      SourceBoolStructAt ym 2 out parent addresses layout ∧ Source.MemOK E SH ym ∧
      StateRepr 1 1 8 (Frag.init Γ) (σ.withHeap out) base mm ∧
      (out.field parent layout.child_type).id=1 ∧ out.len right .dyn=3 := by
  have hr : SourceBoolStructAt (withArgs sy k3 true) 2 hp parent addresses layout := initial_at.same_heaps rfl rfl
  have hv : SourceBoolMemoryAt (withArgs sy k3 true) 1 hp right .dyn := right_at
  have hk : σ.heap.len right .dyn≤k3.1.toNat := by
    simp only [σ,Heap.len,Heap.get,Objs.get,hp,right,MObj.elems_dyn,k3,indexValue,Int.toNat_natCast,List.length_cons,List.length_nil]
    decide
  obtain ⟨ym,mm,hs,hitems,hprog,hc,hword,hr',hm,hrepr,hy,hsel,hlen,hn,hstack,halloc⟩ :=
    hr.reference_delete_reject layout (G p) F0 0 σ parent right addresses hv xroot xrhs xi root rhs (.lit 3 (by decide)) k3
      rfl rfl rfl rfl rfl rfl (by decide) hk SH (withArgs_memOK _ _ _ source_memOK) initial_repr rfl
  refine ⟨ym,mm,hitems,hprog,hword,hr',hm,hrepr,?_,?_⟩
  · change ((σ.heap.setField parent layout.child_type right).field parent layout.child_type).id=1
    rw [hsel];rfl
  · change (σ.heap.setField parent layout.child_type right).len right .dyn=3
    rw [hlen]
    simp only [σ,Heap.len,Heap.get,Objs.get,hp,right,MObj.elems_dyn,List.length_cons,List.length_nil]


/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.reference_then_delete_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reference_then_delete_program

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.reference_delete_new_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reference_delete_new_capacity

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.reference_delete_timeout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reference_delete_timeout

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.reference_delete_exact_end' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reference_delete_exact_end

private def growthObject (xs : List Bool) (hx : xs.length<2^256) : MObj H B := ⟨xs,hx⟩
private def growthHeap (xs : List Bool) (hx : xs.length<2^256) := (hp.alloc (growthObject xs hx)).1
private def growthRef (xs : List Bool) (hx : xs.length<2^256) := (hp.alloc (growthObject xs hx)).2
private def growthRoot : HRef (H++[B]) (.struct S) := parent.wk (List.prefix_append H [B])
private def growthAddress := allocatedSourceAddress addresses H.length sy.2.heap.next
private def growthSource (xs : List Bool) : Source.EMState E SΓ :=
  (sy.1,{sy.2 with heap := (sy.2.heap.alloc ⟨SB,sourceBoolMemory xs⟩).1})

/-- Arbitrary valid runtime payload: real paired allocation preserves the named
parent, all represented old aliases and exact source tables; fresh reads derive. -/
theorem named_struct_alloc_views (p : Roadmap.Pipeline) (xs : List Bool) (hx : xs.length<2^256) :
    (Source.allocRef (E := E) (Γ := SΓ) (sourceBoolMemory xs)).run sy=
      (.ok (.memRef rfl 3),growthSource xs) ∧
    SourceBoolStructAt (growthSource xs) 2 (growthHeap xs hx) growthRoot growthAddress layout ∧
    SourceBoolMemoryAt (growthSource xs) 3 (growthHeap xs hx) (growthRef xs hx) .dyn ∧
    Source.MemOK E SH (growthSource xs) ∧
    (growthRef xs hx).id=3 ∧
    [growthAddress 0,growthAddress 1,growthAddress 2,growthAddress 3]=[0,1,2,3] ∧
    [MObj.elems .dyn ((growthHeap xs hx).get (left.wk (List.prefix_append H [B]))),
      MObj.elems .dyn ((growthHeap xs hx).get (right.wk (List.prefix_append H [B]))),
      MObj.elems .dyn ((growthHeap xs hx).get (growthRef xs hx))]=
      [[true,false,false],[false,true,false],xs] ∧
    [(growthSource xs).2.heap.get 0,(growthSource xs).2.heap.get 1,(growthSource xs).2.heap.get 2,(growthSource xs).2.heap.get 3]=
      [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,
        some ⟨SS,data 0⟩,some ⟨SB,sourceBoolMemory xs⟩] ∧
    (Source.evalE (G p) F0 2 (.member (.local sroot) 0 layout.source_tag_type)).run (growthSource xs)=
      (.ok (.val (sourceUint u7)),growthSource xs) ∧
    (Source.evalE (G p) F0 2 (.member (.local sroot) 1 layout.source_child_type)).run (growthSource xs)=
      (.ok (.val (.memRef rfl 0)),growthSource xs) ∧
    (∀ (k : PrimTy.uint.Denote) (v : Bool),(Source.readLoc (E := E) (Γ := SΓ) F0 (τ := .bool) (.mem 3 k.1.toNat)).run (growthSource xs)=
      (.ok (.bool v),growthSource xs) ↔ (growthHeap xs hx).index (growthRef xs hx) .dyn k=some v) := by
  obtain ⟨ha,hkeep,hr,hf,hm,hid,haddr,hold,hne,hpa,hca,halias,hlocal,heffects⟩ :=
    initial_at.alloc_bool (growthObject xs hx) SH source_memOK
  simp only [MObj.elems_dyn,growthObject] at ha hr hf hm
  have htag := hr.eval_member_tag (G p) F0 0 sroot (by rfl)
  have hchild := hr.eval_member_child (G p) F0 0 sroot (by rfl)
  refine ⟨ha,hr,hf,hm,rfl,rfl,?_,rfl,htag,hchild,?_⟩
  · change [MObj.elems .dyn ((hp.alloc (growthObject xs hx)).1.get (left.wk _)),
      MObj.elems .dyn ((hp.alloc (growthObject xs hx)).1.get (right.wk _)),
      MObj.elems .dyn ((hp.alloc (growthObject xs hx)).1.get (hp.alloc (growthObject xs hx)).2)]=_
    rw [hkeep left,hkeep right,hp.get_alloc (growthObject xs hx)]
    simp only [MObj.elems_wk,List.map_id'' (f := MVal.wk (List.prefix_append H [B]) (.prim .bool)) (fun _ => rfl),
      MObj.elems_dyn,growthObject,Heap.get,Objs.get,hp,left,right]
  · intro k v
    exact hf.read_iff F0 k v

private def growthInput := withArgs sy k1 true
private def allocatedInput : Source.EMState E XΓ :=
  (growthInput.1,(growthSource [false,true,true,true]).2)
private def allocatedSelectedHeap := (growthHeap [false,true,true,true] (by decide)).setField growthRoot layout.child_type (growthRef [false,true,true,true] (by decide))
private def allocatedSelectedSource : Source.EMState E XΓ :=
  (growthInput.1,{allocatedInput.2 with heap := allocatedInput.2.heap.write 2 (data 3) (by rfl)})
private def allocatedDeletedHeap := allocatedSelectedHeap.set (growthRef [false,true,true,true] (by decide)) ⟨[false,false,true,true],by decide⟩
private def allocatedDeletedSource : Source.EMState E XΓ :=
  (growthInput.1,{allocatedSelectedSource.2 with heap := allocatedSelectedSource.2.heap.write 3 (sourceBoolMemory [false,false,true,true]) (by rfl)})

/-- Real allocation then field replacement and reached member DELETE; fresh
length4 differs from old length3, and old aliases retain their independent data. -/
theorem allocated_reference_delete (p : Roadmap.Pipeline) :
    (Source.allocRef (E := E) (Γ := XΓ) (sourceBoolMemory [false,true,true,true])).run growthInput=
      (.ok (.memRef rfl 3),allocatedInput) ∧
    (Source.writeLoc (E := E) (Γ := XΓ) F0 0 (.mem (τ := SB) 2 1) (.memRef rfl 3)).run allocatedInput=
      (.ok (),allocatedSelectedSource) ∧
    (Source.evalE (G p) F0 4 (sourceStructChildDelete layout xroot xi)).run allocatedSelectedSource=
      (.ok Source.RVal.unit,allocatedDeletedSource) ∧
    allocatedSelectedHeap.writeAddr (.index (growthRef [false,true,true,true] (by decide)) .dyn k1) false=some allocatedDeletedHeap ∧
    SourceBoolStructAt allocatedInput 2 (growthHeap [false,true,true,true] (by decide)) growthRoot growthAddress layout ∧
    SourceBoolStructAt allocatedSelectedSource 2 allocatedSelectedHeap growthRoot growthAddress layout ∧
    SourceBoolStructAt allocatedDeletedSource 2 allocatedDeletedHeap growthRoot growthAddress layout ∧
    Source.MemOK E SH allocatedDeletedSource ∧
    [allocatedInput.2.heap.get 0,allocatedInput.2.heap.get 1,allocatedInput.2.heap.get 2,allocatedInput.2.heap.get 3,
      allocatedSelectedSource.2.heap.get 0,allocatedSelectedSource.2.heap.get 1,allocatedSelectedSource.2.heap.get 2,allocatedSelectedSource.2.heap.get 3,
      allocatedDeletedSource.2.heap.get 0,allocatedDeletedSource.2.heap.get 1,allocatedDeletedSource.2.heap.get 2,allocatedDeletedSource.2.heap.get 3]=
      [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 0⟩,some ⟨SB,sourceBoolMemory [false,true,true,true]⟩,
       some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 3⟩,some ⟨SB,sourceBoolMemory [false,true,true,true]⟩,
       some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 3⟩,some ⟨SB,sourceBoolMemory [false,false,true,true]⟩] ∧
    [MObj.elems .dyn ((growthHeap [false,true,true,true] (by decide)).get (growthRef [false,true,true,true] (by decide))),
      MObj.elems .dyn (allocatedSelectedHeap.get (growthRef [false,true,true,true] (by decide))),
      MObj.elems .dyn (allocatedDeletedHeap.get (growthRef [false,true,true,true] (by decide))),
      MObj.elems .dyn (allocatedDeletedHeap.get (left.wk (List.prefix_append H [B]))),
      MObj.elems .dyn (allocatedDeletedHeap.get (right.wk (List.prefix_append H [B])))]=
      [[false,true,true,true],[false,true,true,true],[false,false,true,true],[true,false,false],[false,true,false]] ∧
    (Source.evalE (G p) F0 3 (sourceStructChildRead layout xroot xi)).run allocatedSelectedSource=
      (.ok (.val (.bool true)),allocatedSelectedSource) ∧
    (Source.evalE (G p) F0 3 (sourceStructChildRead layout xroot xi)).run allocatedDeletedSource=
      (.ok (.val (.bool false)),allocatedDeletedSource) ∧
    allocatedDeletedSource.1.get (.there (.there soldAlias))=.memRef rfl 0 ∧
    allocatedDeletedHeap.field growthRoot layout.tag_type=u7 ∧
    (allocatedDeletedHeap.field growthRoot layout.child_type).id=3 := by
  have hr : SourceBoolStructAt growthInput 2 hp parent addresses layout := ⟨initial_at.parent,initial_at.leaf⟩
  have hmem : Source.MemOK E SH growthInput := (withArgs_memOK _ _ _ source_memOK)
  obtain ⟨z,w,v,out,ha,hw,hd,hwrite,hrz,hrw,hrv,hmz,hmw,hmv,hlw,hlv,hsel,hlen,hparent,halias⟩ :=
    hr.alloc_select_delete (growthObject [false,true,true,true] (by decide)) SH hmem (G p) F0 0 xroot xi k1 rfl rfl (by simp only [MObj.elems_dyn,growthObject,k1,indexValue,Int.toNat_natCast];decide)
  simp only [MObj.elems_dyn,growthObject] at ha hrz hrw hrv hmz hmw hmv
  have haz : (Source.allocRef (E := E) (Γ := XΓ) (sourceBoolMemory [false,true,true,true])).run growthInput=(.ok (.memRef rfl 3),allocatedInput) := rfl
  have hez : z=allocatedInput := congrArg Prod.snd (ha.symm.trans haz)
  subst z
  have hwc : (Source.writeLoc (E := E) (Γ := XΓ) F0 0 (.mem (τ := SB) 2 1) (.memRef rfl 3)).run allocatedInput=(.ok (),allocatedSelectedSource) := by
    obtain ⟨ht,hs⟩ := source_struct_write allocatedInput 2 dn layout.source_types u7 0 3 hrz.parent
    exact hs
  have hew : w=allocatedSelectedSource := congrArg Prod.snd (hw.symm.trans hwc)
  subst w
  have hg : allocatedSelectedHeap.get (growthRef [false,true,true,true] (by decide))=growthObject [false,true,true,true] (by decide) := by
    unfold allocatedSelectedHeap Heap.setField
    rw [Heap.get_set_ne _ _ _ (by decide)]
    change (hp.alloc (growthObject [false,true,true,true] (by decide))).1.get (hp.alloc (growthObject [false,true,true,true] (by decide))).2=_
    rw [hp.get_alloc]
    rfl
  have hwtarget : allocatedSelectedHeap.writeAddr (.index (growthRef [false,true,true,true] (by decide)) .dyn k1) false=some allocatedDeletedHeap := by
    simp only [Heap.writeAddr,Heap.setIndex,hg,MObj.elems_dyn,MObj.setElem_dyn,growthObject,k1,indexValue,Int.toNat_natCast]
    rfl
  have ho : out=allocatedDeletedHeap := Option.some.inj (hwrite.symm.trans hwtarget)
  subst out
  have hdc : (Source.evalE (G p) F0 4 (sourceStructChildDelete layout xroot xi)).run allocatedSelectedSource=(.ok Source.RVal.unit,allocatedDeletedSource) := by
    have hrw' : SourceBoolStructAt allocatedSelectedSource 2 allocatedSelectedHeap growthRoot growthAddress layout := hrw
    rw [sourceStructChildDelete,Source.evalE,Source.Hoare.run_bind,hrw'.eval_child_loc (G p) F0 0 xroot xi k1 rfl rfl (by simp only [Heap.len,MObj.elems_dyn];decide)]
    change (Source.deleteLoc F0 3 (τ := .bool) (.mem 3 k1.1.toNat) >>= fun _ => pure Source.RVal.unit).run allocatedSelectedSource=_
    obtain ⟨ht,hb⟩ := source_bool_write allocatedSelectedSource 3 [false,true,true,true] (by rfl) k1.1.toNat (by decide) false
    have hdel : (Source.deleteLoc (E := E) (Γ := XΓ) F0 3 (τ := .bool) (.mem 3 k1.1.toNat)).run allocatedSelectedSource=(.ok (),allocatedDeletedSource) := hb
    rw [Source.Hoare.run_bind,hdel]
    rfl
  have hev : v=allocatedDeletedSource := congrArg Prod.snd (hd.symm.trans hdc)
  subst v
  refine ⟨ha,hw,hd,hwrite,hrz,hrw,hrv,hmv,rfl,?_,?_,?_,rfl,rfl,rfl⟩
  · simp only [MObj.elems_dyn]
    rfl
  · exact hrw.eval_child_read (G p) F0 0 xroot xi k1 true rfl rfl (by simp only [Heap.index,MObj.elems_dyn];rfl)
  · exact hrv.eval_child_read (G p) F0 0 xroot xi k1 false rfl rfl (by simp only [Heap.index,MObj.elems_dyn];rfl)

/-- Empty allocation is inhabited, not a successful element read. Element32
is a logical element boundary only; exact-end33 rejects at the fresh Source cell. -/
theorem named_struct_alloc_boundaries (p : Roadmap.Pipeline) :
    SourceBoolStructAt (growthSource []) 2 (growthHeap [] (by decide)) growthRoot growthAddress layout ∧
    (Source.allocRef (E := E) (Γ := SΓ) (sourceBoolMemory [])).run sy=(.ok (.memRef rfl 3),growthSource []) ∧
    (Source.readLoc (E := E) (Γ := SΓ) F0 (τ := .bool) (.mem 3 0)).run (growthSource [])=
      (.error (.revert (Source.panicData .index)),growthSource []) ∧
    (growthHeap [] (by decide)).index (growthRef [] (by decide)) .dyn k0=none ∧
    SourceBoolStructAt (growthSource (List.replicate 32 false++[true])) 2
      (growthHeap (List.replicate 32 false++[true]) (by decide)) growthRoot growthAddress layout ∧
    (Source.readLoc (E := E) (Γ := SΓ) F0 (τ := .bool) (.mem 3 32)).run (growthSource (List.replicate 32 false++[true]))=
      (.ok (.bool true),growthSource (List.replicate 32 false++[true])) ∧
    (Source.readLoc (E := E) (Γ := SΓ) F0 (τ := .bool) (.mem 3 33)).run (growthSource (List.replicate 32 false++[true]))=
      (.error (.revert (Source.panicData .index)),growthSource (List.replicate 32 false++[true])) ∧
    [growthAddress 0,growthAddress 1,growthAddress 2,growthAddress 3]=[0,1,2,3] := by
  have he := named_struct_alloc_views p [] (by decide)
  have hb := named_struct_alloc_views p (List.replicate 32 false++[true]) (by decide)
  refine ⟨he.2.1,he.1,?_,?_,hb.2.1,?_,?_,rfl⟩
  · exact source_bool_bounds (growthSource []) 3 [] (by rfl) 0 (by decide)
  · simp only [Heap.index,MObj.elems_dyn]
    rfl
  · exact source_bool_read (growthSource (List.replicate 32 false++[true])) 3 _ (by rfl) 32 (by decide)
  · exact source_bool_bounds (growthSource (List.replicate 32 false++[true])) 3 _ (by rfl) 33 (by decide)

/-- Mapping the fresh ID onto occupied LEFT is false for the actual new data.
Allocation alone still selects LEFT; stale selection disagrees with fresh reads. -/
theorem named_struct_alloc_negatives (p : Roadmap.Pipeline) :
    growthAddress 3≠0 ∧
    ¬SourceBoolMemoryAt (growthSource [false,true,true,true]) 0
      (growthHeap [false,true,true,true] (by decide)) (growthRef [false,true,true,true] (by decide)) .dyn ∧
    (Source.readLoc (E := E) (Γ := SΓ) F0 (τ := .bool) (.mem 0 0)).run (growthSource [false,true,true,true])=
      (.ok (.bool true),growthSource [false,true,true,true]) ∧
    (Source.readLoc (E := E) (Γ := SΓ) F0 (τ := .bool) (.mem 3 0)).run (growthSource [false,true,true,true])=
      (.ok (.bool false),growthSource [false,true,true,true]) ∧
    (Source.evalE (G p) F0 2 (.member (.local sroot) 1 layout.source_child_type)).run (growthSource [false,true,true,true])=
      (.ok (.val (.memRef rfl 0)),growthSource [false,true,true,true]) ∧
    [parent.id,left.id,right.id,(growthRef [false,true,true,true] (by decide)).id]=[2,0,1,3] := by
  have h := named_struct_alloc_views p [false,true,true,true] (by decide)
  refine ⟨by decide,?_,?_,?_,h.2.2.2.2.2.2.2.2.2.1,rfl⟩
  · intro hbad
    have hb : (growthSource [false,true,true,true]).2.heap.get 0=some ⟨SB,sourceBoolMemory [false,true,true,true]⟩ := by
      unfold SourceBoolMemoryAt at hbad
      rw [MObj.elems_dyn] at hbad
      exact hbad
    have hf := source_bool_read (growthSource [false,true,true,true]) 0 [false,true,true,true] hb 0 (by decide)
    have ht := source_bool_read (growthSource [false,true,true,true]) 0 [true,false,false] (by rfl) 0 (by decide)
    rw [ht] at hf
    cases hf
  · exact source_bool_read (growthSource [false,true,true,true]) 0 [true,false,false] (by rfl) 0 (by decide)
  · exact source_bool_read (growthSource [false,true,true,true]) 3 [false,true,true,true] (by rfl) 0 (by decide)


private def grownDefaultState := σ.allocPush (defaultArray (H := H) .bool ⟨0,W_pos⟩)
private def grownDefaultBase := upd base H.length (⟨48,by decide⟩ : Fin W)
private def grownDefaultMachine := writeMachine (allocateMachine machine ⟨48,by decide⟩ ⟨0,W_pos⟩) (cell 5) w[48]

/-- Existing EMPTY-default allocator/compiler is actually applied in the
populated struct context, preserving the old observer and all16 old word cells
except the free pointer; new local/header, stack and allocator are explicit. -/
theorem named_struct_default_word (p : Roadmap.Pipeline) :
    ∃ z : Source.EMState E SΓ,
      (Source.zeroVal (E := E) (Γ := SΓ) 2 SB).run sy=(.ok (.memRef rfl 3),z) ∧
      (Source.allocRef (E := E) (Γ := SΓ) (sourceBoolMemory [])).run sy=(.ok (.memRef rfl 3),z) ∧
      TRun.declMem B none rfl σ=.ok ⟨grownDefaultState,List.prefix_append _ _⟩ ∧
      run (declareNewCode 1 (.lit 0 rfl : Simple C Γ .uint)) machine=.ok grownDefaultMachine 0 ∧
      SourceBoolStructAt z 2 grownDefaultState.heap growthRoot growthAddress layout ∧
      SourceBoolMemoryAt z 3 grownDefaultState.heap (σ.alloc (defaultArray .bool ⟨0,W_pos⟩)).2 .dyn ∧
      Source.MemOK E SH z ∧
      StateRepr 1 1 8 ((Frag.init Γ).push (.mem B) .ok) grownDefaultState grownDefaultBase grownDefaultMachine ∧
      StructAllocatorRepr grownDefaultState.heap grownDefaultBase 8 ⟨49,by decide⟩ grownDefaultMachine ∧
      grownDefaultMachine.stack=machine.stack ∧
      [cells machine,cells grownDefaultMachine]=
        [[w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[16]],
         [w[49],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[16]]] ∧
      [grownDefaultMachine.mem 5,grownDefaultMachine.mem 48,grownDefaultMachine.mem 49]=[w[48],w[0],w[0]] ∧
      [z.2.heap.get 0,z.2.heap.get 1,z.2.heap.get 2,z.2.heap.get 3]=
        [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 0⟩,some ⟨SB,sourceBoolMemory []⟩] ∧
      (Source.evalE (G p) F0 2 (.member (.local sroot) 1 layout.source_child_type)).run z=(.ok (.val (.memRef rfl 0)),z) ∧
      grownDefaultState.heap.field growthRoot layout.tag_type=u7 := by
  obtain ⟨z,hz,ha,hd,hc,hr,hfresh,hm,hword,halloc,hstack,hid⟩ := initial_at.default_word_growth σ parent addresses layout 0 SH source_memOK
    initial_repr initial_allocator (by decide) (by decide) (by decide)
  have hknown : z=growthSource [] := congrArg Prod.snd (ha.symm.trans (by rfl))
  subst z
  refine ⟨growthSource [],hz,ha,hd,hc,hr,hfresh,hm,hword,halloc,hstack,rfl,rfl,rfl,?_,rfl⟩
  exact hr.eval_member_child (G p) F0 0 sroot rfl

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.named_struct_alloc_views' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_struct_alloc_views

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.allocated_reference_delete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allocated_reference_delete

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.named_struct_alloc_boundaries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_struct_alloc_boundaries

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.named_struct_alloc_negatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_struct_alloc_negatives

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.named_struct_default_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_struct_default_word

private abbrev DΓ : Source.RCtx := SB::SΓ
private def declaredSource : Source.EMState E DΓ := (.cons (.memRef rfl 3) sy.1,(growthSource []).2)
private def boundSource : Source.EMState E DΓ :=
  (declaredSource.1,{declaredSource.2 with heap := declaredSource.2.heap.write 2 (data 3) (by rfl)})
private def boundHeap := grownDefaultState.heap.setField growthRoot layout.child_type
  (σ.alloc (defaultArray .bool ⟨0,W_pos⟩)).2
private def boundMachine := writeMachine grownDefaultMachine 33 w[48]
private def declaredCode : List Instr := declareNewCode 1 (.lit 0 rfl : Simple C Γ .uint)
private def boundCode : List Instr := structReferenceWriteCode 1 (.there root) .here "items"
private def declaredProgram : Prog C Γ (.mem B::Γ) :=
  .cons (.declMem B (.user "freshBool") none rfl rfl)
    (.cons (.assignMem (.field (.var (.there root) (by decide)) "items" layout.child_type) (.ref (.var .here rfl))) .nil)

/-- Actual context-changing declaration THEN reached assignment in Source
RItems, intrinsic Prog and full word append, with complete ordered observations. -/
theorem named_declare_assign_program (p : Roadmap.Pipeline) :
    (Source.execS (G p) F0 5 SΓ.length none (.declVar SB : Source.RStmt E [] false .body SΓ DΓ) sy.1).run (.nil,sy.2)=
      (.ok (.normal declaredSource.1),(.nil,declaredSource.2)) ∧
    (Source.evalE (G p) F0 3 (sourceStructAssign layout (.there sroot) .here)).run declaredSource=
      (.ok (.val (.memRef rfl 3)),boundSource) ∧
    (Source.execS (G p) F0 4 SΓ.length none (.expr (sourceStructAssign layout (.there sroot) .here) : Source.RStmt E [] false .body DΓ DΓ) declaredSource.1).run (.nil,declaredSource.2)=
      (.ok (.normal boundSource.1),(.nil,boundSource.2)) ∧
    (Source.execItems (G p) F0 6 SΓ.length none (sourceStructDeclareAssign layout sroot) sy.1).run (.nil,sy.2)=
      (.ok (.normal boundSource.1),(.nil,boundSource.2)) ∧
    Prog.run σ declaredProgram=.ok ⟨grownDefaultState.withHeap boundHeap,List.prefix_append _ _⟩ ∧
    run declaredCode machine=.ok grownDefaultMachine 0 ∧ run boundCode grownDefaultMachine=.ok boundMachine 0 ∧
    run (declaredCode++boundCode) machine=.ok boundMachine 0 ∧
    SourceBoolStructAt declaredSource 2 grownDefaultState.heap growthRoot growthAddress layout ∧
    SourceBoolStructAt boundSource 2 boundHeap growthRoot growthAddress layout ∧
    Source.MemOK E SH declaredSource ∧ Source.MemOK E SH boundSource ∧
    StateRepr 1 1 8 ((Frag.init Γ).push (.mem B) .ok) (grownDefaultState.withHeap boundHeap) grownDefaultBase boundMachine ∧
    StructAllocatorRepr boundHeap grownDefaultBase 8 ⟨49,by decide⟩ boundMachine ∧
    [sy.2.heap.get 0,sy.2.heap.get 1,sy.2.heap.get 2,sy.2.heap.get 3,
      declaredSource.2.heap.get 0,declaredSource.2.heap.get 1,declaredSource.2.heap.get 2,declaredSource.2.heap.get 3,
      boundSource.2.heap.get 0,boundSource.2.heap.get 1,boundSource.2.heap.get 2,boundSource.2.heap.get 3]=
      [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 0⟩,none,
       some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 0⟩,some ⟨SB,sourceBoolMemory []⟩,
       some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 3⟩,some ⟨SB,sourceBoolMemory []⟩] ∧
    [cells machine,cells grownDefaultMachine,cells boundMachine]=
      [[w[48],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[16]],
       [w[49],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[16]],
       [w[49],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[48]]] ∧
    [boundMachine.mem 5,boundMachine.mem 48,boundMachine.mem 49]=[w[48],w[0],w[0]] ∧
    (declaredSource.1.get .here,declaredSource.1.get (.there sroot),boundSource.1.get .here,
      boundSource.1.get (.there sroot),boundSource.1.get (.there soldAlias))=
      (.memRef rfl 3,.memRef rfl 2,.memRef rfl 3,.memRef rfl 2,.memRef rfl 0) ∧
    [(TEnv.get (.here : Idx (.mem B::Γ) (.mem B)) grownDefaultState.env).map HRef.id,
      (TEnv.get (.there root) grownDefaultState.env).map HRef.id,
      (TEnv.get (.there oldAlias) (grownDefaultState.withHeap boundHeap).env).map HRef.id]=[some 3,some 2,some 0] ∧
    boundHeap.field growthRoot layout.tag_type=u7 ∧ (boundHeap.field growthRoot layout.child_type).id=3 ∧
    SourceBoolMemoryAt boundSource 0 boundHeap (left.wk (List.prefix_append H [B])) .dyn ∧
    SourceBoolMemoryAt boundSource 1 boundHeap (right.wk (List.prefix_append H [B])) .dyn ∧
    [MObj.elems .dyn (boundHeap.get (left.wk (List.prefix_append H [B]))),
      MObj.elems .dyn (boundHeap.get (right.wk (List.prefix_append H [B]))),
      MObj.elems .dyn (boundHeap.get (σ.alloc (defaultArray .bool ⟨0,W_pos⟩)).2)]=[[true,false,false],[false,true,false],[]] ∧
    boundMachine.stack=[w[42]] ∧ boundSource.2.ex=sy.2.ex ∧ boundSource.2.logs=sy.2.logs := by
  obtain ⟨mid,z,m',hdecl,hw,he,hs,hitems,hd,hi,hcode,hc,happend,hrmid,hr,hm0,hm,hword,halloc,hsfresh,hsroot,hl,htr,htf,htag,hsel,hlen,halias,hstack,htarget,heffects⟩ :=
    SourceBoolStructAt.declare_assign_word layout (G p) F0 0 σ parent addresses initial_at sroot root rfl rfl (by decide) SH source_memOK
      initial_repr initial_allocator (by decide) (by decide) (by decide)
  have hdc : (Source.execS (G p) F0 5 SΓ.length none (.declVar SB : Source.RStmt E [] false .body SΓ DΓ) sy.1).run (.nil,sy.2)=
      (.ok (.normal declaredSource.1),(.nil,declaredSource.2)) :=
    source_decl_statement_run (G p) F0 4 SΓ.length sy (growthSource []) (.memRef rfl 3) (source_bool_default_run sy 2)
  have hmL : mid.1=declaredSource.1 := Source.Out.normal.inj (Except.ok.inj (congrArg Prod.fst (hdecl.symm.trans hdc)))
  have hmS : mid.2=declaredSource.2 := congrArg (fun a => a.2.2) (hdecl.symm.trans hdc)
  have hmid : mid=declaredSource := Prod.ext hmL hmS
  subst mid
  have hknown : (Source.writeLoc (E := E) (Γ := DΓ) F0 2 (.mem (τ := SB) 2 1) (.memRef rfl 3)).run declaredSource=(.ok (),boundSource) := by
    obtain ⟨ht,hw⟩ := source_struct_write declaredSource 2 dn layout.source_types u7 0 3 hrmid.parent
    exact hw
  have hz : z=boundSource := congrArg Prod.snd (hw.symm.trans hknown)
  subst z
  change m'=boundMachine at htarget
  subst m'
  refine ⟨hdecl,he,hs,hitems,hi,hcode,hc,happend,hrmid,hr,hm0,hm,hword,halloc,rfl,rfl,rfl,rfl,rfl,?_,?_,halias left left_at,halias right right_at,?_,hstack,heffects.1,heffects.2.2.1⟩
  · exact htag
  · change boundHeap.field growthRoot layout.child_type=(σ.alloc (defaultArray .bool ⟨0,W_pos⟩)).2 at hsel
    rw [hsel];rfl
  · simp only [MObj.elems_dyn]
    rfl

/-- Actual late timeout preserves the reached allocation, not the initial
heap. Earlier insufficient declaration fuel has a genuinely different result. -/
theorem named_declare_assign_timeouts (p : Roadmap.Pipeline) :
    (Source.execS (G p) F0 4 SΓ.length none (.declVar SB : Source.RStmt E [] false .body SΓ DΓ) sy.1).run (.nil,sy.2)=
      (.ok (.normal declaredSource.1),(.nil,declaredSource.2)) ∧
    (Source.execS (G p) F0 3 SΓ.length none (.expr (sourceStructAssign layout (.there sroot) .here) : Source.RStmt E [] false .body DΓ DΓ) declaredSource.1).run (.nil,declaredSource.2)=
      (.error .timeout,(.nil,declaredSource.2)) ∧
    (Source.execItems (G p) F0 5 SΓ.length none (sourceStructDeclareAssign layout sroot) sy.1).run (.nil,sy.2)=
      (.error .timeout,(.nil,declaredSource.2)) ∧
    (Source.execItems (G p) F0 3 SΓ.length none (sourceStructDeclareAssign layout sroot) sy.1).run (.nil,sy.2)=
      (.error .timeout,(.nil,sy.2)) ∧
    (Source.execItems (G p) F0 0 SΓ.length none (sourceStructDeclareAssign layout sroot) sy.1).run (.nil,sy.2)=
      (.error .timeout,(.nil,sy.2)) ∧
    [sy.2.heap.get 3,declaredSource.2.heap.get 3,boundSource.2.heap.get 3]=
      [none,some ⟨SB,sourceBoolMemory []⟩,some ⟨SB,sourceBoolMemory []⟩] ∧
    [sy.2.heap.get 2,declaredSource.2.heap.get 2,boundSource.2.heap.get 2]=
      [some ⟨SS,data 0⟩,some ⟨SS,data 0⟩,some ⟨SS,data 3⟩] ∧
    (Source.readLoc (E := E) (Γ := DΓ) F0 (τ := .bool) (.mem 3 0)).run boundSource=
      (.error (.revert (Source.panicData .index)),boundSource) ∧
    boundHeap.index (σ.alloc (defaultArray .bool ⟨0,W_pos⟩)).2 .dyn k0=none ∧
    [grownDefaultMachine.mem 33,boundMachine.mem 33]=[w[16],w[48]] := by
  have hs : (Source.execS (G p) F0 4 SΓ.length none (.declVar SB : Source.RStmt E [] false .body SΓ DΓ) sy.1).run (.nil,sy.2)=
      (.ok (.normal declaredSource.1),(.nil,declaredSource.2)) :=
    source_decl_statement_run (G p) F0 3 SΓ.length sy (growthSource []) (.memRef rfl 3) (source_bool_default_run sy 1)
  have he := source_struct_assign_low_horizon layout (G p) F0 declaredSource (.there sroot) .here 2 (by decide)
  have ht := source_expr_statement_error (G p) F0 2 SΓ.length _ declaredSource declaredSource .timeout he
  have hi := source_items_context_pair_error (G p) F0 2 SΓ.length (.declVar SB) (.expr (sourceStructAssign layout (.there sroot) .here))
    sy declaredSource declaredSource .timeout hs ht
  refine ⟨hs,ht,hi,?_,rfl,rfl,rfl,source_bool_bounds boundSource 3 [] (by rfl) 0 (by decide),?_,rfl⟩
  · have hd := source_bool_declaration_timeouts (G p) F0 sy 2 (by decide)
    rw [sourceStructDeclareAssign,Source.execItems,Source.Hoare.run_bind,hd]
  · simp only [Heap.index,MObj.elems_dyn]
    rfl

private def staleDeclaredHeap := grownDefaultState.heap.setField growthRoot layout.child_type (right.wk (List.prefix_append H [B]))
private def staleDeclaredSource : Source.EMState E DΓ :=
  (declaredSource.1,{declaredSource.2 with heap := declaredSource.2.heap.write 2 (data 1) (by rfl)})
private def staleDeclaredMachine := writeMachine grownDefaultMachine 33 w[24]

/-- The old RHS local is inhabited but wrong: it still denotes RIGHT1/base24,
where the new local denotes fresh3/base48. Actual wrong execution discriminates it. -/
theorem named_declare_stale_rhs (p : Roadmap.Pipeline) :
    (Source.evalE (G p) F0 3 (sourceStructAssign layout (.there sroot) (.there srhs))).run declaredSource=
      (.ok (.val (.memRef rfl 1)),staleDeclaredSource) ∧
    Stmt.run grownDefaultState (.assignMem (.field (.var (.there root) (by decide)) "items" layout.child_type) (.ref (.var (.there rhs) rfl)))=
      .ok ⟨grownDefaultState.withHeap staleDeclaredHeap,List.prefix_refl _⟩ ∧
    run (structReferenceWriteCode (Γ := .mem B::Γ) 1 (.there root) (.there rhs) "items") grownDefaultMachine=.ok staleDeclaredMachine 0 ∧
    (Source.evalE (G p) F0 2 (.member (.local (.there sroot)) 1 layout.source_child_type)).run staleDeclaredSource=
      (.ok (.val (.memRef rfl 1)),staleDeclaredSource) ∧
    (Source.evalE (G p) F0 2 (.member (.local (.there sroot)) 1 layout.source_child_type)).run boundSource=
      (.ok (.val (.memRef rfl 3)),boundSource) ∧
    [staleDeclaredSource.2.heap.get 0,staleDeclaredSource.2.heap.get 1,staleDeclaredSource.2.heap.get 2,staleDeclaredSource.2.heap.get 3]=
      [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SB,sourceBoolMemory [false,true,false]⟩,some ⟨SS,data 1⟩,some ⟨SB,sourceBoolMemory []⟩] ∧
    [cells grownDefaultMachine,cells staleDeclaredMachine,cells boundMachine]=
      [[w[49],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[16]],
       [w[49],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[24]],
       [w[49],w[32],w[16],w[24],w[32],w[99],w[3],w[1],w[0],w[0],w[3],w[0],w[1],w[0],w[7],w[48]]] ∧
    (declaredSource.1.get (.here : Source.Idx DΓ SB),declaredSource.1.get (.there srhs),staleDeclaredSource.1.get .here)=
      (.memRef rfl 3,.memRef rfl 1,.memRef rfl 3) ∧
    staleDeclaredMachine.stack=[w[42]] ∧ staleDeclaredMachine.mem 5=w[48] ∧
    staleDeclaredMachine.mem 33≠boundMachine.mem 33 := by
  obtain ⟨hdecl,heok,hsok,hitems,hiprog,hdeclcode,hbindcode,happend,hrmid,hrbound,hmmid,tail⟩ := named_declare_assign_program p
  obtain ⟨z0,hzero,hdecl0,hd,hcode0,hnew,hmemnew,hmword,ha,hstack0,hid⟩ :=
    source_bool_declaration_word (G p) F0 sy 0 SH source_memOK σ initial_repr initial_allocator (by decide) (by decide) (by decide)
  have hz0 : z0=growthSource [] := congrArg Prod.snd (hzero.symm.trans (source_bool_default_run sy 0))
  subst z0
  have hv : SourceBoolMemoryAt declaredSource 1 grownDefaultState.heap (right.wk (List.prefix_append H [B])) .dyn := by
    obtain ⟨hsa,hke,hst,hfr,hmk,hfi,had,hold,hne,hpa,hca,halias,tail⟩ :=
      initial_at.alloc_bool (defaultArray .bool ⟨0,W_pos⟩) SH source_memOK
    have hright := (halias right right_at).1
    simp only [MObj.elems_dyn,defaultArray,List.replicate_zero] at hright
    exact hright.recontext rfl
  obtain ⟨z,m',hw,he,hs,hi,hc,hr,hm,hrepr,hl,hstack,htarget,halloc,htag,hsel,hchildren,hsource,heffects⟩ :=
    SourceBoolStructAt.resolved_assign_word layout (G p) F0 0 grownDefaultState growthRoot (right.wk (List.prefix_append H [B])) growthAddress hrmid hv
      (.there sroot) (.there srhs) (.there root) (.there rhs) rfl rfl rfl rfl (by decide) SH hmmid hmword
  have hwc : (Source.writeLoc (E := E) (Γ := DΓ) F0 2 (.mem (τ := SB) 2 1) (.memRef rfl 1)).run declaredSource=(.ok (),staleDeclaredSource) := by
    obtain ⟨ht,hw⟩ := source_struct_write declaredSource 2 dn layout.source_types u7 0 1 hrmid.parent
    exact hw
  have hz : z=staleDeclaredSource := congrArg Prod.snd (hw.symm.trans hwc)
  subst z
  change m'=staleDeclaredMachine at htarget
  subst m'
  change SourceBoolStructAt staleDeclaredSource 2 staleDeclaredHeap growthRoot growthAddress layout at hr
  have hread := hr.eval_member_child (G p) F0 0 (.there sroot) rfl
  change staleDeclaredHeap.field growthRoot layout.child_type=right.wk (List.prefix_append H [B]) at hsel
  rw [hsel] at hread
  have hreadgood := hrbound.eval_member_child (G p) F0 0 (.there sroot) rfl
  refine ⟨he,hi,hc,hread,hreadgood,rfl,rfl,rfl,hstack,rfl,by decide⟩

/-- Bounds after the actual successful program: primitive Source read panics,
intrinsic indexing is None, and a real target read suffix reverts. These are
separate observation scopes; there is no successful suffix machine or rollback. -/
theorem named_declared_empty_bounds (p : Roadmap.Pipeline) :
    (Source.execItems (G p) F0 6 SΓ.length none (sourceStructDeclareAssign layout sroot) sy.1).run (.nil,sy.2)=
      (.ok (.normal boundSource.1),(.nil,boundSource.2)) ∧
    (Source.readLoc (E := E) (Γ := DΓ) F0 (τ := .bool) (.mem 3 0)).run boundSource=
      (.error (.revert (Source.panicData .index)),boundSource) ∧
    boundHeap.index (σ.alloc (defaultArray .bool ⟨0,W_pos⟩)).2 .dyn k0=none ∧
    run ((declaredCode++boundCode)++([.push w[0]]++readArrayCode ⟨48,by decide⟩)) machine=.revert ∧
    [boundMachine.mem 33,boundMachine.mem 48,boundMachine.mem 0]=[w[48],w[0],w[49]] := by
  obtain ⟨hdecl,he,hs,hitems,hi,hc0,hc1,hcode,tail⟩ := named_declare_assign_program p
  have ha := arrayAddr_run boundMachine ⟨48,by decide⟩ ⟨0,W_pos⟩ 0 W_pos (by rfl)
  have ha' : run (arrayAddrCode ⟨48,by decide⟩) (boundMachine.push w[0])=.revert := by
    simpa only [Fin.val_zero,Nat.lt_irrefl,↓reduceIte] using ha
  have hr : run (readArrayCode ⟨48,by decide⟩) (boundMachine.push w[0])=.revert := by
    rw [readArrayCode,run_append_revert ha']
  have hp : run [.push w[0]] boundMachine=.ok (boundMachine.push w[0]) 0 := by
    simp only [run,exec_cons_zero,Instr.step,Machine.next,Out.ok_bind,exec_nil]
    rfl
  refine ⟨hitems,source_bool_bounds boundSource 3 [] (by rfl) 0 (by decide),?_,?_,rfl⟩
  · simp only [Heap.index,MObj.elems_dyn]
    rfl
  · rw [run_append_ok hcode,run_append_ok hp]
    exact hr


/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.named_declare_assign_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_declare_assign_program

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.named_declare_assign_timeouts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_declare_assign_timeouts

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.named_declare_stale_rhs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_declare_stale_rhs

/-- info: 'Solidity.Backend.MemoryOps.SourceStructControls.named_declared_empty_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms named_declared_empty_bounds

end Solidity.Backend.MemoryOps.SourceStructControls
