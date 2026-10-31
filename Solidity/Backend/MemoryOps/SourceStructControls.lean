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

end Solidity.Backend.MemoryOps.SourceStructControls
