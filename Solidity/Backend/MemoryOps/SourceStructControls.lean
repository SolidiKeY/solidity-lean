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

end Solidity.Backend.MemoryOps.SourceStructControls
