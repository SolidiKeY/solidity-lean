import Solidity.Backend.MemoryOps.SourceAlias
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceAliasControls
open Evm Evm.Memory
open Source.SemanticsExamples (E0 F0 s0)
private def C : Contract := {vars := []}
private abbrev B : RefTy := .array (.prim .bool)
private abbrev R : RefTy := .array (.ref B)
private abbrev H : HTy := [B,R,R]
private def child : HRef H B := ⟨0,rfl⟩
private def oldRoot : HRef H R := ⟨1,rfl⟩
private def newRoot : HRef H R := ⟨2,rfl⟩
private def hp : Heap H := (⟨[true,false,false],by decide⟩,(⟨[child],by decide⟩,(⟨[child,child],by decide⟩,())))
private abbrev Γ : Ctx := [.mem R,.mem R,.mem R]
private def σ : State C Γ := {storage := Storage.init C,H := H,heap := hp,env := (some newRoot,(some oldRoot,(some oldRoot,())))}
private def base (i : Nat) : Fin W := if i=0 then ⟨16,by decide⟩ else if i=1 then ⟨24,by decide⟩ else ⟨28,by decide⟩
private def machine : Machine := {Machine.init with stack := [w[42]],mem := fun a =>
  if a=0 then w[32] else if a=1 then w[24] else if a=2 then w[24] else if a=3 then w[28] else if a=5 then w[99]
  else if a=16 then w[3] else if a=17 then w[1] else if a=24 then w[1] else if a=25 then w[16]
  else if a=28 then w[2] else if a=29 then w[16] else if a=30 then w[16] else w[0]}
private theorem prim_refs {p : PrimTy} (q : HRef H (.array (.prim p))) : p=.bool ∧ HEq q child := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi;exact ⟨rfl,HEq.rfl⟩
  | succ i => cases i with
    | zero => cases hi
    | succ i => cases i with
      | zero => cases hi
      | succ i => cases hi
private theorem ref_refs {Q : RefTy} (q : HRef H (.array (.ref Q))) : Q=B ∧ (HEq q oldRoot ∨ HEq q newRoot) := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi
  | succ i => cases i with
    | zero => cases hi;exact ⟨rfl,.inl HEq.rfl⟩
    | succ i => cases i with
      | zero => cases hi;exact ⟨rfl,.inr HEq.rfl⟩
      | succ i => cases hi
private theorem no_struct {s : Name} (q : HRef H (.struct s)) : False := by
  rcases q with ⟨i,hi⟩
  cases i with
  | zero => cases hi
  | succ i => cases i with
    | zero => cases hi
    | succ i => cases i with
      | zero => cases hi
      | succ i => cases hi
private theorem child_repr : ArrayRepr hp child (base child.id) machine := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Heap.len,Heap.get,Objs.get,hp,child,oldRoot,newRoot,MObj.elems_dyn] using (show 16+1+3≤W from by decide)
  · simpa only [Heap.len,Heap.get,Objs.get,hp,child,oldRoot,newRoot,MObj.elems_dyn] using (show machine.mem 16=.val (wmod 3) from rfl)
  · intro i v hi
    simp only [Heap.get,Objs.get,hp,child,MObj.elems_dyn] at hi
    cases i with
    | zero => cases Option.some.inj hi;rfl
    | succ i => cases i with
      | zero => cases Option.some.inj hi;rfl
      | succ i => cases i with
        | zero => cases Option.some.inj hi;rfl
        | succ i => cases hi
private theorem old_repr : RefArrayRepr hp oldRoot base machine := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Heap.len,Heap.get,Objs.get,hp,child,oldRoot,newRoot,MObj.elems_dyn] using (show 24+1+1≤W from by decide)
  · simpa only [Heap.len,Heap.get,Objs.get,hp,child,oldRoot,newRoot,MObj.elems_dyn] using (show machine.mem 24=.val (wmod 1) from rfl)
  · intro i v hi
    simp only [Heap.get,Objs.get,hp,oldRoot,MObj.elems_dyn] at hi
    cases i with
    | zero => cases Option.some.inj hi;rfl
    | succ i => cases hi
private theorem new_repr : RefArrayRepr hp newRoot base machine := by
  refine ⟨?_,?_,?_⟩
  · simpa only [Heap.len,Heap.get,Objs.get,hp,child,oldRoot,newRoot,MObj.elems_dyn] using (show 28+1+2≤W from by decide)
  · simpa only [Heap.len,Heap.get,Objs.get,hp,child,oldRoot,newRoot,MObj.elems_dyn] using (show machine.mem 28=.val (wmod 2) from rfl)
  · intro i v hi
    simp only [Heap.get,Objs.get,hp,newRoot,MObj.elems_dyn] at hi
    cases i with
    | zero => cases Option.some.inj hi;rfl
    | succ i => cases i with
      | zero => cases Option.some.inj hi;rfl
      | succ i => cases hi
private theorem initial_state : StateRepr 1 1 8 (Frag.init Γ) σ base machine := by
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨?_,?_,?_,by decide,?_,?_,RefFieldsRepr.withoutStructs _ _ _ (fun q => no_struct q)⟩
  · refine ⟨hc.store,?_,?_,hc.net,hc.netSelf,hc.bound,?_,hc.env,hc.funds,hc.oracle⟩
    all_goals intro p i;cases i with | there i => cases i with | there i => cases i with | there i => nomatch i
  · refine ⟨?_,?_,?_⟩
    · intro p q;obtain ⟨rfl,hq⟩ := prim_refs q;cases hq;exact child_repr
    · intro p q;obtain ⟨rfl,hq⟩ := prim_refs q;cases hq;exact show 8≤16 from by decide
    · intro p t q z hne
      obtain ⟨rfl,hq⟩ := prim_refs q;cases hq
      obtain ⟨rfl,hz⟩ := prim_refs z;cases hz
      exact (hne rfl).elim
  · intro Q i
    cases i with
    | here => exact ⟨newRoot,rfl,rfl⟩
    | there i => cases i with
      | here => exact ⟨oldRoot,rfl,rfl⟩
      | there i => cases i with
        | here => exact ⟨oldRoot,rfl,rfl⟩
        | there i => nomatch i
  · exact ⟨fun q => (no_struct q).elim,fun q => (no_struct q).elim,fun q _ _ => (no_struct q).elim⟩
  · intro p s arr q;exact (no_struct q).elim
private theorem initial_refs : RefArrayHeapRepr hp base 8 machine := by
  constructor
  · intro Q q;obtain ⟨rfl,hq|hq⟩ := ref_refs q <;> cases hq
    · exact old_repr
    · exact new_repr
  · intro Q q;obtain ⟨rfl,hq|hq⟩ := ref_refs q <;> cases hq
    · exact show 8≤24 from by decide
    · exact show 8≤28 from by decide
  · intro Q T q t hne
    obtain ⟨rfl,hq|hq⟩ := ref_refs q <;> cases hq
    · obtain ⟨rfl,ht|ht⟩ := ref_refs t <;> cases ht
      · exact (hne rfl).elim
      · left;simpa only [Heap.len,Heap.get,Objs.get,hp,child,oldRoot,newRoot,MObj.elems_dyn] using (show 24+1+1≤28 from by decide)
    · obtain ⟨rfl,ht|ht⟩ := ref_refs t <;> cases ht
      · right;simpa only [Heap.len,Heap.get,Objs.get,hp,child,oldRoot,newRoot,MObj.elems_dyn] using (show 24+1+1≤28 from by decide)
      · exact (hne rfl).elim
  · intro Q p q t
    obtain ⟨rfl,ht⟩ := prim_refs t;cases ht
    obtain ⟨rfl,hq|hq⟩ := ref_refs q <;> cases hq
    · right;simpa only [Heap.len,Heap.get,Objs.get,hp,child,oldRoot,newRoot,MObj.elems_dyn] using (show 16+1+3≤24 from by decide)
    · right;simpa only [Heap.len,Heap.get,Objs.get,hp,child,oldRoot,newRoot,MObj.elems_dyn] using (show 16+1+3≤28 from by decide)
  · intro Q s q t;exact (no_struct t).elim
private theorem initial_repr : RefArrayStateRepr 1 1 8 (Frag.init Γ) σ base machine := ⟨initial_state,initial_refs⟩

private abbrev SB : Source.STy := .array .memory .bool none
private abbrev SR : Source.STy := .array .memory SB none
private abbrev SΓ : Source.RCtx := [SR,SR,SR]
private def rootData (n : Nat) : Source.Data E0.layout SR :=
  .array n (fun _ h => by cases h) (fun _ => .val (.memRef rfl 0))
private def y0 : Source.EMState E0 [] := (.nil,s0)
private def yChild : Source.EMState E0 [] := ((Source.allocRef (sourceBoolMemory [true,false,false])).run y0).2
private def yOld : Source.EMState E0 [] := ((Source.allocRef (rootData 1)).run yChild).2
private def yNew : Source.EMState E0 [] := ((Source.allocRef (rootData 2)).run yOld).2
private def sy : Source.EMState E0 SΓ := (.cons (.memRef rfl 2) (.cons (.memRef rfl 1) (.cons (.memRef rfl 1) .nil)),yNew.2)
private abbrev SH : Source.HeapTy := (Source.Heap.empty (D := E0.layout)).ty
private theorem child_memOK : Source.MemOK E0 SH yChild := by
  have hm : Source.MemOK E0 SH y0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have h := source_bool_alloc_memOK (E := E0) (Γ := []) SH [true,false,false] y0 hm
  have he : (Source.allocRef (E := E0) (Γ := []) (sourceBoolMemory [true,false,false])).run y0=(.ok (.memRef rfl 0),yChild) := rfl
  rw [he] at h;exact h.1
private theorem old_memOK : Source.MemOK E0 SH yOld := by
  have h := Source.allocRef_mem' (E := E0) (Γ := []) (H := SH) (rootData 1) (by trivial)
    (by intro j;exact ⟨.memRef rfl 0,rfl⟩) yChild
    ⟨child_memOK,.array (fun _ => .val ⟨SB,rfl,rfl⟩)⟩
  have he : (Source.allocRef (E := E0) (Γ := []) (rootData 1)).run yChild=(.ok (.memRef rfl 1),yOld) := rfl
  rw [he] at h;exact h.1
private theorem new_memOK : Source.MemOK E0 SH yNew := by
  have h := Source.allocRef_mem' (E := E0) (Γ := []) (H := SH) (rootData 2) (by trivial)
    (by intro j;exact ⟨.memRef rfl 0,rfl⟩) yOld
    ⟨old_memOK,.array (fun _ => .val ⟨SB,rfl,rfl⟩)⟩
  have he : (Source.allocRef (E := E0) (Γ := []) (rootData 2)).run yOld=(.ok (.memRef rfl 2),yNew) := rfl
  rw [he] at h;exact h.1
private theorem source_memOK : Source.MemOK E0 SH sy := by
  refine ⟨⟨new_memOK.1.1,?_⟩,new_memOK.2⟩
  exact ⟨⟨SR,rfl,rfl⟩,⟨⟨SR,rfl,rfl⟩,⟨⟨SR,rfl,rfl⟩,trivial⟩⟩⟩
private theorem initial_child : SourceBoolMemoryAt sy 0 hp child .dyn := by
  unfold SourceBoolMemoryAt
  simp only [Heap.get,Objs.get,hp,child,MObj.elems_dyn]
  rfl


private theorem initial_allocator : StructAllocatorRepr σ.heap base 8 ⟨32,by decide⟩ machine := by
  apply AllocatorRepr.withoutStructs _ (fun q => no_struct q)
  refine ⟨initial_state.heap,?_,?_⟩
  · refine ⟨by decide,by decide,rfl,?_⟩
    intro addr ha
    change 32≤addr at ha
    change (if addr=0 then w[32] else if addr=1 then w[24] else if addr=2 then w[24] else if addr=3 then w[28] else if addr=5 then w[99]
      else if addr=16 then w[3] else if addr=17 then w[1] else if addr=24 then w[1] else if addr=25 then w[16]
      else if addr=28 then w[2] else if addr=29 then w[16] else if addr=30 then w[16] else w[0])=w[0]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),
      if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  · intro p q
    obtain ⟨rfl,hq⟩ := prim_refs q;cases hq
    simpa only [σ,Heap.len,Heap.get,Objs.get,hp,child,MObj.elems_dyn] using (show 16+1+3≤32 from by decide)

private def aliasSource : Source.EMState E0 SΓ := (sy.1.set (.there .here) (.memRef rfl 2),sy.2)
private def aliasState := σ.setLocal (.there .here) (some newRoot)
private def aliasMachine := writeMachine machine 2 w[28]
private def term : Source.RExpr E0 SΓ SR := sourceLocalAlias (.there .here) .here
private def code : List Instr := aliasLocalCode 1 (.there .here : Idx Γ (.mem R)) .here
private def cells (m : Machine) : List Word := [m.mem 0,m.mem 1,m.mem 2,m.mem 3,m.mem 5,m.mem 16,m.mem 17,m.mem 18,m.mem 19,m.mem 24,m.mem 25,m.mem 28,m.mem 29,m.mem 30]

/-- Nonprimitive alias rebinding changes the selected parent and pointer,
retaining the old alias, both parent objects and all shared child contents. -/
theorem nested_alias_views (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 term).run sy=(.ok (.val (.memRef rfl 2)),aliasSource) ∧
    (Source.execS (Source.SemanticsExamples.G0 p) F0 3 SΓ.length none
      (.expr term : Source.RStmt E0 [] false .body SΓ SΓ) sy.1).run (.nil,sy.2)=
        (.ok (.normal aliasSource.1),(.nil,aliasSource.2)) ∧
    Stmt.run σ (.rebindMem (.there .here) (.alias (.var .here rfl)))=.ok ⟨aliasState,List.prefix_refl _⟩ ∧
    run code machine=.ok aliasMachine 0 ∧ Source.MemOK E0 SH aliasSource ∧
    RefArrayStateRepr 1 1 8 (Frag.init Γ) aliasState base aliasMachine ∧
    aliasSource.2.heap=sy.2.heap ∧ aliasState.heap=hp ∧
    [sy.1.get (.there .here),sy.1.get .here,sy.1.get (.there (.there .here)),
      aliasSource.1.get (.there .here),aliasSource.1.get .here,aliasSource.1.get (.there (.there .here))]=
        [.memRef rfl 1,.memRef rfl 2,.memRef rfl 1,.memRef rfl 2,.memRef rfl 2,.memRef rfl 1] ∧
    [(TEnv.get (.there .here) σ.env).map HRef.id,(TEnv.get .here σ.env).map HRef.id,
      (TEnv.get (.there (.there .here)) σ.env).map HRef.id,(TEnv.get (.there .here) aliasState.env).map HRef.id,
      (TEnv.get .here aliasState.env).map HRef.id,(TEnv.get (.there (.there .here)) aliasState.env).map HRef.id]=
        [some 1,some 2,some 1,some 2,some 2,some 1] ∧
    [(MObj.elems .dyn (hp.get oldRoot)).map HRef.id,(MObj.elems .dyn (hp.get newRoot)).map HRef.id,
      (MObj.elems (H := aliasState.H) .dyn (aliasState.heap.get oldRoot)).map HRef.id,
      (MObj.elems (H := aliasState.H) .dyn (aliasState.heap.get newRoot)).map HRef.id]=[[0],[0,0],[0],[0,0]] ∧
    [MObj.elems .dyn (hp.get child),MObj.elems (H := aliasState.H) .dyn (aliasState.heap.get child)]=
      [[true,false,false],[true,false,false]] ∧
    [cells machine,cells aliasMachine]=
      [[w[32],w[24],w[24],w[28],w[99],w[3],w[1],w[0],w[0],w[1],w[16],w[2],w[16],w[16]],
       [w[32],w[24],w[28],w[28],w[99],w[3],w[1],w[0],w[0],w[1],w[16],w[2],w[16],w[16]]] ∧
    [aliasSource.2.heap.get 0,aliasSource.2.heap.get 1,aliasSource.2.heap.get 2]=
      [some ⟨SB,sourceBoolMemory [true,false,false]⟩,some ⟨SR,rootData 1⟩,some ⟨SR,rootData 2⟩] ∧
    (Source.lengthOf (E := E0) (Γ := SΓ) F0 (.memRef rfl 2 : Source.Val E0.layout SR)).run aliasSource=(.ok 2,aliasSource) ∧
    (Source.lengthOf (E := E0) (Γ := SΓ) F0 (.memRef rfl 1 : Source.Val E0.layout SR)).run aliasSource=(.ok 1,aliasSource) ∧
    (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := SB) (.mem 2 1)).run aliasSource=(.ok (.memRef rfl 0),aliasSource) ∧
    (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := .bool) (.mem 0 0)).run aliasSource=(.ok (.bool true),aliasSource) ∧
    (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := .bool) (.mem 0 1)).run aliasSource=(.ok (.bool false),aliasSource) ∧
    aliasSource.2.heap.next=3 ∧ aliasState.H.length=3 ∧ aliasMachine.stack=[w[42]] ∧ aliasMachine.mem 2≠w[24] ∧ StructAllocatorRepr aliasState.heap base 8 ⟨32,by decide⟩ aliasMachine := by
  obtain ⟨he,hs,hi,hc,hm,hsh,hth,hlocal,htlocal,hr,hstack,ha⟩ :=
    source_alias_word (Source.SemanticsExamples.G0 p) F0 0 sy (.there .here) .here rfl 2 rfl
      SH source_memOK σ (.there .here) .here newRoot rfl rfl initial_repr
  have h0 : aliasSource.2.heap.get 0=some ⟨SB,sourceBoolMemory [true,false,false]⟩ := by
    have hc := initial_child
    unfold SourceBoolMemoryAt at hc
    simpa only [Heap.get,Objs.get,hp,child,MObj.elems_dyn] using hc
  have h1 : aliasSource.2.heap.get 1=some ⟨SR,rootData 1⟩ := rfl
  have h2 : aliasSource.2.heap.get 2=some ⟨SR,rootData 2⟩ := rfl
  refine ⟨he,hs,hi,hc,hm,hr,rfl,rfl,rfl,rfl,?_,?_,rfl,?_,?_,?_,?_,
    source_bool_read aliasSource 0 _ h0 0 (by decide),source_bool_read aliasSource 0 _ h0 1 (by decide),rfl,rfl,hstack,?_,ha ⟨32,by decide⟩ (by decide) initial_allocator⟩
  · simp only [aliasState,State.setLocal,σ,Heap.get,Objs.get,hp,oldRoot,newRoot,MObj.elems_dyn,List.map_cons,List.map_nil]
    rfl
  · simp only [aliasState,State.setLocal,σ,Heap.get,Objs.get,hp,child,MObj.elems_dyn]
  · rw [h0,h1,h2]
  · simp only [Source.lengthOf,Source.Hoare.run_bind]
    rw [source_heapObj_run aliasSource 2 _ h2]
    rfl
  · simp only [Source.lengthOf,Source.Hoare.run_bind]
    rw [source_heapObj_run aliasSource 1 _ h1]
    rfl
  · change (Source.memElem (E := E0) (Γ := SΓ) 2 1 SB).run aliasSource=_
    rw [Source.memElem,Source.Hoare.run_bind,source_heapObj_run aliasSource 2 _ h2]
    rfl
  · change w[28]≠w[24]
    decide

/-- Self-aliasing is supported, not excluded by a distinctness premise. Small
Source horizons time out without any claim about target gas or allocation. -/
theorem self_alias_and_horizons (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 2 (sourceLocalAlias (.here : Source.Idx SΓ SR) .here)).run sy=
      (.ok (.val (.memRef rfl 2)),sy) ∧
    Stmt.run σ (.rebindMem (.here : Idx Γ (.mem R)) (.alias (.var .here rfl)))=.ok ⟨σ,List.prefix_refl _⟩ ∧
    run (aliasLocalCode 1 (.here : Idx Γ (.mem R)) .here) machine=.ok machine 0 ∧
    (∀ n, n≤1 → (Source.evalE (Source.SemanticsExamples.G0 p) F0 n term).run sy=(.error .timeout,sy)) := by
  obtain ⟨he,hs,hi,hc,hm,hsh,hth,hlocal,htlocal,hr,hstack,ha⟩ :=
    source_alias_word (Source.SemanticsExamples.G0 p) F0 0 sy .here .here rfl 2 rfl
      SH source_memOK σ .here .here newRoot rfl rfl initial_repr
  have hmem : upd machine.mem 3 w[28]=machine.mem := by
    funext a
    by_cases h : a=3
    · subst a;rw [upd_same];rfl
    · rw [upd_other _ _ h]
  have heq : writeMachine machine 3 w[28]=machine := congrArg (fun mem => {machine with mem := mem}) hmem
  refine ⟨he,hi,?_,source_local_alias_low_horizon (Source.SemanticsExamples.G0 p) F0 sy (.there .here) .here⟩
  have hc' : run (aliasLocalCode 1 (.here : Idx Γ (.mem R)) .here) machine=.ok (writeMachine machine 3 w[28]) 0 := hc
  rw [heq] at hc'
  exact hc'

/-- info: 'Solidity.Backend.MemoryOps.SourceAliasControls.nested_alias_views' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms nested_alias_views
/-- info: 'Solidity.Backend.MemoryOps.SourceAliasControls.self_alias_and_horizons' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms self_alias_and_horizons

end Solidity.Backend.MemoryOps.SourceAliasControls
