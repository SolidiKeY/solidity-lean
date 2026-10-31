import Solidity.Backend.MemoryOps.SourceSequence
import Solidity.Backend.MemoryOps.SourceAssignment
import Solidity.Backend.MemoryOps.SourceDeclaration
import Solidity.Backend.MemoryOps.SourceIndexedDelete
import Solidity.Backend.MemoryOps.SourceDeleteTarget
import Solidity.Backend.MemoryOps.SourceDefault
import Solidity.Evm.Correct
import Solidity.Source.SemanticsExamples

namespace Solidity.Backend.MemoryOps.SourceTargetControls
open Evm Evm.Memory
open Source.SemanticsExamples (E0 F0 s0)
private def C : Contract := {vars := []}
private abbrev B : RefTy := .array (.prim .bool)
private abbrev H : HTy := [B]
private abbrev Γ : Ctx := [.mem B]
private def r : HRef H B := ⟨0,rfl⟩
private def hp : Heap H := (⟨[true,false,false],by decide⟩,())
private def σ : State C Γ := {storage := Storage.init C,H := H,heap := hp,env := (some r,())}
private def base : Nat → Fin W := fun _ => ⟨16,by decide⟩
private def machine : Machine := {Machine.init with stack := [w[42]],mem := fun a =>
  if a=0 then w[20] else if a=1 then w[16] else if a=5 then w[99] else
  if a=16 then w[3] else if a=17 then w[1] else w[0]}
private theorem id_zero {R : RefTy} (q : HRef H R) : q.id=0 := by
  have h := q.id_lt
  change q.id<1 at h
  omega
private theorem no_struct {s : Name} (q : HRef H (.struct s)) : False := by
  have h := (HRef.heq_of_id q r (id_zero q)).1
  cases h
private theorem array_repr : ArrayRepr hp r (base r.id) machine := by
  refine ⟨?_,?_,?_⟩
  · change 16+1+hp.len r .dyn≤W
    simp only [Heap.len,Heap.get,Objs.get,hp,r,MObj.elems_dyn]
    decide
  · change machine.mem 16=.val (wmod (hp.len r .dyn))
    simp only [Heap.len,Heap.get,Objs.get,hp,r,MObj.elems_dyn]
    rfl
  · intro i v hi
    simp only [Heap.get,Objs.get,hp,r,MObj.elems_dyn] at hi
    cases i with
    | zero => cases Option.some.inj hi; rfl
    | succ i =>
      cases i with
      | zero => cases Option.some.inj hi; rfl
      | succ i =>
        cases i with
        | zero => cases Option.some.inj hi; rfl
        | succ i =>
          cases hi
private theorem initial_repr : StateRepr 1 1 8 (Frag.init Γ) σ base machine := by
  have hc := Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨?_,?_,?_,by decide,?_,?_,RefFieldsRepr.withoutStructs _ _ _ (fun q => no_struct q)⟩
  · refine ⟨hc.store,?_,?_,hc.net,hc.netSelf,hc.bound,?_,hc.env,hc.funds,hc.oracle⟩
    · intro p i; cases i with | there i => nomatch i
    · intro R i hi; cases i with | there i => nomatch i
    · intro R i hi; cases i with | there i => nomatch i
  · constructor
    · intro p q
      obtain ⟨ht,hq⟩ := HRef.heq_of_id q r (id_zero q)
      have hp : p=.bool := Ty.prim.inj (RefTy.array.inj ht)
      cases hp
      cases eq_of_heq hq
      exact array_repr
    · intro p q; exact show 8≤16 from by decide
    · intro p q rr ss hne
      exact (hne ((id_zero rr).trans (id_zero ss).symm)).elim
  · intro R i
    cases i with
    | here => exact ⟨r,rfl,rfl⟩
    | there i => nomatch i
  · exact ⟨fun q => (no_struct q).elim,fun q => (no_struct q).elim,fun q _ _ => (no_struct q).elim⟩
  · intro p s arr q
    exact (no_struct q).elim

private def zero : Val C Γ .uint := .simple (.lit 0 rfl)
private def code : List Instr := deleteLocalCode 1 (.here : Idx Γ (.mem B)) (compileVal 1 zero)
private theorem code_run (m : Machine) (hptr : m.mem 1=w[16]) (hlen : m.mem 16=w[3]) : run code m=.ok (writeMachine m 17 w[0]) 0 := by
  have hz : compileVal 1 zero=[.push w[0]] := by
    simp only [zero,compileVal,compileSimple,toWord,Int.le_refl,↓reduceIte,Int.toNat_zero]
    rw [wmod_of_lt W_pos]
  rw [code,deleteLocalCode,writeLocalValueCode,hz]
  rw [List.append_assoc,List.append_assoc]
  change run ([.push w[0]] ++ ([.mload 1] ++ ([.push w[0]] ++ writeArrayStackCode))) m=_
  rw [run_append_ok (show run [.push w[0]] m=.ok (m.push w[0]) 0 from rfl)]
  rw [run_append_ok (show run [.mload 1] (m.push w[0])=
    .ok ((m.push w[0]).push w[16]) 0 from by
      change Out.ok ((m.push w[0]).push (m.mem 1)) 0=_
      rw [hptr])]
  rw [run_append_ok (show run [.push w[0]] ((m.push w[0]).push w[16])=
    .ok (((m.push w[0]).push w[16]).push w[0]) 0 from rfl)]
  have ha := arrayAddrStack_run (m.push w[0]) ⟨16,by decide⟩ ⟨0,W_pos⟩ 3 (by decide) (by simpa only [Machine.push,wmod_of_lt (by decide : 3<W)] using hlen)
  rw [if_pos (by decide : (0 : Nat)<3)] at ha
  rw [writeArrayStackCode,run_append_ok ha]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt (by decide : 17<W),
    Out.ok_bind,exec_nil,writeMachine]
private def y0 : Source.EMState E0 [] := (.nil,s0)
private def sy : Source.EMState E0 [] := ((Source.allocRef (sourceBoolMemory [true,false,false])).run y0).2
private theorem represented : SourceBoolMemoryAt sy 0 hp r .dyn := by
  unfold SourceBoolMemoryAt
  simp only [Heap.get,Objs.get,hp,r,MObj.elems_dyn]
  rfl

private abbrev SH : Source.HeapTy := (Source.Heap.empty (D := E0.layout)).ty
private theorem source_memOK : Source.MemOK E0 SH sy := by
  have h0 : Source.MemOK E0 SH y0 :=
    ⟨⟨⟨Source.HeapOK.empty,Source.HeapTy.Le.refl _⟩,trivial⟩,Source.HeapShaped.empty,Source.HeapInner.empty⟩
  have h := source_bool_alloc_memOK (E := E0) (Γ := []) SH [true,false,false] y0 h0
  have hz : (Source.allocRef (sourceBoolMemory [true,false,false])).run y0=(.ok (.memRef rfl 0),sy) := rfl
  rw [hz] at h
  exact h.1

/-- Apply the general independent-source/word-target theorem to actual inhabited
initial representations; all observed values and preserved frame cells are fixed. -/
theorem delete_three_views :
    ∃ (out : Heap H) (z : Source.EMState E0 []),
      σ.heap.writeAddr (.index r .dyn (uintOfNat 0)) (PrimTy.dflt .bool)=some out ∧
      (Source.deleteLoc (E := E0) (Γ := []) F0 1 (τ := .bool) (.mem 0 0)).run sy=(.ok (),z) ∧
      run code machine=.ok (writeMachine machine 17 w[0]) 0 ∧
      StateRepr 1 1 8 (Frag.init Γ) (σ.withHeap out) base (writeMachine machine 17 w[0]) ∧
      SourceBoolMemoryAt z 0 out r .dyn ∧
      [MObj.elems .dyn (hp.get r),MObj.elems .dyn (out.get r)]=[[true,false,false],[false,false,false]] ∧
      [machine.mem 0,machine.mem 1,machine.mem 5,machine.mem 16,machine.mem 17,machine.mem 18,machine.mem 19]=
        [w[20],w[16],w[99],w[3],w[1],w[0],w[0]] ∧
      [(writeMachine machine 17 w[0]).mem 0,(writeMachine machine 17 w[0]).mem 1,
       (writeMachine machine 17 w[0]).mem 5,(writeMachine machine 17 w[0]).mem 16,
       (writeMachine machine 17 w[0]).mem 17,(writeMachine machine 17 w[0]).mem 18,
       (writeMachine machine 17 w[0]).mem 19]=[w[20],w[16],w[99],w[3],w[0],w[0],w[0]] ∧
      (writeMachine machine 17 w[0]).stack=[w[42]] ∧
      (Source.readLoc (E := E0) (Γ := []) F0 (τ := .bool) (.mem 0 0)).run sy=(.ok (.bool true),sy) ∧
      (Source.readLoc (E := E0) (Γ := []) F0 (τ := .bool) (.mem 0 0)).run z=(.ok (.bool false),z) ∧
      (writeMachine machine 17 w[0]).mem 17≠w[1] ∧ Source.MemOK E0 SH sy ∧ Source.MemOK E0 SH z := by
  have hk : (uintOfNat 0).1.toNat<σ.heap.len r .dyn := by
    simp only [σ,Heap.len,Heap.get,Objs.get,hp,r,MObj.elems_dyn]
    decide
  obtain ⟨out,z,target,hw,hintr,hs,ht,hr,hrep,hstack,halloc⟩ :=
    source_delete_word_target σ r represented F0 0 .here rfl zero (uintOfNat 0) rfl hk initial_repr rfl
  have he : target=writeMachine machine 17 w[0] := by
    have he := (code_run machine rfl rfl).symm.trans ht
    cases he
    rfl
  subst target
  have hv : MObj.elems .dyn (out.get r)=[false,false,false] := by
    change hp.setIndex r .dyn (uintOfNat 0) false=some out at hw
    simp only [Heap.setIndex] at hw
    have hk' : (uintOfNat 0).1.toNat<(MObj.elems .dyn (hp.get r)).length := hk
    rw [if_pos hk'] at hw
    rw [←Option.some.inj hw,Heap.get_set_same,MObj.elems_setElem]
    simp only [Heap.get,Objs.get,hp,r,MObj.elems_dyn]
    rfl
  refine ⟨out,z,hw,hs,code_run machine rfl rfl,hrep,hr,?_,rfl,rfl,rfl,?_,?_,?_⟩
  · rw [hv]
    simp only [Heap.get,Objs.get,hp,r,MObj.elems_dyn]
  · exact source_bool_read sy 0 [true,false,false] rfl 0 (by decide)
  · have hh : z.2.heap.get 0=some ⟨.array .memory .bool none,sourceBoolMemory [false,false,false]⟩ := by rw [←hv];exact hr
    exact source_bool_read z 0 _ hh 0 (by decide)
  · refine ⟨by decide,source_memOK,?_⟩
    exact source_bool_delete_memOK sy z SH source_memOK F0 1 0 0 hs

private def endpoint : Val C Γ .uint := .simple (.lit 3 (by decide))

theorem delete_word_endpoint :
    (Source.deleteLoc (E := E0) (Γ := []) F0 1 (τ := .bool) (.mem 0 3)).run sy=
      (.error (.revert (Source.panicData .index)),sy) ∧
      run (deleteLocalCode 1 (.here : Idx Γ (.mem B)) (compileVal 1 endpoint)) machine=.revert ∧
      (Source.deleteLoc (E := E0) (Γ := []) F0 0 (τ := .bool) (.mem 0 3)).run sy=(.error .timeout,sy) := by
  have hk : σ.heap.len r .dyn≤(uintOfNat 3).1.toNat := by
    simp only [σ,Heap.len,Heap.get,Objs.get,hp,r,MObj.elems_dyn]
    decide
  have h := source_delete_word_bounds σ r represented F0 0 .here rfl endpoint (uintOfNat 3) rfl hk initial_repr rfl
  exact ⟨h.1,h.2,source_bool_delete_timeout sy F0 0 3⟩

private theorem cons_eq {α : Type} {a b : α} {xs ys : List α}
    (ha : a=b) (hs : xs=ys) : a::xs=b::ys := by
  cases ha
  cases hs
  rfl
private theorem initial_allocator : StructAllocatorRepr σ.heap base 8 ⟨20,by decide⟩ machine := by
  apply AllocatorRepr.withoutStructs _ (fun q => no_struct q)
  refine ⟨initial_repr.heap,?_,?_⟩
  · refine ⟨by decide,by decide,rfl,?_⟩
    intro addr ha
    change 20≤addr at ha
    change (if addr=0 then w[20] else if addr=1 then w[16] else if addr=5 then w[99] else
      if addr=16 then w[3] else if addr=17 then w[1] else w[0])=w[0]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  · intro p q
    obtain ⟨ht,hq⟩ := HRef.heq_of_id q r (id_zero q)
    have hp : p=.bool := Ty.prim.inj (RefTy.array.inj ht)
    cases hp
    cases eq_of_heq hq
    simp only [σ,base,Heap.len,Heap.get,Objs.get,hp,r,MObj.elems_dyn]
    decide
private def ctorObj : MObj H B := defaultArray .bool ⟨0,W_pos⟩
private def ctorState := σ.allocPush ctorObj
private def ctorRef := (σ.alloc ctorObj).2
private def ctorBase := upd base H.length (⟨20,by decide⟩ : Fin W)
private def ctorMachine := writeMachine (allocateMachine machine ⟨20,by decide⟩ ⟨0,W_pos⟩) 2 w[20]
private def ctorCode := declareNewCode 1 (.lit 0 rfl : Simple C Γ .uint)

/-- Actual Source constructor, Heap.allocDefault, intrinsic default declaration
and published emitted allocator share their observed empty fresh root. -/
theorem default_constructor_views :
    ∃ z : Source.EMState E0 [],
      (Source.zeroVal (E := E0) (Γ := []) 2 (.array .memory .bool none)).run sy=(.ok (.memRef rfl 1),z) ∧
      TRun.declMem B none rfl σ=.ok ⟨ctorState,List.prefix_append _ _⟩ ∧
      run ctorCode machine=.ok ctorMachine 0 ∧
      StateRepr 1 1 8 ((Frag.init Γ).push (.mem B) .ok) ctorState ctorBase ctorMachine ∧
      StructAllocatorRepr ctorState.heap ctorBase 8 ⟨21,by decide⟩ ctorMachine ∧
      SourceBoolMemoryAt z 1 ctorState.heap ctorRef .dyn ∧
      [MObj.elems .dyn (hp.get r),MObj.elems (H := ctorState.H) .dyn (ctorState.heap.get (r.wk (List.prefix_append H [B]))),
        MObj.elems (H := ctorState.H) .dyn (ctorState.heap.get ctorRef)]=[[true,false,false],[true,false,false],[]] ∧
      [sy.2.heap.get 0,z.2.heap.get 0,z.2.heap.get 1]=
        [some ⟨.array .memory .bool none,sourceBoolMemory [true,false,false]⟩,
         some ⟨.array .memory .bool none,sourceBoolMemory [true,false,false]⟩,
         some ⟨.array .memory .bool none,sourceBoolMemory []⟩] ∧
      [ctorMachine.mem 0,ctorMachine.mem 1,ctorMachine.mem 2,ctorMachine.mem 5,
       ctorMachine.mem 16,ctorMachine.mem 17,ctorMachine.mem 18,ctorMachine.mem 19,ctorMachine.mem 20]=
        [w[21],w[16],w[20],w[99],w[3],w[1],w[0],w[0],w[0]] ∧
      ctorMachine.stack=[w[42]] ∧ ctorRef.id=1 ∧ r.id=0 ∧
      Source.MemOK E0 SH z ∧
      (Source.readLoc (E := E0) (Γ := []) F0 (τ := .bool) (.mem 1 0)).run z=
        (.error (.revert (Source.panicData .index)),z) ∧
      (let g := hp.allocDefault B rfl
       SourceBoolMemoryAt z 1 g.heap g.val .dyn ∧
       SourceBoolMemoryAt z 0 g.heap (r.wk g.ext) .dyn ∧g.val.id≠(r.wk g.ext).id) := by
  obtain ⟨z,hs,hd,hcode,hr,hrep,ha,hstack,hid⟩ := source_bool_default_word sy 0 σ initial_repr initial_allocator
    (by decide) (by decide) (by decide)
  have hsource : (Source.zeroVal (E := E0) (Γ := []) 2 (.array .memory .bool none)).run sy=(.ok (.memRef rfl 1),z) := hs
  have hvnew : MObj.elems .dyn (ctorState.heap.get ctorRef)=[] := by
    change MObj.elems .dyn ((σ.allocPush ctorObj).heap.get (σ.alloc ctorObj).2)=[]
    rw [State.allocPush_get,MObj.elems_wk,MObj.elems_dyn]
    simp only [ctorObj,defaultArray,List.replicate_zero,List.map_nil]
  have hvold : MObj.elems .dyn (ctorState.heap.get (r.wk (List.prefix_append H [B])))=[true,false,false] := by
    change MObj.elems .dyn ((hp.alloc ctorObj).1.get (r.wk (List.prefix_append H [B])))=_
    rw [Heap.keeps_alloc hp ctorObj r,MObj.elems_wk,MObj.elems_dyn]
    rfl
  have hsz : z=(sy.1,{sy.2 with heap := (sy.2.heap.alloc ⟨.array .memory .bool none,sourceBoolMemory []⟩).1}) := by
    have he := hsource.symm.trans (source_bool_default_run sy 0)
    exact congrArg Prod.snd he
  have hm := source_bool_default_memOK (E := E0) (Γ := []) SH 0 sy source_memOK
  rw [hsource] at hm
  have hroot := source_bool_default_intrinsic sy hp 0
  have hframe := represented.default_frame 0
  rw [hsource] at hroot hframe
  refine ⟨z,hsource,hd,hcode,hrep,ha,hr,?_,?_,?_,hstack,hid,rfl,hm.1,?_,hroot.1,hframe.1,hframe.2.2.1⟩
  · have h0 : MObj.elems .dyn (hp.get r)=[true,false,false] := by
      simp only [Heap.get,Objs.get,hp,r,MObj.elems_dyn]
    exact cons_eq h0 (cons_eq hvold (congrArg (fun xs : List Bool => [xs]) hvnew))
  · have h0 : sy.2.heap.get 0=some ⟨.array .memory .bool none,sourceBoolMemory [true,false,false]⟩ := rfl
    have hmid : z.2.heap.get 0=some ⟨.array .memory .bool none,sourceBoolMemory [true,false,false]⟩ := by
      rw [hsz]
      change (sy.2.heap.alloc ⟨.array .memory .bool none,sourceBoolMemory []⟩).1.get 0=some _
      exact (Source.Heap.alloc_other sy.2.heap ⟨.array .memory .bool none,sourceBoolMemory []⟩
        (a := 0) (by decide : 0≠1)).trans h0
    have hnew : z.2.heap.get 1=some ⟨.array .memory .bool none,sourceBoolMemory []⟩ := by
      have he : z.2.heap.get 1=some ⟨.array .memory .bool none,
        sourceBoolMemory (MObj.elems .dyn (ctorState.heap.get ctorRef))⟩ := hr
      exact he.trans (congrArg (fun xs : List Bool => (some ⟨Source.STy.array .memory .bool none,
        sourceBoolMemory (D := E0.layout) xs⟩ : Option (Σ τ, Source.Data E0.layout τ))) hvnew)
    exact cons_eq h0 (cons_eq hmid (congrArg (fun x => [x]) hnew))
  · simp only [ctorMachine,allocateMachine]
    rw [wmod_of_lt (by decide : 21<W)]
    rfl
  · have he : z.2.heap.get 1=some ⟨.array .memory .bool none,sourceBoolMemory []⟩ := by rw [←hvnew];exact hr
    exact source_bool_bounds z 1 [] he 0 (Nat.le_refl _)

private def limit : Fin W := ⟨W-1,by have h := W_pos;omega⟩
private def fullMachine : Machine := writeMachine machine 0 (.val limit)

/-- Preserve both real source timeout cases and a concrete word-cursor wrap.
The latter is symbolic allocator behavior, not a physical EVM failure claim. -/
theorem constructor_boundaries :
    ∃ z : Source.EMState E0 [],
      (Source.zeroVal (E := E0) (Γ := []) 2 (.array .memory .bool none)).run sy=(.ok (.memRef rfl 1),z) ∧
      (Source.zeroVal (E := E0) (Γ := []) 0 (.array .memory .bool none)).run sy=(.error .timeout,sy) ∧
      (Source.zeroVal (E := E0) (Γ := []) 1 (.array .memory .bool none)).run sy=(.error .timeout,sy) ∧
      run allocateArrayCode (fullMachine.push w[0])=
        .ok ((allocateMachine fullMachine limit ⟨0,W_pos⟩).push (.val limit)) 0 ∧
      (allocateMachine fullMachine limit ⟨0,W_pos⟩).mem 0=w[0] ∧
      ¬FreeMemory 8 ⟨0,W_pos⟩ (allocateMachine fullMachine limit ⟨0,W_pos⟩) := by
  obtain ⟨z,hs,_⟩ := default_constructor_views
  have hl : limit.val+1=W := by
    change W-1+1=W
    exact Nat.sub_add_cancel (by have h := W_pos;omega)
  have hc : fullMachine.mem 0=.val limit := by
    simp only [fullMachine,writeMachine,upd_same]
  have hw := word_empty_allocator_wrap fullMachine limit hc hl
  have hlow := source_bool_default_lowfuel sy
  exact ⟨z,hs,hlow.1,hlow.2,hw.1,hw.2.1,hw.2.2 8 (by decide)⟩

/-- info: 'Solidity.Backend.MemoryOps.SourceTargetControls.default_constructor_views' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms default_constructor_views
/-- info: 'Solidity.Backend.MemoryOps.SourceTargetControls.constructor_boundaries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms constructor_boundaries


/-- info: 'Solidity.Backend.MemoryOps.SourceTargetControls.delete_three_views' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms delete_three_views
/-- info: 'Solidity.Backend.MemoryOps.SourceTargetControls.delete_word_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms delete_word_endpoint

private abbrev SΓ : Source.RCtx := [.int .u256,.array .memory .bool none,.array .memory .bool none]
private def indexedSource (k : PrimTy.uint.Denote) : Source.EMState E0 SΓ :=
  (.cons (sourceUint k) (.cons (.memRef rfl 0) (.cons (.memRef rfl 0) .nil)),sy.2)
private def indexedState (k : PrimTy.uint.Denote) := σ.push (t := .val .uint) k
private def indexedMachine (k : Nat) := writeMachine machine 2 (.val (wmod k))
private abbrev sroot : Source.Idx SΓ (.array .memory .bool none) := .there .here
private abbrev sindex : Source.Idx SΓ (.int .u256) := .here
private def term : Source.RExpr E0 SΓ (.tuple []) := sourceIndexedDelete sroot sindex
private theorem indexed_memOK (k : PrimTy.uint.Denote) : Source.MemOK E0 SH (indexedSource k) := by
  refine ⟨⟨source_memOK.1.1,?_⟩,source_memOK.2⟩
  exact ⟨trivial,⟨⟨_,rfl,rfl⟩,⟨⟨_,rfl,rfl⟩,trivial⟩⟩⟩
private theorem indexed_repr : StateRepr 1 1 8 ((Frag.init Γ).push (.val .uint) .ok)
    (indexedState (uintOfNat 0)) base (indexedMachine 0) := by
  exact initial_repr.consVal (uintOfNat 0) w[0] (ReprV.uint_of rfl) (by decide)

private def indexedCode : List Instr := deleteLocalCode 1 (.there .here : Idx [.val .uint,.mem B] (.mem B))
  (compileVal 1 (.simple (.local .here) : Val C [.val .uint,.mem B] .uint))
private theorem indexed_code_run (m : Machine) (hptr : m.mem 1=w[16]) (hindex : m.mem 2=w[0])
    (hlen : m.mem 16=w[3]) : run indexedCode m=.ok (writeMachine m 17 w[0]) 0 := by
  change run ([.push w[0]] ++ ([.mload 1] ++ ([.mload 2] ++ writeArrayStackCode))) m=_
  rw [run_append_ok (show run [.push w[0]] m=.ok (m.push w[0]) 0 from rfl)]
  rw [run_append_ok (show run [.mload 1] (m.push w[0])=
    .ok ((m.push w[0]).push w[16]) 0 from by
      change Out.ok ((m.push w[0]).push (m.mem 1)) 0=_
      rw [hptr])]
  rw [run_append_ok (show run [.mload 2] ((m.push w[0]).push w[16])=
    .ok (((m.push w[0]).push w[16]).push w[0]) 0 from by
      change Out.ok (((m.push w[0]).push w[16]).push (m.mem 2)) 0=_
      rw [hindex])]
  have ha := arrayAddrStack_run (m.push w[0]) ⟨16,by decide⟩ ⟨0,W_pos⟩ 3 (by decide)
    (by simpa only [Machine.push,wmod_of_lt (by decide : 3<W)] using hlen)
  rw [if_pos (by decide : (0 : Nat)<3)] at ha
  rw [writeArrayStackCode,run_append_ok ha]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt (by decide : 17<W),
    Out.ok_bind,exec_nil,writeMachine]

/-- Execute the resolved local-index delete and its expression statement with
an inhabited independent heap relation and two old Source aliases. The target
index is a real scalar local, not a literal supplied to the operation. -/
theorem resolved_runtime_delete (p : Roadmap.Pipeline) :
    ∃ (out : Heap H) (z : Source.EMState E0 SΓ) (target : Machine),
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 term).run (indexedSource (uintOfNat 0))=(.ok Source.RVal.unit,z) ∧
      (Source.execS (Source.SemanticsExamples.G0 p) F0 4 SΓ.length none
        (.expr term : Source.RStmt E0 [] false .body SΓ SΓ) (indexedSource (uintOfNat 0)).1).run (.nil,sy.2)=
          (.ok (.normal (indexedSource (uintOfNat 0)).1),(.nil,z.2)) ∧
      run (deleteLocalCode 1 (.there .here : Idx [.val .uint,.mem B] (.mem B))
        (compileVal 1 (.simple (.local .here) : Val C [.val .uint,.mem B] .uint))) (indexedMachine 0)=.ok target 0 ∧
      SourceBoolMemoryAt z 0 out r .dyn ∧ Source.MemOK E0 SH z ∧
      z.1=(indexedSource (uintOfNat 0)).1 ∧
      [MObj.elems .dyn (hp.get r),MObj.elems .dyn (out.get r)]=[[true,false,false],[false,false,false]] ∧
      (Source.readLoc (E := E0) (Γ := SΓ) F0 (τ := .bool) (.mem 0 0)).run z=(.ok (.bool false),z) ∧
      z.1.get (.there (.there .here))=.memRef rfl 0 ∧ target.stack=[w[42]] ∧
      [target.mem 0,target.mem 1,target.mem 2,target.mem 5,target.mem 16,target.mem 17,target.mem 18,target.mem 19]=
        [w[20],w[16],w[0],w[99],w[3],w[0],w[0],w[0]] := by
  have hr : SourceBoolMemoryAt (indexedSource (uintOfNat 0)) 0 (indexedState (uintOfNat 0)).heap r .dyn := represented
  have hk : (uintOfNat 0).1.toNat<(indexedState (uintOfNat 0)).heap.len r .dyn := by
    simp only [indexedState,State.push,σ,Heap.len,Heap.get,Objs.get,hp,r,MObj.elems_dyn]
    decide
  obtain ⟨out,z,target,hw,he,hs,hi,hcode,hrep,hm,hmem,hl,hstack,ha⟩ :=
    resolved_delete_word (Source.SemanticsExamples.G0 p) F0 0 (indexedState (uintOfNat 0)) r hr
      sroot sindex (.there .here) .here (uintOfNat 0) rfl rfl rfl rfl hk indexed_repr SH (indexed_memOK _)
  have hv : MObj.elems .dyn (out.get r)=[false,false,false] := by
    change hp.setIndex r .dyn (uintOfNat 0) false=some out at hw
    simp only [Heap.setIndex] at hw
    have hk' : (uintOfNat 0).1.toNat<(MObj.elems .dyn (hp.get r)).length := hk
    rw [if_pos hk'] at hw
    rw [←Option.some.inj hw,Heap.get_set_same,MObj.elems_setElem]
    simp only [Heap.get,Objs.get,hp,r,MObj.elems_dyn]
    rfl
  have ht : target=writeMachine (indexedMachine 0) 17 w[0] := by
    have hc := indexed_code_run (indexedMachine 0) rfl rfl rfl
    have heq := hc.symm.trans hcode
    cases heq
    rfl
  refine ⟨out,z,target,he,hs,hcode,hrep,hmem,hl,?_,?_,?_,hstack,?_⟩
  · rw [hv]
    simp only [Heap.get,Objs.get,hp,r,MObj.elems_dyn]
  · have hh : z.2.heap.get 0=some ⟨.array .memory .bool none,sourceBoolMemory [false,false,false]⟩ := by rw [←hv];exact hrep
    exact source_bool_read z 0 _ hh 0 (by decide)
  · rw [hl];rfl
  · rw [ht];rfl

/-- A valid runtime local whose value is the exact array endpoint is rejected
by actual Source location evaluation, before a deletion can take place. -/
theorem resolved_runtime_endpoint (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 term).run (indexedSource (uintOfNat 3))=
      (.error (.revert (Source.panicData .index)),indexedSource (uintOfNat 3)) ∧
      run indexedCode (indexedMachine 3)=.revert := by
  have hr : SourceBoolMemoryAt (indexedSource (uintOfNat 3)) 0 hp r .dyn := represented
  have hm : StateRepr 1 1 8 ((Frag.init Γ).push (.val .uint) .ok)
      (indexedState (uintOfNat 3)) base (indexedMachine 3) :=
    initial_repr.consVal (uintOfNat 3) w[3] (ReprV.uint_of rfl) (by decide)
  exact resolved_delete_word_bounds (Source.SemanticsExamples.G0 p) F0 0 (indexedState (uintOfNat 3)) r hr
    sroot sindex (.there .here) .here (uintOfNat 3) rfl rfl rfl rfl (by
      simp only [indexedState,State.push,σ,Heap.len,Heap.get,Objs.get,hp,r,MObj.elems_dyn]
      decide) hm
/-- info: 'Solidity.Backend.MemoryOps.SourceTargetControls.resolved_runtime_delete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms resolved_runtime_delete
/-- info: 'Solidity.Backend.MemoryOps.SourceTargetControls.resolved_runtime_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms resolved_runtime_endpoint


/-- The REAL resolved default declaration returns a fresh reference local;
full existing constructor observations are tied to the SAME reached heap. -/
theorem resolved_default_declaration (p : Roadmap.Pipeline) :
    ∃ z : Source.EMState E0 [],
      (Source.execS (Source.SemanticsExamples.G0 p) F0 3 0 none
        (.declVar (.array .memory .bool none) : Source.RStmt E0 [] false .body [] [.array .memory .bool none]) .nil).run (.nil,sy.2)=
          (.ok (.normal (.cons (.memRef rfl 1) z.1)),(.nil,z.2)) ∧
      TRun.declMem B none rfl σ=.ok ⟨ctorState,List.prefix_append _ _⟩ ∧
      run ctorCode machine=.ok ctorMachine 0 ∧
      SourceBoolMemoryAt (.cons (.memRef rfl 1 : Source.Val E0.layout (.array .memory .bool none)) z.1,z.2)
        1 ctorState.heap ctorRef .dyn ∧
      Source.MemOK E0 SH (.cons (.memRef rfl 1 : Source.Val E0.layout (.array .memory .bool none)) z.1,z.2) ∧
      [sy.2.heap.get 0,z.2.heap.get 0,z.2.heap.get 1]=
        [some ⟨.array .memory .bool none,sourceBoolMemory [true,false,false]⟩,
         some ⟨.array .memory .bool none,sourceBoolMemory [true,false,false]⟩,
         some ⟨.array .memory .bool none,sourceBoolMemory []⟩] ∧
      [MObj.elems .dyn (hp.get r),MObj.elems (H := ctorState.H) .dyn (ctorState.heap.get (r.wk (List.prefix_append H [B]))),
        MObj.elems (H := ctorState.H) .dyn (ctorState.heap.get ctorRef)]=[[true,false,false],[true,false,false],[]] ∧
      [ctorMachine.mem 0,ctorMachine.mem 1,ctorMachine.mem 2,ctorMachine.mem 5,ctorMachine.mem 16,
        ctorMachine.mem 17,ctorMachine.mem 18,ctorMachine.mem 19,ctorMachine.mem 20]=
        [w[21],w[16],w[20],w[99],w[3],w[1],w[0],w[0],w[0]] ∧
      ctorMachine.stack=[w[42]] ∧ ctorRef.id=1 ∧ r.id=0 := by
  obtain ⟨z,hzero,hs,hd,hc,hr,hnew,hm,ha,hstack,hid⟩ :=
    source_bool_declaration_word (Source.SemanticsExamples.G0 p) F0 sy 0 SH source_memOK σ
      initial_repr initial_allocator (by decide) (by decide) (by decide)
  obtain ⟨z0,hzero0,_,_,_,_,_,hv,ht,hw,hstack0,hid0,hold,_,_,_⟩ := default_constructor_views
  have he : z=z0 := congrArg Prod.snd (hzero.symm.trans hzero0)
  subst z0
  exact ⟨z,hs,hd,hc,hr,hnew,ht,hv,hw,hstack0,hid0,hold⟩

/-- Low Source horizons cannot return a fabricated fresh local. The same
nontrivial old heap is unchanged at every supported timeout observation. -/
theorem resolved_declaration_timeouts (p : Roadmap.Pipeline) :
    ∀ n, n≤2 → (Source.execS (Source.SemanticsExamples.G0 p) F0 n 0 none
      (.declVar (.array .memory .bool none) : Source.RStmt E0 [] false .body [] [.array .memory .bool none]) .nil).run (.nil,sy.2)=
        (.error .timeout,(.nil,sy.2)) :=
  source_bool_declaration_timeouts (Source.SemanticsExamples.G0 p) F0 sy
/-- info: 'Solidity.Backend.MemoryOps.SourceTargetControls.resolved_default_declaration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms resolved_default_declaration
/-- info: 'Solidity.Backend.MemoryOps.SourceTargetControls.resolved_declaration_timeouts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms resolved_declaration_timeouts


private abbrev AΓ : Source.RCtx := .bool::SΓ
private def assignSource (k : PrimTy.uint.Denote) (v : Bool) : Source.EMState E0 AΓ :=
  (.cons (.bool v) (indexedSource k).1,sy.2)
private def assignState (k : PrimTy.uint.Denote) (v : Bool) := (indexedState k).push (t := .val .bool) v
private def assignMachine (k : Nat) (v : Bool) := writeMachine (indexedMachine k) 3 (.val (bword v))
private abbrev aroot : Source.Idx AΓ (.array .memory .bool none) := .there sroot
private abbrev aindex : Source.Idx AΓ (.int .u256) := .there sindex
private def assignTerm : Source.RExpr E0 AΓ .bool := sourceIndexedAssign aroot aindex .here
private def assignCode := writeLocalCode (C := C) 1 (.there (.there .here) : Idx [.val .bool,.val .uint,.mem B] (.mem B))
  (.simple (.local (.there .here))) (.simple (.local .here))
private theorem assign_memOK (k : PrimTy.uint.Denote) (v : Bool) : Source.MemOK E0 SH (assignSource k v) :=
  ⟨⟨(indexed_memOK k).1.1,⟨trivial,(indexed_memOK k).1.2⟩⟩,(indexed_memOK k).2⟩
private theorem assign_repr_one : StateRepr 1 1 8
    (((Frag.init Γ).push (.val .uint) .ok).push (.val .bool) .ok)
    (assignState (uintOfNat 1) true) base (assignMachine 1 true) := by
  have h := initial_repr.consVal (uintOfNat 1) w[1] (ReprV.uint_of rfl) (by decide)
  exact h.consVal (p := .bool) true w[1] rfl (by decide)
private theorem assign_code_run (m : Machine) (hptr : m.mem 1=w[16]) (hi : m.mem 2=w[1])
    (hv : m.mem 3=w[1]) (hlen : m.mem 16=w[3]) : run assignCode m=.ok (writeMachine m 18 w[1]) 0 := by
  change run ([.mload 3] ++ ([.mload 1] ++ ([.mload 2] ++ writeArrayStackCode))) m=_
  rw [run_append_ok (show run [.mload 3] m=.ok (m.push w[1]) 0 from by
    change Out.ok (m.push (m.mem 3)) 0=_
    rw [hv])]
  rw [run_append_ok (show run [.mload 1] (m.push w[1])=.ok ((m.push w[1]).push w[16]) 0 from by
    change Out.ok ((m.push w[1]).push (m.mem 1)) 0=_
    rw [hptr])]
  rw [run_append_ok (show run [.mload 2] ((m.push w[1]).push w[16])=
    .ok (((m.push w[1]).push w[16]).push w[1]) 0 from by
      change Out.ok (((m.push w[1]).push w[16]).push (m.mem 2)) 0=_
      rw [hi])]
  have ha := arrayAddrStack_run (m.push w[1]) ⟨16,by decide⟩ ⟨1,by decide⟩ 3 (by decide)
    (by simpa only [Machine.push,wmod_of_lt (by decide : 3<W)] using hlen)
  rw [if_pos (by decide : (1 : Nat)<3)] at ha
  rw [writeArrayStackCode,run_append_ok ha]
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt (by decide : 18<W),
    Out.ok_bind,exec_nil,writeMachine]

/-- RHS and index are real locals; writing true at index1 materially differs
from delete/default, a wrong zero index, and a stale/ignored RHS value. -/
theorem resolved_runtime_assignment (p : Roadmap.Pipeline) :
    ∃ (out : Heap H) (z : Source.EMState E0 AΓ) (target : Machine),
      (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 assignTerm).run (assignSource (uintOfNat 1) true)=
        (.ok (.val (.bool true)),z) ∧
      (Source.execS (Source.SemanticsExamples.G0 p) F0 4 AΓ.length none
        (.expr assignTerm : Source.RStmt E0 [] false .body AΓ AΓ) (assignSource (uintOfNat 1) true).1).run (.nil,sy.2)=
          (.ok (.normal (assignSource (uintOfNat 1) true).1),(.nil,z.2)) ∧
      run assignCode (assignMachine 1 true)=.ok target 0 ∧
      SourceBoolMemoryAt z 0 out r .dyn ∧ Source.MemOK E0 SH z ∧ z.1=(assignSource (uintOfNat 1) true).1 ∧
      [MObj.elems .dyn (hp.get r),MObj.elems .dyn (out.get r)]=[[true,false,false],[true,true,false]] ∧
      (Source.readLoc (E := E0) (Γ := AΓ) F0 (τ := .bool) (.mem 0 1)).run z=(.ok (.bool true),z) ∧
      z.1.get (.there (.there (.there .here)))=.memRef rfl 0 ∧
      [target.mem 0,target.mem 1,target.mem 2,target.mem 3,target.mem 5,target.mem 16,target.mem 17,target.mem 18,target.mem 19]=
        [w[20],w[16],w[1],w[1],w[99],w[3],w[1],w[1],w[0]] ∧
      target.stack=[w[42]] ∧ target.mem 18≠w[0] := by
  have hr : SourceBoolMemoryAt (assignSource (uintOfNat 1) true) 0 (assignState (uintOfNat 1) true).heap r .dyn := represented
  have hk : (uintOfNat 1).1.toNat<(assignState (uintOfNat 1) true).heap.len r .dyn := by
    simp only [assignState,indexedState,State.push,σ,Heap.len,Heap.get,Objs.get,hp,r,MObj.elems_dyn]
    decide
  obtain ⟨out,z,target,hw,he,hs,hi,hcode,hrep,hm,hmem,hl,hstack,ha⟩ :=
    resolved_assign_word (Source.SemanticsExamples.G0 p) F0 0 (assignState (uintOfNat 1) true) r hr
      aroot aindex .here (.there (.there .here)) (.there .here) .here (uintOfNat 1) true
      rfl rfl rfl rfl rfl rfl hk assign_repr_one SH (assign_memOK _ _)
  have hv : MObj.elems .dyn (out.get r)=[true,true,false] := by
    change hp.setIndex r .dyn (uintOfNat 1) true=some out at hw
    simp only [Heap.setIndex] at hw
    have hk' : (uintOfNat 1).1.toNat<(MObj.elems .dyn (hp.get r)).length := hk
    rw [if_pos hk'] at hw
    rw [←Option.some.inj hw,Heap.get_set_same,MObj.elems_setElem]
    simp only [Heap.get,Objs.get,hp,r,MObj.elems_dyn]
    rfl
  have ht : target=writeMachine (assignMachine 1 true) 18 w[1] := by
    have hc := assign_code_run (assignMachine 1 true) rfl rfl rfl rfl
    have heq := hc.symm.trans hcode
    cases heq
    rfl
  refine ⟨out,z,target,he,hs,hcode,hrep,hmem,hl,?_,?_,?_,?_,hstack,?_⟩
  · rw [hv];simp only [Heap.get,Objs.get,hp,r,MObj.elems_dyn]
  · have hh : z.2.heap.get 0=some ⟨.array .memory .bool none,sourceBoolMemory [true,true,false]⟩ := by rw [←hv];exact hrep
    exact source_bool_read z 0 _ hh 1 (by decide)
  · rw [hl];rfl
  · rw [ht];rfl
  · rw [ht];exact by decide

theorem resolved_assignment_endpoint (p : Roadmap.Pipeline) :
    (Source.evalE (Source.SemanticsExamples.G0 p) F0 3 assignTerm).run (assignSource (uintOfNat 3) true)=
      (.error (.revert (Source.panicData .index)),assignSource (uintOfNat 3) true) ∧
      run assignCode (assignMachine 3 true)=.revert := by
  have hr : SourceBoolMemoryAt (assignSource (uintOfNat 3) true) 0 (assignState (uintOfNat 3) true).heap r .dyn := represented
  have h := initial_repr.consVal (uintOfNat 3) w[3] (ReprV.uint_of rfl) (by decide)
  have hm := h.consVal (p := .bool) true w[1] (show ReprV .bool true w[1] from rfl) (by decide : 1+([.val .uint,.mem B].length+1)≤8)
  exact resolved_assign_word_bounds (Source.SemanticsExamples.G0 p) F0 0 (assignState (uintOfNat 3) true) r hr
    aroot aindex .here (.there (.there .here)) (.there .here) .here (uintOfNat 3) true
    rfl rfl rfl rfl rfl rfl (by
      simp only [assignState,indexedState,State.push,σ,Heap.len,Heap.get,Objs.get,hp,r,MObj.elems_dyn]
      decide) hm
/-- info: 'Solidity.Backend.MemoryOps.SourceTargetControls.resolved_runtime_assignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms resolved_runtime_assignment
/-- info: 'Solidity.Backend.MemoryOps.SourceTargetControls.resolved_assignment_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms resolved_assignment_endpoint


private abbrev AΔ : Ctx := [.val .bool,.val .uint,.mem B]
private abbrev otherAlias : Source.Idx AΓ (.array .memory .bool none) := .there (.there (.there .here))
private def seqDelete : Source.RExpr E0 AΓ (.tuple []) := sourceIndexedDelete aroot aindex
private def seqItems : Source.RItems E0 [] false .body AΓ AΓ := .stmt (.expr assignTerm) (.stmt (.expr seqDelete) .nil)
private def reverseItems : Source.RItems E0 [] false .body AΓ AΓ := .stmt (.expr seqDelete) (.stmt (.expr assignTerm) .nil)
private def seqDeleteCode : List Instr := deleteLocalCode 1 (.there (.there .here) : Idx AΔ (.mem B))
  (compileVal 1 (.simple (.local (.there .here)) : Val C AΔ .uint))
private def seqProgram : Prog C AΔ AΔ := .cons
  (.assignMem (.index .dyn (.var (.there (.there .here)) rfl) (.simple (.local (.there .here)))) (.val (.simple (.local .here))))
  (.cons (.deleteMem (.loc (.index .dyn (.var (.there (.there .here)) rfl) (.simple (.local (.there .here))))) rfl) .nil)
private def reverseProgram : Prog C AΔ AΔ := .cons
  (.deleteMem (.loc (.index .dyn (.var (.there (.there .here)) rfl) (.simple (.local (.there .here))))) rfl)
  (.cons (.assignMem (.index .dyn (.var (.there (.there .here)) rfl) (.simple (.local (.there .here)))) (.val (.simple (.local .here)))) .nil)
private def seqCells (m : Machine) : List Word := [m.mem 0,m.mem 1,m.mem 2,m.mem 3,m.mem 5,m.mem 16,m.mem 17,m.mem 18,m.mem 19]
private theorem one_valid : (uintOfNat 1).1.toNat<(assignState (uintOfNat 1) true).heap.len r .dyn := by
  simp only [assignState,indexedState,State.push,σ,Heap.len,Heap.get,Objs.get,hp,r,MObj.elems_dyn]
  decide
private theorem delete_cell_run (m : Machine) (c : Nat) (k : Fin W) (hk : k.val<3)
    (hptr : m.mem 1=w[16]) (hi : m.mem c=.val k) (hlen : m.mem 16=w[3]) :
    run ([.push w[0]] ++ ([.mload 1] ++ ([.mload c] ++ writeArrayStackCode))) m=
      .ok (writeMachine m (16+1+k.val) w[0]) 0 := by
  rw [run_append_ok (show run [.push w[0]] m=.ok (m.push w[0]) 0 from rfl)]
  rw [run_append_ok (show run [.mload 1] (m.push w[0])=.ok ((m.push w[0]).push w[16]) 0 from by
    change Out.ok ((m.push w[0]).push (m.mem 1)) 0=_
    rw [hptr])]
  rw [run_append_ok (show run [.mload c] ((m.push w[0]).push w[16])=
    .ok (((m.push w[0]).push w[16]).push (.val k)) 0 from by
      change Out.ok (((m.push w[0]).push w[16]).push (m.mem c)) 0=_
      rw [hi])]
  have ha := arrayAddrStack_run (m.push w[0]) ⟨16,by decide⟩ k 3 (by decide)
    (by simpa only [Machine.push,wmod_of_lt (by decide : 3<W)] using hlen)
  rw [if_pos hk] at ha
  rw [writeArrayStackCode,run_append_ok ha]
  have haddr : 16+1+k.val<W := by
    have hw : 20<W := by decide
    omega
  simp only [run,Machine.push,exec_cons_zero,Instr.step,wmod_of_lt haddr,Out.ok_bind,exec_nil,writeMachine]
private theorem seq_delete_run (m : Machine) (hptr : m.mem 1=w[16]) (hi : m.mem 2=w[1]) (hlen : m.mem 16=w[3]) :
    run seqDeleteCode m=.ok (writeMachine m 18 w[0]) 0 :=
  delete_cell_run m 2 ⟨1,by decide⟩ (by decide) hptr hi hlen

/-- Actual reached sequence and its complete ordered observations; both declared
pipelines use the same independently inhabited initial heap and locals. -/
theorem reached_assignment_delete (p : Roadmap.Pipeline) :
    ∃ (mid out : Heap H) (ym z : Source.EMState E0 AΓ) (mm target : Machine),
      (assignState (uintOfNat 1) true).heap.writeAddr (.index r .dyn (uintOfNat 1)) true=some mid ∧
      mid.writeAddr (.index r .dyn (uintOfNat 1)) false=some out ∧
      (Source.execS (Source.SemanticsExamples.G0 p) F0 5 AΓ.length none (.expr assignTerm : Source.RStmt E0 [] false .body AΓ AΓ)
        (assignSource (uintOfNat 1) true).1).run (.nil,sy.2)=(.ok (.normal (assignSource (uintOfNat 1) true).1),(.nil,ym.2)) ∧
      (Source.execS (Source.SemanticsExamples.G0 p) F0 4 AΓ.length none (.expr seqDelete : Source.RStmt E0 [] false .body AΓ AΓ)
        ym.1).run (.nil,ym.2)=(.ok (.normal ym.1),(.nil,z.2)) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 AΓ.length none seqItems (assignSource (uintOfNat 1) true).1).run (.nil,sy.2)=
        (.ok (.normal (assignSource (uintOfNat 1) true).1),(.nil,z.2)) ∧
      Prog.run (assignState (uintOfNat 1) true) seqProgram=.ok ⟨(assignState (uintOfNat 1) true).withHeap out,List.prefix_refl _⟩ ∧
      run assignCode (assignMachine 1 true)=.ok mm 0 ∧ run seqDeleteCode mm=.ok target 0 ∧
      run (assignCode ++ seqDeleteCode) (assignMachine 1 true)=.ok target 0 ∧
      [MObj.elems .dyn (hp.get r),MObj.elems .dyn (mid.get r),MObj.elems .dyn (out.get r)]=
        [[true,false,false],[true,true,false],[true,false,false]] ∧
      [seqCells (assignMachine 1 true),seqCells mm,seqCells target]=
        [[w[20],w[16],w[1],w[1],w[99],w[3],w[1],w[0],w[0]],[w[20],w[16],w[1],w[1],w[99],w[3],w[1],w[1],w[0]],[w[20],w[16],w[1],w[1],w[99],w[3],w[1],w[0],w[0]]] ∧
      SourceBoolMemoryAt ym 0 mid r .dyn ∧ SourceBoolMemoryAt z 0 out r .dyn ∧
      Source.MemOK E0 SH ym ∧ Source.MemOK E0 SH z ∧ z.1=(assignSource (uintOfNat 1) true).1 ∧
      (Source.evalLoc (Source.SemanticsExamples.G0 p) F0 2
        (.indexArray (.local otherAlias) (by decide) (.local aindex) rfl)).run z=(.ok (.mem 0 1),z) ∧
      (Source.readLoc (E := E0) (Γ := AΓ) F0 (τ := .bool) (.mem 0 1)).run z=(.ok (.bool false),z) ∧
      target.stack=[w[42]] := by
  have hr : SourceBoolMemoryAt (assignSource (uintOfNat 1) true) 0 (assignState (uintOfNat 1) true).heap r .dyn := represented
  obtain ⟨mid,out,ym,z,mm,target,hw1,hw2,hs1,hs2,hs,hi,hc1,hc2,hc,hr1,hr2,hm1,hm2,hmem1,hmem2,hy1,hy2,hstack,ha⟩ :=
    resolved_assign_delete_word (Source.SemanticsExamples.G0 p) F0 0 (assignState (uintOfNat 1) true) r hr
      aroot aindex aindex .here (.there (.there .here)) (.there .here) (.there .here) .here
      (uintOfNat 1) (uintOfNat 1) true rfl rfl rfl rfl rfl rfl rfl rfl one_valid one_valid assign_repr_one SH (assign_memOK _ _)
  have hv1 : MObj.elems .dyn (mid.get r)=[true,true,false] := by
    rw [indexedWrite_elems _ _ _ _ _ _ hw1]
    simp only [assignState,indexedState,State.push,σ,Heap.get,Objs.get,hp,r,MObj.elems_dyn]
    rfl
  have hv2 : MObj.elems .dyn (out.get r)=[true,false,false] := by
    rw [indexedWrite_elems _ _ _ _ _ _ hw2,hv1];rfl
  have hm : mm=writeMachine (assignMachine 1 true) 18 w[1] := by
    have hc0 := assign_code_run (assignMachine 1 true) rfl rfl rfl rfl
    have he := hc0.symm.trans hc1
    cases he;rfl
  have ht : target=writeMachine (writeMachine (assignMachine 1 true) 18 w[1]) 18 w[0] := by
    have hc0 := seq_delete_run mm (by rw [hm];rfl) (by rw [hm];rfl) (by rw [hm];rfl)
    have he := hc0.symm.trans hc2
    cases he
    rw [hm]
  have hk : (uintOfNat 1).1.toNat<out.len r .dyn := by
    change (uintOfNat 1).1.toNat<(MObj.elems .dyn (out.get r)).length
    rw [hv2];decide
  refine ⟨mid,out,ym,z,mm,target,hw1,hw2,hs1,hs2,hs,hi,hc1,hc2,hc,?_,?_,hr1,hr2,hmem1,hmem2,hy2,?_,?_,hstack⟩
  · rw [hv1,hv2];simp only [Heap.get,Objs.get,hp,r,MObj.elems_dyn]
  · rw [hm,ht];rfl
  · exact hr2.eval_index_loc (Source.SemanticsExamples.G0 p) F0 0 otherAlias aindex (uintOfNat 1)
      (by rw [hy2];rfl) (by rw [hy2];rfl) hk
  · have hh : z.2.heap.get 0=some ⟨.array .memory .bool none,sourceBoolMemory [true,false,false]⟩ := by rw [←hv2];exact hr2
    exact source_bool_read z 0 _ hh 1 (by decide)

/-- Actual reached sequence and its complete ordered observations; both declared
pipelines use the same independently inhabited initial heap and locals. -/
theorem reached_delete_assignment (p : Roadmap.Pipeline) :
    ∃ (mid out : Heap H) (ym z : Source.EMState E0 AΓ) (mm target : Machine),
      (assignState (uintOfNat 1) true).heap.writeAddr (.index r .dyn (uintOfNat 1)) false=some mid ∧
      mid.writeAddr (.index r .dyn (uintOfNat 1)) true=some out ∧
      (Source.execS (Source.SemanticsExamples.G0 p) F0 5 AΓ.length none (.expr seqDelete : Source.RStmt E0 [] false .body AΓ AΓ)
        (assignSource (uintOfNat 1) true).1).run (.nil,sy.2)=(.ok (.normal (assignSource (uintOfNat 1) true).1),(.nil,ym.2)) ∧
      (Source.execS (Source.SemanticsExamples.G0 p) F0 4 AΓ.length none (.expr assignTerm : Source.RStmt E0 [] false .body AΓ AΓ)
        ym.1).run (.nil,ym.2)=(.ok (.normal ym.1),(.nil,z.2)) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 AΓ.length none reverseItems (assignSource (uintOfNat 1) true).1).run (.nil,sy.2)=
        (.ok (.normal (assignSource (uintOfNat 1) true).1),(.nil,z.2)) ∧
      Prog.run (assignState (uintOfNat 1) true) reverseProgram=.ok ⟨(assignState (uintOfNat 1) true).withHeap out,List.prefix_refl _⟩ ∧
      run seqDeleteCode (assignMachine 1 true)=.ok mm 0 ∧ run assignCode mm=.ok target 0 ∧
      run (seqDeleteCode ++ assignCode) (assignMachine 1 true)=.ok target 0 ∧
      [MObj.elems .dyn (hp.get r),MObj.elems .dyn (mid.get r),MObj.elems .dyn (out.get r)]=
        [[true,false,false],[true,false,false],[true,true,false]] ∧
      [seqCells (assignMachine 1 true),seqCells mm,seqCells target]=
        [[w[20],w[16],w[1],w[1],w[99],w[3],w[1],w[0],w[0]],[w[20],w[16],w[1],w[1],w[99],w[3],w[1],w[0],w[0]],[w[20],w[16],w[1],w[1],w[99],w[3],w[1],w[1],w[0]]] ∧
      SourceBoolMemoryAt ym 0 mid r .dyn ∧ SourceBoolMemoryAt z 0 out r .dyn ∧
      Source.MemOK E0 SH ym ∧ Source.MemOK E0 SH z ∧ z.1=(assignSource (uintOfNat 1) true).1 ∧
      (Source.evalLoc (Source.SemanticsExamples.G0 p) F0 2
        (.indexArray (.local otherAlias) (by decide) (.local aindex) rfl)).run z=(.ok (.mem 0 1),z) ∧
      (Source.readLoc (E := E0) (Γ := AΓ) F0 (τ := .bool) (.mem 0 1)).run z=(.ok (.bool true),z) ∧
      target.stack=[w[42]] := by
  have hr : SourceBoolMemoryAt (assignSource (uintOfNat 1) true) 0 (assignState (uintOfNat 1) true).heap r .dyn := represented
  obtain ⟨mid,out,ym,z,mm,target,hw1,hw2,hs1,hs2,hs,hi,hc1,hc2,hc,hr1,hr2,hm1,hm2,hmem1,hmem2,hy1,hy2,hstack,ha⟩ :=
    resolved_delete_assign_word (Source.SemanticsExamples.G0 p) F0 0 (assignState (uintOfNat 1) true) r hr
      aroot aindex aindex .here (.there (.there .here)) (.there .here) (.there .here) .here
      (uintOfNat 1) (uintOfNat 1) true rfl rfl rfl rfl rfl rfl rfl rfl one_valid one_valid assign_repr_one SH (assign_memOK _ _)
  have hv1 : MObj.elems .dyn (mid.get r)=[true,false,false] := by
    rw [indexedWrite_elems _ _ _ _ _ _ hw1]
    simp only [assignState,indexedState,State.push,σ,Heap.get,Objs.get,hp,r,MObj.elems_dyn]
    rfl
  have hv2 : MObj.elems .dyn (out.get r)=[true,true,false] := by
    rw [indexedWrite_elems _ _ _ _ _ _ hw2,hv1];rfl
  have hm : mm=writeMachine (assignMachine 1 true) 18 w[0] := by
    have hc0 := seq_delete_run (assignMachine 1 true) rfl rfl rfl
    have he := hc0.symm.trans hc1
    cases he;rfl
  have ht : target=writeMachine (writeMachine (assignMachine 1 true) 18 w[0]) 18 w[1] := by
    have hc0 := assign_code_run mm (by rw [hm];rfl) (by rw [hm];rfl) (by rw [hm];rfl) (by rw [hm];rfl)
    have he := hc0.symm.trans hc2
    cases he
    rw [hm]
  have hk : (uintOfNat 1).1.toNat<out.len r .dyn := by
    change (uintOfNat 1).1.toNat<(MObj.elems .dyn (out.get r)).length
    rw [hv2];decide
  refine ⟨mid,out,ym,z,mm,target,hw1,hw2,hs1,hs2,hs,hi,hc1,hc2,hc,?_,?_,hr1,hr2,hmem1,hmem2,hy2,?_,?_,hstack⟩
  · rw [hv1,hv2];simp only [Heap.get,Objs.get,hp,r,MObj.elems_dyn]
  · rw [hm,ht];rfl
  · exact hr2.eval_index_loc (Source.SemanticsExamples.G0 p) F0 0 otherAlias aindex (uintOfNat 1)
      (by rw [hy2];rfl) (by rw [hy2];rfl) hk
  · have hh : z.2.heap.get 0=some ⟨.array .memory .bool none,sourceBoolMemory [true,true,false]⟩ := by rw [←hv2];exact hr2
    exact source_bool_read z 0 _ hh 1 (by decide)

/-- info: 'Solidity.Backend.MemoryOps.SourceTargetControls.reached_assignment_delete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reached_assignment_delete
/-- info: 'Solidity.Backend.MemoryOps.SourceTargetControls.reached_delete_assignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reached_delete_assignment


private abbrev DΓ : Source.RCtx := (.int .u256)::AΓ
private abbrev DΔ : Ctx := (.val .uint)::AΔ
private def disjointSource (j : PrimTy.uint.Denote) : Source.EMState E0 DΓ :=
  (.cons (sourceUint j) (assignSource (uintOfNat 1) true).1,sy.2)
private def disjointState (j : PrimTy.uint.Denote) := (assignState (uintOfNat 1) true).push (t := .val .uint) j
private def disjointMachine (j : Nat) := writeMachine (assignMachine 1 true) 4 (.val (wmod j))
private def disjointItems : Source.RItems E0 [] false .body DΓ DΓ :=
  .stmt (.expr (sourceIndexedAssign (.there aroot) (.there aindex) (.there .here)))
    (.stmt (.expr (sourceIndexedDelete (.there aroot) .here)) .nil)
private def disjointProgram : Prog C DΔ DΔ := .cons
  (.assignMem (.index .dyn (.var (.there (.there (.there .here))) rfl) (.simple (.local (.there (.there .here))))) (.val (.simple (.local (.there .here)))))
    (.cons (.deleteMem (.loc (.index .dyn (.var (.there (.there (.there .here))) rfl) (.simple (.local .here)))) rfl) .nil)
private def disjointDeleteCode := deleteLocalCode 1 (.there (.there (.there .here)) : Idx DΔ (.mem B))
  (compileVal 1 (.simple (.local .here) : Val C DΔ .uint))
private def disjointCells (m : Machine) : List Word := [m.mem 0,m.mem 1,m.mem 2,m.mem 3,m.mem 4,m.mem 5,m.mem 16,m.mem 17,m.mem 18,m.mem 19]
private theorem disjoint_memOK (j : PrimTy.uint.Denote) : Source.MemOK E0 SH (disjointSource j) :=
  ⟨⟨(assign_memOK (uintOfNat 1) true).1.1,⟨trivial,(assign_memOK (uintOfNat 1) true).1.2⟩⟩,(assign_memOK (uintOfNat 1) true).2⟩
private theorem disjoint_zero_repr : StateRepr 1 1 8
    ((((Frag.init Γ).push (.val .uint) .ok).push (.val .bool) .ok).push (.val .uint) .ok)
    (disjointState (uintOfNat 0)) base (disjointMachine 0) :=
  assign_repr_one.consVal (uintOfNat 0) w[0] (ReprV.uint_of rfl) (by decide)
private theorem disjoint_three_repr : StateRepr 1 1 8
    ((((Frag.init Γ).push (.val .uint) .ok).push (.val .bool) .ok).push (.val .uint) .ok)
    (disjointState (uintOfNat 3)) base (disjointMachine 3) :=
  assign_repr_one.consVal (uintOfNat 3) w[3] (ReprV.uint_of rfl) (by decide)

/-- The second runtime index differs from the first; it deletes an initially
true neighbour while retaining the actual first assignment's changed cell. -/
theorem reached_disjoint_cells (p : Roadmap.Pipeline) :
    ∃ (mid out : Heap H) (ym z : Source.EMState E0 DΓ) (mm target : Machine),
      (disjointState (uintOfNat 0)).heap.writeAddr (.index r .dyn (uintOfNat 1)) true=some mid ∧
      mid.writeAddr (.index r .dyn (uintOfNat 0)) false=some out ∧
      (Source.execS (Source.SemanticsExamples.G0 p) F0 5 DΓ.length none
        (.expr (sourceIndexedAssign (.there aroot) (.there aindex) (.there .here)) : Source.RStmt E0 [] false .body DΓ DΓ)
        (disjointSource (uintOfNat 0)).1).run (.nil,sy.2)=(.ok (.normal (disjointSource (uintOfNat 0)).1),(.nil,ym.2)) ∧
      (Source.execS (Source.SemanticsExamples.G0 p) F0 4 DΓ.length none
        (.expr (sourceIndexedDelete (.there aroot) .here) : Source.RStmt E0 [] false .body DΓ DΓ)
        ym.1).run (.nil,ym.2)=(.ok (.normal ym.1),(.nil,z.2)) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 DΓ.length none disjointItems (disjointSource (uintOfNat 0)).1).run (.nil,sy.2)=
        (.ok (.normal (disjointSource (uintOfNat 0)).1),(.nil,z.2)) ∧
      Prog.run (disjointState (uintOfNat 0)) disjointProgram=.ok ⟨(disjointState (uintOfNat 0)).withHeap out,List.prefix_refl _⟩ ∧
      run assignCode (disjointMachine 0)=.ok mm 0 ∧ run disjointDeleteCode mm=.ok target 0 ∧
      run (assignCode ++ disjointDeleteCode) (disjointMachine 0)=.ok target 0 ∧
      [MObj.elems .dyn (hp.get r),MObj.elems .dyn (mid.get r),MObj.elems .dyn (out.get r)]=
        [[true,false,false],[true,true,false],[false,true,false]] ∧
      [disjointCells (disjointMachine 0),disjointCells mm,disjointCells target]=
        [[w[20],w[16],w[1],w[1],w[0],w[99],w[3],w[1],w[0],w[0]],
         [w[20],w[16],w[1],w[1],w[0],w[99],w[3],w[1],w[1],w[0]],
         [w[20],w[16],w[1],w[1],w[0],w[99],w[3],w[0],w[1],w[0]]] ∧
      SourceBoolMemoryAt ym 0 mid r .dyn ∧ SourceBoolMemoryAt z 0 out r .dyn ∧ Source.MemOK E0 SH z ∧ z.1=(disjointSource (uintOfNat 0)).1 ∧
      (Source.readLoc (E := E0) (Γ := DΓ) F0 (τ := .bool) (.mem 0 0)).run z=(.ok (.bool false),z) ∧
      (Source.readLoc (E := E0) (Γ := DΓ) F0 (τ := .bool) (.mem 0 1)).run z=(.ok (.bool true),z) ∧ target.stack=[w[42]] := by
  have hr : SourceBoolMemoryAt (disjointSource (uintOfNat 0)) 0 (disjointState (uintOfNat 0)).heap r .dyn := represented
  obtain ⟨mid,out,ym,z,mm,target,hw1,hw2,hs1,hs2,hs,hi,hc1,hc2,hc,hr1,hr2,hm1,hm2,hmem1,hmem2,hy1,hy2,hstack,ha⟩ :=
    resolved_assign_delete_word (Source.SemanticsExamples.G0 p) F0 0 (disjointState (uintOfNat 0)) r hr
      (.there aroot) (.there aindex) .here (.there .here) (.there (.there (.there .here))) (.there (.there .here)) .here (.there .here)
      (uintOfNat 1) (uintOfNat 0) true rfl rfl rfl rfl rfl rfl rfl rfl one_valid (by
        simp only [disjointState,assignState,indexedState,State.push,σ,Heap.len,Heap.get,Objs.get,hp,r,MObj.elems_dyn];decide)
      disjoint_zero_repr SH (disjoint_memOK _)
  have hv1 : MObj.elems .dyn (mid.get r)=[true,true,false] := by
    rw [indexedWrite_elems _ _ _ _ _ _ hw1]
    simp only [disjointState,assignState,indexedState,State.push,σ,Heap.get,Objs.get,hp,r,MObj.elems_dyn];rfl
  have hv2 : MObj.elems .dyn (out.get r)=[false,true,false] := by
    rw [indexedWrite_elems _ _ _ _ _ _ hw2,hv1];rfl
  have hm : mm=writeMachine (disjointMachine 0) 18 w[1] := by
    have he := (assign_code_run (disjointMachine 0) rfl rfl rfl rfl).symm.trans hc1
    cases he;rfl
  have ht : target=writeMachine (writeMachine (disjointMachine 0) 18 w[1]) 17 w[0] := by
    have hc0 := delete_cell_run mm 4 ⟨0,W_pos⟩ (by decide) (by rw [hm];rfl) (by rw [hm];rfl) (by rw [hm];rfl)
    have he := hc0.symm.trans hc2
    cases he
    rw [hm]
    rfl
  have hh : z.2.heap.get 0=some ⟨.array .memory .bool none,sourceBoolMemory [false,true,false]⟩ := by rw [←hv2];exact hr2
  refine ⟨mid,out,ym,z,mm,target,hw1,hw2,hs1,hs2,hs,hi,hc1,hc2,hc,?_,?_,hr1,hr2,hmem2,hy2,
    source_bool_read z 0 _ hh 0 (by decide),source_bool_read z 0 _ hh 1 (by decide),hstack⟩
  · rw [hv1,hv2];simp only [Heap.get,Objs.get,hp,r,MObj.elems_dyn]
  · rw [hm,ht];rfl

/-- The first assignment genuinely succeeds and changes the heap; endpoint
rejection is in the actual reached second operation, with no suffix heap. -/
theorem reached_endpoint_failure (p : Roadmap.Pipeline) :
    ∃ (mid : Heap H) (ym : Source.EMState E0 DΓ) (mm : Machine),
      (Source.execS (Source.SemanticsExamples.G0 p) F0 5 DΓ.length none
        (.expr (sourceIndexedAssign (.there aroot) (.there aindex) (.there .here)) : Source.RStmt E0 [] false .body DΓ DΓ)
        (disjointSource (uintOfNat 3)).1).run (.nil,sy.2)=(.ok (.normal (disjointSource (uintOfNat 3)).1),(.nil,ym.2)) ∧
      run assignCode (disjointMachine 3)=.ok mm 0 ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 DΓ.length none disjointItems (disjointSource (uintOfNat 3)).1).run (.nil,sy.2)=
        (.error (.revert (Source.panicData .index)),(.nil,ym.2)) ∧
      Prog.run (disjointState (uintOfNat 3)) disjointProgram=.error .revert ∧
      run disjointDeleteCode mm=.revert ∧ run (assignCode ++ disjointDeleteCode) (disjointMachine 3)=.revert ∧
      [MObj.elems .dyn (hp.get r),MObj.elems .dyn (mid.get r)]=[[true,false,false],[true,true,false]] ∧
      [disjointCells (disjointMachine 3),disjointCells mm]=
        [[w[20],w[16],w[1],w[1],w[3],w[99],w[3],w[1],w[0],w[0]],
         [w[20],w[16],w[1],w[1],w[3],w[99],w[3],w[1],w[1],w[0]]] ∧
      SourceBoolMemoryAt ym 0 mid r .dyn ∧ Source.MemOK E0 SH ym ∧
      (Source.readLoc (E := E0) (Γ := DΓ) F0 (τ := .bool) (.mem 0 1)).run ym=(.ok (.bool true),ym) := by
  have hr : SourceBoolMemoryAt (disjointSource (uintOfNat 3)) 0 (disjointState (uintOfNat 3)).heap r .dyn := represented
  obtain ⟨mid,ym,mm,hw,hs,hc1,hsfail,hifail,hcfail,hc,hr1,hmem,hy⟩ :=
    resolved_assign_delete_reject (Source.SemanticsExamples.G0 p) F0 0 (disjointState (uintOfNat 3)) r hr
      (.there aroot) (.there aindex) .here (.there .here) (.there (.there (.there .here))) (.there (.there .here)) .here (.there .here)
      (uintOfNat 1) (uintOfNat 3) true rfl rfl rfl rfl rfl rfl rfl rfl one_valid (by
        simp only [disjointState,assignState,indexedState,State.push,σ,Heap.len,Heap.get,Objs.get,hp,r,MObj.elems_dyn];decide)
      disjoint_three_repr SH (disjoint_memOK _)
  have hv : MObj.elems .dyn (mid.get r)=[true,true,false] := by
    rw [indexedWrite_elems _ _ _ _ _ _ hw]
    simp only [disjointState,assignState,indexedState,State.push,σ,Heap.get,Objs.get,hp,r,MObj.elems_dyn];rfl
  have hm : mm=writeMachine (disjointMachine 3) 18 w[1] := by
    have he := (assign_code_run (disjointMachine 3) rfl rfl rfl rfl).symm.trans hc1
    cases he;rfl
  have hh : ym.2.heap.get 0=some ⟨.array .memory .bool none,sourceBoolMemory [true,true,false]⟩ := by rw [←hv];exact hr1
  refine ⟨mid,ym,mm,hs,hc1,hsfail,hifail,hcfail,hc,?_,?_,hr1,hmem,source_bool_read ym 0 _ hh 1 (by decide)⟩
  · rw [hv];simp only [Heap.get,Objs.get,hp,r,MObj.elems_dyn]
  · rw [hm];rfl

/-- Horizon5 completes a material first assignment, then times out while
resolving the deletion. This is not rollback or a target gas observation. -/
theorem reached_horizon_timeout (p : Roadmap.Pipeline) :
    ∃ (mid : Heap H) (ym : Source.EMState E0 AΓ) (mm : Machine),
      (Source.execS (Source.SemanticsExamples.G0 p) F0 4 AΓ.length none (.expr assignTerm : Source.RStmt E0 [] false .body AΓ AΓ)
        (assignSource (uintOfNat 1) true).1).run (.nil,sy.2)=(.ok (.normal (assignSource (uintOfNat 1) true).1),(.nil,ym.2)) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 5 AΓ.length none seqItems (assignSource (uintOfNat 1) true).1).run (.nil,sy.2)=
        (.error .timeout,(.nil,ym.2)) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 0 AΓ.length none seqItems (assignSource (uintOfNat 1) true).1).run (.nil,sy.2)=
        (.error .timeout,(.nil,sy.2)) ∧
      run assignCode (assignMachine 1 true)=.ok mm 0 ∧
      [MObj.elems .dyn (hp.get r),MObj.elems .dyn (mid.get r)]=[[true,false,false],[true,true,false]] ∧
      SourceBoolMemoryAt ym 0 mid r .dyn ∧ Source.MemOK E0 SH ym ∧
      (Source.readLoc (E := E0) (Γ := AΓ) F0 (τ := .bool) (.mem 0 1)).run ym=(.ok (.bool true),ym) := by
  have hr : SourceBoolMemoryAt (assignSource (uintOfNat 1) true) 0 (assignState (uintOfNat 1) true).heap r .dyn := represented
  obtain ⟨mid,ym,mm,hw,he,hs,hi,hc,hr1,hm1,hmem,hy,hstack,ha⟩ :=
    resolved_assign_word (Source.SemanticsExamples.G0 p) F0 0 (assignState (uintOfNat 1) true) r hr
      aroot aindex .here (.there (.there .here)) (.there .here) .here (uintOfNat 1) true
      rfl rfl rfl rfl rfl rfl one_valid assign_repr_one SH (assign_memOK _ _)
  have hshort := source_indexed_delete_horizon_two (Source.SemanticsExamples.G0 p) F0 ym aroot aindex
  have hs2 := source_expr_statement_error (Source.SemanticsExamples.G0 p) F0 2 AΓ.length seqDelete ym ym .timeout hshort
  have htail : (Source.execItems (Source.SemanticsExamples.G0 p) F0 4 AΓ.length none
      (.stmt (.expr seqDelete) .nil : Source.RItems E0 [] false .body AΓ AΓ) ym.1).run (.nil,ym.2)=(.error .timeout,(.nil,ym.2)) := by
    rw [Source.execItems,Source.Hoare.run_bind,hs2]
  have hs' : (Source.execS (Source.SemanticsExamples.G0 p) F0 4 AΓ.length none
      (.expr assignTerm : Source.RStmt E0 [] false .body AΓ AΓ) (assignSource (uintOfNat 1) true).1).run (.nil,sy.2)=
      (.ok (.normal ym.1),(.nil,ym.2)) := by simpa only [hy] using hs
  have hseq : (Source.execItems (Source.SemanticsExamples.G0 p) F0 5 AΓ.length none seqItems (assignSource (uintOfNat 1) true).1).run (.nil,sy.2)=
      (.error .timeout,(.nil,ym.2)) := by
    rw [seqItems,Source.execItems,Source.Hoare.run_bind,hs']
    change (Source.execItems (Source.SemanticsExamples.G0 p) F0 4 AΓ.length none
      (.stmt (.expr seqDelete) .nil : Source.RItems E0 [] false .body AΓ AΓ) ym.1 >>= fun o => Source.EM.lift (o.up AΓ)).run (.nil,ym.2)=_
    rw [Source.Hoare.run_bind,htail]
  have hv : MObj.elems .dyn (mid.get r)=[true,true,false] := by
    rw [indexedWrite_elems _ _ _ _ _ _ hw]
    simp only [assignState,indexedState,State.push,σ,Heap.get,Objs.get,hp,r,MObj.elems_dyn];rfl
  have hh : ym.2.heap.get 0=some ⟨.array .memory .bool none,sourceBoolMemory [true,true,false]⟩ := by rw [←hv];exact hr1
  refine ⟨mid,ym,mm,hs,hseq,rfl,hc,?_,hr1,hmem,source_bool_read ym 0 _ hh 1 (by decide)⟩
  rw [hv];simp only [Heap.get,Objs.get,hp,r,MObj.elems_dyn]

/-- info: 'Solidity.Backend.MemoryOps.SourceTargetControls.reached_disjoint_cells' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reached_disjoint_cells
/-- info: 'Solidity.Backend.MemoryOps.SourceTargetControls.reached_endpoint_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reached_endpoint_failure
/-- info: 'Solidity.Backend.MemoryOps.SourceTargetControls.reached_horizon_timeout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms reached_horizon_timeout


/-- Same input, different executed order: final alias observations and word
outputs differ. This is a real noncommutation control, not an evaluator oracle. -/
theorem sequence_order_counterexample (p : Roadmap.Pipeline) :
    ∃ (zf zr : Source.EMState E0 AΓ) (mf mr : Machine),
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 AΓ.length none seqItems (assignSource (uintOfNat 1) true).1).run (.nil,sy.2)=
        (.ok (.normal (assignSource (uintOfNat 1) true).1),(.nil,zf.2)) ∧
      (Source.execItems (Source.SemanticsExamples.G0 p) F0 6 AΓ.length none reverseItems (assignSource (uintOfNat 1) true).1).run (.nil,sy.2)=
        (.ok (.normal (assignSource (uintOfNat 1) true).1),(.nil,zr.2)) ∧
      run (assignCode ++ seqDeleteCode) (assignMachine 1 true)=.ok mf 0 ∧
      run (seqDeleteCode ++ assignCode) (assignMachine 1 true)=.ok mr 0 ∧
      (Source.readLoc (E := E0) (Γ := AΓ) F0 (τ := .bool) (.mem 0 1)).run zf=(.ok (.bool false),zf) ∧
      (Source.readLoc (E := E0) (Γ := AΓ) F0 (τ := .bool) (.mem 0 1)).run zr=(.ok (.bool true),zr) ∧
      mf.mem 18=w[0] ∧ mr.mem 18=w[1] ∧ mf.mem 18≠mr.mem 18 := by
  obtain ⟨_,_,_,zf,_,mf,_,_,_,_,hsf,_,_,_,hcf,_,hwf,_,_,_,_,_,_,hrf,_⟩ := reached_assignment_delete p
  obtain ⟨_,_,_,zr,_,mr,_,_,_,_,hsr,_,_,_,hcr,_,hwr,_,_,_,_,_,_,hrr,_⟩ := reached_delete_assignment p
  have hf := congrArg (fun rows : List (List Word) => rows[2]?.bind (fun row => row[7]?)) hwf
  have hr := congrArg (fun rows : List (List Word) => rows[2]?.bind (fun row => row[7]?)) hwr
  simp only [seqCells,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.bind_some] at hf hr
  have hf' : mf.mem 18=w[0] := Option.some.inj hf
  have hr' : mr.mem 18=w[1] := Option.some.inj hr
  refine ⟨zf,zr,mf,mr,hsf,hsr,hcf,hcr,hrf,hrr,hf',hr',?_⟩
  rw [hf',hr']
  decide
/-- info: 'Solidity.Backend.MemoryOps.SourceTargetControls.sequence_order_counterexample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms sequence_order_counterexample

end Solidity.Backend.MemoryOps.SourceTargetControls
