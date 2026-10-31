import Solidity.Backend.MemoryOps.SourceDeleteTarget
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

/-- info: 'Solidity.Backend.MemoryOps.SourceTargetControls.delete_three_views' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms delete_three_views
/-- info: 'Solidity.Backend.MemoryOps.SourceTargetControls.delete_word_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms delete_word_endpoint
end Solidity.Backend.MemoryOps.SourceTargetControls
