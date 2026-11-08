import Solidity.Backend.MemoryOps.SourceNestedDelete

/-! Existing parent reference slots are redirected to an existing represented
Boolean child. This is pointer assignment, not allocation or deep copying.
The finite observer is derived from INITIAL tables; no address injection or
postcorrespondence is assumed. -/
namespace Solidity.Backend.MemoryOps

private theorem refs_congr {D : Source.Layout} {n m : Nat}
    (hn : ∀ k, none=some k → k=n) (hm : ∀ k, none=some k → k=m)
    (f : Fin n → Source.Data D (.array .memory .bool none))
    (g : Fin m → Source.Data D (.array .memory .bool none))
    (hl : n=m) (he : ∀ j : Fin n, f j=g ⟨j.val,by omega⟩) :
    Source.Data.array (l := .memory) (n := none) n hn f=Source.Data.array (l := .memory) (n := none) m hm g := by
  subst m
  have hf : f=g := funext he
  cases hf
  rfl

private theorem sourceRefs_set {D : Source.Layout} {H : HTy} (address : Nat → Nat)
    (rs : List (HRef H (.array (.prim .bool)))) (i : Nat) (v : HRef H (.array (.prim .bool))) :
    sourceBoolRefMemory (D := D) address (rs.set i v)=
      .array rs.length (fun _ h => by cases h)
        (fun j => if j.val=i then .val (.memRef rfl (address v.id))
          else .val (.memRef rfl (address rs[j].id))) := by
  apply refs_congr _ _ _ _ (List.length_set ..)
  intro j
  change Source.Data.val (Source.Val.memRef rfl (address ((rs.set i v)[j.val]).id))=_
  rw [List.getElem_set]
  by_cases hj : i=j.val
  · simp only [hj,↓reduceIte]
  · simp only [hj,Ne.symm hj,↓reduceIte,Fin.getElem_fin]

/-- Executed Source pointer-slot write, with its canonical initial-table-derived
new table. No conversion certificate or desired output relation is an input. -/
theorem source_refs_write {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    (y : Source.EMState E Γ) (a : Nat) (address : Nat → Nat)
    (rs : List (HRef H (.array (.prim .bool))))
    (hr : y.2.heap.get a=some ⟨SourceBoolRefsTy,sourceBoolRefMemory address rs⟩)
    (i : Nat) (hi : i<rs.length) (v : HRef H (.array (.prim .bool))) :
    ∃ (ht : y.2.heap.ty a=some SourceBoolRefsTy),
      (Source.memSet (E := E) (Γ := Γ) a i (τ := .array .memory .bool none) (.memRef rfl (address v.id))).run y=
        (.ok (), (y.1,{y.2 with heap := y.2.heap.write a (sourceBoolRefMemory address (rs.set i v)) ht})) := by
  have ht : y.2.heap.ty a=some SourceBoolRefsTy := by
    change (y.2.heap.get a).map Sigma.fst=some _
    rw [hr]; rfl
  refine ⟨ht,?_⟩
  rw [Source.memSet,Source.Hoare.run_bind,source_heapObj_run y a _ hr]
  simp only [sourceBoolRefMemory,hi,↓reduceDIte]
  rw [←sourceRefs_set address rs i v]
  simp only [Source.heapPut,Source.Hoare.run_bind]
  rw [show (Source.EM.st (E := E) (Γ := Γ)).run y=(.ok y.2,y) from rfl]
  simp only [ht,↓reduceDIte]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Redirecting a parent slot changes no Boolean object, including retained old
aliases and the newly selected child. Type separation supplies the necessary
parent/child address inequality; no global injection is required. -/
theorem SourceBoolRefsAt.write_reference {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {a : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y a hp r address)
    (v : HRef H (.array (.prim .bool))) (hv : SourceBoolMemoryAt y (address v.id) hp v .dyn)
    (F : Source.Fr) (fuel : Nat) (i : Fin Evm.W) (hi : i.val<hp.len r .dyn)
    (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index r .dyn (Evm.Memory.indexValue i)) v=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem (τ := .array .memory .bool none) a i.val) (.memRef rfl (address v.id))).run y=(.ok (),z) ∧
      SourceBoolRefsAt z a out r address ∧ Source.MemOK E SH z ∧ z.1=y.1 ∧
      MObj.elems .dyn (out.get r)=(MObj.elems .dyn (hp.get r)).set i.val v ∧
      (∀ q : HRef H (.array (.prim .bool)),out.get q=hp.get q) ∧
      (∀ q, SourceBoolMemoryAt y (address q.id) hp q .dyn → SourceBoolMemoryAt z (address q.id) out q .dyn) ∧
      (z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals) := by
  let rs := MObj.elems .dyn (hp.get r)
  obtain ⟨ht,hw⟩ := source_refs_write y a address rs hr.parent i.val hi v
  let out := hp.set r (MObj.setElem .dyn (hp.get r) i.val v)
  let z : Source.EMState E Γ :=
    (y.1,{y.2 with heap := y.2.heap.write a (sourceBoolRefMemory address (rs.set i.val v)) ht})
  have child_frame : ∀ q : HRef H (.array (.prim .bool)),out.get q=hp.get q := by
    intro q
    apply Heap.get_set_ne
    intro he
    cases (HRef.heq_of_id r q he).1
  have hs : (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem (τ := .array .memory .bool none) a i.val) (.memRef rfl (address v.id))).run y=(.ok (),z) := hw
  have hvty : y.2.heap.ty (address v.id)=some (.array .memory .bool none) := by
    change (y.2.heap.get (address v.id)).map Sigma.fst=some _
    rw [hv];rfl
  have hmk := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) F fuel
    (.mem (τ := .array .memory .bool none) a i.val) (.memRef rfl (address v.id)) y ⟨hm,⟨_,hvty,rfl⟩⟩
  rw [hs] at hmk
  have elems : MObj.elems .dyn (out.get r)=rs.set i.val v := by
    simp only [out,Heap.get_set_same,MObj.elems_setElem]
    rfl
  refine ⟨out,z,?_,hs,⟨?_,?_⟩,hmk,rfl,elems,child_frame,?_,⟨rfl,rfl,rfl,rfl⟩⟩
  · simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast]
    exact ite_eq_left hi
  · change (y.2.heap.write _ _ ht).get a=some _
    rw [Source.Heap.write_get,elems]
  · intro q hq
    rw [elems] at hq
    have hc : SourceBoolMemoryAt y (address q.id) hp q .dyn := by
      rcases List.mem_or_eq_of_mem_set hq with hq | hq
      · exact hr.children q hq
      · subst q;exact hv
    have hne : address q.id≠a := by
      intro he
      rw [he] at hc
      have ht' := congrArg Sigma.fst (Option.some.inj (hr.parent.symm.trans hc))
      cases ht'
    unfold SourceBoolMemoryAt
    change (y.2.heap.write _ _ ht).get (address q.id)=some _
    rw [Source.Heap.write_other y.2.heap hne,child_frame]
    exact hc
  · intro q hc
    have hne : address q.id≠a := by
      intro he
      rw [he] at hc
      have ht' := congrArg Sigma.fst (Option.some.inj (hr.parent.symm.trans hc))
      cases ht'
    unfold SourceBoolMemoryAt
    change (y.2.heap.write _ _ ht).get (address q.id)=some _
    rw [Source.Heap.write_other y.2.heap hne,child_frame]
    exact hc


/-- The same actual write consumes the published reference-array word
certificate and its full state preservation theorem. -/
theorem SourceBoolRefsAt.write_reference_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (σ : State C Δ) (r : HRef σ.H BoolRefsRef)
    (address : Nat → Nat) (hr : SourceBoolRefsAt y a σ.heap r address)
    (v : HRef σ.H (.array (.prim .bool))) (hv : SourceBoolMemoryAt y (address v.id) σ.heap v .dyn)
    (Fsrc : Source.Fr) (fuel : Nat) (i : Fin Evm.W) (hi : i.val<σ.heap.len r .dyn)
    (SH : Source.HeapTy) (hmk : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ),
      σ.heap.writeAddr (.index r .dyn (Evm.Memory.indexValue i)) v=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc fuel (.mem (τ := .array .memory .bool none) a i.val) (.memRef rfl (address v.id))).run y=(.ok (),z) ∧
      Evm.run (Evm.Memory.writeArrayCode (base r.id)) ((m.push (.val (base v.id))).push (.val i))=
        .ok (Evm.Memory.writeMachine m ((base r.id).val+1+i.val) (.val (base v.id))) 0 ∧
      SourceBoolRefsAt z a out r address ∧ Source.MemOK E SH z ∧
      Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap out) base
        (Evm.Memory.writeMachine m ((base r.id).val+1+i.val) (.val (base v.id))) ∧
      z.1=y.1 ∧ MObj.elems .dyn (out.get r)=(MObj.elems .dyn (σ.heap.get r)).set i.val v ∧
      (∀ q : HRef σ.H (.array (.prim .bool)),out.get q=σ.heap.get q) ∧
      (∀ q, SourceBoolMemoryAt y (address q.id) σ.heap q .dyn → SourceBoolMemoryAt z (address q.id) out q .dyn) ∧
      (z.2.ex=y.2.ex ∧ z.2.events=y.2.events ∧ z.2.logs=y.2.logs ∧ z.2.fnLocals=y.2.fnLocals) := by
  obtain ⟨out,z,ho,hs,hr',hm',hl,he,hchildren,hsource,heffects⟩ := hr.write_reference v hv Fsrc fuel i hi SH hmk
  have hout : out=σ.heap.set r (MObj.setElem .dyn (σ.heap.get r) i.val v) := by
    have hw : σ.heap.writeAddr (.index r .dyn (Evm.Memory.indexValue i)) v=
        some (σ.heap.set r (MObj.setElem .dyn (σ.heap.get r) i.val v)) := by
      simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast]
      exact ite_eq_left hi
    exact Option.some.inj (ho.symm.trans hw)
  obtain ⟨_,_,hc,_⟩ | ⟨hn,_⟩ := (hm.arrays.arrays r).write i v
  · exact ⟨out,z,ho,hs,hc,hr',hm',hout ▸ hm.setReference r i.val hi v,hl,he,hchildren,hsource,heffects⟩
  · rw [ho] at hn;cases hn

/-- info: 'Solidity.Backend.MemoryOps.source_refs_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_refs_write

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.write_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.write_reference

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.write_reference_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.write_reference_word

end Solidity.Backend.MemoryOps
