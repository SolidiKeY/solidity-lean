import Solidity.Backend.MemoryOps.SourceNestedSelect

/-! A selected-child write frame for the existing finite nested observer.
This frame uses a sufficient INITIAL selected-footprint alias condition.
No-op writes may preserve correspondence without that condition.
This is a local theorem premise, not a source admission restriction/global graph
injection, and no desired reached representation is assumed. -/
namespace Solidity.Backend.MemoryOps

theorem SourceBoolRefsAt.parent_ne_child {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (q : HRef H (.array (.prim .bool)))
    (hq : q∈MObj.elems .dyn (hp.get r)) : parentAddress≠address q.id := by
  have hc := hr.children q hq
  intro he
  rw [←he] at hc
  have ht := congrArg Sigma.fst (Option.some.inj (hr.parent.symm.trans hc))
  cases ht

set_option backward.isDefEq.respectTransparency false in
/-- The existing actual source/intrinsic write preserves the whole selected
parent observer, including repeated aliases to the modified child. Other old
children need only local separation from THIS written address; they need not be
pairwise distinct. No stagewise/final preservation premise appears. -/
theorem SourceBoolRefsAt.write_child {E : Source.Env} {Γ : Source.RCtx} {H : HTy}
    {y : Source.EMState E Γ} {parentAddress : Nat} {hp : Heap H} {r : HRef H BoolRefsRef}
    {address : Nat → Nat} (hr : SourceBoolRefsAt y parentAddress hp r address)
    (q : HRef H (.array (.prim .bool))) (hq : q∈MObj.elems .dyn (hp.get r))
    (hsep : ∀ t∈MObj.elems .dyn (hp.get r), t.id≠q.id → address t.id≠address q.id)
    (F : Source.Fr) (fuel : Nat) (i : PrimTy.uint.Denote) (v : Bool)
    (hi : i.1.toNat<hp.len q .dyn) (SH : Source.HeapTy) (hm : Source.MemOK E SH y) :
    ∃ (out : Heap H) (z : Source.EMState E Γ),
      hp.writeAddr (.index q .dyn i) v=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem (address q.id) i.1.toNat) (.bool v)).run y=(.ok (),z) ∧
      SourceBoolRefsAt z parentAddress out r address ∧ Source.MemOK E SH z ∧
      z.1=y.1 ∧ out.get r=hp.get r := by
  have hc := hr.children q hq
  let values := MObj.elems .dyn (hp.get q)
  obtain ⟨ht,hw⟩ := source_bool_write y (address q.id) values hc i.1.toNat hi v
  let out := hp.set q (MObj.setElem .dyn (hp.get q) i.1.toNat v)
  let z : Source.EMState E Γ :=
    (y.1,{y.2 with heap := y.2.heap.write (address q.id) (sourceBoolMemory (values.set i.1.toNat v)) ht})
  have hqr : q.id≠r.id := by
    intro he
    cases (HRef.heq_of_id q r he).1
  have hparent : out.get r=hp.get r := Heap.get_set_ne hp q r hqr _
  have hs : (Source.writeLoc (E := E) (Γ := Γ) F fuel (.mem (address q.id) i.1.toNat) (.bool v)).run y=(.ok (),z) := hw
  have hmk := Source.writeLoc_memOK (E := E) (Γ := Γ) (H := SH) F fuel
    (.mem (τ := .bool) (address q.id) i.1.toNat) (.bool v) y ⟨hm,trivial⟩
  rw [hs] at hmk
  refine ⟨out,z,?_,hs,⟨?_,?_⟩,hmk,rfl,hparent⟩
  · simp only [Heap.len] at hi
    simp only [Heap.writeAddr,Heap.setIndex,hi,↓reduceIte]
    rfl
  · rw [hparent]
    exact (Source.Heap.write_other y.2.heap (hr.parent_ne_child q hq) _ ht).trans hr.parent
  · intro t hmem
    rw [hparent] at hmem
    by_cases he : t.id=q.id
    · have heq : t=q := eq_of_heq (HRef.heq_of_id t q he).2
      subst t
      unfold SourceBoolMemoryAt
      change (y.2.heap.write _ _ ht).get (address q.id)=some _
      rw [Source.Heap.write_get,Heap.get_set_same,MObj.elems_setElem]
    · unfold SourceBoolMemoryAt
      change (y.2.heap.write _ _ ht).get (address t.id)=some _
      rw [Source.Heap.write_other y.2.heap (hsep t hmem he),Heap.get_set_ne hp q t (Ne.symm he)]
      exact hr.children t hmem


/-- The independently derived whole nested observer frames the SAME actual
primitive write certified by the published word-array operation. -/
theorem SourceBoolRefsAt.write_child_word {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {parentAddress : Nat} (σ : State C Δ) (r : HRef σ.H BoolRefsRef)
    (address : Nat → Nat) (hr : SourceBoolRefsAt y parentAddress σ.heap r address)
    (q : HRef σ.H (.array (.prim .bool))) (hq : q∈MObj.elems .dyn (σ.heap.get r))
    (hsep : ∀ t∈MObj.elems .dyn (σ.heap.get r),t.id≠q.id → address t.id≠address q.id)
    (Fsrc : Source.Fr) (fuel : Nat) (i : Fin Evm.W) (v : Bool)
    (hi : i.val<σ.heap.len q .dyn) (SH : Source.HeapTy) (hmk : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ),
      σ.heap.writeAddr (.index q .dyn (Evm.Memory.indexValue i)) v=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc fuel (.mem (address q.id) i.val) (.bool v)).run y=(.ok (),z) ∧
      Evm.run (Evm.Memory.writeArrayCode (base q.id)) ((m.push (.val (Evm.bword v))).push (.val i))=
        .ok (Evm.Memory.writeMachine m ((base q.id).val+1+i.val) (.val (Evm.bword v))) 0 ∧
      SourceBoolRefsAt z parentAddress out r address ∧ Source.MemOK E SH z ∧
      Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap out) base
        (Evm.Memory.writeMachine m ((base q.id).val+1+i.val) (.val (Evm.bword v))) ∧
      z.1=y.1 ∧ out.get r=σ.heap.get r := by
  obtain ⟨out,z,ho,hs,hr',hm',hl,hparent⟩ := hr.write_child q hq hsep Fsrc fuel (Evm.Memory.indexValue i) v
    (by simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hi) SH hmk
  have he : out=σ.heap.set q (MObj.setElem .dyn (σ.heap.get q) i.val v) := by
    have hw : σ.heap.writeAddr (.index q .dyn (Evm.Memory.indexValue i)) v=
        some (σ.heap.set q (MObj.setElem .dyn (σ.heap.get q) i.val v)) := by
      simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast]
      exact ite_eq_left hi
    exact Option.some.inj (ho.symm.trans hw)
  obtain ⟨_,_,hc,_⟩ | ⟨hn,_⟩ := Evm.Memory.writeArray_correct (hm.state.heap.arrays q) i v (.val (Evm.bword v)) rfl
  · refine ⟨out,z,ho,?_,hc,hr',hm',?_,hl,hparent⟩
    · simpa only [Evm.Memory.indexValue,Int.toNat_natCast] using hs
    · rw [he]
      exact hm.setPrimitive q i.val hi v (.val (Evm.bword v)) rfl
  · rw [ho] at hn;cases hn

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.write_child_word' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.write_child_word

/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.parent_ne_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.parent_ne_child
/-- info: 'Solidity.Backend.MemoryOps.SourceBoolRefsAt.write_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SourceBoolRefsAt.write_child
end Solidity.Backend.MemoryOps
