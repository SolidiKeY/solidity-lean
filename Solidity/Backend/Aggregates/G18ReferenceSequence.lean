import Solidity.Backend.Aggregates.G18Memory
import Solidity.Backend.MemoryOps.SourceReferenceWrite

/-! Actual pointer rebinding followed by mutation of its reached selected child.
No allocation, source profile change, byte-EVM or post-decoder claim is made. -/
namespace Solidity.Backend.Aggregates
open MemoryOps

/-- Compose the published pointer-slot write with the owned reached-child
consumer. Local separation is needed only from the child actually mutated;
other aliases need not be pairwise distinct. -/
theorem rebind_then_mutate {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {a : Nat} (σ : State C Δ) (r : HRef σ.H BoolRefsRef)
    (address : Nat → Nat) (hr : SourceBoolRefsAt y a σ.heap r address)
    (v : HRef σ.H (.array (.prim .bool)))
    (hv : SourceBoolMemoryAt y (address v.id) σ.heap v .dyn)
    (sep : ∀ t ∈ MObj.elems .dyn (σ.heap.get r),t.id≠v.id → address t.id≠address v.id)
    (Fsrc : Source.Fr) (fuel : Nat) (i j : Fin Evm.W) (value : Bool)
    (hi : i.val<σ.heap.len r .dyn) (hj : j.val<σ.heap.len v .dyn)
    (SH : Source.HeapTy) (hmk : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    let m₁ := Evm.Memory.writeMachine m ((base r.id).val+1+i.val) (.val (base v.id))
    let m₂ := Evm.Memory.writeMachine m₁ ((base v.id).val+1+j.val) (.val (Evm.bword value))
    ∃ (mid out : Heap σ.H) (z w : Source.EMState E Γ),
      σ.heap.writeAddr (.index r .dyn (Evm.Memory.indexValue i)) v=some mid ∧
      mid.writeAddr (.index v .dyn (Evm.Memory.indexValue j)) value=some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc fuel
        (.mem (τ := .array .memory .bool none) a i.val) (.memRef rfl (address v.id))).run y=(.ok (),z) ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc fuel
        (.mem (address v.id) j.val) (.bool value)).run z=(.ok (),w) ∧
      Evm.run (Evm.Memory.writeArrayCode (base r.id))
        ((m.push (.val (base v.id))).push (.val i))=.ok m₁ 0 ∧
      Evm.run (Evm.Memory.writeArrayCode (base v.id))
        ((m₁.push (.val (Evm.bword value))).push (.val j))=.ok m₂ 0 ∧
      SourceBoolRefsAt w a out r address ∧ Source.MemOK E SH w ∧
      Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap out) base m₂ ∧
      z.1=y.1 ∧ w.1=y.1 ∧
      MObj.elems .dyn (out.get r)=(MObj.elems .dyn (σ.heap.get r)).set i.val v ∧
      (∀ t : HRef σ.H (.array (.prim .bool)),t.id≠v.id → out.get t=σ.heap.get t) ∧
      (∀ (x k : Fin Evm.W) (t : HRef σ.H (.array (.prim .bool))) (val : Bool),
        out.index r .dyn (Evm.Memory.indexValue x)=some t →
        out.index t .dyn (Evm.Memory.indexValue k)=some val →
        (Source.readLoc (E := E) (Γ := Γ) Fsrc (τ := .array .memory .bool none)
          (.mem a x.val)).run w=(.ok (.memRef rfl (address t.id)),w) ∧
        (Source.readLoc (E := E) (Γ := Γ) Fsrc (τ := .bool)
          (.mem (address t.id) k.val)).run w=(.ok (.bool val),w) ∧
        m₂.mem ((base r.id).val+1+x.val)=.val (base t.id) ∧
        m₂.mem ((base t.id).val+1+k.val)=.val (Evm.bword val) ∧
        Evm.run (Evm.Memory.readArrayCode (base r.id)) (m₂.push (.val x))=
          .ok (m₂.push (.val (base t.id))) 0 ∧
        Evm.run (Evm.Memory.readArrayCode (base t.id)) (m₂.push (.val k))=
          .ok (m₂.push (.val (Evm.bword val))) 0) := by
  obtain ⟨mid,z,ht,hs,hw,hr₁,hm₁,hw₁,hl₁,he,hchildren,_,_⟩ :=
    hr.write_reference_word σ r address v hv Fsrc fuel i hi SH hmk hm
  have hvlen : mid.len v .dyn=σ.heap.len v .dyn := by
    unfold Heap.len
    rw [hchildren v]
  have selected : v ∈ MObj.elems .dyn (mid.get r) := by
    rw [he]
    exact List.mem_set hi v
  have sep₁ : ∀ t ∈ MObj.elems .dyn (mid.get r),t.id≠v.id → address t.id≠address v.id := by
    intro t ht hn
    rw [he] at ht
    rcases List.mem_or_eq_of_mem_set ht with ht | ht
    · exact sep t ht hn
    · subst t
      exact (hn rfl).elim
  obtain ⟨out,w,ht₂,hs₂,hw₂,hr₂,hm₂,hwrep₂,hl₂,hparent,_⟩ :=
    nested_write_observe (σ.withHeap mid) r address hr₁ v selected sep₁ Fsrc fuel j value
      (by simpa only [State.withHeap,hvlen] using hj) SH hm₁ hw₁
  have hout : out=mid.set v (MObj.setElem .dyn (mid.get v) j.val value) := by
    have hk : mid.writeAddr (.index v .dyn (Evm.Memory.indexValue j)) value=
        some (mid.set v (MObj.setElem .dyn (mid.get v) j.val value)) := by
      simp only [Heap.writeAddr,Heap.setIndex,Evm.Memory.indexValue,Int.toNat_natCast]
      exact if_pos (by change j.val<mid.len v .dyn;rw [hvlen];exact hj)
    exact Option.some.inj (ht₂.symm.trans hk)
  refine ⟨mid,out,z,w,ht,ht₂,hs,hs₂,hw,hw₂,hr₂,hm₂,hwrep₂,hl₁,hl₂.trans hl₁,?_,?_,?_⟩
  · rw [hparent]
    exact he
  · intro t hn
    rw [hout,Heap.get_set_ne mid v t (Ne.symm hn)]
    exact hchildren t
  · intro x k t val hx hk
    exact hr₂.word_observe hwrep₂ Fsrc x k t val hx hk
end Solidity.Backend.Aggregates
