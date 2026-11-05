import Solidity.Backend.MemoryOps.SourceNestedMutation

/-! G18.03: actual source write, actual emitted word write, and ALL subsequent
selected alias observations over the reached representation. This consumes the
published initial SourceBoolRefsAt; it neither certifies declaration admission
nor assumes a desired reached simulation. The layout and initial typed observer
are inputs. -/
namespace Solidity.Backend.Aggregates
open MemoryOps

/-- A write preserves the complete nested observer, so every represented
selection (including repeated references to the modified child) can immediately
be read on both machines. No reached representation is a premise. -/
theorem nested_write_observe {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {parentAddress : Nat} (σ : State C Δ)
    (r : HRef σ.H BoolRefsRef) (address : Nat → Nat)
    (hr : SourceBoolRefsAt y parentAddress σ.heap r address)
    (q : HRef σ.H (.array (.prim .bool)))
    (hq : q ∈ MObj.elems .dyn (σ.heap.get r))
    (hsep : ∀ t ∈ MObj.elems .dyn (σ.heap.get r), t.id ≠ q.id → address t.id ≠ address q.id)
    (Fsrc : Source.Fr) (fuel : Nat) (i : Fin Evm.W) (v : Bool)
    (hi : i.val < σ.heap.len q .dyn) (SH : Source.HeapTy) (hmk : Source.MemOK E SH y)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.RefArrayStateRepr L b frame F σ base m) :
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ),
      σ.heap.writeAddr (.index q .dyn (Evm.Memory.indexValue i)) v = some out ∧
      (Source.writeLoc (E := E) (Γ := Γ) Fsrc fuel (.mem (address q.id) i.val) (.bool v)).run y = (.ok (), z) ∧
      Evm.run (Evm.Memory.writeArrayCode (base q.id)) ((m.push (.val (Evm.bword v))).push (.val i)) =
        .ok (Evm.Memory.writeMachine m ((base q.id).val+1+i.val) (.val (Evm.bword v))) 0 ∧
      SourceBoolRefsAt z parentAddress out r address ∧ Source.MemOK E SH z ∧
      Evm.Memory.RefArrayStateRepr L b frame F (σ.withHeap out) base
        (Evm.Memory.writeMachine m ((base q.id).val+1+i.val) (.val (Evm.bword v))) ∧
      z.1 = y.1 ∧ out.get r = σ.heap.get r ∧
      ∀ (a j : Fin Evm.W) (t : HRef σ.H (.array (.prim .bool))) (w : Bool),
        out.index r .dyn (Evm.Memory.indexValue a) = some t →
        out.index t .dyn (Evm.Memory.indexValue j) = some w →
        (Source.readLoc (E := E) (Γ := Γ) Fsrc (τ := .bool) (.mem (address t.id) j.val)).run z = (.ok (.bool w), z) ∧
        (Evm.Memory.writeMachine m ((base q.id).val+1+i.val) (.val (Evm.bword v))).mem
          ((base r.id).val+1+a.val) = .val (base t.id) ∧
        (Evm.Memory.writeMachine m ((base q.id).val+1+i.val) (.val (Evm.bword v))).mem
          ((base t.id).val+1+j.val) = .val (Evm.bword w) ∧
        Evm.run (Evm.Memory.readArrayCode (base t.id))
          ((Evm.Memory.writeMachine m ((base q.id).val+1+i.val) (.val (Evm.bword v))).push (.val j)) =
          .ok ((Evm.Memory.writeMachine m ((base q.id).val+1+i.val) (.val (Evm.bword v))).push (.val (Evm.bword w))) 0 := by
  obtain ⟨out, z, ho, hs, ht, hr', hmk', hm', hl, hp⟩ :=
    hr.write_child_word σ r address q hq hsep Fsrc fuel i v hi SH hmk hm
  refine ⟨out, z, ho, hs, ht, hr', hmk', hm', hl, hp, ?_⟩
  intro a j t w ha hj
  have obs := hr'.word_observe hm' Fsrc a j t w ha hj
  exact ⟨obs.2.1, obs.2.2.1, obs.2.2.2.1, obs.2.2.2.2.2⟩

#print axioms nested_write_observe
end Solidity.Backend.Aggregates
