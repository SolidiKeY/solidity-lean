import Solidity.Backend.MemoryOps.SourceDelete
import Solidity.Evm.MemoryDelete

/-! Compose the independent Source primitive delete with the PUBLISHED symbolic
word-memory compiler certificate. Initial machine representation is explicit;
physical byte-memory, source syntax compilation and general references stay open. -/
namespace Solidity.Backend.MemoryOps

theorem source_delete_word_target {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (σ : State C Δ)
    (r : HRef σ.H (.array (.prim .bool))) (hr : SourceBoolMemoryAt y address σ.heap r .dyn)
    (Fsrc : Source.Fr) (fuel : Nat) (j : Idx Δ (.mem (.array (.prim .bool))))
    (hj : TEnv.get j σ.env=some r) (i : Val C Δ .uint) (k : PrimTy.uint.Denote)
    (he : i.evalT σ=.ok k) (hk : k.1.toNat<σ.heap.len r .dyn)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (hi : Evm.valIn F i=true) :
    ∃ (out : Heap σ.H) (z : Source.EMState E Γ) (target : Evm.Machine),
      σ.heap.writeAddr (.index r .dyn k) (PrimTy.dflt .bool)=some out ∧
      TRun.deleteMem (.loc (.index .dyn (.var j rfl) i)) σ=.ok ⟨σ.withHeap out,List.prefix_refl _⟩ ∧
      (Source.deleteLoc (E := E) (Γ := Γ) Fsrc (fuel+1) (τ := .bool) (.mem address k.1.toNat)).run y=(.ok (),z) ∧
      Evm.run (Evm.Memory.deleteLocalCode b j (Evm.compileVal b i)) m=.ok target 0 ∧
      SourceBoolMemoryAt z address out r .dyn ∧
      Evm.Memory.StateRepr L b frame F (σ.withHeap out) base target ∧
      target.stack=m.stack ∧ Evm.Memory.KeepsAllocator b frame σ base m (σ.withHeap out) target := by
  obtain ⟨out,z,hw,hclear,hsource,hrepr⟩ := SourceBoolMemoryAt.clearT σ r .dyn hr Fsrc fuel k hk
  have hdelete : TRun.deleteMem (.loc (.index .dyn (.var j rfl) i)) σ=
      .ok ⟨σ.withHeap out,List.prefix_refl _⟩ := by
    simp only [TRun.deleteMem,MLoc.addrT,MPath.mvalT,hj,he,bind,Except.bind,pure,Except.pure]
    exact hclear
  have htarget := Evm.Memory.deleteLocalValue_correct hm j i (Evm.compileVal b i)
    (fun hm' => Evm.val_sim i hm'.core hi)
  rw [hdelete] at htarget
  rcases htarget with ⟨o,m',heq,hrun,hstate,hstack,halloc⟩ | ⟨hbad,_⟩
  · cases Except.ok.inj heq
    exact ⟨out,z,m',hw,hdelete,hsource,hrun,hrepr,hstate,hstack,halloc⟩
  · cases hbad

/-- Exact separate rejection observations. This does not identify the Source
panic payload with an EVM returndata encoding: the word certificate has only
its published revert observation. -/
theorem source_delete_word_bounds {E : Source.Env} {Γ : Source.RCtx} {C : Contract} {Δ : Ctx}
    {y : Source.EMState E Γ} {address : Nat} (σ : State C Δ)
    (r : HRef σ.H (.array (.prim .bool))) (hr : SourceBoolMemoryAt y address σ.heap r .dyn)
    (Fsrc : Source.Fr) (fuel : Nat) (j : Idx Δ (.mem (.array (.prim .bool))))
    (hj : TEnv.get j σ.env=some r) (i : Val C Δ .uint) (k : PrimTy.uint.Denote)
    (he : i.evalT σ=.ok k) (hk : σ.heap.len r .dyn≤k.1.toNat)
    {L b frame : Nat} {F : Evm.Frag Δ} {base : Nat → Fin Evm.W} {m : Evm.Machine}
    (hm : Evm.Memory.StateRepr L b frame F σ base m) (hi : Evm.valIn F i=true) :
    (Source.deleteLoc (E := E) (Γ := Γ) Fsrc (fuel+1) (τ := .bool) (.mem address k.1.toNat)).run y=
      (.error (.revert (Source.panicData .index)),y) ∧
      Evm.run (Evm.Memory.deleteLocalCode b j (Evm.compileVal b i)) m=.revert := by
  have hb := hr.delete_bounds Fsrc fuel k hk
  have hdelete : TRun.deleteMem (.loc (.index .dyn (.var j rfl) i)) σ=.error .revert := by
    simp only [TRun.deleteMem,MLoc.addrT,MPath.mvalT,hj,he,bind,Except.bind,pure,Except.pure,
      TRun.clearT,hb.2,TRes.ofOpt]
  have htarget := Evm.Memory.deleteLocalValue_correct hm j i (Evm.compileVal b i)
    (fun hm' => Evm.val_sim i hm'.core hi)
  rw [hdelete] at htarget
  refine ⟨hb.1,?_⟩
  rcases htarget with ⟨o,m',heq,_⟩ | ⟨_,hrun⟩
  · cases heq
  · exact hrun

/-- info: 'Solidity.Backend.MemoryOps.source_delete_word_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_delete_word_target
/-- info: 'Solidity.Backend.MemoryOps.source_delete_word_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms source_delete_word_bounds
end Solidity.Backend.MemoryOps
