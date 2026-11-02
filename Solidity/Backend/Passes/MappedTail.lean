import Solidity.Backend.Passes.EmittedTail
import Solidity.Backend.Passes.MappedSequence

/-! Stack transport retains a fixed actual output address-map witness.
This changes only proof witnesses over the existing branch-specific Rep. -/
namespace Solidity.Backend.Passes
open Solidity.Evm Solidity.Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ}

/-- Both machine stack fields may change while the exact same selected map,
typed heap, allocator implications and fragment stay represented. -/
theorem mapped_output_stack (result : Compilation b F P)
    {base outBase : Nat → Fin W} {σ : State C Γ} {initial : Machine}
    {τ : State C Δ} {out : Machine}
    (h : MappedOutput result L frame base σ initial τ out outBase)
    (entryTail resultTail : List Word) :
    MappedOutput result L frame base σ {initial with stack := entryTail}
      τ {out with stack := resultTail} outBase := by
  cases result with
  | core frag cert => exact ⟨h.1, h.2.stack resultTail⟩
  | memory result =>
    refine ⟨h.1.stack resultTail, h.2.1, ?_⟩
    intro cursor hb ha hs
    exact (h.2.2 cursor hb (ha.mem_eq rfl) hs).mem_eq rfl
  | referenceArrays result => exact ⟨h.1, h.2.state.stack resultTail, h.2.arrays.stack resultTail⟩
  | objects result =>
    refine ⟨h.1, ⟨h.2.1.core.stack resultTail, h.2.1.heap.stack resultTail,
      h.2.1.pointers, h.2.1.locals⟩, ?_⟩
    intro cursor hb ha
    exact (h.2.2 cursor hb (ha.mem_eq rfl)).mem_eq rfl
  | construction result =>
    refine ⟨⟨h.1.core.stack resultTail, h.1.heap.stack resultTail,
      h.1.pointers, h.1.locals⟩, h.2.1, ?_⟩
    intro cursor hb ha hs
    exact (h.2.2 cursor hb (ha.mem_eq rfl) hs).mem_eq rfl
  | memoryLoops result =>
    rcases h with ⟨amount,ext,hcost,hstate,hbase,hgrowth⟩
    refine ⟨amount,ext,hcost,hstate.stack resultTail,hbase,?_⟩
    intro cursor hb ha hs
    exact (hgrowth cursor hb (ha.mem_eq rfl) hs).mem_eq rfl
  | memoryLoopScopes result =>
    rcases h with ⟨amount,ext,hcost,hstate,hbase,hgrowth⟩
    refine ⟨amount,ext,hcost,hstate.stack resultTail,hbase,?_⟩
    intro cursor hb ha hs
    exact (hgrowth cursor hb (ha.mem_eq rfl) hs).mem_eq rfl
  | memoryCalls result pushFree =>
    refine ⟨h.1.stack resultTail, h.2.1, ?_⟩
    intro cursor hb ha hs
    exact (h.2.2 cursor hb (ha.mem_eq rfl) hs).mem_eq rfl
  | memoryCopy result =>
    refine ⟨h.1.stack resultTail, h.2.1, ?_⟩
    intro cursor hb ha hs
    exact (h.2.2 cursor hb (ha.mem_eq rfl) hs).mem_eq rfl
  | fixedMemory result =>
    exact ⟨h.1, ⟨h.2.1.legacy.stack resultTail, h.2.1.fixed.mem_eq rfl⟩, h.2.2.1, h.2.2.2⟩
  | copyConstruction result =>
    refine ⟨⟨h.1.core.stack resultTail, h.1.heap.stack resultTail,
      h.1.pointers, h.1.locals⟩, h.2.1, ?_⟩
    intro cursor hb ha hs
    exact (h.2.2 cursor hb (ha.mem_eq rfl) hs).mem_eq rfl


/-- One canonical non-stack machine AND one fixed selected output map work
for every saved tail. Actual equality still comes from execution, not Rep. -/
theorem compilation_success_shared_mapped (result : Compilation b F P)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : result.Input L frame base σ m) (hp : Evm.Prog.pays P = false)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o) :
    ∃ canonical outBase, run result.code {m with stack := []} = .ok canonical 0 ∧
      canonical.stack = [] ∧ ∀ tail,
        run result.code {m with stack := tail} = .ok {canonical with stack := tail} 0 ∧
        MappedOutput result (L + Evm.Prog.pushes P) frame base σ {m with stack := tail}
          o.st {canonical with stack := tail} outBase := by
  obtain ⟨canonical, ht, hstack, hr⟩ := compilation_success_tail result hi hp hs []
  obtain ⟨outBase, hm⟩ :=
    (mapped_output_iff result _ _ _ _ _ _ _).mp hr
  refine ⟨canonical, outBase, ht, hstack, ?_⟩
  intro tail
  have he := compilation_tail_exact result hi hp tail
  rw [ht] at he
  exact ⟨he, mapped_output_stack result hm tail tail⟩

end Solidity.Backend.Passes
