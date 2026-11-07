import Solidity.Evm.MemoryLoopHorizonObjectAllocating

/-! Genuine successful source prefixes for the empty-array allocating body.
Each turn executes the actual declaration and accumulates exactly one cell of
construction cost. The source prefix exists for every count, but no physical
allocator room or target execution is inferred without the separate strong
capacity premises. No source evaluator budget is changed. -/
namespace Solidity.Evm.Memory.HorizonObjectAllocating
variable {C : Contract} {Γ : Ctx}

theorem body_run_ok (state : State C Γ) :
    ∃ out, (body : Prog C Γ _).run state = .ok out := by
  exact ⟨_,rfl⟩

theorem prefixes (state : State C Γ) :
    ∀ n, ∃ out, Construction.CountedLoopPrefix (.simple (.bool true)) body state out n n
  | 0 => ⟨_,.start⟩
  | n+1 => by
    obtain ⟨out,hp⟩ := prefixes state n
    obtain ⟨next,step⟩ := body_run_ok out.st
    refine ⟨⟨next.st.drop (body : Prog C Γ _).ext,out.ext.trans next.ext⟩,?_⟩
    simpa only [body_cost] using (Construction.CountedLoopPrefix.next hp rfl step)

theorem source_pending (state : State C Γ) (n : Nat) :
    ∃ out, TLoop.iterN (horizonBody body)
      (fun o => (.simple (.bool true) : Val C Γ .bool).evalT o.st) n
      ⟨state,List.prefix_refl _⟩ = .inl out := by
  obtain ⟨out,hp⟩ := prefixes state n
  exact ⟨out,hp.iterN_eq⟩

end Solidity.Evm.Memory.HorizonObjectAllocating
