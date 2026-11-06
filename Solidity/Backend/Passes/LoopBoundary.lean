import Solidity.Backend.Passes.CoreBoundary
import Solidity.Backend.Passes.MappedTail
import Solidity.Evm.MemoryLoopScopeBudget

/-! Exact reached-cost adapters over the published loop certificates. Source
prefix capacity, cost/heap-extension witnesses and actual maps stay correlated.
No loop algorithm, evaluator or representation is introduced here. -/
namespace Solidity.Backend.Passes
open Evm Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}
  {base : Nat → Fin W} {σ : State C Γ} {m : Machine}

/-- Every successful scope cost is zero or an ACTUAL reached allocation demand.
The selected condition and successful prefix runs remain in the constructors. -/
theorem scope_cost_prefix {G : Frag Δ} {code : List Instr}
    {hp : Memory.LoopScopes.ProgCert b F G P code}
    {o : Solidity.Out C σ.H Δ} {amount : Nat}
    (hc : Memory.LoopScopes.Cost hp σ o amount) :
    amount = 0 ∨ Memory.LoopScopes.Demand hp σ amount := by
  induction hc using Memory.LoopScopes.Cost.rec
    (motive_1 := fun {Γ Δ F G s code} hs σ o amount _ =>
      amount = 0 ∨ Memory.LoopScopes.StmtDemand hs σ amount) with
  | base hc =>
    exact .inr (.base (Memory.LoopScopes.base_success_demand _ (.base hc)))
  | block ho hc ih =>
    rcases ih with hz | hd
    · exact .inl hz
    · exact .inr (.block hd)
  | iteTrue hv ho hc ih =>
    rcases ih with hz | hd
    · exact .inl hz
    · exact .inr (.iteTrue hv hd)
  | iteFalse hv ho hc ih =>
    rcases ih with hz | hd
    · exact .inl hz
    · exact .inr (.iteFalse hv hd)
  | nil => exact .inl rfl
  | cons ho hc ht ihs iht =>
    rcases iht with hzTail | hdTail
    · rcases ihs with hz | hd
      · exact .inl (by rw [hz,hzTail])
      · exact .inr (by simpa only [hzTail,Nat.add_zero] using Memory.LoopScopes.Demand.head hd)
    · exact .inr (.tail ho hc hdTail)

theorem scope_cost_allocation_input {G : Frag Δ} {code : List Instr}
    {hp : Memory.LoopScopes.ProgCert b F G P code}
    {o : Solidity.Out C σ.H Δ} {amount : Nat}
    (room : Memory.LoopScopes.Room hp frame σ base m)
    (hc : Memory.LoopScopes.Cost hp σ o amount) :
    Memory.AllocationInput b frame amount σ base m := by
  rcases scope_cost_prefix hc with hz | hd
  · exact .inl hz
  · exact room amount hd

theorem loops_memory_link (left : Memory.Loops.CompiledProg b F P)
    (right : Memory.CompiledProg b left.frag Q)
    (capacity : b + Memory.frameNeedProg Q ≤ frame)
    (nonallocating : Memory.hasAllocation Q = false) :
    MappedBoundaryLink (.memoryLoops left) (.memory right) L frame base σ m := by
  intro o mid selected _ _ output
  rcases output with ⟨amount,ext,hcost,state,hbase,hgrowth⟩
  exact ⟨state,capacity,.inl (Memory.allocationCostProg_zero Q nonallocating o.st)⟩

theorem loops_budgeted_memory_link (left : Memory.Loops.CompiledProg b F P)
    (right : Memory.CompiledProg b left.frag Q)
    (capacity : b + Memory.frameNeedProg Q ≤ frame)
    (budget : ∀ (o : Solidity.Out C σ.H Δ) (amount : Nat) (ext : σ.H <+: o.st.H),
      P.run σ = .ok o → Memory.Loops.Cost left.cert σ ⟨o.st,ext⟩ amount →
      Memory.AllocationInput b frame (amount + right.cert.cost o.st) σ base m) :
    MappedBoundaryLink (.memoryLoops left) (.memory right) L frame base σ m := by
  intro o mid selected hs _ output
  rcases output with ⟨amount,ext,hcost,state,hbase,hgrowth⟩
  exact ⟨state,capacity,hgrowth.nextInput (budget o amount ext hs hcost)⟩

/-- The actual map, cost and extension are ALL selected before forall tail.
No post-fault map or desired preservation equality is a premise. -/
theorem loops_success_shared (out : Memory.Loops.CompiledProg b F P)
    (hi : (Compilation.memoryLoops out).Input L frame base σ m)
    (payment : Evm.Prog.pays P = false) {o : Solidity.Out C σ.H Δ}
    (source : P.run σ = .ok o) :
    ∃ (selected : Nat → Fin W) (amount : Nat) (ext : σ.H <+: o.st.H) (canonical : Machine),
    Memory.Loops.Cost out.cert σ ⟨o.st,ext⟩ amount ∧ canonical.stack = [] ∧ ∀ tail,
    run out.code {m with stack := tail} = .ok {canonical with stack := tail} 0 ∧
    Memory.StateRepr L b frame out.frag o.st selected {canonical with stack := tail} ∧
    Memory.BaseExtends σ.H base selected ∧
    Memory.GrowsAllocator b frame amount σ base {m with stack := tail}
      o.st selected {canonical with stack := tail} ∧
    MappedOutput (.memoryLoops out) L frame base σ {m with stack := tail}
      o.st {canonical with stack := tail} selected := by
  obtain ⟨canonical,ht,hstack,hr⟩ := compilation_success_tail (.memoryLoops out) hi payment source []
  have represented : (Compilation.memoryLoops out).Rep L frame base σ {m with stack := []}
      o.st canonical := by
    simpa only [out.cert.pushes_zero,Nat.add_zero] using hr
  rcases represented with ⟨selected,amount,ext,hcost,state,hbase,hgrowth⟩
  refine ⟨selected,amount,ext,canonical,hcost,hstack,?_⟩
  intro tail
  have he := compilation_tail_exact (Compilation.memoryLoops out) hi payment tail
  rw [ht] at he
  have growth : Memory.GrowsAllocator b frame amount σ base {m with stack := tail}
      o.st selected {canonical with stack := tail} := by
    intro cursor hb ha hs
    exact (hgrowth cursor hb (ha.mem_eq rfl) hs).mem_eq rfl
  exact ⟨he,state.stack tail,hbase,growth,amount,ext,hcost,state.stack tail,hbase,growth⟩

theorem loop_scopes_memory_link (left : Memory.LoopScopes.CompiledProg b F P)
    (right : Memory.CompiledProg b left.frag Q)
    (capacity : b + Memory.frameNeedProg Q ≤ frame)
    (nonallocating : Memory.hasAllocation Q = false) :
    MappedBoundaryLink (.memoryLoopScopes left) (.memory right) L frame base σ m := by
  intro o mid selected _ _ output
  rcases output with ⟨amount,ext,hcost,state,hbase,hgrowth⟩
  exact ⟨state,capacity,.inl (Memory.allocationCostProg_zero Q nonallocating o.st)⟩

theorem loop_scopes_budgeted_memory_link (left : Memory.LoopScopes.CompiledProg b F P)
    (right : Memory.CompiledProg b left.frag Q)
    (capacity : b + Memory.frameNeedProg Q ≤ frame)
    (budget : ∀ (o : Solidity.Out C σ.H Δ) (amount : Nat) (ext : σ.H <+: o.st.H),
      P.run σ = .ok o → Memory.LoopScopes.Cost left.cert σ ⟨o.st,ext⟩ amount →
      Memory.AllocationInput b frame (amount + right.cert.cost o.st) σ base m) :
    MappedBoundaryLink (.memoryLoopScopes left) (.memory right) L frame base σ m := by
  intro o mid selected hs _ output
  rcases output with ⟨amount,ext,hcost,state,hbase,hgrowth⟩
  exact ⟨state,capacity,hgrowth.nextInput (budget o amount ext hs hcost)⟩

/-- The actual map, cost and extension are ALL selected before forall tail.
No post-fault map or desired preservation equality is a premise. -/
theorem loop_scopes_success_shared (out : Memory.LoopScopes.CompiledProg b F P)
    (hi : (Compilation.memoryLoopScopes out).Input L frame base σ m)
    (payment : Evm.Prog.pays P = false) {o : Solidity.Out C σ.H Δ}
    (source : P.run σ = .ok o) :
    ∃ (selected : Nat → Fin W) (amount : Nat) (ext : σ.H <+: o.st.H) (canonical : Machine),
    Memory.LoopScopes.Cost out.cert σ ⟨o.st,ext⟩ amount ∧ canonical.stack = [] ∧ ∀ tail,
    run out.code {m with stack := tail} = .ok {canonical with stack := tail} 0 ∧
    Memory.StateRepr L b frame out.frag o.st selected {canonical with stack := tail} ∧
    Memory.BaseExtends σ.H base selected ∧
    Memory.GrowsAllocator b frame amount σ base {m with stack := tail}
      o.st selected {canonical with stack := tail} ∧
    MappedOutput (.memoryLoopScopes out) L frame base σ {m with stack := tail}
      o.st {canonical with stack := tail} selected := by
  obtain ⟨canonical,ht,hstack,hr⟩ := compilation_success_tail (.memoryLoopScopes out) hi payment source []
  have represented : (Compilation.memoryLoopScopes out).Rep L frame base σ {m with stack := []}
      o.st canonical := by
    simpa only [out.cert.pushes_zero,Nat.add_zero] using hr
  rcases represented with ⟨selected,amount,ext,hcost,state,hbase,hgrowth⟩
  refine ⟨selected,amount,ext,canonical,hcost,hstack,?_⟩
  intro tail
  have he := compilation_tail_exact (Compilation.memoryLoopScopes out) hi payment tail
  rw [ht] at he
  have growth : Memory.GrowsAllocator b frame amount σ base {m with stack := tail}
      o.st selected {canonical with stack := tail} := by
    intro cursor hb ha hs
    exact (hgrowth cursor hb (ha.mem_eq rfl) hs).mem_eq rfl
  exact ⟨he,state.stack tail,hbase,growth,amount,ext,hcost,state.stack tail,hbase,growth⟩

end Solidity.Backend.Passes
