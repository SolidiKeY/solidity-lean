import Solidity.Evm.MemoryLoopScopeCompile
import Solidity.Backend.InternalFlow.PublishedDirectCalls
import Solidity.Backend.InternalFlow.ScopedLoopFrame

/-! Consumers of published loop certificates. Room/Cost remain distinct from
legacy finite allocationCost. Mutated old objects are not claimed unchanged. -/
namespace Solidity.Backend.InternalFlow.PublishedLoops
open Evm Evm.Memory
variable {C : Contract}

/-- Pin actual source success, including the reached relational cost. -/
theorem direct_endpoint {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : Loops.ProgCert b F G P code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (frameRoom : b + hp.need ≤ frame)
    (capacity : Loops.Room hp frame σ base m)
    (out : Solidity.Out C σ.H Δ) (executed : P.run σ = .ok out) :
    ∃ m' base' cost, run code m = .ok m' 0 ∧ Loops.Cost hp σ out cost ∧
      StateRepr L b frame G out.st base' m' ∧ m'.stack = m.stack ∧
      BaseExtends σ.H base base' ∧ GrowsAllocator b frame cost σ base m out.st base' m' := by
  rcases hp.correct repr frameRoom capacity with ⟨o,m',base',cost,hs,ht,hc,hr,hk,he,hg⟩ | ⟨hs,ht⟩ | ⟨hs,ht⟩
  · have same : o = out := Except.ok.inj (hs.symm.trans executed)
    subst o
    exact ⟨m',base',cost,ht,hc,hr,hk,he,hg⟩
  · rw [executed] at hs; contradiction
  · rw [executed] at hs; contradiction

/-- Exact revert; divergence is abstract fault, never successful exhaustion. -/
theorem direct_revert {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : Loops.ProgCert b F G P code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (frameRoom : b + hp.need ≤ frame)
    (capacity : Loops.Room hp frame σ base m)
    (failed : P.run σ = .error .revert) : run code m = .revert := by
  rcases hp.correct repr frameRoom capacity with ⟨o,m',base',cost,hs,ht,hc,hr,hk,he,hg⟩ | ⟨hs,ht⟩ | ⟨hs,ht⟩
  · rw [failed] at hs; contradiction
  · exact ht
  · rw [failed] at hs; cases Except.error.inj hs

/-- Exact diverge; divergence is abstract fault, never successful exhaustion. -/
theorem direct_diverge {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : Loops.ProgCert b F G P code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (frameRoom : b + hp.need ≤ frame)
    (capacity : Loops.Room hp frame σ base m)
    (failed : P.run σ = .error .diverge) : run code m = .fault := by
  rcases hp.correct repr frameRoom capacity with ⟨o,m',base',cost,hs,ht,hc,hr,hk,he,hg⟩ | ⟨hs,ht⟩ | ⟨hs,ht⟩
  · rw [failed] at hs; contradiction
  · rw [failed] at hs; cases Except.error.inj hs
  · exact ht

/-- Pin actual source success, including the reached relational cost. -/
theorem scoped_endpoint {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : LoopScopes.ProgCert b F G P code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (frameRoom : b + hp.need ≤ frame)
    (capacity : LoopScopes.Room hp frame σ base m)
    (out : Solidity.Out C σ.H Δ) (executed : P.run σ = .ok out) :
    ∃ m' base' cost, run code m = .ok m' 0 ∧ LoopScopes.Cost hp σ out cost ∧
      StateRepr L b frame G out.st base' m' ∧ m'.stack = m.stack ∧
      BaseExtends σ.H base base' ∧ GrowsAllocator b frame cost σ base m out.st base' m' := by
  rcases hp.correct σ base m repr frameRoom capacity with ⟨o,m',base',cost,hs,ht,hc,hr,hk,he,hg⟩ | ⟨hs,ht⟩ | ⟨hs,ht⟩
  · have same : o = out := Except.ok.inj (hs.symm.trans executed)
    subst o
    exact ⟨m',base',cost,ht,hc,hr,hk,he,hg⟩
  · rw [executed] at hs; contradiction
  · rw [executed] at hs; contradiction

/-- Exact revert; divergence is abstract fault, never successful exhaustion. -/
theorem scoped_revert {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : LoopScopes.ProgCert b F G P code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (frameRoom : b + hp.need ≤ frame)
    (capacity : LoopScopes.Room hp frame σ base m)
    (failed : P.run σ = .error .revert) : run code m = .revert := by
  rcases hp.correct σ base m repr frameRoom capacity with ⟨o,m',base',cost,hs,ht,hc,hr,hk,he,hg⟩ | ⟨hs,ht⟩ | ⟨hs,ht⟩
  · rw [failed] at hs; contradiction
  · exact ht
  · rw [failed] at hs; cases Except.error.inj hs

/-- Exact diverge; divergence is abstract fault, never successful exhaustion. -/
theorem scoped_diverge {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : LoopScopes.ProgCert b F G P code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (frameRoom : b + hp.need ≤ frame)
    (capacity : LoopScopes.Room hp frame σ base m)
    (failed : P.run σ = .error .diverge) : run code m = .fault := by
  rcases hp.correct σ base m repr frameRoom capacity with ⟨o,m',base',cost,hs,ht,hc,hr,hk,he,hg⟩ | ⟨hs,ht⟩ | ⟨hs,ht⟩
  · rw [failed] at hs; contradiction
  · rw [failed] at hs; cases Except.error.inj hs
  · exact ht

/-- Local unwind uses the published StateRepr.drop; code/stack and actual
Cost/extension survive, while the complete caller context is retained. -/
theorem block_endpoint {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {body : Prog C Γ Δ} {code : List Instr} (hp : LoopScopes.ProgCert b F G body code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (frameRoom : b + hp.need ≤ frame)
    (capacity : LoopScopes.Room hp frame σ base m)
    (out : Solidity.Out C σ.H Δ) (executed : body.run σ = .ok out) :
    ∃ m' base' cost, run code m = .ok m' 0 ∧ LoopScopes.Cost hp σ out cost ∧
      StateRepr L b frame (G.restrict Γ) (out.st.drop body.ext) base' m' ∧
      m'.stack = m.stack ∧ BaseExtends σ.H base base' ∧
      GrowsAllocator b frame cost σ base m (out.st.drop body.ext) base' m' ∧
      (out.st.drop body.ext).env = TEnv.drop body.ext out.st.env := by
  obtain ⟨m',base',cost,ht,hc,hr,hk,he,hg⟩ := scoped_endpoint hp repr frameRoom capacity out executed
  exact ⟨m',base',cost,ht,hc,hr.drop body.ext,hk,he,hg,rfl⟩

/-- Actual source-only demand bounds and a real allocating before derive the
reached Room. No target midpoint or simulation is an input premise. -/
theorem after_allocating_prefix {b L frame budget : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} (before : Calls.Program b F P)
    {G : Frag Ξ} {Q : Prog C Δ Ξ} {code : List Instr}
    (hp : LoopScopes.ProgCert b before.frag G Q code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m)
    (prefixRoom : b + before.need ≤ frame) (loopRoom : b + hp.need ≤ frame)
    (capacity : AllocationInput b frame (before.cost σ + budget) σ base m)
    (mid : Solidity.Out C σ.H Δ) (ranPrefix : P.run σ = .ok mid)
    (bound : ∀ amount, LoopScopes.Demand hp mid.st amount → amount ≤ budget)
    (out : Solidity.Out C mid.st.H Ξ) (ranLoop : Q.run mid.st = .ok out) :
    ∃ m₁ base₁ m₂ base₂ cost,
      run before.code m = .ok m₁ 0 ∧ run code m₁ = .ok m₂ 0 ∧
      run (before.code ++ code) m = .ok m₂ 0 ∧
      LoopScopes.Cost hp mid.st out cost ∧ StateRepr L b frame before.frag mid.st base₁ m₁ ∧
      StateRepr L b frame G out.st base₂ m₂ ∧ BaseExtends mid.st.H base₁ base₂ ∧
      GrowsAllocator b frame cost mid.st base₁ m₁ out.st base₂ m₂ ∧
      m₂.stack = m.stack ∧ BaseExtends σ.H base base₂ ∧
      GrowsAllocator b frame (before.cost σ + cost) σ base m out.st base₂ m₂ := by
  obtain ⟨m₁,base₁,ht,hr,hk,he,hg⟩ := PublishedDirectCalls.program_endpoint before repr prefixRoom
    (capacity.of_le (Nat.le_add_right _ _)) mid ranPrefix
  have reached : LoopScopes.Room hp frame mid.st base₁ m₁ :=
    fun amount demand => (hg.nextInput capacity).of_le (bound amount demand)
  obtain ⟨m₂,base₂,cost,ht',hc,hr',hk',he',hg'⟩ := scoped_endpoint hp hr loopRoom reached out ranLoop
  refine ⟨m₁,base₁,m₂,base₂,cost,ht,ht',?_,hc,hr,hr',he',hg',hk'.trans hk,he.trans mid.ext he',hg.comp hg'⟩
  rw [run_append_ok ht]
  exact ht'

/-- Derive the actual successful prefix and reached relational Room before
observing any suffix outcome. No failed suffix State is reconstructed. -/
theorem allocating_prefix_room {b L frame budget : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} (before : Calls.Program b F P)
    {G : Frag Ξ} {Q : Prog C Δ Ξ} {code : List Instr}
    (hp : LoopScopes.ProgCert b before.frag G Q code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m)
    (prefixRoom : b + before.need ≤ frame)
    (capacity : AllocationInput b frame (before.cost σ + budget) σ base m)
    (mid : Solidity.Out C σ.H Δ) (ranPrefix : P.run σ = .ok mid)
    (bound : ∀ amount, LoopScopes.Demand hp mid.st amount → amount ≤ budget) :
    ∃ m₁ base₁, run before.code m = .ok m₁ 0 ∧
      StateRepr L b frame before.frag mid.st base₁ m₁ ∧
      m₁.stack = m.stack ∧ BaseExtends σ.H base base₁ ∧
      GrowsAllocator b frame (before.cost σ) σ base m mid.st base₁ m₁ ∧
      LoopScopes.Room hp frame mid.st base₁ m₁ := by
  obtain ⟨m₁,base₁,ht,hr,hk,he,hg⟩ := PublishedDirectCalls.program_endpoint before repr prefixRoom
    (capacity.of_le (Nat.le_add_right _ _)) mid ranPrefix
  exact ⟨m₁,base₁,ht,hr,hk,he,hg,
    fun amount demand => (hg.nextInput capacity).of_le (bound amount demand)⟩

/-- Actual prefix followed by bare revert; no rollback or failed State is inferred. -/
theorem after_allocating_prefix_revert {b L frame budget : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} (before : Calls.Program b F P)
    {G : Frag Ξ} {Q : Prog C Δ Ξ} {code : List Instr}
    (hp : LoopScopes.ProgCert b before.frag G Q code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m)
    (prefixRoom : b + before.need ≤ frame) (loopRoom : b + hp.need ≤ frame)
    (capacity : AllocationInput b frame (before.cost σ + budget) σ base m)
    (mid : Solidity.Out C σ.H Δ) (ranPrefix : P.run σ = .ok mid)
    (bound : ∀ amount, LoopScopes.Demand hp mid.st amount → amount ≤ budget)
    (halted : Q.run mid.st = .error .revert) :
    ∃ m₁ base₁, run before.code m = .ok m₁ 0 ∧
      StateRepr L b frame before.frag mid.st base₁ m₁ ∧
      m₁.stack = m.stack ∧ BaseExtends σ.H base base₁ ∧
      GrowsAllocator b frame (before.cost σ) σ base m mid.st base₁ m₁ ∧
      run code m₁ = .revert ∧ run (before.code ++ code) m = .revert := by
  obtain ⟨m₁,base₁,ht,hr,hk,he,hg,room⟩ := allocating_prefix_room before hp repr prefixRoom capacity mid ranPrefix bound
  have hf : run code m₁ = .revert := scoped_revert hp hr loopRoom room halted
  refine ⟨m₁,base₁,ht,hr,hk,he,hg,hf,?_⟩
  rw [run_append_ok ht]
  exact hf

/-- Actual prefix followed by divergence, mapped only to abstract fault. -/
theorem after_allocating_prefix_diverge {b L frame budget : Nat} {Γ Δ Ξ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} (before : Calls.Program b F P)
    {G : Frag Ξ} {Q : Prog C Δ Ξ} {code : List Instr}
    (hp : LoopScopes.ProgCert b before.frag G Q code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m)
    (prefixRoom : b + before.need ≤ frame) (loopRoom : b + hp.need ≤ frame)
    (capacity : AllocationInput b frame (before.cost σ + budget) σ base m)
    (mid : Solidity.Out C σ.H Δ) (ranPrefix : P.run σ = .ok mid)
    (bound : ∀ amount, LoopScopes.Demand hp mid.st amount → amount ≤ budget)
    (halted : Q.run mid.st = .error .diverge) :
    ∃ m₁ base₁, run before.code m = .ok m₁ 0 ∧
      StateRepr L b frame before.frag mid.st base₁ m₁ ∧
      m₁.stack = m.stack ∧ BaseExtends σ.H base base₁ ∧
      GrowsAllocator b frame (before.cost σ) σ base m mid.st base₁ m₁ ∧
      run code m₁ = .fault ∧ run (before.code ++ code) m = .fault := by
  obtain ⟨m₁,base₁,ht,hr,hk,he,hg,room⟩ := allocating_prefix_room before hp repr prefixRoom capacity mid ranPrefix bound
  have hf : run code m₁ = .fault := scoped_diverge hp hr loopRoom room halted
  refine ⟨m₁,base₁,ht,hr,hk,he,hg,hf,?_⟩
  rw [run_append_ok ht]
  exact hf

/-- Old alias identities retain their original target address after a loop;
contents are governed by the actual reached heap, not Heap.Keeps. -/
theorem old_alias {L b frame : Nat} {Γ Δ : Ctx} {F : Frag Δ}
    {σ : State C Γ} (out : Solidity.Out C σ.H Δ) {base base' : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F out.st base' m) (ext : BaseExtends σ.H base base')
    {R : RefTy} (r : HRef σ.H R) (i : Idx Δ (.mem R))
    (observed : TEnv.get i out.st.env = some (r.wk out.ext)) :
    m.mem (cellOf b i) = .val (base r.id) :=
  PublishedDirectCalls.old_alias_at_entry_address out repr ext r i observed
end Solidity.Backend.InternalFlow.PublishedLoops
