import Solidity.Evm.MemoryCalls
import Solidity.Backend.InternalFlow.FrameLaws

/-! Consumers of the published ordinary memory-call producer. Structural call
expansion is finite; these results make no unbounded recursion claim. -/
namespace Solidity.Backend.InternalFlow.PublishedDirectCalls
open Evm Evm.Memory
variable {C : Contract}

/-- Pin the producer's successful endpoint to an actual intrinsic execution.
The returned address map preserves every old typed identity, including aliases.
Contents may mutate: BaseExtends does not assert heap noninterference. -/
theorem statement_endpoint {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ}
    {s : Stmt C Γ Δ} (compiled : Calls.Statement b F s)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m)
    (room : b + compiled.need ≤ frame)
    (capacity : AllocationInput b frame (compiled.cost σ) σ base m)
    (o : Solidity.Out C σ.H Δ) (executed : s.run σ = .ok o) :
    ∃ m' base', Evm.run compiled.code m = .ok m' 0 ∧
      StateRepr L b frame compiled.frag o.st base' m' ∧ m'.stack = m.stack ∧
      (∀ {R : RefTy} (r : HRef σ.H R), base' r.id = base r.id) ∧
      GrowsAllocator b frame (compiled.cost σ) σ base m o.st base' m' := by
  rcases compiled.sound repr room capacity with ⟨o', m', base', hs, ht, hr, hk, he, ha⟩ | ⟨hs, ht⟩
  · have ho : o' = o := Except.ok.inj (hs.symm.trans executed)
    subst o'
    exact ⟨m', base', ht, hr, hk, he, ha⟩
  · rw [executed] at hs
    contradiction

/-- The actual frame result from argument evaluation and body execution is
also the represented target endpoint. Its environment contains only exported
results and the transported caller tail, not the private argument/local frame. -/
theorem call_endpoint {b L frame : Nat} {Γ Δ rs ps Γf : Ctx} {F : Frag Γ}
    (name : Name) (args : Args C Γ ps) (ret : CallRet Γ rs Δ)
    (body : Prog C (rs ++ ps) Γf)
    (compiled : Calls.Statement b F (.call name args ret body))
    (σ : State C Γ) (arguments : TEnv C σ.H ps)
    (ha : args.evalT σ = .ok arguments)
    (out : Solidity.Out C (ret.enterT (σ.withEnv arguments)).st.H Γf)
    (hb : body.runR (ret.enterT (σ.withEnv arguments)).st = .ok out)
    {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m)
    (room : b + compiled.need ≤ frame)
    (capacity : AllocationInput b frame (compiled.cost σ) σ base m) :
    let exported : Solidity.Out C σ.H Δ :=
      ⟨out.st.withEnv (ret.leaveT
        (TEnv.wk ((ret.enterT (σ.withEnv arguments)).ext.trans out.ext) Γ σ.env)
        (TEnv.take rs (TEnv.drop body.ext out.st.env))),
        (ret.enterT (σ.withEnv arguments)).ext.trans out.ext⟩
    ∃ m' base', Evm.run compiled.code m = .ok m' 0 ∧
      StateRepr L b frame compiled.frag exported.st base' m' ∧ m'.stack = m.stack ∧
      BaseExtends σ.H base base' ∧
      GrowsAllocator b frame (compiled.cost σ) σ base m exported.st base' m' := by
  apply statement_endpoint compiled repr room capacity
  exact InternalFlow.call_return args ret body.ext body.runR σ arguments ha out hb

/-- Only ordinary bare revert is supported by this target producer. In
particular this theorem cannot erase bytes or turn panic/exhaustion into revert. -/
theorem statement_revert {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ}
    {s : Stmt C Γ Δ} (compiled : Calls.Statement b F s)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (room : b + compiled.need ≤ frame)
    (capacity : AllocationInput b frame (compiled.cost σ) σ base m)
    (failed : s.run σ = .error .revert) : Evm.run compiled.code m = .revert := by
  rcases compiled.sound repr room capacity with ⟨o, m', base', hs, _⟩ | ⟨_, ht⟩
  · rw [failed] at hs
    contradiction
  · exact ht

/-- Program counterpart for finite direct-call composition; costs are those
computed by the producer from the reached intrinsic execution. -/
theorem program_endpoint {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ}
    {P : Prog C Γ Δ} (compiled : Calls.Program b F P)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (room : b + compiled.need ≤ frame)
    (capacity : AllocationInput b frame (compiled.cost σ) σ base m)
    (o : Solidity.Out C σ.H Δ) (executed : P.run σ = .ok o) :
    ∃ m' base', Evm.run compiled.code m = .ok m' 0 ∧
      StateRepr L b frame compiled.frag o.st base' m' ∧ m'.stack = m.stack ∧
      BaseExtends σ.H base base' ∧
      GrowsAllocator b frame (compiled.cost σ) σ base m o.st base' m' := by
  rcases compiled.sound repr room capacity with ⟨o', m', base', hs, ht, hr, hk, he, ha⟩ | ⟨hs, ht⟩
  · have ho : o' = o := Except.ok.inj (hs.symm.trans executed)
    subst o'
    exact ⟨m', base', ht, hr, hk, he, ha⟩
  · rw [executed] at hs
    contradiction

end Solidity.Backend.InternalFlow.PublishedDirectCalls
