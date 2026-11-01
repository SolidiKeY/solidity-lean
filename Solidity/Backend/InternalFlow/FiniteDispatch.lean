import Solidity.Semantics.Dispatch
import Solidity.Backend.InternalFlow.PublishedDirectCalls

/-! Checked finite intrinsic dispatch transport. Conditions and arm bodies
are actual published certificates over DispatchArm.chain, not simulation
oracles. Frontend guard/candidate links must be proved for each consumer. -/
namespace Solidity.Backend.InternalFlow.FiniteDispatch
open Evm Evm.Memory
variable {C : Contract}

/-- Data-only certificate tuples indexed by the EXISTING arm list. -/
def Checks (b : Nat) {Γ : Ctx} (F : Frag Γ) : List (DispatchArm C Γ) → Type
  | [] => Unit
  | a :: as => (CompiledVal b F a.cond × Calls.Program b F a.body) × Checks b F as

/-- Compose existing branch/call constructors over the published typed chain. -/
def checkedChain (b : Nat) {Γ : Ctx} (F : Frag Γ) (fail : Stmt C Γ Γ)
    (fallback : Calls.Statement b F fail) :
    (arms : List (DispatchArm C Γ)) → Checks b F arms →
    Calls.Statement b F (DispatchArm.chain arms fail)
  | [], _ => fallback
  | a :: as, checks =>
    let tail := checkedChain b F fail fallback as checks.2
    Calls.branch a.cond checks.1.1 checks.1.2
      (Calls.cons tail (Calls.nil b tail.frag))

/-- Scope restriction and the branch meet are retained exactly. -/
theorem cons_frag (b : Nat) {Γ : Ctx} (F : Frag Γ) (fail : Stmt C Γ Γ)
    (fallback : Calls.Statement b F fail) (a : DispatchArm C Γ) (as : List (DispatchArm C Γ))
    (head : CompiledVal b F a.cond × Calls.Program b F a.body) (tail : Checks b F as) :
    (checkedChain b F fail fallback (a :: as) (head,tail)).frag =
      (head.2.frag.restrict Γ).meet
        ((checkedChain b F fail fallback as tail).frag.restrict Γ) := rfl

/-- Both candidate frames remain reserved even when only one is reached. -/
theorem cons_need (b : Nat) {Γ : Ctx} (F : Frag Γ) (fail : Stmt C Γ Γ)
    (fallback : Calls.Statement b F fail) (a : DispatchArm C Γ) (as : List (DispatchArm C Γ))
    (head : CompiledVal b F a.cond × Calls.Program b F a.body) (tail : Checks b F as) :
    (checkedChain b F fail fallback (a :: as) (head,tail)).need =
      max head.2.need (max (checkedChain b F fail fallback as tail).need Γ.length) := rfl

/-- Explicitly bridge the published runC selection theorem to actual runR. -/
theorem select_run {Γ : Ctx} (pre : List (DispatchArm C Γ)) (a : DispatchArm C Γ)
    (post : List (DispatchArm C Γ)) (fail : Stmt C Γ Γ) (σ : State C Γ)
    (miss : ∀ x ∈ pre, x.cond.evalT σ = .ok false) (hit : a.cond.evalT σ = .ok true) :
    (DispatchArm.chain (pre ++ a :: post) fail).run σ =
      (a.body.run σ).map fun o => ⟨o.st.drop a.body.ext,o.ext⟩ := by
  change Stmt.runR _ σ = (Prog.runR _ σ).map _
  rw [Stmt.runR_eq,Prog.runR_eq]
  exact DispatchArm.chain_select pre a post fail σ miss hit

theorem none_run {Γ : Ctx} (arms : List (DispatchArm C Γ)) (fail : Stmt C Γ Γ)
    (σ : State C Γ) (miss : ∀ a ∈ arms, a.cond.evalT σ = .ok false) :
    (DispatchArm.chain arms fail).run σ = fail.run σ := by
  change Stmt.runR _ σ = Stmt.runR _ σ
  rw [Stmt.runR_eq,Stmt.runR_eq]
  exact DispatchArm.chain_none arms fail σ miss

/-- Arm-local drop and actual reached execution feed the real target frame.
The representation/room/allocation premises are the published producer's
actual inputs, discharged by concrete prefix execution in inhabited tests. -/
theorem selected_endpoint {b L frame : Nat} {Γ : Ctx} {F : Frag Γ}
    (pre : List (DispatchArm C Γ)) (a : DispatchArm C Γ) (post : List (DispatchArm C Γ))
    (fail : Stmt C Γ Γ) (compiled : Calls.Statement b F (DispatchArm.chain (pre ++ a :: post) fail))
    (σ : State C Γ) (miss : ∀ x ∈ pre, x.cond.evalT σ = .ok false)
    (hit : a.cond.evalT σ = .ok true) (out : Solidity.Out C σ.H a.Γ')
    (body : a.body.run σ = .ok out) {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (room : b + compiled.need ≤ frame)
    (capacity : AllocationInput b frame (compiled.cost σ) σ base m) :
    ∃ m' base', Evm.run compiled.code m = .ok m' 0 ∧
      StateRepr L b frame compiled.frag (out.st.drop a.body.ext) base' m' ∧
      m'.stack = m.stack ∧ BaseExtends σ.H base base' ∧
      GrowsAllocator b frame (compiled.cost σ) σ base m (out.st.drop a.body.ext) base' m' := by
  apply PublishedDirectCalls.statement_endpoint compiled repr room capacity
    (⟨out.st.drop a.body.ext,out.ext⟩ : Solidity.Out C σ.H Γ)
  rw [select_run pre a post fail σ miss hit,body]
  rfl

/-- Exact ordinary fallback only; panic/payload/exhaustion are not erased. -/
theorem fallback_revert {b L frame : Nat} {Γ : Ctx} {F : Frag Γ}
    (arms : List (DispatchArm C Γ)) (fail : Stmt C Γ Γ)
    (compiled : Calls.Statement b F (DispatchArm.chain arms fail)) (σ : State C Γ)
    (miss : ∀ a ∈ arms, a.cond.evalT σ = .ok false) (failed : fail.run σ = .error .revert)
    {base : Nat → Fin W} {m : Machine} (repr : StateRepr L b frame F σ base m)
    (room : b + compiled.need ≤ frame)
    (capacity : AllocationInput b frame (compiled.cost σ) σ base m) :
    Evm.run compiled.code m = .revert := by
  apply PublishedDirectCalls.statement_revert compiled repr room capacity
  rw [none_run arms fail σ miss,failed]

end Solidity.Backend.InternalFlow.FiniteDispatch
