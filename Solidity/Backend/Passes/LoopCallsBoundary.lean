import Solidity.Backend.Passes.LoopBoundary
import Solidity.Backend.Passes.MemoryCallBoundary

/-! Expanded calls receive their real private-frame need and reached cost.
A generic sum budget remains an explicit prerequisite, never a claimed result. -/
namespace Solidity.Backend.Passes
open Evm Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}
  {base : Nat → Fin W} {σ : State C Γ} {m : Machine}

theorem loops_budgeted_memoryCalls_link (left : Memory.Loops.CompiledProg b F P)
    (right : Memory.Calls.Program b left.frag Q) (pushFree : Evm.Prog.pushes Q = 0)
    (capacity : b + right.need ≤ frame)
    (budget : ∀ (o : Solidity.Out C σ.H Δ) (amount : Nat) (ext : σ.H <+: o.st.H),
      P.run σ = .ok o → Memory.Loops.Cost left.cert σ ⟨o.st,ext⟩ amount →
      Memory.AllocationInput b frame (amount + right.cost o.st) σ base m) :
    MappedBoundaryLink (.memoryLoops left) (.memoryCalls right pushFree) L frame base σ m := by
  intro o mid selected hs _ output
  rcases output with ⟨amount,ext,hcost,state,hbase,hgrowth⟩
  exact ⟨state,capacity,hgrowth.nextInput (budget o amount ext hs hcost)⟩

theorem loop_scopes_budgeted_memoryCalls_link (left : Memory.LoopScopes.CompiledProg b F P)
    (right : Memory.Calls.Program b left.frag Q) (pushFree : Evm.Prog.pushes Q = 0)
    (capacity : b + right.need ≤ frame)
    (budget : ∀ (o : Solidity.Out C σ.H Δ) (amount : Nat) (ext : σ.H <+: o.st.H),
      P.run σ = .ok o → Memory.LoopScopes.Cost left.cert σ ⟨o.st,ext⟩ amount →
      Memory.AllocationInput b frame (amount + right.cost o.st) σ base m) :
    MappedBoundaryLink (.memoryLoopScopes left) (.memoryCalls right pushFree) L frame base σ m := by
  intro o mid selected hs _ output
  rcases output with ⟨amount,ext,hcost,state,hbase,hgrowth⟩
  exact ⟨state,capacity,hgrowth.nextInput (budget o amount ext hs hcost)⟩

end Solidity.Backend.Passes
