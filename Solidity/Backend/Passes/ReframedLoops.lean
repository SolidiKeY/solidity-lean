import Solidity.Backend.Passes.ReframedSequence
import Solidity.Backend.Passes.LoopScopeApplication

/-! Frame release after actual allocating loop outputs. Original Cost/Room and
selected-map relations remain prefix facts; no loop producer is modified. -/
namespace Solidity.Backend.Passes
open Evm Evm.Compiler
variable {C : Contract} {b L beforeFrame afterFrame : Nat} {Γ Δ Ξ : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ}

theorem loops_shrinking_link (left : Memory.Loops.CompiledProg b F P)
    (right : Memory.CompiledProg b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (smaller : afterFrame ≤ beforeFrame) (locals : b + Δ.length ≤ afterFrame)
    (codeRoom : b + Memory.frameNeedProg Q ≤ afterFrame)
    (noAlloc : Memory.hasAllocation Q = false) :
    ReframedLink (.memoryLoops left) (.memory right)
      L beforeFrame afterFrame base σ m := by
  intro o mid selected _ _ output
  rcases output with ⟨amount,ext,cost,state,baseExt,growth⟩
  exact ⟨memory_state_shrink state smaller locals,codeRoom,
    .inl (Memory.allocationCostProg_zero Q noAlloc o.st)⟩

theorem loop_scopes_shrinking_link (left : Memory.LoopScopes.CompiledProg b F P)
    (right : Memory.CompiledProg b left.frag Q)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (smaller : afterFrame ≤ beforeFrame) (locals : b + Δ.length ≤ afterFrame)
    (codeRoom : b + Memory.frameNeedProg Q ≤ afterFrame)
    (noAlloc : Memory.hasAllocation Q = false) :
    ReframedLink (.memoryLoopScopes left) (.memory right)
      L beforeFrame afterFrame base σ m := by
  intro o mid selected _ _ output
  rcases output with ⟨amount,ext,cost,state,baseExt,growth⟩
  exact ⟨memory_state_shrink state smaller locals,codeRoom,
    .inl (Memory.allocationCostProg_zero Q noAlloc o.st)⟩

namespace ReframedLoopControls
open MemoryCallControls (C initial base machine)
open LoopScopeControls

theorem bounds : 1 + LoopScopeControls.Γ.length ≤ 5 ∧
    1 + Memory.frameNeedProg consume ≤ 5 := by decide +kernel

/-- Actual maps, machine skeletons, loop cost and extension precede tails.
For EACH tail both emitted associations and full outputs hold; the new suffix
Input is derived from that same reached output. Suffix output stays at128. -/
theorem reached : ∃ (mb nb ob : Nat → Fin W) (mid next out : Machine)
    (amount : Nat) (ext : prepared.st.H <+: loopOut.st.H),
    Memory.LoopScopes.Cost enclosed.cert prepared.st ⟨loopOut.st,ext⟩ amount ∧
    mid.stack = [] ∧ next.stack = [] ∧ out.stack = [] ∧ ∀ tail,
    MappedOutput (.memory preparation) 1 128 base initial {machine with stack := tail}
      prepared.st {mid with stack := tail} mb ∧
    run enclosed.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
    MappedOutput checked 1 128 mb prepared.st {mid with stack := tail}
      loopOut.st {next with stack := tail} nb ∧
    (Compilation.memory suffix).Input 1 5 nb loopOut.st {next with stack := tail} ∧
    run ((preparation.code ++ enclosed.code) ++ suffix.code) {machine with stack := tail} =
      .ok {out with stack := tail} 0 ∧
    run (preparation.code ++ (enclosed.code ++ suffix.code)) {machine with stack := tail} =
      .ok {out with stack := tail} 0 ∧
    MappedOutput (.memory suffix) 1 128 nb loopOut.st {next with stack := tail}
      final.st {out with stack := tail} ob := by
  obtain ⟨mb,nb,ob,mid,next,out,amount,ext,hcost,hm,hn,ho,hall⟩ :=
    LoopScopeApplication.shared
  refine ⟨mb,nb,ob,mid,next,out,amount,ext,hcost,hm,hn,ho,?_⟩
  intro tail
  obtain ⟨ha,hd,he,hl,hr,ma,md,me⟩ := hall tail
  have link := loop_scopes_shrinking_link enclosed suffix
    (base := mb) (σ := prepared.st) (m := {mid with stack := tail})
    (L := 1) (beforeFrame := 128) (afterFrame := 5)
    (by decide) bounds.1 bounds.2 costs.2
  have hi := link loopOut {next with stack := tail} nb wrapped_source hd
    (by simpa only [enclosed.cert.pushes_zero,Nat.add_zero] using md)
  exact ⟨ma,hd,md,by simpa only [enclosed.cert.pushes_zero,Nat.add_zero] using hi,hl,hr,me⟩
end ReframedLoopControls
end Solidity.Backend.Passes
