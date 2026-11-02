import Solidity.Backend.Passes.LoopBoundary
import Solidity.Backend.Passes.TripleSequence

/-! Three-stage composition keeps the loop stage's ACTUAL allocation cost and
heap-extension witness outside the arbitrary-tail quantifier, along with maps
and machines. Both independent physical links are still required. -/
namespace Solidity.Backend.Passes
open Evm Evm.Compiler
variable {C : Contract} {b L frame : Nat} {Γ Δ Ξ Ω : Ctx}
  {F : Frag Γ} {P : Prog C Γ Δ} {Q : Prog C Δ Ξ} {R : Prog C Ξ Ω}

theorem loop_scopes_triple_shared (a : Compilation b F P)
    (d : Memory.LoopScopes.CompiledProg b a.frag Q) (e : Compilation b d.frag R)
    {base : Nat → Fin W} {σ : State C Γ} {m : Machine}
    (hi : a.Input L frame base σ m) (empty : m.stack = [])
    (ad : MappedBoundaryLink a (.memoryLoopScopes d) L frame base σ m)
    (de : ReachedMappedLink a (.memoryLoopScopes d) e L frame base σ m)
    (hp : Evm.Prog.pays P = false) (hq : Evm.Prog.pays Q = false) (hr : Evm.Prog.pays R = false)
    {o : Solidity.Out C σ.H Δ} (hs : P.run σ = .ok o)
    {u : Solidity.Out C o.st.H Ξ} (hu : Q.run o.st = .ok u)
    {v : Solidity.Out C u.st.H Ω} (hv : R.run u.st = .ok v) :
    ∃ (mb nb ob : Nat → Fin W) (mid next final : Machine) (amount : Nat)
      (ext : o.st.H <+: u.st.H),
    Memory.LoopScopes.Cost d.cert o.st ⟨u.st,ext⟩ amount ∧
    mid.stack = [] ∧ next.stack = [] ∧ final.stack = [] ∧ ∀ tail,
    run a.code {m with stack := tail} = .ok {mid with stack := tail} 0 ∧
    run d.code {mid with stack := tail} = .ok {next with stack := tail} 0 ∧
    run e.code {next with stack := tail} = .ok {final with stack := tail} 0 ∧
    run ((a.code ++ d.code) ++ e.code) {m with stack := tail} = .ok {final with stack := tail} 0 ∧
    run (a.code ++ (d.code ++ e.code)) {m with stack := tail} = .ok {final with stack := tail} 0 ∧
    MappedOutput a (L + Evm.Prog.pushes P) frame base σ {m with stack := tail}
      o.st {mid with stack := tail} mb ∧
    MappedOutput (.memoryLoopScopes d) ((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q)
      frame mb o.st {mid with stack := tail} u.st {next with stack := tail} nb ∧
    MappedOutput e (((L + Evm.Prog.pushes P) + Evm.Prog.pushes Q) + Evm.Prog.pushes R)
      frame nb u.st {next with stack := tail} v.st {final with stack := tail} ob := by
  obtain ⟨mb,nb,ob,mid,next,final,hm,hn,hf,all⟩ :=
    compilation_triple_shared a (.memoryLoopScopes d) e hi empty ad de hp hq hr hs hu hv
  obtain ⟨_,_,_,_,_,_,hd,_⟩ := all []
  rcases hd with ⟨amount,ext,hcost,state,hbase,hgrowth⟩
  refine ⟨mb,nb,ob,mid,next,final,amount,ext,hcost,hm,hn,hf,?_⟩
  intro tail
  obtain ⟨ha,hd,he,hl,hall,ma,_,me⟩ := all tail
  have growth : Memory.GrowsAllocator b frame amount o.st mb {mid with stack := tail}
      u.st nb {next with stack := tail} := by
    intro cursor hb hs hfit
    exact (hgrowth cursor hb (hs.mem_eq rfl) hfit).mem_eq rfl
  exact ⟨ha,hd,he,hl,hall,ma,⟨amount,ext,hcost,state.stack tail,hbase,growth⟩,me⟩

end Solidity.Backend.Passes
