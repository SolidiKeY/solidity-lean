import Solidity.Evm.MemoryLoopHorizon
import Solidity.Evm.MemoryLoopScopeSound
import Solidity.Evm.MemoryLoopScopeCompile

/-! Outer-loop transport for actual scope/branch/loop-aware body certificates.
No source or target representation change. A body executes its actual unbounded
run; finite horizon counts OUTER turns, not recursive statement fuel. Inner
body divergence is a completed failure observation, distinct from pending. -/
namespace Solidity.Evm.Memory.MixedLoops
variable {C : Contract} {Γ Δ : Ctx}

structure Certificate (b : Nat) (F : Frag Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Δ) (cond code : List Instr) where
  condition : ValFrag b F c cond
  bodyFrag : Frag Δ
  bodyCert : LoopScopes.ProgCert b F bodyFrag body code
  stable : bodyFrag.restrict Γ=F

/-- Actual successful prefixes with the body's own exact, reached cost. -/
inductive Prefix {b F c body cond code} (cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code)
    (σ : State C Γ) : Solidity.Out C σ.H Γ → Nat → Prop where
  | start : Prefix cert σ ⟨σ,List.prefix_refl _⟩ 0
  | next {o : Solidity.Out C σ.H Γ} {cost bodyCost : Nat} {o' : Solidity.Out C o.st.H Δ}
      (hpref : Prefix cert σ o cost) (condition : c.evalT o.st=.ok true)
      (run : body.run o.st=.ok o') (spent : LoopScopes.Cost cert.bodyCert o.st o' bodyCost) :
      Prefix cert σ ⟨o'.st.drop body.ext,o.ext.trans o'.ext⟩ (cost+bodyCost)

/-- Every reached body demand, including reverting/diverging bodies, shifted
by the exact successful outer-prefix cost. Unselected branches add no demand. -/
def Room {b F c body cond code} (cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code)
    (frame : Nat) (σ : State C Γ) (base : Nat → Fin W) (m : Machine) : Prop :=
  ∀ (o : Solidity.Out C σ.H Γ) (cost : Nat), Prefix cert σ o cost →
    c.evalT o.st=.ok true → ∀ amount, LoopScopes.Demand cert.bodyCert o.st amount →
      AllocationInput b frame (cost+amount) σ base m

inductive Horizon {b F c body cond code} (cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code)
    (L frame : Nat) (σ : State C Γ) (base : Nat → Fin W) (m₀ : Machine) :
    Solidity.Out C σ.H Γ ⊕ TRes (Solidity.Out C σ.H Γ) → Machine ⊕ Out → Prop where
  | more {o m base' cost} (hpref : Prefix cert σ o cost)
      (repr : StateRepr L b frame F o.st base' m) (stack : m.stack=m₀.stack)
      (bases : BaseExtends σ.H base base')
      (growth : GrowsAllocator b frame cost σ base m₀ o.st base' m) :
      Horizon cert L frame σ base m₀ (.inl o) (.inl m)
  | done {o m base' cost} (hpref : Prefix cert σ o cost)
      (repr : StateRepr L b frame F o.st base' m) (stack : m.stack=m₀.stack)
      (bases : BaseExtends σ.H base base')
      (growth : GrowsAllocator b frame cost σ base m₀ o.st base' m) :
      Horizon cert L frame σ base m₀ (.inr (.ok o)) (.inr (.ok m 0))
  | revert : Horizon cert L frame σ base m₀ (.inr (.error .revert)) (.inr .revert)
  | diverge : Horizon cert L frame σ base m₀ (.inr (.error .diverge)) (.inr .fault)

theorem Certificate.step {b L frame F c body cond code}
    (cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code)
    {σ : State C Γ} {base : Nat → Fin W} {m₀ : Machine}
    (room : Room cert frame σ base m₀) (cap : b+cert.bodyCert.need≤frame)
    {o : Solidity.Out C σ.H Γ} {m : Machine} {base' : Nat → Fin W} {cost : Nat}
    (hpref : Prefix cert σ o cost) (repr : StateRepr L b frame F o.st base' m)
    (stack : m.stack=m₀.stack) (bases : BaseExtends σ.H base base')
    (growth : GrowsAllocator b frame cost σ base m₀ o.st base' m) :
    Horizon cert L frame σ base m₀
      (TLoop.step (horizonBody body) (fun o=>c.evalT o.st) o)
      (loopTurn (fun m=>exec cond 0 m) (fun m=>exec code 0 m) m) := by
  rcases cert.condition.correct repr with ⟨v,w,hv,hw,hc⟩ | ⟨hv,hc⟩
  · obtain rfl := hw.bool_inv
    have conditionRun : exec cond 0 m=.ok (m.push (.val (bword v))) 0 := hc
    unfold TLoop.step loopTurn
    dsimp only
    rw [hv,conditionRun]
    cases v
    · exact .done hpref repr stack bases growth
    · change Horizon cert L frame σ base m₀ _
        (match exec code 0 m with
         | .ok m₂ 0 => .inl m₂
         | .ok _ (_+1) => .inr .fault
         | r => .inr r)
      have bodyRoom : LoopScopes.Room cert.bodyCert frame o.st base' m := by
        intro amount demand
        exact growth.nextInput (room o cost hpref hv amount demand)
      rcases cert.bodyCert.correct o.st base' m repr cap bodyRoom with
        ⟨out,next,newBase,spent,sourceRun,targetRun,bodyCost,represented,sameStack,extended,grew⟩ |
        ⟨sourceRun,targetRun⟩ | ⟨sourceRun,targetRun⟩
      · have targetRun' : exec code 0 m=.ok next 0 := targetRun
        simp only [horizonBody,sourceRun,Except.map,targetRun']
        refine .more (.next hpref hv sourceRun bodyCost) ?_ (sameStack.trans stack)
          (bases.trans o.ext extended) (growth.comp grew)
        rw [←cert.stable]
        exact represented.drop body.ext
      · have targetRun' : exec code 0 m=.revert := targetRun
        simp only [horizonBody,sourceRun,Except.map,targetRun']
        exact .revert
      · have targetRun' : exec code 0 m=.fault := targetRun
        simp only [horizonBody,sourceRun,Except.map,targetRun']
        exact .diverge
  · have conditionRun : exec cond 0 m=.revert := hc
    unfold TLoop.step loopTurn
    dsimp only
    rw [hv,conditionRun]
    exact .revert

theorem Certificate.iter {b L frame F c body cond code}
    (cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code)
    {σ : State C Γ} {base : Nat → Fin W} {m₀ : Machine}
    (room : Room cert frame σ base m₀) (cap : b+cert.bodyCert.need≤frame) :
    ∀ n {o : Solidity.Out C σ.H Γ} {m : Machine} {base' : Nat → Fin W} {cost : Nat},
      Prefix cert σ o cost → StateRepr L b frame F o.st base' m →
      m.stack=m₀.stack → BaseExtends σ.H base base' →
      GrowsAllocator b frame cost σ base m₀ o.st base' m →
      Horizon cert L frame σ base m₀
        (TLoop.iterN (horizonBody body) (fun o=>c.evalT o.st) n o)
        (loopIterN (fun m=>exec cond 0 m) (fun m=>exec code 0 m) n m)
  | 0,_,_,_,_,hp,hr,hs,he,hg => .more hp hr hs he hg
  | n+1,_,_,_,_,hp,hr,hs,he,hg => by
    have step := cert.step room cap hp hr hs he hg
    simp only [TLoop.iterN,loopIterN]
    revert step
    generalize TLoop.step _ _ _=A
    generalize loopTurn _ _ _=B
    intro step
    cases step with
    | more hp hr hs he hg => exact cert.iter room cap n hp hr hs he hg
    | done hp hr hs he hg => exact .done hp hr hs he hg
    | revert => exact .revert
    | diverge => exact .diverge

theorem Certificate.correct_horizon {b L frame F c body cond code}
    (cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (cap : b+cert.bodyCert.need≤frame)
    (room : Room cert frame σ base m) (n : Nat) :
    Horizon cert L frame σ base m
      (TLoop.iterN (horizonBody body) (fun o=>c.evalT o.st) n ⟨σ,List.prefix_refl _⟩)
      (loopIterN (fun m=>exec cond 0 m) (fun m=>exec code 0 m) n m) :=
  cert.iter room cap n .start repr rfl (BaseExtends.refl base) (fun _ _ input _=>input)

end Solidity.Evm.Memory.MixedLoops
