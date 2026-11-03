import Solidity.Evm.MemoryMixedLoopCompile
import Solidity.Evm.MemoryLoopFiniteHorizon

namespace Solidity.Evm.Memory.MixedLoops
variable {C : Contract} {Γ Δ : Ctx}

inductive CountedPrefix {b F c body cond code}
    (cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code) (σ : State C Γ) :
    Solidity.Out C σ.H Γ → Nat → Nat → Prop where
  | start : CountedPrefix cert σ ⟨σ,List.prefix_refl _⟩ 0 0
  | next {o : Solidity.Out C σ.H Γ} {cost spent turns : Nat} {out : Solidity.Out C o.st.H Δ}
      (before : CountedPrefix cert σ o cost turns) (condition : c.evalT o.st=.ok true)
      (run : body.run o.st=.ok out) (bodyCost : LoopScopes.Cost cert.bodyCert o.st out spent) :
      CountedPrefix cert σ ⟨out.st.drop body.ext,o.ext.trans out.ext⟩ (cost+spent) (turns+1)

theorem CountedPrefix.forget {b F c body cond code}
    {cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code}
    {σ : State C Γ} {o cost turns} (h : CountedPrefix cert σ o cost turns) : Prefix cert σ o cost := by
  induction h with
  | start => exact .start
  | next hp hc hr spent ih => exact .next ih hc hr spent

theorem CountedPrefix.iterN_eq {b F c body cond code}
    {cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code}
    {σ : State C Γ} {o cost turns} (h : CountedPrefix cert σ o cost turns) :
    TLoop.iterN (horizonBody body) (fun out=>c.evalT out.st) turns ⟨σ,List.prefix_refl _⟩=.inl o := by
  induction h with
  | start => rfl
  | next hp hc hr spent ih =>
    rw [iterN_succ_of_pending ih]
    simp only [TLoop.step,horizonBody,hc,hr,Except.map]

def FiniteRoom {b F c body cond code}
    (cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code)
    (frame : Nat) (σ : State C Γ) (base : Nat → Fin W) (m : Machine) (horizon : Nat) : Prop :=
  ∀ (o : Solidity.Out C σ.H Γ) (cost turns : Nat), CountedPrefix cert σ o cost turns →
    turns<horizon → c.evalT o.st=.ok true → ∀ amount, LoopScopes.Demand cert.bodyCert o.st amount →
      AllocationInput b frame (cost+amount) σ base m

theorem Room.finite {b frame F c body cond code}
    {cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (room : Room cert frame σ base m) (n : Nat) : FiniteRoom cert frame σ base m n :=
  fun o cost _ hp _ hc amount demand=>room o cost hp.forget hc amount demand

theorem finiteRoom_zero {b frame F c body cond code}
    (cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code)
    (σ : State C Γ) (base : Nat → Fin W) (m : Machine) : FiniteRoom cert frame σ base m 0 := by
  intro o cost turns hp before
  omega

inductive CountedHorizon {b F c body cond code}
    (cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code)
    (L frame : Nat) (σ : State C Γ) (base : Nat → Fin W) (m₀ : Machine) (turns : Nat) :
    Solidity.Out C σ.H Γ ⊕ TRes (Solidity.Out C σ.H Γ) → Machine ⊕ Out → Prop where
  | more {o m base' cost} (hp : CountedPrefix cert σ o cost turns)
      (repr : StateRepr L b frame F o.st base' m) (stack : m.stack=m₀.stack)
      (bases : BaseExtends σ.H base base')
      (growth : GrowsAllocator b frame cost σ base m₀ o.st base' m) :
      CountedHorizon cert L frame σ base m₀ turns (.inl o) (.inl m)
  | done {o m base' cost count} (hp : CountedPrefix cert σ o cost count)
      (earlier : count<turns) (stopped : c.evalT o.st=.ok false)
      (repr : StateRepr L b frame F o.st base' m) (stack : m.stack=m₀.stack)
      (bases : BaseExtends σ.H base base')
      (growth : GrowsAllocator b frame cost σ base m₀ o.st base' m) :
      CountedHorizon cert L frame σ base m₀ turns (.inr (.ok o)) (.inr (.ok m 0))
  | revert : CountedHorizon cert L frame σ base m₀ turns (.inr (.error .revert)) (.inr .revert)
  | diverge : CountedHorizon cert L frame σ base m₀ turns (.inr (.error .diverge)) (.inr .fault)

theorem CountedHorizon.forget {b F c body cond code}
    {cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code}
    {L frame σ base m turns source target} (h : CountedHorizon cert L frame σ base m turns source target) :
    Horizon cert L frame σ base m source target := by
  cases h with
  | more hp hr hs he hg => exact .more hp.forget hr hs he hg
  | done hp earlier stopped hr hs he hg => exact .done hp.forget hr hs he hg
  | revert => exact .revert
  | diverge => exact .diverge

theorem Certificate.finite_step {b L frame F c body cond code}
    (cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code)
    {σ : State C Γ} {base : Nat → Fin W} {m₀ : Machine}
    (cap : b+cert.bodyCert.need≤frame)
    {o : Solidity.Out C σ.H Γ} {m : Machine} {base' : Nat → Fin W} {cost turns : Nat}
    (hpref : CountedPrefix cert σ o cost turns)
    (room : c.evalT o.st=.ok true → ∀ amount, LoopScopes.Demand cert.bodyCert o.st amount →
      AllocationInput b frame (cost+amount) σ base m₀)
    (repr : StateRepr L b frame F o.st base' m) (stack : m.stack=m₀.stack)
    (bases : BaseExtends σ.H base base')
    (growth : GrowsAllocator b frame cost σ base m₀ o.st base' m) :
    CountedHorizon cert L frame σ base m₀ (turns+1)
      (TLoop.step (horizonBody body) (fun o=>c.evalT o.st) o)
      (loopTurn (fun m=>exec cond 0 m) (fun m=>exec code 0 m) m) := by
  rcases cert.condition.correct repr with ⟨v,w,hv,hw,hc⟩ | ⟨hv,hc⟩
  · obtain rfl := hw.bool_inv
    have conditionRun : exec cond 0 m=.ok (m.push (.val (bword v))) 0 := hc
    unfold TLoop.step loopTurn
    dsimp only
    rw [hv,conditionRun]
    cases v
    · exact .done hpref (Nat.lt_succ_self turns) hv repr stack bases growth
    · change CountedHorizon cert L frame σ base m₀ (turns+1) _
        (match exec code 0 m with
         | .ok next 0 => .inl next
         | .ok _ (_+1) => .inr .fault
         | r => .inr r)
      have bodyRoom : LoopScopes.Room cert.bodyCert frame o.st base' m :=
        fun amount demand=>growth.nextInput (room hv amount demand)
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

theorem Certificate.finite_iter {b L frame horizon F c body cond code}
    (cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code)
    {σ : State C Γ} {base : Nat → Fin W} {m₀ : Machine}
    (room : FiniteRoom cert frame σ base m₀ horizon) (cap : b+cert.bodyCert.need≤frame) :
    ∀ n turns, turns+n≤horizon →
      ∀ {o : Solidity.Out C σ.H Γ} {m : Machine} {base' : Nat → Fin W} {cost : Nat},
      CountedPrefix cert σ o cost turns → StateRepr L b frame F o.st base' m →
      m.stack=m₀.stack → BaseExtends σ.H base base' →
      GrowsAllocator b frame cost σ base m₀ o.st base' m →
      CountedHorizon cert L frame σ base m₀ (turns+n)
        (TLoop.iterN (horizonBody body) (fun o=>c.evalT o.st) n o)
        (loopIterN (fun m=>exec cond 0 m) (fun m=>exec code 0 m) n m)
  | 0,_,_,_,_,_,_,hp,hr,hs,he,hg => .more hp hr hs he hg
  | n+1,turns,budget,_,_,_,_,hp,hr,hs,he,hg => by
    have step := cert.finite_step cap hp (fun hc=>room _ _ turns hp (by omega) hc) hr hs he hg
    simp only [TLoop.iterN,loopIterN]
    revert step
    generalize TLoop.step _ _ _=source
    generalize loopTurn _ _ _=target
    intro step
    cases step with
    | more hp hr hs he hg =>
      have rest := cert.finite_iter room cap n (turns+1) (by omega) hp hr hs he hg
      simpa only [Nat.succ_add,Nat.add_succ] using rest
    | done hp earlier stopped hr hs he hg => exact .done hp (by omega) stopped hr hs he hg
    | revert => exact .revert
    | diverge => exact .diverge

/-- The public finite-only input does NOT require room after this horizon.
The current body still uses its actual full run, including an inner divergence. -/
theorem Certificate.correct_finite_horizon {b L frame F c body cond code}
    (cert : Certificate (C:=C) (Γ:=Γ) (Δ:=Δ) b F c body cond code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (n : Nat) (repr : StateRepr L b frame F σ base m) (cap : b+cert.bodyCert.need≤frame)
    (room : FiniteRoom cert frame σ base m n) :
    CountedHorizon cert L frame σ base m n
      (TLoop.iterN (horizonBody body) (fun o=>c.evalT o.st) n ⟨σ,List.prefix_refl _⟩)
      (loopIterN (fun m=>exec cond 0 m) (fun m=>exec code 0 m) n m) := by
  simpa only [Nat.zero_add] using cert.finite_iter room cap n 0 (by omega) .start repr rfl
    (BaseExtends.refl base) (fun _ _ input _=>input)

end Solidity.Evm.Memory.MixedLoops
