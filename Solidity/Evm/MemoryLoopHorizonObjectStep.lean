import Solidity.Evm.MemoryLoopHorizonObjectCoverage
import Solidity.Evm.MemoryLoopHorizonObjectScope

/-! One actual condition/body turn for complete-object construction. Certificates
reuse owner condition/body proofs; capacity quantifies only reached true turns.
No concrete certificate, whole-loop result or Source adequacy is assumed. -/
namespace Solidity.Evm.Memory.Construction
variable {C : Contract} {Γ Δ : Ctx}

/-- Existing strong condition and construction-body certificates with scope stability. -/
structure LoopCert (b : Nat) (F : Frag Γ) (c : Val C Γ .bool) (body : Prog C Γ Δ)
    (cond code : List Instr) where
  condition : Objects.ValFrag b F c cond
  bodyFrag : Frag Δ
  bodyCert : ProgFrag b F bodyFrag body code
  stable : bodyFrag.restrict Γ = F

/-- Matched observations retain the complete object heap and allocator. -/
inductive HorizonRelation (L b frame : Nat) (F : Frag Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Δ) (σ : State C Γ) (base : Nat → Fin W) (initial : Machine) :
    Solidity.Out C σ.H Γ ⊕ TRes (Solidity.Out C σ.H Γ) → Machine ⊕ Out → Prop where
  | more {o machine nextBase cost turns}
      (hp : CountedLoopPrefix c body σ o cost turns)
      (repr : Objects.StateRepr L b frame F o.st nextBase machine)
      (stack : machine.stack = initial.stack) (bases : BaseExtends σ.H base nextBase)
      (grows : Objects.GrowsAllocator b frame cost σ base initial o.st nextBase machine) :
      HorizonRelation L b frame F c body σ base initial (.inl o) (.inl machine)
  | done {o machine nextBase cost turns}
      (hp : CountedLoopPrefix c body σ o cost turns)
      (repr : Objects.StateRepr L b frame F o.st nextBase machine)
      (stack : machine.stack = initial.stack) (bases : BaseExtends σ.H base nextBase)
      (grows : Objects.GrowsAllocator b frame cost σ base initial o.st nextBase machine) :
      HorizonRelation L b frame F c body σ base initial (.inr (.ok o)) (.inr (.ok machine 0))
  | revert : HorizonRelation L b frame F c body σ base initial (.inr (.error .revert)) (.inr .revert)

theorem LoopCert.horizon_step {b L frame horizon : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {initial : Machine}
    (room : FiniteLoopRoom b frame c body σ base initial horizon)
    (capacity : b + frameNeedProg body ≤ frame)
    {o : Solidity.Out C σ.H Γ} {machine : Machine} {nextBase : Nat → Fin W} {cost turns : Nat}
    (hp : CountedLoopPrefix c body σ o cost turns) (within : turns < horizon)
    (repr : Objects.StateRepr L b frame F o.st nextBase machine)
    (stack : machine.stack = initial.stack) (bases : BaseExtends σ.H base nextBase)
    (grows : Objects.GrowsAllocator b frame cost σ base initial o.st nextBase machine) :
    HorizonRelation L b frame F c body σ base initial
      (TLoop.step (horizonBody body) (fun o => c.evalT o.st) o)
      (loopTurn (fun m => exec cond 0 m) (fun m => exec code 0 m) machine) := by
  rcases cert.condition.correct repr with ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
  · obtain rfl := hw.bool_inv
    have hc' : exec cond 0 machine = .ok (machine.push (.val (bword v))) 0 := hc
    unfold TLoop.step loopTurn
    dsimp only
    rw [hv, hc']
    cases v
    · exact .done hp repr stack bases grows
    · change HorizonRelation L b frame F c body σ base initial _
        (match exec code 0 machine with
          | .ok m₂ 0 => .inl m₂
          | .ok _ (_ + 1) => .inr .fault
          | r => .inr r)
      have ha : Objects.AllocationInput b frame (allocationCostProg body o.st) o.st nextBase machine :=
        grows.nextInput (room o cost turns hp within hv)
      rcases cert.bodyCert.correct repr capacity ha with
        ⟨o', machine', nextBase', ho, ht, hr, hs, he, hg⟩ | ⟨ho, ht⟩
      · have ht' : exec code 0 machine = .ok machine' 0 := ht
        simp only [horizonBody, ho, Except.map, ht']
        refine .more (.next hp hv ho) ?_ (hs.trans stack) (bases.trans o.ext he) ?_
        · rw [← cert.stable]
          exact hr.drop body.ext
        · exact grows.comp hg
      · have ht' : exec code 0 machine = .revert := ht
        simp only [horizonBody, ho, Except.map, ht']
        exact .revert
  · have hc' : exec cond 0 machine = .revert := hc
    unfold TLoop.step loopTurn
    dsimp only
    rw [hv, hc']
    exact .revert

end Solidity.Evm.Memory.Construction
