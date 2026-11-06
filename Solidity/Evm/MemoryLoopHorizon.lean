import Solidity.Evm.MemoryLoop

/-!
Public finite-horizon transport for the actual memory-loop source and target
iterators. Pending prefixes retain their physical state and allocation growth;
they are not classified as divergence. Capacity is the existing `LoopRoom`
contract (not a newly assumed simulation law). Finite-only capacity weakening
and enclosing-program horizon transport are separate obligations.
-/
namespace Solidity.Evm.Memory
variable {C : Contract} {Γ Δ : Ctx}

/-- Matched finite observations, retaining exact physical facts for pending and successful states.
`done` does not independently assert a false condition; the transport theorem
connects it to the actual iterators. -/
inductive HorizonRelation (L b frame : Nat) (F : Frag Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Δ) (σ : State C Γ) (base : Nat → Fin W) (m₀ : Machine) :
    Solidity.Out C σ.H Γ ⊕ TRes (Solidity.Out C σ.H Γ) → Machine ⊕ Out → Prop where
  | more {o m base' cost} (hpref : LoopPrefix c body σ o cost)
      (repr : StateRepr L b frame F o.st base' m) (stack : m.stack = m₀.stack)
      (hbase : BaseExtends σ.H base base')
      (grows : GrowsAllocator b frame cost σ base m₀ o.st base' m) :
      HorizonRelation L b frame F c body σ base m₀ (.inl o) (.inl m)
  | done {o m base' cost} (hpref : LoopPrefix c body σ o cost)
      (repr : StateRepr L b frame F o.st base' m) (stack : m.stack = m₀.stack)
      (hbase : BaseExtends σ.H base base')
      (grows : GrowsAllocator b frame cost σ base m₀ o.st base' m) :
      HorizonRelation L b frame F c body σ base m₀ (.inr (.ok o)) (.inr (.ok m 0))
  | revert : HorizonRelation L b frame F c body σ base m₀ (.inr (.error .revert)) (.inr .revert)

/-- Actual source body execution followed by the existing scope drop. -/
def horizonBody (body : Prog C Γ Δ) {H : HTy} (o : Solidity.Out C H Γ) :
    TRes (Solidity.Out C H Γ) :=
  (body.run o.st).map fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩

/-- One actual condition/body turn, including condition and body reverts. -/
theorem LoopCert.horizon_step {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {m₀ : Machine}
    (room : LoopRoom b frame c body σ base m₀) (cap : b + frameNeedProg body ≤ frame)
    {o : Solidity.Out C σ.H Γ} {m : Machine} {base' : Nat → Fin W} {cost : Nat}
    (hpref : LoopPrefix c body σ o cost) (repr : StateRepr L b frame F o.st base' m)
    (stack : m.stack = m₀.stack) (hbase : BaseExtends σ.H base base')
    (grows : GrowsAllocator b frame cost σ base m₀ o.st base' m) :
    HorizonRelation L b frame F c body σ base m₀
      (TLoop.step (horizonBody body) (fun o => c.evalT o.st) o)
      (loopTurn (fun m => exec cond 0 m) (fun m => exec code 0 m) m) := by
  rcases cert.condition.correct repr with ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
  · obtain rfl := hw.bool_inv
    have hc' : exec cond 0 m = .ok (m.push (.val (bword v))) 0 := hc
    unfold TLoop.step loopTurn
    dsimp only
    rw [hv, hc']
    cases v
    · exact .done hpref repr stack hbase grows
    · change HorizonRelation L b frame F c body σ base m₀ _
        (match exec code 0 m with
          | .ok m₂ 0 => .inl m₂
          | .ok _ (_ + 1) => .inr .fault
          | r => .inr r)
      have ha : AllocationInput b frame (allocationCostProg body o.st) o.st base' m :=
        grows.nextInput (room o cost hpref hv)
      rcases cert.bodyCert.correct repr cap ha with
        ⟨o', m', base'', ho, ht, hr, hs, he, hg⟩ | ⟨ho, ht⟩
      · have ht' : exec code 0 m = .ok m' 0 := ht
        simp only [horizonBody, ho, Except.map, ht']
        refine .more (.next hpref hv ho) ?_ (hs.trans stack) (hbase.trans o.ext he) ?_
        · rw [← cert.stable]
          exact hr.drop body.ext
        · exact grows.comp hg
      · have ht' : exec code 0 m = .revert := ht
        simp only [horizonBody, ho, Except.map, ht']
        exact .revert
  · have hc' : exec cond 0 m = .revert := hc
    unfold TLoop.step loopTurn
    dsimp only
    rw [hv, hc']
    exact .revert

/-- Generalized transport from any represented reached prefix. -/
theorem LoopCert.horizon_iter {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {m₀ : Machine}
    (room : LoopRoom b frame c body σ base m₀) (cap : b + frameNeedProg body ≤ frame) :
    ∀ n {o : Solidity.Out C σ.H Γ} {m : Machine} {base' : Nat → Fin W} {cost : Nat},
      LoopPrefix c body σ o cost → StateRepr L b frame F o.st base' m →
      m.stack = m₀.stack → BaseExtends σ.H base base' →
      GrowsAllocator b frame cost σ base m₀ o.st base' m →
      HorizonRelation L b frame F c body σ base m₀
        (TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n o)
        (loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n m)
  | 0, _, _, _, _, hp, hr, hs, he, hg => .more hp hr hs he hg
  | n + 1, _, _, _, _, hp, hr, hs, he, hg => by
    have ht := LoopCert.horizon_step cert room cap hp hr hs he hg
    simp only [TLoop.iterN, loopIterN]
    revert ht
    generalize TLoop.step _ _ _ = A
    generalize loopTurn _ _ _ = B
    intro ht
    cases ht with
    | more hp hr hs he hg => exact LoopCert.horizon_iter cert room cap n hp hr hs he hg
    | done hp hr hs he hg => exact .done hp hr hs he hg
    | revert => exact .revert

/-- Public initial-state interface, valid at every finite horizon, including zero.
The body uses its actual unbounded source run, as in `MemoryLoop`; this is not
recursive per-statement fuel semantics. -/
theorem LoopCert.correct_horizon {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ}
    {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m)
    (cap : b + frameNeedProg body ≤ frame)
    (room : LoopRoom b frame c body σ base m) (n : Nat) :
    HorizonRelation L b frame F c body σ base m
      (TLoop.iterN (horizonBody body) (fun o => c.evalT o.st) n
        ⟨σ, List.prefix_refl _⟩)
      (loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n m) :=
  cert.horizon_iter room cap n LoopPrefix.start repr rfl
    (BaseExtends.refl base) (fun _ _ ha _ => ha)

/-- A pending source horizon cannot be reported as a completed target execution. -/
theorem HorizonRelation.pending_target {L b frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {σ : State C Γ}
    {base : Nat → Fin W} {m₀ : Machine} {o : Solidity.Out C σ.H Γ}
    {r : Machine ⊕ Out}
    (h : HorizonRelation L b frame F c body σ base m₀ (.inl o) r) :
    ∃ m, r = .inl m := by
  cases h with
  | more => exact ⟨_, rfl⟩

end Solidity.Evm.Memory
