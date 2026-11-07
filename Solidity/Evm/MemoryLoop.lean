import Solidity.Evm.MemoryCompile

/-!
# Checked memory loops

Finite prefixes carry their exact reached allocation cost. Capacity quantifies
those prefixes, including a turn whose body later reverts. No bound on iteration
count or successful-termination premise is used. The body is the existing finite
memory fragment; unsupported body statements remain refused by its compiler.
-/
-- Retain the existing typed loop-prefix proof reductions on Lean 4.35.
set_option backward.isDefEq.respectTransparency false

namespace Solidity.Evm.Memory

variable {C : Contract} {Γ Δ : Ctx}

/-- The source states reached after successful turns, with their exact cost. -/
inductive LoopPrefix (c : Val C Γ .bool) (body : Prog C Γ Δ) (σ : State C Γ) :
    Solidity.Out C σ.H Γ → Nat → Prop where
  | start : LoopPrefix c body σ ⟨σ, List.prefix_refl _⟩ 0
  | next {o : Solidity.Out C σ.H Γ} {cost : Nat} {o' : Solidity.Out C o.st.H Δ}
      (hpref : LoopPrefix c body σ o cost) (cond : c.evalT o.st = .ok true)
      (step : body.run o.st = .ok o') :
      LoopPrefix c body σ ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩
        (cost + allocationCostProg body o.st)

/-- Room for each actually reached allocating turn, measured at the initial
cursor. A failed condition or zero turns demand no unreachable allocation. -/
def LoopRoom (b frame : Nat) (c : Val C Γ .bool) (body : Prog C Γ Δ)
    (σ : State C Γ) (base : Nat → Fin W) (m : Machine) : Prop :=
  ∀ (o : Solidity.Out C σ.H Γ) (cost : Nat), LoopPrefix c body σ o cost →
    c.evalT o.st = .ok true →
    AllocationInput b frame (cost + allocationCostProg body o.st) σ base m

/-- Nonallocating bodies have a vacuous capacity premise even when they diverge. -/
theorem LoopPrefix.cost_zero {c : Val C Γ .bool} {body : Prog C Γ Δ} {σ : State C Γ}
    {o : Solidity.Out C σ.H Γ} {cost : Nat} (h : LoopPrefix c body σ o cost)
    (ha : hasAllocation body = false) : cost = 0 := by
  induction h with
  | start => rfl
  | next hpref cond step ih => rw [ih, allocationCostProg_zero body ha]

theorem loopRoom_nonallocating {b frame : Nat} (c : Val C Γ .bool) (body : Prog C Γ Δ)
    (ha : hasAllocation body = false) (σ : State C Γ) (base : Nat → Fin W) (m : Machine) :
    LoopRoom b frame c body σ base m := by
  intro o cost hp _
  exact .inl (by rw [hp.cost_zero ha, allocationCostProg_zero body ha])

/-- Every completed prefix fits whenever every reached turn fits. -/
theorem LoopPrefix.input {b frame : Nat} {c : Val C Γ .bool} {body : Prog C Γ Δ}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (room : LoopRoom b frame c body σ base m) {o : Solidity.Out C σ.H Γ} {cost : Nat}
    (hp : LoopPrefix c body σ o cost) : AllocationInput b frame cost σ base m := by
  cases hp with
  | start => exact .inl rfl
  | next hp hc hs => exact room _ _ hp hc

/-- A useful inhabited capacity witness for bodies that disable their condition.
This is a witness lemma, not a premise of the general loop simulation. -/
theorem loopRoom_one_turn {b frame : Nat} (c : Val C Γ .bool) (body : Prog C Γ Δ)
    (σ : State C Γ) (base : Nat → Fin W) (m : Machine)
    (stops : ∀ (τ : State C Γ) (o : Solidity.Out C τ.H Δ),
      body.run τ = .ok o → c.evalT (o.st.drop body.ext) = .ok false)
    (room : AllocationInput b frame (allocationCostProg body σ) σ base m) :
    LoopRoom b frame c body σ base m := by
  intro o cost hp hc
  cases hp with
  | start => simpa only [Nat.zero_add] using room
  | next hp hv hs =>
    have hf := stops _ _ hs
    rw [hf] at hc
    cases hc

/-- Reproduce the old public memory compiler's actual unsupported shape. -/
theorem legacy_loop_refused (b : Nat) (F : Frag Γ) (a : LoopAnn C Γ)
    (c : Val C Γ .bool) (body : Prog C Γ Δ) :
    Memory.compileStmt b F (.loop a c body) = none := rfl

/-- A typed loop certificate reuses the checked finite memory-body compiler. -/
structure LoopCert (b : Nat) (F : Frag Γ) (c : Val C Γ .bool) (body : Prog C Γ Δ)
    (cond code : List Instr) where
  condition : ValFrag b F c cond
  bodyFrag : Frag Δ
  bodyCert : ProgFrag b F bodyFrag body code
  stable : bodyFrag.restrict Γ = F

/-- Success preserves the complete memory relation and the exact prefix cost;
revert and divergence remain distinct, and exhaustion is never success. -/
def LoopResult (L b frame : Nat) (F : Frag Γ) (c : Val C Γ .bool) (body : Prog C Γ Δ)
    (σ : State C Γ) (base : Nat → Fin W) (m : Machine)
    (res : TRes (Solidity.Out C σ.H Γ)) (out : Out) : Prop :=
  (∃ o m' base' cost, res = .ok o ∧ out = .ok m' 0 ∧
    LoopPrefix c body σ o cost ∧ StateRepr L b frame F o.st base' m' ∧
    m'.stack = m.stack ∧ BaseExtends σ.H base base' ∧
    GrowsAllocator b frame cost σ base m o.st base' m') ∨
  (res = .error .revert ∧ out = .revert) ∨
  (res = .error .diverge ∧ out = .fault)

private inductive MemoryTurn (L b frame : Nat) (F : Frag Γ) (c : Val C Γ .bool)
    (body : Prog C Γ Δ) (σ : State C Γ) (base : Nat → Fin W) (m₀ : Machine) :
    Solidity.Out C σ.H Γ ⊕ TRes (Solidity.Out C σ.H Γ) → Machine ⊕ Out → Prop where
  | more {o m base' cost} (hpref : LoopPrefix c body σ o cost)
      (repr : StateRepr L b frame F o.st base' m) (stack : m.stack = m₀.stack)
      (hbase : BaseExtends σ.H base base')
      (grows : GrowsAllocator b frame cost σ base m₀ o.st base' m) :
      MemoryTurn L b frame F c body σ base m₀ (.inl o) (.inl m)
  | done {o m base' cost} (hpref : LoopPrefix c body σ o cost)
      (repr : StateRepr L b frame F o.st base' m) (stack : m.stack = m₀.stack)
      (hbase : BaseExtends σ.H base base')
      (grows : GrowsAllocator b frame cost σ base m₀ o.st base' m) :
      MemoryTurn L b frame F c body σ base m₀ (.inr (.ok o)) (.inr (.ok m 0))
  | revert : MemoryTurn L b frame F c body σ base m₀ (.inr (.error .revert)) (.inr .revert)

private def loopBody (body : Prog C Γ Δ) {H : HTy} (o : Solidity.Out C H Γ) :
    TRes (Solidity.Out C H Γ) :=
  (body.run o.st).map fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩

private theorem memory_loop_turn {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {m₀ : Machine}
    (room : LoopRoom b frame c body σ base m₀) (cap : b + frameNeedProg body ≤ frame)
    {o : Solidity.Out C σ.H Γ} {m : Machine} {base' : Nat → Fin W} {cost : Nat}
    (hpref : LoopPrefix c body σ o cost) (repr : StateRepr L b frame F o.st base' m)
    (stack : m.stack = m₀.stack) (hbase : BaseExtends σ.H base base')
    (grows : GrowsAllocator b frame cost σ base m₀ o.st base' m) :
    MemoryTurn L b frame F c body σ base m₀
      (TLoop.step (loopBody body) (fun o => c.evalT o.st) o)
      (loopTurn (fun m => exec cond 0 m) (fun m => exec code 0 m) m) := by
  rcases cert.condition.correct repr with ⟨v, w, hv, hw, hc⟩ | ⟨hv, hc⟩
  · obtain rfl := hw.bool_inv
    have hc' : exec cond 0 m = .ok (m.push (.val (bword v))) 0 := hc
    unfold TLoop.step loopTurn
    dsimp only
    rw [hv, hc']
    cases v
    · exact .done hpref repr stack hbase grows
    · change MemoryTurn L b frame F c body σ base m₀ _
        (match exec code 0 m with
          | .ok m₂ 0 => .inl m₂
          | .ok _ (_ + 1) => .inr .fault
          | r => .inr r)
      have ha : AllocationInput b frame (allocationCostProg body o.st) o.st base' m :=
        grows.nextInput (room o cost hpref hv)
      rcases cert.bodyCert.correct repr cap ha with
        ⟨o', m', base'', ho, ht, hr, hs, he, hg⟩ | ⟨ho, ht⟩
      · have ht' : exec code 0 m = .ok m' 0 := ht
        simp only [loopBody, ho, Except.map, ht']
        refine .more (.next hpref hv ho) ?_ (hs.trans stack) (hbase.trans o.ext he) ?_
        · rw [← cert.stable]
          exact hr.drop body.ext
        · exact grows.comp hg
      · have ht' : exec code 0 m = .revert := ht
        simp only [loopBody, ho, Except.map, ht']
        exact .revert
  · have hc' : exec cond 0 m = .revert := hc
    unfold TLoop.step loopTurn
    dsimp only
    rw [hv, hc']
    exact .revert

private theorem memory_loop_iter {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) {σ : State C Γ} {base : Nat → Fin W} {m₀ : Machine}
    (room : LoopRoom b frame c body σ base m₀) (cap : b + frameNeedProg body ≤ frame) :
    ∀ n {o : Solidity.Out C σ.H Γ} {m : Machine} {base' : Nat → Fin W} {cost : Nat},
      LoopPrefix c body σ o cost → StateRepr L b frame F o.st base' m →
      m.stack = m₀.stack → BaseExtends σ.H base base' →
      GrowsAllocator b frame cost σ base m₀ o.st base' m →
      MemoryTurn L b frame F c body σ base m₀
        (TLoop.iterN (loopBody body) (fun o => c.evalT o.st) n o)
        (loopIterN (fun m => exec cond 0 m) (fun m => exec code 0 m) n m)
  | 0, _, _, _, _, hp, hr, hs, he, hg => .more hp hr hs he hg
  | n + 1, _, _, _, _, hp, hr, hs, he, hg => by
    have ht := memory_loop_turn cert room cap hp hr hs he hg
    simp only [TLoop.iterN, loopIterN]
    revert ht
    generalize TLoop.step _ _ _ = A
    generalize loopTurn _ _ _ = B
    intro ht
    cases ht with
    | more hp hr hs he hg => exact memory_loop_iter cert room cap n hp hr hs he hg
    | done hp hr hs he hg => exact .done hp hr hs he hg
    | revert => exact .revert

/-- Unbounded loop simulation, including allocations, exits and divergence. -/
theorem LoopCert.correct {b L frame : Nat} {F : Frag Γ}
    {c : Val C Γ .bool} {body : Prog C Γ Δ} {cond code : List Instr}
    (cert : LoopCert b F c body cond code) (a : LoopAnn C Γ)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (repr : StateRepr L b frame F σ base m) (cap : b + frameNeedProg body ≤ frame)
    (room : LoopRoom b frame c body σ base m) :
    LoopResult L b frame F c body σ base m ((Stmt.loop a c body).run σ)
      (run [.loop cond code] m) := by
  have hcode : run [.loop cond code] m =
      loopRun (fun m => exec cond 0 m) (fun m => exec code 0 m) m := by
    show (Instr.step (.loop cond code) m).bind (fun m' k' => exec [] k' m') = _
    simp only [Instr.step]
    cases loopRun _ _ m <;> rfl
  rw [hcode, Stmt.run_loop]
  change LoopResult L b frame F c body σ base m
    (TLoop.run (loopBody body) (fun o => c.evalT o.st) ⟨σ, List.prefix_refl _⟩)
    (loopRun (fun m => exec cond 0 m) (fun m => exec code 0 m) m)
  have initial : GrowsAllocator b frame 0 σ base m σ base m :=
    fun _ _ ha _ => ha
  by_cases hex : ∃ r n, TLoop.iterN (loopBody body) (fun o => c.evalT o.st) n
      ⟨σ, List.prefix_refl _⟩ = .inr r
  · obtain ⟨r, n, hn⟩ := hex
    have hrel := memory_loop_iter cert room cap n LoopPrefix.start repr rfl
      (BaseExtends.refl base) initial
    rw [hn] at hrel
    rw [TLoop.run_of_iterN hn]
    generalize hB : loopIterN _ _ n m = B at hrel
    cases hrel with
    | done hp hr hs he hg => exact .inl ⟨_, _, _, _, rfl, loopRun_of_iterN hB, hp, hr, hs, he, hg⟩
    | revert => exact .inr (.inl ⟨rfl, loopRun_of_iterN hB⟩)
  · have hrun : TLoop.run (loopBody body) (fun o => c.evalT o.st)
        ⟨σ, List.prefix_refl _⟩ = .error .diverge := by
      simp only [TLoop.run, hex, dif_neg, not_false_eq_true]
    rw [hrun]
    refine .inr (.inr ⟨rfl, loopRun_of_forall fun n => ?_⟩)
    have hrel := memory_loop_iter cert room cap n LoopPrefix.start repr rfl
      (BaseExtends.refl base) initial
    generalize hA : TLoop.iterN _ _ n _ = A at hrel
    generalize hB : loopIterN _ _ n m = B at hrel
    cases hrel with
    | more => exact ⟨_, rfl⟩
    | done => exact (hex ⟨_, n, hA⟩).elim
    | revert => exact (hex ⟨_, n, hA⟩).elim

end Solidity.Evm.Memory
