import Solidity.Evm.MemoryLoop

/-! Checked sequential composition of finite memory statements and memory loops.
Capacity is source-prefix based: a later demand is shifted by the exact cost
of the successful prefix, and unreachable suffixes generate no demand. -/
namespace Solidity.Evm.Memory.Loops

variable {C : Contract}

inductive StmtCert (b : Nat) : {Γ Δ : Ctx} → Frag Γ → Frag Δ →
    Stmt C Γ Δ → List Instr → Type where
  | finite {Γ Δ F G s code} (cert : StmtFrag (C := C) b (Γ := Γ) (Δ := Δ) F G s code) :
      StmtCert b F G s code
  | loop {Γ Δ : Ctx} {F : Frag Γ} (a : LoopAnn C Γ) (c : Val C Γ .bool)
      (body : Prog C Γ Δ) (cond code : List Instr) (G : Frag Δ)
      (hc : ValFrag b F c cond) (hb : ProgFrag b F G body code) (stable : G.restrict Γ = F) :
      StmtCert b F F (.loop a c body) [.loop cond code]

inductive ProgCert (b : Nat) : {Γ Δ : Ctx} → Frag Γ → Frag Δ →
    Prog C Γ Δ → List Instr → Type where
  | nil {Γ : Ctx} (F : Frag Γ) : ProgCert b F F .nil []
  | cons {Γ Δ Ξ F G K s P head tail}
      (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s head)
      (hp : ProgCert b (Γ := Δ) (Δ := Ξ) G K P tail) :
      ProgCert b F K (.cons s P) (head ++ tail)

/-- Exact successful-statement cost, tied to the certified source shape. -/
def StmtCert.Cost {b Γ Δ F G s code} (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code)
    (σ : State C Γ) (o : Solidity.Out C σ.H Δ) (cost : Nat) : Prop :=
  StmtCert.casesOn
    (motive := fun {Δ} _ _ _ _ _ => (σ : State C Γ) → Solidity.Out C σ.H Δ → Nat → Prop) hs
    (fun {_ _ _ s _} _ σ _ cost => cost = allocationCostStmt s σ)
    (fun _ c body _ _ _ _ _ _ σ o cost => LoopPrefix c body σ o cost) σ o cost

inductive Cost {b : Nat} : {Γ Δ : Ctx} → {F : Frag Γ} → {G : Frag Δ} →
    {P : Prog C Γ Δ} → {code : List Instr} → ProgCert b F G P code →
    (σ : State C Γ) → Solidity.Out C σ.H Δ → Nat → Prop where
  | nil {Γ F} (σ : State C Γ) : Cost (.nil F) σ ⟨σ, List.prefix_refl _⟩ 0
  | cons {Γ Δ Ξ F G K s P head tail}
      {hs : StmtCert b (Γ := Γ) (Δ := Δ) F G s head}
      {hp : ProgCert b (Γ := Δ) (Δ := Ξ) G K P tail}
      {σ : State C Γ} {o : Solidity.Out C σ.H Δ} {o' : Solidity.Out C o.st.H Ξ} {cost rest}
      (ho : s.run σ = .ok o) (hc : hs.Cost σ o cost) (ht : Cost hp o.st o' rest) :
      Cost (.cons hs hp) σ ⟨o'.st, o.ext.trans o'.ext⟩ (cost + rest)

/-- A statement's reached source allocation demands, including partial reverts. -/
def StmtCert.Demand {b Γ Δ F G s code}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code) (σ : State C Γ) (amount : Nat) : Prop :=
  StmtCert.casesOn
    (motive := fun {_} _ _ _ _ _ => State C Γ → Nat → Prop) hs
    (fun {_ _ _ s _} _ σ amount => amount = allocationCostStmt s σ)
    (fun _ c body _ _ _ _ _ _ σ amount =>
      (∃ o, LoopPrefix c body σ o amount) ∨
      (∃ o cost, LoopPrefix c body σ o cost ∧ c.evalT o.st = .ok true ∧
        amount = cost + allocationCostProg body o.st)) σ amount

def Demand {b Γ Δ F G P code} (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    (σ : State C Γ) (amount : Nat) : Prop :=
  ProgCert.casesOn
    (motive := fun {Γ _} _ _ _ _ _ => State C Γ → Nat → Prop) hp
    (fun _ _ _ => False)
    (fun {_ _ _ _ _ _ s _ _ _} hs ht σ amount => hs.Demand σ amount ∨
      ∃ (o : Solidity.Out C σ.H _) (cost rest : Nat), s.run σ = .ok o ∧
        hs.Cost σ o cost ∧ Demand ht o.st rest ∧ amount = cost + rest) σ amount

theorem Demand.head {b Γ Δ Ξ F G K s P head tail}
    {hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s head}
    {hp : ProgCert b (Γ := Δ) (Δ := Ξ) G K P tail} {σ : State C Γ} {amount}
    (h : hs.Demand σ amount) : Demand (.cons hs hp) σ amount := .inl h

theorem Demand.tail {b Γ Δ Ξ F G K s P head tail}
    {hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s head}
    {hp : ProgCert b (Γ := Δ) (Δ := Ξ) G K P tail}
    {σ : State C Γ} {o : Solidity.Out C σ.H Δ} {cost amount}
    (ho : s.run σ = .ok o) (hc : hs.Cost σ o cost) (h : Demand hp o.st amount) :
    Demand (.cons hs hp) σ (cost + amount) := .inr ⟨o, cost, amount, ho, hc, h, rfl⟩

def Room {b Γ Δ F G P code} (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    (frame : Nat) (σ : State C Γ) (base : Nat → Fin W) (m : Machine) : Prop :=
  ∀ amount, Demand hp σ amount → AllocationInput b frame amount σ base m

/-- Reserve every body temporary, rather than the loop's unchanged final context. -/
def StmtCert.need {b Γ Δ F G s code}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code) : Nat :=
  StmtCert.casesOn (motive := fun {_} _ _ _ _ _ => Nat) hs
    (fun {_ _ _ s _} _ => frameNeedStmt s)
    (fun _ _ body _ _ _ _ _ _ => max Γ.length (frameNeedProg body))

def ProgCert.need {b Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code) : Nat :=
  ProgCert.casesOn (motive := fun {_ _} _ _ _ _ _ => Nat) hp
    (fun {Γ} _ => Γ.length)
    (fun hs ht => max hs.need ht.need)

/-- The full result includes divergence without enlarging legacy GrowingResult. -/
def Result {b Γ Δ F G P code} (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    (L frame : Nat) (σ : State C Γ) (base : Nat → Fin W) (m : Machine)
    (res : TRes (Solidity.Out C σ.H Δ)) (out : Out) : Prop :=
  (∃ o m' base' cost, res = .ok o ∧ out = .ok m' 0 ∧ Cost hp σ o cost ∧
    StateRepr L b frame G o.st base' m' ∧ m'.stack = m.stack ∧ BaseExtends σ.H base base' ∧
    GrowsAllocator b frame cost σ base m o.st base' m') ∨
  (res = .error .revert ∧ out = .revert) ∨ (res = .error .diverge ∧ out = .fault)

private def StmtResult {b Γ Δ F G s code} (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code)
    (L frame : Nat) (σ : State C Γ) (base : Nat → Fin W) (m : Machine) : Prop :=
  (∃ o m' base' cost, s.run σ = .ok o ∧ run code m = .ok m' 0 ∧ hs.Cost σ o cost ∧
    StateRepr L b frame G o.st base' m' ∧ m'.stack = m.stack ∧ BaseExtends σ.H base base' ∧
    GrowsAllocator b frame cost σ base m o.st base' m') ∨
  (s.run σ = .error .revert ∧ run code m = .revert) ∨
  (s.run σ = .error .diverge ∧ run code m = .fault)

private theorem stmt_correct {b L frame Γ Δ F G s code}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (hr : StateRepr L b frame F σ base m) (cap : b + hs.need ≤ frame)
    (room : ∀ amount, hs.Demand σ amount → AllocationInput b frame amount σ base m) :
    StmtResult hs L frame σ base m := by
  cases hs with
  | finite cert =>
    rcases cert.correct hr cap (room _ rfl) with ⟨o, m', base', ho, ht, hr, hs, he, hg⟩ | ⟨ho, ht⟩
    · exact .inl ⟨o, m', base', _, ho, ht, rfl, hr, hs, he, hg⟩
    · exact .inr (.inl ⟨ho, ht⟩)
  | loop a c body cond code G hc hb stable =>
    have hcap : b + frameNeedProg body ≤ frame := by
      change b + max Γ.length (frameNeedProg body) ≤ frame at cap
      omega
    have hroom : LoopRoom b frame c body σ base m :=
      fun o cost hp hv => room _ (.inr ⟨o, cost, hp, hv, rfl⟩)
    exact (LoopCert.correct ⟨hc, G, hb, stable⟩ a hr hcap hroom)

private theorem source_cons_halt {Γ Δ Ξ : Ctx} {σ : State C Γ} {s : Stmt C Γ Δ}
    {P : Prog C Δ Ξ} {halt : THalt} (h : s.run σ = .error halt) :
    (Prog.cons s P).run σ = .error halt := by
  show TRun.seq s.runR P.runR σ = _
  simp only [TRun.seq, Solidity.Stmt.run] at h ⊢
  rw [h]

private theorem target_append_fault {head tail : List Instr} {m : Machine}
    (h : run head m = .fault) : run (head ++ tail) m = .fault := by
  simp only [run] at h ⊢
  rw [exec_append, h]
  rfl

/-- Checked sequence simulation with source-prefix capacity and exact cost. -/
theorem ProgCert.correct {b L frame Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (hr : StateRepr L b frame F σ base m) (cap : b + hp.need ≤ frame)
    (room : Room hp frame σ base m) : Result hp L frame σ base m (P.run σ) (run code m) := by
  induction hp generalizing base m with
  | nil F =>
    exact .inl ⟨⟨σ, List.prefix_refl _⟩, m, base, 0, rfl, rfl, .nil σ, hr, rfl,
      BaseExtends.refl base, fun _ _ ha _ => ha⟩
  | @cons Γ Δ Ξ F G K s P head tail hs hp ih =>
    have caps : b + hs.need ≤ frame := by change b + max hs.need hp.need ≤ frame at cap; omega
    have capp : b + hp.need ≤ frame := by change b + max hs.need hp.need ≤ frame at cap; omega
    rcases stmt_correct hs hr caps (fun amount h => room amount (.head h)) with
      ⟨o, m', base', cost, ho, ht, hc, hr', stack, he, hg⟩ | ⟨ho, ht⟩ | ⟨ho, ht⟩
    · have next : Room hp frame o.st base' m' := by
        intro amount hd
        exact hg.nextInput (room _ (.tail ho hc hd))
      rcases ih hr' capp next with
        ⟨o', m'', base'', rest, ho', ht', hc', hr'', stack', he', hg'⟩ | ⟨ho', ht'⟩ | ⟨ho', ht'⟩
      · refine .inl ⟨⟨o'.st, o.ext.trans o'.ext⟩, m'', base'', cost + rest,
          ?_, ?_, .cons ho hc hc', hr'', stack'.trans stack, he.trans o.ext he', hg.comp hg'⟩
        · rw [Solidity.Prog.run_cons_ok ho, ho']; rfl
        · rw [run_append_ok ht]; exact ht'
      · exact .inr (.inl ⟨by rw [Solidity.Prog.run_cons_ok ho, ho']; rfl,
          by rw [run_append_ok ht]; exact ht'⟩)
      · exact .inr (.inr ⟨by rw [Solidity.Prog.run_cons_ok ho, ho']; rfl,
          by rw [run_append_ok ht]; exact ht'⟩)
    · exact .inr (.inl ⟨source_cons_halt ho, run_append_revert ht⟩)
    · exact .inr (.inr ⟨source_cons_halt ho, target_append_fault ht⟩)

structure CompiledStmt (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) where
  frag : Frag Δ
  code : List Instr
  cert : StmtCert b F frag s code

structure CompiledProg (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) where
  frag : Frag Δ
  code : List Instr
  cert : ProgCert b F frag P code

private def compileFiniteStmt (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) :
    Option (CompiledStmt b F s) := do
  let compiled ← Memory.compileStmt b F s
  pure ⟨compiled.frag, compiled.code, .finite compiled.cert⟩

/-- The only new statement registration is a checked memory loop.
The tactic term generates the dependent eliminator, with no indexed matcher. -/
def compileStmt (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) :
    Option (CompiledStmt b F s) := by
  cases s
  case loop =>
    rename_i a c body
    exact do
      let condition ← Memory.compileVal b F c
      let compiled ← Memory.compileProg b F body
      if stable : compiled.frag.restrict Γ = F then
        pure ⟨F, [.loop condition.code compiled.code],
          .loop a c body condition.code compiled.code compiled.frag condition.cert compiled.cert stable⟩
      else none
  all_goals exact compileFiniteStmt b F _

def compileProg (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) :
    Option (CompiledProg b F P) :=
  Prog.casesOn (motive_2 := fun Γ Δ P => (F : Frag Γ) → Option (CompiledProg b F P)) P
    (fun F => some ⟨F, [], .nil F⟩)
    (fun s P F => do
      let head ← compileStmt b F s
      let tail ← compileProg b head.frag P
      pure ⟨tail.frag, head.code ++ tail.code, .cons head.cert tail.cert⟩) F

theorem StmtCert.pushes_zero {b Γ Δ F G s code}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code) : Evm.Stmt.pushes s = 0 := by
  cases hs with
  | finite cert => exact cert.pushes_zero
  | loop => rfl

theorem ProgCert.pushes_zero {b Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code) : Evm.Prog.pushes P = 0 := by
  induction hp with
  | nil => rfl
  | cons hs hp ih => exact Nat.add_eq_zero.mpr ⟨hs.pushes_zero, ih⟩

/-- A singleton loop retains exactly the reached-prefix capacity premise. -/
theorem room_singleton {b frame Γ Δ F a c body cond code G}
    (hc : ValFrag (C := C) b (Γ := Γ) F c cond)
    (hb : ProgFrag b (Γ := Γ) (Δ := Δ) F G body code) (stable : G.restrict Γ = F)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (room : LoopRoom b frame c body σ base m) :
    Room (.cons (.loop a c body cond code G hc hb stable) (.nil F)) frame σ base m := by
  intro amount hd
  change ((∃ o, LoopPrefix c body σ o amount) ∨
    (∃ o cost, LoopPrefix c body σ o cost ∧ c.evalT o.st = .ok true ∧
      amount = cost + allocationCostProg body o.st)) ∨ _ at hd
  rcases hd with (⟨o, hp⟩ | ⟨o, cost, hp, hv, rfl⟩) | ⟨o, cost, rest, ho, hc, hd, he⟩
  · exact hp.input room
  · exact room _ _ hp hv
  · exact hd.elim

def StmtCert.allocates {b Γ Δ F G s code}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code) : Bool :=
  StmtCert.casesOn (motive := fun {_} _ _ _ _ _ => Bool) hs
    (fun {_ _ _ s _} _ => hasAllocationStmt s)
    (fun _ _ body _ _ _ _ _ _ => hasAllocation body)

def ProgCert.allocates {b Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code) : Bool :=
  ProgCert.casesOn (motive := fun {_ _} _ _ _ _ _ => Bool) hp
    (fun _ => false)
    (fun hs ht => hs.allocates || ht.allocates)

private theorem stmt_cost_zero {b Γ Δ F G s code}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code)
    {σ : State C Γ} {o : Solidity.Out C σ.H Δ} {amount : Nat}
    (hn : hs.allocates = false) (hc : hs.Cost σ o amount) : amount = 0 := by
  cases hs with
  | finite cert =>
    rw [hc]
    simp only [allocationCostStmt, show hasAllocationStmt s = false from hn, Bool.false_eq_true, if_false]
  | loop a c body cond code G hv hb stable => exact hc.cost_zero hn

private theorem stmt_demand_zero {b Γ Δ F G s code}
    (hs : StmtCert (C := C) b (Γ := Γ) (Δ := Δ) F G s code)
    {σ : State C Γ} {amount : Nat} (hn : hs.allocates = false)
    (hd : hs.Demand σ amount) : amount = 0 := by
  cases hs with
  | finite cert =>
    rw [hd]
    simp only [allocationCostStmt, show hasAllocationStmt s = false from hn, Bool.false_eq_true, if_false]
  | loop a c body cond code G hv hb stable =>
    rcases hd with ⟨o, hp⟩ | ⟨o, cost, hp, _, rfl⟩
    · exact hp.cost_zero hn
    · rw [hp.cost_zero hn, allocationCostProg_zero body hn]

/-- Nonallocating source prefixes demand exactly zero cells. -/
theorem demand_nonallocating {b Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    (hn : hp.allocates = false) {σ : State C Γ} {amount : Nat}
    (hd : Demand hp σ amount) : amount = 0 := by
  induction hp generalizing amount with
  | nil F => exact hd.elim
  | @cons Γ Δ Ξ F G K s P head tail hs hp ih =>
    have hh : hs.allocates = false ∧ hp.allocates = false := Bool.or_eq_false_iff.mp hn
    rcases hd with hd | ⟨o, cost, rest, ho, hc, hd, rfl⟩
    · exact stmt_demand_zero hs hh.1 hd
    · rw [stmt_cost_zero hs hh.1 hc, ih hh.2 hd]

/-- All nonallocating programs have inhabited capacity, including diverging loops. -/
theorem room_nonallocating {b frame Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    (hn : hp.allocates = false) (σ : State C Γ) (base : Nat → Fin W) (m : Machine) :
    Room hp frame σ base m := fun _ hd => .inl (demand_nonallocating hp hn hd)

/-- An allocating prefix followed by nonallocating loops needs only its own
reached allocation cost, even when the suffix diverges. -/
theorem room_cons_nonallocating {b frame Γ Δ Ξ F G K s P head tail}
    (hs : StmtFrag (C := C) b (Γ := Γ) (Δ := Δ) F G s head)
    (hp : ProgCert b (Γ := Δ) (Δ := Ξ) G K P tail) (hn : hp.allocates = false)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (ha : AllocationInput b frame (allocationCostStmt s σ) σ base m) :
    Room (.cons (.finite hs) hp) frame σ base m := by
  intro amount hd
  rcases hd with hd | ⟨o, cost, rest, ho, hc, hd, rfl⟩
  · exact hd ▸ ha
  · change cost = allocationCostStmt s σ at hc
    rw [hc, demand_nonallocating hp hn hd, Nat.add_zero]
    exact ha

/-- Recognize a reached finite prefix followed by a nonallocating suffix.
The recognition computes a cost, never an unproved capacity or simulation. -/
def prefixBudget {b Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code) (σ : State C Γ) : Option Nat :=
  ProgCert.casesOn
    (motive := fun {Γ _} _ _ _ _ _ => State C Γ → Option Nat) hp
    (fun _ _ => some 0)
    (fun {Γ _ _ _ _ _ _ _ _ _} hs ht σ =>
      StmtCert.casesOn
        (motive := fun {Δ} _ _ _ _ _ =>
          (State C Δ → Option Nat) → Bool → State C Γ → Option Nat) hs
        (fun {_ _ _ s _} _ rest allocates σ =>
          if allocates then
            match s.run σ with
            | .ok o => (rest o.st).map (allocationCostStmt s σ + ·)
            | .error _ => some (allocationCostStmt s σ)
          else some (allocationCostStmt s σ))
        (fun {_ _} _ _ _ _ _ _ _ _ _ _ _ _ => none)
        (fun τ => prefixBudget ht τ) ht.allocates σ) σ

private theorem prefixBudget_finite {b Γ Δ Ξ F G K s P head tail}
    (hs : StmtFrag (C := C) b (Γ := Γ) (Δ := Δ) F G s head)
    (hp : ProgCert b (Γ := Δ) (Δ := Ξ) G K P tail) (σ : State C Γ) :
    prefixBudget (.cons (.finite hs) hp) σ =
      if hp.allocates then
        match s.run σ with
        | .ok o => (prefixBudget hp o.st).map (allocationCostStmt s σ + ·)
        | .error _ => some (allocationCostStmt s σ)
      else some (allocationCostStmt s σ) := rfl

/-- Recognition bounds every actual source demand; it skips a nonallocating
suffix rather than evaluating a possibly divergent loop. -/
theorem demand_le_prefixBudget {b Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code) {budget amount : Nat}
    {σ : State C Γ} (hb : prefixBudget hp σ = some budget)
    (hd : Demand hp σ amount) : amount ≤ budget := by
  induction hp generalizing budget amount with
  | nil F => exact hd.elim
  | @cons Γ Δ Ξ F G K s P head tail hs ht ih =>
    cases hs with
    | loop => change none = some budget at hb; cases hb
    | finite cert =>
      rw [prefixBudget_finite] at hb
      cases hn : ht.allocates with
      | false =>
        simp only [hn, Bool.false_eq_true, if_false] at hb
        cases hb
        rcases hd with hd | ⟨o, cost, rest, ho, hc, hd, rfl⟩
        · exact hd ▸ Nat.le_refl _
        · change cost = allocationCostStmt s σ at hc
          rw [hc, demand_nonallocating ht hn hd, Nat.add_zero]
          exact Nat.le_refl _
      | true =>
        simp only [hn, if_true] at hb
        cases hsrun : s.run σ with
        | error halt =>
          simp only [hsrun] at hb
          cases hb
          rcases hd with hd | ⟨o, cost, rest, ho, hc, hd, rfl⟩
          · exact hd ▸ Nat.le_refl _
          · rw [hsrun] at ho
            cases ho
        | ok out =>
          simp only [hsrun] at hb
          cases htbudget : prefixBudget ht out.st with
          | none => rw [htbudget] at hb; cases hb
          | some restBudget =>
            rw [htbudget] at hb
            cases hb
            rcases hd with hd | ⟨o, cost, rest, ho, hc, hd, rfl⟩
            · rw [hd]
              exact Nat.le_add_right _ _
            · have he : o = out := Except.ok.inj (ho.symm.trans hsrun)
              subst o
              change cost = allocationCostStmt s σ at hc
              rw [hc]
              exact Nat.add_le_add_left (ih htbudget hd) _

theorem room_of_prefixBudget {b frame Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code) {amount : Nat}
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (hb : prefixBudget hp σ = some amount) (ha : AllocationInput b frame amount σ base m) :
    Room hp frame σ base m := fun _ hd => ha.of_le (demand_le_prefixBudget hp hb hd)

/-- Exhaustion is impossible in the certified memory-loop fragment, rather than
being silently identified with another halt. -/
theorem ProgCert.not_exhausted {b L frame Γ Δ F G P code}
    (hp : ProgCert (C := C) b (Γ := Γ) (Δ := Δ) F G P code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (hr : StateRepr L b frame F σ base m) (cap : b + hp.need ≤ frame)
    (room : Room hp frame σ base m) : P.run σ ≠ .error .exhausted := by
  rcases hp.correct hr cap room with ⟨o, _, _, _, ho, _⟩ | ⟨ho, _⟩ | ⟨ho, _⟩ <;>
    rw [ho] <;> intro h <;> cases h

end Solidity.Evm.Memory.Loops
