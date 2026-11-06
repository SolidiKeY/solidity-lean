import Solidity.Evm.MemoryStorageObjectCopy

/-! Compose actual storage copies with the published owned allocation/mutation
certificates. No owner algorithm is duplicated and no heap equality is assumed.
Capacity and reached-copy bounds follow the actual source prefix. -/
namespace Solidity.Evm.Memory.CopyConstruction
variable {C : Contract}

inductive StmtFrag (b : Nat) : {Γ Δ : Ctx} → Frag Γ → Frag Δ → Stmt C Γ Δ → List Instr → Prop where
  | construction {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ} {s : Stmt C Γ Δ} {code : List Instr}
      (hs : Construction.StmtFrag b F G s code) : StmtFrag b F G s code
  | copying {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ} {s : Stmt C Γ Δ} {code : List Instr}
      (hs : Fixed.StmtFrag b F G s code) : StmtFrag b F G s code

inductive ProgFrag (b : Nat) : {Γ Δ : Ctx} → Frag Γ → Frag Δ → Prog C Γ Δ → List Instr → Prop where
  | nil {Γ : Ctx} (F : Frag Γ) : ProgFrag b F F .nil []
  | cons {Γ Δ Ξ : Ctx} {F : Frag Γ} {G : Frag Δ} {K : Frag Ξ}
      {s : Stmt C Γ Δ} {P : Prog C Δ Ξ} {head tail : List Instr}
      (hs : StmtFrag b F G s head) (hp : ProgFrag b G K P tail) :
      ProgFrag b F K (.cons s P) (head ++ tail)

structure CompiledStmt (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) where
  frag : Frag Δ
  code : List Instr
  cert : StmtFrag b F frag s code
structure CompiledProg (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (P : Prog C Γ Δ) where
  frag : Frag Δ
  code : List Instr
  cert : ProgFrag b F frag P code

/-- Owner construction selection is unchanged; only missing copy leaves fall back. -/
def compileStmt (b : Nat) {Γ Δ : Ctx} (F : Frag Γ) (s : Stmt C Γ Δ) : Option (CompiledStmt b F s) :=
  match Construction.compileStmt b F s with
  | some r => some ⟨r.frag, r.code, .construction r.cert⟩
  | none => (Fixed.compileStmt b F s).map fun r => ⟨r.frag, r.code, .copying r.cert⟩

/-- Generalized intrinsic recursion preserves both contexts at admission. -/
def compileProg (b : Nat) : {Γ Δ : Ctx} → (F : Frag Γ) → (P : Prog C Γ Δ) → Option (CompiledProg b F P)
  | _, _, F, P => Prog.casesOn (motive_2 := fun Γ _ P => (F : Frag Γ) → Option (CompiledProg b F P)) P
      (fun F => some ⟨F, [], .nil F⟩)
      (fun s P F => do
        let head ← compileStmt b F s
        let tail ← compileProg b head.frag P
        pure ⟨tail.frag, head.code ++ tail.code, .cons head.cert tail.cert⟩) F
  termination_by structural _ _ _F P => P

private theorem copy_cost_zero {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {s : Stmt C Γ Δ} {code : List Instr} (hs : Fixed.StmtFrag b F G s code) (σ : State C Γ) :
    Construction.allocationCostStmt s σ = 0 := by
  cases hs <;> rfl

theorem StmtFrag.correct {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {s : Stmt C Γ Δ} {code : List Instr} (hs : StmtFrag b F G s code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : Objects.StateRepr L b frame F σ base m) (hcap : b + frameNeedStmt s ≤ frame)
    (ha : Objects.AllocationInput b frame (Construction.allocationCostStmt s σ) σ base m)
    (hb : copyBoundStmt s σ ≤ L) :
    Objects.GrowingResult L b frame (Construction.allocationCostStmt s σ) G σ base m
      (s.run σ) (run code m) := by
  cases hs with
  | construction hs => exact hs.correct h hcap ha
  | copying hs =>
    rw [copy_cost_zero hs σ]
    exact ((hs.correct h.fixedCopy hb).objects h).growing

private theorem run_cons_revert {Γ Δ Ξ : Ctx} {σ : State C Γ}
    {s : Stmt C Γ Δ} {P : Prog C Δ Ξ} (h : s.run σ = .error .revert) :
    (Prog.cons s P).run σ = .error .revert := by
  show TRun.seq s.runR P.runR σ = _
  simp only [TRun.seq, Solidity.Stmt.run] at h ⊢
  rw [h]

theorem ProgFrag.correct {b L frame : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : ProgFrag b F G P code)
    {σ : State C Γ} {base : Nat → Fin W} {m : Machine}
    (h : Objects.StateRepr L b frame F σ base m) (hcap : b + frameNeedProg P ≤ frame)
    (ha : Objects.AllocationInput b frame (Construction.allocationCostProg P σ) σ base m)
    (hb : copyBoundProg P σ ≤ L) :
    Objects.GrowingResult L b frame (Construction.allocationCostProg P σ) G σ base m
      (P.run σ) (run code m) := by
  induction hp generalizing base m with
  | nil F => exact .inl ⟨⟨σ, List.prefix_refl _⟩, m, base, rfl, rfl, h, rfl,
      BaseExtends.refl _, fun _ _ ha _ => ha⟩
  | @cons Γ Δ Ξ F G K s P head tail hs hp ih =>
    have hcaps : b + frameNeedStmt s ≤ frame := by
      change b + max (frameNeedStmt s) (frameNeedProg P) ≤ frame at hcap
      omega
    have hcapp : b + frameNeedProg P ≤ frame := by
      change b + max (frameNeedStmt s) (frameNeedProg P) ≤ frame at hcap
      omega
    have hah : Objects.AllocationInput b frame (Construction.allocationCostStmt s σ) σ base m :=
      ha.of_le (by rw [Construction.allocationCostProg_cons]; exact Nat.le_add_right _ _)
    have hbs : copyBoundStmt s σ ≤ L := by
      rw [copyBoundProg_cons] at hb
      exact Nat.le_trans (Nat.le_max_left _ _) hb
    rcases hs.correct h hcaps hah hbs with ⟨o, m₁, base₁, ho, hc, hm, hst, hex, hal⟩ | ⟨ho, hc⟩
    · rw [Solidity.Prog.run_cons_ok ho, run_append_ok hc]
      have hcost : Construction.allocationCostProg (.cons s P) σ =
          Construction.allocationCostStmt s σ + Construction.allocationCostProg P o.st := by
        rw [Construction.allocationCostProg_cons, ho]
      have hat : Objects.AllocationInput b frame (Construction.allocationCostProg P o.st) o.st base₁ m₁ :=
        hal.nextInput (hcost ▸ ha)
      have hbt : copyBoundProg P o.st ≤ L := by
        rw [copyBoundProg_cons, ho] at hb
        exact Nat.le_trans (Nat.le_max_right _ _) hb
      rcases ih hm hcapp hat hbt with ⟨o', m₂, base₂, ho', hc', hm', hst', hex', hal'⟩ | ⟨ho', hc'⟩
      · refine .inl ⟨⟨o'.st, o.ext.trans o'.ext⟩, m₂, base₂,
          by rw [ho']; rfl, hc', hm', hst'.trans hst, hex.trans o.ext hex', ?_⟩
        rw [hcost]
        exact hal.comp hal'
      · exact .inr ⟨by rw [ho']; rfl, hc'⟩
    · exact .inr ⟨run_cons_revert ho, run_append_revert hc⟩

theorem StmtFrag.pushes_zero {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {s : Stmt C Γ Δ} {code : List Instr} (hs : StmtFrag b F G s code) : Evm.Stmt.pushes s = 0 := by
  cases hs with
  | construction hs => exact hs.pushes_zero
  | copying hs =>
    have hz := (Fixed.ProgFrag.cons hs (Fixed.ProgFrag.nil G)).pushes_zero
    change Evm.Stmt.pushes s + 0 = 0 at hz
    exact (Nat.add_zero _).symm.trans hz

theorem ProgFrag.pushes_zero {b : Nat} {Γ Δ : Ctx} {F : Frag Γ} {G : Frag Δ}
    {P : Prog C Γ Δ} {code : List Instr} (hp : ProgFrag b F G P code) : Evm.Prog.pushes P = 0 := by
  induction hp with
  | nil F => rfl
  | cons hs hp ih =>
    change Evm.Stmt.pushes _ + Evm.Prog.pushes _ = 0
    rw [hs.pushes_zero, ih]

end Solidity.Evm.Memory.CopyConstruction
