import Solidity.Goals.ElabTotal

/-!
Exact control-arm execution receipts for `Solidity.Goals.loweringBySimulation`.
These compose child computations; they do not establish fragment coverage or
`Diagram.Total`. All reader settings, local contexts, fresh counters and memo
transitions remain explicit in the receipts.
-/
namespace Solidity.Correctness.Lowering.Sim.CoverageControl

open Solidity.Goals

variable [FreshNames] (C : Contract)

/-- Sequence two successful computations, retaining both state layers. -/
theorem bind_success {α β : Type} (x : ElabM α) (f : α → ElabM β)
    (sc : ElabScope) (s₀ s₁ s₂ : ECtx × Nat) (m₀ m₁ m₂ : CallMemo)
    (a : α) (b : β)
    (hx : ((x.run sc).run s₀).run m₀ = .ok ((a, s₁), m₁))
    (hf : (((f a).run sc).run s₁).run m₁ = .ok ((b, s₂), m₂)) :
    (((x >>= f).run sc).run s₀).run m₀ = .ok ((b, s₂), m₂) := by
  change (Except.bind (((x.run sc).run s₀).run m₀) _) = _
  rw [hx]
  exact hf

/-- The condition is checked first, then both branches are elaborated in order,
even when the condition is a constant. Each branch receipt starts at its
predecessor's exact state and memo. -/
theorem ite_success (rc : ElabRec C) (c : RawExpr) (thn els : List RawStmt)
    (sc : ElabScope) (s₀ s₁ s₂ s₃ : ECtx × Nat) (m₀ m₁ m₂ m₃ : CallMemo)
    (v : Val C (ECtx.toNCtx s₀.1).ctx .bool)
    (t e : Blk C (ECtx.toNCtx s₀.1).ctx)
    (hc : (((checkIn C (ECtx.toNCtx s₀.1) .bool c).run sc).run s₀).run m₀ =
      .ok ((v, s₁), m₁))
    (ht : (((rc.elabScope (ECtx.toNCtx s₀.1) thn).run sc).run s₁).run m₁ =
      .ok ((t, s₂), m₂))
    (he : (((rc.elabScope (ECtx.toNCtx s₀.1) els).run sc).run s₂).run m₂ =
      .ok ((e, s₃), m₃)) :
    (((elabStmt1With C rc (.ite c thn els)).run sc).run s₀).run m₀ =
      .ok (([.of (ECtx.toNCtx s₀.1) (.ite v t.2 e.2)], s₃), m₃) := by
  change ((((checkIn C (ECtx.toNCtx s₀.1) .bool c) >>= fun v => do
    let t ← rc.elabScope (ECtx.toNCtx s₀.1) thn
    let e ← rc.elabScope (ECtx.toNCtx s₀.1) els
    pure [SStmt.of (ECtx.toNCtx s₀.1) (.ite v t.2 e.2)]).run sc).run s₀).run m₀ = _
  apply bind_success _ _ sc s₀ s₁ s₃ m₀ m₁ m₃ v _ hc
  apply bind_success _ _ sc s₁ s₂ s₃ m₁ m₂ m₃ t _ ht
  apply bind_success _ _ sc s₂ s₃ s₃ m₂ m₃ m₃ e _ he
  rfl

/-- The canonical lowered loop with default annotation emits `LoopAnn.auto`.
Its condition uses the actual loop-expression callback, before the body scope. -/
theorem loop_default_success (rc : ElabRec C) (c : RawExpr) (body : List RawStmt)
    (sc : ElabScope) (s₀ s₁ s₂ : ECtx × Nat) (m₀ m₁ m₂ : CallMemo)
    (v : Val C (ECtx.toNCtx s₀.1).ctx .bool) (b : Blk C (ECtx.toNCtx s₀.1).ctx)
    (hc : (((rc.loopExpr (ECtx.toNCtx s₀.1) .bool c "condition").run sc).run s₀).run m₀ =
      .ok ((v, s₁), m₁))
    (hb : (((rc.elabScope (ECtx.toNCtx s₀.1) body).run sc).run s₁).run m₁ =
      .ok ((b, s₂), m₂)) :
    (((elabStmt1With C rc (.loop {} c body)).run sc).run s₀).run m₀ =
      .ok (([.of (ECtx.toNCtx s₀.1) (.loop .auto v b.2)], s₂), m₂) := by
  change ((((rc.loopExpr (ECtx.toNCtx s₀.1) .bool c "condition") >>= fun v => do
    let b ← rc.elabScope (ECtx.toNCtx s₀.1) body
    pure [SStmt.of (ECtx.toNCtx s₀.1) (.loop .auto v b.2)]).run sc).run s₀).run m₀ = _
  apply bind_success _ _ sc s₀ s₁ s₂ m₀ m₁ m₂ v _ hc
  apply bind_success _ _ sc s₁ s₂ s₂ m₁ m₂ m₂ b _ hb
  rfl

/-- The producer equations needed here, isolated from the kernel-totality
assumption so clients cannot mistake it for an established theorem. -/
theorem producer_equations (hk : Solidity.Goals.elabKernelTotal) :
    elabStmt1 C = elabStmt1With C (elabRec C ()) ∧
    (elabRec C ()).loopExpr = loopExpr C ∧
    (elabRec C ()).elabScope = elabScope C := by
  obtain ⟨⟨-, -, -, hstmt, -, -⟩, names, -⟩ := hk.1 C
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, nstmt, nloop, -, -, -, nscope, _⟩ := names
  exact ⟨nstmt ▸ hstmt, nloop, nscope⟩

/-- Conditional composition at the actual producer, conditional only on the
explicit kernel interface and the three individual child executions. -/
theorem producer_ite_success (hk : Solidity.Goals.elabKernelTotal)
    (c : RawExpr) (thn els : List RawStmt)
    (sc : ElabScope) (s₀ s₁ s₂ s₃ : ECtx × Nat) (m₀ m₁ m₂ m₃ : CallMemo)
    (v : Val C (ECtx.toNCtx s₀.1).ctx .bool)
    (t e : Blk C (ECtx.toNCtx s₀.1).ctx)
    (hc : (((checkIn C (ECtx.toNCtx s₀.1) .bool c).run sc).run s₀).run m₀ =
      .ok ((v, s₁), m₁))
    (ht : (((elabScope C (ECtx.toNCtx s₀.1) thn).run sc).run s₁).run m₁ =
      .ok ((t, s₂), m₂))
    (he : (((elabScope C (ECtx.toNCtx s₀.1) els).run sc).run s₂).run m₂ =
      .ok ((e, s₃), m₃)) :
    (((elabStmt1 C (.ite c thn els)).run sc).run s₀).run m₀ =
      .ok (([.of (ECtx.toNCtx s₀.1) (.ite v t.2 e.2)], s₃), m₃) := by
  obtain ⟨hstmt, -, hscope⟩ := producer_equations C hk
  rw [hstmt]
  apply ite_success C (elabRec C ()) c thn els sc s₀ s₁ s₂ s₃ m₀ m₁ m₂ m₃ v t e hc
  · simpa only [hscope] using ht
  · simpa only [hscope] using he

/-- Default lowered-loop composition at the actual producer; arbitrary
annotations and raw-loop lowering are outside this helper's conclusion. -/
theorem producer_loop_default_success (hk : Solidity.Goals.elabKernelTotal)
    (c : RawExpr) (body : List RawStmt)
    (sc : ElabScope) (s₀ s₁ s₂ : ECtx × Nat) (m₀ m₁ m₂ : CallMemo)
    (v : Val C (ECtx.toNCtx s₀.1).ctx .bool) (b : Blk C (ECtx.toNCtx s₀.1).ctx)
    (hc : (((loopExpr C (ECtx.toNCtx s₀.1) .bool c "condition").run sc).run s₀).run m₀ =
      .ok ((v, s₁), m₁))
    (hb : (((elabScope C (ECtx.toNCtx s₀.1) body).run sc).run s₁).run m₁ =
      .ok ((b, s₂), m₂)) :
    (((elabStmt1 C (.loop {} c body)).run sc).run s₀).run m₀ =
      .ok (([.of (ECtx.toNCtx s₀.1) (.loop .auto v b.2)], s₂), m₂) := by
  obtain ⟨hstmt, hloop, hscope⟩ := producer_equations C hk
  rw [hstmt]
  apply loop_default_success C (elabRec C ()) c body sc s₀ s₁ s₂ m₀ m₁ m₂ v b
  · simpa only [hloop] using hc
  · simpa only [hscope] using hb

end Solidity.Correctness.Lowering.Sim.CoverageControl
