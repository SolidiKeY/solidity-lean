import Solidity.Roadmap.V16.Transactions
import Solidity.Calculus.Lifetime

/-!
# Scoped consumers of existing box, diamond and function specifications

These consequences use actual Spec.sat, Lifetime.Invariant.ofSpecs and actual
run witnesses. They change no rule, Fml.inTarget, SolKey map or search budget.
They do not supply runtime/deployment/callback or loop correspondence.
-/
namespace Solidity.Roadmap.V16

/-- A typed box supplies its postcondition at an actual successful run.
Unlike the existing empty-context bridge this admits arbitrary dependent
input/output contexts. -/
theorem spec_box_post {C : Contract} {Γ Δ : Ctx} {σ : State C Γ}
    {P : Prog C Γ Δ} {φ : Spec C Δ} {o : Out C σ.H Δ}
    (box : Spec.sat σ (.box P φ)) (run : P.run σ = .ok o) : Spec.sat o.st φ := by
  simp only [Spec.sat, run] at box
  exact box

/-- A diamond is a success witness only after excluding the EXISTING
exhaustion alternative. This does not redefine the approved diamond reading. -/
theorem spec_diamond_success {C : Contract} {Γ Δ : Ctx} {σ : State C Γ}
    {P : Prog C Γ Δ} {φ : Spec C Δ}
    (diamond : Spec.sat σ (.diamond P φ)) (notExhausted : P.run σ ≠ .error .exhausted) :
    ∃ o : Out C σ.H Δ, P.run σ = .ok o ∧ Spec.sat o.st φ := by
  cases hr : P.run σ with
  | ok o => exact ⟨o, rfl, by simpa only [Spec.sat, hr] using diamond⟩
  | error e =>
    have he : e = .exhausted := by simpa only [Spec.sat, hr] using diamond
    subst e
    exact False.elim (notExhausted hr)

/-- A concrete diamond witness gives an actual admitted commit, keeping
fresh entry/payment and nonpayability checks explicit. -/
theorem diamond_commit {C : Contract} {D A : Type} {M : Lifetime.System C D A}
    {s : Lifetime.World C} {a : A} {tx : TTx} {σ : State C []} {φ : Spec C []}
    (accepted : s.accepts tx) (allowed : M.allowCall s a tx)
    (payable : (!M.payable a && tx.msgValue.1 != 0) = false)
    (entered : s.enter tx = .ok σ)
    (diamond : Spec.sat σ (.diamond (M.call a) φ))
    (notExhausted : (M.call a).run σ ≠ .error .exhausted) :
    ∃ o : Out C σ.H [], Lifetime.Step M s (.call a tx) (Lifetime.World.ofState o.st) ∧
      Spec.sat o.st φ := by
  obtain ⟨o, run, post⟩ := spec_diamond_success diamond notExhausted
  refine ⟨o, .commit accepted allowed ?_, post⟩
  simp only [Lifetime.System.run, payable, Bool.false_eq_true, if_false,
    entered, bind, Except.bind, run, pure, Except.pure]

/-- Function boxes establish the SOURCE invariant using the published rule;
NEW backward reachable-state induction then transports it to every target
reachable state. Deployment, entry/payment/time, interface coverage, backward
steps and predicate reflection remain visible premises, not discharged work. -/
theorem specification_invariant_transport
    {C₁ C₂ : Contract} {D₁ D₂ A₁ A₂ : Type}
    {M₁ : Lifetime.System C₁ D₁ A₁} {M₂ : Lifetime.System C₂ D₂ A₂}
    (P : Lifetime.World C₁ → Prop) (Q : Lifetime.World C₂ → Prop)
    (deploy : ∀ d tx σ, M₁.allowDeploy d tx →
      C₁.deployT (M₁.deploy d) tx = .ok σ → P (Lifetime.World.ofState σ))
    (pre post : A₁ → Spec C₁ [])
    (proved : ∀ a, Spec.Valid (.imp (pre a) (.box (M₁.call a) (post a))))
    (entry : ∀ s a tx σ, s.accepts tx → M₁.allowCall s a tx → P s →
      s.enter tx = .ok σ → Spec.sat σ (pre a))
    (reflectPost : ∀ a σ, Spec.sat σ (post a) → P (Lifetime.World.ofState σ))
    (time : ∀ s t, s.timestamp.1 ≤ t.1 → P s → P (s.atTime t))
    (R : Lifetime.World C₁ → Lifetime.World C₂ → Prop)
    (event : Lifetime.Event A₂ → Lifetime.Event A₁)
    (initial : ∀ t, M₂.Init t → ∃ s, M₁.Init s ∧ R s t)
    (step : ∀ {s t u a}, R s t → Lifetime.Step M₂ t a u →
      ∃ v, Lifetime.Step M₁ s (event a) v ∧ R v u)
    (reflect : ∀ s t, R s t → P s → Q t) : Lifetime.AG M₂ Q :=
  reachable_invariant R event initial step P Q
    (Lifetime.Invariant.ofSpecs deploy pre post proved entry reflectPost time) reflect
end Solidity.Roadmap.V16
