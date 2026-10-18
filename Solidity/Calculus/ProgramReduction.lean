import Solidity.Calculus.ExactRun
import Solidity.Calculus.SoundLoops
import Solidity.Calculus.DeclarationReduction
import Solidity.Calculus.ParameterReduction

/-!
# Exact normalization of supported source programs

The normalizer uses the existing pointwise formula-equivalence certificate.
Each supported statement becomes the update certified against its actual
typed run. Both directions are retained before arithmetic compilation, so
a false leaf refers to the original program's starting state.
-/

namespace Solidity.Decide

variable {C : Contract}

namespace ProgramNormalization

theorem afterT_congr_iff {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (σ : State C Γ)
    (P Q : State C Δ → Prop) (h : ∀ τ, P τ ↔ Q τ) : U.afterT m σ P ↔ U.afterT m σ Q := by
  exact ⟨fun hp => Upd.afterT_imp hp (fun τ hτ => (h τ).1 hτ),
    fun hq => Upd.afterT_imp hq (fun τ hτ => (h τ).2 hτ)⟩

def update {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) {φ : Fml C Δ}
    (r : DeclarationReduction φ) : DeclarationReduction (.upd m U φ) :=
  ⟨.upd m U r.formula, fun σ => afterT_congr_iff m U σ _ _ r.correct⟩

def empty {Γ : Ctx} (m : Modality) (φ : Fml C Γ) :
    DeclarationReduction (.modal m (.nil : Prog C Γ Γ) .nil φ) :=
  ⟨φ, fun _ => ⟨fun h => ⟨h, nofun⟩, And.left⟩⟩

def statement {Γ Δ Γ₁ Γ₀ : Ctx} (m : Modality) {s : Stmt C Γ Δ} (r : ExactStatement s)
    (ω : Prog C Δ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    DeclarationReduction (.modal m (.cons s ω) κ φ) :=
  ⟨.upd m r.update (.modal m ω κ φ), fun σ => r.equivalent σ m ω κ φ⟩

def sequence {Γ Δ Γ₀ : Ctx} (m : Modality) (ω : Prog C Γ Δ) (κ : Frames C Δ Γ₀) (φ : Fml C Γ₀) :
    DeclarationReduction (.modal m (.nil : Prog C Γ Γ) (.seq ω κ) φ) :=
  ⟨.modal m ω κ φ, fun σ => by
    change m.afterRunTR _ (Prog.runFrames σ ω κ) ↔ m.afterRunTR _ (Prog.runFrames σ .nil (.seq ω κ))
    rw [Prog.runFrames_seq]⟩

def pop {Γ Δ Γ₀ : Ctx} (m : Modality) (b : BlockKind) (h : Ext Γ Δ)
    (κ : Frames C Γ Γ₀) (φ : Fml C Γ₀) :
    DeclarationReduction (.modal m (.nil : Prog C Δ Δ) (.pop b h κ) φ) :=
  ⟨.upd m (Upd.nil.pop h) (.modal m .nil κ φ), fun σ =>
    (Upd.afterT_lands_iff (Upd.lands_pop_nil h σ) m _).trans Iff.rfl⟩

def drop {Γ Δ Γ₀ : Ctx} (m : Modality) (h : Thin Γ Δ) (κ : Frames C Γ Γ₀) (φ : Fml C Γ₀) :
    DeclarationReduction (.modal m (.nil : Prog C Δ Δ) (.drop h κ) φ) :=
  ⟨.upd m (Upd.nil.drop h) (.modal m .nil κ φ), fun σ =>
    (Upd.afterT_lands_iff (Upd.lands_drop_nil h σ) m _).trans Iff.rfl⟩

def block {Γ Δ Γ₁ Γ₀ : Ctx} (m : Modality) (body : Prog C Γ Δ) (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    DeclarationReduction (.modal m (.cons (.block body) ω) κ φ) :=
  ⟨.modal m body (.pop .block body.ext (.seq ω κ)) φ, by
    intro σ
    simp only [holds_modal_iff, runSt_cons_frames, Stmt.runSt_block, runSt_block_frames]⟩

def unfold {Γ Δ Γ' Γ₁ Γ₀ : Ctx} (m : Modality) (s : Stmt C Γ Γ')
    (P : Prog C Γ Δ) (h : Ext Γ' Δ)
    (exactRun : ∀ σ, (Prog.runSt σ P).map (State.drop h) = Stmt.runSt σ s)
    (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    DeclarationReduction (.modal m (.cons s ω) κ φ) :=
  ⟨.modal m P (.pop .block h (.seq ω κ)) φ, by
    intro σ
    rw [holds_modal_iff, holds_modal_iff, runSt_cons_frames, ← exactRun σ]
    cases Prog.runSt σ P <;> simp only [Except.bind, Except.map, Frames.runSt_pop, Frames.runSt_seq]⟩

def inline {Γ Δ Γ' Γ₁ Γ₀ : Ctx} (m : Modality) (s : Stmt C Γ Γ')
    (P : Prog C Γ Δ) (h : Thin Γ' Δ)
    (exactRun : ∀ σ, (Prog.runSt σ P).map (State.thin h) = Stmt.runSt σ s)
    (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    DeclarationReduction (.modal m (.cons s ω) κ φ) :=
  ⟨.modal m P (.drop h (.seq ω κ)) φ, by
    intro σ
    rw [holds_modal_iff, holds_modal_iff, runSt_cons_frames, ← exactRun σ]
    cases Prog.runSt σ P <;> simp only [Except.bind, Except.map, Frames.runSt_drop, Frames.runSt_seq]⟩

def callNone {Γ ps Γf Γ₁ Γ₀ : Ctx} (m : Modality) (f : Name) (args : Args C Γ ps)
    (body : Prog C ([] ++ ps) Γf) (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    DeclarationReduction (.modal m (.cons (.call f args .none body) ω) κ φ) :=
  unfold m (.call f args .none body)
    (args.declsThen (.cons (.block (body.wk (Thin.atop ps Γ)).2.2) .nil))
    (Ext.append Γ ps) (Stmt.runSt_callNone f args body) ω κ φ

def callVal {Γ ps Γf Γ₁ Γ₀ : Ctx} (m : Modality) (f : Name) (args : Args C Γ ps)
    (p : PrimTy) (r : Var) (res : Option (Idx Γ (.val p))) (body : Prog C ([.val p] ++ ps) Γf)
    (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    DeclarationReduction (.modal m (.cons (.call f args (.val p r res) body) ω) κ φ) :=
  unfold m (.call f args (.val p r res) body)
    (args.declsThen (.cons (.declLocal p r none)
      (.cons (.block (body.wk (Thin.atop (.val p :: ps) Γ)).2.2) (match res with
        | none => .nil
        | some j => .cons (.assignLocal (j.under ps).there (.simple (.local .here))) .nil))))
    (.push (Ext.append Γ ps)) (Stmt.runSt_callVal f args p r res body) ω κ φ

def callRets {Γ ps rs Γf Γ₁ Γ₀ : Ctx} (m : Modality) (f : Name) (args : Args C Γ ps)
    (bs : Binders rs) (body : Prog C (rs ++ ps) Γf)
    (ω : Prog C (rs ++ Γ) Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    DeclarationReduction (.modal m (.cons (.call f args (.rets bs) body) ω) κ φ) :=
  inline m (.call f args (.rets bs) body)
    (args.declsThen (bs.declsThen
      (.cons (.block (body.wk (Thin.keepAll rs (Thin.atop ps Γ))).2.2) .nil)))
    (Thin.keepAll rs (Thin.ofExt (Ext.append Γ ps))) (Stmt.runSt_callRets f args bs body) ω κ φ

def compose {Γ : Ctx} {φ : Fml C Γ} (a : DeclarationReduction φ)
    (b : DeclarationReduction a.formula) : DeclarationReduction φ :=
  ⟨b.formula, fun σ => (b.correct σ).trans (a.correct σ)⟩

def bindValue {Γ : Ctx} (m : Modality) (x : Var) (p : PrimTy) {φ : Fml C (.val p :: Γ)}
    (r : DeclarationReduction φ) : DeclarationReduction (.bind m x (.val p) φ) :=
  ⟨.all x p r.formula, fun σ => forall_congr' fun v => r.correct (σ.push v)⟩

def requireFormula {Γ : Ctx} (m : Modality) (c : Val C Γ .bool) (φ : Fml C Γ) : Fml C Γ :=
  match m with
  | .box => .imp (.isBoolD c.lower true) φ
  | .diamond => .and (.isBoolD c.lower true) φ

theorem requireFormula_holds {Γ : Ctx} (m : Modality) (c : Val C Γ .bool)
    (φ : Fml C Γ) (σ : State C Γ) :
    holds σ (requireFormula m c φ) ↔
      match m with
      | .box => c.evalT σ = .ok true → holds σ φ
      | .diamond => c.evalT σ = .ok true ∧ holds σ φ :=
  match m with
  | .box => imp_congr (holds_isBoolD_lower c σ true) Iff.rfl
  | .diamond => and_congr (holds_isBoolD_lower c σ true) Iff.rfl

def require {Γ Γ₁ Γ₀ : Ctx} (m : Modality) (c : Val C Γ .bool)
    (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    DeclarationReduction (.modal m (.cons (.require c) ω) κ φ) :=
  ⟨requireFormula m c (.modal m ω κ φ), by
    intro σ
    rw [holds_modal_cons_iff]
    cases hc : c.evalT σ with
    | ok b =>
      cases b <;> cases m <;>
        simp only [requireFormula_holds, hc, Stmt.runSt, Stmt.run, Stmt.runR, TRun.require,
          boolT, ok_bind, pure, Except.pure, Except.map, Modality.afterRunTR, Modality.onTHalt,
          reduceCtorEq, Except.ok.injEq, Bool.false_eq_true, if_false, if_true, false_and,
          true_and, false_implies, true_implies]
      all_goals first | exact ⟨fun _ => nofun, fun _ => trivial⟩
                      | exact ⟨fun h => ⟨h, nofun⟩, And.left⟩
    | error e =>
      have he : e = .revert := (Val.evalT_revertOnly σ c).error hc
      subst e
      cases m <;>
        simp only [requireFormula_holds, hc, Stmt.runSt, Stmt.run, Stmt.runR, TRun.require,
          error_bind, Except.map, Modality.afterRunTR, Modality.onTHalt,
          reduceCtorEq, false_and, true_and, false_implies]
      exact ⟨fun _ => nofun, fun _ => trivial⟩⟩

def assertFormula {Γ : Ctx} (m : Modality) (c : Val C Γ .bool) (φ : Fml C Γ) : Fml C Γ :=
  .and (.not (.isBoolD c.lower false)) (requireFormula m c φ)

theorem assertFormula_holds {Γ : Ctx} (m : Modality) (c : Val C Γ .bool)
    (φ : Fml C Γ) (σ : State C Γ) :
    holds σ (assertFormula m c φ) ↔ c.evalT σ ≠ .ok false ∧
      (match m with
      | .box => c.evalT σ = .ok true → holds σ φ
      | .diamond => c.evalT σ = .ok true ∧ holds σ φ) :=
  and_congr (not_congr (holds_isBoolD_lower c σ false)) (requireFormula_holds m c φ σ)

def assert {Γ Γ₁ Γ₀ : Ctx} (m : Modality) (c : Val C Γ .bool)
    (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    DeclarationReduction (.modal m (.cons (.assert c) ω) κ φ) :=
  ⟨assertFormula m c (.modal m ω κ φ), by
    intro σ
    rw [holds_modal_cons_iff, assertFormula_holds]
    cases hc : c.evalT σ with
    | ok b =>
      cases b <;> cases m <;>
        simp only [hc, Stmt.runSt, Stmt.run, Stmt.runR, TRun.assert,
          boolT, ok_bind, pure, Except.pure, Except.map, Modality.afterRunTR,
          Modality.onTHalt, Except.ok.injEq, reduceCtorEq,
          Bool.false_eq_true, if_false, if_true, false_and, true_and, true_implies]
      all_goals grind
    | error e =>
      have he : e = .revert := (Val.evalT_revertOnly σ c).error hc
      subst e
      cases m <;>
        simp only [hc, Stmt.runSt, Stmt.run, Stmt.runR, TRun.assert,
          error_bind, Except.map, Modality.afterRunTR, Modality.onTHalt,
          reduceCtorEq, false_and, true_and, false_implies]
      all_goals grind⟩

def revert {Γ Γ₁ Γ₀ : Ctx} (m : Modality)
    (ω : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    DeclarationReduction (.modal m (.cons .revert ω) κ φ) :=
  ⟨match m with | .box => .tt | .diamond => .ff, by
    intro σ
    rw [holds_modal_cons_iff]
    cases m with
    | box => exact ⟨fun _ => ⟨trivial, nofun⟩, fun _ => trivial⟩
    | diamond => exact ⟨fun h => (h trivial).elim, fun h => THalt.noConfusion h.1⟩⟩

def branchFormula {Γ : Ctx} (m : Modality) (c : Val C Γ .bool) (P Q : Fml C Γ) : Fml C Γ :=
  match m with
  | .box => .and (.imp (.isBoolD c.lower true) P) (.imp (.isBoolD c.lower false) Q)
  | .diamond => .not (.and (.not (.and (.isBoolD c.lower true) P))
      (.not (.and (.isBoolD c.lower false) Q)))

theorem branchFormula_holds {Γ : Ctx} (m : Modality) (c : Val C Γ .bool)
    (P Q : Fml C Γ) (σ : State C Γ) :
    holds σ (branchFormula m c P Q) ↔
      match m with
      | .box => (c.evalT σ = .ok true → holds σ P) ∧ (c.evalT σ = .ok false → holds σ Q)
      | .diamond => ¬ (¬ (c.evalT σ = .ok true ∧ holds σ P) ∧
          ¬ (c.evalT σ = .ok false ∧ holds σ Q)) :=
  match m with
  | .box => and_congr (imp_congr (holds_isBoolD_lower c σ true) Iff.rfl)
      (imp_congr (holds_isBoolD_lower c σ false) Iff.rfl)
  | .diamond => not_congr (and_congr
      (not_congr (and_congr (holds_isBoolD_lower c σ true) Iff.rfl))
      (not_congr (and_congr (holds_isBoolD_lower c σ false) Iff.rfl)))

def branch {Γ Δ₁ Δ₂ Γ₁ Γ₀ : Ctx} (m : Modality) (c : Val C Γ .bool)
    (P : Prog C Γ Δ₁) (Q : Prog C Γ Δ₂) (ω : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (φ : Fml C Γ₀) :
    DeclarationReduction (.modal m (.cons (.ite c P Q) ω) κ φ) :=
  ⟨branchFormula m c (.modal m P (.pop .block P.ext (.seq ω κ)) φ)
      (.modal m Q (.pop .block Q.ext (.seq ω κ)) φ), by
    intro σ
    simp only [branchFormula_holds, holds_modal_iff, runSt_cons_frames,
      Stmt.runSt_ite, runSt_block_frames]
    cases hc : c.evalT σ with
    | ok b =>
      cases b <;> cases m <;>
        simp only [Except.bind, boolT, if_false, if_true, Except.ok.injEq,
          Bool.false_eq_true, reduceCtorEq, true_implies,
          false_implies, true_and, false_and, and_true, not_false_eq_true,
          Classical.not_not]
    | error e =>
      have he : e = .revert := (Val.evalT_revertOnly σ c).error hc
      subst e
      cases m <;>
        simp only [Except.bind, Modality.afterRunTR, Modality.onTHalt,
          reduceCtorEq, false_implies, false_and, true_and, not_false_eq_true,
          not_true_eq_false]
      exact ⟨fun _ => nofun, fun _ => trivial⟩⟩

/-- A structural depth certificate plus shared remaining node budget. Each
rewrite, frame and logical child consumes one node, across both branches. -/
private def normalizeCore : Nat → {Γ : Ctx} → (φ : Fml C Γ) →
    StateT Nat Option (DeclarationReduction φ)
  | 0, _, _ => fun _ => none
  | fuel + 1, _, φ => do
    let remaining ← get
    if remaining == 0 then return ← liftM (none : Option (DeclarationReduction φ))
    set (remaining - 1)
    match φ with
    | .not φ => (normalizeCore fuel φ).map DeclarationReduction.not
    | .and φ ψ => do
      return DeclarationReduction.and (← normalizeCore fuel φ) (← normalizeCore fuel ψ)
    | .imp φ ψ => do
      return DeclarationReduction.imp (← normalizeCore fuel φ) (← normalizeCore fuel ψ)
    | .all x p φ => (normalizeCore fuel φ).map (DeclarationReduction.all x p)
    | .bind m x (.val p) φ => (normalizeCore fuel φ).map (bindValue m x p)
    | .upd m U φ => (normalizeCore fuel φ).map (update m U)
    | .modal m .nil .nil φ =>
      (normalizeCore fuel φ).map (compose (empty m φ))
    | .modal m .nil (.seq ω κ) φ =>
      (normalizeCore fuel (.modal m ω κ φ)).map (compose (sequence m ω κ φ))
    | .modal m .nil (.pop b h κ) φ =>
      (normalizeCore fuel (.upd m (Upd.nil.pop h) (.modal m .nil κ φ))).map
        (compose (pop m b h κ φ))
    | .modal m .nil (.drop h κ) φ =>
      (normalizeCore fuel (.upd m (Upd.nil.drop h) (.modal m .nil κ φ))).map
        (compose (drop m h κ φ))
    | .modal m (.cons (.block body) ω) κ φ =>
      (normalizeCore fuel (.modal m body (.pop .block body.ext (.seq ω κ)) φ)).map
        (compose (block m body ω κ φ))
    | .modal m (.cons (.ite c P Q) ω) κ φ =>
      (normalizeCore fuel (branchFormula m c (.modal m P (.pop .block P.ext (.seq ω κ)) φ)
        (.modal m Q (.pop .block Q.ext (.seq ω κ)) φ))).map (compose (branch m c P Q ω κ φ))
    | .modal m (.cons (.require c) ω) κ φ =>
      (normalizeCore fuel (requireFormula m c (.modal m ω κ φ))).map (compose (require m c ω κ φ))
    | .modal m (.cons (.assert c) ω) κ φ =>
      (normalizeCore fuel (assertFormula m c (.modal m ω κ φ))).map (compose (assert m c ω κ φ))
    | .modal m (.cons .revert ω) κ φ => pure (revert m ω κ φ)
    | .modal m (.cons (.call f args .none body) ω) κ φ =>
      let d := callNone m f args body ω κ φ
      (normalizeCore fuel d.formula).map (compose d)
    | .modal m (.cons (.call f args (.val p r res) body) ω) κ φ =>
      let d := callVal m f args p r res body ω κ φ
      (normalizeCore fuel d.formula).map (compose d)
    | .modal m (.cons (.call f args (.rets bs) body) ω) κ φ =>
      let d := callRets m f args bs body ω κ φ
      (normalizeCore fuel d.formula).map (compose d)
    | .modal m (.cons s ω) κ φ => do
      let r ← liftM (ExactStatement.ofStatement? s)
      let rest ← normalizeCore fuel (.upd m r.update (.modal m ω κ φ))
      return compose (statement m r ω κ φ) rest
    | φ => pure (DeclarationReduction.keep φ)

/-- Total bounded recognition. Exhausting the shared node budget returns
unsupported, including expansion of unreachable branch continuations. -/
def ofFormula? {Γ : Ctx} (budget : Nat) (φ : Fml C Γ) : Option (DeclarationReduction φ) :=
  (normalizeCore budget φ).run' budget

end ProgramNormalization

/-- Compile an original source formula after exact program normalization. -/
def programReduction? (φ : Fml C []) : Option (ParameterReduction φ) := do
  let d ← ProgramNormalization.ofFormula? 2048 φ
  let r ← parameterReduction? d.formula
  return ⟨r.parameters, r.distinctParameters, r.refs, r.distinctRefs, r.arithmetic,
    fun σ => (r.meaning σ).trans (d.correct σ)⟩

end Solidity.Decide
