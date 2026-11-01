import Solidity.Calculus.DecisionNumericTraversal

/-! # The real program normalizer on numeric logical source bodies
A proof-local view of the actual private StateT computation permits a separate
shared-node/depth invariant without changing producer source or its budgets.
-/
namespace Solidity.Decide

private def actualNormalization {C : Contract} :
    Nat → {Γ : Ctx} → (φ : Fml C Γ) → StateT Nat Option (DeclarationReduction φ) := by
  refine (let N : Nat → {Γ : Ctx} → (φ : Fml C Γ) →
      StateT Nat Option (DeclarationReduction φ) := ?actual
    ?body)
  case body =>
    have capture : ∀ (fuel : Nat) {Γ : Ctx} (φ : Fml C Γ),
        ProgramNormalization.ofFormula? fuel φ = (N fuel φ).run' fuel := by
      intro fuel Γ φ
      unfold ProgramNormalization.ofFormula?
      change (N fuel φ).run' fuel = (N fuel φ).run' fuel
      rfl
    exact N

private theorem actual_truth {C : Contract} {Γ : Ctx} (fuel budget : Nat) :
    actualNormalization (fuel + 1) (.tt : Fml C Γ) (budget + 1) =
      some (DeclarationReduction.keep .tt, budget) := by rfl

private theorem actual_eq {C : Contract} {Γ : Ctx} {p : PrimTy}
    (fuel budget : Nat) (a b : Tm C Γ (.val p)) :
    actualNormalization (fuel + 1) (.eq a b) (budget + 1) =
      some (DeclarationReduction.keep (.eq a b), budget) := by rfl

private theorem actual_not {C : Contract} {Γ : Ctx} (fuel budget : Nat) (φ : Fml C Γ) :
    actualNormalization (fuel + 1) (.not φ) (budget + 1) =
      (actualNormalization fuel φ budget).map
        (fun (d, rest) => (DeclarationReduction.not d, rest)) := by
  change (actualNormalization fuel φ budget).bind
    (fun (d, rest) => some (DeclarationReduction.not d, rest)) = _
  cases actualNormalization fuel φ budget <;> rfl

private theorem actual_and {C : Contract} {Γ : Ctx} (fuel budget : Nat) (φ ψ : Fml C Γ) :
    actualNormalization (fuel + 1) (.and φ ψ) (budget + 1) =
      (actualNormalization fuel φ budget).bind (fun (d, rest) =>
        (actualNormalization fuel ψ rest).map
          (fun (e, last) => (DeclarationReduction.and d e, last))) := by
  change (actualNormalization fuel φ budget).bind (fun (d, rest) =>
    (actualNormalization fuel ψ rest).bind
      (fun (e, last) => some (DeclarationReduction.and d e, last))) = _
  cases hd : actualNormalization fuel φ budget with
  | none => rfl
  | some pair =>
    rcases pair with ⟨d, rest⟩
    change (actualNormalization fuel ψ rest).bind
      (fun (e, last) => some (DeclarationReduction.and d e, last)) =
      (actualNormalization fuel ψ rest).map
        (fun (e, last) => (DeclarationReduction.and d e, last))
    cases actualNormalization fuel ψ rest <;> rfl

private theorem actual_imp {C : Contract} {Γ : Ctx} (fuel budget : Nat) (φ ψ : Fml C Γ) :
    actualNormalization (fuel + 1) (.imp φ ψ) (budget + 1) =
      (actualNormalization fuel φ budget).bind (fun (d, rest) =>
        (actualNormalization fuel ψ rest).map
          (fun (e, last) => (DeclarationReduction.imp d e, last))) := by
  change (actualNormalization fuel φ budget).bind (fun (d, rest) =>
    (actualNormalization fuel ψ rest).bind
      (fun (e, last) => some (DeclarationReduction.imp d e, last))) = _
  cases hd : actualNormalization fuel φ budget with
  | none => rfl
  | some pair =>
    rcases pair with ⟨d, rest⟩
    change (actualNormalization fuel ψ rest).bind
      (fun (e, last) => some (DeclarationReduction.imp d e, last)) =
      (actualNormalization fuel ψ rest).map
        (fun (e, last) => (DeclarationReduction.imp d e, last))
    cases actualNormalization fuel ψ rest <;> rfl

private theorem actual_all {C : Contract} {Γ : Ctx} (fuel budget : Nat)
    (name : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) :
    actualNormalization (fuel + 1) (.all name p φ) (budget + 1) =
      (actualNormalization fuel φ budget).map
        (fun (d, rest) => (DeclarationReduction.all name p d, rest)) := by
  change (actualNormalization fuel φ budget).bind
    (fun (d, rest) => some (DeclarationReduction.all name p d, rest)) = _
  cases actualNormalization fuel φ budget <;> rfl

private theorem smart_and_shape {C : Contract} {Γ : Ctx} {φ ψ : Fml C Γ}
    (hφ : φ.QFUIntLinear) (hψ : ψ.QFUIntLinear) :
    (DeclarationReduction.andFormula φ ψ).QFUIntLinear := by
  unfold DeclarationReduction.andFormula
  split
  · exact hψ
  · exact hφ
  · exact .and hφ hψ

private theorem smart_imp_shape {C : Contract} {Γ : Ctx} {φ ψ : Fml C Γ}
    (hφ : φ.QFUIntLinear) (hψ : ψ.QFUIntLinear) :
    (DeclarationReduction.impFormula φ ψ).QFUIntLinear := by
  unfold DeclarationReduction.impFormula
  split
  · exact hψ
  · exact .imp hφ hψ

private theorem smart_and_weight {C : Contract} {Γ : Ctx} (φ ψ : Fml C Γ) :
    (DeclarationReduction.andFormula φ ψ).uintQFWeight ≤
      φ.uintQFWeight + ψ.uintQFWeight + 1 := by
  unfold DeclarationReduction.andFormula
  split
  · change ψ.uintQFWeight ≤ 1 + ψ.uintQFWeight + 1
    omega
  · change φ.uintQFWeight ≤ φ.uintQFWeight + 1 + 1
    omega
  · exact Nat.le_refl _

private theorem smart_imp_weight {C : Contract} {Γ : Ctx} (φ ψ : Fml C Γ) :
    (DeclarationReduction.impFormula φ ψ).uintQFWeight ≤
      φ.uintQFWeight + ψ.uintQFWeight + 1 := by
  unfold DeclarationReduction.impFormula
  split
  · change ψ.uintQFWeight ≤ 1 + ψ.uintQFWeight + 1
    omega
  · exact Nat.le_refl _

/-- Both resources are explicit: the second branch receives the first branch's
actual remaining state. The weight bounds consumption rather than changing it. -/
private theorem qfUIntLinear_normalizer_state {C : Contract} (fuel budget : Nat)
    {Γ : Ctx} {φ : Fml C Γ} (h : φ.QFUIntLinear)
    (hf : φ.uintQFWeight ≤ fuel) (hb : φ.uintQFWeight ≤ budget) :
    ∃ (d : DeclarationReduction φ) (rest : Nat),
      actualNormalization fuel φ budget = some (d, rest) ∧
      d.formula.QFUIntLinear ∧ d.formula.uintQFWeight ≤ φ.uintQFWeight ∧
      budget ≤ rest + φ.uintQFWeight := by
  induction fuel generalizing Γ φ budget with
  | zero => exact False.elim (Nat.not_lt_of_ge hf (qfUIntLinear_weight_positive h))
  | succ fuel ih =>
    cases budget with
    | zero => exact False.elim (Nat.not_lt_of_ge hb (qfUIntLinear_weight_positive h))
    | succ budget =>
      cases h with
      | tt =>
        refine ⟨DeclarationReduction.keep .tt, budget, actual_truth fuel budget, .tt, Nat.le_refl _, ?_⟩
        exact Nat.le_refl (budget + 1)
      | @eq a b ha hb' =>
        refine ⟨DeclarationReduction.keep (.eq a b), budget, actual_eq fuel budget a b, .eq ha hb', Nat.le_refl _, ?_⟩
        change budget + 1 ≤ budget + (7 * (a.size + b.size) + 13)
        omega
      | @not φ hφ =>
        have hfφ : φ.uintQFWeight ≤ fuel := by
          change φ.uintQFWeight + 1 ≤ fuel + 1 at hf
          omega
        have hbφ : φ.uintQFWeight ≤ budget := by
          change φ.uintQFWeight + 1 ≤ budget + 1 at hb
          omega
        obtain ⟨d, rest, hd, hgrammar, hweight, hconsume⟩ := ih budget hφ hfφ hbφ
        refine ⟨DeclarationReduction.not d, rest, ?_, .not hgrammar, ?_, ?_⟩
        · rw [actual_not, hd]
          rfl
        · change d.formula.uintQFWeight + 1 ≤ φ.uintQFWeight + 1
          omega
        · change budget + 1 ≤ rest + (φ.uintQFWeight + 1)
          omega
      | @and φ ψ hφ hψ =>
        have hfφ : φ.uintQFWeight ≤ fuel := by
          change φ.uintQFWeight + ψ.uintQFWeight + 1 ≤ fuel + 1 at hf
          omega
        have hfψ : ψ.uintQFWeight ≤ fuel := by
          change φ.uintQFWeight + ψ.uintQFWeight + 1 ≤ fuel + 1 at hf
          omega
        have hbφ : φ.uintQFWeight ≤ budget := by
          change φ.uintQFWeight + ψ.uintQFWeight + 1 ≤ budget + 1 at hb
          omega
        obtain ⟨d, middle, hd, hgrammar, hweight, hconsume⟩ := ih budget hφ hfφ hbφ
        have hbψ : ψ.uintQFWeight ≤ middle := by
          change φ.uintQFWeight + ψ.uintQFWeight + 1 ≤ budget + 1 at hb
          omega
        obtain ⟨e, rest, he, egrammar, eweight, econsume⟩ := ih middle hψ hfψ hbψ
        refine ⟨DeclarationReduction.and d e, rest, ?_, smart_and_shape hgrammar egrammar, ?_, ?_⟩
        · rw [actual_and, hd]
          change (actualNormalization fuel ψ middle).map _ = _
          rw [he]
          rfl
        · have hs : (DeclarationReduction.and d e).formula.uintQFWeight ≤
              d.formula.uintQFWeight + e.formula.uintQFWeight + 1 :=
            smart_and_weight d.formula e.formula
          change (DeclarationReduction.and d e).formula.uintQFWeight ≤
            φ.uintQFWeight + ψ.uintQFWeight + 1
          omega
        · change budget + 1 ≤ rest + (φ.uintQFWeight + ψ.uintQFWeight + 1)
          omega
      | @imp φ ψ hφ hψ =>
        have hfφ : φ.uintQFWeight ≤ fuel := by
          change φ.uintQFWeight + ψ.uintQFWeight + 1 ≤ fuel + 1 at hf
          omega
        have hfψ : ψ.uintQFWeight ≤ fuel := by
          change φ.uintQFWeight + ψ.uintQFWeight + 1 ≤ fuel + 1 at hf
          omega
        have hbφ : φ.uintQFWeight ≤ budget := by
          change φ.uintQFWeight + ψ.uintQFWeight + 1 ≤ budget + 1 at hb
          omega
        obtain ⟨d, middle, hd, hgrammar, hweight, hconsume⟩ := ih budget hφ hfφ hbφ
        have hbψ : ψ.uintQFWeight ≤ middle := by
          change φ.uintQFWeight + ψ.uintQFWeight + 1 ≤ budget + 1 at hb
          omega
        obtain ⟨e, rest, he, egrammar, eweight, econsume⟩ := ih middle hψ hfψ hbψ
        refine ⟨DeclarationReduction.imp d e, rest, ?_, smart_imp_shape hgrammar egrammar, ?_, ?_⟩
        · rw [actual_imp, hd]
          change (actualNormalization fuel ψ middle).map _ = _
          rw [he]
          rfl
        · have hs : (DeclarationReduction.imp d e).formula.uintQFWeight ≤
              d.formula.uintQFWeight + e.formula.uintQFWeight + 1 :=
            smart_imp_weight d.formula e.formula
          change (DeclarationReduction.imp d e).formula.uintQFWeight ≤
            φ.uintQFWeight + ψ.uintQFWeight + 1
          omega
        · change budget + 1 ≤ rest + (φ.uintQFWeight + ψ.uintQFWeight + 1)
          omega

/-- The public computation returns an actual equivalent certificate on the
whole logical numeric grammar. Smart truth reductions may change its syntax. -/
theorem qfUIntLinear_normalization {C : Contract} {Γ : Ctx} (budget : Nat)
    {φ : Fml C Γ} (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ budget) :
    ∃ d : DeclarationReduction φ, ProgramNormalization.ofFormula? budget φ = some d ∧
      d.formula.QFUIntLinear ∧ d.formula.uintQFWeight ≤ φ.uintQFWeight := by
  obtain ⟨d, rest, hd, hg, hs, hc⟩ := qfUIntLinear_normalizer_state budget budget h hw hw
  refine ⟨d, ?_, hg, hs⟩
  change (actualNormalization budget φ budget).map Prod.fst = some d
  rw [hd]
  rfl

/-- The existing positive binder consumes one of the unchanged2048 nodes.
No normalization identity, validity oracle or producer premise is required. -/
theorem qfUIntPrefix_normalization {C : Contract} (name : Var)
    {φ : Fml C [.val .uint]} (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 511) :
    ∃ χ : Fml C [.val .uint],
      (ProgramNormalization.ofFormula? 2048 (.all name .uint φ)).map (·.formula) =
        some (.all name .uint χ) ∧ χ.QFUIntLinear ∧ χ.uintQFWeight ≤ φ.uintQFWeight := by
  obtain ⟨d, rest, hd, hg, hs, hc⟩ :=
    qfUIntLinear_normalizer_state 2047 2047 h (by omega) (by omega)
  refine ⟨d.formula, ?_, hg, hs⟩
  change ((actualNormalization 2048 (.all name .uint φ) 2048).map Prod.fst).map (·.formula) = _
  rw [actual_all 2047 2047 name .uint φ, hd]
  rfl

/-- Compose through the actual normalized source, which can differ syntactically
from its input. This is an equation about the real existing pipeline. -/
theorem leafOf_of_normalized_to {C : Contract} (φ χ : Fml C []) (ψ : LFml C)
    (hn : (ProgramNormalization.ofFormula? 2048 φ).map (·.formula) = some χ)
    (hs : (sourceReduction? χ).map (·.leaf) = some ψ) :
    leafOf? φ = some ψ.elim.condSimp.prenex := by
  cases he : ProgramNormalization.ofFormula? 2048 φ with
  | none => rw [he] at hn; cases hn
  | some d =>
    rw [he] at hn
    have hf : d.formula = χ := Option.some.inj hn
    have ht : (sourceReduction? χ).map (fun r => r.leaf.elim.condSimp.prenex) =
        some ψ.elim.condSimp.prenex := by
      have hm : ((sourceReduction? χ).map (·.leaf)).map
          (fun l : LFml C => l.elim.condSimp.prenex) = some ψ.elim.condSimp.prenex :=
        congrArg (Option.map (fun l : LFml C => l.elim.condSimp.prenex)) hs
      simpa only [Option.map_map, Option.map_some] using hm
    simp only [leafOf?, he, Option.bind_eq_bind, Option.pure_def, Option.bind_some]
    simp only [Option.map_eq_bind, Function.comp_def] at ht
    exact hf.symm ▸ ht

/-- Source syntax and its derived weight now reach the actual covered leaf.
The earlier conditional supplied-leaf interface remains available unchanged. -/
theorem qfUIntPrefix_logic_Covered {C : Contract} (name : Var)
    {φ : Fml C [.val .uint]} (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 511) :
    (Fml.all name .uint φ).Covered = true := by
  obtain ⟨χ, hn, hg, hs⟩ := qfUIntPrefix_normalization name h hw
  have hc : χ.uintQFWeight ≤ 511 := Nat.le_trans hs hw
  obtain ⟨ψ, hr, hψ, hp, hb⟩ := qfUIntPrefix_source_coverageFacts name hg hc
  have hl : leafOf? (.all name .uint φ) =
      some (LFml.all 0 .uint ψ).elim.condSimp.prenex :=
    leafOf_of_normalized_to (.all name .uint φ) (.all name .uint χ) (.all 0 .uint ψ) hn hr
  have hl' : leafOf? (.all name .uint φ) = some (.all 0 .uint ψ) := by
    simpa only [LFml.elim, LFml.condSimp, LFml.prenex, hp] using hl
  exact qfUIntLogic_Covered_of_leaf hψ hb hl'

/-- The supported class is admitted under every frozen waiver choice and
covered without hashes; no reverse inclusion is asserted. -/
theorem qfUIntPrefix_logic_boundary {C : Contract} (name : Var) (w : Waivers)
    {φ : Fml C [.val .uint]} (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 511) :
    (Fml.all name .uint φ).inTarget w = true ∧
      (Fml.all name .uint φ).Covered = true ∧ (Fml.all name .uint φ).hasHash = false :=
  ⟨qfUIntPrefix_inTarget name h w, qfUIntPrefix_logic_Covered name h hw,
    qfUIntPrefix_hashFree name h⟩

theorem qfUIntPrefix_logic_answered {C : Contract} (name : Var)
    {φ : Fml C [.val .uint]} (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 511) :
    decideGoal (.all name .uint φ) ≠ .unknown :=
  decideGoal_complete (qfUIntPrefix_logic_Covered name h hw) (qfUIntPrefix_hashFree name h)

/-- The actual answer carries the unchanged hash-premised semantic certificate. -/
theorem qfUIntPrefix_logic_certified {C : Contract} (name : Var)
    {φ : Fml C [.val .uint]} (h : φ.QFUIntLinear) (hw : φ.uintQFWeight ≤ 511) :
    (decideGoal (.all name .uint φ) = .proved ∧ Fml.ValidH (.all name .uint φ)) ∨
      ∃ σ : State C [], decideGoal (.all name .uint φ) = .refuted σ ∧
        ¬ Fml.holdsH σ (.all name .uint φ) := by
  have hd : decideGoal (.all name .uint φ) ≠ .unknown := qfUIntPrefix_logic_answered name h hw
  cases he : decideGoal (.all name .uint φ) with
  | proved => exact Or.inl ⟨rfl, decideGoal_sound he⟩
  | refuted σ => exact Or.inr ⟨σ, rfl, decideGoal_refutes he⟩
  | unknown => exact False.elim (hd he)

end Solidity.Decide
