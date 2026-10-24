import Solidity.Calculus.RewritePast.Scope

/-!
# Rewrites past the program: shadows and merges

A shadowed state write dropped, and two updates merged.

A piece of `Calculus/RewritePast.lean`, whose docstring describes the whole.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)

variable {C : Contract}

/-! ## A shadowed state write dropped -/

section Shadow

variable {Γ : Ctx}

/-- `Tm.spineHas`' compiled twin. -/
def Tm.spineHasM {k : Srt} (S : Tm C Γ k) : {s : Srt} → Tm C Γ s → Bool
  | _, .app1 _ a => a.beqR S || Tm.spineHasM S a
  | _, .app2 _ a _ => a.beqR S || Tm.spineHasM S a
  | _, .app3 _ a _ _ => a.beqR S || Tm.spineHasM S a
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .netOf .. | _, .app0 _ | _, .pvZ _ => false

/-- `S` is read first, strictly inside `T`: the first argument of a symbol of
`T`, or of one below it (every symbol reads its first argument first: where
it halts, the symbol does).  Generic in both sorts, by the recursor. -/
@[implemented_by Tm.spineHasM]
def Tm.spineHas {k : Srt} (S : Tm C Γ k) {s : Srt} (T : Tm C Γ s) : Bool :=
  Tm.rec (motive := fun _ _ => Bool)
    (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ _ _ => false)
    (fun _ => false)
    (fun _ a ih => a.beqR S || ih)
    (fun _ a _ iha _ => a.beqR S || iha)
    (fun _ a _ _ iha _ _ => a.beqR S || iha) (fun _ => false) T

theorem Tm.spineHas_eq_spineHasM {k : Srt} (S : Tm C Γ k) {s : Srt} (T : Tm C Γ s) :
    Tm.spineHas S T = Tm.spineHasM S T := by
  induction T with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ _ | app0 _ | pvZ _ => rfl
  | app1 o a ih => simp only [Tm.spineHasM, ← ih]; rfl
  | app2 o a _ ih _ => simp only [Tm.spineHasM, ← ih]; rfl
  | app3 o a _ _ ih _ _ => simp only [Tm.spineHasM, ← ih]; rfl

/-- `S` is read before anything else of `T`: `T` is `S`, or `S` is on its
spine. -/
def Tm.onSpineS {k : Srt} (T S : Tm C Γ k) : Bool := T.beqR S || Tm.spineHas S T

/-- A term with `S` on its spine halts wherever `S` does. -/
theorem Tm.spineHas_none {k : Srt} {S : Tm C Γ k} {σ : State C Γ} (hS : S.eval σ = none)
    {s : Srt} (T : Tm C Γ s) (h : Tm.spineHasM S T = true) : T.eval σ = none := by
  induction T with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ _ | app0 _ | pvZ _ =>
    exact absurd h Bool.false_ne_true
  | app1 o a iha =>
    simp only [Tm.spineHasM, Bool.or_eq_true] at h
    refine Tm.eval_app1_none o a ?_
    rcases h with h | h
    · cases Tm.sigma_eq_of_beqR h; exact hS
    · exact iha h
  | app2 o a b iha _ =>
    simp only [Tm.spineHasM, Bool.or_eq_true] at h
    refine Tm.eval_app2_none o a b ?_
    rcases h with h | h
    · cases Tm.sigma_eq_of_beqR h; exact hS
    · exact iha h
  | app3 o a b c iha _ _ =>
    simp only [Tm.spineHasM, Bool.or_eq_true] at h
    refine Tm.eval_app3_none o a b c ?_
    rcases h with h | h
    · cases Tm.sigma_eq_of_beqR h; exact hS
    · exact iha h

/-- A term on the spine of `S` halts wherever `S` does. -/
theorem Tm.onSpineS_none {k : Srt} {S : Tm C Γ k} {σ : State C Γ} (hS : S.eval σ = none)
    (T : Tm C Γ k) (h : T.onSpineS S = true) : T.eval σ = none := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rw [Tm.eq_of_beqR h]; exact hS
  · exact Tm.spineHas_none hS T (Tm.spineHas_eq_spineHasM S T ▸ h)

/-- The update with each storage write whose storage a later one reads first
dropped (`P` the storage terms written later), and so each memory write
(`Q`). -/
def Upd.dropSh (P : List (Tm C Γ .st)) (Q : List (Tm C Γ .mem)) :
    {Δ : Ctx} → Upd C Γ Δ → Upd C Γ Δ
  | _, .nil => .nil
  | _, .snoc U e => match e with
    | .storage S =>
      if P.any (·.onSpineS S) then Upd.dropSh P Q U else .snoc (Upd.dropSh (S :: P) Q U) (.storage S)
    | .memory M =>
      if Q.any (·.onSpineS M) then Upd.dropSh P Q U else .snoc (Upd.dropSh P (M :: Q) U) (.memory M)
    | e => .snoc (Upd.dropSh P Q U) e
  | _, .decl U x r => .decl (Upd.dropSh P Q U) x r
  | _, .pop U h => .pop (Upd.dropSh P Q U) h
  | _, .drop U h => .drop (Upd.dropSh P Q U) h

/-- A typed global part's memory, as a heap grown from `H`. -/
def GlobT.memG {H : HTy} (g : GlobT C H) : Grown H (fun _ => Unit) := ⟨g.2, g.1.heap, ()⟩

/-- A typed global part with its storage and memory replaced. -/
def GlobT.withSM {H : HTy} (g : GlobT C H) (st : Storage C) (μ : Grown H (fun _ => Unit)) :
    GlobT C H :=
  ⟨State.mk st μ.H' μ.heap () g.1.net g.1.selfBalance g.1.tx, μ.ext⟩

theorem GlobT.withSM_self {H : HTy} (g : GlobT C H) : g.withSM g.1.storage g.memG = g := rfl

/-- An element that writes neither the storage nor the memory computes alike
from a global part with another storage and memory. -/
theorem UpdElem.globT_withSM {Δ : Ctx} (σ₀ : State C Γ) (st : Storage C)
    (μ : Grown σ₀.H (fun _ => Unit)) (τ : GlobT C σ₀.H) :
    (e : UpdElem C Γ Δ) → (∀ S, e ≠ .storage S) → (∀ M, e ≠ .memory M) →
      e.globT σ₀ (τ.withSM st μ) = (e.globT σ₀ τ).map (·.withSM st μ)
  | .local i r, _, _ => by
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM]
    cases r.eval σ₀ <;> rfl
  | .storage S, h, _ => absurd rfl (h S)
  | .memory M, _, h => absurd rfl (h M)
  | .selfBalance op a, _, _ => by
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM]
    cases a.eval σ₀ with
    | none => rfl
    | some v =>
      simp only [Option.bind_some]
      cases PrimTy.uint.ofInt? (op.apply σ₀.selfBalance.1 v.1) <;> rfl
  | .net r op a, _, _ => by
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM]
    cases r.eval σ₀ <;> cases a.eval σ₀ <;> rfl
  | .pay r a, _, _ => by
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM]
    cases r.eval σ₀ with
    | none => rfl
    | some v =>
      cases a.eval σ₀ with
      | none => rfl
      | some w =>
        simp only [Option.bind_some, Option.map_some]
        rfl
  | .netMt r a, _, _ => by
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM]
    cases r.eval σ₀ <;> cases a.eval σ₀ <;> rfl
  | .setBalance a, _, _ => by
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM]
    cases a.eval σ₀ <;> rfl

theorem UpdElem.globT_storage {Δ : Ctx} (σ₀ : State C Γ) (S : Tm C Γ .st) (τ : GlobT C σ₀.H) :
    (UpdElem.storage S : UpdElem C Γ Δ).globT σ₀ τ = (S.eval σ₀).map τ.withStorage := by
  rw [UpdElem.globT_eq_globTM]
  simp only [UpdElem.globTM]
  cases S.eval σ₀ <;> rfl

theorem UpdElem.globT_memory {Δ : Ctx} (σ₀ : State C Γ) (M : Tm C Γ .mem) (τ : GlobT C σ₀.H) :
    (UpdElem.memory M : UpdElem C Γ Δ).globT σ₀ τ = (M.eval σ₀).map τ.withMem := by
  rw [UpdElem.globT_eq_globTM]
  simp only [UpdElem.globTM]
  cases M.eval σ₀ <;> rfl

/-- How the global part an update computes and the one with the shadowed
writes dropped (`P`, `Q` the writes still to come) relate: one but for the
storage (where a write is to come) and the memory, or the first halted, and
the second too or on a shadowing write that halts. -/
def ShRel (σ₀ : State C Γ) (P : List (Tm C Γ .st)) (Q : List (Tm C Γ .mem))
    (a b : Option (GlobT C σ₀.H)) : Prop :=
  (∃ τ st μ, a = some τ ∧ b = some (τ.withSM st μ) ∧ (P = [] → st = τ.1.storage) ∧
      (Q = [] → μ = τ.memG)) ∨
    (a = none ∧ (b = none ∨ (∃ T ∈ P, T.eval σ₀ = none) ∨ (∃ M ∈ Q, M.eval σ₀ = none)))

theorem ShRel.bind_globT {σ₀ : State C Γ} {P : List (Tm C Γ .st)} {Q : List (Tm C Γ .mem)}
    {Δ : Ctx} {a b : Option (GlobT C σ₀.H)} (h : ShRel σ₀ P Q a b) (e : UpdElem C Γ Δ)
    (hS : ∀ S, e ≠ .storage S) (hM : ∀ M, e ≠ .memory M) :
    ShRel σ₀ P Q (a.bind (e.globT σ₀)) (b.bind (e.globT σ₀)) := by
  rcases h with ⟨τ, st, μ, rfl, rfl, h₁, h₂⟩ | ⟨rfl, h⟩
  · simp only [Option.bind_some]
    rw [UpdElem.globT_withSM σ₀ st μ τ e hS hM]
    cases hw : e.globT σ₀ τ with
    | none => exact .inr ⟨rfl, .inl rfl⟩
    | some ρ =>
      have hρ : ρ.withSM ρ.1.storage ρ.memG = ρ := rfl
      have hτ := UpdElem.globT_withSM σ₀ τ.1.storage τ.memG τ e hS hM
      rw [GlobT.withSM_self, hw] at hτ
      have hτ : ρ = ρ.withSM τ.1.storage τ.memG := Option.some.inj hτ
      refine .inl ⟨ρ, st, μ, rfl, rfl, fun hP => ?_, fun hQ => ?_⟩
      · rw [h₁ hP, hτ]; rfl
      · rw [h₂ hQ, hτ]; rfl
  · refine .inr ⟨rfl, ?_⟩
    rcases h with rfl | h
    · exact .inl rfl
    · exact .inr h

/-- **Dropping the shadowed writes leaves the global part, or a halt a
halt.** -/
theorem Upd.dropSh_rel (σ₀ : State C Γ) : {Δ : Ctx} → (U : Upd C Γ Δ) →
    (P : List (Tm C Γ .st)) → (Q : List (Tm C Γ .mem)) →
      ShRel σ₀ P Q (U.globT σ₀) ((U.dropSh P Q).globT σ₀)
  | _, .nil, P, Q => .inl ⟨σ₀.globG, σ₀.globG.1.storage, σ₀.globG.memG, rfl, rfl,
      fun _ => rfl, fun _ => rfl⟩
  | Δ₁, .snoc U (.storage S), P, Q => by
    simp only [Upd.dropSh]
    split
    · rename_i hP
      obtain ⟨T, hT, hTS⟩ := List.any_eq_true.1 hP
      show ShRel σ₀ P Q ((U.globT σ₀).bind (UpdElem.globT (Δ := Δ₁) σ₀ (.storage S)))
        ((U.dropSh P Q).globT σ₀)
      rcases Upd.dropSh_rel σ₀ U P Q with ⟨τ, st, μ, ha, hb, h₁, h₂⟩ | ⟨ha, h⟩
      · rw [ha, hb, Option.bind_some, UpdElem.globT_storage]
        cases hs : S.eval σ₀ with
        | none => exact .inr ⟨rfl, .inr (.inl ⟨T, hT, Tm.onSpineS_none hs T hTS⟩)⟩
        | some g =>
          refine .inl ⟨τ.withStorage g, st, μ, rfl, rfl,
            fun hP' => absurd hP' (List.ne_nil_of_mem hT), fun hQ => ?_⟩
          rw [h₂ hQ]; rfl
      · rw [ha]
        exact .inr ⟨rfl, h⟩
    · show ShRel σ₀ P Q ((U.globT σ₀).bind (UpdElem.globT (Δ := Δ₁) σ₀ (.storage S)))
        (((U.dropSh (S :: P) Q).globT σ₀).bind (UpdElem.globT (Δ := Δ₁) σ₀ (.storage S)))
      rcases Upd.dropSh_rel σ₀ U (S :: P) Q with ⟨τ, st, μ, ha, hb, h₁, h₂⟩ | ⟨ha, h⟩
      · rw [ha, hb, Option.bind_some, Option.bind_some, UpdElem.globT_storage,
          UpdElem.globT_storage]
        cases hs : S.eval σ₀ with
        | none => exact .inr ⟨rfl, .inl rfl⟩
        | some g =>
          refine .inl ⟨τ.withStorage g, g, μ, rfl, rfl, fun _ => rfl, fun hQ => ?_⟩
          rw [h₂ hQ]; rfl
      · rw [ha]
        refine .inr ⟨rfl, ?_⟩
        rcases h with hb | ⟨T, hT, hTe⟩ | hM
        · rw [hb]; exact .inl rfl
        · rcases List.mem_cons.1 hT with rfl | hT
          · cases (U.dropSh (T :: P) Q).globT σ₀ with
            | none => exact .inl rfl
            | some ρ =>
              refine .inl ?_
              rw [Option.bind_some, UpdElem.globT_storage, hTe]
              rfl
          · exact .inr (.inl ⟨T, hT, hTe⟩)
        · exact .inr (.inr hM)
  | Δ₁, .snoc U (.memory M), P, Q => by
    simp only [Upd.dropSh]
    split
    · rename_i hQ
      obtain ⟨N, hN, hNM⟩ := List.any_eq_true.1 hQ
      show ShRel σ₀ P Q ((U.globT σ₀).bind (UpdElem.globT (Δ := Δ₁) σ₀ (.memory M)))
        ((U.dropSh P Q).globT σ₀)
      rcases Upd.dropSh_rel σ₀ U P Q with ⟨τ, st, μ, ha, hb, h₁, h₂⟩ | ⟨ha, h⟩
      · rw [ha, hb, Option.bind_some, UpdElem.globT_memory]
        cases hs : M.eval σ₀ with
        | none => exact .inr ⟨rfl, .inr (.inr ⟨N, hN, Tm.onSpineS_none hs N hNM⟩)⟩
        | some g =>
          refine .inl ⟨τ.withMem g, st, μ, rfl, rfl, fun hP => ?_,
            fun hQ' => absurd hQ' (List.ne_nil_of_mem hN)⟩
          rw [h₁ hP]; rfl
      · rw [ha]
        exact .inr ⟨rfl, h⟩
    · show ShRel σ₀ P Q ((U.globT σ₀).bind (UpdElem.globT (Δ := Δ₁) σ₀ (.memory M)))
        (((U.dropSh P (M :: Q)).globT σ₀).bind (UpdElem.globT (Δ := Δ₁) σ₀ (.memory M)))
      rcases Upd.dropSh_rel σ₀ U P (M :: Q) with ⟨τ, st, μ, ha, hb, h₁, h₂⟩ | ⟨ha, h⟩
      · rw [ha, hb, Option.bind_some, Option.bind_some, UpdElem.globT_memory,
          UpdElem.globT_memory]
        cases hs : M.eval σ₀ with
        | none => exact .inr ⟨rfl, .inl rfl⟩
        | some g =>
          refine .inl ⟨τ.withMem g, st, g, rfl, rfl, fun hP => ?_, fun _ => rfl⟩
          rw [h₁ hP]; rfl
      · rw [ha]
        refine .inr ⟨rfl, ?_⟩
        rcases h with hb | hP | ⟨N, hN, hNe⟩
        · rw [hb]; exact .inl rfl
        · exact .inr (.inl hP)
        · rcases List.mem_cons.1 hN with rfl | hN
          · cases (U.dropSh P (N :: Q)).globT σ₀ with
            | none => exact .inl rfl
            | some ρ =>
              refine .inl ?_
              rw [Option.bind_some, UpdElem.globT_memory, hNe]
              rfl
          · exact .inr (.inr ⟨N, hN, hNe⟩)
  | _, .snoc U (.local i r), P, Q =>
    (Upd.dropSh_rel σ₀ U P Q).bind_globT _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  | _, .snoc U (.selfBalance op a), P, Q =>
    (Upd.dropSh_rel σ₀ U P Q).bind_globT _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  | _, .snoc U (.net r op a), P, Q =>
    (Upd.dropSh_rel σ₀ U P Q).bind_globT _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  | _, .snoc U (.pay r a), P, Q =>
    (Upd.dropSh_rel σ₀ U P Q).bind_globT _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  | _, .snoc U (.netMt r a), P, Q =>
    (Upd.dropSh_rel σ₀ U P Q).bind_globT _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  | _, .snoc U (.setBalance a), P, Q =>
    (Upd.dropSh_rel σ₀ U P Q).bind_globT _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  | _, .decl U x r, P, Q => by
    have ih := Upd.dropSh_rel σ₀ U P Q
    show ShRel σ₀ P Q ((U.globT σ₀).bind fun g => (r.eval σ₀).bind fun _ => some g)
      (((U.dropSh P Q).globT σ₀).bind fun g => (r.eval σ₀).bind fun _ => some g)
    rcases ih with ⟨τ, st, μ, ha, hb, h₁, h₂⟩ | ⟨ha, h⟩
    · rw [ha, hb, Option.bind_some, Option.bind_some]
      cases r.eval σ₀ with
      | none => exact .inr ⟨rfl, .inl rfl⟩
      | some w => exact .inl ⟨τ, st, μ, rfl, rfl, h₁, h₂⟩
    · rw [ha]
      refine .inr ⟨rfl, ?_⟩
      rcases h with hb | h
      · rw [hb]; exact .inl rfl
      · exact .inr h
  | _, .pop U _, P, Q => Upd.dropSh_rel σ₀ U P Q
  | _, .drop U _, P, Q => Upd.dropSh_rel σ₀ U P Q

/-- Dropping the shadowed writes leaves every local as it was. -/
theorem Upd.dropSh_held : {Δ : Ctx} → (U : Upd C Γ Δ) → (P : List (Tm C Γ .st)) →
    (Q : List (Tm C Γ .mem)) → ∀ {t : LTy} (i : Idx Δ t), (U.dropSh P Q).held i = U.held i
  | _, .nil, _, _, _, _ => rfl
  | _, .snoc U (.storage S), P, Q, _, i => by
    simp only [Upd.dropSh]
    split
    · exact Upd.dropSh_held U P Q i
    · exact Upd.dropSh_held U (S :: P) Q i
  | _, .snoc U (.memory M), P, Q, _, i => by
    simp only [Upd.dropSh]
    split
    · exact Upd.dropSh_held U P Q i
    · exact Upd.dropSh_held U P (M :: Q) i
  | _, .snoc U (.local k r), P, Q, _, i => by
    show Subst.set (Upd.held (U.dropSh P Q)) k r i = Subst.set (Upd.held U) k r i
    unfold Subst.set
    split
    · rfl
    · exact Upd.dropSh_held U P Q i
  | _, .snoc U (.selfBalance _ _), P, Q, _, i | _, .snoc U (.net _ _ _), P, Q, _, i
  | _, .snoc U (.pay _ _), P, Q, _, i | _, .snoc U (.netMt _ _), P, Q, _, i
  | _, .snoc U (.setBalance _), P, Q, _, i => Upd.dropSh_held U P Q i
  | _, .decl U x r, P, Q, _, i => by
    cases i with
    | here => rfl
    | there j => exact Upd.dropSh_held U P Q j
  | _, .pop U e, P, Q, _, i => Upd.dropSh_held U P Q (i.ext e)
  | _, .drop U e, P, Q, _, i => Upd.dropSh_held U P Q (i.wk e)

/-- A term out of gas with `S` on its spine, `S` halting: `S` is out of gas
(what halts the term first is `S`). -/
theorem Tm.spineHas_exhB {k : Srt} {S : Tm C Γ k} {σ : State C Γ} (hS : S.eval σ = none) :
    {s : Srt} → (T : Tm C Γ s) → Tm.spineHasM S T = true → T.exhB σ = true → S.exhB σ = true
  | _, .app1 o a, h, hx => by
    simp only [Tm.spineHasM, Bool.or_eq_true] at h
    simp only [Tm.exhB, Bool.and_eq_true] at hx
    rcases h with h | h
    · cases Tm.sigma_eq_of_beqR h; exact hx.2
    · exact Tm.spineHas_exhB hS a h hx.2
  | _, .app2 o a b, h, hx => by
    simp only [Tm.spineHasM, Bool.or_eq_true] at h
    have ha : a.eval σ = none := by
      rcases h with h | h
      · cases Tm.sigma_eq_of_beqR h; exact hS
      · exact Tm.spineHas_none hS a h
    simp only [Tm.exhB, ha, Op2.exhB_none_fst, Option.isSome_none, Bool.and_false,
      Bool.or_false, Bool.false_or, Bool.and_eq_true] at hx
    rcases h with h | h
    · cases Tm.sigma_eq_of_beqR h; exact hx.2.1
    · exact Tm.spineHas_exhB hS a h hx.2.1
  | _, .app3 o a b c, h, hx => by
    simp only [Tm.spineHasM, Bool.or_eq_true] at h
    have ha : a.eval σ = none := by
      rcases h with h | h
      · cases Tm.sigma_eq_of_beqR h; exact hS
      · exact Tm.spineHas_none hS a h
    simp only [Tm.exhB, ha, Op3.exhB_none_fst, Option.isSome_none, Bool.and_false,
      Bool.false_and, Bool.or_false, Bool.false_or, Bool.and_eq_true] at hx
    rcases h with h | h
    · cases Tm.sigma_eq_of_beqR h; exact hx.2.1.1
    · exact Tm.spineHas_exhB hS a h hx.2.1.1
  | _, .pvV _, h, _ | _, .pvP _, h, _ | _, .pvS _, h, _ | _, .pvI _, h, _ | _, .netOf .., h, _
  | _, .app0 _, h, _ => by simp only [Tm.spineHasM, Bool.false_eq_true] at h

/-- What a term that returns or is out of gas reads first returns or is out
of gas. -/
theorem Tm.onSpineS_okx {k : Srt} {T S : Tm C Γ k} {σ : State C Γ} (h : T.onSpineS S = true)
    (hT : (T.eval σ).isSome = true ∨ T.exhB σ = true) :
    (S.eval σ).isSome = true ∨ S.exhB σ = true := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain rfl := Tm.eq_of_beqR h; exact hT
  · cases hS : S.eval σ with
    | some _ => exact .inl rfl
    | none =>
      have hT' := Tm.spineHas_none hS T (Tm.spineHas_eq_spineHasM S T ▸ h)
      rw [hT'] at hT
      exact .inr (Tm.spineHas_exhB hS T (Tm.spineHas_eq_spineHasM S T ▸ h)
        (hT.resolve_left (by simp only [Option.isSome_none, Bool.false_eq_true, not_false_eq_true])))

/-- **Dropping shadowed writes keeps exhaustion**: a dropped write lies on
the spine of a later one, which returns or is out of gas where the dropped
update reverts nowhere. -/
theorem Upd.dropSh_exh (σ₀ : State C Γ) : {Δ : Ctx} → (U : Upd C Γ Δ) →
    (P : List (Tm C Γ .st)) → (Q : List (Tm C Γ .mem)) →
    (∀ T ∈ P, (T.eval σ₀).isSome = true ∨ T.exhB σ₀ = true) →
    (∀ M ∈ Q, (M.eval σ₀).isSome = true ∨ M.exhB σ₀ = true) →
    (U.dropSh P Q).exhOk σ₀ = true →
      U.exhOk σ₀ = true ∧ ((U.dropSh P Q).exhAny σ₀ = true → U.exhAny σ₀ = true)
  | _, .nil, _, _, _, _, _ => ⟨rfl, id⟩
  | _, .snoc U (.storage S), P, Q, hP, hQ, hk => by
    simp only [Upd.dropSh] at hk ⊢
    by_cases hp : (P.any fun x => x.onSpineS S) = true
    · rw [if_pos hp] at hk ⊢
      obtain ⟨T, hT, hTS⟩ := List.any_eq_true.1 hp
      obtain ⟨ih₁, ih₂⟩ := Upd.dropSh_exh σ₀ U P Q hP hQ hk
      have hS := Tm.onSpineS_okx hTS (hP T hT)
      refine ⟨?_, fun h => ?_⟩
      · simp only [Upd.exhOk, ih₁, Bool.true_and, UpdElem.okB, UpdElem.exhB, Bool.or_eq_true]
        exact hS
      · simp only [Upd.exhAny, ih₂ h, Bool.true_or]
    · rw [if_neg hp] at hk ⊢
      simp only [Upd.exhOk, Bool.and_eq_true, Bool.or_eq_true, UpdElem.okB, UpdElem.exhB] at hk
      have hS : (S.eval σ₀).isSome = true ∨ S.exhB σ₀ = true := hk.2
      obtain ⟨ih₁, ih₂⟩ := Upd.dropSh_exh σ₀ U (S :: P) Q
        (fun T hT => (List.mem_cons.1 hT).elim (fun e => e ▸ hS) (hP T)) hQ hk.1
      refine ⟨?_, fun h => ?_⟩
      · simp only [Upd.exhOk, ih₁, Bool.true_and, UpdElem.okB, UpdElem.exhB, Bool.or_eq_true]
        exact hS
      · simp only [Upd.exhAny, Bool.or_eq_true] at h ⊢
        exact h.imp_left ih₂
  | _, .snoc U (.memory M), P, Q, hP, hQ, hk => by
    simp only [Upd.dropSh] at hk ⊢
    by_cases hq : (Q.any fun x => x.onSpineS M) = true
    · rw [if_pos hq] at hk ⊢
      obtain ⟨N, hN, hNM⟩ := List.any_eq_true.1 hq
      obtain ⟨ih₁, ih₂⟩ := Upd.dropSh_exh σ₀ U P Q hP hQ hk
      have hM := Tm.onSpineS_okx hNM (hQ N hN)
      refine ⟨?_, fun h => ?_⟩
      · simp only [Upd.exhOk, ih₁, Bool.true_and, UpdElem.okB, UpdElem.exhB, Bool.or_eq_true]
        exact hM
      · simp only [Upd.exhAny, ih₂ h, Bool.true_or]
    · rw [if_neg hq] at hk ⊢
      simp only [Upd.exhOk, Bool.and_eq_true, Bool.or_eq_true, UpdElem.okB, UpdElem.exhB] at hk
      have hM : (M.eval σ₀).isSome = true ∨ M.exhB σ₀ = true := hk.2
      obtain ⟨ih₁, ih₂⟩ := Upd.dropSh_exh σ₀ U P (M :: Q) hP
        (fun N hN => (List.mem_cons.1 hN).elim (fun e => e ▸ hM) (hQ N)) hk.1
      refine ⟨?_, fun h => ?_⟩
      · simp only [Upd.exhOk, ih₁, Bool.true_and, UpdElem.okB, UpdElem.exhB, Bool.or_eq_true]
        exact hM
      · simp only [Upd.exhAny, Bool.or_eq_true] at h ⊢
        exact h.imp_left ih₂
  | _, .snoc U (.local _ _), P, Q, hP, hQ, hk | _, .snoc U (.selfBalance _ _), P, Q, hP, hQ, hk
  | _, .snoc U (.net _ _ _), P, Q, hP, hQ, hk | _, .snoc U (.pay _ _), P, Q, hP, hQ, hk
  | _, .snoc U (.netMt _ _), P, Q, hP, hQ, hk | _, .snoc U (.setBalance _), P, Q, hP, hQ, hk => by
    simp only [Upd.dropSh, Upd.exhOk, Bool.and_eq_true] at hk
    obtain ⟨ih₁, ih₂⟩ := Upd.dropSh_exh σ₀ U P Q hP hQ hk.1
    refine ⟨?_, fun h => ?_⟩
    · simp only [Upd.exhOk, ih₁, hk.2, Bool.and_self]
    · simp only [Upd.dropSh, Upd.exhAny, Bool.or_eq_true] at h ⊢
      exact h.imp_left ih₂
  | _, .decl U x r, P, Q, hP, hQ, hk => by
    simp only [Upd.dropSh, Upd.exhOk, Bool.and_eq_true] at hk
    obtain ⟨ih₁, ih₂⟩ := Upd.dropSh_exh σ₀ U P Q hP hQ hk.1
    refine ⟨?_, fun h => ?_⟩
    · simp only [Upd.exhOk, ih₁, hk.2, Bool.and_self]
    · simp only [Upd.dropSh, Upd.exhAny, Bool.or_eq_true] at h ⊢
      exact h.imp_left ih₂
  | _, .pop U e, P, Q, hP, hQ, hk => Upd.dropSh_exh σ₀ U P Q hP hQ hk
  | _, .drop U e, P, Q, hP, hQ, hk => Upd.dropSh_exh σ₀ U P Q hP hQ hk

/-- **`{U} φ` from `U` with its shadowed writes dropped.** -/
theorem holds_upd_dropSh {m : Modality} {Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ} (σ : State C Γ)
    (h : holds σ (.upd m (U.dropSh [] []) φ)) : holds σ (.upd m U φ) := by
  have hr := Upd.dropSh_rel σ U [] []
  refine Upd.afterT_of_lands (fun he h' => ?_) (fun g σ' hL => ?_) h
  · rcases hr with ⟨τ, _, _, ha, _⟩ | ⟨_, hb | ⟨_, hT, _⟩ | ⟨_, hM, _⟩⟩
    · rw [he] at ha; cases ha
    · refine (h'.of_none hb).imp_right fun hx => ?_
      obtain ⟨hx₁, hx₂⟩ := Bool.and_eq_true_iff.1 hx
      obtain ⟨h₁, h₂⟩ := Upd.dropSh_exh σ U [] [] nofun nofun hx₂
      exact Bool.and_eq_true_iff.2 ⟨h₂ hx₁, h₁⟩
    · nomatch hT
    · nomatch hM
  · refine ⟨?_, hL.2.1, fun i => ?_⟩
    · rcases hr with ⟨τ, st, μ, ha, hb, h₁, h₂⟩ | ⟨ha, _⟩
      · rw [hL.1] at ha
        cases ha
        rw [h₁ rfl, h₂ rfl, GlobT.withSM_self] at hb
        exact hb
      · rw [hL.1] at ha; cases ha
    · rw [Upd.dropSh_held]
      exact hL.2.2 i

end Shadow

/-! ## Two updates merged -/

section Merge

/-- The modality `{U}_m {V}_m'` merges under: theirs where they agree, the
other's where one cannot halt (`Upd.totalB`, `ut`, `vt`). -/
def Modality.mergeP (m : Modality) (ut : Bool) (m' : Modality) (vt : Bool) : Option Modality :=
  if m' = m then some m else if ut then some m' else if vt then some m else none

/-- An update that cannot halt reads alike under either modality. -/
theorem holds_upd_total {m m' : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} (hU : U.totalB = true)
    {φ : Fml C Δ} (σ : State C Γ) (h : holds σ (.upd m U φ)) : holds σ (.upd m' U φ) := by
  obtain ⟨g, hg⟩ := Upd.totalB_globT σ U hU
  refine Upd.afterT_intro (fun he => ?_) fun _ σ' hL => h.of_lands hL
  rw [hg] at he; cases he

/-- `{U}{V}` as one update, by the first merge that reads it: `V` read in
`U`'s state (`Upd.seqPar`), over a storage write (`Upd.mergeSt?`), a memory
write (`Upd.mergeMem?`), locals then a memory write (`Upd.mergeMemL?`). -/
def Upd.mergeK? {Γ Δ₁ Δ₂ : Ctx} (U : Upd C Γ Δ₁) (V : Upd C Δ₁ Δ₂) : Option (Upd C Γ Δ₂) :=
  match U.seqPar V with
  | some W => some W
  | none => match U.mergeSt? V with
    | some W => some W
    | none => match U.mergeMem? V with
      | some W => some W
      | none => U.mergeMemL? V

theorem holds_upd_mergeK {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} (hW : U.mergeK? V = some W) {φ : Fml C Δ₂} (σ : State C Γ)
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) := by
  unfold Upd.mergeK? at hW
  split at hW
  · rename_i hs; cases hW; exact holds_upd_seqPar hs σ h
  · split at hW
    · rename_i hs; cases hW; exact holds_upd_mergeSt hs σ h
    · split at hW
      · rename_i hs; cases hW; exact holds_upd_mergeMem hs σ h
      · exact holds_upd_mergeMemL hW σ h

/-- **`sequentialToParallel` past the program**: `{U}_m {V}_m'` as one
update and its modality, the shadowed state writes dropped. -/
def Upd.mergeP? {Γ Δ₁ Δ₂ : Ctx} (m : Modality) (U : Upd C Γ Δ₁) (m' : Modality)
    (V : Upd C Δ₁ Δ₂) : Option (Modality × Upd C Γ Δ₂) :=
  (Modality.mergeP m U.totalB m' V.totalB).bind fun mm =>
    (U.mergeK? V).map fun W => (mm, W.dropSh [] [])

theorem holds_upd_mergeP {m m' : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {r : Modality × Upd C Γ Δ₂} (hr : Upd.mergeP? m U m' V = some r) {φ : Fml C Δ₂}
    (σ : State C Γ) (h : holds σ (.upd r.1 r.2 φ)) : holds σ (.upd m U (.upd m' V φ)) := by
  obtain ⟨mm, hmm, hr⟩ := Option.bind_eq_some_iff.1 hr
  obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 hr
  have h₂ : holds σ (.upd mm U (.upd mm V φ)) := holds_upd_mergeK hW σ (holds_upd_dropSh σ h)
  unfold Modality.mergeP at hmm
  split at hmm
  · rename_i he; cases hmm; rw [he]; exact h₂
  · split at hmm
    · rename_i hu; cases hmm; exact holds_upd_total hu σ h₂
    · split at hmm
      · rename_i hv; cases hmm
        exact holds_upd_mono (fun τ hτ => holds_upd_total hv τ hτ) σ h₂
      · cases hmm

/-- `{U}_m bind x ψ` merged where `ψ` is an update that sets `x` first: the
binder absorbed (`Upd.absorb`), then the two merged. -/
def Fml.absorbMergeP (m : Modality) {Γ Δ : Ctx} (U : Upd C Γ Δ) (x : Var) {t : LTy}
    (ψ : Fml C (t :: Δ)) : Option (Fml C Γ) :=
  match ψ with
  | .upd m'' V χ => (V.absorb x).bind fun V' => (Upd.mergeP? m U m'' V').map fun r => .upd r.1 r.2 χ
  | _ => none

theorem Fml.absorbMergeP_sound {m m' : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} {x : Var} {t : LTy}
    {ψ : Fml C (t :: Δ)} {φ : Fml C Γ} (h : Fml.absorbMergeP m U x ψ = some φ) (σ : State C Γ)
    (hφ : holds σ φ) : holds σ (.upd m U (.bind m' x t ψ)) := by
  unfold Fml.absorbMergeP at h
  split at h
  · rename_i m'' V χ
    obtain ⟨V', hV', h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
    exact holds_upd_mono (fun τ hτ => holds_bind_absorb hV' τ hτ) σ (holds_upd_mergeP hr σ hφ)
  · cases h

/-- `bind x ψ` with its local absorbed into the update `ψ` begins with,
where that update sets it before reading it (`Upd.absorb`). -/
def Fml.absorbBind {Δ : Ctx} (m : Modality) (x : Var) (t : LTy) : Fml C (t :: Δ) → Fml C Δ
  | .upd m'' V χ => match V.absorb x true with
    | some V' => .upd m'' V' χ
    | none => .bind m x t (.upd m'' V χ)
  | ψ => .bind m x t ψ

theorem Fml.absorbBind_holds {Δ : Ctx} {m : Modality} {x : Var} {t : LTy} (ψ : Fml C (t :: Δ))
    (σ : State C Δ) (h : holds σ (Fml.absorbBind m x t ψ)) : holds σ (.bind m x t ψ) := by
  unfold Fml.absorbBind at h
  split at h
  · rename_i m'' V χ
    split at h
    · rename_i V' hV
      exact holds_bind_absorb hV σ h
    · exact h
  · exact h

/-- The hidden binders a formula begins with absorbed, innermost first, into
the update under them (`Fml.absorbBind`). -/
def Fml.absorbBinds : {Δ : Ctx} → Fml C Δ → Fml C Δ
  | _, .bind m x t ψ => Fml.absorbBind m x t (Fml.absorbBinds ψ)
  | _, φ => φ

theorem Fml.absorbBinds_holds : {Δ : Ctx} → (φ : Fml C Δ) → (σ : State C Δ) →
    holds σ (Fml.absorbBinds φ) → holds σ φ
  | _, .bind m x t ψ, σ, h => by
    have h' := Fml.absorbBind_holds (Fml.absorbBinds ψ) σ h
    exact Modality.forallB_imp (fun w hw => Fml.absorbBinds_holds ψ _ hw) h'
  | _, .tt, _, h | _, .eq .., _, h | _, .wellFormed _, _, h | _, .not _, _, h | _, .and .., _, h
  | _, .imp .., _, h | _, .upd .., _, h | _, .modal .., _, h | _, .havoc _, _, h
  | _, .all .., _, h | _, .anon .., _, h | _, .allocAll .., _, h | _, .grow .., _, h => h

/-- `{U}_m φ` merged with the update `φ` begins with once the hidden binders
in front of it are absorbed into it, innermost first (`Fml.absorbBinds`): a
local an update sets after declaring others is declared before them. -/
def Fml.absorbAllMergeP (m : Modality) {Γ Δ : Ctx} (U : Upd C Γ Δ) (φ : Fml C Δ) :
    Option (Fml C Γ) :=
  match Fml.absorbBinds φ with
  | .upd m'' V χ => (Upd.mergeP? m U m'' V).map fun r => .upd r.1 r.2 χ
  | _ => none

theorem Fml.absorbAllMergeP_sound {m : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ}
    {ψ : Fml C Γ} (h : Fml.absorbAllMergeP m U φ = some ψ) (σ : State C Γ) (hψ : holds σ ψ) :
    holds σ (.upd m U φ) := by
  unfold Fml.absorbAllMergeP at h
  split at h
  · rename_i m'' V χ hab
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
    refine holds_upd_mono (fun τ hτ => Fml.absorbBinds_holds φ τ ?_) σ (holds_upd_mergeP hr σ hψ)
    rw [hab]
    exact hτ
  · cases h

/-- `{U}_m φ` merged with the update at the head of `φ`, through a hidden
binder: absorbed where the update sets its local first (`Fml.absorbMergeP`),
or `U` moved under it with its scope ends (`Upd.liftG?`, as
`Calculus/Merge.lean`'s `Fml.merge2` moves one); with `reorder`, first every
binder absorbed, which may declare a local before the ones its update
declares first (`Fml.absorbAllMergeP`). -/
def Fml.merge2P (m : Modality) (reorder : Bool) :
    {Γ Δ : Ctx} → Upd C Γ Δ → Fml C Δ → Option (Fml C Γ)
  | _, _, U, .upd m' V ψ => (Upd.mergeP? m U m' V).map fun r => .upd r.1 r.2 ψ
  | _, _, U, .bind m' x t ψ =>
    match Fml.absorbMergeP m U x ψ with
    | some φ => some φ
    | none =>
      match (if reorder then Fml.absorbAllMergeP m U (.bind m' x t ψ) else none) with
      | some φ => some φ
      | none =>
        if (t.notMem || U.keepsNext) = true then
          (U.liftG? (t := t)).bind fun U' => (Fml.merge2P m reorder U' ψ).map (.bind m' x t)
        else none
  | _, _, _, _ => none

theorem Fml.merge2P_sound {m : Modality} {reorder : Bool} : {Γ Δ : Ctx} → (U : Upd C Γ Δ) →
    (φ : Fml C Δ) → {ψ : Fml C Γ} → Fml.merge2P m reorder U φ = some ψ →
      ∀ σ, holds σ ψ → holds σ (.upd m U φ)
  | _, _, U, .upd m' V χ, ψ, h => by
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hψ => holds_upd_mergeP hr σ hψ
  | _, _, U, .bind m' x t χ, ψ, h => by
    simp only [Fml.merge2P] at h
    split at h
    · rename_i φ hφ
      cases h
      exact fun σ hψ => Fml.absorbMergeP_sound hφ σ hψ
    · split at h
      · rename_i φ' hφ'
        cases h
        split at hφ'
        · exact fun σ hψ => Fml.absorbAllMergeP_sound hφ' σ hψ
        · cases hφ'
      · split at h
        · rename_i ht
          obtain ⟨U', hU', h⟩ := Option.bind_eq_some_iff.1 h
          obtain ⟨χ', hχ', rfl⟩ := Option.map_eq_some_iff.1 h
          intro σ hψ
          exact Fml.upd_bind_of_liftG hU' ht σ
            (Modality.forallB_imp (fun v h => Fml.merge2P_sound U' χ hχ' _ h) hψ)
        · cases h
  | _, _, _, .tt, _, h | _, _, _, .eq .., _, h | _, _, _, .wellFormed _, _, h | _, _, _, .not _, _, h
  | _, _, _, .and .., _, h | _, _, _, .imp .., _, h | _, _, _, .modal .., _, h
  | _, _, _, .havoc _, _, h | _, _, _, .all .., _, h | _, _, _, .anon .., _, h
  | _, _, _, .allocAll .., _, h | _, _, _, .grow .., _, h => nomatch h

/-- `sequentialToParallel` past the program on the updates at positions `k`
and `k + 1` of the line's update spine, under its quantifiers and hidden
binders. -/
def Fml.mergeAtP {Γ : Ctx} (reorder : Bool) : Nat → Fml C Γ → Option (Fml C Γ)
  | k, .all x p φ => (Fml.mergeAtP reorder k φ).map (.all x p)
  | k, .bind m x t φ => (Fml.mergeAtP reorder k φ).map (.bind m x t)
  | 0, .upd m U φ => Fml.merge2P m reorder U φ
  | k + 1, .upd m U φ => (Fml.mergeAtP reorder k φ).map (.upd m U)
  | _, _ => none

/-- `Fml.mergeAtP` `n` times: the `n + 1` updates from position `k` merged
into one, the innermost pair first (a merge over
a memory write asks the write last in the update before, which the pair
after it is merged into first). -/
def Fml.mergeRunP {Γ : Ctx} (reorder : Bool) (k : Nat) : Nat → Fml C Γ → Option (Fml C Γ)
  | 0, φ => some φ
  | n + 1, φ => (φ.mergeAtP reorder (k + n)).bind (Fml.mergeRunP reorder k n)

theorem Fml.mergeAtP_sound (reorder : Bool) : {Γ : Ctx} → (k : Nat) → (φ : Fml C Γ) → {ψ : Fml C Γ} →
    φ.mergeAtP reorder k = some ψ → ∀ σ, holds σ ψ → holds σ φ
  | _, k, .all x p φ, ψ₀, h => by
    have h : (Fml.mergeAtP reorder k φ).map (Fml.all x p) = some ψ₀ := by rw [← h]; cases k <;> rfl
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs v => Fml.mergeAtP_sound reorder k φ hψ _ (hs v)
  | _, k, .bind m x t φ, ψ₀, h => by
    have h : (Fml.mergeAtP reorder k φ).map (Fml.bind m x t) = some ψ₀ := by rw [← h]; cases k <;> rfl
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs => Modality.forallB_imp (fun v => Fml.mergeAtP_sound reorder k φ hψ _) hs
  | _, 0, .upd m U φ, _, h => Fml.merge2P_sound U φ h
  | _, k + 1, .upd m U φ, _, h => by
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs => Upd.afterT_imp hs fun σ' a => Fml.mergeAtP_sound reorder k φ hψ σ' a
  | _, k, .tt, _, h | _, k, .eq .., _, h | _, k, .wellFormed _, _, h | _, k, .not _, _, h
  | _, k, .and .., _, h | _, k, .imp .., _, h | _, k, .modal .., _, h | _, k, .havoc _, _, h
  | _, k, .anon .., _, h | _, k, .allocAll .., _, h | _, k, .grow .., _, h => by
    cases k <;> cases h

theorem Fml.mergeRunP_sound {Γ : Ctx} (reorder : Bool) (k : Nat) : (n : Nat) → (φ : Fml C Γ) →
    {ψ : Fml C Γ} → φ.mergeRunP reorder k n = some ψ → ∀ σ, holds σ ψ → holds σ φ
  | 0, φ, _, h => by cases h; exact fun _ h => h
  | n + 1, φ, _, h => by
    obtain ⟨χ, hχ, h⟩ := Option.bind_eq_some_iff.1 h
    exact fun σ hψ => Fml.mergeAtP_sound reorder (k + n) φ hχ σ (Fml.mergeRunP_sound reorder k n χ h σ hψ)

/-- **`sequentialToParallel` past the program**: the `n + 1` updates from
position `k` of the spine merged (`Fml.mergeRunP`), each local where its
update declares it; where that leaves a hidden binder unmerged, every binder
absorbed (`Fml.absorbAllMergeP`: a local an update sets late is declared,
and printed, first). -/
def FmlRw.mergePast (k n : Nat) : FmlRw C where
  apply := fun φ => match φ.mergeRunP false k (n + 1) with
    | some ψ => some ψ
    | none => φ.mergeRunP true k (n + 1)
  sound := fun {_ φ _} h σ hψ => by
    split at h
    · cases h
      exact Fml.mergeRunP_sound false k (n + 1) φ (by assumption) σ hψ
    · exact Fml.mergeRunP_sound true k (n + 1) φ h σ hψ

end Merge

end Solidity
