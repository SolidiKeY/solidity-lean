import Solidity.Calculus.Sound

/-!
# The steps after the program, on the scoped sequent

What symbolic execution leaves is closed as KeY closes it: the updates
merged (`merge`, `mergeStorage`), the terms rewritten inside the sequent,
the goal split and closed.  The rules on the context's updates are
constructors of `Proves` (`Calculus/Proves.lean`: `merge`, `updRw`), so
they apply while a modality is still open.  The steps that finish a goal
are derived here from `Proves.closeHolds`; each needs a sequent with no modality
left (`Fml.modalFree`), and those that drop a fact a context gives, no
diamond in it (`Hyps.boxOnly`):

* `andSplit` (`andRight`), `eqDSplit`: `a = b` into `defined(a)`,
  `defined(b)` and `a ≐ b`;
* `definedWritten`, `definedLit`, `eqRefl`, `eqClose`, `eqDClose`: a local
  of the typed state always holds a value of its type, so `defined(x)`
  needs no update that wrote `x`;
* `applyOnRigidBox` (`applyOnRigidFormula` under the box): the last update
  applied to a first-order goal and dropped (`Fml.substU`; a goal that reads
  no global part where the update writes one);
* `simplify` (`simplifyUpdate`, under the box): an element setting a local
  the same update pops later is dropped (`Upd.simp`);
* `rewrite'`: `Proves.rewrite` (a rule of the calculus, decision 90) with
  the rewritten context and goal written out.

`Upd.simp` and `Fml.substU` use `match` on the indexed
families, against Gate G0's first condition: an exemption, timed
(`docs/intrinsic.md`, W3c `tactics`), since they run once a rule.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality RuleSet)

variable {C : Contract}

/-! ## Symbols that read no global part, in the Theory -/

section DenoteSame

variable {g₀ g₁ : State C []}

theorem _root_.Solidity.Op0.denote_same {s : Srt} (o : Op0 C s)
    (hc : g₀ = g₁ ∨ o.globFree = true) : o.denote g₀ = o.denote g₁ := by
  rcases hc with rfl | hf
  · rfl
  · cases o <;> first | rfl | exact absurd hf Bool.false_ne_true

theorem _root_.Solidity.Op1.denote_same {a s : Srt} (o : Op1 C a s)
    (hc : g₀ = g₁ ∨ o.globFree = true) (d : a.TDen C) : o.denote g₀ d = o.denote g₁ d := by
  rcases hc with rfl | hf
  · rfl
  · cases o <;> first | rfl | exact absurd hf Bool.false_ne_true

/-- A binary symbol's denotation reads its arguments' typed readings only
where it reads the memory, which a symbol free of the global part does
not. -/
theorem _root_.Solidity.Op2.denote_same {a b s : Srt} (o : Op2 C a b s)
    (hc : g₀ = g₁ ∨ o.globFree = true) {x : Option (a.Den C g₀.H)} {x' : Option (a.Den C g₁.H)}
    {y : Option (b.Den C g₀.H)} {y' : Option (b.Den C g₁.H)}
    (hx : Srt.SameO a x x') (hy : Srt.SameO b y y') (da : a.TDen C) (db : b.TDen C) :
    o.denote g₀ x y da db = o.denote g₁ x' y' da db := by
  rcases hc with rfl | hf
  · rw [Srt.SameO.eq hx, Srt.SameO.eq hy]
  · cases o <;> first | rfl | exact absurd hf Bool.false_ne_true

end DenoteSame

/-! ## A term read in the state before an update, in the Theory -/

/-- An alias denotes the location it holds, a dangling one unset. -/
theorem Tm.denote_pvP {Γ : Ctx} (σ : State C Γ) {R : RefTy} (i : Idx Γ (.alias R)) :
    (Tm.pvP i).denote σ = ((σ.getV i).map SLoc.ref).getD (.dangling _ .nil) := by
  show (match (TEnv.get i σ.env : Option (SRef C (.ref R))) with
    | some r => SLoc.ref r | none => .dangling _ .nil) =
      ((TEnv.get i σ.env : Option (SRef C (.ref R))).map SLoc.ref).getD (.dangling _ .nil)
  cases (TEnv.get i σ.env : Option (SRef C (.ref R))) <;> rfl

section Denote

variable {Γ Δ : Ctx} {σ₀ : State C Γ} {σ₁ : State C Δ} {U : Upd C Γ Δ} {g : GlobT C σ₀.H}

/-- **A term read before an update denotes what it denotes in every typed
state the update lands on**, its locals replaced by what the update leaves
in them. -/
theorem Tm.denote_substH (hL : U.Lands σ₀ g σ₁) :
    {k : Srt} → (t : Tm C Δ k) → {t' : Tm C Γ k} → t.substH U.held U.envOnly none = some t' →
      t'.denote σ₀ = t.denote σ₁
  | _, .pvV i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvV j) | .rhs (.val t) => some t) = some t' := h
    generalize U.held i = x at h hx
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      show some _ = some _
      rw [hx]
    | .rhs (.val t), hx, h =>
      cases h
      exact Tm.denote_eval σ₀ t' _ hx
  | _, .pvP i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvP j) | .rhs (.path p) => some p | .rhs .unset => none) =
          some t' := h
    generalize U.held i = x at h hx
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      have hx : σ₁.getV i = σ₀.getV j := hx
      rw [Tm.denote_pvP, Tm.denote_pvP, hx]
    | .rhs (.path p), hx, h =>
      cases h
      have hx : (t'.eval σ₀).bind (fun r => some (some r)) = some (TEnv.get i σ₁.env) := hx
      cases hp : t'.eval σ₀ with
      | none => rw [hp] at hx; cases hx
      | some q =>
        rw [hp] at hx
        have hq : TEnv.get i σ₁.env = some q := (Option.some.inj hx).symm
        simp only [Tm.denote, hq]
        exact Tm.denote_eval σ₀ t' q hp
  | _, .pvS i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvS j) | .rhs _ => none) = some t' := h
    generalize U.held i = x at h hx
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      simp only [Tm.denote, hx]
    | .rhs _, _, h => cases h
  | _, .pvI _, _, _ => rfl
  | _, .netOf i a, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => (a.substH U.held U.envOnly none).map (Tm.netOf j) | .rhs _ => none) =
          some t' := h
    generalize U.held i = x at h hx
    match x, hx, h with
    | .rhs _, _, h => cases h
    | .pos j, hx, h =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      simp only [Tm.denote]
      rw [Tm.denote_substH hL a ha, hx]
  | _, .app0 o, t', h => by
    simp only [Tm.substH] at h
    split at h
    · rename_i hc
      cases h
      exact Op0.denote_same o (hL.glob_or hc)
    · revert h
      cases o <;> exact fun h => Option.noConfusion h
  | _, .app1 o x, t', h => by
    simp only [Tm.substH] at h
    split at h
    · rename_i hc
      obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
      show o.denote σ₀.glob (x'.denote σ₀) = o.denote σ₁.glob (x.denote σ₁)
      rw [Tm.denote_substH hL x hx]
      exact Op1.denote_same o (hL.glob_or hc) _
    · cases h
  | _, .app2 o x y, t', h => by
    simp only [Tm.substH] at h
    split at h
    · rename_i hc
      obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      have hst : ∀ z, (none : Option (Tm C Γ .st)) = some z → z.eval σ₀ = some σ₁.storage :=
        fun _ h => Option.noConfusion h
      show o.denote σ₀.glob (x'.eval σ₀) (y'.eval σ₀) (x'.denote σ₀) (y'.denote σ₀) =
        o.denote σ₁.glob (x.eval σ₁) (y.eval σ₁) (x.denote σ₁) (y.denote σ₁)
      rw [Tm.denote_substH hL x hx, Tm.denote_substH hL y hy]
      exact Op2.denote_same o (hL.glob_or hc) (Tm.eval_substH hL hst x hx)
        (Tm.eval_substH hL hst y hy) _ _
    · cases h
  | _, .app3 o x y z, t', h => by
    simp only [Tm.substH] at h
    split at h
    · obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨z', hz, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      show o.denote (x'.denote σ₀) (y'.denote σ₀) (z'.denote σ₀) =
        o.denote (x.denote σ₁) (y.denote σ₁) (z.denote σ₁)
      rw [Tm.denote_substH hL x hx, Tm.denote_substH hL y hy, Tm.denote_substH hL z hz]
    · cases h
  | _, .pvZ i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvZ j) | .rhs (.zint t) => some t) = some t' := h
    generalize U.held i = x at h hx
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      show some _ = some _
      rw [hx]
    | .rhs (.zint t), hx, h =>
      cases h
      exact Tm.denote_eval σ₀ t' _ hx

end Denote

/-! ## Two typed states read alike are one

With nothing erased, a typed state is its global part and its locals'
values (a memory local's identity types its reference in the one heap
typing), so two states a term reads alike are equal (`State.eq_of_readsAs`)
and every congruence of the erased reading is `subst`. -/

section ReadsAs

variable {Γ : Ctx}

/-- Two typed states with one global part and one value per local. -/
def State.ReadsAs (σ σ' : State C Γ) : Prop :=
  σ.glob = σ'.glob ∧ ∀ {t : LTy} (i : Idx Γ t), σ.getV i = σ'.getV i

theorem LTy.VDen.ofT_injective {H : HTy} : (t : LTy) → {v w : t.TDenote C H} →
    LTy.VDen.ofT t v = LTy.VDen.ofT t w → v = w
  | .val _, _, _, h | .alias _, _, _, h | .old, _, _, h | .oldNet, _, _, h | .kint, _, _, h => h
  | .mem _, v, w, h => by
    rcases v with _ | ⟨i, hi⟩ <;> rcases w with _ | ⟨j, hj⟩
    · rfl
    · cases h
    · cases h
    · simp only [LTy.VDen.ofT, Option.map_some, Option.some.injEq] at h
      subst h
      rfl

/-- **Two typed states read alike are one.** -/
theorem State.eq_of_readsAs {σ σ' : State C Γ} (h : σ.ReadsAs σ') : σ = σ' := by
  obtain ⟨hg, hl⟩ := h
  rcases σ with ⟨st, H, hp, env, nt, sb, tx⟩
  rcases σ' with ⟨st', H', hp', env', nt', sb', tx'⟩
  simp only [State.glob, State.mk.injEq] at hg
  obtain ⟨rfl, rfl, hh, -, rfl, rfl, rfl⟩ := hg
  cases hh
  have he : env = env' :=
    TEnv.ext fun _ i => LTy.VDen.ofT_injective _ (hl i)
  rw [he]

end ReadsAs

/-! ## Applying an update to a first-order goal -/

/-- A first-order formula of the scope an update leaves, read in the scope it
is applied in: its terms' locals replaced by what the update leaves in
them (`Tm.substH`); `none` past an atom it cannot read there. -/
def Fml.substU {Γ Δ : Ctx} (U : Upd C Γ Δ) : Fml C Δ → Option (Fml C Γ)
  | .tt => some .tt
  | .eq a b => do pure (.eq (← a.substH U.held U.envOnly none) (← b.substH U.held U.envOnly none))
  | .defined t => (t.substH U.held U.envOnly none).map .defined
  | .not φ => (Fml.substU U φ).map .not
  | .and φ ψ => do pure (.and (← Fml.substU U φ) (← Fml.substU U ψ))
  | .imp φ ψ => do pure (.imp (← Fml.substU U φ) (← Fml.substU U ψ))
  | _ => none

/-- **A goal read before an update holds in every typed state the update
lands on exactly where it holds before.** -/
theorem Fml.substU_holds {Γ Δ : Ctx} {U : Upd C Γ Δ} {σ : State C Γ} {g : GlobT C σ.H}
    {σ' : State C Δ} (hL : U.Lands σ g σ') :
    (φ : Fml C Δ) → {φ' : Fml C Γ} → Fml.substU U φ = some φ' → (holds σ φ' ↔ holds σ' φ)
  | .tt, _, h => by cases h; exact Iff.rfl
  | .eq a b, _, h => by
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    rw [holds_eq, holds_eq, Tm.denote_substH hL a ha, Tm.denote_substH hL b hb]
  | .defined t, _, h => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [holds_defined, holds_defined,
      Srt.sameO_val.1 (Tm.eval_substH hL (st := none) (fun _ h => Option.noConfusion h) t ht)]
  | .not φ, _, h => by
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact not_congr (Fml.substU_holds hL φ hφ)
  | .and φ ψ, _, h => by
    obtain ⟨φ', hφ, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ψ', hψ, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact and_congr (Fml.substU_holds hL φ hφ) (Fml.substU_holds hL ψ hψ)
  | .imp φ ψ, _, h => by
    obtain ⟨φ', hφ, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ψ', hψ, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact imp_congr (Fml.substU_holds hL φ hφ) (Fml.substU_holds hL ψ hψ)
  | .upd .., _, h | .modal .., _, h | .havoc _, _, h
  | .all .., _, h | .bind .., _, h | .anon .., _, h => by
    cases h

/-- Under the box, the goal applied gives the update in front of the goal. -/
theorem holds_upd_of_substU {Γ Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ} {φ' : Fml C Γ}
    (hs : Fml.substU U φ = some φ') (σ : State C Γ) (h : holds σ φ') :
    holds σ (.upd .box U φ) :=
  Upd.afterT_intro (fun _ => trivial) fun _ _ hL => (Fml.substU_holds hL φ hs).1 h


/-! ## Dropping what an update pops -/

section Simp

/-- An update with each element that sets a local it pops later dropped:
`n` of the top locals of `Δ` are popped after it. -/
def Upd.simp {Γ : Ctx} : {Δ : Ctx} → Nat → Upd C Γ Δ → Upd C Γ Δ
  | _, _, .nil => .nil
  | _, n, .snoc U (.local i r) =>
    if i.toNat < n then Upd.simp n U else .snoc (Upd.simp n U) (.local i r)
  | _, n, .snoc U e => .snoc (Upd.simp n U) e
  | _, n, .decl U x r => .decl (Upd.simp (n - 1) U) x r
  | _, n, .pop U h => .pop (Upd.simp (n + h.depth) U) h
  | _, _, .drop U h => .drop (Upd.simp 0 U) h

theorem Idx.toNat_ext {Γ : Ctx} {t : LTy} (j : Idx Γ t) : {Δ : Ctx} → (h : Ext Γ Δ) →
    (j.ext h).toNat = j.toNat + h.depth
  | _, .refl => rfl
  | _, .push h => by
    show (j.ext h).toNat + 1 = j.toNat + (h.depth + 1)
    rw [Idx.toNat_ext j h, Nat.add_assoc]

/-- **Where an update returns, so does the update with what it pops
dropped**, to the same global part. -/
theorem Upd.simp_globT {Γ : Ctx} (σ₀ : State C Γ) : {Δ : Ctx} → (n : Nat) → (U : Upd C Γ Δ) →
    ∀ {g : GlobT C σ₀.H}, U.globT σ₀ = some g → (U.simp n).globT σ₀ = some g
  | _, _, .nil, _, h => h
  | _, n, .snoc U e, g, h => by
    change (U.globT σ₀).bind (e.globT σ₀) = some g at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨g₀, h₀, h⟩ := h
    have ih := Upd.simp_globT σ₀ n U h₀
    cases e with
    | «local» i r =>
      rw [UpdElem.globT_eq_globTM] at h
      simp only [UpdElem.globTM, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨v, hv, rfl⟩ := h
      simp only [Upd.simp]
      split
      · exact ih
      · show ((U.simp n).globT σ₀).bind ((UpdElem.local i r).globT σ₀) = _
        rw [ih, Option.bind_some, UpdElem.globT_eq_globTM]
        simp only [UpdElem.globTM, hv, Option.bind_some]
    | _ =>
      show ((U.simp n).globT σ₀).bind (UpdElem.globT σ₀ _) = _
      rw [ih]
      exact h
  | _, n, .decl U x r, g, h => by
    change (U.globT σ₀).bind (fun g => (r.eval σ₀).bind fun _ => some g) = some g at h
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨g₀, h₀, v, hv, rfl⟩ := h
    show ((U.simp (n - 1)).globT σ₀).bind (fun g => (r.eval σ₀).bind fun _ => some g) = _
    rw [Upd.simp_globT σ₀ (n - 1) U h₀, Option.bind_some, hv, Option.bind_some]
  | _, n, .pop U e, _, h => Upd.simp_globT σ₀ (n + e.depth) U h
  | _, _, .drop U _, _, h => Upd.simp_globT σ₀ 0 U h

/-- **The update with what it pops dropped leaves every local above the
`n` top ones as the update does.** -/
theorem Upd.simp_held {Γ : Ctx} : {Δ : Ctx} → (n : Nat) → (U : Upd C Γ Δ) →
    ∀ {t : LTy} (i : Idx Δ t), n ≤ i.toNat → (U.simp n).held i = U.held i
  | _, _, .nil, _, _, _ => rfl
  | _, n, .snoc U e, t, i, hi => by
    cases e with
    | «local» k r =>
      simp only [Upd.simp]
      split
      · rename_i hk
        show _ = Subst.set (Upd.held U) k r i
        unfold Subst.set
        rw [dif_neg (by omega)]
        exact Upd.simp_held n U i hi
      · show Subst.set (Upd.held (U.simp n)) k r i = Subst.set (Upd.held U) k r i
        unfold Subst.set
        split
        · rfl
        · exact Upd.simp_held n U i hi
    | storage _ | memory _ | selfBalance _ _ | net _ _ _ | pay _ _ | netMt _ _ | setBalance _ =>
      exact Upd.simp_held n U i hi
  | _, n, .decl U x r, _, i, hi => by
    cases i with
    | here => rfl
    | there j => exact Upd.simp_held (n - 1) U j (by simp only [Idx.toNat] at hi; omega)
  | _, n, .pop U e, _, i, hi =>
    Upd.simp_held (n + e.depth) U (i.ext e) (by rw [Idx.toNat_ext]; omega)
  | _, _, .drop U e, _, i, _ => Upd.simp_held 0 U (i.wk e) (Nat.zero_le _)

/-- Under the box, an update with what it pops dropped gives the update. -/
theorem holds_upd_simp {Γ Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ} (σ : State C Γ)
    (h : holds σ (.upd .box (U.simp 0) φ)) : holds σ (.upd .box U φ) :=
  Upd.afterT_of_lands (fun _ _ => .inl trivial)
    (fun _ _ hL => Upd.lands_of (fun _ hg => Upd.simp_globT σ 0 U hg)
      (fun i v hv => by rw [Upd.simp_held 0 U i (Nat.zero_le _)]; exact hv) hL) h

end Simp

/-! ## The rules -/

section Rules

variable {R : RuleSet} {Γ₀ Γ : Ctx} {H : Hyps C Γ₀ Γ}

/-- **`andRight`**: a conjunction from each conjunct, in the same context. -/
theorem Proves.andSplit {φ ψ : Fml C Γ} (h₁ : Proves C R Γ₀ H φ) (h₂ : Proves C R Γ₀ H ψ)
    (hm : (H.wrap (.and φ ψ)).modalFree = true := by first | rfl | decide) :
    Proves C R Γ₀ H (.and φ ψ) :=
  .closeHolds (fun σ => H.wrap_and (χ := .and φ ψ) (fun _ a b => ⟨a, b⟩) σ
    (Proves.sound h₁ σ) (Proves.sound h₂ σ)) hm

/-- A program comparison `a = b` (`Fml.eqD`) from its three parts: `a` and
`b` return, and they are equal in the Theory. -/
theorem Proves.eqDSplit {p : PrimTy} {a b : Tm C Γ (.val p)} (ha : Proves C R Γ₀ H (.defined a))
    (hb : Proves C R Γ₀ H (.defined b)) (he : Proves C R Γ₀ H (.eq a b))
    (hm : (H.wrap (Fml.eqD a b)).modalFree = true := by first | rfl | decide) :
    Proves C R Γ₀ H (Fml.eqD a b) :=
  .closeHolds (fun σ => H.wrap_and (χ := Fml.eqD a b) (fun _ x yz => ⟨x, yz⟩) σ
    (Proves.sound ha σ) (H.wrap_and (χ := .and (.defined b) (.eq a b)) (fun _ y z => ⟨y, z⟩) σ
      (Proves.sound hb σ) (Proves.sound he σ))) hm

/-- **`defined(x)`**: a local of the typed state holds a value of its type,
behind a context with no diamond.  Today's asks the update that wrote `x`,
since today's state may not bind it. -/
theorem Proves.definedWritten {p : PrimTy} {i : Idx Γ (.val p)}
    (hb : H.boxOnly = true := by first | rfl | decide)
    (hm : (H.wrap (.defined (.pvV i))).modalFree = true := by first | rfl | decide) :
    Proves C R Γ₀ H (.defined (.pvV i)) :=
  .closeHolds (fun σ => H.wrap_valid (φ := .defined (.pvV i)) hb
    (fun _ h => Option.noConfusion h) σ) hm

/-- A literal is defined, behind a context with no diamond. -/
theorem Proves.definedLit {p : PrimTy} {v : p.Denote} (hb : H.boxOnly = true := by first | rfl | decide)
    (hm : (H.wrap (.defined (.app0 (.lit v)))).modalFree = true := by first | rfl | decide) :
    Proves C R Γ₀ H (.defined (.app0 (.lit v))) :=
  .closeHolds (fun σ => H.wrap_valid (φ := .defined (.app0 (.lit v))) hb
    (fun _ h => Option.noConfusion h) σ) hm

/-- **`eqClose`** for any term: `t ≐ t`, behind a context with no diamond. -/
theorem Proves.eqRefl {p : PrimTy} {t : Tm C Γ (.val p)} (hb : H.boxOnly = true := by first | rfl | decide)
    (hm : (H.wrap (.eq t t)).modalFree = true := by first | rfl | decide) :
    Proves C R Γ₀ H (.eq t t) :=
  .closeHolds (fun σ => H.wrap_valid (φ := .eq t t) hb (fun _ => rfl) σ) hm

/-- **`eqClose`**: `v ≐ v`, behind a context with no diamond. -/
theorem Proves.eqClose {p : PrimTy} {v : p.Denote} (hb : H.boxOnly = true := by first | rfl | decide)
    (hm : (H.wrap (.eq (.app0 (.lit v)) (.app0 (.lit v)))).modalFree = true := by
      first | rfl | decide) :
    Proves C R Γ₀ H (.eq (.app0 (.lit v)) (.app0 (.lit v))) :=
  Proves.eqRefl hb hm

/-- **`eqDClose`**: `v = v` as a program comparison writes it (`Fml.eqD`),
behind a context with no diamond. -/
theorem Proves.eqDClose {p : PrimTy} {v : p.Denote} (hb : H.boxOnly = true := by first | rfl | decide)
    (hm : (H.wrap (Fml.eqD (.app0 (.lit v)) (.app0 (.lit v)))).modalFree = true := by
      first | rfl | decide) :
    Proves C R Γ₀ H (Fml.eqD (.app0 (.lit v)) (.app0 (.lit v))) :=
  .closeHolds (fun σ => H.wrap_valid (φ := Fml.eqD (.app0 (.lit v)) (.app0 (.lit v))) hb
    (fun _ => ⟨fun h => Option.noConfusion h, fun h => Option.noConfusion h, rfl⟩) σ) hm

/-- **`applyOnRigidFormula` under the box**: the last update applied to a
first-order goal and dropped (`Fml.substU`).  The goal reads no global part
where the update writes one: the update's right-hand sides are read in the
state before it, the goal's symbols would be read after. -/
theorem Proves.applyOnRigidBox {Δ : Ctx} {W : Upd C Γ Δ} {φ : Fml C Δ} {φ' : Fml C Γ}
    (hs : Fml.substU W φ = some φ') (h : Proves C R Γ₀ H φ')
    (hm : ((H.upd .box W).wrap φ).modalFree = true := by first | rfl | decide) :
    Proves C R Γ₀ (H.upd .box W) φ :=
  .closeHolds (fun σ => H.wrap_mono (φ := φ') (ψ := .upd .box W φ)
    (fun τ hτ => holds_upd_of_substU hs τ hτ) σ (Proves.sound h σ)) hm

/-- **`simplifyUpdate`** under the box: the elements of the last update that
set a local the update pops later are dropped (`Upd.simp`). -/
theorem Proves.simplify {Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ}
    (h : Proves C R Γ₀ (H.upd .box (U.simp 0)) φ)
    (hm : ((H.upd .box U).wrap φ).modalFree = true := by first | rfl | decide) :
    Proves C R Γ₀ (H.upd .box U) φ :=
  .closeHolds (fun σ => H.wrap_mono (φ := .upd .box (U.simp 0) φ) (ψ := .upd .box U φ)
    (fun τ hτ => holds_upd_simp τ hτ) σ (Proves.sound h σ)) hm

/-- `Proves.simplify`, the simplified update written out. -/
theorem Proves.simplify' {Δ : Ctx} {U U₂ : Upd C Γ Δ} {φ : Fml C Δ} (hs : U.simp 0 = U₂)
    (h : Proves C R Γ₀ (H.upd .box U₂) φ)
    (hm : ((H.upd .box U).wrap φ).modalFree = true := by first | rfl | decide) :
    Proves C R Γ₀ (H.upd .box U) φ :=
  Proves.simplify (hs ▸ h) hm

/-- `Proves.rewrite`, the rewritten context and goal written out. -/
theorem Proves.rewrite' {H' : Hyps C Γ₀ Γ} {φ φ' : Fml C Γ} {p : PrimTy}
    (q : Tm C [] (.val p) × Tm C [] (.val p)) (hq : Tm.Theq q.1 q.2)
    (hH : H.rwEqC q = H') (hs : φ.rwEqC q = φ') (h : Proves C R Γ₀ H' φ') : Proves C R Γ₀ H φ :=
  Proves.rewrite q hq (hH ▸ hs ▸ h)

/-- `Proves.updRw`, the rewritten update written out. -/
theorem Proves.updRw' {Δ : Ctx} {U U₂ : Upd C Γ Δ} {φ : Fml C Δ} {p : PrimTy}
    (q : Tm C [] (.val p) × Tm C [] (.val p)) (hq : Tm.EvalRefines q.1 q.2)
    (hs : U.rwC q = U₂) (h : Proves C R Γ₀ (H.upd .box U₂) φ) : Proves C R Γ₀ (H.upd .box U) φ :=
  Proves.updRw q hq (hs ▸ h)

end Rules

end Solidity
