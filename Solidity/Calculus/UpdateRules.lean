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
open Theory Theory.StValue
open Semantics (Value SVal)

variable {C : Contract}

/-! ## Symbols that read no global part, in the Theory -/

theorem _root_.Solidity.Op0.denote_globFree {s : Srt} {o : Op0 s} (h : o.globFree = true)
    (g g' : Semantics.State) : o.denote g = o.denote g' := by
  cases o <;> first | rfl | cases h

theorem _root_.Solidity.Op1.denote_globFree {a s : Srt} {o : Op1 a s} (h : o.globFree = true)
    (g g' : Semantics.State) (x : a.Den) : o.denote g x = o.denote g' x := by
  cases o <;> first | rfl | cases h

theorem _root_.Solidity.Op2.denote_globFree {a b s : Srt} {o : Op2 a b s} (h : o.globFree = true)
    (g g' : Semantics.State) (x : a.Ev) (y : b.Ev) (dx : a.Den) (dy : b.Den) :
    o.denote g x y dx dy = o.denote g' x y dx dy := by
  cases o <;> first | rfl | cases h

/-! ## A term read in the state before an update, in the Theory -/

section Denote

variable {Γ Δ : Ctx} {σ₀ : EState C Γ} {σ₁ : EState C Δ} {U : Upd C Γ Δ}

theorem Tm.denote_substH_pvV {p : PrimTy} {i : Idx Δ (.val p)} {t' : Tm C Γ .val} :
    (x : Held C Γ (.val p)) → Held.OK σ₀ σ₁ i x →
      (match x with | .pos j => some (Tm.pvV j) | .rhs (.val t) => some t) = some t' →
      t'.denote σ₀ = (Tm.pvV i).denote σ₁
  | .pos j, hok, h => by
    cases h
    have hok : Env.get i σ₁.env = Env.get j σ₀.env := hok
    show StValue.prim _ = StValue.prim _
    rw [hok]
  | .rhs (.val t), hok, h => by cases h; exact Tm.denote_eval σ₀ t' _ hok

theorem Tm.denote_substH_pvP {R : RefTy} {i : Idx Δ (.alias R)} {t' : Tm C Γ .path} :
    (x : Held C Γ (.alias R)) → Held.OK σ₀ σ₁ i x →
      (match x with
        | .pos j => some (Tm.pvP j) | .rhs (.path p) => some p | .rhs .unset => none) = some t' →
      t'.denote σ₀ = (Tm.pvP i).denote σ₁
  | .pos j, hok, h => by
    cases h
    have hok : Env.get i σ₁.env = Env.get j σ₀.env := hok
    simp only [Tm.denote, aliasPath, hok]
  | .rhs (.path p), hok, h => by
    cases h
    have hok : (do pure (some (← t'.eval σ₀))) = Except.ok (Env.get i σ₁.env) := hok
    cases hp : t'.eval σ₀ with
    | error e => rw [hp] at hok; cases hok
    | ok q =>
      rw [hp] at hok
      injection hok with hq
      show _ = (match aliasPath σ₁ i with | .ok (r, segs) => rootPath r segs | .error _ => [])
      unfold aliasPath
      rw [← hq]
      exact Tm.denote_eval σ₀ t' q.1 q.2 hp
  | .rhs .unset, _, h => by cases h

theorem Tm.denote_substH_pvS {g : Bool} {i : Idx Δ .old} {t' : Tm C Γ .st} :
    (x : Held C Γ .old) → Held.OK σ₀ σ₁ i x →
      (match x with | .pos j => if g then some (Tm.pvS j) else none | .rhs _ => none) = some t' →
      t'.denote σ₀ = (Tm.pvS i).denote σ₁
  | .pos j, hok, h => by
    cases g with
    | false => cases h
    | true =>
      cases h
      have hok : Env.get i σ₁.env = Env.get j σ₀.env := hok
      show SVal.abs.fields _ = SVal.abs.fields _
      rw [hok]
  | .rhs _, _, h => by cases h

/-- **A term read before an update denotes what it denotes after**, its
locals replaced by what the update leaves in them. -/
theorem Tm.denote_substH (hU : U.apply σ₀ = .ok σ₁) :
    {k : Srt} → (t : Tm C Δ k) → {t' : Tm C Γ k} → t.substH U.held U.envOnly none = some t' →
      t'.denote σ₀ = t.denote σ₁
  | _, .pvV i, _, h => Tm.denote_substH_pvV _ (Upd.held_ok U hU i) h
  | _, .pvP i, _, h => Tm.denote_substH_pvP _ (Upd.held_ok U hU i) h
  | _, .pvS i, _, h => Tm.denote_substH_pvS _ (Upd.held_ok U hU i) h
  | _, .pvI _, _, h => by
    simp only [Tm.substH] at h
    split at h <;> cases h <;> rfl
  | _, .netOf i a, t', h => by
    have hx := Upd.held_ok U hU i
    have h : (match U.held i with
        | .pos j => (a.substH U.held U.envOnly none).map (Tm.netOf j) | .rhs _ => none) = some t' := h
    generalize U.held i = x at h hx
    cases x with
    | rhs _ => cases h
    | pos j =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      have hx : Env.get i σ₁.env = Env.get j σ₀.env := hx
      simp only [Tm.denote]
      rw [Tm.denote_substH hU a ha, hx]
  | _, .app0 o, t', h => by
    simp only [Tm.substH] at h
    split at h
    · rename_i hc
      cases h
      show o.denote σ₀.glob = o.denote σ₁.glob
      rcases Bool.or_eq_true _ _ ▸ hc with hg | hg
      · rw [Upd.envOnly_glob U hg hU]
      · exact Op0.denote_globFree hg _ _
    · revert h
      cases o <;> exact fun h => Option.noConfusion h
  | _, .app1 o ho x, t', h => by
    simp only [Tm.substH] at h
    split at h
    · rename_i hc
      obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
      show o.denote σ₀.glob (x'.denote σ₀) = o.denote σ₁.glob (x.denote σ₁)
      rw [Tm.denote_substH hU x hx]
      rcases Bool.or_eq_true _ _ ▸ hc with hg | hg
      · rw [Upd.envOnly_glob U hg hU]
      · exact Op1.denote_globFree hg _ _ _
    · cases h
  | _, .app2 o x y, t', h => by
    simp only [Tm.substH] at h
    split at h
    · rename_i hc
      obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      have hst : ∀ z, (none : Option (Tm C Γ .st)) = some z → z.eval σ₀ = pure σ₁.glob :=
        fun _ h => Option.noConfusion h
      show o.denote σ₀.glob (x'.eval σ₀) (y'.eval σ₀) (x'.denote σ₀) (y'.denote σ₀) =
        o.denote σ₁.glob (x.eval σ₁) (y.eval σ₁) (x.denote σ₁) (y.denote σ₁)
      rw [Tm.denote_substH hU x hx, Tm.denote_substH hU y hy, Tm.eval_substH hU hst x hx,
        Tm.eval_substH hU hst y hy]
      rcases Bool.or_eq_true _ _ ▸ hc with hg | hg
      · rw [Upd.envOnly_glob U hg hU]
      · exact Op2.denote_globFree hg _ _ _ _ _ _
    · cases h
  | _, .app3 o x y z, t', h => by
    simp only [Tm.substH] at h
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z', hz, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show o.denote (x'.denote σ₀) (y'.denote σ₀) (z'.denote σ₀) =
      o.denote (x.denote σ₁) (y.denote σ₁) (z.denote σ₁)
    rw [Tm.denote_substH hU x hx, Tm.denote_substH hU y hy, Tm.denote_substH hU z hz]

end Denote

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

/-- **A goal read before an update holds after it.** -/
theorem Fml.substU_holds {Γ Δ : Ctx} {U : Upd C Γ Δ} {σ₀ : EState C Γ} {σ₁ : EState C Δ}
    (hU : U.apply σ₀ = .ok σ₁) : (φ : Fml C Δ) → {φ' : Fml C Γ} → Fml.substU U φ = some φ' →
      ∀ (σ : State C Γ) (σ' : State C Δ), σ.erase = σ₀ → σ'.erase = σ₁ →
        (holds σ φ' ↔ holds σ' φ)
  | .tt, _, h, _, _, _, _ => by cases h; exact Iff.rfl
  | .eq a b, _, h, σ, σ', e, e' => by
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show Equiv (a'.denote σ.erase) (b'.denote σ.erase) ↔ Equiv (a.denote σ'.erase) (b.denote σ'.erase)
    rw [e, e', Tm.denote_substH hU a ha, Tm.denote_substH hU b hb]
  | .defined t, _, h, σ, σ', e, e' => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h
    show (∃ x, t'.eval σ.erase = .ok x) ↔ (∃ x, t.eval σ'.erase = .ok x)
    rw [e, e', Tm.eval_substH hU (st := none) (fun _ h => Option.noConfusion h) t ht]
  | .not φ, _, h, σ, σ', e, e' => by
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact not_congr (Fml.substU_holds hU φ hφ σ σ' e e')
  | .and φ ψ, _, h, σ, σ', e, e' => by
    obtain ⟨φ', hφ, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ψ', hψ, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact and_congr (Fml.substU_holds hU φ hφ σ σ' e e') (Fml.substU_holds hU ψ hψ σ σ' e e')
  | .imp φ ψ, _, h, σ, σ', e, e' => by
    obtain ⟨φ', hφ, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ψ', hψ, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact imp_congr (Fml.substU_holds hU φ hφ σ σ' e e') (Fml.substU_holds hU ψ hψ σ σ' e e')
  | .upd .., _, h, _, _, _, _ | .modal .., _, h, _, _, _, _ | .havoc _, _, h, _, _, _, _
  | .all .., _, h, _, _, _, _ | .bind .., _, h, _, _, _, _ | .anon .., _, h, _, _, _, _ => by
    cases h

/-- Under the box, the goal applied gives the update in front of the goal. -/
theorem holds_upd_of_substU {Γ Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ} {φ' : Fml C Γ}
    (hs : Fml.substU U φ = some φ') (σ : State C Γ) (h : holds σ φ') :
    holds σ (.upd .box U φ) := by
  rw [holds_upd_erased]
  show Modality.afterC .box _ (U.apply σ.erase)
  cases hU : U.apply σ.erase with
  | error => trivial
  | ok σ₁ => exact fun σ' e _ => (Fml.substU_holds hU φ hs σ σ' rfl e).1 h


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

/-- Two states alike but in their `n` top locals. -/
def EState.AgreeAbove {Δ : Ctx} (n : Nat) (τ τ' : EState C Δ) : Prop :=
  τ' = τ.withEnv τ'.env ∧ ∀ {t : LTy} (i : Idx Δ t), n ≤ i.toNat → Env.get i τ.env = Env.get i τ'.env

theorem EState.AgreeAbove.refl {Δ : Ctx} (n : Nat) (τ : EState C Δ) : EState.AgreeAbove n τ τ :=
  ⟨rfl, fun _ _ => rfl⟩

theorem EState.AgreeAbove.eq {Δ : Ctx} {τ τ' : EState C Δ} (h : EState.AgreeAbove 0 τ τ') : τ' = τ := by
  obtain ⟨h₁, h₂⟩ := h
  rw [h₁, Env.ext_get τ'.env τ.env fun i => (h₂ i (Nat.zero_le _)).symm]
  rfl

theorem Idx.toNat_ext {Γ : Ctx} {t : LTy} (j : Idx Γ t) : {Δ : Ctx} → (h : Ext Γ Δ) →
    (j.ext h).toNat = j.toNat + h.depth
  | _, .refl => rfl
  | _, .push h => by
    show (j.ext h).toNat + 1 = j.toNat + (h.depth + 1)
    rw [Idx.toNat_ext j h, Nat.add_assoc]

theorem Res.map_bind_ok {α β γ : Type} (x : Semantics.Res α) (f : α → Semantics.Res β) (g : β → γ) :
    (x >>= f).map g = x >>= fun a => (f a).map g := by
  cases x <;> rfl

/-- An element that sets no local reads the locals of the state it writes
into not at all. -/
theorem UpdElem.write_withEnv {Γ Δ : Ctx} (σ₀ : EState C Γ) (e : UpdElem C Γ Δ)
    (he : ∀ {t} (i : Idx Δ t) (r : Rhs C Γ t), e ≠ .local i r) (τ : EState C Δ) (e' : Env C Δ) :
    e.write σ₀ (τ.withEnv e') = (e.write σ₀ τ).map (·.withEnv e') := by
  cases e with
  | «local» i r => exact absurd rfl (he i r)
  | storage x => simp only [UpdElem.write, Res.map_bind_ok]; rfl
  | memory x => simp only [UpdElem.write, Res.map_bind_ok]; rfl
  | selfBalance op a => simp only [UpdElem.write, Res.map_bind_ok]; rfl
  | net r op a => simp only [UpdElem.write, Res.map_bind_ok]; rfl
  | pay r a =>
    simp only [UpdElem.write, Res.map_bind_ok]
    congr; funext; congr; funext; congr; funext; congr; funext amt
    split <;> rfl
  | netMt r a => simp only [UpdElem.write, Res.map_bind_ok]; rfl
  | setBalance a => simp only [UpdElem.write, Res.map_bind_ok]; rfl

/-- An element that sets no local, written into two states alike above
`n`, leaves two states alike above `n`. -/
theorem Upd.simp_snoc_other {Γ Δ : Ctx} (σ₀ : EState C Γ) {n : Nat} {U U' : Upd C Γ Δ}
    {e : UpdElem C Γ Δ} {τ τ₀ τ₀' : EState C Δ} (_ : U.apply σ₀ = .ok τ₀)
    (h₀' : U'.apply σ₀ = .ok τ₀') (hw : τ₀' = τ₀.withEnv τ₀'.env)
    (hag : ∀ {t : LTy} (i : Idx Δ t), n ≤ i.toNat → Env.get i τ₀.env = Env.get i τ₀'.env)
    (he : ∀ {t} (i : Idx Δ t) (r : Rhs C Γ t), e ≠ .local i r) (h : e.write σ₀ τ₀ = .ok τ) :
    ∃ τ', (Upd.snoc U' e).apply σ₀ = .ok τ' ∧ EState.AgreeAbove n τ τ' := by
  have hτ : τ = τ.withEnv τ₀.env := by
    have := UpdElem.write_withEnv σ₀ e he τ₀ τ₀.env
    rw [show τ₀.withEnv τ₀.env = τ₀ from rfl, h] at this
    exact Except.ok.inj this
  refine ⟨τ.withEnv τ₀'.env, ?_, rfl, fun j _ => ?_⟩
  · show (do e.write σ₀ (← U'.apply σ₀)) = _
    rw [h₀']
    show e.write σ₀ τ₀' = _
    have : e.write σ₀ (τ₀.withEnv τ₀'.env) = .ok (τ.withEnv τ₀'.env) := by
      rw [UpdElem.write_withEnv σ₀ e he τ₀ τ₀'.env, h]; rfl
    rwa [← hw] at this
  · rw [hτ]; exact hag j ‹_›

/-- **Where an update returns, so does the update with what it pops
dropped**, to a state alike but in its `n` top locals. -/
theorem Upd.simp_apply {Γ : Ctx} (σ₀ : EState C Γ) : {Δ : Ctx} → (n : Nat) → (U : Upd C Γ Δ) →
    ∀ τ, U.apply σ₀ = .ok τ → ∃ τ', (U.simp n).apply σ₀ = .ok τ' ∧ EState.AgreeAbove n τ τ'
  | _, _, .nil, τ, h => ⟨τ, h, EState.AgreeAbove.refl _ _⟩
  | _, n, .snoc U e, τ, h => by
    obtain ⟨τ₀, hτ₀, h⟩ := Semantics.bind_ok_inv h
    obtain ⟨τ₀', h₀', ⟨hw, hag⟩⟩ := Upd.simp_apply σ₀ n U τ₀ hτ₀
    cases e with
    | «local» i r =>
      obtain ⟨v, hv, h⟩ := Semantics.bind_ok_inv h
      cases h
      simp only [Upd.simp]
      split
      · rename_i hi
        refine ⟨τ₀', h₀', ?_, fun j hj => ?_⟩
        · rw [hw]; rfl
        · show Env.get j (Env.set i v τ₀.env) = _
          rw [Env.get_set_other i j (by omega), hag j hj]
      · refine ⟨τ₀'.setLocal i v, ?_, ?_, fun j hj => ?_⟩
        · show (do (UpdElem.local i r).write σ₀ (← (U.simp n).apply σ₀)) = _
          rw [h₀']
          show (do pure (τ₀'.setLocal i (← r.eval σ₀))) = _
          rw [hv]; rfl
        · rw [hw]; rfl
        · show Env.get j (Env.set i v τ₀.env) = Env.get j (Env.set i v τ₀'.env)
          by_cases hij : i.toNat = j.toNat
          · obtain rfl := Idx.ty_eq_of_toNat hij
            obtain rfl := Idx.toNat_inj i j hij
            rw [Env.get_set, Env.get_set]
          · rw [Env.get_set_other i j hij, Env.get_set_other i j hij, hag j hj]
    | _ => exact Upd.simp_snoc_other σ₀ hτ₀ h₀' hw hag (fun _ _ h => UpdElem.noConfusion h) h
  | _, n, .decl U x r, τ, h => by
    obtain ⟨τ₀, hτ₀, h⟩ := Semantics.bind_ok_inv h
    obtain ⟨v, hv, h⟩ := Semantics.bind_ok_inv h
    cases h
    obtain ⟨τ₀', h₀', ⟨hw, hag⟩⟩ := Upd.simp_apply σ₀ (n - 1) U τ₀ hτ₀
    refine ⟨τ₀'.push v, ?_, ?_, fun j hj => ?_⟩
    · show (do let τ ← (U.simp (n - 1)).apply σ₀; pure (τ.push (← r.eval σ₀))) = _
      rw [h₀', hv]; rfl
    · rw [hw]; rfl
    · cases j with
      | here => rfl
      | there j => exact hag j (by simp only [Idx.toNat] at hj; omega)
  | _, n, .pop U e, τ, h => by
    cases hτ₀ : U.apply σ₀ with
    | error => rw [Upd.apply, hτ₀] at h; cases h
    | ok τ₀ =>
      rw [Upd.apply, hτ₀] at h; cases h
      obtain ⟨τ₀', h₀', ⟨hw, hag⟩⟩ := Upd.simp_apply σ₀ (n + e.depth) U τ₀ hτ₀
      refine ⟨τ₀'.drop e, ?_, ?_, fun j hj => ?_⟩
      · show ((U.simp (n + e.depth)).apply σ₀).map (EState.drop e) = _
        rw [h₀']; rfl
      · rw [hw]; rfl
      · show Env.get j (Env.drop e τ₀.env) = Env.get j (Env.drop e τ₀'.env)
        rw [Env.get_drop, Env.get_drop]
        exact hag _ (by rw [Idx.toNat_ext]; omega)
  | _, _, .drop U e, τ, h => by
    cases hτ₀ : U.apply σ₀ with
    | error => rw [Upd.apply, hτ₀] at h; cases h
    | ok τ₀ =>
      rw [Upd.apply, hτ₀] at h; cases h
      obtain ⟨τ₀', h₀', hag⟩ := Upd.simp_apply σ₀ 0 U τ₀ hτ₀
      rw [hag.eq] at h₀'
      refine ⟨τ₀.thin e, ?_, EState.AgreeAbove.refl _ _⟩
      show ((U.simp 0).apply σ₀).map (EState.thin e) = _
      rw [h₀']; rfl

/-- Under the box, an update with what it pops dropped gives the update. -/
theorem holds_upd_simp {Γ Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ} (σ : State C Γ)
    (h : holds σ (.upd .box (U.simp 0) φ)) : holds σ (.upd .box U φ) := by
  rw [holds_upd_erased]
  show Modality.afterC .box _ (U.apply σ.erase)
  have h : Modality.afterC .box _ ((U.simp 0).apply σ.erase) := (holds_upd_erased _ _ _ _).1 h
  cases hU : U.apply σ.erase with
  | error => trivial
  | ok τ =>
    obtain ⟨τ', h', hag⟩ := Upd.simp_apply σ.erase 0 U τ hU
    rw [h', hag.eq] at h
    exact h

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
theorem Proves.eqDSplit {a b : Tm C Γ .val} (ha : Proves C R Γ₀ H (.defined a))
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
  .closeHolds (fun σ => H.wrap_valid (φ := .defined (.pvV i)) hb (fun _ => ⟨_, rfl⟩) σ) hm

/-- A literal is defined, behind a context with no diamond. -/
theorem Proves.definedLit {v : Value} (hb : H.boxOnly = true := by first | rfl | decide)
    (hm : (H.wrap (.defined (.app0 (.lit v)))).modalFree = true := by first | rfl | decide) :
    Proves C R Γ₀ H (.defined (.app0 (.lit v))) :=
  .closeHolds (fun σ => H.wrap_valid (φ := .defined (.app0 (.lit v))) hb (fun _ => ⟨v, rfl⟩) σ) hm

/-- **`eqClose`** for any term: `t ≐ t`, behind a context with no diamond. -/
theorem Proves.eqRefl {t : Tm C Γ .val} (hb : H.boxOnly = true := by first | rfl | decide)
    (hm : (H.wrap (.eq t t)).modalFree = true := by first | rfl | decide) :
    Proves C R Γ₀ H (.eq t t) :=
  .closeHolds (fun σ => H.wrap_valid (φ := .eq t t) hb (fun _ => Equiv.refl _) σ) hm

/-- **`eqClose`**: `v ≐ v`, behind a context with no diamond. -/
theorem Proves.eqClose {v : Value} (hb : H.boxOnly = true := by first | rfl | decide)
    (hm : (H.wrap (.eq (.app0 (.lit v)) (.app0 (.lit v)))).modalFree = true := by
      first | rfl | decide) :
    Proves C R Γ₀ H (.eq (.app0 (.lit v)) (.app0 (.lit v))) :=
  Proves.eqRefl hb hm

/-- **`eqDClose`**: `v = v` as a program comparison writes it (`Fml.eqD`),
behind a context with no diamond. -/
theorem Proves.eqDClose {v : Value} (hb : H.boxOnly = true := by first | rfl | decide)
    (hm : (H.wrap (Fml.eqD (.app0 (.lit v)) (.app0 (.lit v)))).modalFree = true := by
      first | rfl | decide) :
    Proves C R Γ₀ H (Fml.eqD (.app0 (.lit v)) (.app0 (.lit v))) :=
  .closeHolds (fun σ => H.wrap_valid (φ := Fml.eqD (.app0 (.lit v)) (.app0 (.lit v))) hb
    (fun _ => ⟨⟨v, rfl⟩, ⟨v, rfl⟩, Equiv.refl _⟩) σ) hm

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
theorem Proves.rewrite' {H' : Hyps C Γ₀ Γ} {φ φ' : Fml C Γ}
    (q : Tm C [] .val × Tm C [] .val) (hq : Tm.Theq q.1 q.2)
    (hH : H.rwEqC q = H') (hs : φ.rwEqC q = φ') (h : Proves C R Γ₀ H' φ') : Proves C R Γ₀ H φ :=
  Proves.rewrite q hq (hH ▸ hs ▸ h)

/-- `Proves.updRw`, the rewritten update written out. -/
theorem Proves.updRw' {Δ : Ctx} {U U₂ : Upd C Γ Δ} {φ : Fml C Δ}
    (q : Tm C [] .val × Tm C [] .val) (hq : Tm.EvalRefines q.1 q.2)
    (hs : U.rwC q = U₂) (h : Proves C R Γ₀ (H.upd .box U₂) φ) : Proves C R Γ₀ (H.upd .box U) φ :=
  Proves.updRw q hq (hs ▸ h)

end Rules

end Solidity
