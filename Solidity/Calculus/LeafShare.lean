import Solidity.Calculus.TermWk
import Solidity.Calculus.Logic
import Solidity.Calculus.CallSummary

/-!
# A leaf's values shared

A call's summary (`internalCallSummary`, `Calculus/CallSummary.lean`) is
one update whose term substitutes each callee's term at its call: in the
family `f₀(x) = x * 3`, `fₖ(x) = fₖ₋₁(fₖ₋₁(x))`, `{ y := a * 3 * … * 3 }`
with `2^k` products, one per call site.  The term is linear in the call
sites; reading it whole is not: the closer's evaluation reads the whole
update at once, each product's range check nested in the one before it
(`docs/automation.md`, M6).

Here the term is read one value at a time, each a fresh local with its
defining fact, KeY's contract applied once per call site: `{ y := C[s] }`
is `{ z := s } { y := C[z] ‖ pop }`, `s` the innermost strict redex of the
term (`Tm.redex?`: a symbol applied to locals and nullary symbols, reached
through operands that are always read, `Op2.strictB`), `z` popped after.
Where `s` does not return, neither does `C[s]`, so the two fail alike
(`holds_upd_share`); where it does, `C[z]` reads what `C[s]` read.  So
`{ y := a * 3 * 3 }` is `{ z := a * 3 } { y := z * 3 ‖ pop }`, and a leaf
of `n` call sites is `n` updates of one product each, which `sol_close`'s
steps read in turn (`CloseJ.shareStep`, `CloseJ.peel`,
`Calculus/CloseScoped/Steps.lean`).  Lean only: solkey applies a contract
at a call, it has no summaries to split.

Nothing here is trusted by the closer: each split is an `apply` of
`holds_upd_share`, its redex equation `rfl` and its `pushFree` conditions
`rfl`, which the kernel checks.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3)

variable {C : Contract}

/-! ## Strict operands -/

/-- A strict operator never short-circuits: `x * y` reads `y` whatever `x`
is (`&&` and `||` are the lazy ones). -/
theorem BinOp.shortT_of_lazyB {op : BinOp} (h : op.lazyB = false) {p : PrimTy} (a : p.Denote) :
    op.shortT a = none := by
  cases op <;> first | (cases p <;> rfl) | (simp only [BinOp.lazyB, Bool.true_eq_false] at h)

/-- **A strict symbol reverts where an operand does**: `x * 3` where `x`
overflows. -/
theorem Op2.eval_none_of_strictB (g : State C []) {a b s : Srt} {o : Op2 C a b s}
    (ho : o.strictB = true) (x : Option (a.Den C g.H)) (y : Option (b.Den C g.H))
    (h : x = none ∨ y = none) : o.eval g x y = none := by
  cases o with
  | binop op hop =>
    have hl : op.lazyB = false := by simpa only [Op2.strictB, Bool.not_eq_true'] using ho
    show x.bind (fun a => binopT op hop a y) = none
    rcases h with rfl | rfl
    · rfl
    · cases x with
      | none => rfl
      | some a =>
        show binopT op hop a none = none
        unfold binopT
        rw [BinOp.shortT_of_lazyB hl]
        rfl
  | _ => exact absurd ho Bool.false_ne_true

/-! ## The innermost redex -/

section Redex

variable {Γ : Ctx}

/-- A term read at once: a local or a nullary symbol (a literal, a root). -/
def Tm.leafB {s : Srt} : Tm C Γ s → Bool
  | .pvV _ => true
  | .app0 _ => true
  | _ => false

/-- The term itself as the redex, where it is a value: read from the fresh
local on top. -/
def Tm.self? : {s : Srt} → Tm C Γ s →
    Option ((q : PrimTy) × Tm C Γ (.val q) × Tm C (.val q :: Γ) s)
  | .val _, t => some ⟨_, t, .pvV .here⟩
  | _, _ => none

/-- **The innermost strict redex of a term**: a binary symbol applied to two
leaves (`Tm.leafB`), reached through operands always read (`Op2.strictB`),
the left one first; the redex and the term reading it from a fresh local on
top, every other local moved past it.  `x * 3 * 3` gives `x * 3` and
`z * 3`. -/
def Tm.redex? : {s : Srt} → Tm C Γ s →
    Option ((q : PrimTy) × Tm C Γ (.val q) × Tm C (.val q :: Γ) s)
  | _, .app2 o x y =>
    if o.strictB then
      match x.redex? with
      | some ⟨q, r, x'⟩ => some ⟨q, r, .app2 o x' (y.wk (.drop .refl))⟩
      | none => match y.redex? with
        | some ⟨q, r, y'⟩ => some ⟨q, r, .app2 o (x.wk (.drop .refl)) y'⟩
        | none => if x.leafB && y.leafB then (Tm.app2 o x y).self? else none
    else none
  | _, _ => none

/-- A term weakened past a pushed local reads as before: `x * 3` under a
fresh `uint z` is `x * 3`. -/
theorem Tm.eval_wk_push {t : LTy} (σ : State C Γ) (u : t.TDenote C σ.H) {s : Srt}
    (x : Tm C Γ s) : (x.wk (.drop .refl)).eval (σ.push u) = x.eval σ := by
  rw [Tm.eval_wk]
  cases σ
  rfl

/-- **The term as its own redex** (`Tm.self?`): `x * 3` read from a local
holding its value. -/
theorem Tm.self?_spec {s : Srt} {t : Tm C Γ s} {q : PrimTy} {r : Tm C Γ (.val q)}
    {t' : Tm C (.val q :: Γ) s} (h : t.self? = some ⟨q, r, t'⟩) (σ : State C Γ) :
    (r.eval σ = none → t.eval σ = none) ∧
      ∀ u, r.eval σ = some u →
        t'.eval (σ.push (t := .val q) (show (LTy.val q).TDenote C σ.H from u)) = t.eval σ := by
  cases s with
  | val p =>
    cases h
    exact ⟨id, fun u hu => hu.symm⟩
  | _ => cases h

/-- **The redex reads as the term**: where the redex does not return, the
term does not; where it returns `u`, the term with the redex read from a
local holding `u` reads what the term reads. -/
theorem Tm.redex?_spec : {s : Srt} → (t : Tm C Γ s) → {q : PrimTy} → {r : Tm C Γ (.val q)} →
    {t' : Tm C (.val q :: Γ) s} → t.redex? = some ⟨q, r, t'⟩ → (σ : State C Γ) →
    (r.eval σ = none → t.eval σ = none) ∧
      ∀ u, r.eval σ = some u →
        t'.eval (σ.push (t := .val q) (show (LTy.val q).TDenote C σ.H from u)) = t.eval σ
  | _, .app2 o x y, q, r, t', h, σ => by
    unfold Tm.redex? at h
    split at h
    · rename_i ho
      split at h
      · rename_i q₁ r₁ x' hx
        cases h
        obtain ⟨h₁, h₂⟩ := Tm.redex?_spec x hx σ
        refine ⟨fun hr => ?_, fun u hu => ?_⟩
        · show o.eval σ.glob (x.eval σ) (y.eval σ) = none
          exact Op2.eval_none_of_strictB σ.glob ho _ _ (.inl (h₁ hr))
        · show o.eval σ.glob (x'.eval (σ.push (t := .val q) u))
              ((y.wk (.drop .refl)).eval (σ.push (t := .val q) u)) =
            o.eval σ.glob (x.eval σ) (y.eval σ)
          rw [h₂ u hu, Tm.eval_wk_push]
      · rename_i hx
        split at h
        · rename_i q₁ r₁ y' hy
          cases h
          obtain ⟨h₁, h₂⟩ := Tm.redex?_spec y hy σ
          refine ⟨fun hr => ?_, fun u hu => ?_⟩
          · show o.eval σ.glob (x.eval σ) (y.eval σ) = none
            exact Op2.eval_none_of_strictB σ.glob ho _ _ (.inr (h₁ hr))
          · show o.eval σ.glob ((x.wk (.drop .refl)).eval (σ.push (t := .val q) u))
                (y'.eval (σ.push (t := .val q) u)) =
              o.eval σ.glob (x.eval σ) (y.eval σ)
            rw [h₂ u hu, Tm.eval_wk_push]
        · split at h
          · exact Tm.self?_spec h σ
          · cases h
    · cases h
  | _, .pvV _, _, _, _, h, _ | _, .pvP _, _, _, _, h, _ | _, .pvS _, _, _, _, h, _
  | _, .pvI _, _, _, _, h, _ | _, .netOf _ _, _, _, _, h, _ | _, .app0 _, _, _, _, h, _
  | _, .app1 _ _, _, _, _, h, _ | _, .app3 _ _ _ _, _, _, _, h, _ | _, .pvZ _, _, _, _, h, _ =>
    nomatch h

end Redex

/-! ## An update's value shared -/

section Share

variable {Γ : Ctx}

/-- `{ y := t ‖ pop }` read as itself with nothing popped. -/
theorem holds_upd_pop_refl {Δ : Ctx} {m : Modality} (U : Upd C Γ Δ) (φ : Fml C Δ)
    (σ : State C Γ) (h : holds σ (.upd m (U.pop .refl) φ)) : holds σ (.upd m U φ) := by
  have e : (U.pop .refl).applyV σ = U.applyV σ := by
    show (U.applyV σ).bind (fun p => some (p.1, p.2.drop .refl)) = _
    cases U.applyV σ <;> rfl
  have hx : (U.pop .refl).exh σ = U.exh σ := rfl
  change Upd.afterT m σ _ _ at h
  change Upd.afterT m σ _ _
  rw [Upd.afterT_applyV] at h ⊢
  rw [e, hx] at h
  exact h

/-- **A value shared** (KeY's contract applied once per call site):
`{ y := t ‖ pop }` holds where `{ z := r } { y := t' ‖ pop }` does, `r` a
redex of `t` (`Tm.redex?`) and `t'` reading it from `z`; the two halt
alike.  `{ y := a * 3 * 3 }` from `{ z := a * 3 } { y := z * 3 }`. -/
theorem holds_upd_share {Γ' : Ctx} {m : Modality} {p q : PrimTy} (z : Var)
    (j : Idx Γ (.val p)) (h : Ext Γ' Γ) (t : Tm C Γ (.val p)) (r : Tm C Γ (.val q))
    (t' : Tm C (.val q :: Γ) (.val p)) (ht : t.redex? = some ⟨q, r, t'⟩)
    (hU₁ : ((Upd.nil : Upd C Γ Γ).decl z (.val r)).pushFree = true)
    (hU₂ : (((Upd.nil : Upd C (.val q :: Γ) (.val q :: Γ)).snoc
      (.local (.there j) (.val t'))).pop (.push h)).pushFree = true)
    (φ : Fml C Γ') (σ : State C Γ)
    (hh : holds σ (.upd m ((Upd.nil : Upd C Γ Γ).decl z (.val r))
      (.upd m (((Upd.nil : Upd C (.val q :: Γ) (.val q :: Γ)).snoc
        (.local (.there j) (.val t'))).pop (.push h)) φ))) :
    holds σ (.upd m (((Upd.nil : Upd C Γ Γ).snoc (.local j (.val t))).pop h) φ) := by
  have hs := Tm.redex?_spec t ht
  change Upd.afterT m σ _ (fun τ => Upd.afterT m τ _ (holds · φ)) at hh
  change Upd.afterT m σ _ (holds · φ)
  rw [Upd.afterT_applyV] at hh ⊢
  have e₁ : ((Upd.nil : Upd C Γ Γ).decl z (.val r)).applyV σ =
      (r.eval σ).bind fun u => some (σ.globG, σ.locV.push u) := rfl
  have eW : (((Upd.nil : Upd C Γ Γ).snoc (.local j (.val t))).pop h).applyV σ =
      (t.eval σ).bind fun v => some (σ.globG, (σ.locV.set j v).drop h) := by
    show (((t.eval σ).bind fun v => some (σ.globG, σ.locV.set j v))).bind
      (fun p => some (p.1, p.2.drop h)) = _
    cases t.eval σ <;> rfl
  rw [e₁] at hh
  rw [eW]
  cases hr : r.eval σ with
  | none =>
    rw [(hs σ).1 hr]
    rw [hr] at hh
    rcases hh with hh | hh
    · exact .inl hh
    · rw [Upd.exh_of_pushFree hU₁] at hh; cases hh
  | some u =>
    rw [hr] at hh
    have hτ := hh (σ.push (t := .val q) u) rfl (fun i => by
      show (σ.push (t := .val q) u).locV _ i = _
      rw [State.locV_push]; rfl)
    rw [Upd.afterT_applyV] at hτ
    have e₂ : (((Upd.nil : Upd C (.val q :: Γ) (.val q :: Γ)).snoc
        (.local (.there j) (.val t'))).pop (.push h)).applyV (σ.push (t := .val q) u) =
        (t'.eval (σ.push (t := .val q) u)).bind fun v =>
          some ((σ.push (t := .val q) u).globG,
            (((σ.push (t := .val q) u).locV.set (.there j) v).drop (.push h))) := by
      show ((((t'.eval (σ.push (t := .val q) u)).bind fun v =>
          some ((σ.push (t := .val q) u).globG,
            (σ.push (t := .val q) u).locV.set (.there j) v))).bind
        (fun p => some (p.1, p.2.drop (.push h)))) = _
      cases t'.eval (σ.push (t := .val q) u) <;> rfl
    rw [e₂, (hs σ).2 u hr] at hτ
    cases hv : t.eval σ with
    | none =>
      rw [hv] at hτ
      rcases hτ with hτ | hτ
      · exact .inl hτ
      · rw [Upd.exh_of_pushFree hU₂] at hτ; cases hτ
    | some v =>
      rw [hv] at hτ
      intro σ' hg hl
      refine hτ σ' hg fun {t'} i => ?_
      rw [hl i]
      show σ.locV.set j v t' (i.ext h) =
        (σ.push (t := .val q) u).locV.set (.there j) v t' ((i.ext h).there)
      by_cases hj : j.toNat = (i.ext h).toNat
      · obtain rfl := Idx.ty_eq_of_toNat hj
        obtain rfl := Idx.toNat_inj j (i.ext h) hj
        rw [LocsV.set_same, LocsV.set_same]
      · rw [LocsV.set_ne _ _ _ hj, LocsV.set_ne _ _ _ (by
          show j.toNat + 1 ≠ (i.ext h).toNat + 1
          omega)]
        rfl

end Share

/-- info: 'Solidity.holds_upd_share' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms holds_upd_share

end Solidity
