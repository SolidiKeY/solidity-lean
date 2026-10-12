import Solidity.Calculus.RewritePast
import Solidity.Calculus.TermLaws
import Solidity.Calculus.NotationResolve
import Solidity.Calculus.Quote

/-!
# A law in an update's right-hand sides, under any modality

KeY's `updRw` past the program, on the scoped line: a law `t ⇝ t'` read in
an update's right-hand sides under either modality, where the update itself
holds the write the law reads back.  `{ storage := save(storage, p, 10) ‖
x := find(save(storage, p, 10), p) }` halts exactly where
`save(storage, p, 10)` does, and so does `{ storage := save(storage, p, 10)
‖ x := 10 }`: the read returns wherever the write it reads back does, and
the write is an element of the update.

**The law is solkey's taclet** (`Calculus/TermLaws.lean`): a term taclet
(`TermTaclet`), a law of a memory read (`EvalLaw`), with what makes it
exact in an update (`LawCov`: `Upd.covers`, `Upd.coversRef`,
`Tm.sameBase`, `Upd.coversEval`), all on the scoped terms.

**The rewrite.**  The law's two sides are scoped terms at one sort and at
the update's scope (`LawPair`), the instance found on the scoped line;
every occurrence of the left side in an update's right-hand sides becomes
the right side (`Tm.rwG`, `Upd.rwG`: `Calculus/SeqRewrite.lean`'s one
traversal, `Upd.rwBy`, at `LawPair.pick`; any sort: a memory law rewrites
an identity too).

**Why it holds.**  The right side returns what the left side returns
(`LawPair.Refines`), so where the update lands its rewrite lands
(`Upd.rwBy_lands`).  Where the rewritten update returns, the law refines
back there (`LawCov.back`), so the update returns the same global part
(`Upd.rwBy_globT_rev`) and halts only where the rewrite does
(`holds_upd_rwG`).  `LawCov.back` (`Calculus/TermLaws.lean`) states the
update's return by its erased run; the one bridge to it is
`Upd.apply_glob`, in `FmlRw.lawUpdS`.

These functions run once a link and use `match` on the indexed families,
under the exemption of `Calculus/RewriteScoped.lean`'s walks (proposal 104).
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)
open Semantics (Res)

variable {C : Contract}

/-! ## A law's two sides, at any sort -/

/-- A law's two sides: terms at one sort, at the scope `Γ`. -/
structure LawPair (C : Contract) (Γ : Ctx) where
  {k : Srt}
  lhs : Tm C Γ k
  rhs : Tm C Γ k

/-- The right side at the sort `s`, where it is the law's. -/
def LawPair.rhsAt? {Γ : Ctx} (q : LawPair C Γ) (s : Srt) : Option (Tm C Γ s) :=
  if h : q.k = s then some (h ▸ q.rhs) else none

/-- The right side returns what the left side returns, in every typed
state. -/
def LawPair.Refines {Γ : Ctx} (q : LawPair C Γ) : Prop :=
  ∀ σ : State C Γ, Srt.Le q.k (q.lhs.evalT σ) (q.rhs.evalT σ)

/-- A law that refines in every erased state refines in every typed one. -/
theorem LawPair.Refines.of_at {Γ : Ctx} {q : LawPair C Γ} (h : Tm.EvalRefinesAt q.lhs q.rhs) :
    q.Refines := fun σ => by
  rw [Tm.evalT_eq, Tm.evalT_eq]
  exact h σ.erase

section Rw

variable {Γ : Ctx} (q : LawPair C Γ)

/-- The law's right side for `t`, where `t` reads its left side. -/
def LawPair.pick {s : Srt} (t : Tm C Γ s) : Option (Tm C Γ s) :=
  if t.beqR q.lhs then q.rhsAt? s else none

/-- Every occurrence of the law's left side in a term, replaced by its
right side. -/
abbrev Tm.rwG {s : Srt} (t : Tm C Γ s) : Tm C Γ s := Tm.rwBy q.pick t

/-- An update's right-hand sides rewritten. -/
abbrev Upd.rwG {Δ : Ctx} (U : Upd C Γ Δ) : Upd C Γ Δ := Upd.rwBy q.pick U

/-- Whether `Upd.rwG` rewrites something. -/
abbrev Upd.hasG {Δ : Ctx} (U : Upd C Γ Δ) : Bool := Upd.hasBy q.pick U

end Rw

/-! ## The rewrite read -/

section RwEval

variable {Γ : Ctx} {q : LawPair C Γ}

/-- Where the law fires, the term is its left side and the replacement its
right side. -/
theorem LawPair.pick_some {s : Srt} {t t' : Tm C Γ s} (h : q.pick t = some t') :
    ∃ (e : q.k = s), t = e ▸ q.lhs ∧ t' = e ▸ q.rhs := by
  unfold LawPair.pick at h
  split at h
  · rename_i hc
    have he := Tm.eq_of_beqM t q.lhs ((Tm.beqR_eq_beqM t q.lhs).symm.trans hc)
    cases q with
    | mk lhs rhs =>
      obtain ⟨rfl, hh⟩ := Sigma.mk.inj he
      cases hh
      simp only [LawPair.rhsAt?, dif_pos, Option.some.injEq] at h
      exact ⟨rfl, rfl, h.symm⟩
  · cases h

/-- **A law that refines keeps every value a term returns.** -/
theorem LawPair.pick_le (hq : q.Refines) (σ : State C Γ) : PickLe q.pick σ := fun h => by
  obtain ⟨e, rfl, rfl⟩ := LawPair.pick_some h
  subst e
  exact hq σ

/-- **A law that refines back at one state keeps every value its rewrite
returns there.** -/
theorem LawPair.pick_ge (σ : State C Γ) (hq : Srt.Le q.k (q.rhs.evalT σ) (q.lhs.evalT σ)) :
    PickGe q.pick σ := fun h => by
  obtain ⟨e, rfl, rfl⟩ := LawPair.pick_some h
  subst e
  exact hq

end RwEval

/-! ## A law in an update's right-hand sides

A law (`LawCov`, `Calculus/TermLaws.lean`) in the right-hand sides of an
update at its scope: it refines (`LawCov.fwd`), and refines back wherever an
update its check accepts returns (`LawCov.back`), checked on the rewritten
update. -/

section Laws

variable {Γ₀ : Ctx}

/-- **A law in an update's right-hand sides, under any modality**, where it
refines, and refines back wherever the rewritten update returns. -/
theorem holds_upd_rwG {q : LawPair C Γ₀} (hr : q.Refines) {m : Modality} {Δ : Ctx}
    {U : Upd C Γ₀ Δ} {φ : Fml C Δ} (σ : State C Γ₀)
    (hb : ∀ g, (Upd.rwG q U).globT σ = .ok g → Srt.Le q.k (q.rhs.evalT σ) (q.lhs.evalT σ))
    (h : holds σ (.upd m (Upd.rwG q U) φ)) : holds σ (.upd m U φ) := by
  refine Upd.afterT_intro (fun e he => ?_) fun g σ' hL hH =>
    h.of_lands (Upd.rwBy_lands σ (LawPair.pick_le hr σ) U hL) hH
  cases hB : (Upd.rwG q U).globT σ with
  | error e' => exact h.of_error hB
  | ok g =>
    rw [Upd.rwBy_globT_rev σ (LawPair.pick_ge σ (hb g hB)) U g hB] at he
    cases he

/-- The law `E` in the right-hand sides of `{U}_m φ`, `U` at the law's scope. -/
def Fml.updRwS (q : LawPair C Γ₀) (E : LawCov C Γ₀ q.k q.lhs q.rhs)
    {Δ : Ctx} (m : Modality) (U : Upd C Γ₀ Δ) (φ : Fml C Δ) : Option (Fml C Γ₀) :=
  if (Upd.hasG q U && E.chk (Upd.rwG q U)) = true then some (.upd m (Upd.rwG q U) φ) else none

/-- `Fml.updRwS` on an update read at the law's scope `Γ₀`. -/
def Fml.updRwSAt (q : LawPair C Γ₀) (E : LawCov C Γ₀ q.k q.lhs q.rhs)
    {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) : Option (Fml C Γ) :=
  if h : Γ = Γ₀ then
    cast (congrArg (fun G => Option (Fml C G)) h.symm)
      (Fml.updRwS q E m (cast (congrArg (fun G => Upd C G Δ) h) U) φ)
  else none

/-- **`updRw` past the program**: the law `E` in the right-hand sides of the
update at position `i`, under any modality, its two sides at the update's
scope `Γ₀`. -/
def FmlRw.lawUpdS (q : LawPair C Γ₀) (E : LawCov C Γ₀ q.k q.lhs q.rhs) (i : Nat) : FmlRw C :=
  FmlRw.atSpine (fun m U φ => Fml.updRwSAt q E m U φ) (fun {Γ _ m U φ ψ} h σ hψ => by
    dsimp only [Fml.updRwSAt] at h
    split at h
    · rename_i he
      subst he
      simp only [cast_eq] at h
      dsimp only [Fml.updRwS] at h
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true] at hc
        refine holds_upd_rwG (LawPair.Refines.of_at E.fwd) σ (fun g hB => ?_) hψ
        have hm := Upd.apply_glob σ (Upd.rwG q U)
        rw [hB] at hm
        cases hA : (Upd.rwG q U).apply σ.erase with
        | error e => rw [hA] at hm; cases hm
        | ok τ =>
          rw [Tm.evalT_eq, Tm.evalT_eq]
          exact E.back (Upd.rwG q U) σ.erase τ hc.2 hA
      · cases h
    · cases h) i

/-- The scopes of the updates along the spine, each update's context. -/
def Fml.spineScopes : (Γ : Ctx) → Fml C Γ → List Ctx
  | _, .all _ _ φ => Fml.spineScopes _ φ
  | _, .bind _ _ _ φ => Fml.spineScopes _ φ
  | Γ, .upd _ _ ψ => Γ :: Fml.spineScopes _ ψ
  | _, _ => []

end Laws

end Solidity
