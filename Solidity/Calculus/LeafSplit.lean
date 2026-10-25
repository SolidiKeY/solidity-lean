import Solidity.Calculus.Logic

/-!
# A joined value split back into its cases (`ifthenelse_split`)

A joined `if` (`ifElseJoin`, `Upd.ifJoin?`) runs as one update whose values
are conditional, `{x := c ? t : e}`, so the rest of the program runs once.
The closer reads some leaves more cheaply as the two cases the walk's split
would have left (`docs/automation.md`, M8): here the update is split back
at the leaf, KeY's `ifthenelse_split` on the antecedent, where `c` is a
`bool` local.  `{x := c ? t : e} φ` holds where both `c = TRUE → {x := t} φ`
and `c = FALSE → {x := e} φ` do (`Fml.SplitTo.here`): the local holds one
of the two, and in that case the joined update computes what the case's
does (`Upd.IteCase.applyV`).  Every joined value of the update read at the
same condition takes the same side, so the two elements of
`if (c) { x = 1; } else { y = 2; }` are split at once.  The split goes in
through the binders, updates, premises and conjunctions in front of the
update (`Fml.SplitTo.upd` …), so a leaf's split is one lemma per formula
in front of it.  Lean only: KeY's split rewrites a formula in place.

Nothing here is trusted by the closer: `sol_close_ite_split`
(`Calculus/CloseScoped/Steps.lean`) applies these lemmas, its `pushFree`
conditions by evaluation, and the kernel checks the proof.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)

variable {C : Contract} {Γ : Ctx}

/-- `U'` is `U` with joined values `x := c ? t : e`, `c` the local at
position `j`, read as their `b` side: `{x := se1 ? x + 1 : 0}` as
`{x := x + 1}` (`b` true) or `{x := 0}` (`b` false). -/
inductive Upd.IteCase (j : Nat) (b : Bool) : {Δ : Ctx} → Upd C Γ Δ → Upd C Γ Δ → Prop
  | nil : Upd.IteCase j b .nil .nil
  | snoc {Δ : Ctx} {U U' : Upd C Γ Δ} (el : UpdElem C Γ Δ) (h : Upd.IteCase j b U U') :
      Upd.IteCase j b (U.snoc el) (U'.snoc el)
  | ite {Δ : Ctx} {U U' : Upd C Γ Δ} {p : PrimTy} (i : Idx Δ (.val p)) (k : Idx Γ (.val .bool))
      (t e : Tm C Γ (.val p)) (hk : k.toNat = j) (h : Upd.IteCase j b U U') :
      Upd.IteCase j b (U.snoc (.local i (.val (.app3 .ite (.pvV k) t e))))
        (U'.snoc (.local i (.val (cond b t e))))
  | decl {Δ : Ctx} {t : LTy} {U U' : Upd C Γ Δ} (x : Var) (r : Rhs C Γ t)
      (h : Upd.IteCase j b U U') : Upd.IteCase j b (U.decl x r) (U'.decl x r)
  | pop {Δ Δ' : Ctx} {U U' : Upd C Γ Δ} (e : Ext Δ' Δ) (h : Upd.IteCase j b U U') :
      Upd.IteCase j b (U.pop e) (U'.pop e)
  | drop {Δ Δ' : Ctx} {U U' : Upd C Γ Δ} (e : Thin Δ' Δ) (h : Upd.IteCase j b U U') :
      Upd.IteCase j b (U.drop e) (U'.drop e)

/-- **A case of a joined update computes what the joined one does** where
the condition holds `b`: `{x := se1 ? x + 1 : 0}` and `{x := x + 1}` where
`se1` is true. -/
theorem Upd.IteCase.applyV {j : Nat} {b : Bool} (σ : State C Γ)
    (hj : ∀ i : Idx Γ (.val .bool), i.toNat = j → TEnv.get i σ.env = b) :
    {Δ : Ctx} → {U U' : Upd C Γ Δ} → Upd.IteCase j b U U' → U'.applyV σ = U.applyV σ
  | _, _, _, .nil => rfl
  | _, _, _, .snoc el h => by
    show (Upd.applyV σ _).bind _ = (Upd.applyV σ _).bind _
    rw [h.applyV σ hj]
  | _, _, _, .ite i k t e hk h => by
    show (Upd.applyV σ _).bind _ = (Upd.applyV σ _).bind _
    rw [h.applyV σ hj]
    have hc : (Tm.app3 Op3.ite (Tm.pvV k) t e).eval σ = cond b (t.eval σ) (e.eval σ) := by
      show ((Tm.pvV k).eval σ).bind (fun cv => cond cv (t.eval σ) (e.eval σ)) = _
      show (some (TEnv.get k σ.env)).bind _ = _
      rw [hj k hk]; rfl
    have hc' : (cond b t e).eval σ = cond b (t.eval σ) (e.eval σ) := by cases b <;> rfl
    congr 1
    funext q
    show ((cond b t e).eval σ).bind _ = ((Tm.app3 Op3.ite (Tm.pvV k) t e).eval σ).bind _
    rw [hc, hc']
  | _, _, _, .decl x r h => by
    show (Upd.applyV σ _).bind _ = (Upd.applyV σ _).bind _
    rw [h.applyV σ hj]
  | _, _, _, .pop e h => by
    show (Upd.applyV σ _).bind _ = (Upd.applyV σ _).bind _
    rw [h.applyV σ hj]
  | _, _, _, .drop e h => by
    show (Upd.applyV σ _).bind _ = (Upd.applyV σ _).bind _
    rw [h.applyV σ hj]

/-- The case `b` of a joined update holds where the condition is `b`:
`{x := se1 ? x + 1 : 0} φ` from `{x := x + 1} φ` where `se1` is true. -/
theorem holds_upd_iteCase {Δ : Ctx} {m : Modality} {U U' : Upd C Γ Δ} {φ : Fml C Δ}
    (σ : State C Γ) (k : Idx Γ (.val .bool)) {b : Bool} (h : Upd.IteCase k.toNat b U U')
    (hU : U.pushFree = true) (hU' : U'.pushFree = true) (hb : TEnv.get k σ.env = b)
    (hh : holds σ (.upd m U' φ)) : holds σ (.upd m U φ) := by
  have hj : ∀ i : Idx Γ (.val .bool), i.toNat = k.toNat → TEnv.get i σ.env = b := by
    intro i hi
    obtain rfl := Idx.toNat_inj i k hi
    exact hb
  change Upd.afterT m σ _ _ at hh
  change Upd.afterT m σ _ _
  rw [Upd.afterT_applyV] at hh ⊢
  rw [h.applyV σ hj, Upd.exh_of_pushFree hU'] at hh
  rw [Upd.exh_of_pushFree hU]
  exact hh

/-- `ψ₁` and `ψ₂` together give `φ`, in every state: the two cases of
`if (c) { x = 1; } else { x = 2; }`'s joined update give it. -/
def Fml.SplitTo {Γ : Ctx} (φ ψ₁ ψ₂ : Fml C Γ) : Prop :=
  ∀ σ : State C Γ, holds σ ψ₁ → holds σ ψ₂ → holds σ φ

/-- A split leaf is valid where both its cases are. -/
theorem Fml.SplitTo.valid {φ ψ₁ ψ₂ : Fml C []} (h : Fml.SplitTo φ ψ₁ ψ₂) (h₁ : Fml.Valid ψ₁)
    (h₂ : Fml.Valid ψ₂) : Fml.Valid φ := fun σ => h σ (h₁ σ) (h₂ σ)

/-- **KeY's `ifthenelse_split`** on a joined update: `{x := c ? t : e} φ`
from `c = TRUE → {x := t} φ` and `c = FALSE → {x := e} φ`. -/
theorem Fml.SplitTo.here {Δ : Ctx} (m : Modality) {U U₁ U₂ : Upd C Γ Δ} (φ : Fml C Δ)
    (k : Idx Γ (.val .bool)) (h₁ : Upd.IteCase k.toNat true U U₁)
    (h₂ : Upd.IteCase k.toNat false U U₂) (hU : U.pushFree = true) (hU₁ : U₁.pushFree = true)
    (hU₂ : U₂.pushFree = true) :
    Fml.SplitTo (.upd m U φ)
      (.imp (.eq (.pvV k) (.app0 (.lit (p := .bool) true))) (.upd m U₁ φ))
      (.imp (.eq (.pvV k) (.app0 (.lit (p := .bool) false))) (.upd m U₂ φ)) := by
  intro σ a₁ a₂
  cases hb : TEnv.get k σ.env
  · exact holds_upd_iteCase σ k h₂ hU hU₂ hb (a₂ ((holds_eq_pvV_lit σ k false).2 hb))
  · exact holds_upd_iteCase σ k h₁ hU hU₁ hb (a₁ ((holds_eq_pvV_lit σ k true).2 hb))

/-- The split under an update: `{y := 1} {x := c ? 1 : 2} φ`. -/
theorem Fml.SplitTo.upd {Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) {φ ψ₁ ψ₂ : Fml C Δ}
    (h : Fml.SplitTo φ ψ₁ ψ₂) : Fml.SplitTo (.upd m U φ) (.upd m U ψ₁) (.upd m U ψ₂) := by
  intro σ a₁ a₂
  change Upd.afterT m σ U _ at a₁ a₂ ⊢
  unfold Upd.afterT at a₁ a₂ ⊢
  split
  · rename_i he; rw [he] at a₁; exact a₁
  · rename_i g hg
    rw [hg] at a₁ a₂
    exact fun σ' hl => h σ' (a₁ σ' hl) (a₂ σ' hl)

/-- The split under a parameter: `∀ uint a, {x := c ? a : 2} φ`. -/
theorem Fml.SplitTo.all (x : Var) (p : PrimTy) {φ ψ₁ ψ₂ : Fml C (.val p :: Γ)}
    (h : Fml.SplitTo φ ψ₁ ψ₂) : Fml.SplitTo (.all x p φ) (.all x p ψ₁) (.all x p ψ₂) :=
  fun _ a₁ a₂ v => h _ (a₁ v) (a₂ v)

/-- The split under a hidden binder (`uint x = …;` dropped to `x = …;`). -/
theorem Fml.SplitTo.bind (m : Modality) (x : Var) (t : LTy) {φ ψ₁ ψ₂ : Fml C (t :: Γ)}
    (h : Fml.SplitTo φ ψ₁ ψ₂) : Fml.SplitTo (.bind m x t φ) (.bind m x t ψ₁) (.bind m x t ψ₂) :=
  fun _ a₁ a₂ v => h _ (a₁ v) (a₂ v)

/-- The split under a premise: `a > 1 → {x := c ? a : 2} φ`. -/
theorem Fml.SplitTo.imp (a : Fml C Γ) {φ ψ₁ ψ₂ : Fml C Γ}
    (h : Fml.SplitTo φ ψ₁ ψ₂) : Fml.SplitTo (.imp a φ) (.imp a ψ₁) (.imp a ψ₂) :=
  fun σ a₁ a₂ ha => h σ (a₁ ha) (a₂ ha)

/-- The split in a conjunction's left side. -/
theorem Fml.SplitTo.andL {φ ψ₁ ψ₂ : Fml C Γ} (r : Fml C Γ)
    (h : Fml.SplitTo φ ψ₁ ψ₂) : Fml.SplitTo (.and φ r) (.and ψ₁ r) (.and ψ₂ r) :=
  fun σ a₁ a₂ => ⟨h σ a₁.1 a₂.1, a₁.2⟩

/-- The split in a conjunction's right side. -/
theorem Fml.SplitTo.andR (l : Fml C Γ) {φ ψ₁ ψ₂ : Fml C Γ}
    (h : Fml.SplitTo φ ψ₁ ψ₂) : Fml.SplitTo (.and l φ) (.and l ψ₁) (.and l ψ₂) :=
  fun σ a₁ a₂ => ⟨a₁.1, h σ a₁.2 a₂.2⟩

/-- The split under `{havoc}`: a loop's exit, `if (c) { x = 1; }` after it. -/
theorem Fml.SplitTo.havoc {φ ψ₁ ψ₂ : Fml C Γ}
    (h : Fml.SplitTo φ ψ₁ ψ₂) : Fml.SplitTo (.havoc φ) (.havoc ψ₁) (.havoc ψ₂) :=
  fun _ a₁ a₂ st nt sb => h _ (a₁ st nt sb) (a₂ st nt sb)

/-- The split under `{anon(xs)}`: a loop body's `if (c) { x = 1; } else { x = 2; }`. -/
theorem Fml.SplitTo.anon (xs : List ((t : LTy) × Idx Γ t)) {φ ψ₁ ψ₂ : Fml C Γ}
    (h : Fml.SplitTo φ ψ₁ ψ₂) : Fml.SplitTo (.anon xs φ) (.anon xs ψ₁) (.anon xs ψ₂) :=
  fun _ a₁ a₂ v => h _ (a₁ v) (a₂ v)

/-- info: 'Solidity.Fml.SplitTo.here' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fml.SplitTo.here

end Solidity
