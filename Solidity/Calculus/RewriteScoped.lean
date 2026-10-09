import Solidity.Calculus.UpdateRules
import Solidity.Calculus.Merge
import Solidity.Calculus.Literals

/-!
# Rewrites of a scoped line

A chain's rewrite links on the scoped line itself (`Fml C Γ`), so that a
rewrite goes in while the program is still open and the strategy's steps go
on after it: `{ x := 250 ‖ se1 := 250 + 10 <= 255 } (… ∧ (se1 ≐ false → [ revert(); ] φ))`
folds its literals, pushes the update through the branches and folds them,
and `revertBox` then fires on what is left.  Past the program the rewrites
stay `Calculus/ChainRewrites.lean`'s on the erasure (`Fml.ViaE`).

A rewrite is a function on the whole line with the one fact a chain needs
of it: wherever the line after holds, the line before does (`FmlRw`).  A
link `φ ~[n]~> ψ` is `r.apply φ = some ψ` (`Fml.RwBy`), proved by `rfl`.

| `FmlRw` | line before ⇝ line after | sound by | solkey |
|---|---|---|---|
| `lit r i` | a literal law in the right-hand sides of the update at spine position `i`, any modality | `Upd.rwC_apply_eq` (iff) | `add_literals`, `leq_literals`, … |
| `lawUpd r ht i` | a term taclet onto a term that cannot halt, in the box update at `i` | `holds_upd_rwC` | `updRw` |
| `applyOnRigid i s` | `{U}(A ∧ B)`, `{U}(a → B)`, `{U}¬a`, `{U}a` with `a` first-order: `U` applied to the first-order parts (`Fml.substU`), kept in front of the rest; `U` at `i`, cannot halt or under the box | `Fml.pushS_sound` | `applyOnRigidFormula` |
| `concrete n s` | `true ∧ A ⇝ A`, `false → A ⇝ true`, `v ≐ v ⇝ true`, … below `n` updates | `Fml.concreteAlongS_holds` (iff) | `concrete_*`, `eqClose` |

`sequentialToParallel` while the program is open is `Calculus/Merge.lean`'s.

**Where.**  The spine of a line is its updates, through its quantifiers and
hidden binders (`Fml.belowS`, as `Fml.mergeAt` walks it): a rewrite of an
update names its position, a fold the number of updates above it.  Under a
branch a rewrite follows the line's propositional skeleton (`Skel`,
`Calculus/ChainBranches.lean`), which the elaborator computes from the line
with its postconditions in slots (`Fml.skelS`): a postcondition variable,
a program, a quantifier is a part the rewrite never looks at, so the
kernel computes it past them by `rfl`.

These functions run once a link, not once a step, and use `match` on the
indexed families, against Gate G0's first condition: an exemption, as
`Calculus/Merge.lean`'s merge is.
-/

namespace Solidity

open Solidity (Srt Op0 Modality)
open Semantics (Value)
open Theory Theory.StValue

variable {C : Contract}

/-! ## A rewrite of a scoped line -/

/-- A rewrite of a scoped line: the line after, computed (`apply`), and why
the line before follows from it (`sound`). -/
structure FmlRw (C : Contract) where
  /-- The line after, or `none` where the rule does not fit. -/
  apply : {Γ : Ctx} → Fml C Γ → Option (Fml C Γ)
  /-- Wherever the line after holds, the line before does. -/
  sound : ∀ {Γ : Ctx} {φ ψ : Fml C Γ}, apply φ = some ψ → ∀ σ : State C Γ, holds σ ψ → holds σ φ

/-- `φ ~[n]~> ψ` on scoped lines: the rewrite `r`, named `n` as the chain
writes it, turns `φ` into `ψ`. -/
def Fml.RwBy {Γ : Ctx} (_n : String) (r : FmlRw C) (φ ψ : Fml C Γ) : Prop := r.apply φ = some ψ

/-! ## Where on the line -/

section Where

/-- `f` on the line below `n` of its updates, through its quantifiers and
hidden binders. -/
def Fml.belowS (f : {Γ : Ctx} → Fml C Γ → Option (Fml C Γ)) :
    {Γ : Ctx} → Nat → Fml C Γ → Option (Fml C Γ)
  | _, n, .all x p φ => (Fml.belowS f n φ).map (.all x p)
  | _, n, .bind m x t φ => (Fml.belowS f n φ).map (.bind m x t)
  | _, 0, φ => f φ
  | _, n + 1, .upd m U φ => (Fml.belowS f n φ).map (.upd m U)
  | _, _ + 1, _ => none

/-- `f` on an update in front of the line. -/
def Fml.atUpd (f : {Γ Δ : Ctx} → Modality → Upd C Γ Δ → Fml C Δ → Option (Fml C Γ)) :
    {Γ : Ctx} → Fml C Γ → Option (Fml C Γ)
  | _, .upd m U φ => f m U φ
  | _, _ => none

variable {f : {Γ : Ctx} → Fml C Γ → Option (Fml C Γ)}

/-- A rewrite below the spine is one of the line. -/
theorem Fml.belowS_sound
    (hf : ∀ {Γ : Ctx} {φ ψ : Fml C Γ}, f φ = some ψ → ∀ σ, holds σ ψ → holds σ φ) :
    {Γ : Ctx} → (n : Nat) → (φ : Fml C Γ) → {ψ : Fml C Γ} → Fml.belowS f n φ = some ψ →
      ∀ σ, holds σ ψ → holds σ φ
  | _, n, .all x p φ, ψ₀, h => by
    have h : (Fml.belowS f n φ).map (Fml.all x p) = some ψ₀ := by rw [← h]; cases n <;> rfl
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs v => Fml.belowS_sound hf n φ hψ _ (hs v)
  | _, n, .bind m x t φ, ψ₀, h => by
    have h : (Fml.belowS f n φ).map (Fml.bind m x t) = some ψ₀ := by rw [← h]; cases n <;> rfl
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs => Modality.forallB_imp (fun v => Fml.belowS_sound hf n φ hψ _) hs
  | _, n + 1, .upd m U φ, _, h => by
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs => Modality.afterC_imp hs fun τ a σ' e hx =>
      Fml.belowS_sound hf n φ hψ σ' (a σ' e hx)
  | _, 0, .tt, _, h | _, 0, .eq .., _, h | _, 0, .defined _, _, h | _, 0, .not _, _, h
  | _, 0, .and .., _, h | _, 0, .imp .., _, h | _, 0, .upd .., _, h | _, 0, .modal .., _, h
  | _, 0, .havoc _, _, h | _, 0, .anon .., _, h => hf h
  | _, _ + 1, .tt, _, h | _, _ + 1, .eq .., _, h | _, _ + 1, .defined _, _, h
  | _, _ + 1, .not _, _, h | _, _ + 1, .and .., _, h | _, _ + 1, .imp .., _, h
  | _, _ + 1, .modal .., _, h | _, _ + 1, .havoc _, _, h | _, _ + 1, .anon .., _, h => by cases h

/-- A rewrite of the update in front is one of the line. -/
theorem Fml.atUpd_sound {g : {Γ Δ : Ctx} → Modality → Upd C Γ Δ → Fml C Δ → Option (Fml C Γ)}
    (hg : ∀ {Γ Δ : Ctx} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ} {ψ : Fml C Γ},
      g m U φ = some ψ → ∀ σ, holds σ ψ → holds σ (.upd m U φ)) :
    {Γ : Ctx} → {φ ψ : Fml C Γ} → Fml.atUpd g φ = some ψ → ∀ σ, holds σ ψ → holds σ φ
  | _, .upd _ _ _, _, h => hg h
  | _, .tt, _, h | _, .eq .., _, h | _, .defined _, _, h | _, .not _, _, h | _, .and .., _, h
  | _, .imp .., _, h | _, .modal .., _, h | _, .havoc _, _, h | _, .all .., _, h
  | _, .bind .., _, h | _, .anon .., _, h => by cases h

end Where

/-- A rewrite below `n` updates of the spine. -/
def FmlRw.below (f : {Γ : Ctx} → Fml C Γ → Option (Fml C Γ))
    (hf : ∀ {Γ : Ctx} {φ ψ : Fml C Γ}, f φ = some ψ → ∀ σ, holds σ ψ → holds σ φ) (n : Nat) :
    FmlRw C :=
  ⟨fun φ => Fml.belowS f n φ, fun h => Fml.belowS_sound hf n _ h⟩

/-- A rewrite of the update at position `i` of the spine. -/
def FmlRw.atSpine (g : {Γ Δ : Ctx} → Modality → Upd C Γ Δ → Fml C Δ → Option (Fml C Γ))
    (hg : ∀ {Γ Δ : Ctx} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ} {ψ : Fml C Γ},
      g m U φ = some ψ → ∀ σ, holds σ ψ → holds σ (.upd m U φ)) (i : Nat) : FmlRw C :=
  FmlRw.below (fun φ => Fml.atUpd g φ) (fun h => Fml.atUpd_sound hg h) i

/-! ## A law in an update's right-hand sides -/

section Laws

variable {Γ : Ctx} {q : Solidity.Term C × Solidity.Term C}

/-- Whether `Tm.pickC` rewrites `t`: a closed value term reading `q.1` on
its erasure, `q.2` a term at the scope. -/
def Tm.firesC (q : Solidity.Term C × Solidity.Term C) : {s : Srt} → Tm C Γ s → Bool
  | .val, t => (t.toNil?).isSome && t.erase [] == q.1 && (Tm.ofClosed? (Γ := Γ) q.2).isSome
  | _, _ => false

/-- Whether `Tm.rwC` rewrites something in `t`. -/
def Tm.hasC (q : Solidity.Term C × Solidity.Term C) : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ => false
  | _, .netOf _ a => Tm.hasC q a
  | _, t@(.app0 _) => Tm.firesC q t
  | _, t@(.app1 _ _ x) => Tm.firesC q t || Tm.hasC q x
  | _, t@(.app2 _ x y) => Tm.firesC q t || Tm.hasC q x || Tm.hasC q y
  | _, t@(.app3 _ x y z) => Tm.firesC q t || Tm.hasC q x || Tm.hasC q y || Tm.hasC q z

/-- Whether `Rhs.rwC` rewrites something. -/
def Rhs.hasC (q : Solidity.Term C × Solidity.Term C) : {t : LTy} → Rhs C Γ t → Bool
  | _, .val t => t.hasC q
  | _, .path p => p.hasC q
  | _, .mref i => i.hasC q
  | _, .store s => s.hasC q
  | _, _ => false

/-- Whether `UpdElem.rwC` rewrites something. -/
def UpdElem.hasC {Δ : Ctx} (q : Solidity.Term C × Solidity.Term C) : UpdElem C Γ Δ → Bool
  | .local _ r => r.hasC q
  | .storage s => s.hasC q
  | .memory m => m.hasC q
  | .selfBalance _ a | .setBalance a => a.hasC q
  | .net r _ a | .pay r a | .netMt r a => r.hasC q || a.hasC q

/-- Whether `Upd.rwC` rewrites something. -/
def Upd.hasC (q : Solidity.Term C × Solidity.Term C) : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => false
  | _, .snoc U e => Upd.hasC q U || e.hasC q
  | _, .decl U _ r => Upd.hasC q U || r.hasC q
  | _, .pop U _ | _, .drop U _ => Upd.hasC q U

/-- A law whose two sides return alike in every state: a literal law. -/
def Term.EvalEq (t t' : Solidity.Term C) : Prop := ∀ g, t.eval g = t'.eval g

theorem LitLaw.evalEq {t t' : Solidity.Term C} (r : LitLaw t t') : Term.EvalEq t t' := by
  obtain ⟨v, rfl, h⟩ := r.exact
  intro g
  rw [h g]
  rfl

theorem Tm.pickC_eval_eq (hq : Term.EvalEq q.1 q.2) (σ : EState C Γ) :
    {s : Srt} → {t d : Tm C Γ s} → d.eval σ = t.eval σ → (Tm.pickC q t d).eval σ = t.eval σ
  | .val, t, d, hd => by
    simp only [Tm.pickC]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Option.isSome_iff_exists, beq_iff_eq] at hc
      obtain ⟨⟨t₀, ht₀⟩, he⟩ := hc
      cases ho : Tm.ofClosed? (Γ := Γ) q.2 with
      | none => exact hd
      | some u =>
        show u.eval σ = t.eval σ
        rw [Tm.eval_toNil σ t ht₀, he, Tm.eval_ofClosed σ q.2 ho, hq]
    · exact hd
  | .path, _, _, hd | .st, _, _, hd | .sv, _, _, hd | .ident, _, _, hd | .addr, _, _, hd
  | .mem, _, _, hd | .mv, _, _, hd => hd

/-- **An exact law keeps what every term returns.** -/
theorem Tm.rwC_eval_eq (hq : Term.EvalEq q.1 q.2) (σ : EState C Γ) :
    {s : Srt} → (t : Tm C Γ s) → (t.rwC q).eval σ = t.eval σ
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ => rfl
  | _, .netOf i a => by simp only [Tm.rwC, Tm.eval, Tm.rwC_eval_eq hq σ a]
  | _, .app0 _ => Tm.pickC_eval_eq hq σ rfl
  | _, .app1 o _ x => Tm.pickC_eval_eq hq σ (by simp only [Tm.eval, Tm.rwC_eval_eq hq σ x])
  | _, .app2 o x y =>
    Tm.pickC_eval_eq hq σ (by simp only [Tm.eval, Tm.rwC_eval_eq hq σ x, Tm.rwC_eval_eq hq σ y])
  | _, .app3 o x y z => Tm.pickC_eval_eq hq σ (by
      simp only [Tm.eval, Tm.rwC_eval_eq hq σ x, Tm.rwC_eval_eq hq σ y, Tm.rwC_eval_eq hq σ z])

theorem Rhs.rwC_eval_eq (hq : Term.EvalEq q.1 q.2) (σ : EState C Γ) {t : LTy} (r : Rhs C Γ t) :
    (r.rwC q).eval σ = r.eval σ := by
  cases r <;> simp only [Rhs.rwC, Rhs.eval, Tm.rwC_eval_eq hq σ]

theorem UpdElem.rwC_write_eq (hq : Term.EvalEq q.1 q.2) {Δ : Ctx} (σ₀ : EState C Γ)
    (e : UpdElem C Γ Δ) (τ : EState C Δ) : (e.rwC q).write σ₀ τ = e.write σ₀ τ := by
  cases e <;> simp only [UpdElem.rwC, UpdElem.write, Rhs.rwC_eval_eq hq σ₀, Tm.rwC_eval_eq hq σ₀]

/-- **An exact law keeps where every update ends.** -/
theorem Upd.rwC_apply_eq (hq : Term.EvalEq q.1 q.2) (σ₀ : EState C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → (U.rwC q).apply σ₀ = U.apply σ₀
  | _, .nil => rfl
  | _, .snoc U e => by
    simp only [Upd.rwC, Upd.apply, Upd.rwC_apply_eq hq σ₀ U, UpdElem.rwC_write_eq hq σ₀]
  | _, .decl U x r => by
    simp only [Upd.rwC, Upd.apply, Upd.rwC_apply_eq hq σ₀ U, Rhs.rwC_eval_eq hq σ₀]
  | _, .pop U h => by simp only [Upd.rwC, Upd.apply, Upd.rwC_apply_eq hq σ₀ U]
  | _, .drop U h => by simp only [Upd.rwC, Upd.apply, Upd.rwC_apply_eq hq σ₀ U]

theorem holds_upd_rwC_iff (hq : Term.EvalEq q.1 q.2) {m : Modality} {Δ : Ctx} {U : Upd C Γ Δ}
    {φ : Fml C Δ} (σ : State C Γ) : holds σ (.upd m (U.rwC q) φ) ↔ holds σ (.upd m U φ) := by
  show Modality.afterC m _ ((U.rwC q).apply σ.erase) ↔ Modality.afterC m _ (U.apply σ.erase)
  rw [Upd.rwC_apply_eq hq]

end Laws

/-- An exact law in the update's right-hand sides, under any modality. -/
def Fml.updRwEq (q : Solidity.Term C × Solidity.Term C) {Γ Δ : Ctx} (m : Modality)
    (U : Upd C Γ Δ) (φ : Fml C Δ) : Option (Fml C Γ) :=
  if U.hasC q then some (.upd m (U.rwC q) φ) else none

/-- A law in the right-hand sides of a box update. -/
def Fml.updRwBox (q : Solidity.Term C × Solidity.Term C) {Γ Δ : Ctx} :
    Modality → Upd C Γ Δ → Fml C Δ → Option (Fml C Γ)
  | .box, U, φ => if U.hasC q then some (.upd .box (U.rwC q) φ) else none
  | .diamond, _, _ => none

namespace FmlRw

/-- **A literal law** (`add_literals`, …) in the right-hand sides of the
update at position `i`, under any modality: it is exact. -/
def lit {t t' : Solidity.Term C} (r : LitLaw t t') (i : Nat) : FmlRw C :=
  FmlRw.atSpine (fun m U φ => Fml.updRwEq (t, t') m U φ) (fun {_ _ m U φ ψ} h σ hψ => by
    dsimp only [Fml.updRwEq] at h
    split at h
    · cases h; exact (holds_upd_rwC_iff (q := (t, t')) r.evalEq σ).1 hψ
    · cases h) i

/-- **A term taclet** onto a term that cannot halt, in the right-hand sides
of the box update at position `i` (solkey's `updRw`). -/
def lawUpd {t t' : Solidity.Term C} (r : TermTaclet t t') (ht : t'.total = true) (i : Nat) :
    FmlRw C :=
  FmlRw.atSpine (fun m U φ => Fml.updRwBox (t, t') m U φ) (fun {_ _ m U φ ψ} h σ hψ => by
    cases m with
    | diamond => cases h
    | box =>
      dsimp only [Fml.updRwBox] at h
      split at h
      · cases h; exact holds_upd_rwC (q := (t, t')) (Term.EvalRefines.of_theq r.sound ht) σ hψ
      · cases h) i

end FmlRw

/-! ## `applyOnRigid` under a branch -/

section Push

/-- A value term that cannot halt: a local, a literal. -/
def Tm.totalV {Γ : Ctx} : Tm C Γ .val → Bool
  | .pvV _ => true
  | .app0 (.lit _) => true
  | _ => false

/-- A right-hand side that cannot halt. -/
def Rhs.totalS {Γ : Ctx} : {t : LTy} → Rhs C Γ t → Bool
  | _, .val t => t.totalV
  | _, .unset => true
  | _, .saveNetMt => true
  | _, _ => false

/-- An update of locals whose right-hand sides cannot halt: it returns in
every state. -/
def Upd.totalS {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => true
  | _, .snoc U (.local _ r) => Upd.totalS U && r.totalS
  | _, .snoc _ _ => false
  | _, .decl U _ r => Upd.totalS U && r.totalS
  | _, .pop U _ | _, .drop U _ => Upd.totalS U

theorem Tm.totalV_eval {Γ : Ctx} (σ : EState C Γ) :
    (t : Tm C Γ .val) → t.totalV = true → ∃ v, t.eval σ = .ok v
  | .pvV _, _ => ⟨_, rfl⟩
  | .app0 (.lit v), _ => ⟨v, rfl⟩
  | .app0 (.env _), h | .netOf .., h | .app1 .., h | .app2 .., h | .app3 .., h => by cases h

theorem Rhs.totalS_eval {Γ : Ctx} (σ : EState C Γ) :
    {t : LTy} → (r : Rhs C Γ t) → r.totalS = true → ∃ v, r.eval σ = .ok v
  | _, .val t, h => Tm.totalV_eval σ t h
  | _, .unset, _ => ⟨_, rfl⟩
  | _, .saveNetMt, _ => ⟨_, rfl⟩
  | _, .path _, h | _, .mref _, h | _, .store _, h | _, .saveNet, h => by cases h

theorem Upd.totalS_apply {Γ : Ctx} (σ₀ : EState C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → U.totalS = true → ∃ τ, U.apply σ₀ = .ok τ
  | _, .nil, _ => ⟨_, rfl⟩
  | _, .snoc U (.local i r), h => by
    obtain ⟨hU, hr⟩ := Bool.and_eq_true_iff.1 h
    obtain ⟨τ, hτ⟩ := Upd.totalS_apply σ₀ U hU
    obtain ⟨v, hv⟩ := Rhs.totalS_eval σ₀ r hr
    refine ⟨τ.setLocal i v, ?_⟩
    simp only [Upd.apply, UpdElem.write, hτ, hv]
    rfl
  | _, .snoc _ (.storage _), h | _, .snoc _ (.memory _), h | _, .snoc _ (.selfBalance ..), h
  | _, .snoc _ (.net ..), h | _, .snoc _ (.pay ..), h | _, .snoc _ (.netMt ..), h
  | _, .snoc _ (.setBalance _), h => by cases h
  | _, .decl U x r, h => by
    obtain ⟨hU, hr⟩ := Bool.and_eq_true_iff.1 h
    obtain ⟨τ, hτ⟩ := Upd.totalS_apply σ₀ U hU
    obtain ⟨v, hv⟩ := Rhs.totalS_eval σ₀ r hr
    refine ⟨τ.push v, ?_⟩
    simp only [Upd.apply, hτ, hv]
    rfl
  | _, .pop U e, h => by
    obtain ⟨τ, hτ⟩ := Upd.totalS_apply σ₀ U h
    exact ⟨τ.drop e, by simp only [Upd.apply, hτ]; rfl⟩
  | _, .drop U e, h => by
    obtain ⟨τ, hτ⟩ := Upd.totalS_apply σ₀ U h
    exact ⟨τ.thin e, by simp only [Upd.apply, hτ]; rfl⟩

/-- Whether a modality is the box. -/
def Modality.isBoxS : Modality → Bool
  | .box => true
  | .diamond => false

/-- A skeleton with no part not to look at: a first-order formula of
connectives and literal leaves. -/
def Skel.closedS : Skel → Bool
  | .lit => true
  | .and _ _ l r | .imp _ _ l r => l.closedS && r.closedS
  | .not _ s => s.closedS
  | _ => false

/-- A skeleton `applyOnRigid` acts on: a connective or a literal leaf. -/
def Skel.pushable : Skel → Bool
  | .lit | .and .. | .imp .. | .not .. => true
  | _ => false

variable {Γ Δ : Ctx}

/-- `{U}_m φ` pushed through the connectives of the skeleton `s`: a
first-order part (`Skel.closedS`) applied (`Fml.substU`), the update kept
in front of the rest, and of a part it cannot be applied to. -/
def Fml.pushS (m : Modality) (U : Upd C Γ Δ) : Skel → Fml C Δ → Fml C Γ
  | .and _ _ l r, φ => match φ with
    | .and a b => .and (Fml.pushS m U l a) (Fml.pushS m U r b)
    | φ => .upd m U φ
  | .imp _ _ l r, φ => match φ with
    | .imp a b =>
      if l.closedS then
        match Fml.substU U a with
        | some a' => .imp a' (Fml.pushS m U r b)
        | none => .upd m U (.imp a b)
      else .upd m U (.imp a b)
    | φ => .upd m U φ
  | .not _ s, φ => match φ with
    | .not a =>
      if s.closedS then
        match Fml.substU U a with
        | some a' => .not a'
        | none => .upd m U (.not a)
      else .upd m U (.not a)
    | φ => .upd m U φ
  | .lit, φ => match Fml.substU U φ with
    | some φ' => φ'
    | none => .upd m U φ
  | _, φ => .upd m U φ

/-- The update in front, where it returns: what it leaves read in each typed
state it ends in. -/
theorem holds_upd_of_ok {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ} {σ : State C Γ}
    (hU : (∃ τ, U.apply σ.erase = .ok τ) ∨ m = .box)
    (k : ∀ σ₁, U.apply σ.erase = .ok σ₁ → ∀ σ' : State C Δ, σ'.erase = σ₁ → σ.H <+: σ'.H →
      holds σ' φ) :
    holds σ (.upd m U φ) := by
  show Modality.afterC m _ (U.apply σ.erase)
  cases hr : U.apply σ.erase with
  | ok σ₁ => exact k σ₁ hr
  | error e =>
    rcases hU with ⟨τ, hτ⟩ | rfl
    · rw [hr] at hτ; cases hτ
    · trivial

/-- The update in front of a conjunction, from it in front of each part. -/
theorem holds_upd_and {m : Modality} {U : Upd C Γ Δ} {a b : Fml C Δ} {σ : State C Γ}
    (ha : holds σ (.upd m U a)) (hb : holds σ (.upd m U b)) : holds σ (.upd m U (.and a b)) := by
  have ha : Modality.afterC m _ (U.apply σ.erase) := ha
  have hb : Modality.afterC m _ (U.apply σ.erase) := hb
  show Modality.afterC m _ (U.apply σ.erase)
  cases hr : U.apply σ.erase with
  | ok σ₁ =>
    rw [hr] at ha hb
    exact fun σ' e x => ⟨ha σ' e x, hb σ' e x⟩
  | error e => rw [hr] at ha; exact ha

/-- **The update pushed through gives the update in front**, where the
update returns or under the box. -/
theorem Fml.pushS_sound {m : Modality} {U : Upd C Γ Δ} {σ : State C Γ}
    (hU : (∃ τ, U.apply σ.erase = .ok τ) ∨ m = .box) :
    (s : Skel) → (φ : Fml C Δ) → holds σ (Fml.pushS m U s φ) → holds σ (.upd m U φ)
  | .and _ _ l r, φ, h => by
    cases φ with
    | and a b =>
      exact holds_upd_and (Fml.pushS_sound hU l a h.1) (Fml.pushS_sound hU r b h.2)
    | _ => exact h
  | .imp _ _ l r, φ, h => by
    cases φ with
    | imp a b =>
      simp only [Fml.pushS] at h
      split at h
      · split at h
        · rename_i a' hs
          refine holds_upd_of_ok hU fun σ₁ hr σ' e x ha => ?_
          have hb := Fml.pushS_sound hU r b (h ((Fml.substU_holds hr a hs σ σ' rfl e).2 ha))
          have hb : Modality.afterC m _ (U.apply σ.erase) := hb
          rw [hr] at hb
          exact hb σ' e x
        · exact h
      · exact h
    | _ => exact h
  | .not _ s, φ, h => by
    cases φ with
    | not a =>
      simp only [Fml.pushS] at h
      split at h
      · split at h
        · rename_i a' hs
          exact holds_upd_of_ok hU fun σ₁ hr σ' e _ ha =>
            h ((Fml.substU_holds hr a hs σ σ' rfl e).2 ha)
        · exact h
      · exact h
    | _ => exact h
  | .lit, φ, h => by
    simp only [Fml.pushS] at h
    split at h
    · rename_i φ' hs
      exact holds_upd_of_ok hU fun σ₁ hr σ' e _ => (Fml.substU_holds hr φ hs σ σ' rfl e).1 h
    · exact h
  | .opaque, _, h | .upd _, _, h => h

/-- `applyOnRigid` on the update in front, along the skeleton `s` of the
formula under it, where the update cannot halt or under the box. -/
def Fml.pushAt (s : Skel) {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) :
    Option (Fml C Γ) :=
  if s.pushable && (U.totalS || m.isBoxS) then some (Fml.pushS m U s φ) else none

theorem Fml.pushAt_sound {s : Skel} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ} {ψ : Fml C Γ}
    (h : Fml.pushAt s m U φ = some ψ) (σ : State C Γ) (hψ : holds σ ψ) :
    holds σ (.upd m U φ) := by
  unfold Fml.pushAt at h
  split at h
  · rename_i hc
    cases h
    have hc : U.totalS = true ∨ m.isBoxS = true := by
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hc
      exact hc.2
    refine Fml.pushS_sound ?_ s φ hψ
    rcases hc with ht | hb
    · exact .inl (Upd.totalS_apply σ.erase U ht)
    · cases m with
      | box => exact .inr rfl
      | diamond => cases hb
  · cases h

end Push

/-- **`applyOnRigid`** at position `i` of the spine, along the skeleton `s`
of the formula under that update. -/
def FmlRw.applyOnRigid (i : Nat) (s : Skel) : FmlRw C :=
  FmlRw.atSpine (fun m U φ => Fml.pushAt s m U φ) (fun h σ hψ => Fml.pushAt_sound h σ hψ) i

/-! ## The literal connectives folded -/

section Concrete

variable {Γ : Ctx}

/-- `true`. -/
def Fml.isTTS : Fml C Γ → Bool
  | .tt => true
  | _ => false

/-- `false`, which is `¬true`. -/
def Fml.isFFS : Fml C Γ → Bool
  | .not .tt => true
  | _ => false

theorem Fml.eq_tt_of_isTTS : {φ : Fml C Γ} → φ.isTTS = true → φ = .tt
  | .tt, _ => rfl

theorem Fml.eq_ff_of_isFFS : {φ : Fml C Γ} → φ.isFFS = true → φ = .not .tt
  | .not .tt, _ => rfl

/-- `φ ∧ ψ` folded: `concrete_and_1-4`.  `lo`, `ro`: a part not to look at. -/
def Fml.andCS (lo ro : Bool) (φ ψ : Fml C Γ) : Fml C Γ :=
  if (!lo && φ.isTTS) = true then ψ
  else if (!lo && φ.isFFS) = true then .ff
  else if (!ro && ψ.isTTS) = true then φ
  else if (!ro && ψ.isFFS) = true then .ff
  else .and φ ψ

/-- `φ → ψ` folded: `concrete_impl_1-4`. -/
def Fml.impCS (lo ro : Bool) (φ ψ : Fml C Γ) : Fml C Γ :=
  if (!lo && φ.isTTS) = true then ψ
  else if (!lo && φ.isFFS) = true then .tt
  else if (!ro && ψ.isTTS) = true then .tt
  else if (!ro && ψ.isFFS) = true then .not φ
  else .imp φ ψ

/-- `¬φ` folded: `concrete_not_2`. -/
def Fml.notCS (o : Bool) (φ : Fml C Γ) : Fml C Γ :=
  if (!o && φ.isFFS) = true then .tt else .not φ

/-- A literal leaf folded: two literals compared (`eqClose`), a literal
defined. -/
def Fml.litCS : Fml C Γ → Fml C Γ
  | .eq (.app0 (.lit v)) (.app0 (.lit w)) => if v = w then .tt else .ff
  | .defined (.app0 (.lit _)) => .tt
  | φ => φ

/-- Whether a fold fires on a connective's parts. -/
def Fml.connFiresS (lo ro : Bool) (φ ψ : Fml C Γ) : Bool :=
  (!lo && (φ.isTTS || φ.isFFS)) || (!ro && (ψ.isTTS || ψ.isFFS))

/-- Whether a fold fires on a literal leaf. -/
def Fml.litFiresS : Fml C Γ → Bool
  | .eq (.app0 (.lit _)) (.app0 (.lit _)) | .defined (.app0 (.lit _)) => true
  | _ => false

theorem Fml.andCS_holds (lo ro : Bool) (φ ψ : Fml C Γ) (σ : State C Γ) :
    holds σ (Fml.andCS lo ro φ ψ) ↔ (holds σ φ ∧ holds σ ψ) := by
  unfold Fml.andCS
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain rfl := Fml.eq_tt_of_isTTS h.2
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain rfl := Fml.eq_ff_of_isFFS h.2
    exact ⟨fun h => absurd trivial h, fun h => absurd trivial h.1⟩
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain rfl := Fml.eq_tt_of_isTTS h.2
    exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain rfl := Fml.eq_ff_of_isFFS h.2
    exact ⟨fun h => absurd trivial h, fun h => absurd trivial h.2⟩
  exact Iff.rfl

theorem Fml.impCS_holds (lo ro : Bool) (φ ψ : Fml C Γ) (σ : State C Γ) :
    holds σ (Fml.impCS lo ro φ ψ) ↔ (holds σ φ → holds σ ψ) := by
  unfold Fml.impCS
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain rfl := Fml.eq_tt_of_isTTS h.2
    exact ⟨fun h _ => h, fun h => h trivial⟩
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain rfl := Fml.eq_ff_of_isFFS h.2
    exact ⟨fun _ h => absurd trivial h, fun _ => trivial⟩
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain rfl := Fml.eq_tt_of_isTTS h.2
    exact ⟨fun _ _ => trivial, fun _ => trivial⟩
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain rfl := Fml.eq_ff_of_isFFS h.2
    exact ⟨fun h a => absurd (h a) id, fun h a => absurd trivial (h a)⟩
  exact Iff.rfl

theorem Fml.notCS_holds (o : Bool) (φ : Fml C Γ) (σ : State C Γ) :
    holds σ (Fml.notCS o φ) ↔ ¬ holds σ φ := by
  unfold Fml.notCS
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain rfl := Fml.eq_ff_of_isFFS h.2
    exact ⟨fun _ h => h trivial, fun _ => trivial⟩
  exact Iff.rfl

theorem Fml.litCS_holds (φ : Fml C Γ) (σ : State C Γ) : holds σ φ.litCS ↔ holds σ φ := by
  unfold Fml.litCS
  split
  · rename_i v w
    split
    · rename_i hvw
      subst hvw
      exact ⟨fun _ => Equiv.refl _, fun _ => trivial⟩
    · rename_i hvw
      refine ⟨fun h => absurd trivial h, fun h => ?_⟩
      exact absurd (StValue.prim.inj (Equiv.prim_iff.1 h)) hvw
  · rename_i v
    exact ⟨fun _ => ⟨v, rfl⟩, fun _ => trivial⟩
  · exact Iff.rfl

/-- The folds, bottom-up along the skeleton `s`. -/
def Fml.concreteAlongS : Skel → Fml C Γ → Fml C Γ
  | .and lo ro l r, φ => match φ with
    | .and a b => Fml.andCS lo ro (Fml.concreteAlongS l a) (Fml.concreteAlongS r b)
    | φ => φ
  | .imp lo ro l r, φ => match φ with
    | .imp a b => Fml.impCS lo ro (Fml.concreteAlongS l a) (Fml.concreteAlongS r b)
    | φ => φ
  | .not o s, φ => match φ with
    | .not a => Fml.notCS o (Fml.concreteAlongS s a)
    | φ => φ
  | .lit, φ => φ.litCS
  | _, φ => φ

/-- Whether some fold fires along `s`. -/
def Fml.concretesAlongS : Skel → Fml C Γ → Bool
  | .and lo ro l r, φ => match φ with
    | .and a b => Fml.concretesAlongS l a || Fml.concretesAlongS r b ||
      Fml.connFiresS lo ro (Fml.concreteAlongS l a) (Fml.concreteAlongS r b)
    | _ => false
  | .imp lo ro l r, φ => match φ with
    | .imp a b => Fml.concretesAlongS l a || Fml.concretesAlongS r b ||
      Fml.connFiresS lo ro (Fml.concreteAlongS l a) (Fml.concreteAlongS r b)
    | _ => false
  | .not o s, φ => match φ with
    | .not a => Fml.concretesAlongS s a || (!o && (Fml.concreteAlongS s a).isFFS)
    | _ => false
  | .lit, φ => φ.litFiresS
  | _, _ => false

/-- **The folds are equivalences.** -/
theorem Fml.concreteAlongS_holds (σ : State C Γ) :
    (s : Skel) → (φ : Fml C Γ) → (holds σ (Fml.concreteAlongS s φ) ↔ holds σ φ)
  | .opaque, _ | .upd _, _ => Iff.rfl
  | .lit, φ => Fml.litCS_holds φ σ
  | .and lo ro l r, φ => by
    cases φ with
    | and a b =>
      exact (Fml.andCS_holds lo ro _ _ σ).trans
        (and_congr (Fml.concreteAlongS_holds σ l a) (Fml.concreteAlongS_holds σ r b))
    | _ => exact Iff.rfl
  | .imp lo ro l r, φ => by
    cases φ with
    | imp a b =>
      exact (Fml.impCS_holds lo ro _ _ σ).trans
        (imp_congr (Fml.concreteAlongS_holds σ l a) (Fml.concreteAlongS_holds σ r b))
    | _ => exact Iff.rfl
  | .not o s, φ => by
    cases φ with
    | not a => exact (Fml.notCS_holds o _ σ).trans (not_congr (Fml.concreteAlongS_holds σ s a))
    | _ => exact Iff.rfl

/-- The folds along `s`, if one fires. -/
def Fml.concreteOnS (s : Skel) (φ : Fml C Γ) : Option (Fml C Γ) :=
  if Fml.concretesAlongS s φ then some (Fml.concreteAlongS s φ) else none

theorem Fml.concreteOnS_sound {s : Skel} {φ ψ : Fml C Γ} (h : Fml.concreteOnS s φ = some ψ)
    (σ : State C Γ) (hψ : holds σ ψ) : holds σ φ := by
  unfold Fml.concreteOnS at h
  split at h
  · cases h; exact (Fml.concreteAlongS_holds σ s φ).1 hψ
  · cases h

end Concrete

/-- **`concrete`** below `n` updates of the spine, along the skeleton `s` of
the formula there. -/
def FmlRw.concrete (n : Nat) (s : Skel) : FmlRw C :=
  FmlRw.below (fun φ => Fml.concreteOnS s φ) (fun h σ hψ => Fml.concreteOnS_sound h σ hψ) n

/-! ## The skeleton of a scoped line

Computed by the compiled code, on the line with its postconditions in their
slots (`Fml.chainSlot`, an `{anon(…)}`): a slot, a program, a quantifier, a
`havoc` are parts no rewrite looks at.  The status mirrors the folds of
`Fml.concreteAlongS`, so the flags of a connective (`lo`, `ro`, `o`) are
exact (`Calculus/RewriteChains.lean`'s `skelOf` on `Update.lean`'s lines). -/

/-- What a part folds to under `Fml.concreteAlongS`: `true`, `false`, a
formula not to look at, or anything else. -/
inductive SkelSt where
  | tt | ff | opaque | other
  deriving DecidableEq, Inhabited

/-- The skeleton of a formula and what it folds to. -/
def Fml.skelS {Γ : Ctx} : Fml C Γ → Skel × SkelSt
  | .tt => (.lit, .tt)
  | .eq (.app0 (.lit v)) (.app0 (.lit w)) => (.lit, if v = w then .tt else .ff)
  | .eq _ _ => (.lit, .other)
  | .defined (.app0 (.lit _)) => (.lit, .tt)
  | .defined _ => (.lit, .other)
  | .not a =>
    let (sa, ta) := Fml.skelS a
    let st := match ta with
      | .ff => .tt
      | .tt => .ff
      | .opaque => .opaque
      | .other => .other
    (.not (ta == .opaque) sa, st)
  | .and a b =>
    let (sa, ta) := Fml.skelS a
    let (sb, tb) := Fml.skelS b
    let st := if ta == .tt then tb else if ta == .ff then .ff
      else if tb == .tt then ta else if tb == .ff then .ff else .other
    (.and (ta == .opaque) (tb == .opaque) sa sb, st)
  | .imp a b =>
    let (sa, ta) := Fml.skelS a
    let (sb, tb) := Fml.skelS b
    let st := if ta == .tt then tb else if ta == .ff then .tt
      else if tb == .tt then .tt else if tb == .ff then (if ta == .opaque then .opaque else .other)
      else .other
    (.imp (ta == .opaque) (tb == .opaque) sa sb, st)
  | .upd _ _ ψ => (.upd (Fml.skelS ψ).1, .opaque)
  | _ => (.opaque, .opaque)

/-- The skeletons below `0, 1, …` updates of the spine (through the
quantifiers and hidden binders), as far as the spine goes: the number of
updates is one less than their count. -/
def Fml.spineSkels {Γ : Ctx} : Fml C Γ → List Skel
  | .all _ _ φ => Fml.spineSkels φ
  | .bind _ _ _ φ => Fml.spineSkels φ
  | .upd m U ψ => (Fml.skelS (.upd m U ψ)).1 :: Fml.spineSkels ψ
  | φ => [(Fml.skelS φ).1]

end Solidity
