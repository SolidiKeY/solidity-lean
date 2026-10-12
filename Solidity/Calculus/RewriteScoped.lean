import Solidity.Calculus.StatePartsScoped
import Solidity.Calculus.Merge
import Solidity.Calculus.TermLaws
import Solidity.Calculus.SeqRewrite

/-!
# Rewrites of a scoped line

A chain's rewrite links on the scoped line itself (`Fml C Γ`), so that a
rewrite goes in while the program is still open and the strategy's steps go
on after it: `{ x := 250 ‖ se1 := 250 + 10 <= 255 } (… ∧ (se1 ≐ false → [ revert(); ] φ))`
folds its literals, pushes the update through the branches and folds them,
and `revertBox` then fires on what is left.  Past the program they rewrite
the scoped line too, with `Calculus/RewritePast.lean`'s and
`Calculus/RewriteLaws.lean`'s (W9.4).

A rewrite is a function on the whole line with the one fact a chain needs
of it: wherever the line after holds, the line before does (`FmlRw`).  A
link `φ ~[n]~> ψ` is `r.apply φ = some ψ` (`Fml.RwBy`), proved by `rfl`.

| `FmlRw` | line before ⇝ line after | sound by | solkey |
|---|---|---|---|
| `lit r i` | a literal law in the right-hand sides of the update at spine position `i`, any modality | `Upd.rwC_apply_eq` (iff) | `add_literals`, `leq_literals`, … |
| `lawUpd r ht i` | a term taclet (`TermTaclet`) onto a literal, in the box update at `i` | `holds_upd_rwC` | `updRw` |
| `applyOnRigid i s` | `{U}(A ∧ B)`, `{U}(a → B)`, `{U}¬a`, `{U}a` with `a` first-order: `U` applied to the first-order parts (`Fml.substU`), kept in front of the rest; `U` at `i`, cannot halt or under the box | `Fml.pushS_sound` | `applyOnRigidFormula` |
| `applyStorageBox i s` | `applyOnRigid` where `U` is a box update of the storage and locals (`Fml.pushStAt`) | `Fml.pushS_sound` | `applyOnRigidFormula` (`applyStorageBox`) |
| `concrete n s` | `true ∧ A ⇝ A`, `false → A ⇝ true`, `v ≐ v ⇝ true`, … below `n` updates | `Fml.concreteAlongS_holds` (iff) | `concrete_*`, `eqClose` |
| `litEq r n s`, `lawEq r n s` | a literal law or a term taclet (`TermTaclet`) in the equations along the skeleton `s` below `n` updates: a whole side, and in `defined(…)` for a literal law | `Fml.lawAlongS_holds` (iff) | `add_literals`, …, a term taclet's `\find` on an equation's side |
| `mergeIn p n` | the `n + 1` updates at the end of the path `p` (through `∧`, the right of `→`, updates and binders) merged | `Fml.mergeRun_leads` | `sequentialToParallel2` |
| `stateMerge r i` | the update at `i` merged with the next over its storage or memory write (`MergeNameS`) | `MergeNameS.top_sound` | `sequentialToParallel2` |
| `applyOnPV i s` | `{U}(x ≐ c → A) ⇝ {U}(v ≐ c → A)`, `U` leaving the literal `v` in `x`, in the atoms along `s` | `Fml.applyOnPVTop_sound` | `applyOnPV` |
| `simplifyUpdate i b` | the update at `i` without what it pops later (the box) and its shadowed writes (`Upd.simpS`), the scope ends after it merged in first where `b` | `Fml.simpAtB_holds` | `simplifyUpdate1/2/3` |

`sequentialToParallel` while the program is open is `Calculus/Merge.lean`'s.

**Where.**  The spine of a line is its updates, through its quantifiers and
hidden binders (`Fml.belowS`, as `Fml.mergeAt` walks it): a rewrite of an
update names its position, a fold the number of updates above it.  Under a
branch a rewrite follows the line's propositional skeleton (`Skel`, below),
which the elaborator computes from the line
with its postconditions in slots (`Fml.skelS`): a postcondition variable,
a program, a quantifier is a part the rewrite never looks at, so the
kernel computes it past them by `rfl`.

These functions run once a link, not once a step, and use `match` on the
indexed families, against Gate G0's first condition: an exemption, as
`Calculus/Merge.lean`'s merge is (decision 92, and proposal 104 for the
walks W7 added: `Fml.lawAlongS`, `Fml.lawFiresS`, `Fml.lawAtom`, `Fml.lawAtomFires`,
`Fml.stepIn`, `Fml.atPath`, `Tm.litPV`, `Tm.litPVFires`, `Fml.litPVAlong`,
`Fml.litPVFires`, `Fml.applyOnPVTop`).  What `sol_upd` and `sol_merge`
run on a whole leaf (`Upd.simpS`, `Fml.mergeB`) is
`Calculus/UpdRuleScoped.lean`'s, by the recursor.
-/

namespace Solidity

open Solidity (Srt Op0 Modality)
open Semantics (Value)
open Theory Theory.StValue

/-! ## The skeleton of a line -/

/-- The propositional skeleton of a formula, as the elaborator reads it off
a line: a connective, a literal leaf (`true`, `a ≐ b`, `defined(t)`), an
update with the skeleton under it, or a part not looked at — a
postcondition variable, a program, a quantifier, a `havoc`.  A connective
carries whether each of its parts, once rewritten, may be a formula not to
look at (`lo`, `ro`, `o`), which the folds of `concrete` read before
testing a part for `true` or `false`. -/
inductive Skel where
  | opaque
  | lit
  | and (lo ro : Bool) (l r : Skel)
  | imp (lo ro : Bool) (l r : Skel)
  | not (o : Bool) (s : Skel)
  | upd (s : Skel)
  deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

/-- A connective. -/
def Skel.isConn : Skel → Bool
  | .and .. | .imp .. | .not .. => true
  | _ => false

/-- A connective somewhere, through the updates: a rewrite under a branch
has somewhere to act. -/
def Skel.hasConn : Skel → Bool
  | .and .. | .imp .. | .not .. => true
  | .upd s => s.hasConn
  | _ => false

/-- A literal leaf or a connective somewhere: a fold or a literal law has
somewhere to act. -/
def Skel.hasLit : Skel → Bool
  | .lit | .and .. | .imp .. | .not .. => true
  | .upd s => s.hasLit
  | .opaque => false

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

variable {Γ : Ctx} {q : Tm C [] .val × Tm C [] .val}

/-- Whether `Tm.rwC` rewrites something in `t`. -/
abbrev Tm.hasC (q : Tm C [] .val × Tm C [] .val) {s : Srt} (t : Tm C Γ s) : Bool :=
  Tm.hasBy (Tm.pickClosed q) t

/-- Whether `Upd.rwC` rewrites something. -/
abbrev Upd.hasC (q : Tm C [] .val × Tm C [] .val) {Δ : Ctx} (U : Upd C Γ Δ) : Bool :=
  Upd.hasBy (Tm.pickClosed q) U

/-- Two closed terms that return alike in every state: a literal law's. -/
def Tm.EvalEq (t t' : Tm C [] .val) : Prop := ∀ σ : EState C [], t.eval σ = t'.eval σ

theorem Tm.pickClosed_eq (hq : Tm.EvalEq q.1 q.2) (σ : EState C Γ) :
    PickEq (Tm.pickClosed q) σ := fun h => by
  obtain ⟨rfl, hc, rfl⟩ := Tm.pickClosed_some h
  show (Tm.ofNil q.2).eval σ = _
  rw [Tm.eval_ofNil σ, Tm.eval_closedAs hc σ, hq]

/-- **An exact law keeps what every term returns.** -/
theorem Tm.rwC_eval_eq (hq : Tm.EvalEq q.1 q.2) (σ : EState C Γ) {s : Srt} (t : Tm C Γ s) :
    (t.rwC q).eval σ = t.eval σ :=
  Tm.rwBy_eval_eq σ (Tm.pickClosed_eq hq σ) t

/-- **An exact law keeps where every update ends.** -/
theorem Upd.rwC_apply_eq (hq : Tm.EvalEq q.1 q.2) (σ₀ : EState C Γ) {Δ : Ctx} (U : Upd C Γ Δ) :
    (U.rwC q).apply σ₀ = U.apply σ₀ :=
  Upd.rwBy_apply_eq σ₀ (Tm.pickClosed_eq hq σ₀) U

theorem holds_upd_rwC_iff (hq : Tm.EvalEq q.1 q.2) {m : Modality} {Δ : Ctx} {U : Upd C Γ Δ}
    {φ : Fml C Δ} (σ : State C Γ) : holds σ (.upd m (U.rwC q) φ) ↔ holds σ (.upd m U φ) := by
  show Modality.afterC m _ ((U.rwC q).apply σ.erase) ↔ Modality.afterC m _ (U.apply σ.erase)
  rw [Upd.rwC_apply_eq hq]

end Laws

/-- An exact law in the update's right-hand sides, under any modality. -/
def Fml.updRwEq (q : Tm C [] .val × Tm C [] .val) {Γ Δ : Ctx} (m : Modality)
    (U : Upd C Γ Δ) (φ : Fml C Δ) : Option (Fml C Γ) :=
  if U.hasC q then some (.upd m (U.rwC q) φ) else none

/-- A law in the right-hand sides of a box update. -/
def Fml.updRwBox (q : Tm C [] .val × Tm C [] .val) {Γ Δ : Ctx} :
    Modality → Upd C Γ Δ → Fml C Δ → Option (Fml C Γ)
  | .box, U, φ => if U.hasC q then some (.upd .box (U.rwC q) φ) else none
  | .diamond, _, _ => none

namespace FmlRw

/-- **A literal law** (`add_literals`, …) in the right-hand sides of the
update at position `i`, under any modality: it is exact. -/
def lit {t t' : Tm C [] .val} (r : LitLaw t t') (i : Nat) : FmlRw C :=
  FmlRw.atSpine (fun m U φ => Fml.updRwEq (t, t') m U φ)
    (fun {_ _ m U φ ψ} h σ hψ => by
      dsimp only [Fml.updRwEq] at h
      split at h
      · cases h; exact (holds_upd_rwC_iff (q := (t, t')) r.evalEq σ).1 hψ
      · cases h) i

/-- **A term taclet** onto a literal, in the right-hand sides of the box
update at position `i` (solkey's `updRw`). -/
def lawUpd {t t' : Tm C [] .val} (r : TermTaclet t t') (ht : t'.isLit = true) (i : Nat) :
    FmlRw C :=
  FmlRw.atSpine (fun m U φ => Fml.updRwBox (t, t') m U φ) (fun {_ _ m U φ ψ} h σ hψ => by
    cases m with
    | diamond => cases h
    | box =>
      dsimp only [Fml.updRwBox] at h
      split at h
      · cases h; exact holds_upd_rwC (q := (t, t')) (Tm.EvalRefines.of_theq r.sound ht) σ hψ
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

/-- `applyOnRigid` on a box update that writes no global part but the
storage (`Upd.stOnly`): storage writes and locals.  Wider than
`applyStorageBox` past the program (`Calculus/RewritePast.lean`), which
asks a lone `{storage := s}`, so the same link may apply while the program
is open and be refused past it (proposal 105). -/
def Fml.pushStAt (s : Skel) {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) :
    Option (Fml C Γ) :=
  if (m.isBoxS && U.stOnly) = true then Fml.pushAt s m U φ else none

theorem Fml.pushStAt_sound {s : Skel} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ}
    {ψ : Fml C Γ} (h : Fml.pushStAt s m U φ = some ψ) (σ : State C Γ) (hψ : holds σ ψ) :
    holds σ (.upd m U φ) := by
  unfold Fml.pushStAt at h
  split at h
  · exact Fml.pushAt_sound h σ hψ
  · cases h

/-- **`applyStorageBox`** at position `i` of the spine, along the skeleton
`s`: `applyOnRigid` where the update is a box update of the storage and
locals only (`Fml.pushStAt`). -/
def FmlRw.applyStorageBox (i : Nat) (s : Skel) : FmlRw C :=
  FmlRw.atSpine (fun m U φ => Fml.pushStAt s m U φ) (fun h σ hψ => Fml.pushStAt_sound h σ hψ) i

/-! ## A law in the line's equations

A law read in the atoms along the skeleton (`Skel`): a whole side of an
equation that is its left side (`Tm.sideC`, the Theory's equation,
`Tm.Theq`), and, for an exact law (a literal law, `Tm.EvalEq`), every
closed occurrence in a `defined(…)` term (`Tm.rwC`).  Each is an
equivalence, so it applies at any position, negative ones included. -/

section LawEq

variable {Γ : Ctx}

/-- An atom with the law `q` read in it; `exact` for a law whose two sides
return alike. -/
def Fml.lawAtom (q : Tm C [] .val × Tm C [] .val) (exact : Bool) : Fml C Γ → Fml C Γ
  | .eq a b => .eq (a.sideC q) (b.sideC q)
  | .defined t => if exact then .defined (t.rwC q) else .defined t
  | φ => φ

/-- Whether `Fml.lawAtom` rewrites something. -/
def Fml.lawAtomFires (q : Tm C [] .val × Tm C [] .val) (exact : Bool) : Fml C Γ → Bool
  | .eq a b => a.closedAs q.1 || b.closedAs q.1
  | .defined t => exact && t.hasC q
  | _ => false

/-- The law `q` in the atoms along the skeleton `s`. -/
def Fml.lawAlongS (q : Tm C [] .val × Tm C [] .val) (exact : Bool) :
    {Γ : Ctx} → Skel → Fml C Γ → Fml C Γ
  | _, .lit, φ => Fml.lawAtom q exact φ
  | _, .and _ _ l r, .and a b => .and (Fml.lawAlongS q exact l a) (Fml.lawAlongS q exact r b)
  | _, .imp _ _ l r, .imp a b => .imp (Fml.lawAlongS q exact l a) (Fml.lawAlongS q exact r b)
  | _, .not _ s, .not a => .not (Fml.lawAlongS q exact s a)
  | _, .upd s, .upd m U ψ => .upd m U (Fml.lawAlongS q exact s ψ)
  | _, _, φ => φ

/-- Whether `Fml.lawAlongS` rewrites something. -/
def Fml.lawFiresS (q : Tm C [] .val × Tm C [] .val) (exact : Bool) :
    {Γ : Ctx} → Skel → Fml C Γ → Bool
  | _, .lit, φ => Fml.lawAtomFires q exact φ
  | _, .and _ _ l r, .and a b => Fml.lawFiresS q exact l a || Fml.lawFiresS q exact r b
  | _, .imp _ _ l r, .imp a b => Fml.lawFiresS q exact l a || Fml.lawFiresS q exact r b
  | _, .not _ s, .not a => Fml.lawFiresS q exact s a
  | _, .upd s, .upd _ _ ψ => Fml.lawFiresS q exact s ψ
  | _, _, _ => false

variable {q : Tm C [] .val × Tm C [] .val} {exact : Bool}

theorem Fml.lawAtom_holds (hq : Tm.Theq q.1 q.2) (hx : exact = true → Tm.EvalEq q.1 q.2)
    (φ : Fml C Γ) (σ : State C Γ) : holds σ (Fml.lawAtom q exact φ) ↔ holds σ φ := by
  cases φ with
  | eq a b =>
    show Equiv ((a.sideC q).denote σ.erase) ((b.sideC q).denote σ.erase) ↔
      Equiv (a.denote σ.erase) (b.denote σ.erase)
    have ha := Tm.sideC_denote hq σ.erase a
    have hb := Tm.sideC_denote hq σ.erase b
    exact ⟨fun h => (ha.symm.trans h).trans hb, fun h => (ha.trans h).trans hb.symm⟩
  | defined t =>
    cases exact with
    | false => exact Iff.rfl
    | true =>
      show (∃ x, (t.rwC q).eval σ.erase = .ok x) ↔ (∃ x, t.eval σ.erase = .ok x)
      rw [Tm.rwC_eval_eq (hx rfl)]
  | _ => exact Iff.rfl

/-- Two formulas alike in every state are alike after an update. -/
theorem holds_upd_congr {Δ : Ctx} {m : Modality} {U : Upd C Γ Δ} {ψ ψ' : Fml C Δ}
    (h : ∀ τ : State C Δ, holds τ ψ' ↔ holds τ ψ) (σ : State C Γ) :
    holds σ (.upd m U ψ') ↔ holds σ (.upd m U ψ) := by
  show Modality.afterC m _ (U.apply σ.erase) ↔ Modality.afterC m _ (U.apply σ.erase)
  have key : (fun τ => ∀ σ' : State C Δ, σ'.erase = τ → σ.H <+: σ'.H → holds σ' ψ') =
      (fun τ => ∀ σ' : State C Δ, σ'.erase = τ → σ.H <+: σ'.H → holds σ' ψ) :=
    funext fun _ => propext (forall_congr' fun σ' => imp_congr_right fun _ =>
      imp_congr_right fun _ => h σ')
  rw [key]

/-- **A law along the skeleton keeps what the line says.** -/
theorem Fml.lawAlongS_holds (hq : Tm.Theq q.1 q.2) (hx : exact = true → Tm.EvalEq q.1 q.2) :
    {Γ : Ctx} → (s : Skel) → (φ : Fml C Γ) → ∀ σ : State C Γ,
      (holds σ (Fml.lawAlongS q exact s φ) ↔ holds σ φ)
  | _, .lit, φ, σ => Fml.lawAtom_holds hq hx φ σ
  | _, .and _ _ l r, .and a b, σ =>
    and_congr (Fml.lawAlongS_holds hq hx l a σ) (Fml.lawAlongS_holds hq hx r b σ)
  | _, .imp _ _ l r, .imp a b, σ =>
    imp_congr (Fml.lawAlongS_holds hq hx l a σ) (Fml.lawAlongS_holds hq hx r b σ)
  | _, .not _ s, .not a, σ => not_congr (Fml.lawAlongS_holds hq hx s a σ)
  | _, .upd s, .upd _ _ ψ, σ => holds_upd_congr (fun τ => Fml.lawAlongS_holds hq hx s ψ τ) σ
  | _, .and .., .tt, _ | _, .and .., .eq .., _ | _, .and .., .defined _, _
  | _, .and .., .not _, _ | _, .and .., .imp .., _ | _, .and .., .upd .., _
  | _, .and .., .modal .., _ | _, .and .., .havoc _, _ | _, .and .., .all .., _
  | _, .and .., .bind .., _ | _, .and .., .anon .., _
  | _, .imp .., .tt, _ | _, .imp .., .eq .., _ | _, .imp .., .defined _, _
  | _, .imp .., .not _, _ | _, .imp .., .and .., _ | _, .imp .., .upd .., _
  | _, .imp .., .modal .., _ | _, .imp .., .havoc _, _ | _, .imp .., .all .., _
  | _, .imp .., .bind .., _ | _, .imp .., .anon .., _
  | _, .not .., .tt, _ | _, .not .., .eq .., _ | _, .not .., .defined _, _
  | _, .not .., .and .., _ | _, .not .., .imp .., _ | _, .not .., .upd .., _
  | _, .not .., .modal .., _ | _, .not .., .havoc _, _ | _, .not .., .all .., _
  | _, .not .., .bind .., _ | _, .not .., .anon .., _
  | _, .upd _, .tt, _ | _, .upd _, .eq .., _ | _, .upd _, .defined _, _
  | _, .upd _, .not _, _ | _, .upd _, .and .., _ | _, .upd _, .imp .., _
  | _, .upd _, .modal .., _ | _, .upd _, .havoc _, _ | _, .upd _, .all .., _
  | _, .upd _, .bind .., _ | _, .upd _, .anon .., _
  | _, .opaque, _, _ => Iff.rfl

/-- The law along the skeleton, where it rewrites something. -/
def Fml.lawOnS (q : Tm C [] .val × Tm C [] .val) (exact : Bool) (s : Skel) (φ : Fml C Γ) :
    Option (Fml C Γ) :=
  if Fml.lawFiresS q exact s φ then some (Fml.lawAlongS q exact s φ) else none

theorem Fml.lawOnS_sound (hq : Tm.Theq q.1 q.2) (hx : exact = true → Tm.EvalEq q.1 q.2)
    {s : Skel} {φ ψ : Fml C Γ} (h : Fml.lawOnS q exact s φ = some ψ) (σ : State C Γ)
    (hψ : holds σ ψ) : holds σ φ := by
  unfold Fml.lawOnS at h
  split at h
  · cases h; exact (Fml.lawAlongS_holds hq hx s φ σ).1 hψ
  · cases h

end LawEq

namespace FmlRw

/-- **A literal law** in the equations along the skeleton `s` below `n`
updates of the spine: a whole side of an equation, and every closed
occurrence in a `defined(…)` term. -/
def litEq {t t' : Tm C [] .val} (r : LitLaw t t') (n : Nat) (s : Skel) : FmlRw C :=
  FmlRw.below (fun φ => Fml.lawOnS (t, t') true s φ)
    (fun h σ hψ => Fml.lawOnS_sound (q := (t, t')) r.theq (fun _ => r.evalEq) h σ hψ) n

/-- **A term taclet** in the equations along the skeleton `s` below `n`
updates of the spine: a whole side of an equation (solkey's `\find` on an
equation's side). -/
def lawEq {t t' : Tm C [] .val} (r : TermTaclet t t') (n : Nat) (s : Skel) : FmlRw C :=
  FmlRw.below (fun φ => Fml.lawOnS (t, t') false s φ)
    (fun h σ hψ => Fml.lawOnS_sound (q := (t, t')) r.sound (fun h => absurd h Bool.false_ne_true)
      h σ hψ) n

end FmlRw

/-! ## `sequentialToParallel` under a branch

The merge of `Calculus/Merge.lean` at a position of the line below its
spine, reached along a path the elaborator reads off the line: through a
conjunction, the right of an implication, an update, a quantifier or a
hidden binder, the positive positions, where a one-way rewrite gives the
line (`ChainBranches`' `LineRw.mergeIn` on the erasure). -/

/-- A step of a path into a line. -/
inductive PathStep where
  | andL | andR | impR | upd | binder
  deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

/-- `g` one step in, along `d`. -/
def Fml.stepIn (d : PathStep) (g : {Γ : Ctx} → Fml C Γ → Option (Fml C Γ)) :
    {Γ : Ctx} → Fml C Γ → Option (Fml C Γ)
  | _, φ => match d, φ with
    | .andL, .and a b => (g a).map (.and · b)
    | .andR, .and a b => (g b).map (.and a ·)
    | .impR, .imp a b => (g b).map (.imp a ·)
    | .upd, .upd m U ψ => (g ψ).map (.upd m U ·)
    | .binder, .all x q ψ => (g ψ).map (.all x q ·)
    | .binder, .bind m x t ψ => (g ψ).map (.bind m x t ·)
    | _, _ => none

/-- `f` at the end of the path `p`. -/
def Fml.atPath (f : {Γ : Ctx} → Fml C Γ → Option (Fml C Γ)) :
    List PathStep → {Γ : Ctx} → Fml C Γ → Option (Fml C Γ)
  | [], _, φ => f φ
  | d :: p, _, φ => Fml.stepIn d (Fml.atPath f p) φ

theorem Fml.stepIn_sound {d : PathStep} {g : {Γ : Ctx} → Fml C Γ → Option (Fml C Γ)}
    (hg : ∀ {Γ : Ctx} {φ ψ : Fml C Γ}, g φ = some ψ → ∀ σ, holds σ ψ → holds σ φ)
    {Γ : Ctx} {φ ψ : Fml C Γ} (h : Fml.stepIn d g φ = some ψ) (σ : State C Γ)
    (hψ : holds σ ψ) : holds σ φ := by
  cases d <;> cases φ <;> simp only [Fml.stepIn, reduceCtorEq] at h
  · obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨hg ha σ hψ.1, hψ.2⟩
  · obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨hψ.1, hg hb σ hψ.2⟩
  · obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun ha => hg hb σ (hψ ha)
  · obtain ⟨ψ', hψ', rfl⟩ := Option.map_eq_some_iff.1 h
    exact holds_upd_mono (fun τ => hg hψ' τ) σ hψ
  · obtain ⟨ψ', hψ', rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun v => hg hψ' _ (hψ v)
  · obtain ⟨ψ', hψ', rfl⟩ := Option.map_eq_some_iff.1 h
    exact Modality.forallB_imp (fun _ h => hg hψ' _ h) hψ

theorem Fml.atPath_sound {f : {Γ : Ctx} → Fml C Γ → Option (Fml C Γ)}
    (hf : ∀ {Γ : Ctx} {φ ψ : Fml C Γ}, f φ = some ψ → ∀ σ, holds σ ψ → holds σ φ) :
    (p : List PathStep) → {Γ : Ctx} → {φ ψ : Fml C Γ} → Fml.atPath f p φ = some ψ →
      ∀ σ, holds σ ψ → holds σ φ
  | [], _, _, _, h => hf h
  | _ :: p, _, _, _, h => Fml.stepIn_sound (fun h' => Fml.atPath_sound hf p h') h

/-- **`sequentialToParallel` under a branch**: the `n + 1` updates at the
end of the path `p` merged into one (`Fml.mergeRun`). -/
def FmlRw.mergeIn (p : List PathStep) (n : Nat) : FmlRw C :=
  ⟨fun φ => Fml.atPath (fun ψ => ψ.mergeRun 0 n) p φ,
    fun h σ hψ => Fml.atPath_sound (fun h' σ' => Fml.mergeRun_leads 0 n _ h' σ') p h σ hψ⟩

/-- **A merge over a storage or memory write** (`Calculus/StatePartsScoped.lean`:
`{L ‖ storage := S}{V}`, `{memory := M}{V}`, `{L ‖ memory := M}{V}`) at
position `i` of the spine. -/
def FmlRw.stateMerge (r : MergeNameS) (i : Nat) : FmlRw C :=
  FmlRw.atSpine (fun m U φ => r.top m U φ) (fun h σ hψ => r.top_sound _ _ _ _ h σ hψ) i

/-! ## A local's literal under its update: `applyOnPV`

KeY's `applyOnPV` reads a program variable behind an update as the update
binds it, `{x := v} x ⇝ v`, where the update cannot be applied whole
(it writes the storage, or halts): a local the update leaves holding a
literal (`Upd.held`) is that literal in the atoms along the skeleton
below it (not past a further update), the update kept in front.  Wherever
the update returns, the state it leaves holds the literal there
(`Upd.held_ok`); where it halts nothing below it is read. -/

section ApplyOnPV

variable {Γ Δ : Ctx}

/-- The literal a local holds after an update, if it holds one. -/
def Held.litVal? {p : PrimTy} : Held C Γ (.val p) → Option Semantics.Value
  | .rhs (.val t) => t.litVal?
  | _ => none

theorem Tm.litVal?_eval {Γ : Ctx} (σ : EState C Γ) :
    (t : Tm C Γ .val) → {v : Semantics.Value} → t.litVal? = some v → t.eval σ = .ok v
  | .app0 (.lit _), _, h => by cases h; rfl
  | .pvV _, _, h | .netOf .., _, h | .app1 .., _, h | .app2 .., _, h | .app3 .., _, h => by
    cases h
  | .app0 (.env _), _, h => by cases h

/-- A local holding a literal after an update holds it in the state the
update leaves. -/
theorem Held.litVal?_get {σ₀ : EState C Γ} {σ₁ : EState C Δ} {p : PrimTy} {i : Idx Δ (.val p)}
    {x : Held C Γ (.val p)} (hok : Held.OK σ₀ σ₁ i x) {v : Semantics.Value}
    (h : x.litVal? = some v) : Env.get i σ₁.env = v := by
  cases x with
  | pos j => cases h
  | rhs r =>
    cases r with
    | val t =>
      have hok : t.eval σ₀ = .ok (Env.get i σ₁.env) := hok
      rw [Tm.litVal?_eval σ₀ t h] at hok
      exact (Except.ok.inj hok).symm

/-- A term with each value local `s` leaves holding a literal read as it. -/
def Tm.litPV (s : Subst C Γ Δ) : {k : Srt} → Tm C Δ k → Tm C Δ k
  | _, .pvV i => match (s i).litVal? with
    | some v => .app0 (.lit v)
    | none => .pvV i
  | _, .netOf i a => .netOf i (Tm.litPV s a)
  | _, .app1 o ho x => .app1 o ho (Tm.litPV s x)
  | _, .app2 o x y => .app2 o (Tm.litPV s x) (Tm.litPV s y)
  | _, .app3 o x y z => .app3 o (Tm.litPV s x) (Tm.litPV s y) (Tm.litPV s z)
  | _, t => t

/-- Whether `Tm.litPV` reads a local as a literal in the term. -/
def Tm.litPVFires (s : Subst C Γ Δ) : {k : Srt} → Tm C Δ k → Bool
  | _, .pvV i => ((s i).litVal?).isSome
  | _, .netOf _ a => Tm.litPVFires s a
  | _, .app1 _ _ x => Tm.litPVFires s x
  | _, .app2 _ x y => Tm.litPVFires s x || Tm.litPVFires s y
  | _, .app3 _ x y z => Tm.litPVFires s x || Tm.litPVFires s y || Tm.litPVFires s z
  | _, _ => false

/-- **A local read as the literal it holds** reads and denotes as before. -/
theorem Tm.litPV_eq {s : Subst C Γ Δ} {σ₀ : EState C Γ} {τ : EState C Δ}
    (hok : ∀ {t : LTy} (i : Idx Δ t), Held.OK σ₀ τ i (s i)) :
    {k : Srt} → (t : Tm C Δ k) → (t.litPV s).eval τ = t.eval τ ∧ (t.litPV s).denote τ = t.denote τ
  | _, .pvV i => by
    simp only [Tm.litPV]
    split
    · rename_i v hv
      have hg := Held.litVal?_get (hok i) hv
      exact ⟨by rw [← hg]; rfl, by rw [← hg]; rfl⟩
    · exact ⟨rfl, rfl⟩
  | _, .netOf i a => by
    obtain ⟨he, hd⟩ := Tm.litPV_eq hok a
    exact ⟨by simp only [Tm.litPV, Tm.eval, he], by simp only [Tm.litPV, Tm.denote, hd]⟩
  | _, .app1 o ho x => by
    obtain ⟨he, hd⟩ := Tm.litPV_eq hok x
    exact ⟨by simp only [Tm.litPV, Tm.eval, he], by simp only [Tm.litPV, Tm.denote, hd]⟩
  | _, .app2 o x y => by
    obtain ⟨hex, hdx⟩ := Tm.litPV_eq hok x
    obtain ⟨hey, hdy⟩ := Tm.litPV_eq hok y
    exact ⟨by simp only [Tm.litPV, Tm.eval, hex, hey], by simp only [Tm.litPV, Tm.denote, hex, hey, hdx, hdy]⟩
  | _, .app3 o x y z => by
    obtain ⟨hex, hdx⟩ := Tm.litPV_eq hok x
    obtain ⟨hey, hdy⟩ := Tm.litPV_eq hok y
    obtain ⟨hez, hdz⟩ := Tm.litPV_eq hok z
    exact ⟨by simp only [Tm.litPV, Tm.eval, hex, hey, hez],
      by simp only [Tm.litPV, Tm.denote, hdx, hdy, hdz]⟩
  | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .app0 _ => ⟨rfl, rfl⟩

/-- The atoms along the skeleton `s`, not past an update, with the locals
`h` leaves holding a literal read as it. -/
def Fml.litPVAlong (h : Subst C Γ Δ) : Skel → Fml C Δ → Fml C Δ
  | .lit, .eq a b => .eq (a.litPV h) (b.litPV h)
  | .lit, .defined t => .defined (t.litPV h)
  | .and _ _ l r, .and a b => .and (Fml.litPVAlong h l a) (Fml.litPVAlong h r b)
  | .imp _ _ l r, .imp a b => .imp (Fml.litPVAlong h l a) (Fml.litPVAlong h r b)
  | .not _ s, .not a => .not (Fml.litPVAlong h s a)
  | _, φ => φ

/-- Whether `Fml.litPVAlong` reads a local as a literal. -/
def Fml.litPVFires (h : Subst C Γ Δ) : Skel → Fml C Δ → Bool
  | .lit, .eq a b => a.litPVFires h || b.litPVFires h
  | .lit, .defined t => t.litPVFires h
  | .and _ _ l r, .and a b | .imp _ _ l r, .imp a b =>
    Fml.litPVFires h l a || Fml.litPVFires h r b
  | .not _ s, .not a => Fml.litPVFires h s a
  | _, _ => false

theorem Fml.litPVAlong_holds {h : Subst C Γ Δ} {σ₀ : EState C Γ} (σ : State C Δ)
    (hok : ∀ {t : LTy} (i : Idx Δ t), Held.OK σ₀ σ.erase i (h i)) :
    (s : Skel) → (φ : Fml C Δ) → (holds σ (Fml.litPVAlong h s φ) ↔ holds σ φ)
  | .lit, .eq a b => by
    show Theory.StValue.Equiv ((a.litPV h).denote σ.erase) ((b.litPV h).denote σ.erase) ↔
      Theory.StValue.Equiv (a.denote σ.erase) (b.denote σ.erase)
    rw [(Tm.litPV_eq hok a).2, (Tm.litPV_eq hok b).2]
  | .lit, .defined t => by
    show (∃ x, (t.litPV h).eval σ.erase = .ok x) ↔ (∃ x, t.eval σ.erase = .ok x)
    rw [(Tm.litPV_eq hok t).1]
  | .and _ _ l r, .and a b =>
    and_congr (Fml.litPVAlong_holds σ hok l a) (Fml.litPVAlong_holds σ hok r b)
  | .imp _ _ l r, .imp a b =>
    imp_congr (Fml.litPVAlong_holds σ hok l a) (Fml.litPVAlong_holds σ hok r b)
  | .not _ s, .not a => not_congr (Fml.litPVAlong_holds σ hok s a)
  | .lit, .tt | .lit, .not _ | .lit, .and .. | .lit, .imp .. | .lit, .upd .. | .lit, .modal ..
  | .lit, .havoc _ | .lit, .all .. | .lit, .bind .. | .lit, .anon .. => Iff.rfl
  | .and .., .tt | .and .., .eq .. | .and .., .defined _ | .and .., .not _ | .and .., .imp ..
  | .and .., .upd .. | .and .., .modal .. | .and .., .havoc _ | .and .., .all ..
  | .and .., .bind .. | .and .., .anon .. => Iff.rfl
  | .imp .., .tt | .imp .., .eq .. | .imp .., .defined _ | .imp .., .not _ | .imp .., .and ..
  | .imp .., .upd .. | .imp .., .modal .. | .imp .., .havoc _ | .imp .., .all ..
  | .imp .., .bind .. | .imp .., .anon .. => Iff.rfl
  | .not .., .tt | .not .., .eq .. | .not .., .defined _ | .not .., .and .. | .not .., .imp ..
  | .not .., .upd .. | .not .., .modal .. | .not .., .havoc _ | .not .., .all ..
  | .not .., .bind .. | .not .., .anon .. => Iff.rfl
  | .upd _, _ | .opaque, _ => Iff.rfl

/-- `applyOnPV` under `{U}_m φ`, `φ` of skeleton `s`. -/
def Fml.applyOnPVTop (s : Skel) (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) :
    Option (Fml C Γ) :=
  if Fml.litPVFires U.held s φ then some (.upd m U (Fml.litPVAlong U.held s φ)) else none

theorem Fml.applyOnPVTop_sound {s : Skel} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ}
    {ψ : Fml C Γ} (h : Fml.applyOnPVTop s m U φ = some ψ) (σ : State C Γ) (hψ : holds σ ψ) :
    holds σ (.upd m U φ) := by
  unfold Fml.applyOnPVTop at h
  split at h
  · cases h
    show Modality.afterC m _ (U.apply σ.erase)
    have hψ : Modality.afterC m _ (U.apply σ.erase) := hψ
    cases hU : U.apply σ.erase with
    | error => rw [hU] at hψ; exact hψ
    | ok τ =>
      rw [hU] at hψ
      intro σ' he hx
      have hok : ∀ {t : LTy} (i : Idx Δ t), Held.OK σ.erase σ'.erase i (U.held i) := by
        rw [he]; exact Upd.held_ok U hU
      exact (Fml.litPVAlong_holds σ' hok s φ).1 (hψ σ' he hx)
  · cases h

end ApplyOnPV

/-- **`applyOnPV`** under the update at position `i` of the spine, along the
skeleton `s` of the formula under it. -/
def FmlRw.applyOnPV (i : Nat) (s : Skel) : FmlRw C :=
  FmlRw.atSpine (fun m U φ => Fml.applyOnPVTop s m U φ) (fun h σ hψ => Fml.applyOnPVTop_sound h σ hψ) i

/-! ## `simplifyUpdate` -/

/-- `simplifyUpdate` on `{U}_m φ` (`Fml.simpAt`), with the scope ends `φ`
begins with merged in first only where `absorb` says: the elaborator
(`scopedRwCands`) tries `absorb := false` first, and `absorb := true` only
where the line under `U` is an update (its skeleton `.upd _`), never a
postcondition the kernel cannot look into. -/
def Fml.simpAtB (absorb : Bool) {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) :
    Option (Fml C Γ) :=
  if absorb then Fml.simpAt m U φ
  else if (U.simpS m).size < U.size then some (.upd m (U.simpS m) φ) else none

theorem Fml.simpAtB_holds {absorb : Bool} {Γ Δ : Ctx} {m : Modality} {U : Upd C Γ Δ}
    {φ : Fml C Δ} {χ : Fml C Γ} (h : Fml.simpAtB absorb m U φ = some χ) (σ : State C Γ)
    (hχ : holds σ χ) : holds σ (.upd m U φ) := by
  unfold Fml.simpAtB at h
  split at h
  · exact Fml.simpAt_holds h σ hχ
  · split at h
    · cases h; exact holds_upd_simpS σ hχ
    · cases h

/-- **`simplifyUpdate`** on the update at position `i` of the spine: what
it pops later, under the box, and the writes a later one shadows dropped
(`Upd.simpS`), the scope ends after it merged in first where `absorb`. -/
def FmlRw.simplifyUpdate (i : Nat) (absorb : Bool) : FmlRw C :=
  FmlRw.atSpine (fun m U φ => Fml.simpAtB absorb m U φ) (fun h σ hψ => Fml.simpAtB_holds h σ hψ) i

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
