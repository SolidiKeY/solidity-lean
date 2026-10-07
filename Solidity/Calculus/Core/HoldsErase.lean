import Solidity.Calculus.Core.Logic
import Solidity.Semantics.RunErase

/-!
# A scoped formula holds where its erasure does

`holds_erase` (`docs/intrinsic.md`, M6a): a scoped formula holds in `σ`
exactly where its erasure (`Fml.erase`, `Calculus/Core/Fml.lean`) holds,
by `Update.lean`'s `holds`, in any untyped state that agrees with `σ` on the
locals named `ns` (`Agree`, `Semantics/RunErase.lean`).  The pieces:

* a term reads alike (`Tm.eval_erase`): a value, a path, an identity the
  same, a storage or memory the same up to the locals the untyped state
  carries (`StEq`), since every symbol reads the global part only (the
  `*_nat`/`*_wl` lemmas of `Semantics/RunErase.lean`); it denotes the same
  (`Tm.denote_erase`);
* an update ends in agreeing states (`Upd.apply_erase`), a declaration under
  a fresh name;
* a modality's program is `run_erase`'s (`Prog.erasesAt`), its frames the
  statements they hold, a scope's end nothing (the untyped state keeps the
  popped locals, which `Agree` allows).

The formulas are `Fml.Plain`: every binder fresh (a declaration, a `∀`, a
block's locals: `Prog.Fresh`), and no hidden binder or anonymising update,
whose untyped readings range over more than the typed ones (the untyped
`anon` over every binding, the erased hidden binder over whatever the name
held before).
-/

namespace Solidity.Core

open Semantics (Value SVal MVal Seg Halt Res Binding lookupBy setBy)
open Solidity (Srt Op0 Op1 Op2 Op3 Modality)

variable {C : Contract}

/-! ## Readings alike -/

/-- Two global parts alike up to the locals they carry. -/
def StEq (s₁ s₂ : Semantics.State) : Prop := withLocals s₁ [] = withLocals s₂ []

theorem StEq.refl (s : Semantics.State) : StEq s s := rfl
theorem StEq.symm {s₁ s₂ : Semantics.State} (h : StEq s₁ s₂) : StEq s₂ s₁ := Eq.symm h
theorem StEq.trans {s₁ s₂ s₃ : Semantics.State} (h : StEq s₁ s₂) (h' : StEq s₂ s₃) : StEq s₁ s₃ :=
  Eq.trans h h'

theorem StEq.wl (s : Semantics.State) (e e' : List (Var × Binding)) :
    StEq (withLocals s e) (withLocals s e') := rfl

/-- A state is its global part with its locals. -/
theorem wl_env (s : Semantics.State) : withLocals (withLocals s []) s.env = s := rfl

/-- Two outcomes alike: the same halt, or related results. -/
def Res.Rel {α β : Type} (R : α → β → Prop) : Res α → Res β → Prop
  | .ok a, .ok b => R a b
  | .error e, .error e' => e = e'
  | _, _ => False

theorem Res.Rel.of_eq {α : Type} {R : α → α → Prop} (hR : ∀ a, R a a) {x y : Res α} (h : x = y) :
    Res.Rel R x y := by
  subst h; cases x <;> simp only [Res.Rel, hR]

theorem Res.Rel.bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {x : Res α} {y : Res β}
    (h : Res.Rel R x y) {f : α → Res γ} {g : β → Res δ} (hfg : ∀ a b, R a b → Res.Rel S (f a) (g b)) :
    Res.Rel S (x >>= f) (y >>= g) := by
  cases x with
  | ok a => cases y with
    | ok b => exact hfg a b h
    | error => exact h.elim
  | error e => cases y with
    | ok => exact h.elim
    | error e' => exact h

theorem Res.Rel.map {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {x : Res α} {y : Res β}
    (h : Res.Rel R x y) {f : α → γ} {g : β → δ} (hfg : ∀ a b, R a b → S (f a) (g b)) :
    Res.Rel S (f <$> x) (g <$> y) := by
  cases x with
  | ok a => cases y with
    | ok b => exact hfg a b h
    | error => exact h.elim
  | error e => cases y with
    | ok => exact h.elim
    | error e' => exact h

/-- How a term's reading is alike: a storage or a memory up to the locals,
anything else the same. -/
def Srt.EvRel : (s : Srt) → s.Ev → s.Ev → Prop
  | .st, x, y => Res.Rel StEq x y
  | .mem, x, y => Res.Rel StEq x y
  | .val, x, y => x = y
  | .path, x, y => x = y
  | .sv, x, y => x = y
  | .ident, x, y => x = y
  | .addr, x, y => x = y
  | .mv, x, y => x = y

/-- An operation on the global part, natural in the locals, does alike on
alike parts. -/
theorem Natural.rel {f : Semantics.State → Res Semantics.State} (hf : Natural f)
    {s₁ s₂ : Semantics.State} (h : StEq s₁ s₂) : Res.Rel StEq (f s₁) (f s₂) := by
  have h₁ : f s₁ = (fun s' => withLocals s' s₁.env) <$> f (withLocals s₁ []) := hf (withLocals s₁ []) s₁.env
  have h₂ : f s₂ = (fun s' => withLocals s' s₂.env) <$> f (withLocals s₂ []) := hf (withLocals s₂ []) s₂.env
  rw [h₁, h₂, show withLocals s₁ [] = withLocals s₂ [] from h]
  cases f (withLocals s₂ []) with
  | error => rfl
  | ok u => exact StEq.wl u _ _

theorem NaturalA.rel {α : Type} {f : Semantics.State → Res (Semantics.State × α)} (hf : NaturalA f)
    {s₁ s₂ : Semantics.State} (h : StEq s₁ s₂) :
    Res.Rel (fun a b => StEq a.1 b.1 ∧ a.2 = b.2) (f s₁) (f s₂) := by
  have h₁ : f s₁ = (fun p => (withLocals p.1 s₁.env, p.2)) <$> f (withLocals s₁ []) := hf (withLocals s₁ []) s₁.env
  have h₂ : f s₂ = (fun p => (withLocals p.1 s₂.env, p.2)) <$> f (withLocals s₂ []) := hf (withLocals s₂ []) s₂.env
  rw [h₁, h₂, show withLocals s₁ [] = withLocals s₂ [] from h]
  cases f (withLocals s₂ []) with
  | error => rfl
  | ok u => exact ⟨StEq.wl u.1 _ _, rfl⟩

/-- A reading of the global part reads alike parts alike. -/
theorem StEq.read {α : Type} {f : Semantics.State → α}
    (hf : ∀ s e, f (withLocals s e) = f s) {s₁ s₂ : Semantics.State} (h : StEq s₁ s₂) :
    f s₁ = f s₂ := by
  have h₁ : f s₁ = f (withLocals s₁ []) := hf (withLocals s₁ []) s₁.env
  have h₂ : f s₂ = f (withLocals s₂ []) := hf (withLocals s₂ []) s₂.env
  rw [h₁, h₂]
  exact congrArg f h

end Solidity.Core
