import Solidity.Calculus.Graft
import Solidity.Calculus.TermLib

/-!
# A Theory equation in a scoped sequent, read on its scoped terms

A rewrite of a scoped sequent by a term taclet (`TermTaclet`,
`Calculus/TermLib.lean`) or a Theory equation (`Tm.Theq`): `q = (t, t')`, two
closed value terms at the empty scope.  A term of the sequent is `t` where it
has no local and reads `t` at the empty scope (`Tm.closedAs`: `Tm.toNil?`,
compared by `Tm.beqR`); it becomes `t'` read at its scope (`Tm.ofNil`).  A
closed term reads what it reads at the empty scope over the same global
part (`Tm.eval_toNilS`, `Tm.denote_ofNil`, the state's global part
`EState.nil`), so nothing below reads the closer's terms or the erasure.

*In an equation*: a side of an equation that is `t` becomes `t'`
(`Tm.sideC`), in every equation of the formula, at any depth of its
connectives, updates, quantifiers and hidden binders, and in the
postcondition of a modality still open (`Fml.rwEqC`).  A Theory equation
holds in every state (`Tm.Theq`), so the formula rewritten holds exactly
where it does (`Fml.rwEqC_holds`): under a modality, in every state its
program ends in.  An update's right-hand sides and a `defined` are not
rewritten there: they are read by the interpreter, which a Theory equation
does not preserve.  `Proves.rewrite` (`Calculus/Proves.lean`) rewrites the
context's preconditions and the goal at once (`Hyps.rwEqC`).

*In an update's right-hand sides* (`Proves.updRw`): every closed
occurrence of `t` becomes `t'` (`Tm.rwC`), where `t'` returns wherever `t`
does, the same value (`Tm.EvalRefines`: a Theory equation onto a literal,
`Tm.EvalRefines.of_theq`), and where the update returns, the rewritten one
returns the same state (`Upd.rwC_apply`).

The kernel unfolds `Fml.rwEqC` and `Hyps.rwEqC` where `Proves.rewrite'`
checks the rewritten sequent (`rfl`), so both are written by the
recursors (Gate G0, conditions 1 and 2), each with its `match` form as the
compiled twin (`Fml.rwEqCM`, `Hyps.rwEqCM`) and a link theorem; the
recursor's clauses are stated by hand (`Fml.rwEqC_not`, …), by `rfl`.
`Tm.toNil?`, `Tm.ofNil` and the update's rewrite use `match` (the
exemption of `Calculus/Graft.lean`'s functions): they run once a rule.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)
open Semantics (Res)
open Theory Theory.StValue

variable {C : Contract}

/-! ## Closed terms -/

section Closed

variable {Γ : Ctx}

/-- A term with no local, at the empty scope. -/
def Tm.toNil? : {s : Srt} → Tm C Γ s → Option (Tm C [] s)
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .netOf .. => none
  | _, .app0 o => some (.app0 o)
  | _, .app1 o ho x => (Tm.toNil? x).map (.app1 o ho)
  | _, .app2 o x y => do pure (.app2 o (← Tm.toNil? x) (← Tm.toNil? y))
  | _, .app3 o x y z => do pure (.app3 o (← Tm.toNil? x) (← Tm.toNil? y) (← Tm.toNil? z))

/-- A term at the empty scope, read at the scope `Γ`. -/
def Tm.ofNil : {s : Srt} → Tm C [] s → Tm C Γ s
  | _, .pvV i | _, .pvP i | _, .pvS i | _, .pvI i | _, .netOf i _ => nomatch i
  | _, .app0 o => .app0 o
  | _, .app1 o ho x => .app1 o ho (Tm.ofNil x)
  | _, .app2 o x y => .app2 o (Tm.ofNil x) (Tm.ofNil y)
  | _, .app3 o x y z => .app3 o (Tm.ofNil x) (Tm.ofNil y) (Tm.ofNil z)

/-- The state's global part, with no local. -/
def EState.nil (σ : EState C Γ) : EState C [] := σ.withEnv (Δ := []) ()

/-- Two states with one global part have one at the empty scope. -/
theorem EState.nil_eq_of_glob {Δ : Ctx} {σ : EState C Γ} {τ : EState C Δ} (h : σ.glob = τ.glob) :
    σ.nil = τ.nil := by
  cases σ; cases τ
  simp only [EState.glob, Semantics.State.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, -, rfl, rfl, rfl⟩ := h
  rfl

/-- `t` has no local and reads `q` at the empty scope. -/
def Tm.closedAs (t : Tm C Γ .val) (q : Tm C [] .val) : Bool :=
  match t.toNil? with
  | some t₀ => t₀.beqR q
  | none => false

/-- A closed term reads what it reads at the empty scope. -/
theorem Tm.eval_toNilS (σ : EState C Γ) : {s : Srt} → (t : Tm C Γ s) → {t₀ : Tm C [] s} →
    t.toNil? = some t₀ → t.eval σ = t₀.eval σ.nil
  | _, .pvV _, _, h | _, .pvP _, _, h | _, .pvS _, _, h | _, .pvI _, _, h | _, .netOf .., _, h =>
    nomatch h
  | _, .app0 o, _, h => by cases h; rfl
  | _, .app1 o ho x, _, h => by
    obtain ⟨x₀, hx, rfl⟩ := Option.map_eq_some_iff.1 h
    show o.eval σ.glob (x.eval σ) = o.eval σ.glob (x₀.eval σ.nil)
    rw [Tm.eval_toNilS σ x hx]
  | _, .app2 o x y, _, h => by
    obtain ⟨x₀, hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y₀, hy, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show o.eval σ.glob (x.eval σ) (y.eval σ) = o.eval σ.glob (x₀.eval σ.nil) (y₀.eval σ.nil)
    rw [Tm.eval_toNilS σ x hx, Tm.eval_toNilS σ y hy]
  | _, .app3 o x y z, _, h => by
    obtain ⟨x₀, hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y₀, hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z₀, hz, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show o.eval σ.glob (x.eval σ) (y.eval σ) (z.eval σ) =
      o.eval σ.glob (x₀.eval σ.nil) (y₀.eval σ.nil) (z₀.eval σ.nil)
    rw [Tm.eval_toNilS σ x hx, Tm.eval_toNilS σ y hy, Tm.eval_toNilS σ z hz]

/-- A closed term denotes what it denotes at the empty scope. -/
theorem Tm.denote_toNilS (σ : EState C Γ) : {s : Srt} → (t : Tm C Γ s) → {t₀ : Tm C [] s} →
    t.toNil? = some t₀ → t.denote σ = t₀.denote σ.nil
  | _, .pvV _, _, h | _, .pvP _, _, h | _, .pvS _, _, h | _, .pvI _, _, h | _, .netOf .., _, h =>
    nomatch h
  | _, .app0 o, _, h => by cases h; rfl
  | _, .app1 o ho x, _, h => by
    obtain ⟨x₀, hx, rfl⟩ := Option.map_eq_some_iff.1 h
    show o.denote σ.glob (x.denote σ) = o.denote σ.glob (x₀.denote σ.nil)
    rw [Tm.denote_toNilS σ x hx]
  | _, .app2 o x y, _, h => by
    obtain ⟨x₀, hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y₀, hy, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show o.denote σ.glob (x.eval σ) (y.eval σ) (x.denote σ) (y.denote σ) =
      o.denote σ.glob (x₀.eval σ.nil) (y₀.eval σ.nil) (x₀.denote σ.nil) (y₀.denote σ.nil)
    rw [Tm.denote_toNilS σ x hx, Tm.denote_toNilS σ y hy, Tm.eval_toNilS σ x hx,
      Tm.eval_toNilS σ y hy]
  | _, .app3 o x y z, _, h => by
    obtain ⟨x₀, hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y₀, hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z₀, hz, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show o.denote (x.denote σ) (y.denote σ) (z.denote σ) =
      o.denote (x₀.denote σ.nil) (y₀.denote σ.nil) (z₀.denote σ.nil)
    rw [Tm.denote_toNilS σ x hx, Tm.denote_toNilS σ y hy, Tm.denote_toNilS σ z hz]

/-- A term of the empty scope reads alike at any scope. -/
theorem Tm.eval_ofNil (σ : EState C Γ) : {s : Srt} → (t : Tm C [] s) → (Tm.ofNil t).eval σ = t.eval σ.nil
  | _, .pvV i | _, .pvP i | _, .pvS i | _, .pvI i | _, .netOf i _ => nomatch i
  | _, .app0 _ => rfl
  | _, .app1 o _ x => by
    show o.eval σ.glob ((Tm.ofNil x).eval σ) = o.eval σ.glob (x.eval σ.nil)
    rw [Tm.eval_ofNil σ x]
  | _, .app2 o x y => by
    show o.eval σ.glob ((Tm.ofNil x).eval σ) ((Tm.ofNil y).eval σ) =
      o.eval σ.glob (x.eval σ.nil) (y.eval σ.nil)
    rw [Tm.eval_ofNil σ x, Tm.eval_ofNil σ y]
  | _, .app3 o x y z => by
    show o.eval σ.glob ((Tm.ofNil x).eval σ) ((Tm.ofNil y).eval σ) ((Tm.ofNil z).eval σ) =
      o.eval σ.glob (x.eval σ.nil) (y.eval σ.nil) (z.eval σ.nil)
    rw [Tm.eval_ofNil σ x, Tm.eval_ofNil σ y, Tm.eval_ofNil σ z]

/-- A term of the empty scope denotes alike at any scope. -/
theorem Tm.denote_ofNil (σ : EState C Γ) : {s : Srt} → (t : Tm C [] s) →
    (Tm.ofNil t).denote σ = t.denote σ.nil
  | _, .pvV i | _, .pvP i | _, .pvS i | _, .pvI i | _, .netOf i _ => nomatch i
  | _, .app0 _ => rfl
  | _, .app1 o _ x => by
    show o.denote σ.glob ((Tm.ofNil x).denote σ) = o.denote σ.glob (x.denote σ.nil)
    rw [Tm.denote_ofNil σ x]
  | _, .app2 o x y => by
    show o.denote σ.glob ((Tm.ofNil x).eval σ) ((Tm.ofNil y).eval σ) ((Tm.ofNil x).denote σ)
        ((Tm.ofNil y).denote σ) =
      o.denote σ.glob (x.eval σ.nil) (y.eval σ.nil) (x.denote σ.nil) (y.denote σ.nil)
    rw [Tm.denote_ofNil σ x, Tm.denote_ofNil σ y, Tm.eval_ofNil σ x, Tm.eval_ofNil σ y]
  | _, .app3 o x y z => by
    show o.denote ((Tm.ofNil x).denote σ) ((Tm.ofNil y).denote σ) ((Tm.ofNil z).denote σ) =
      o.denote (x.denote σ.nil) (y.denote σ.nil) (z.denote σ.nil)
    rw [Tm.denote_ofNil σ x, Tm.denote_ofNil σ y, Tm.denote_ofNil σ z]

theorem Tm.closedAs_toNil {q : Tm C [] .val} {t : Tm C Γ .val} (h : t.closedAs q = true) :
    t.toNil? = some q := by
  unfold Tm.closedAs at h
  split at h
  · rename_i t₀ ht
    rw [ht, Tm.eq_of_beqR h]
  · cases h

theorem Tm.eval_closedAs {q : Tm C [] .val} {t : Tm C Γ .val} (h : t.closedAs q = true)
    (σ : EState C Γ) : t.eval σ = q.eval σ.nil :=
  Tm.eval_toNilS σ t (Tm.closedAs_toNil h)

theorem Tm.denote_closedAs {q : Tm C [] .val} {t : Tm C Γ .val} (h : t.closedAs q = true)
    (σ : EState C Γ) : t.denote σ = q.denote σ.nil :=
  Tm.denote_toNilS σ t (Tm.closedAs_toNil h)

end Closed

/-! ## The term bridge -/

section Bridge

open Semantics (bind_ok_inv)

variable {Γ : Ctx}

/-- **The term bridge** on scoped terms (`Theory/Bridge/Denote.lean`): a term's denotation agrees with its
reading wherever the reading returns. -/
theorem Tm.denote_eval (σ : EState C Γ) : {s : Srt} → (t : Tm C Γ s) →
    Srt.Bridge s (t.denote σ) (t.eval σ)
  | _, .pvV _ => by intro x h; cases h; rfl
  | _, .pvP i => by
    intro r segs h
    have h' : aliasPath σ i = .ok (r, segs) := h
    simp only [Tm.denote, h']
  | _, .pvS _ => by intro τ h; cases h; exact StValue.Equiv.refl _
  | _, .pvI _ => trivial
  | _, .netOf i a => by
    intro x h
    obtain ⟨va, ha, h⟩ := bind_ok_inv h
    obtain ⟨n, hn, h⟩ := bind_ok_inv h
    cases h
    cases va with
    | bool => cases hn
    | int n' =>
      cases hn
      simp only [Tm.denote, Tm.denote_eval σ a _ ha]
  | _, .app0 o => Op0.denote_eval o
  | _, .app1 o _ a => Op1.denote_eval o (Tm.denote_eval σ a)
  | _, .app2 o a b => Op2.denote_eval o (Tm.denote_eval σ a) (Tm.denote_eval σ b)
  | _, .app3 o a b c =>
    Op3.denote_eval o (Tm.denote_eval σ a) (Tm.denote_eval σ b) (Tm.denote_eval σ c)

end Bridge

/-! ## Rewriting the right-hand sides of an update -/

section RwC

variable {Γ : Ctx}

/-- A literal: a value term that cannot halt at the empty scope. -/
def Tm.isLit : Tm C Γ .val → Bool
  | .app0 (.lit _) => true
  | _ => false

/-- Where `t` returns, `t'` returns the same value. -/
def Tm.EvalRefines (t t' : Tm C [] .val) : Prop := ∀ σ : EState C [], Res.Le (t.eval σ) (t'.eval σ)

/-- **A Theory equation onto a literal refines evaluation**: where `t`
returns `x` it denotes `x` (`Tm.denote_eval`), the two denote alike, and
the literal returns what it denotes. -/
theorem Tm.EvalRefines.of_theq {t t' : Tm C [] .val} (h : Tm.Theq t t') (ht : t'.isLit = true) :
    Tm.EvalRefines t t' := fun σ x hx => by
  have e := h σ
  rw [Tm.denote_eval σ t x hx] at e
  match t', ht, e with
  | .app0 (.lit v), _, e =>
    cases Theory.StValue.Equiv.prim_iff.1 e
    rfl

/-- `t` where it is a closed value term reading `q.1`: `q.2`; `d` anywhere
else. -/
def Tm.pickC (q : Tm C [] .val × Tm C [] .val) : {s : Srt} → Tm C Γ s → Tm C Γ s → Tm C Γ s
  | .val, t, d => if t.closedAs q.1 then Tm.ofNil q.2 else d
  | _, _, d => d

/-- Every closed occurrence of `q.1` in a term, replaced by `q.2`. -/
def Tm.rwC (q : Tm C [] .val × Tm C [] .val) : {s : Srt} → Tm C Γ s → Tm C Γ s
  | _, .pvV i => .pvV i
  | _, .pvP i => .pvP i
  | _, .pvS i => .pvS i
  | _, .pvI i => .pvI i
  | _, .netOf i a => .netOf i (Tm.rwC q a)
  | _, .app0 o => Tm.pickC q (.app0 o) (.app0 o)
  | _, .app1 o ho x => Tm.pickC q (.app1 o ho x) (.app1 o ho (Tm.rwC q x))
  | _, .app2 o x y => Tm.pickC q (.app2 o x y) (.app2 o (Tm.rwC q x) (Tm.rwC q y))
  | _, .app3 o x y z =>
    Tm.pickC q (.app3 o x y z) (.app3 o (Tm.rwC q x) (Tm.rwC q y) (Tm.rwC q z))

/-- A right-hand side rewritten. -/
def Rhs.rwC (q : Tm C [] .val × Tm C [] .val) : {t : LTy} → Rhs C Γ t → Rhs C Γ t
  | _, .val t => .val (t.rwC q)
  | _, .path p => .path (p.rwC q)
  | _, .unset => .unset
  | _, .mref i => .mref (i.rwC q)
  | _, .store s => .store (s.rwC q)
  | _, .saveNet => .saveNet
  | _, .saveNetMt => .saveNetMt

/-- An element's right-hand sides rewritten. -/
def UpdElem.rwC {Δ : Ctx} (q : Tm C [] .val × Tm C [] .val) : UpdElem C Γ Δ → UpdElem C Γ Δ
  | .local i r => .local i (r.rwC q)
  | .storage s => .storage (s.rwC q)
  | .memory m => .memory (m.rwC q)
  | .selfBalance op a => .selfBalance op (a.rwC q)
  | .net r op a => .net (r.rwC q) op (a.rwC q)
  | .pay r a => .pay (r.rwC q) (a.rwC q)
  | .netMt r a => .netMt (r.rwC q) (a.rwC q)
  | .setBalance a => .setBalance (a.rwC q)

/-- An update's right-hand sides rewritten. -/
def Upd.rwC (q : Tm C [] .val × Tm C [] .val) : {Δ : Ctx} → Upd C Γ Δ → Upd C Γ Δ
  | _, .nil => .nil
  | _, .snoc U e => .snoc (Upd.rwC q U) (e.rwC q)
  | _, .decl U x r => .decl (Upd.rwC q U) x (r.rwC q)
  | _, .pop U h => .pop (Upd.rwC q U) h
  | _, .drop U h => .drop (Upd.rwC q U) h

variable {q : Tm C [] .val × Tm C [] .val}

theorem Tm.pickC_eval (hq : Tm.EvalRefines q.1 q.2) (σ : EState C Γ) :
    {s : Srt} → {t d : Tm C Γ s} → Srt.Le s (t.eval σ) (d.eval σ) →
      Srt.Le s (t.eval σ) ((Tm.pickC q t d).eval σ)
  | .val, t, d, hd => by
    simp only [Tm.pickC]
    split
    · rename_i hc
      show Res.Le (t.eval σ) ((Tm.ofNil q.2).eval σ)
      rw [Tm.eval_closedAs hc σ, Tm.eval_ofNil σ]
      exact hq σ.nil
    · exact hd
  | .path, _, _, hd | .st, _, _, hd | .sv, _, _, hd | .ident, _, _, hd | .addr, _, _, hd
  | .mem, _, _, hd | .mv, _, _, hd => hd

/-- **Rewriting keeps every value a term returns.** -/
theorem Tm.rwC_eval (hq : Tm.EvalRefines q.1 q.2) (σ : EState C Γ) :
    {s : Srt} → (t : Tm C Γ s) → Srt.Le s (t.eval σ) ((t.rwC q).eval σ)
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ => Srt.Le.refl _ _
  | _, .netOf _ a => Res.Le.bind (Tm.rwC_eval hq σ a) fun _ => Res.Le.refl _
  | _, .app0 _ => Tm.pickC_eval hq σ (Srt.Le.refl _ _)
  | _, .app1 o _ x => Tm.pickC_eval hq σ (o.eval_le (Tm.rwC_eval hq σ x))
  | _, .app2 o x y => Tm.pickC_eval hq σ (o.eval_le (Tm.rwC_eval hq σ x) (Tm.rwC_eval hq σ y))
  | _, .app3 o x y z =>
    Tm.pickC_eval hq σ (o.eval_le (Tm.rwC_eval hq σ x) (Tm.rwC_eval hq σ y) (Tm.rwC_eval hq σ z))

theorem Rhs.rwC_eval (hq : Tm.EvalRefines q.1 q.2) (σ : EState C Γ) {t : LTy} (r : Rhs C Γ t) :
    Res.Le (r.eval σ) ((r.rwC q).eval σ) := by
  cases r with
  | val t => exact Tm.rwC_eval hq σ t
  | path p => exact Res.Le.bind (Tm.rwC_eval hq σ p) fun _ => Res.Le.refl _
  | unset => exact Res.Le.refl _
  | mref i => exact Res.Le.bind (Tm.rwC_eval hq σ i) fun _ => Res.Le.refl _
  | store s => exact Res.Le.bind (Tm.rwC_eval hq σ s) fun _ => Res.Le.refl _
  | saveNet => exact Res.Le.refl _
  | saveNetMt => exact Res.Le.refl _

theorem UpdElem.rwC_write (hq : Tm.EvalRefines q.1 q.2) {Δ : Ctx} (σ₀ : EState C Γ)
    (e : UpdElem C Γ Δ) (τ : EState C Δ) : Res.Le (e.write σ₀ τ) ((e.rwC q).write σ₀ τ) := by
  have hv := fun t : Tm C Γ .val => Tm.rwC_eval hq σ₀ t
  cases e with
  | «local» i r => exact Res.Le.bind (Rhs.rwC_eval hq σ₀ r) fun _ => Res.Le.refl _
  | storage s => exact Res.Le.bind (Tm.rwC_eval hq σ₀ s) fun _ => Res.Le.refl _
  | memory m => exact Res.Le.bind (Tm.rwC_eval hq σ₀ m) fun _ => Res.Le.refl _
  | selfBalance op a => exact Res.Le.bind (hv a) fun _ => Res.Le.refl _
  | net r op a | pay r a | netMt r a =>
    refine Res.Le.bind (hv r) fun _ => Res.Le.bind (Res.Le.refl _) fun _ => ?_
    exact Res.Le.bind (hv a) fun _ => Res.Le.refl _
  | setBalance a => exact Res.Le.bind (hv a) fun _ => Res.Le.refl _

/-- **Where an update returns, its rewrite returns the same state.** -/
theorem Upd.rwC_apply (hq : Tm.EvalRefines q.1 q.2) (σ₀ : EState C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → Res.Le (U.apply σ₀) ((U.rwC q).apply σ₀)
  | _, .nil => Res.Le.refl _
  | _, .snoc U e => Res.Le.bind (Upd.rwC_apply hq σ₀ U) fun τ => UpdElem.rwC_write hq σ₀ e τ
  | _, .decl U x r => Res.Le.bind (Upd.rwC_apply hq σ₀ U) fun _ =>
      Res.Le.bind (Rhs.rwC_eval hq σ₀ r) fun _ => Res.Le.refl _
  | _, .pop U h => fun τ hτ => by
    change (U.apply σ₀).map (EState.drop h) = .ok τ at hτ
    cases hU : U.apply σ₀ with
    | error => rw [hU] at hτ; cases hτ
    | ok τ₀ =>
      rw [hU] at hτ; cases hτ
      show ((U.rwC q).apply σ₀).map (EState.drop h) = _
      rw [Upd.rwC_apply hq σ₀ U τ₀ hU]; rfl
  | _, .drop U h => fun τ hτ => by
    change (U.apply σ₀).map (EState.thin h) = .ok τ at hτ
    cases hU : U.apply σ₀ with
    | error => rw [hU] at hτ; cases hτ
    | ok τ₀ =>
      rw [hU] at hτ; cases hτ
      show ((U.rwC q).apply σ₀).map (EState.thin h) = _
      rw [Upd.rwC_apply hq σ₀ U τ₀ hU]; rfl

/-- **Under the box, a rewritten update gives the update.** -/
theorem holds_upd_rwC (hq : Tm.EvalRefines q.1 q.2) {Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ}
    (σ : State C Γ) (h : holds σ (.upd .box (U.rwC q) φ)) : holds σ (.upd .box U φ) := by
  show Modality.afterC .box _ (U.apply σ.erase)
  have h : Modality.afterC .box _ ((U.rwC q).apply σ.erase) := h
  cases hU : U.apply σ.erase with
  | error => trivial
  | ok τ => rw [Upd.rwC_apply hq σ.erase U τ hU] at h; exact h

end RwC

section RwEq

variable {Γ : Ctx}

/-- A side of an equation, made `q.2` where it is a closed term reading
`q.1`. -/
def Tm.sideC (q : Tm C [] .val × Tm C [] .val) (t : Tm C Γ .val) : Tm C Γ .val :=
  if t.closedAs q.1 then Tm.ofNil q.2 else t

/-- `Fml.rwEqC`'s compiled twin. -/
def Fml.rwEqCM (q : Tm C [] .val × Tm C [] .val) : {Γ : Ctx} → Fml C Γ → Fml C Γ
  | _, .tt => .tt
  | _, .eq a b => .eq (a.sideC q) (b.sideC q)
  | _, .defined t => .defined t
  | _, .not φ => .not (Fml.rwEqCM q φ)
  | _, .and φ ψ => .and (Fml.rwEqCM q φ) (Fml.rwEqCM q ψ)
  | _, .imp φ ψ => .imp (Fml.rwEqCM q φ) (Fml.rwEqCM q ψ)
  | _, .upd m U φ => .upd m U (Fml.rwEqCM q φ)
  | _, .modal m P κ φ => .modal m P κ (Fml.rwEqCM q φ)
  | _, .havoc φ => .havoc (Fml.rwEqCM q φ)
  | _, .all x p φ => .all x p (Fml.rwEqCM q φ)
  | _, .bind m x t φ => .bind m x t (Fml.rwEqCM q φ)
  | _, .anon xs φ => .anon xs (Fml.rwEqCM q φ)

/-- Every equation of a formula, rewritten: both sides by `Tm.sideC`,
through every connective, update, quantifier and hidden binder, and into the
postcondition of a modality; by the recursor. -/
@[implemented_by Fml.rwEqCM]
def Fml.rwEqC (q : Tm C [] .val × Tm C [] .val) {Γ : Ctx} (φ : Fml C Γ) : Fml C Γ :=
  Fml.rec (motive := fun Γ _ => Fml C Γ)
    (tt := .tt) (eq := fun a b => .eq (a.sideC q) (b.sideC q)) (defined := fun t => .defined t)
    (not := fun _ ih => .not ih) (and := fun _ _ ihφ ihψ => .and ihφ ihψ)
    (imp := fun _ _ ihφ ihψ => .imp ihφ ihψ) (upd := fun m U _ ih => .upd m U ih)
    (modal := fun m P κ _ ih => .modal m P κ ih) (havoc := fun _ ih => .havoc ih)
    (all := fun x p _ ih => .all x p ih) (bind := fun m x t _ ih => .bind m x t ih)
    (anon := fun xs _ ih => .anon xs ih) φ

section Clauses

variable (q : Tm C [] .val × Tm C [] .val)

theorem Fml.rwEqC_not (φ : Fml C Γ) : (Fml.not φ).rwEqC q = .not (φ.rwEqC q) := rfl
theorem Fml.rwEqC_and (φ ψ : Fml C Γ) : (Fml.and φ ψ).rwEqC q = .and (φ.rwEqC q) (ψ.rwEqC q) :=
  rfl
theorem Fml.rwEqC_imp (φ ψ : Fml C Γ) : (Fml.imp φ ψ).rwEqC q = .imp (φ.rwEqC q) (ψ.rwEqC q) :=
  rfl
theorem Fml.rwEqC_upd {Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) :
    (Fml.upd m U φ).rwEqC q = .upd m U (φ.rwEqC q) := rfl
theorem Fml.rwEqC_modal {Γ₁ Γ₂ : Ctx} (m : Modality) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₂)
    (φ : Fml C Γ₂) : (Fml.modal m P κ φ).rwEqC q = .modal m P κ (φ.rwEqC q) := rfl
theorem Fml.rwEqC_havoc (φ : Fml C Γ) : (Fml.havoc φ).rwEqC q = .havoc (φ.rwEqC q) := rfl
theorem Fml.rwEqC_all (x : Var) (p : PrimTy) (φ : Fml C (.val p :: Γ)) :
    (Fml.all x p φ).rwEqC q = .all x p (φ.rwEqC q) := rfl
theorem Fml.rwEqC_bind (m : Modality) (x : Var) (t : LTy) (φ : Fml C (t :: Γ)) :
    (Fml.bind m x t φ).rwEqC q = .bind m x t (φ.rwEqC q) := rfl
theorem Fml.rwEqC_anon (xs : List ((t : LTy) × Idx Γ t)) (φ : Fml C Γ) :
    (Fml.anon xs φ).rwEqC q = .anon xs (φ.rwEqC q) := rfl

/-- The recursor's rewrite is the twin's. -/
theorem Fml.rwEqC_eq_rwEqCM (φ : Fml C Γ) : φ.rwEqC q = φ.rwEqCM q := by
  induction φ with
  | tt | eq | defined => rfl
  | not φ ih | upd m U φ ih | modal m P κ φ ih | havoc φ ih | all x p φ ih | bind m x t φ ih
  | anon xs φ ih => simp only [Fml.rwEqCM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [Fml.rwEqCM, ← ihφ, ← ihψ]; rfl

end Clauses

theorem Tm.sideC_denote {q : Tm C [] .val × Tm C [] .val} (hq : Tm.Theq q.1 q.2)
    (σ : EState C Γ) (t : Tm C Γ .val) : Equiv ((t.sideC q).denote σ) (t.denote σ) := by
  unfold Tm.sideC
  split
  · rename_i hc
    rw [Tm.denote_ofNil σ, Tm.denote_closedAs hc σ]
    exact (hq σ.nil).symm
  · exact Equiv.refl _

/-- **A formula rewritten by a Theory equation holds where it does.** -/
theorem Fml.rwEqC_holds {q : Tm C [] .val × Tm C [] .val} (hq : Tm.Theq q.1 q.2) :
    {Γ : Ctx} → (φ : Fml C Γ) → ∀ σ : State C Γ, (holds σ (φ.rwEqC q) ↔ holds σ φ)
  | _, .tt, _ => Iff.rfl
  | _, .eq a b, σ => by
    show Equiv ((a.sideC q).denote σ.erase) ((b.sideC q).denote σ.erase) ↔
      Equiv (a.denote σ.erase) (b.denote σ.erase)
    have ha := Tm.sideC_denote hq σ.erase a
    have hb := Tm.sideC_denote hq σ.erase b
    exact ⟨fun h => (ha.symm.trans h).trans hb, fun h => (ha.trans h).trans hb.symm⟩
  | _, .defined _, _ => Iff.rfl
  | _, .not φ, σ => not_congr (Fml.rwEqC_holds hq φ σ)
  | _, .and φ ψ, σ => and_congr (Fml.rwEqC_holds hq φ σ) (Fml.rwEqC_holds hq ψ σ)
  | _, .imp φ ψ, σ => imp_congr (Fml.rwEqC_holds hq φ σ) (Fml.rwEqC_holds hq ψ σ)
  | _, .upd m U φ, σ => by
    have ih := Fml.rwEqC_holds hq φ
    simp only [Fml.rwEqC_upd, holds, ih]
  | _, .modal m P κ φ, σ => by
    have ih := Fml.rwEqC_holds hq φ
    simp only [Fml.rwEqC_modal, holds, ih]
  | _, .havoc φ, σ => by
    have ih := Fml.rwEqC_holds hq φ
    simp only [Fml.rwEqC_havoc, holds, ih]
  | _, .all x p φ, σ => by
    have ih := Fml.rwEqC_holds hq φ
    simp only [Fml.rwEqC_all, holds, ih]
  | _, .bind m x t φ, σ => by
    have ih := Fml.rwEqC_holds hq φ
    simp only [Fml.rwEqC_bind, holds, ih]
  | _, .anon xs φ, σ => by
    have ih := Fml.rwEqC_holds hq φ
    simp only [Fml.rwEqC_anon, holds, ih]

end RwEq

/-! ## Finding the closed terms of a sequent

What `rw` and a chain's `~[r]~>` match a law against: the closed value
terms of a scoped formula, each read at the empty scope (`Tm.toNil?`,
computed). -/

section Meta

open Lean Meta

/-- `e`, a scoped value term with no local, read at the empty scope:
`Tm.toNil? e` computed. -/
def Tm.toNilQ? (e : Expr) : MetaM (Option Expr) := do
  if e.hasLooseBVars || e.hasMVar then return none
  let some ty ← (try some <$> whnf (← inferType e) catch _ => pure none) | return none
  unless ty.isAppOfArity ``Tm 3 && (← whnf (ty.getArg! 2)).isConstOf ``Srt.val do return none
  let r ← Meta.reduce (← mkAppM ``Tm.toNil? #[e]) (skipTypes := true)
  return if r.isAppOfArity ``Option.some 2 then some r.appArg! else none

/-- The closed value terms of `e`, outermost first, each read at the empty
scope (`Tm.toNilQ?`) and kept once; the terms inside one are not listed. -/
partial def Tm.closedNilVals (e : Expr) (acc : Array Expr := #[]) : MetaM (Array Expr) := do
  if !e.hasLooseBVars && !e.hasMVar then
    let e' ← whnfR e
    if e'.getAppFn.constName?.any (·.getPrefix == ``Tm) then
      if let some t ← Tm.toNilQ? e then
        return if acc.contains t then acc else acc.push t
  e.getAppArgs.foldlM (fun acc a => Tm.closedNilVals a acc) acc

end Meta

end Solidity
