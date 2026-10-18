import Solidity.Calculus.Graft
import Solidity.Calculus.TermEq

/-!
# A Theory equation in a scoped sequent, read on its scoped terms

A rewrite of a scoped sequent by a term taclet (`TermTaclet`,
`Calculus/TermLib.lean`) or a Theory equation (`Tm.Theq`): `q = (t, t')`, two
closed value terms at the empty scope.  A term of the sequent is `t` where it
has no local and reads `t` at the empty scope (`Tm.closedAs`: `Tm.toNil?`,
compared by `Tm.beqR`); it becomes `t'` read at its scope (`Tm.ofNil`).  A
closed term reads what it reads at the empty scope over the same global
part (`Tm.eval_toNilS`, `Tm.denote_ofNil`, the typed state's global part
`State.toNil`, its `State.glob`).

*In an equation*: a side of an equation that is `t` becomes `t'`
(`Tm.sideC`), in every equation of the formula, at any depth of its
connectives, updates, quantifiers and hidden binders, and in the
postcondition of a modality still open (`Fml.rwEqC`).  A Theory equation
holds in every state (`Tm.Theq`), so the formula rewritten holds exactly
where it does (`Fml.rwEqC_holds`): under a modality, in every state its
program ends in.  An update's right-hand sides and a `wt(s)` are not
rewritten there: they are read by the interpreter, which a Theory equation
does not preserve.  `Proves.rewrite` (`Calculus/Proves.lean`) rewrites the
context's preconditions and the goal at once (`Hyps.rwEqC`).

*In an update's right-hand sides* (`Proves.updRw`): every closed
occurrence of `t` becomes `t'` (`Tm.rwC`), where `t'` returns wherever `t`
does, the same value (`Tm.EvalRefines`: a Theory equation onto a literal,
`Tm.EvalRefines.of_theq`), and where the update lands, the rewritten one
lands (`Upd.rwBy_lands`).

The kernel unfolds `Fml.rwEqC` and `Hyps.rwEqC` where `Proves.rewrite'`
checks the rewritten sequent (`rfl`), so both are written by the
recursors (Gate G0, conditions 1 and 2), each with its `match` form as the
compiled twin (`Fml.rwEqCM`, `Hyps.rwEqCM`) and a link theorem; the
recursor's clauses are stated by hand (`Fml.rwEqC_and`, …), by `rfl`.
`Tm.toNil?`, `Tm.ofNil` and the update's rewrite use `match` (the
exemption of `Calculus/Graft.lean`'s functions): they run once a rule.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)

variable {C : Contract}

/-! ## Closed terms -/

section Closed

variable {Γ : Ctx}

/-- A term with no local, at the empty scope. -/
def Tm.toNil? : {s : Srt} → Tm C Γ s → Option (Tm C [] s)
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .netOf .. | _, .pvZ _ => none
  | _, .app0 o => some (.app0 o)
  | _, .app1 o x => (Tm.toNil? x).map (.app1 o)
  | _, .app2 o x y => do pure (.app2 o (← Tm.toNil? x) (← Tm.toNil? y))
  | _, .app3 o x y z => do pure (.app3 o (← Tm.toNil? x) (← Tm.toNil? y) (← Tm.toNil? z))

/-- A term at the empty scope, read at the scope `Γ`. -/
def Tm.ofNil : {s : Srt} → Tm C [] s → Tm C Γ s
  | _, .pvV i | _, .pvP i | _, .pvS i | _, .pvI i | _, .netOf i _ | _, .pvZ i => nomatch i
  | _, .app0 o => .app0 o
  | _, .app1 o x => .app1 o (Tm.ofNil x)
  | _, .app2 o x y => .app2 o (Tm.ofNil x) (Tm.ofNil y)
  | _, .app3 o x y z => .app3 o (Tm.ofNil x) (Tm.ofNil y) (Tm.ofNil z)

/-- `t` has no local and reads `q` at the empty scope. -/
def Tm.closedAs {s : Srt} (t : Tm C Γ s) (q : Tm C [] s) : Bool :=
  match t.toNil? with
  | some t₀ => t₀.beqR q
  | none => false

theorem Tm.closedAs_toNil {s : Srt} {q : Tm C [] s} {t : Tm C Γ s} (h : t.closedAs q = true) :
    t.toNil? = some q := by
  unfold Tm.closedAs at h
  split at h
  · rename_i t₀ ht
    rw [ht, Tm.eq_of_beqR h]
  · cases h

/-! ### Closed terms on the typed state -/

/-- The typed state's global part, with no local. -/
abbrev State.toNil (σ : State C Γ) : State C [] := σ.glob

/-- A closed term reads what it reads at the empty scope. -/
theorem Tm.eval_toNilS (σ : State C Γ) : {s : Srt} → (t : Tm C Γ s) → {t₀ : Tm C [] s} →
    t.toNil? = some t₀ → t.eval σ = t₀.eval σ.toNil
  | _, .pvV _, _, h | _, .pvP _, _, h | _, .pvS _, _, h | _, .pvI _, _, h | _, .netOf .., _, h | _, .pvZ _, _, h =>
    nomatch h
  | _, .app0 o, _, h => by cases h; rfl
  | _, .app1 o x, _, h => by
    obtain ⟨x₀, hx, rfl⟩ := Option.map_eq_some_iff.1 h
    show o.eval σ.glob (x.eval σ) = o.eval σ.glob (x₀.eval σ.toNil)
    rw [Tm.eval_toNilS σ x hx]
  | _, .app2 o x y, _, h => by
    obtain ⟨x₀, hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y₀, hy, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show o.eval σ.glob (x.eval σ) (y.eval σ) =
      o.eval σ.glob (x₀.eval σ.toNil) (y₀.eval σ.toNil)
    rw [Tm.eval_toNilS σ x hx, Tm.eval_toNilS σ y hy]
  | _, .app3 o x y z, _, h => by
    obtain ⟨x₀, hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y₀, hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z₀, hz, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show o.eval σ.glob (x.eval σ) (y.eval σ) (z.eval σ) =
      o.eval σ.glob (x₀.eval σ.toNil) (y₀.eval σ.toNil) (z₀.eval σ.toNil)
    rw [Tm.eval_toNilS σ x hx, Tm.eval_toNilS σ y hy, Tm.eval_toNilS σ z hz]

/-- A closed term denotes what it denotes at the empty scope. -/
theorem Tm.denote_toNilS (σ : State C Γ) : {s : Srt} → (t : Tm C Γ s) → {t₀ : Tm C [] s} →
    t.toNil? = some t₀ → t.denote σ = t₀.denote σ.toNil
  | _, .pvV _, _, h | _, .pvP _, _, h | _, .pvS _, _, h | _, .pvI _, _, h | _, .netOf .., _, h | _, .pvZ _, _, h =>
    nomatch h
  | _, .app0 o, _, h => by cases h; rfl
  | _, .app1 o x, _, h => by
    obtain ⟨x₀, hx, rfl⟩ := Option.map_eq_some_iff.1 h
    show o.denote σ.glob (x.denote σ) = o.denote σ.glob (x₀.denote σ.toNil)
    rw [Tm.denote_toNilS σ x hx]
  | _, .app2 o x y, _, h => by
    obtain ⟨x₀, hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y₀, hy, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show o.denote σ.glob (x.eval σ) (y.eval σ) (x.denote σ) (y.denote σ) =
      o.denote σ.glob (x₀.eval σ.toNil) (y₀.eval σ.toNil) (x₀.denote σ.toNil)
        (y₀.denote σ.toNil)
    rw [Tm.denote_toNilS σ x hx, Tm.denote_toNilS σ y hy, Tm.eval_toNilS σ x hx,
      Tm.eval_toNilS σ y hy]
  | _, .app3 o x y z, _, h => by
    obtain ⟨x₀, hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y₀, hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z₀, hz, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show o.denote (x.denote σ) (y.denote σ) (z.denote σ) =
      o.denote (x₀.denote σ.toNil) (y₀.denote σ.toNil) (z₀.denote σ.toNil)
    rw [Tm.denote_toNilS σ x hx, Tm.denote_toNilS σ y hy, Tm.denote_toNilS σ z hz]

/-- A term of the empty scope reads alike at any scope. -/
theorem Tm.eval_ofNil (σ : State C Γ) : {s : Srt} → (t : Tm C [] s) →
    (Tm.ofNil t).eval σ = t.eval σ.toNil
  | _, .pvV i | _, .pvP i | _, .pvS i | _, .pvI i | _, .netOf i _ | _, .pvZ i => nomatch i
  | _, .app0 _ => rfl
  | _, .app1 o x => by
    show o.eval σ.glob ((Tm.ofNil x).eval σ) = o.eval σ.glob (x.eval σ.toNil)
    rw [Tm.eval_ofNil σ x]
  | _, .app2 o x y => by
    show o.eval σ.glob ((Tm.ofNil x).eval σ) ((Tm.ofNil y).eval σ) =
      o.eval σ.glob (x.eval σ.toNil) (y.eval σ.toNil)
    rw [Tm.eval_ofNil σ x, Tm.eval_ofNil σ y]
  | _, .app3 o x y z => by
    show o.eval σ.glob ((Tm.ofNil x).eval σ) ((Tm.ofNil y).eval σ) ((Tm.ofNil z).eval σ) =
      o.eval σ.glob (x.eval σ.toNil) (y.eval σ.toNil) (z.eval σ.toNil)
    rw [Tm.eval_ofNil σ x, Tm.eval_ofNil σ y, Tm.eval_ofNil σ z]

/-- A term of the empty scope denotes alike at any scope. -/
theorem Tm.denote_ofNil (σ : State C Γ) : {s : Srt} → (t : Tm C [] s) →
    (Tm.ofNil t).denote σ = t.denote σ.toNil
  | _, .pvV i | _, .pvP i | _, .pvS i | _, .pvI i | _, .netOf i _ | _, .pvZ i => nomatch i
  | _, .app0 _ => rfl
  | _, .app1 o x => by
    show o.denote σ.glob ((Tm.ofNil x).denote σ) = o.denote σ.glob (x.denote σ.toNil)
    rw [Tm.denote_ofNil σ x]
  | _, .app2 o x y => by
    show o.denote σ.glob ((Tm.ofNil x).eval σ) ((Tm.ofNil y).eval σ) ((Tm.ofNil x).denote σ)
        ((Tm.ofNil y).denote σ) =
      o.denote σ.glob (x.eval σ.toNil) (y.eval σ.toNil) (x.denote σ.toNil) (y.denote σ.toNil)
    rw [Tm.denote_ofNil σ x, Tm.denote_ofNil σ y, Tm.eval_ofNil σ x, Tm.eval_ofNil σ y]
  | _, .app3 o x y z => by
    show o.denote ((Tm.ofNil x).denote σ) ((Tm.ofNil y).denote σ) ((Tm.ofNil z).denote σ) =
      o.denote (x.denote σ.toNil) (y.denote σ.toNil) (z.denote σ.toNil)
    rw [Tm.denote_ofNil σ x, Tm.denote_ofNil σ y, Tm.denote_ofNil σ z]

theorem Tm.eval_closedAs {s : Srt} {q : Tm C [] s} {t : Tm C Γ s} (h : t.closedAs q = true)
    (σ : State C Γ) : t.eval σ = q.eval σ.toNil :=
  Tm.eval_toNilS σ t (Tm.closedAs_toNil h)

theorem Tm.denote_closedAs {s : Srt} {q : Tm C [] s} {t : Tm C Γ s} (h : t.closedAs q = true)
    (σ : State C Γ) : t.denote σ = q.denote σ.toNil :=
  Tm.denote_toNilS σ t (Tm.closedAs_toNil h)

end Closed

/-! ## Rewriting the right-hand sides of an update -/

section RwC

variable {Γ : Ctx} {p : PrimTy}

/-- The literal a term is, if it is one. -/
def Tm.litVal? : Tm C Γ (.val p) → Option p.Denote
  | .app0 (.lit v) => some v
  | _ => none

/-- A literal: a value term that cannot halt at the empty scope. -/
abbrev Tm.isLit (t : Tm C Γ (.val p)) : Bool := t.litVal?.isSome

/-- Where `t` returns, `t'` returns the same value. -/
def Tm.EvalRefines (t t' : Tm C [] (.val p)) : Prop :=
  ∀ σ : State C [], OLe (t.eval σ) (t'.eval σ)

/-- **A Theory equation onto a literal refines evaluation**: where `t`
returns `x` it denotes `x` (`Tm.denote_eval`), the two denote alike, and
the literal returns what it denotes. -/
theorem Tm.eq_of_litVal? {t : Tm C Γ (.val p)} {v : p.Denote} (h : t.litVal? = some v) :
    t = .app0 (.lit v) := by
  unfold Tm.litVal? at h
  split at h
  · cases h; rfl
  · cases h

theorem Tm.EvalRefines.of_theq {t t' : Tm C [] (.val p)} (h : Tm.Theq t t')
    (ht : t'.isLit = true) : Tm.EvalRefines t t' := fun σ x hx => by
  have e := h σ
  rw [Tm.denote_eval σ t x hx] at e
  cases hl : t'.litVal? with
  | none => simp only [Tm.isLit, hl, Option.isSome_none, Bool.false_eq_true] at ht
  | some v =>
    obtain rfl := Tm.eq_of_litVal? hl
    have e : some v = some x := e.symm
    rw [Option.some.inj e]
    rfl

end RwC

/-! ### One traversal for every rewrite of an update's right-hand sides

`f t` is the replacement of the subterm `t`, where the rewrite fires on it;
`Tm.rwBy f` replaces every subterm it fires on, the outermost first, and
`Tm.hasBy f` says whether it fires anywhere.  A literal law and a term
taclet read at the empty scope (`Tm.pickClosed`, `Upd.rwC`) and a law at
the update's scope (`LawPair.pick`, `Upd.rwG`, `Calculus/RewriteLaws.lean`)
are its two instances. -/

section RwBy

variable {Γ : Ctx} (f : {s : Srt} → Tm C Γ s → Option (Tm C Γ s))

/-- Every subterm `f` fires on, replaced by what it gives. -/
def Tm.rwBy : {s : Srt} → Tm C Γ s → Tm C Γ s
  | _, .pvV i => .pvV i
  | _, .pvP i => .pvP i
  | _, .pvS i => .pvS i
  | _, .pvI i => .pvI i
  | _, .pvZ i => .pvZ i
  | _, .netOf i a => .netOf i (Tm.rwBy a)
  | _, .app0 o => (f (.app0 o)).getD (.app0 o)
  | _, .app1 o x => (f (.app1 o x)).getD (.app1 o (Tm.rwBy x))
  | _, .app2 o x y => (f (.app2 o x y)).getD (.app2 o (Tm.rwBy x) (Tm.rwBy y))
  | _, .app3 o x y z => (f (.app3 o x y z)).getD (.app3 o (Tm.rwBy x) (Tm.rwBy y) (Tm.rwBy z))

/-- A right-hand side rewritten. -/
def Rhs.rwBy : {t : LTy} → Rhs C Γ t → Rhs C Γ t
  | _, .val t => .val (Tm.rwBy f t)
  | _, .path p => .path (Tm.rwBy f p)
  | _, .unset => .unset
  | _, .mref i => .mref (Tm.rwBy f i)
  | _, .store s => .store (Tm.rwBy f s)
  | _, .saveNet => .saveNet
  | _, .saveNetMt => .saveNetMt
  | _, .zint t => .zint (Tm.rwBy f t)

/-- An element's right-hand sides rewritten. -/
def UpdElem.rwBy {Δ : Ctx} : UpdElem C Γ Δ → UpdElem C Γ Δ
  | .local i r => .local i (Rhs.rwBy f r)
  | .storage s => .storage (Tm.rwBy f s)
  | .memory m => .memory (Tm.rwBy f m)
  | .selfBalance op a => .selfBalance op (Tm.rwBy f a)
  | .net r op a => .net (Tm.rwBy f r) op (Tm.rwBy f a)
  | .pay r a => .pay (Tm.rwBy f r) (Tm.rwBy f a)
  | .netMt r a => .netMt (Tm.rwBy f r) (Tm.rwBy f a)
  | .setBalance a => .setBalance (Tm.rwBy f a)

/-- An update's right-hand sides rewritten. -/
def Upd.rwBy : {Δ : Ctx} → Upd C Γ Δ → Upd C Γ Δ
  | _, .nil => .nil
  | _, .snoc U e => .snoc (Upd.rwBy U) (UpdElem.rwBy f e)
  | _, .decl U x r => .decl (Upd.rwBy U) x (Rhs.rwBy f r)
  | _, .pop U h => .pop (Upd.rwBy U) h
  | _, .drop U h => .drop (Upd.rwBy U) h

/-- Whether `Tm.rwBy f` rewrites something in a term. -/
def Tm.hasBy : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .pvZ _ => false
  | _, .netOf _ a => Tm.hasBy a
  | _, t@(.app0 _) => (f t).isSome
  | _, t@(.app1 _ x) => (f t).isSome || Tm.hasBy x
  | _, t@(.app2 _ x y) => (f t).isSome || Tm.hasBy x || Tm.hasBy y
  | _, t@(.app3 _ x y z) => (f t).isSome || Tm.hasBy x || Tm.hasBy y || Tm.hasBy z

/-- Whether `Rhs.rwBy f` rewrites something. -/
def Rhs.hasBy : {t : LTy} → Rhs C Γ t → Bool
  | _, .val t => Tm.hasBy f t
  | _, .path p => Tm.hasBy f p
  | _, .mref i => Tm.hasBy f i
  | _, .store s => Tm.hasBy f s
  | _, .zint t => Tm.hasBy f t
  | _, _ => false

/-- Whether `UpdElem.rwBy f` rewrites something. -/
def UpdElem.hasBy {Δ : Ctx} : UpdElem C Γ Δ → Bool
  | .local _ r => Rhs.hasBy f r
  | .storage s => Tm.hasBy f s
  | .memory m => Tm.hasBy f m
  | .selfBalance _ a | .setBalance a => Tm.hasBy f a
  | .net r _ a | .pay r a | .netMt r a => Tm.hasBy f r || Tm.hasBy f a

/-- Whether `Upd.rwBy f` rewrites something. -/
def Upd.hasBy : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => false
  | _, .snoc U e => Upd.hasBy U || UpdElem.hasBy f e
  | _, .decl U _ r => Upd.hasBy U || Rhs.hasBy f r
  | _, .pop U _ | _, .drop U _ => Upd.hasBy U

end RwBy

section RwByEval

variable {Γ : Ctx} {f : {s : Srt} → Tm C Γ s → Option (Tm C Γ s)} (σ : State C Γ)

/-- What a rewrite gives returns what the subterm it fires on returns. -/
def PickLe (f : {s : Srt} → Tm C Γ s → Option (Tm C Γ s)) (σ : State C Γ) : Prop :=
  ∀ {s : Srt} {t t' : Tm C Γ s}, f t = some t' → OLe (t.eval σ) (t'.eval σ)

/-- The subterm a rewrite fires on returns what the rewrite gives returns. -/
def PickGe (f : {s : Srt} → Tm C Γ s → Option (Tm C Γ s)) (σ : State C Γ) : Prop :=
  ∀ {s : Srt} {t t' : Tm C Γ s}, f t = some t' → OLe (t'.eval σ) (t.eval σ)

/-- What a rewrite gives returns exactly what the subterm it fires on returns. -/
def PickEq (f : {s : Srt} → Tm C Γ s → Option (Tm C Γ s)) (σ : State C Γ) : Prop :=
  ∀ {s : Srt} {t t' : Tm C Γ s}, f t = some t' → t'.eval σ = t.eval σ

theorem PickEq.le {σ : State C Γ} (hf : PickEq f σ) : PickLe f σ :=
  fun h _ hx => (hf h).trans hx

theorem PickEq.ge {σ : State C Γ} (hf : PickEq f σ) : PickGe f σ :=
  fun h _ hx => (hf h).symm.trans hx

theorem Tm.getD_le (hf : PickLe f σ) {s : Srt} {t d : Tm C Γ s}
    (hd : OLe (t.eval σ) (d.eval σ)) : OLe (t.eval σ) (((f t).getD d).eval σ) := by
  cases h : f t with
  | none => exact hd
  | some t' => exact hf h

theorem Tm.getD_ge (hf : PickGe f σ) {s : Srt} {t d : Tm C Γ s}
    (hd : OLe (d.eval σ) (t.eval σ)) : OLe (((f t).getD d).eval σ) (t.eval σ) := by
  cases h : f t with
  | none => exact hd
  | some t' => exact hf h

/-- **A rewrite keeps every value a term returns.** -/
theorem Tm.rwBy_eval (hf : PickLe f σ) :
    {s : Srt} → (t : Tm C Γ s) → OLe (t.eval σ) ((Tm.rwBy f t).eval σ)
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .pvZ _ => OLe.refl _
  | _, .netOf _ a => OLe.bind (Tm.rwBy_eval hf a) fun _ => OLe.refl _
  | _, .app0 _ => Tm.getD_le σ hf (OLe.refl _)
  | _, .app1 o x => Tm.getD_le σ hf (o.eval_le (Tm.rwBy_eval hf x))
  | _, .app2 o x y => Tm.getD_le σ hf (o.eval_le (Tm.rwBy_eval hf x) (Tm.rwBy_eval hf y))
  | _, .app3 o x y z =>
    Tm.getD_le σ hf (o.eval_le (Tm.rwBy_eval hf x) (Tm.rwBy_eval hf y) (Tm.rwBy_eval hf z))

/-- **A rewrite returns nothing the term does not.** -/
theorem Tm.rwBy_eval_rev (hf : PickGe f σ) :
    {s : Srt} → (t : Tm C Γ s) → OLe ((Tm.rwBy f t).eval σ) (t.eval σ)
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .pvZ _ => OLe.refl _
  | _, .netOf _ a => OLe.bind (Tm.rwBy_eval_rev hf a) fun _ => OLe.refl _
  | _, .app0 _ => Tm.getD_ge σ hf (OLe.refl _)
  | _, .app1 o x => Tm.getD_ge σ hf (o.eval_le (Tm.rwBy_eval_rev hf x))
  | _, .app2 o x y =>
    Tm.getD_ge σ hf (o.eval_le (Tm.rwBy_eval_rev hf x) (Tm.rwBy_eval_rev hf y))
  | _, .app3 o x y z => Tm.getD_ge σ hf
      (o.eval_le (Tm.rwBy_eval_rev hf x) (Tm.rwBy_eval_rev hf y) (Tm.rwBy_eval_rev hf z))

/-- **An exact rewrite keeps what every term returns.** -/
theorem Tm.rwBy_eval_eq (hf : PickEq f σ) {s : Srt} (t : Tm C Γ s) :
    (Tm.rwBy f t).eval σ = t.eval σ :=
  OLe.antisymm (Tm.rwBy_eval_rev σ hf.ge t) (Tm.rwBy_eval σ hf.le t)

theorem Rhs.rwBy_eval (hf : PickLe f σ) {t : LTy} (r : Rhs C Γ t) :
    OLe (r.eval σ) ((Rhs.rwBy f r).eval σ) := by
  cases r with
  | val t | zint t => exact Tm.rwBy_eval σ hf t
  | path p => exact OLe.bind (Tm.rwBy_eval σ hf p) fun _ => OLe.refl _
  | unset => exact OLe.refl _
  | mref i => exact OLe.bind (Tm.rwBy_eval σ hf i) fun _ => OLe.refl _
  | store s => exact OLe.bind (Tm.rwBy_eval σ hf s) fun _ => OLe.refl _
  | saveNet => exact OLe.refl _
  | saveNetMt => exact OLe.refl _

theorem Rhs.rwBy_eval_rev (hf : PickGe f σ) {t : LTy} (r : Rhs C Γ t) :
    OLe ((Rhs.rwBy f r).eval σ) (r.eval σ) := by
  cases r with
  | val t | zint t => exact Tm.rwBy_eval_rev σ hf t
  | path p => exact OLe.bind (Tm.rwBy_eval_rev σ hf p) fun _ => OLe.refl _
  | unset => exact OLe.refl _
  | mref i => exact OLe.bind (Tm.rwBy_eval_rev σ hf i) fun _ => OLe.refl _
  | store s => exact OLe.bind (Tm.rwBy_eval_rev σ hf s) fun _ => OLe.refl _
  | saveNet => exact OLe.refl _
  | saveNetMt => exact OLe.refl _

theorem Rhs.rwBy_eval_eq (hf : PickEq f σ) {t : LTy} (r : Rhs C Γ t) :
    (Rhs.rwBy f r).eval σ = r.eval σ :=
  OLe.antisymm (Rhs.rwBy_eval_rev σ hf.ge r) (Rhs.rwBy_eval σ hf.le r)

/-- An element's global part, by its right-hand sides' readings: a map of
`globT`'s arguments, so that the three rewrites below share one proof. -/
theorem UpdElem.rwBy_globT (hf : PickLe f σ) {Δ : Ctx} (e : UpdElem C Γ Δ) (G : GlobT C σ.H) :
    OLe (e.globT σ G) ((UpdElem.rwBy f e).globT σ G) := by
  have hv := fun {p : PrimTy} (t : Tm C Γ (.val p)) => Tm.rwBy_eval σ hf t
  rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
  cases e with
  | «local» i r => exact OLe.bind (Rhs.rwBy_eval σ hf r) fun _ => OLe.refl _
  | storage s => exact OLe.bind (Tm.rwBy_eval σ hf s) fun _ => OLe.refl _
  | memory m => exact OLe.bind (Tm.rwBy_eval σ hf m) fun _ => OLe.refl _
  | selfBalance op a => exact OLe.bind (hv a) fun _ => OLe.refl _
  | net r op a | pay r a | netMt r a =>
    exact OLe.bind (hv r) fun _ => OLe.bind (hv a) fun _ => OLe.refl _
  | setBalance a => exact OLe.bind (hv a) fun _ => OLe.refl _

theorem UpdElem.rwBy_globT_rev (hf : PickGe f σ) {Δ : Ctx} (e : UpdElem C Γ Δ)
    (G : GlobT C σ.H) : OLe ((UpdElem.rwBy f e).globT σ G) (e.globT σ G) := by
  have hv := fun {p : PrimTy} (t : Tm C Γ (.val p)) => Tm.rwBy_eval_rev σ hf t
  rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
  cases e with
  | «local» i r => exact OLe.bind (Rhs.rwBy_eval_rev σ hf r) fun _ => OLe.refl _
  | storage s => exact OLe.bind (Tm.rwBy_eval_rev σ hf s) fun _ => OLe.refl _
  | memory m => exact OLe.bind (Tm.rwBy_eval_rev σ hf m) fun _ => OLe.refl _
  | selfBalance op a => exact OLe.bind (hv a) fun _ => OLe.refl _
  | net r op a | pay r a | netMt r a =>
    exact OLe.bind (hv r) fun _ => OLe.bind (hv a) fun _ => OLe.refl _
  | setBalance a => exact OLe.bind (hv a) fun _ => OLe.refl _

theorem UpdElem.rwBy_globT_eq (hf : PickEq f σ) {Δ : Ctx} (e : UpdElem C Γ Δ)
    (G : GlobT C σ.H) : (UpdElem.rwBy f e).globT σ G = e.globT σ G :=
  OLe.antisymm (UpdElem.rwBy_globT_rev σ hf.ge e G) (UpdElem.rwBy_globT σ hf.le e G)

/-- **Where an update returns, its rewrite returns the same global part.** -/
theorem Upd.rwBy_globT (hf : PickLe f σ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → OLe (U.globT σ) ((Upd.rwBy f U).globT σ)
  | _, .nil => OLe.refl _
  | _, .snoc U e => OLe.bind (Upd.rwBy_globT hf U) fun G => UpdElem.rwBy_globT σ hf e G
  | _, .decl U _ r => OLe.bind (Upd.rwBy_globT hf U) fun _ =>
      OLe.bind (Rhs.rwBy_eval σ hf r) fun _ => OLe.refl _
  | _, .pop U _ => Upd.rwBy_globT hf U
  | _, .drop U _ => Upd.rwBy_globT hf U

/-- **Where the rewrite returns, the update returns the same global part.** -/
theorem Upd.rwBy_globT_rev (hf : PickGe f σ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → OLe ((Upd.rwBy f U).globT σ) (U.globT σ)
  | _, .nil => OLe.refl _
  | _, .snoc U e => OLe.bind (Upd.rwBy_globT_rev hf U) fun G => UpdElem.rwBy_globT_rev σ hf e G
  | _, .decl U _ r => OLe.bind (Upd.rwBy_globT_rev hf U) fun _ =>
      OLe.bind (Rhs.rwBy_eval_rev σ hf r) fun _ => OLe.refl _
  | _, .pop U _ => Upd.rwBy_globT_rev hf U
  | _, .drop U _ => Upd.rwBy_globT_rev hf U

/-- **An exact rewrite keeps the global part every update computes.** -/
theorem Upd.rwBy_globT_eq (hf : PickEq f σ) {Δ : Ctx} (U : Upd C Γ Δ) :
    (Upd.rwBy f U).globT σ = U.globT σ :=
  OLe.antisymm (Upd.rwBy_globT_rev σ hf.ge U) (Upd.rwBy_globT σ hf.le U)

/-- What a local holds, its right-hand side rewritten. -/
def Held.rwBy {t : LTy} : Held C Γ t → Held C Γ t
  | .pos j => .pos j
  | .rhs r => .rhs (Rhs.rwBy f r)

/-- A rewritten update leaves in each local what the update does, rewritten. -/
theorem Upd.held_rwBy : {Δ : Ctx} → (U : Upd C Γ Δ) → ∀ {t : LTy} (i : Idx Δ t),
    (Upd.rwBy f U).held i = Held.rwBy (f := f) (U.held i)
  | _, .nil, _, _ => rfl
  | _, .snoc U e, t, i => by
    cases e with
    | «local» k r =>
      show Subst.set (Upd.held (Upd.rwBy f U)) k (Rhs.rwBy f r) i =
        Held.rwBy (f := f) (Subst.set (Upd.held U) k r i)
      unfold Subst.set
      split
      · rename_i h
        generalize Idx.ty_eq_of_toNat h = e
        cases e
        rfl
      · exact Upd.held_rwBy U i
    | storage _ | memory _ | selfBalance _ _ | net _ _ _ | pay _ _ | netMt _ _ | setBalance _ =>
      exact Upd.held_rwBy U i
  | _, .decl U _ r, _, i => by
    cases i with
    | here => rfl
    | there j => exact Upd.held_rwBy U j
  | _, .pop U e, _, i => Upd.held_rwBy U (i.ext e)
  | _, .drop U e, _, i => Upd.held_rwBy U (i.wk e)

/-- **Where an update lands, its rewrite lands.** -/
theorem Upd.rwBy_lands (hf : PickLe f σ) {Δ : Ctx} (U : Upd C Γ Δ) {g : GlobT C σ.H}
    {σ' : State C Δ} (hL : U.Lands σ g σ') : (Upd.rwBy f U).Lands σ g σ' := by
  refine Upd.lands_of (fun g h => Upd.rwBy_globT σ hf U g h) (fun i v h => ?_) hL
  rw [Upd.held_rwBy]
  generalize U.held i = x at h
  cases x with
  | pos j => exact h
  | rhs r => exact Rhs.rwBy_eval σ hf r v h

/-- **An exact rewrite lands where the update does.** -/
theorem Upd.rwBy_lands_iff (hf : PickEq f σ) {Δ : Ctx} (U : Upd C Γ Δ) (g : GlobT C σ.H)
    (σ' : State C Δ) : (Upd.rwBy f U).Lands σ g σ' ↔ U.Lands σ g σ' := by
  unfold Upd.Lands
  rw [Upd.rwBy_globT_eq σ hf U]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  refine forall_congr' fun _ => forall_congr' fun i => ?_
  rw [Held.OK_iff_OKV, Held.OK_iff_OKV, Upd.held_rwBy]
  generalize U.held i = x
  cases x with
  | pos j => exact Iff.rfl
  | rhs r =>
    show (Rhs.rwBy f r).eval σ = _ ↔ r.eval σ = _
    rw [Rhs.rwBy_eval_eq σ hf]

/-- A rewrite whose replacement is out of gas exactly where the term it
replaces is. -/
def PickExh (f : {s : Srt} → Tm C Γ s → Option (Tm C Γ s)) (σ : State C Γ) : Prop :=
  ∀ {s : Srt} {t t' : Tm C Γ s}, f t = some t' → t'.exhB σ = t.exhB σ

/-- **An exact rewrite whose replacements are out of gas where the terms
they replace are keeps exhaustion.** -/
theorem Tm.rwBy_exhB (hf : PickEq f σ) (hn : PickExh f σ) :
    {s : Srt} → (t : Tm C Γ s) → (Tm.rwBy f t).exhB σ = t.exhB σ
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .pvZ _ => rfl
  | _, .netOf i a => by
    have he := Tm.rwBy_eval_eq σ hf (Tm.netOf i a)
    show (Tm.netOf i (Tm.rwBy f a)).exhB σ = _
    have he' : (Tm.netOf i (Tm.rwBy f a)).eval σ = (Tm.netOf i a).eval σ := he
    simp only [Tm.exhB, he', Tm.rwBy_exhB hf hn a]
  | _, .app0 o => by
    show ((f (.app0 o)).getD _).exhB σ = _
    cases h : f (Tm.app0 o) with
    | some _ => exact hn h
    | none => rfl
  | _, .app1 o x => by
    have he := Tm.rwBy_eval_eq σ hf (Tm.app1 o x)
    show ((f (.app1 o x)).getD _).exhB σ = _
    cases h : f (Tm.app1 o x) with
    | some _ => exact hn h
    | none =>
      have he' : (Tm.app1 o (Tm.rwBy f x)).eval σ = (Tm.app1 o x).eval σ := by
        rw [← he]; show _ = ((f (.app1 o x)).getD _).eval σ; rw [h]; rfl
      simp only [Option.getD_none, Tm.exhB, he', Tm.rwBy_exhB hf hn x]
  | _, .app2 o x y => by
    have he := Tm.rwBy_eval_eq σ hf (Tm.app2 o x y)
    show ((f (.app2 o x y)).getD _).exhB σ = _
    cases h : f (Tm.app2 o x y) with
    | some _ => exact hn h
    | none =>
      have he' : (Tm.app2 o (Tm.rwBy f x) (Tm.rwBy f y)).eval σ = (Tm.app2 o x y).eval σ := by
        rw [← he]; show _ = ((f (.app2 o x y)).getD _).eval σ; rw [h]; rfl
      simp only [Option.getD_none, Tm.exhB, he', Tm.rwBy_exhB hf hn x, Tm.rwBy_exhB hf hn y,
        Tm.rwBy_eval_eq σ hf x, Tm.rwBy_eval_eq σ hf y]
  | _, .app3 o x y z => by
    have he := Tm.rwBy_eval_eq σ hf (Tm.app3 o x y z)
    show ((f (.app3 o x y z)).getD _).exhB σ = _
    cases h : f (Tm.app3 o x y z) with
    | some _ => exact hn h
    | none =>
      have he' : (Tm.app3 o (Tm.rwBy f x) (Tm.rwBy f y) (Tm.rwBy f z)).eval σ =
          (Tm.app3 o x y z).eval σ := by
        rw [← he]; show _ = ((f (.app3 o x y z)).getD _).eval σ; rw [h]; rfl
      simp only [Option.getD_none, Tm.exhB, he', Tm.rwBy_exhB hf hn x, Tm.rwBy_exhB hf hn y,
        Tm.rwBy_exhB hf hn z, Tm.rwBy_eval_eq σ hf x, Tm.rwBy_eval_eq σ hf y,
        Tm.rwBy_eval_eq σ hf z]

theorem Rhs.rwBy_exhB (hf : PickEq f σ) (hn : PickExh f σ) {t : LTy} (r : Rhs C Γ t) :
    (Rhs.rwBy f r).exhB σ = r.exhB σ := by
  cases r <;> first | rfl | exact Tm.rwBy_exhB σ hf hn _

theorem UpdElem.rwBy_exhB (hf : PickEq f σ) (hn : PickExh f σ) {Δ : Ctx} (e : UpdElem C Γ Δ) :
    (UpdElem.rwBy f e).exhB σ = e.exhB σ := by
  cases e <;>
    simp only [UpdElem.rwBy, UpdElem.exhB, Tm.rwBy_exhB σ hf hn, Rhs.rwBy_exhB σ hf hn,
      Tm.rwBy_eval_eq σ hf]

theorem Upd.rwBy_exhAny (hf : PickEq f σ) (hn : PickExh f σ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → (Upd.rwBy f U).exhAny σ = U.exhAny σ
  | _, .nil => rfl
  | _, .snoc U e => by
    have he : (UpdElem.rwBy f e).exhB σ = e.exhB σ := UpdElem.rwBy_exhB σ hf hn e
    simp only [Upd.rwBy, Upd.exhAny, Upd.rwBy_exhAny hf hn U, he]
  | _, .decl U _ r => by
    simp only [Upd.rwBy, Upd.exhAny, Upd.rwBy_exhAny hf hn U, Rhs.rwBy_exhB σ hf hn r]
  | _, .pop U _ => Upd.rwBy_exhAny hf hn U
  | _, .drop U _ => Upd.rwBy_exhAny hf hn U

theorem Upd.rwBy_exhOk (hf : PickEq f σ) (hn : PickExh f σ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → (Upd.rwBy f U).exhOk σ = U.exhOk σ
  | _, .nil => rfl
  | _, .snoc U e => by
    have he : (UpdElem.rwBy f e).exhB σ = e.exhB σ := UpdElem.rwBy_exhB σ hf hn e
    have ho : (UpdElem.rwBy f e).okB σ = e.okB σ := by
      rw [← UpdElem.globT_isSome σ _ σ.globG, ← UpdElem.globT_isSome σ e σ.globG,
        UpdElem.rwBy_globT_eq σ hf e]
    simp only [Upd.rwBy, Upd.exhOk, Upd.rwBy_exhOk hf hn U, he, ho]
  | _, .decl U _ r => by
    simp only [Upd.rwBy, Upd.exhOk, Upd.rwBy_exhOk hf hn U, Rhs.rwBy_eval_eq σ hf,
      Rhs.rwBy_exhB σ hf hn r]
  | _, .pop U _ => Upd.rwBy_exhOk hf hn U
  | _, .drop U _ => Upd.rwBy_exhOk hf hn U

theorem Upd.rwBy_exh (hf : PickEq f σ) (hn : PickExh f σ) {Δ : Ctx} (U : Upd C Γ Δ) :
    (Upd.rwBy f U).exh σ = U.exh σ := by
  simp only [Upd.exh, Upd.rwBy_exhAny σ hf hn U, Upd.rwBy_exhOk σ hf hn U]

/-- **An exact rewrite reads after the update as the update**, firing on
no storage term. -/
theorem Upd.rwBy_afterT (hf : PickEq f σ) (hn : PickExh f σ) {Δ : Ctx} (m : Modality)
    (U : Upd C Γ Δ) (p : State C Δ → Prop) : (Upd.rwBy f U).afterT m σ p ↔ U.afterT m σ p := by
  unfold Upd.afterT
  rw [Upd.rwBy_globT_eq σ hf U]
  split
  · rw [Upd.rwBy_exh σ hf hn U]
  · rename_i g _
    simp only [Upd.rwBy_lands_iff σ hf U g]

end RwByEval

/-! ### At the empty scope: a closed term's rewrite -/

section RwC

variable {Γ : Ctx} {p : PrimTy}

/-- `q.2` for a closed value term reading `q.1`, at its type. -/
def Tm.pickClosed (q : Tm C [] (.val p) × Tm C [] (.val p)) :
    {s : Srt} → Tm C Γ s → Option (Tm C Γ s)
  | .val p', t =>
    if h : p = p' then
      if t.closedAs (h ▸ q.1) then some (Tm.ofNil (h ▸ q.2)) else none
    else none
  | _, _ => none

/-- Every closed occurrence of `q.1` in a term, replaced by `q.2`. -/
abbrev Tm.rwC (q : Tm C [] (.val p) × Tm C [] (.val p)) {s : Srt} (t : Tm C Γ s) : Tm C Γ s :=
  Tm.rwBy (Tm.pickClosed q) t

/-- A right-hand side rewritten. -/
abbrev Rhs.rwC (q : Tm C [] (.val p) × Tm C [] (.val p)) {t : LTy} (r : Rhs C Γ t) : Rhs C Γ t :=
  Rhs.rwBy (Tm.pickClosed q) r

/-- An element's right-hand sides rewritten. -/
abbrev UpdElem.rwC {Δ : Ctx} (q : Tm C [] (.val p) × Tm C [] (.val p)) (e : UpdElem C Γ Δ) :
    UpdElem C Γ Δ :=
  UpdElem.rwBy (Tm.pickClosed q) e

/-- An update's right-hand sides rewritten. -/
abbrev Upd.rwC (q : Tm C [] (.val p) × Tm C [] (.val p)) {Δ : Ctx} (U : Upd C Γ Δ) :
    Upd C Γ Δ :=
  Upd.rwBy (Tm.pickClosed q) U

variable {q : Tm C [] (.val p) × Tm C [] (.val p)}

theorem Tm.pickClosed_le (hq : Tm.EvalRefines q.1 q.2) (σ : State C Γ) :
    PickLe (Tm.pickClosed q) σ := by
  intro s t t' h
  cases s with
  | val p' =>
    simp only [Tm.pickClosed] at h
    split at h
    · rename_i e
      subst e
      split at h
      · rename_i hc
        cases h
        rw [Tm.eval_closedAs hc σ, Tm.eval_ofNil σ]
        exact hq σ.toNil
      · cases h
    · cases h
  | _ => simp only [Tm.pickClosed, reduceCtorEq] at h

/-- **Under the box, a rewritten update gives the update.** -/
theorem holds_upd_rwC (hq : Tm.EvalRefines q.1 q.2) {Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ}
    (σ : State C Γ) (h : holds σ (.upd .box (U.rwC q) φ)) : holds σ (.upd .box U φ) :=
  Upd.afterT_of_lands (fun _ _ => .inl trivial)
    (fun _ _ hL => Upd.rwBy_lands σ (Tm.pickClosed_le hq σ) U hL) h

end RwC

section RwEq

variable {Γ : Ctx} {p : PrimTy}

/-- A side of an equation, made `q.2` where it is a closed term reading
`q.1`, at its type. -/
def Tm.sideC (q : Tm C [] (.val p) × Tm C [] (.val p)) {p' : PrimTy} (t : Tm C Γ (.val p')) :
    Tm C Γ (.val p') :=
  if h : p = p' then (if t.closedAs (h ▸ q.1) then Tm.ofNil (h ▸ q.2) else t) else t

/-- `Fml.rwEqC`'s compiled twin. -/
def Fml.rwEqCM (q : Tm C [] (.val p) × Tm C [] (.val p)) : {Γ : Ctx} → Fml C Γ → Fml C Γ
  | _, .tt => .tt
  | _, .eq a b => .eq (a.sideC q) (b.sideC q)
  | _, .wellFormed s => .wellFormed s
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
def Fml.rwEqC (q : Tm C [] (.val p) × Tm C [] (.val p)) {Γ : Ctx} (φ : Fml C Γ) : Fml C Γ :=
  Fml.rec (motive := fun Γ _ => Fml C Γ)
    (tt := .tt) (eq := fun a b => .eq (a.sideC q) (b.sideC q)) (wellFormed := fun s => .wellFormed s)
    (not := fun _ ih => .not ih) (and := fun _ _ ihφ ihψ => .and ihφ ihψ)
    (imp := fun _ _ ihφ ihψ => .imp ihφ ihψ) (upd := fun m U _ ih => .upd m U ih)
    (modal := fun m P κ _ ih => .modal m P κ ih) (havoc := fun _ ih => .havoc ih)
    (all := fun x p _ ih => .all x p ih) (bind := fun m x t _ ih => .bind m x t ih)
    (anon := fun xs _ ih => .anon xs ih) φ

section Clauses

variable (q : Tm C [] (.val p) × Tm C [] (.val p))

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
theorem Fml.rwEqC_all (x : Var) (p' : PrimTy) (φ : Fml C (.val p' :: Γ)) :
    (Fml.all x p' φ).rwEqC q = .all x p' (φ.rwEqC q) := rfl
theorem Fml.rwEqC_bind (m : Modality) (x : Var) (t : LTy) (φ : Fml C (t :: Γ)) :
    (Fml.bind m x t φ).rwEqC q = .bind m x t (φ.rwEqC q) := rfl
theorem Fml.rwEqC_anon (xs : List ((t : LTy) × Idx Γ t)) (φ : Fml C Γ) :
    (Fml.anon xs φ).rwEqC q = .anon xs (φ.rwEqC q) := rfl

/-- The recursor's rewrite is the twin's. -/
theorem Fml.rwEqC_eq_rwEqCM (φ : Fml C Γ) : φ.rwEqC q = φ.rwEqCM q := by
  induction φ with
  | tt | eq | wellFormed => rfl
  | not φ ih | upd m U φ ih | modal m P κ φ ih | havoc φ ih | all x p φ ih | bind m x t φ ih
  | anon xs φ ih => simp only [Fml.rwEqCM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => simp only [Fml.rwEqCM, ← ihφ, ← ihψ]; rfl

end Clauses

theorem Tm.sideC_denote {q : Tm C [] (.val p) × Tm C [] (.val p)} (hq : Tm.Theq q.1 q.2)
    (σ : State C Γ) {p' : PrimTy} (t : Tm C Γ (.val p')) :
    (t.sideC q).denote σ = t.denote σ := by
  unfold Tm.sideC
  split
  · rename_i e
    subst e
    split
    · rename_i hc
      rw [Tm.denote_ofNil σ, Tm.denote_closedAs hc σ]
      exact (hq σ.toNil).symm
    · rfl
  · rfl

/-- **A formula rewritten by a Theory equation holds where it does.** -/
theorem Fml.rwEqC_holds {q : Tm C [] (.val p) × Tm C [] (.val p)} (hq : Tm.Theq q.1 q.2) :
    {Γ : Ctx} → (φ : Fml C Γ) → ∀ σ : State C Γ, (holds σ (φ.rwEqC q) ↔ holds σ φ)
  | _, .tt, _ => Iff.rfl
  | _, .eq a b, σ => by
    show holds σ (.eq (a.sideC q) (b.sideC q)) ↔ holds σ (.eq a b)
    rw [holds_eq, holds_eq]
    rw [Tm.sideC_denote hq σ a, Tm.sideC_denote hq σ b]
  | _, .wellFormed _, _ => Iff.rfl
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
  unless ty.isAppOfArity ``Tm 3 && (← whnf (ty.getArg! 2)).isAppOfArity ``Srt.val 1 do return none
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
