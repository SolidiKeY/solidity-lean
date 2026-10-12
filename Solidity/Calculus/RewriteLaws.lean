import Solidity.Calculus.RewritePast
import Solidity.Calculus.HoldsErase
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

**The law is the erasure's.**  solkey's taclets are transcribed once, on
`Update.lean`'s terms (`TermTaclet`, `EvalLaw`), with what makes them exact
in an update (`Upd.covers`, `Upd.coversRef`, `Upd.coversEval`,
`Term.base?`: `LineRw.lawUpdAny`, `lawUpdRef`, `lawUpdEq`, `lawUpdEval`).
Here they are read on the scoped update through its erasure
(`ErasedCov`): a scoped term reads as its erasure (`Tm.eval_erase`) and an
update returns where its erasure does (`Upd.apply_erase`).

**The rewrite.**  The law's two sides are scoped terms at one sort and at
the update's scope (`LawPair`), the erasure's read back at the update's
names (`Tm.resolveN`); every occurrence of the left side in an update's
right-hand sides becomes the right side (`Tm.rwG`, `Upd.rwG`, any sort: a
memory law rewrites an identity too).

**Why it holds.**  The right side returns what the left side returns
(`LawPair.Refines`), so where the update returns its rewrite returns the
same state (`Upd.rwG_apply`).  Where the rewritten update returns, its
erasure returns, and the erasure's law refines back there
(`LawPair.back_ofErased`), so the update returns the same state
(`Upd.rwG_apply_rev`).  Two updates that halt in the same states and
return the same states are one to either modality (`holds_upd_rwG`).

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

/-- The right side returns what the left side returns, in every state. -/
def LawPair.Refines {Γ : Ctx} (q : LawPair C Γ) : Prop :=
  ∀ σ : EState C Γ, Srt.Le q.k (q.lhs.eval σ) (q.rhs.eval σ)

section Rw

variable {Γ : Ctx} (q : LawPair C Γ)

/-- `t` reads the law's left side. -/
def Tm.firesG {s : Srt} (t : Tm C Γ s) : Bool := t.beqR q.lhs

/-- `t` replaced by the law's right side where it reads the left side, else `d`. -/
def Tm.pickG {s : Srt} (t d : Tm C Γ s) : Tm C Γ s :=
  if t.firesG q then
    match q.rhsAt? s with
    | some r => r
    | none => d
  else d

/-- Every occurrence of the law's left side in a term, replaced by its
right side. -/
def Tm.rwG : {s : Srt} → Tm C Γ s → Tm C Γ s
  | _, .pvV i => .pvV i
  | _, .pvP i => .pvP i
  | _, .pvS i => .pvS i
  | _, .pvI i => .pvI i
  | _, .netOf i a => .netOf i (Tm.rwG a)
  | _, .app0 o => Tm.pickG q (.app0 o) (.app0 o)
  | _, .app1 o ho x => Tm.pickG q (.app1 o ho x) (.app1 o ho (Tm.rwG x))
  | _, .app2 o x y => Tm.pickG q (.app2 o x y) (.app2 o (Tm.rwG x) (Tm.rwG y))
  | _, .app3 o x y z => Tm.pickG q (.app3 o x y z) (.app3 o (Tm.rwG x) (Tm.rwG y) (Tm.rwG z))

/-- A right-hand side rewritten. -/
def Rhs.rwG : {t : LTy} → Rhs C Γ t → Rhs C Γ t
  | _, .val t => .val (Tm.rwG q t)
  | _, .path p => .path (Tm.rwG q p)
  | _, .unset => .unset
  | _, .mref i => .mref (Tm.rwG q i)
  | _, .store s => .store (Tm.rwG q s)
  | _, .saveNet => .saveNet
  | _, .saveNetMt => .saveNetMt

/-- An element's right-hand sides rewritten. -/
def UpdElem.rwG {Δ : Ctx} : UpdElem C Γ Δ → UpdElem C Γ Δ
  | .local i r => .local i (Rhs.rwG q r)
  | .storage s => .storage (Tm.rwG q s)
  | .memory m => .memory (Tm.rwG q m)
  | .selfBalance op a => .selfBalance op (Tm.rwG q a)
  | .net r op a => .net (Tm.rwG q r) op (Tm.rwG q a)
  | .pay r a => .pay (Tm.rwG q r) (Tm.rwG q a)
  | .netMt r a => .netMt (Tm.rwG q r) (Tm.rwG q a)
  | .setBalance a => .setBalance (Tm.rwG q a)

/-- An update's right-hand sides rewritten. -/
def Upd.rwG : {Δ : Ctx} → Upd C Γ Δ → Upd C Γ Δ
  | _, .nil => .nil
  | _, .snoc U e => .snoc (Upd.rwG U) (UpdElem.rwG q e)
  | _, .decl U x r => .decl (Upd.rwG U) x (Rhs.rwG q r)
  | _, .pop U h => .pop (Upd.rwG U) h
  | _, .drop U h => .drop (Upd.rwG U) h

/-- Whether `Tm.rwG` rewrites something in a term. -/
def Tm.hasG : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ => false
  | _, .netOf _ a => Tm.hasG a
  | _, t@(.app0 _) => Tm.firesG q t
  | _, t@(.app1 _ _ x) => Tm.firesG q t || Tm.hasG x
  | _, t@(.app2 _ x y) => Tm.firesG q t || Tm.hasG x || Tm.hasG y
  | _, t@(.app3 _ x y z) => Tm.firesG q t || Tm.hasG x || Tm.hasG y || Tm.hasG z

/-- Whether `Rhs.rwG` rewrites something. -/
def Rhs.hasG : {t : LTy} → Rhs C Γ t → Bool
  | _, .val t => Tm.hasG q t
  | _, .path p => Tm.hasG q p
  | _, .mref i => Tm.hasG q i
  | _, .store s => Tm.hasG q s
  | _, _ => false

/-- Whether `UpdElem.rwG` rewrites something. -/
def UpdElem.hasG {Δ : Ctx} : UpdElem C Γ Δ → Bool
  | .local _ r => Rhs.hasG q r
  | .storage s => Tm.hasG q s
  | .memory m => Tm.hasG q m
  | .selfBalance _ a | .setBalance a => Tm.hasG q a
  | .net r _ a | .pay r a | .netMt r a => Tm.hasG q r || Tm.hasG q a

/-- Whether `Upd.rwG` rewrites something. -/
def Upd.hasG : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => false
  | _, .snoc U e => Upd.hasG U || UpdElem.hasG q e
  | _, .decl U _ r => Upd.hasG U || Rhs.hasG q r
  | _, .pop U _ | _, .drop U _ => Upd.hasG U

end Rw

/-! ## The rewrite read -/

section RwEval

variable {Γ : Ctx} {q : LawPair C Γ}

/-- Where a term reads the law's left side, it is the left side, and the
replacement is the right side. -/
theorem Tm.pickG_fires {s : Srt} {t : Tm C Γ s} (h : Tm.firesG q t = true) :
    ∃ (e : q.k = s), t = e ▸ q.lhs ∧ q.rhsAt? s = some (e ▸ q.rhs) := by
  have he := Tm.eq_of_beqM t q.lhs ((Tm.beqR_eq_beqM t q.lhs).symm.trans h)
  cases q with
  | mk lhs rhs =>
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj he
    cases hh
    exact ⟨rfl, rfl, by simp only [LawPair.rhsAt?, dif_pos]⟩

/-- **A law that refines keeps every value a term returns** (forward). -/
theorem Tm.pickG_eval (hq : q.Refines) (σ : EState C Γ) {s : Srt} {t d : Tm C Γ s}
    (hd : Srt.Le s (t.eval σ) (d.eval σ)) : Srt.Le s (t.eval σ) ((Tm.pickG q t d).eval σ) := by
  unfold Tm.pickG
  split
  · rename_i hc
    obtain ⟨e, ht, hr⟩ := Tm.pickG_fires hc
    rw [hr]
    subst e ht
    exact hq σ
  · exact hd

/-- **A law that refines back at one state keeps every value its rewrite
returns there** (reverse, pointwise). -/
theorem Tm.pickG_eval_rev (σ : EState C Γ) (hq : Srt.Le q.k (q.rhs.eval σ) (q.lhs.eval σ))
    {s : Srt} {t d : Tm C Γ s} (hd : Srt.Le s (d.eval σ) (t.eval σ)) :
    Srt.Le s ((Tm.pickG q t d).eval σ) (t.eval σ) := by
  unfold Tm.pickG
  split
  · rename_i hc
    obtain ⟨e, ht, hr⟩ := Tm.pickG_fires hc
    rw [hr]
    subst e ht
    exact hq
  · exact hd

theorem Tm.rwG_eval (hq : q.Refines) (σ : EState C Γ) :
    {s : Srt} → (t : Tm C Γ s) → Srt.Le s (t.eval σ) ((Tm.rwG q t).eval σ)
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ => Srt.Le.refl _ _
  | _, .netOf _ a => Res.Le.bind (Tm.rwG_eval hq σ a) fun _ => Res.Le.refl _
  | _, .app0 _ => Tm.pickG_eval hq σ (Srt.Le.refl _ _)
  | _, .app1 o _ x => Tm.pickG_eval hq σ (o.eval_le (Tm.rwG_eval hq σ x))
  | _, .app2 o x y => Tm.pickG_eval hq σ (o.eval_le (Tm.rwG_eval hq σ x) (Tm.rwG_eval hq σ y))
  | _, .app3 o x y z =>
    Tm.pickG_eval hq σ (o.eval_le (Tm.rwG_eval hq σ x) (Tm.rwG_eval hq σ y) (Tm.rwG_eval hq σ z))

theorem Tm.rwG_eval_rev (σ : EState C Γ) (hq : Srt.Le q.k (q.rhs.eval σ) (q.lhs.eval σ)) :
    {s : Srt} → (t : Tm C Γ s) → Srt.Le s ((Tm.rwG q t).eval σ) (t.eval σ)
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ => Srt.Le.refl _ _
  | _, .netOf _ a => Res.Le.bind (Tm.rwG_eval_rev σ hq a) fun _ => Res.Le.refl _
  | _, .app0 _ => Tm.pickG_eval_rev σ hq (Srt.Le.refl _ _)
  | _, .app1 o _ x => Tm.pickG_eval_rev σ hq (o.eval_le (Tm.rwG_eval_rev σ hq x))
  | _, .app2 o x y =>
    Tm.pickG_eval_rev σ hq (o.eval_le (Tm.rwG_eval_rev σ hq x) (Tm.rwG_eval_rev σ hq y))
  | _, .app3 o x y z => Tm.pickG_eval_rev σ hq
      (o.eval_le (Tm.rwG_eval_rev σ hq x) (Tm.rwG_eval_rev σ hq y) (Tm.rwG_eval_rev σ hq z))

theorem Rhs.rwG_eval (hq : q.Refines) (σ : EState C Γ) {t : LTy} (r : Rhs C Γ t) :
    Res.Le (r.eval σ) ((Rhs.rwG q r).eval σ) := by
  cases r with
  | val t => exact Tm.rwG_eval hq σ t
  | path p => exact Res.Le.bind (Tm.rwG_eval hq σ p) fun _ => Res.Le.refl _
  | unset => exact Res.Le.refl _
  | mref i => exact Res.Le.bind (Tm.rwG_eval hq σ i) fun _ => Res.Le.refl _
  | store s => exact Res.Le.bind (Tm.rwG_eval hq σ s) fun _ => Res.Le.refl _
  | saveNet => exact Res.Le.refl _
  | saveNetMt => exact Res.Le.refl _

theorem Rhs.rwG_eval_rev (σ : EState C Γ) (hq : Srt.Le q.k (q.rhs.eval σ) (q.lhs.eval σ))
    {t : LTy} (r : Rhs C Γ t) : Res.Le ((Rhs.rwG q r).eval σ) (r.eval σ) := by
  cases r with
  | val t => exact Tm.rwG_eval_rev σ hq t
  | path p => exact Res.Le.bind (Tm.rwG_eval_rev σ hq p) fun _ => Res.Le.refl _
  | unset => exact Res.Le.refl _
  | mref i => exact Res.Le.bind (Tm.rwG_eval_rev σ hq i) fun _ => Res.Le.refl _
  | store s => exact Res.Le.bind (Tm.rwG_eval_rev σ hq s) fun _ => Res.Le.refl _
  | saveNet => exact Res.Le.refl _
  | saveNetMt => exact Res.Le.refl _

theorem UpdElem.rwG_write (hq : q.Refines) {Δ : Ctx} (σ₀ : EState C Γ)
    (e : UpdElem C Γ Δ) (τ : EState C Δ) : Res.Le (e.write σ₀ τ) ((UpdElem.rwG q e).write σ₀ τ) := by
  have hv := fun t : Tm C Γ .val => Tm.rwG_eval hq σ₀ t
  cases e with
  | «local» i r => exact Res.Le.bind (Rhs.rwG_eval hq σ₀ r) fun _ => Res.Le.refl _
  | storage s => exact Res.Le.bind (Tm.rwG_eval hq σ₀ s) fun _ => Res.Le.refl _
  | memory m => exact Res.Le.bind (Tm.rwG_eval hq σ₀ m) fun _ => Res.Le.refl _
  | selfBalance op a => exact Res.Le.bind (hv a) fun _ => Res.Le.refl _
  | net r op a | pay r a | netMt r a =>
    refine Res.Le.bind (hv r) fun _ => Res.Le.bind (Res.Le.refl _) fun _ => ?_
    exact Res.Le.bind (hv a) fun _ => Res.Le.refl _
  | setBalance a => exact Res.Le.bind (hv a) fun _ => Res.Le.refl _

theorem UpdElem.rwG_write_rev {Δ : Ctx} (σ₀ : EState C Γ)
    (hq : Srt.Le q.k (q.rhs.eval σ₀) (q.lhs.eval σ₀)) (e : UpdElem C Γ Δ)
    (τ : EState C Δ) : Res.Le ((UpdElem.rwG q e).write σ₀ τ) (e.write σ₀ τ) := by
  have hv := fun t : Tm C Γ .val => Tm.rwG_eval_rev σ₀ hq t
  cases e with
  | «local» i r => exact Res.Le.bind (Rhs.rwG_eval_rev σ₀ hq r) fun _ => Res.Le.refl _
  | storage s => exact Res.Le.bind (Tm.rwG_eval_rev σ₀ hq s) fun _ => Res.Le.refl _
  | memory m => exact Res.Le.bind (Tm.rwG_eval_rev σ₀ hq m) fun _ => Res.Le.refl _
  | selfBalance op a => exact Res.Le.bind (hv a) fun _ => Res.Le.refl _
  | net r op a | pay r a | netMt r a =>
    refine Res.Le.bind (hv r) fun _ => Res.Le.bind (Res.Le.refl _) fun _ => ?_
    exact Res.Le.bind (hv a) fun _ => Res.Le.refl _
  | setBalance a => exact Res.Le.bind (hv a) fun _ => Res.Le.refl _

/-- A map of an update's states keeps `Res.Le`. -/
theorem Res.Le.map {α β : Type} {a b : Res α} (f : α → β) (h : Res.Le a b) :
    Res.Le (a.map f) (b.map f) := fun y hy => by
  cases ha : a with
  | error => rw [ha] at hy; cases hy
  | ok x => rw [ha] at hy; cases hy; rw [h x ha]; rfl

/-- **Where an update returns, its rewrite returns the same state.** -/
theorem Upd.rwG_apply (hq : q.Refines) (σ₀ : EState C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → Res.Le (U.apply σ₀) ((Upd.rwG q U).apply σ₀)
  | _, .nil => Res.Le.refl _
  | _, .snoc U e => Res.Le.bind (Upd.rwG_apply hq σ₀ U) fun τ => UpdElem.rwG_write hq σ₀ e τ
  | _, .decl U _ r => Res.Le.bind (Upd.rwG_apply hq σ₀ U) fun _ =>
      Res.Le.bind (Rhs.rwG_eval hq σ₀ r) fun _ => Res.Le.refl _
  | _, .pop U h => Res.Le.map (EState.drop h) (Upd.rwG_apply hq σ₀ U)
  | _, .drop U h => Res.Le.map (EState.thin h) (Upd.rwG_apply hq σ₀ U)

/-- **Where the rewrite returns, at a state where the law refines back, the
update returns the same state.** -/
theorem Upd.rwG_apply_rev (σ₀ : EState C Γ) (hq : Srt.Le q.k (q.rhs.eval σ₀) (q.lhs.eval σ₀)) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → Res.Le ((Upd.rwG q U).apply σ₀) (U.apply σ₀)
  | _, .nil => Res.Le.refl _
  | _, .snoc U e => Res.Le.bind (Upd.rwG_apply_rev σ₀ hq U) fun τ => UpdElem.rwG_write_rev σ₀ hq e τ
  | _, .decl U _ r => Res.Le.bind (Upd.rwG_apply_rev σ₀ hq U) fun _ =>
      Res.Le.bind (Rhs.rwG_eval_rev σ₀ hq r) fun _ => Res.Le.refl _
  | _, .pop U h => Res.Le.map (EState.drop h) (Upd.rwG_apply_rev σ₀ hq U)
  | _, .drop U h => Res.Le.map (EState.thin h) (Upd.rwG_apply_rev σ₀ hq U)

end RwEval

/-! ## A law of the erasure, in an update's right-hand sides

The erasure's laws in an update's right-hand sides (`LineRw.lawUpdAny`,
`lawUpdRef`, `lawUpdEq`, `lawUpdEval`), read on the scoped update through
its erasure: a scoped term reads as its erasure (`Tm.eval_erase`), and the
update returns where its erasure does (`Upd.apply_erase`).  The law is the
erasure's, solkey's taclet (`TermTaclet`, `EvalLaw`); the scoped line only
carries its two sides, read back at the update's scope. -/

section Erased

/-- The sorts whose readings carry no locals (`Srt.wl` is the identity). -/
def Srt.plain : Srt → Bool
  | .st | .mem => false
  | _ => true

theorem Srt.wl_plain {k : Srt} (h : k.plain = true) (e : List (Var × Semantics.Binding)) (x : k.Ev) :
    Srt.wl e k x = x := by
  cases k <;> first | rfl | cases h

/-- An erased law at an update's right-hand sides: the right side returns
what the left side does (`fwd`), and wherever an update the check `chk`
accepts returns, the left side returns what the right side does (`back`). -/
structure ErasedCov (C : Contract) (u : Srt) (t t' : Surface.Tm C u) where
  chk : Surface.Upd C → Bool
  fwd : Surface.Tm.EvalRefinesAt t t'
  back : ∀ (U : Surface.Upd C) (σ τ : Semantics.State), chk U = true → Surface.Upd.apply U σ = .ok τ →
    Srt.Le u (t'.eval σ) (t.eval σ)

/-- A term taclet onto a term that cannot halt, where the update holds the
write it reads back (`LineRw.lawUpdAny`, `Upd.covers`). -/
def ErasedCov.covered {t t' : Term C} (r : TermTaclet t t') (ht : t'.total = true) :
    ErasedCov C .val t t' :=
  ⟨fun U => U.covers (t, t'), (Term.EvalRefines.of_theq r.sound ht).at,
    fun _ _ _ hc hU => Surface.Upd.covers_le (Term.EvalRefines.of_theq r.sound ht) hc hU⟩

/-- A frame or delete-value law, where the update holds its storage
operation (`LineRw.lawUpdRef`, `Upd.coversRef`). -/
def ErasedCov.ref {t t' : Term C} {r : TermTaclet t t'} (hr : TermTaclet.RefLaw r) :
    ErasedCov C .val t t' :=
  ⟨fun U => U.coversRef (t, t'), hr.evalRefines.at, fun _ _ _ hc hU => hr.back hc hU⟩

/-- Two terms that are one read member-wise (`Term.base?`). -/
def Term.sameBase (t t' : Term C) : Bool := (Term.base? t).isSome && (Term.base? t == Term.base? t')

/-- A member-wise law: its two terms are one read member-wise
(`LineRw.lawUpdEq`, `Term.base_eval`). -/
def ErasedCov.eqv {t t' : Term C} (h : Term.sameBase t t' = true) : ErasedCov C .val t t' :=
  ⟨fun _ => true,
    fun σ => by
      simp only [Term.sameBase, Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
      obtain ⟨⟨b, hb⟩, he⟩ := h
      exact ((Term.base_eval t hb σ).trans (Term.base_eval t' (he ▸ hb) σ).symm).le,
    fun _ σ _ _ _ => by
      simp only [Term.sameBase, Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
      obtain ⟨⟨b, hb⟩, he⟩ := h
      exact ((Term.base_eval t hb σ).trans (Term.base_eval t' (he ▸ hb) σ).symm).ge⟩

/-- A memory law, where the update holds the write it reads past
(`LineRw.lawUpdEval`, `Upd.coversEval`). -/
def ErasedCov.eval {u : Srt} {t t' : Surface.Tm C u} (r : EvalLaw t t') : ErasedCov C u t t' :=
  ⟨fun U => U.coversEval (t, t'), r.sound, fun _ _ _ hc hU => r.back hc hU⟩

variable {Γ₀ : Ctx} {ns : List Var}

/-- **A law refines where its erasure does**, at a sort that carries no locals. -/
theorem LawPair.refines_ofErased {q : LawPair C Γ₀} (hnd : ns.Nodup) (hlen : ns.length = Γ₀.length)
    (hp : q.k.plain = true) (hf : Surface.Tm.EvalRefinesAt (q.lhs.erase ns) (q.rhs.erase ns)) :
    q.Refines := fun σ => by
  have hag := Agree.erase σ hnd hlen
  have h := hf (σ.erase ns)
  rw [Tm.eval_erase hag, Tm.eval_erase hag, Srt.wl_plain hp, Srt.wl_plain hp] at h
  exact h

/-- **Where an update its erased law accepts returns, the law refines back.** -/
theorem LawPair.back_ofErased {q : LawPair C Γ₀} (hnd : ns.Nodup) (hlen : ns.length = Γ₀.length)
    (hp : q.k.plain = true) (E : ErasedCov C q.k (q.lhs.erase ns) (q.rhs.erase ns)) {Δ : Ctx}
    {U : Upd C Γ₀ Δ} (hc : E.chk (U.eraseNR ns).1 = true) (hfr : U.freshB ns = true)
    (σ₀ : EState C Γ₀) {τ : EState C Δ} (hU : U.apply σ₀ = .ok τ) :
    Srt.Le q.k (q.rhs.eval σ₀) (q.lhs.eval σ₀) := by
  have hag := Agree.erase σ₀ hnd hlen
  have hrel := Upd.apply_erase hag U (Upd.freshB_sound U hfr)
  rw [hU] at hrel
  rw [Upd.eraseNR_eq] at hc
  cases he : Surface.Upd.apply (U.erase ns) (σ₀.erase ns) with
  | error e => rw [he] at hrel; exact (hrel : False).elim
  | ok τ' =>
    have h := E.back _ _ _ hc he
    rw [Tm.eval_erase hag, Tm.eval_erase hag, Srt.wl_plain hp, Srt.wl_plain hp] at h
    exact h

/-- **A law in an update's right-hand sides, under any modality**, where it
refines, and refines back wherever the rewritten update returns. -/
theorem holds_upd_rwG {q : LawPair C Γ₀} (hr : q.Refines) {m : Modality} {Δ : Ctx}
    {U : Upd C Γ₀ Δ} {φ : Fml C Δ} (σ : State C Γ₀)
    (hb : ∀ τ, (Upd.rwG q U).apply σ.erase = .ok τ →
      Srt.Le q.k (q.rhs.eval σ.erase) (q.lhs.eval σ.erase))
    (h : holds σ (.upd m (Upd.rwG q U) φ)) : holds σ (.upd m U φ) := by
  show m.afterC _ (U.apply σ.erase)
  have h : m.afterC _ ((Upd.rwG q U).apply σ.erase) := h
  have hle := Upd.rwG_apply hr σ.erase U
  cases hB : (Upd.rwG q U).apply σ.erase with
  | ok τ =>
    have hA := Upd.rwG_apply_rev σ.erase (hb τ hB) U τ hB
    rw [hA]; rw [hB] at h; exact h
  | error e =>
    cases hA : U.apply σ.erase with
    | ok τ => rw [hle τ hA] at hB; cases hB
    | error e' => rw [hB] at h; exact h

/-- The erased law `E` in the right-hand sides of `{U}_m φ`, `U` at the law's scope. -/
def Fml.updRwE (q : LawPair C Γ₀) (ns : List Var) (E : ErasedCov C q.k (q.lhs.erase ns) (q.rhs.erase ns))
    {Δ : Ctx} (m : Modality) (U : Upd C Γ₀ Δ) (φ : Fml C Δ) : Option (Fml C Γ₀) :=
  if (Upd.hasG q U && E.chk ((Upd.rwG q U).eraseNR ns).1 && (Upd.rwG q U).freshB ns) = true then
    some (.upd m (Upd.rwG q U) φ)
  else none

/-- `Fml.updRwE` on an update read at the law's scope `Γ₀`. -/
def Fml.updRwEAt (q : LawPair C Γ₀) (ns : List Var) (E : ErasedCov C q.k (q.lhs.erase ns) (q.rhs.erase ns))
    {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) : Option (Fml C Γ) :=
  if h : Γ = Γ₀ then
    cast (congrArg (fun G => Option (Fml C G)) h.symm)
      (Fml.updRwE q ns E m (cast (congrArg (fun G => Upd C G Δ) h) U) φ)
  else none

/-- **`updRw` past the program, by the erasure's law**: the law `E` in the
right-hand sides of the update at position `i`, under any modality, its two
sides read at the update's scope `Γ₀` with the names `ns`. -/
def FmlRw.lawUpdE (q : LawPair C Γ₀) (ns : List Var) (hnd : ns.Nodup) (hlen : ns.length = Γ₀.length)
    (hp : q.k.plain = true) (E : ErasedCov C q.k (q.lhs.erase ns) (q.rhs.erase ns)) (i : Nat) :
    FmlRw C :=
  FmlRw.atSpine (fun m U φ => Fml.updRwEAt q ns E m U φ) (fun {Γ _ m U φ ψ} h σ hψ => by
    dsimp only [Fml.updRwEAt] at h
    split at h
    · rename_i he
      subst he
      simp only [cast_eq] at h
      dsimp only [Fml.updRwE] at h
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true] at hc
        obtain ⟨⟨-, hc⟩, hfr⟩ := hc
        exact holds_upd_rwG (q.refines_ofErased hnd hlen hp E.fwd) σ
          (fun _ hB => LawPair.back_ofErased hnd hlen hp E hc hfr _ hB) hψ
      · cases h
    · cases h) i

/-- The named scopes of the updates along the spine: each update's context
and the names its locals erase to. -/
def Fml.spineScopes : (Γ : Ctx) → List Var → Fml C Γ → List (Ctx × List Var)
  | _, ns, .all x _ φ => Fml.spineScopes _ (x :: ns) φ
  | _, ns, .bind _ x _ φ => Fml.spineScopes _ (x :: ns) φ
  | Γ, ns, .upd _ U ψ => (Γ, ns) :: Fml.spineScopes _ (U.names ns) ψ
  | _, _, _ => []

/-- The erased law's two sides read at a named scope, quoted: `none` where a
side names no local of the scope. -/
def lawResolveQ (c : Lean.Expr) (Γ : Ctx) (ns : List Var) {u : Srt} (t t' : Surface.Tm C u) :
    Option (Lean.Expr × Lean.Expr) :=
  match Tm.resolveN (ns.zip Γ) t, Tm.resolveN (ns.zip Γ) t' with
  | .ok a, .ok b => some (Tm.quote c a, Tm.quote c b)
  | _, _ => none

end Erased

end Solidity
