import Solidity.Calculus.Logic
import Solidity.Calculus.FirstOrder
import Solidity.Semantics.StateErase
import Solidity.Calculus.StateFacts

/-!
# One update for two: `sequentialToParallel`'s side conditions on scoped updates

KeY's `sequentialToParallel2` (`{u}{u2}φ ⇝ {u ‖ {u}u2}φ`) on the scoped
updates of `Calculus/Fml.lean`: what the sequent's `merge`
(`Calculus/Proves.lean`) and the chains' `~[sequentialToParallel]~>`
(`Calculus/Merge.lean`) compute, and why it is sound.

`{U}{V}φ` becomes `{W}φ`, `W` the elements of `U` and then those of `V`, each
right-hand side of `V` read in `U`'s state (`Upd.seqPar`): its locals
replaced by what `U` leaves in them (`Upd.held`: a local of the state `U` is
applied in, or the right-hand side `U` last wrote to it), and `storage` by
the storage `U` last wrote, where `U` writes no other global part
(`Upd.lastSt`, solkey's `{storage := s}{x := find(storage, p)}` ⇝
`{storage := s ‖ x := find(s, p)}`).  Any other symbol of `V` that reads
the global part (`memory`, a bounds check) is read the same only where `U`
writes no global part (`Upd.envOnly`); any other merge is refused (`none`),
never wrong.  An `.st` term changes only the storage of the state it is read
in (`Tm.eval_st_glob`), so `s` read before `U` is the state after it.

An update moves under a hidden binder when it declares nothing
(`Upd.lift?`), the binder not at a memory type or the update allocating
nothing (`LTy.notMem`, `Upd.keepsNext`): `Fml.upd_bind_of_lift`.

The last box update's right-hand sides rewritten by a term taclet
(`Upd.rwC`, `Proves.updRw`) is `Calculus/SeqRewrite.lean`'s.

The functions use `match` on the indexed families, against Gate G0's first
condition: an exemption (`docs/intrinsic.md`, W3b's merge, extended to the
sequent's update rules in W3c `tactics`, both timed), since they run once a
rule and not once a step.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)
open Semantics (Res)

variable {C : Contract}

/-! ## The atoms, read on the typed state -/

/-- An equation of `holds`, read by the typed readers. -/
theorem holds_eqT {Γ : Ctx} (σ : State C Γ) (a b : Tm C Γ .val) :
    holds σ (.eq a b) ↔ Theory.StValue.Equiv (a.denoteT σ) (b.denoteT σ) := by
  simp only [holds, Tm.denoteT_eq]

/-- A `defined` of `holds`, read by the typed readers. -/
theorem holds_definedT {Γ : Ctx} (σ : State C Γ) (t : Tm C Γ .val) :
    holds σ (.defined t) ↔ ∃ x, t.evalT σ = .ok x := by
  simp only [holds, Tm.evalT_eq]

/-! ## Symbols that read no global part -/

/-- A constant that reads nothing of the state. -/
def _root_.Solidity.Op0.globFree {s : Srt} : Op0 s → Bool
  | .lit _ | .root _ => true
  | _ => false

/-- A unary symbol that reads nothing of the state but its argument. -/
def _root_.Solidity.Op1.globFree {a s : Srt} : Op1 a s → Bool
  | .net | .next | .netOf _ => false
  | _ => true

/-- A binary symbol that reads nothing of the state but its arguments. -/
def _root_.Solidity.Op2.globFree {a b s : Srt} : Op2 a b s → Bool
  | .at => false
  | _ => true

theorem _root_.Solidity.Op0.eval_globFree {s : Srt} {o : Op0 s} (h : o.globFree = true)
    (g g' : Semantics.State) : o.eval g = o.eval g' := by
  cases o <;> first | rfl | cases h

theorem _root_.Solidity.Op1.eval_globFree {a s : Srt} {o : Op1 a s} (h : o.globFree = true)
    (g g' : Semantics.State) (x : a.Ev) : o.eval g x = o.eval g' x := by
  cases o <;> first | rfl | cases h

theorem _root_.Solidity.Op2.eval_globFree {a b s : Srt} {o : Op2 a b s} (h : o.globFree = true)
    (g g' : Semantics.State) (x : a.Ev) (y : b.Ev) : o.eval g x y = o.eval g' x y := by
  cases o <;> first | rfl | cases h

theorem _root_.Solidity.Op3.eval_any {a b c s : Srt} (o : Op3 a b c s) (g g' : Semantics.State)
    (x : a.Ev) (y : b.Ev) (z : c.Ev) : o.eval g x y z = o.eval g' x y z := by
  cases o <;> rfl


/-- An update that writes locals only: the global part of the state it is
applied in is the one it leaves. -/
def Upd.envOnly {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => true
  | _, .snoc U (.local _ _) => Upd.envOnly U
  | _, .snoc _ _ => false
  | _, .decl U _ _ => Upd.envOnly U
  | _, .pop U _ | _, .drop U _ => Upd.envOnly U

/-! ## Reading in the state before -/

/-- `storage` read before an update that last wrote the storage `st` (and no
other global part): `st` itself. -/
def Tm.storageAs {Γ : Ctx} (st : Option (Tm C Γ .st)) : {k : Srt} → Op0 k → Option (Tm C Γ k)
  | _, .storage => st
  | _, _ => none

section Subst

variable {Γ Δ : Ctx} (s : Subst C Γ Δ) (g : Bool) (st : Option (Tm C Γ .st))

/-- A term of `Δ` read in `Γ`: its locals replaced by what they hold; a
symbol that reads the global part only where `g` (the update wrote none). -/
def Tm.substH : {k : Srt} → Tm C Δ k → Option (Tm C Γ k)
  | _, .pvV i => match s i with
    | .pos j => some (.pvV j)
    | .rhs (.val t) => some t
  | _, .pvP i => match s i with
    | .pos j => some (.pvP j)
    | .rhs (.path p) => some p
    | .rhs .unset => none
  | _, .pvS i => match s i with
    | .pos j => if g then some (.pvS j) else none
    | .rhs _ => none
  | _, .pvI i => match s i with
    | .pos j => some (.pvI j)
    | .rhs (.mref t) => some t
  | _, .netOf i a => match s i with
    | .pos j => (Tm.substH a).map (.netOf j)
    | .rhs _ => none
  | _, .app0 o => if g || o.globFree then some (.app0 o) else Tm.storageAs st o
  | _, .app1 o ho x => if g || o.globFree then (Tm.substH x).map (.app1 o ho) else none
  | _, .app2 o x y =>
    if g || o.globFree then do pure (.app2 o (← Tm.substH x) (← Tm.substH y)) else none
  | _, .app3 o x y z => do pure (.app3 o (← Tm.substH x) (← Tm.substH y) (← Tm.substH z))

/-- A right-hand side of `Δ` read in `Γ`. -/
def Rhs.substH : {t : LTy} → Rhs C Δ t → Option (Rhs C Γ t)
  | _, .val t => (t.substH s g st).map .val
  | _, .path p => (p.substH s g st).map .path
  | _, .unset => some .unset
  | _, .mref i => (i.substH s g st).map .mref
  | _, .store x => (x.substH s g st).map .store
  | _, .saveNet => if g then some .saveNet else none
  | _, .saveNetMt => some .saveNetMt

/-- An element whose right-hand sides are read in `Δ`, read in `Γ`. -/
def UpdElem.substH {Ε : Ctx} : UpdElem C Δ Ε → Option (UpdElem C Γ Ε)
  | .local i r => (r.substH s g st).map (.local i)
  | .storage x => (x.substH s g st).map .storage
  | .memory m => (m.substH s g st).map .memory
  | .selfBalance op a => if g then (a.substH s g st).map (.selfBalance op) else none
  | .net r op a => do pure (.net (← r.substH s g st) op (← a.substH s g st))
  | .pay r a => if g then do pure (.pay (← r.substH s g st) (← a.substH s g st)) else none
  | .netMt r a => do pure (.netMt (← r.substH s g st) (← a.substH s g st))
  | .setBalance a => (a.substH s g st).map .setBalance

end Subst

/-- `V` applied after `U`, as one update from `U`'s state: `U`'s elements,
then `V`'s, each read in `U`'s state (`s`, `g`: `U.held`, `U.envOnly`). -/
def Upd.graft {Γ Δ₁ : Ctx} (U : Upd C Γ Δ₁) (s : Subst C Γ Δ₁) (g : Bool) (st : Option (Tm C Γ .st)) :
    {Δ₂ : Ctx} → Upd C Δ₁ Δ₂ → Option (Upd C Γ Δ₂)
  | _, .nil => some U
  | _, .snoc V e => do pure (.snoc (← Upd.graft U s g st V) (← e.substH s g st))
  | _, .decl V x r => do pure (.decl (← Upd.graft U s g st V) x (← r.substH s g st))
  | _, .pop V h => (Upd.graft U s g st V).map (.pop · h)
  | _, .drop V h => (Upd.graft U s g st V).map (.drop · h)


/-! ## The merge is sound, on the typed state

`V` read in a typed state `U` lands on is `V` substituted (`Tm.substH`),
read in the state before: what `U` leaves in a local is what `Upd.held`
says (`Upd.Lands`), and the global part only where `U` writes none
(`Upd.envOnly_globT`). -/

section SoundT

open Semantics (bind_ok_inv)

variable {Γ : Ctx}

/-- An update of locals only leaves the global part it is applied in. -/
theorem Upd.envOnly_globT {σ₀ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) → U.envOnly = true →
    {g : Semantics.State} → U.globT σ₀ = .ok g → g = σ₀.globE
  | _, .nil, _, _, h => by cases h; rfl
  | _, .snoc U e, hU, g, h => by
    obtain ⟨g', hg', h⟩ := bind_ok_inv h
    cases e with
    | «local» k r =>
      obtain ⟨_, _, h⟩ := bind_ok_inv h
      cases h
      exact Upd.envOnly_globT U hU hg'
    | _ => exact absurd hU Bool.false_ne_true
  | _, .decl U _ r, hU, g, h => by
    obtain ⟨g', hg', h⟩ := bind_ok_inv h
    obtain ⟨_, _, h⟩ := bind_ok_inv h
    cases h
    exact Upd.envOnly_globT U hU hg'
  | _, .pop U _, hU, _, h => Upd.envOnly_globT U hU h
  | _, .drop U _, hU, _, h => Upd.envOnly_globT U hU h

variable {Δ : Ctx} {σ₀ : State C Γ} {σ₁ : State C Δ}

theorem Tm.evalT_substH_pvV {p : PrimTy} {i : Idx Δ (.val p)} {t' : Tm C Γ .val} :
    (x : Held C Γ (.val p)) → Held.OKT σ₀ σ₁ i x →
      (match x with | .pos j => some (Tm.pvV j) | .rhs (.val t) => some t) = some t' →
      t'.evalT σ₀ = (Tm.pvV i).evalT σ₁
  | .pos j, hok, h => by
    cases h
    have hok : σ₁.getE i = σ₀.getE j := hok
    simp only [Tm.evalT, hok]
  | .rhs (.val t), hok, h => by cases h; exact hok

theorem Tm.evalT_substH_pvP {R : RefTy} {i : Idx Δ (.alias R)} {t' : Tm C Γ .path} :
    (x : Held C Γ (.alias R)) → Held.OKT σ₀ σ₁ i x →
      (match x with
        | .pos j => some (Tm.pvP j) | .rhs (.path p) => some p | .rhs .unset => none) = some t' →
      t'.evalT σ₀ = (Tm.pvP i).evalT σ₁
  | .pos j, hok, h => by
    cases h
    have hok : σ₁.getE i = σ₀.getE j := hok
    simp only [Tm.evalT, State.aliasPathT_getE, hok]
  | .rhs (.path p), hok, h => by
    cases h
    have hok : (do pure (some (← t'.evalT σ₀))) = Except.ok (σ₁.getE i) := hok
    show _ = σ₁.aliasPathT i
    rw [State.aliasPathT_getE]
    cases hp : t'.evalT σ₀ with
    | error e => rw [hp] at hok; cases hok
    | ok q =>
      rw [hp] at hok
      injection hok with hq
      rw [← hq]
      rfl
  | .rhs .unset, _, h => by cases h

theorem Tm.evalT_substH_pvI {R : RefTy} {i : Idx Δ (.mem R)} {t' : Tm C Γ .ident} :
    (x : Held C Γ (.mem R)) → Held.OKT σ₀ σ₁ i x →
      (match x with | .pos j => some (Tm.pvI j) | .rhs (.mref t) => some t) = some t' →
      t'.evalT σ₀ = (Tm.pvI i).evalT σ₁
  | .pos j, hok, h => by
    cases h
    have hok : σ₁.getE i = σ₀.getE j := hok
    simp only [Tm.evalT, State.memRefT_getE, hok]
  | .rhs (.mref t), hok, h => by
    cases h
    have hok : (do pure (some (← t'.evalT σ₀))) = Except.ok (σ₁.getE i) := hok
    show _ = σ₁.memRefT i
    rw [State.memRefT_getE]
    cases hp : t'.evalT σ₀ with
    | error e => rw [hp] at hok; cases hok
    | ok q =>
      rw [hp] at hok
      injection hok with hq
      rw [← hq]
      rfl

theorem Tm.evalT_substH_pvS {g : Bool} (hg : g = true → σ₁.globE = σ₀.globE) {i : Idx Δ .old}
    {t' : Tm C Γ .st} :
    (x : Held C Γ .old) → Held.OKT σ₀ σ₁ i x →
      (match x with | .pos j => if g then some (Tm.pvS j) else none | .rhs _ => none) = some t' →
      t'.evalT σ₀ = (Tm.pvS i).evalT σ₁
  | .pos j, hok, h => by
    cases g with
    | false => cases h
    | true =>
      cases h
      have hok : σ₁.getE i = σ₀.getE j := hok
      simp only [Tm.evalT, hok, hg rfl]
  | .rhs _, _, h => by cases h

variable {U : Upd C Γ Δ} {g : Semantics.State} {st : Option (Tm C Γ .st)}

/-- Where `U` lands, a global part it leaves unwritten is the one before. -/
theorem Upd.Lands.globE_of_envOnly (hL : U.Lands σ₀ g σ₁) (h : U.envOnly = true) :
    σ₁.globE = σ₀.globE :=
  hL.2.1.trans (Upd.envOnly_globT U h hL.1)

/-- **A term read in the state before is the term read in every typed
state the update lands on.** -/
theorem Tm.evalT_substH (hL : U.Lands σ₀ g σ₁) (hst : ∀ x, st = some x → x.evalT σ₀ = pure g) :
    {k : Srt} → (t : Tm C Δ k) → {t' : Tm C Γ k} → t.substH U.held U.envOnly st = some t' →
      t'.evalT σ₀ = t.evalT σ₁
  | _, .pvV i, _, h => Tm.evalT_substH_pvV _ (hL.2.2 i) h
  | _, .pvP i, _, h => Tm.evalT_substH_pvP _ (hL.2.2 i) h
  | _, .pvS i, _, h => Tm.evalT_substH_pvS hL.globE_of_envOnly _ (hL.2.2 i) h
  | _, .pvI i, _, h => Tm.evalT_substH_pvI _ (hL.2.2 i) h
  | _, .netOf i a, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => (a.substH U.held U.envOnly st).map (Tm.netOf j) | .rhs _ => none) = some t' := h
    generalize U.held i = x at h hx
    cases x with
    | rhs _ => cases h
    | pos j =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      have hx : σ₁.getE i = σ₀.getE j := hx
      simp only [Tm.evalT, Tm.evalT_substH hL hst a ha, hx]
  | _, .app0 o, t', h => by
    simp only [Tm.substH] at h
    split at h
    · rename_i hc
      cases h
      show o.eval σ₀.globE = o.eval σ₁.globE
      rcases Bool.or_eq_true _ _ ▸ hc with hg | hg
      · rw [hL.globE_of_envOnly hg]
      · exact Op0.eval_globFree hg _ _
    · revert h
      cases o with
      | storage =>
        intro h
        show t'.evalT σ₀ = pure σ₁.globE
        rw [hst t' h, hL.2.1]
      | _ => exact fun h => nomatch h
  | _, .app1 o ho x, t', h => by
    simp only [Tm.substH] at h
    split at h
    · rename_i hc
      obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
      show o.eval σ₀.globE (x'.evalT σ₀) = o.eval σ₁.globE (x.evalT σ₁)
      rw [Tm.evalT_substH hL hst x hx]
      rcases Bool.or_eq_true _ _ ▸ hc with hg | hg
      · rw [hL.globE_of_envOnly hg]
      · exact Op1.eval_globFree hg _ _ _
    · cases h
  | _, .app2 o x y, t', h => by
    simp only [Tm.substH] at h
    split at h
    · rename_i hc
      obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      show o.eval σ₀.globE (x'.evalT σ₀) (y'.evalT σ₀) = o.eval σ₁.globE (x.evalT σ₁) (y.evalT σ₁)
      rw [Tm.evalT_substH hL hst x hx, Tm.evalT_substH hL hst y hy]
      rcases Bool.or_eq_true _ _ ▸ hc with hg | hg
      · rw [hL.globE_of_envOnly hg]
      · exact Op2.eval_globFree hg _ _ _ _
    · cases h
  | _, .app3 o x y z, t', h => by
    simp only [Tm.substH] at h
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z', hz, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show o.eval σ₀.globE (x'.evalT σ₀) (y'.evalT σ₀) (z'.evalT σ₀) =
      o.eval σ₁.globE (x.evalT σ₁) (y.evalT σ₁) (z.evalT σ₁)
    rw [Tm.evalT_substH hL hst x hx, Tm.evalT_substH hL hst y hy, Tm.evalT_substH hL hst z hz]
    exact Op3.eval_any o _ _ _ _ _

theorem Rhs.evalT_substH (hL : U.Lands σ₀ g σ₁) (hst : ∀ x, st = some x → x.evalT σ₀ = pure g) :
    {t : LTy} → (r : Rhs C Δ t) → {r' : Rhs C Γ t} → r.substH U.held U.envOnly st = some r' →
      r'.evalT σ₀ = r.evalT σ₁
  | _, .val t, r', h => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Tm.evalT_substH hL hst t ht
  | _, .path p, r', h => by
    obtain ⟨p', hp, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [Rhs.evalT, Tm.evalT_substH hL hst p hp]
  | _, .unset, r', h => by cases h; rfl
  | _, .mref i, r', h => by
    obtain ⟨i', hi, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [Rhs.evalT, Tm.evalT_substH hL hst i hi]
  | _, .store x, r', h => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [Rhs.evalT, Tm.evalT_substH hL hst x hx]
  | _, .saveNet, r', h => by
    simp only [Rhs.substH] at h
    split at h
    · rename_i hg
      cases h
      show pure σ₀.net = pure σ₁.net
      have := hL.globE_of_envOnly hg
      have hn : σ₁.net = σ₀.net := congrArg Semantics.State.net this
      rw [hn]
    · cases h
  | _, .saveNetMt, r', h => by cases h; rfl

theorem UpdElem.globT_substH (hL : U.Lands σ₀ g σ₁)
    (hst : ∀ x, st = some x → x.evalT σ₀ = pure g) {Ε : Ctx} (e : UpdElem C Δ Ε)
    {e' : UpdElem C Γ Ε} (h : e.substH U.held U.envOnly st = some e') (G : Semantics.State) :
    e'.globT σ₀ G = e.globT σ₁ G := by
  cases e with
  | «local» i r =>
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.globT, Rhs.evalT_substH hL hst r hr]
  | storage x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.globT, Tm.evalT_substH hL hst x hx]
  | memory x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.globT, Tm.evalT_substH hL hst x hx]
  | selfBalance op a =>
    simp only [UpdElem.substH] at h
    split at h
    · rename_i hg
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      simp only [UpdElem.globT, Tm.evalT_substH hL hst a ha, hL.globE_of_envOnly hg]
    · cases h
  | net r op a =>
    simp only [UpdElem.substH] at h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [UpdElem.globT, Tm.evalT_substH hL hst r hr, Tm.evalT_substH hL hst a ha]
  | pay r a =>
    simp only [UpdElem.substH] at h
    split at h
    · rename_i hg
      obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      simp only [UpdElem.globT, Tm.evalT_substH hL hst r hr, Tm.evalT_substH hL hst a ha,
        hL.globE_of_envOnly hg]
    · cases h
  | netMt r a =>
    simp only [UpdElem.substH] at h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [UpdElem.globT, Tm.evalT_substH hL hst r hr, Tm.evalT_substH hL hst a ha]
  | setBalance a =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.globT, Tm.evalT_substH hL hst a ha]

end SoundT

section GraftT

open Semantics (bind_ok_inv)

variable {Γ Δ₁ : Ctx} {σ₀ : State C Γ} {U : Upd C Γ Δ₁} {st : Option (Tm C Γ .st)}

/-- The grafted update halts where `U` does. -/
theorem Upd.globT_graft_error {e : Semantics.Halt} (hU : U.globT σ₀ = .error e) :
    {Δ₂ : Ctx} → (V : Upd C Δ₁ Δ₂) → {W : Upd C Γ Δ₂} → U.graft U.held U.envOnly st V = some W →
      W.globT σ₀ = .error e
  | _, .nil, W, h => by cases h; exact hU
  | _, .snoc V e', W, h => by
    simp only [Upd.graft] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e'', -, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [Upd.globT, Upd.globT_graft_error hU V hW]
    rfl
  | _, .decl V x r, W, h => by
    simp only [Upd.graft] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', -, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [Upd.globT, Upd.globT_graft_error hU V hW]
    rfl
  | _, .pop V _, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.globT_graft_error hU V hW
  | _, .drop V _, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.globT_graft_error hU V hW

variable {σ₁ : State C Δ₁} {g₁ : Semantics.State}

/-- **The grafted update computes the global part `V` does** in a state `U`
lands on. -/
theorem Upd.globT_graft (hL : U.Lands σ₀ g₁ σ₁) (hst : ∀ x, st = some x → x.evalT σ₀ = pure g₁) :
    {Δ₂ : Ctx} → (V : Upd C Δ₁ Δ₂) → {W : Upd C Γ Δ₂} → U.graft U.held U.envOnly st V = some W →
      W.globT σ₀ = V.globT σ₁
  | _, .nil, W, h => by
    cases h
    rw [hL.1]
    show _ = pure σ₁.globE
    rw [hL.2.1]
    rfl
  | _, .snoc V e, W, h => by
    simp only [Upd.graft] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [Upd.globT, Upd.globT_graft hL hst V hW, UpdElem.globT_substH hL hst e he]
  | _, .decl V x r, W, h => by
    simp only [Upd.graft] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [Upd.globT, Upd.globT_graft hL hst V hW, Rhs.evalT_substH hL hst r hr]
  | _, .pop V _, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.globT_graft hL hst V hW
  | _, .drop V _, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.globT_graft hL hst V hW

/-- **The grafted update leaves in each local what `V` does**, read in a
state `U` lands on. -/
theorem Upd.held_graft (hL : U.Lands σ₀ g₁ σ₁) (hst : ∀ x, st = some x → x.evalT σ₀ = pure g₁) :
    {Δ₂ : Ctx} → (V : Upd C Δ₁ Δ₂) → {W : Upd C Γ Δ₂} → U.graft U.held U.envOnly st V = some W →
      ∀ {t : LTy} (i : Idx Δ₂ t) (v : t.Denote C), Held.OKV σ₁ v (V.held i) →
        Held.OKV σ₀ v (W.held i)
  | _, .nil, W, h, t, i, v, hv => by
    cases h
    have hi := (Held.OKT_iff_OKV σ₀ σ₁ i _).1 (hL.2.2 i)
    show Held.OKV σ₀ v (U.held i)
    have hv : v = σ₁.getE i := hv
    rw [hv]
    exact hi
  | _, .snoc V e, W, h, t, i, v, hv => by
    simp only [Upd.graft] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    cases e with
    | «local» k r =>
      obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 he
      show Held.OKV σ₀ v (Subst.set (Upd.held W') k r' i)
      have hv : Held.OKV σ₁ v (Subst.set (Upd.held V) k r i) := hv
      unfold Subst.set at hv ⊢
      split
      · rename_i hki
        rw [dif_pos hki] at hv
        obtain rfl := Idx.ty_eq_of_toNat hki
        obtain rfl := Idx.toNat_inj k i hki
        show r'.evalT σ₀ = .ok v
        rw [Rhs.evalT_substH hL hst r hr]
        exact hv
      · rename_i hki
        rw [dif_neg hki] at hv
        exact Upd.held_graft hL hst V hW i v hv
    | storage x | memory x | setBalance x =>
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 he
      exact Upd.held_graft hL hst V hW i v hv
    | selfBalance op a =>
      simp only [UpdElem.substH] at he
      split at he
      · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 he
        exact Upd.held_graft hL hst V hW i v hv
      · cases he
    | net r op a | netMt r a =>
      simp only [UpdElem.substH] at he
      obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 he
      obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 he
      cases he
      exact Upd.held_graft hL hst V hW i v hv
    | pay r a =>
      simp only [UpdElem.substH] at he
      split at he
      · obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 he
        obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 he
        cases he
        exact Upd.held_graft hL hst V hW i v hv
      · cases he
  | _, .decl V x r, W, h, t, i, v, hv => by
    simp only [Upd.graft] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    cases i with
    | here =>
      show r'.evalT σ₀ = .ok v
      rw [Rhs.evalT_substH hL hst r hr]
      exact hv
    | there j => exact Upd.held_graft hL hst V hW j v hv
  | _, .pop V e, W, h, t, i, v, hv => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.held_graft hL hst V hW (i.ext e) v hv
  | _, .drop V e, W, h, t, i, v, hv => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.held_graft hL hst V hW (i.wk e) v hv

end GraftT

/-! ## An update moved under a hidden binder

`{U} ∀x. {V} ψ` (the binder `memoryLocalDeclInitDrop` leaves between a
stack and the rest, decision 12) merges as `∀x. {U ‖ V} ψ` when `U` declares
nothing: `U` reads none of `x`, so it is `U` with every position one deeper
(`Upd.lift?`), applied in a state with `x` on top. -/

/-- The update that drops the top local: a state with one more local read in
the one before (`Tm.substH` of it shifts a term up). -/
abbrev Upd.dropTop (Γ : Ctx) (t : LTy) : Upd C (t :: Γ) Γ := .drop .nil up

/-- An element moved under a pushed local: a local's, the storage's or the
memory's (the ledger's is not needed). -/
def UpdElem.lift? {Γ Δ : Ctx} {t : LTy} : UpdElem C Γ Δ → Option (UpdElem C (t :: Γ) (t :: Δ))
  | .local i r => (r.substH (Upd.dropTop (C := C) Γ t).held true none).map (.local i.there)
  | .storage x => (x.substH (Upd.dropTop (C := C) Γ t).held true none).map .storage
  | .memory x => (x.substH (Upd.dropTop (C := C) Γ t).held true none).map .memory
  | _ => none

/-- An update that declares nothing, moved under a pushed local. -/
def Upd.lift? {Γ : Ctx} {t : LTy} : {Δ : Ctx} → Upd C Γ Δ → Option (Upd C (t :: Γ) (t :: Δ))
  | _, .nil => some .nil
  | _, .snoc U e => do pure (.snoc (← Upd.lift? U) (← e.lift?))
  | _, .decl .. | _, .pop .. | _, .drop .. => none

/-- An update moved under a pushed local, its scope ends too: a pop or a
drop below the local is a thinning that keeps it (the sequent's merge; a
chain's moves `Upd.lift?`'s). -/
def Upd.liftG? {Γ : Ctx} {t : LTy} : {Δ : Ctx} → Upd C Γ Δ → Option (Upd C (t :: Γ) (t :: Δ))
  | _, .nil => some .nil
  | _, .snoc U e => do pure (.snoc (← Upd.liftG? U) (← e.lift?))
  | _, .pop U h => (Upd.liftG? U).map (.drop · (.keep (Thin.ofExt h)))
  | _, .drop U h => (Upd.liftG? U).map (.drop · (.keep h))
  | _, .decl .. => none

section Lift

open Semantics (bind_ok_inv)

variable {Γ : Ctx} {t : LTy}

theorem Upd.dropTop_envOnly : (Upd.dropTop (C := C) Γ t).envOnly = true := rfl

/-- Dropping the top local lands on the state below it. -/
theorem Upd.lands_dropTop (σ : State C Γ) (v : t.TDenote C σ.H) :
    (Upd.dropTop (C := C) Γ t).Lands (σ.push v) σ.globE σ :=
  ⟨rfl, rfl, fun _ => rfl⟩

theorem Tm.evalT_dropTop (σ : State C Γ) (v : t.TDenote C σ.H) {k : Srt} (x : Tm C Γ k)
    {x' : Tm C (t :: Γ) k} (hx : x.substH (Upd.dropTop (C := C) Γ t).held true none = some x') :
    x'.evalT (σ.push v) = x.evalT σ :=
  Tm.evalT_substH (Upd.lands_dropTop σ v) (fun _ h => Option.noConfusion h) x hx

theorem Rhs.evalT_dropTop (σ : State C Γ) (v : t.TDenote C σ.H) {u : LTy} (r : Rhs C Γ u)
    {r' : Rhs C (t :: Γ) u} (hr : r.substH (Upd.dropTop (C := C) Γ t).held true none = some r') :
    r'.evalT (σ.push v) = r.evalT σ :=
  Rhs.evalT_substH (Upd.lands_dropTop σ v) (fun _ h => Option.noConfusion h) r hr

theorem UpdElem.globT_lift? {Δ : Ctx} (σ : State C Γ) (v : t.TDenote C σ.H) (e : UpdElem C Γ Δ)
    {e' : UpdElem C (t :: Γ) (t :: Δ)} (h : e.lift? = some e') (G : Semantics.State) :
    e'.globT (σ.push v) G = e.globT σ G := by
  cases e with
  | «local» i r =>
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.globT, Rhs.evalT_dropTop σ v r hr]
  | storage x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.globT, Tm.evalT_dropTop σ v x hx]
  | memory x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.globT, Tm.evalT_dropTop σ v x hx]
  | selfBalance _ _ | net _ _ _ | pay _ _ | netMt _ _ | setBalance _ => cases h

/-- **The moved update computes the update's global part.** -/
theorem Upd.globT_liftG? (σ : State C Γ) (v : t.TDenote C σ.H) : {Δ : Ctx} → (U : Upd C Γ Δ) →
    {U' : Upd C (t :: Γ) (t :: Δ)} → U.liftG? = some U' → U'.globT (σ.push v) = U.globT σ
  | _, .nil, _, h => by cases h; rfl
  | _, .snoc U e, _, h => by
    simp only [Upd.liftG?] at h
    obtain ⟨U', hU, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [Upd.globT, Upd.globT_liftG? σ v U hU, UpdElem.globT_lift? σ v e he]
  | _, .pop U _, _, hh => by
    obtain ⟨U', hU, rfl⟩ := Option.map_eq_some_iff.1 hh
    exact Upd.globT_liftG? σ v U hU
  | _, .drop U _, _, hh => by
    obtain ⟨U', hU, rfl⟩ := Option.map_eq_some_iff.1 hh
    exact Upd.globT_liftG? σ v U hU
  | _, .decl .., _, h => by cases h

/-- The moved update keeps the top local. -/
theorem Upd.held_liftG?_here : {Δ : Ctx} → (U : Upd C Γ Δ) → {U' : Upd C (t :: Γ) (t :: Δ)} →
    U.liftG? = some U' → U'.held .here = .pos .here
  | _, .nil, _, h => by cases h; rfl
  | _, .snoc U e, _, h => by
    simp only [Upd.liftG?] at h
    obtain ⟨U', hU, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    cases e with
    | «local» i r =>
      obtain ⟨r', -, rfl⟩ := Option.map_eq_some_iff.1 he
      show Subst.set (Upd.held U') i.there r' .here = _
      unfold Subst.set
      rw [dif_neg (show ¬ (i.there.toNat = (Idx.here : Idx (t :: _) t).toNat) by
        simp only [Idx.toNat]; omega)]
      exact Upd.held_liftG?_here U hU
    | storage x | memory x =>
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 he
      show Upd.held U' .here = _
      exact Upd.held_liftG?_here U hU
    | selfBalance _ _ | net _ _ _ | pay _ _ | netMt _ _ | setBalance _ => cases he
  | _, .pop U _, _, hh => by
    obtain ⟨U', hU, rfl⟩ := Option.map_eq_some_iff.1 hh
    exact Upd.held_liftG?_here U hU
  | _, .drop U _, _, hh => by
    obtain ⟨U', hU, rfl⟩ := Option.map_eq_some_iff.1 hh
    exact Upd.held_liftG?_here U hU
  | _, .decl .., _, h => by cases h

/-- The moved update leaves in each local below the top what the update
does, read one local deeper. -/
theorem Upd.held_liftG?_there (σ : State C Γ) (v : t.TDenote C σ.H) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → {U' : Upd C (t :: Γ) (t :: Δ)} → U.liftG? = some U' →
      ∀ {u : LTy} (i : Idx Δ u) (w : u.Denote C), Held.OKV σ w (U.held i) →
        Held.OKV (σ.push v) w (U'.held i.there)
  | _, .nil, _, h, _, i, w, hw => by cases h; exact hw
  | _, .snoc U e, _, h, u, i, w, hw => by
    simp only [Upd.liftG?] at h
    obtain ⟨U', hU, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    cases e with
    | «local» k r =>
      obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 he
      show Held.OKV (σ.push v) w (Subst.set (Upd.held U') k.there r' i.there)
      have hw : Held.OKV σ w (Subst.set (Upd.held U) k r i) := hw
      unfold Subst.set at hw ⊢
      by_cases hki : k.toNat = i.toNat
      · obtain rfl := Idx.ty_eq_of_toNat hki
        obtain rfl := Idx.toNat_inj k i hki
        rw [dif_pos rfl] at hw ⊢
        show r'.evalT (σ.push v) = .ok w
        rw [Rhs.evalT_dropTop σ v r hr]
        exact hw
      · rw [dif_neg hki] at hw
        rw [dif_neg (show ¬ (k.there.toNat = i.there.toNat) by
          simp only [Idx.toNat]; omega)]
        exact Upd.held_liftG?_there σ v U hU i w hw
    | storage x | memory x =>
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 he
      show Held.OKV (σ.push v) w (Upd.held U' i.there)
      exact Upd.held_liftG?_there σ v U hU i w hw
    | selfBalance _ _ | net _ _ _ | pay _ _ | netMt _ _ | setBalance _ => cases he
  | _, .pop U e, _, hh, u, i, w, hw => by
    obtain ⟨U', hU, rfl⟩ := Option.map_eq_some_iff.1 hh
    have hw : Held.OKV σ w (U.held (i.ext e)) := hw
    show Held.OKV (σ.push v) w (U'.held (i.wk (Thin.ofExt e)).there)
    rw [Idx.wk_ofExt]
    exact Upd.held_liftG?_there σ v U hU (i.ext e) w hw
  | _, .drop U e, _, hh, u, i, w, hw => by
    obtain ⟨U', hU, rfl⟩ := Option.map_eq_some_iff.1 hh
    exact Upd.held_liftG?_there σ v U hU (i.wk e) w hw
  | _, .decl .., _, h, _, _, _, _ => by cases h

/-- **The moved update lands on the state the update lands on, the local
kept on top.** -/
theorem Upd.lands_liftG? {Δ : Ctx} {U : Upd C Γ Δ} {U' : Upd C (t :: Γ) (t :: Δ)}
    (hU : U.liftG? = some U') {σ : State C Γ} {g : Semantics.State} {σ' : State C Δ}
    (hL : U.Lands σ g σ') (v : t.TDenote C σ.H) (v' : t.TDenote C σ'.H)
    (hv : LTy.TDenote.erase t v' = LTy.TDenote.erase t v) :
    U'.Lands (σ.push v) g (σ'.push v') := by
  refine ⟨(Upd.globT_liftG? σ v U hU).trans hL.1, hL.2.1, fun i => ?_⟩
  cases i with
  | here =>
    rw [Upd.held_liftG?_here U hU]
    exact hv
  | there j =>
    rw [Held.OKT_iff_OKV]
    exact Upd.held_liftG?_there σ v U hU j _ ((Held.OKT_iff_OKV _ _ _ _).1 (hL.2.2 j))

/-- An update that declares nothing moves as one that ends no scope. -/
theorem Upd.liftG?_of_lift? : {Δ : Ctx} → (U : Upd C Γ Δ) → {U' : Upd C (t :: Γ) (t :: Δ)} →
    U.lift? = some U' → U.liftG? = some U'
  | _, .nil, _, h => h
  | _, .snoc U e, _, h => by
    simp only [Upd.lift?] at h
    obtain ⟨U', hU, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [Upd.liftG?, Upd.liftG?_of_lift? U hU, he]
    rfl
  | _, .decl .., _, h | _, .pop .., _, h | _, .drop .., _, h => by cases h

end Lift

/-! ## Merging in a line -/

/-- A local's type other than a memory one: its typed values do not depend
on the heap, so a binder over it reads the same values from any typed
state. -/
def LTy.notMem : LTy → Bool
  | .mem _ => false
  | _ => true

/-- A local's value of a type other than a memory one, in one heap, is one
in any other, as erased. -/
theorem LTy.erase_of_notMem {t : LTy} (ht : t.notMem = true) {H H' : HTy} (v' : t.TDenote C H') :
    ∃ v : t.TDenote C H, LTy.TDenote.erase t v = LTy.TDenote.erase t v' := by
  cases t with
  | mem => cases ht
  | val | alias | old | oldNet => exact ⟨v', rfl⟩

/-- An element that allocates nothing: a local or the storage set. -/
def UpdElem.keepsNext {Γ Δ : Ctx} : UpdElem C Γ Δ → Bool
  | .local .. | .storage _ => true
  | _ => false

/-- An update that allocates nothing: the next identity it leaves is the one
of the state it is applied in. -/
def Upd.keepsNext {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => true
  | _, .snoc U e => U.keepsNext && e.keepsNext
  | _, .decl U _ _ | _, .pop U _ | _, .drop U _ => U.keepsNext

/-- An update that allocates nothing leaves the next identity it found. -/
theorem Upd.keepsNext_globT {Γ : Ctx} {σ₀ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) → U.keepsNext = true →
    ∀ {g : Semantics.State}, U.globT σ₀ = .ok g → g.nextId = σ₀.globE.nextId
  | _, .nil, _, _, h => by cases h; rfl
  | _, .snoc U e, hk, g, h => by
    have hk' : U.keepsNext = true ∧ e.keepsNext = true := Bool.and_eq_true_iff.mp hk
    obtain ⟨g', h₁, h₂⟩ := Semantics.bind_ok_inv h
    have ih := Upd.keepsNext_globT U hk'.1 h₁
    cases e with
    | «local» i r =>
      obtain ⟨_, -, h₂⟩ := Semantics.bind_ok_inv h₂
      cases h₂
      exact ih
    | storage s =>
      obtain ⟨_, -, h₂⟩ := Semantics.bind_ok_inv h₂
      cases h₂
      exact ih
    | _ => cases hk'.2
  | _, .decl U _ r, hk, g, h => by
    obtain ⟨g', h₁, h₂⟩ := Semantics.bind_ok_inv h
    obtain ⟨_, -, h₂⟩ := Semantics.bind_ok_inv h₂
    cases h₂
    exact Upd.keepsNext_globT U hk h₁
  | _, .pop U _, hk, _, h => Upd.keepsNext_globT U hk h
  | _, .drop U _, hk, _, h => Upd.keepsNext_globT U hk h

/-- A local's value, cast along an equal heap typing, erases as it did. -/
theorem LTy.TDenote.erase_rec {H H' : HTy} (h : H' = H) (t : LTy) (v' : t.TDenote C H') :
    LTy.TDenote.erase t (h ▸ v' : t.TDenote C H) = LTy.TDenote.erase t v' := by
  subst h; rfl

/-- `{U} ∀x. ψ` from `∀x. {U↑} ψ`, `U↑` the update moved under the binder
(`Upd.liftG?`).  A value of the binder after `U` is one before it: its type
is not a memory one, or `U` allocates nothing, so the heap typing after it,
which extends the one before, is that one. -/
theorem Fml.upd_bind_of_liftG {m m' : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} {t : LTy} {x : Var}
    {U' : Upd C (t :: Γ) (t :: Δ)} (hU' : U.liftG? = some U')
    (ht : (t.notMem || U.keepsNext) = true)
    {ψ : Fml C (t :: Δ)} (σ : State C Γ)
    (hψ : m'.forallB fun v : t.TDenote C σ.H => holds (σ.push v) (.upd m U' ψ)) :
    holds σ (.upd m U (.bind m' x t ψ)) := by
  obtain ⟨v₀⟩ := LTy.tdenote_nonempty (C := C) (H := σ.H) t
  refine Upd.afterT_intro (fun e he => ?_) fun g σ' hL hext => ?_
  · have h₀ : U'.afterT m (σ.push v₀) (holds · ψ) := Modality.forallB_all hψ v₀
    exact h₀.of_error ((Upd.globT_liftG? σ v₀ U hU').trans he)
  · refine Modality.forallB_intro fun v' => ?_
    have hv : ∃ v : t.TDenote C σ.H, LTy.TDenote.erase t v = LTy.TDenote.erase t v' := by
      rcases Bool.or_eq_true_iff.mp ht with ht | hk
      · exact LTy.erase_of_notMem ht v'
      · have hn : σ'.H.length = σ.H.length := by
          have h₁ := Upd.keepsNext_globT U hk hL.1
          rw [← hL.2.1] at h₁
          exact h₁
        have hH : σ'.H = σ.H := (hext.eq_of_length hn.symm).symm
        exact ⟨hH ▸ v', LTy.TDenote.erase_rec hH t v'⟩
    obtain ⟨v, hv⟩ := hv
    have h : U'.afterT m (σ.push v) (holds · ψ) := Modality.forallB_all hψ v
    exact h.of_lands (Upd.lands_liftG? hU' hL v v' hv.symm) hext

theorem Fml.upd_bind_of_lift {m m' : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} {t : LTy} {x : Var}
    {U' : Upd C (t :: Γ) (t :: Δ)} (hU' : U.lift? = some U') (ht : (t.notMem || U.keepsNext) = true)
    {ψ : Fml C (t :: Δ)} (σ : State C Γ)
    (hψ : m'.forallB fun v : t.TDenote C σ.H => holds (σ.push v) (.upd m U' ψ)) :
    holds σ (.upd m U (.bind m' x t ψ)) :=
  Fml.upd_bind_of_liftG (Upd.liftG?_of_lift? U hU') ht σ hψ

theorem Env.thin_ofExt {Γ : Ctx} : {Δ : Ctx} → (h : Ext Γ Δ) → (e : Env C Δ) →
    Env.thin (Thin.ofExt h) e = Env.drop h e
  | _, .refl, _ => rfl
  | _, .push h, e => Env.thin_ofExt h e.2

/-! ## The storage an update leaves

`{storage := s}{x := find(storage, p)}` is `{storage := s ‖ x := find(s, p)}`:
`storage` after an update that writes no global part but the storage is the
storage it last wrote (`Upd.lastSt`), read before it.  A storage term
changes only the storage of the state it is read in (`Tm.eval_st_glob`), so
`s` read before the update is the global part after it (`Upd.lastSt_eval`). -/

/-- An element that writes no global part but the storage. -/
def UpdElem.stOnly {Γ Δ : Ctx} : UpdElem C Γ Δ → Bool
  | .local .. | .storage _ => true
  | _ => false

/-- An update that writes no global part but the storage. -/
def Upd.stOnly {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Bool
  | _, .nil => true
  | _, .snoc U e => Upd.stOnly U && e.stOnly
  | _, .decl U _ _ | _, .pop U _ | _, .drop U _ => Upd.stOnly U

/-- The storage an update last writes, read in the state it is applied in,
where it writes no other global part. -/
def Upd.lastSt {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Option (Tm C Γ .st)
  | _, .nil => none
  | _, .snoc U (.storage x) => if Upd.stOnly U then some x else none
  | _, .snoc U (.local _ _) => Upd.lastSt U
  | _, .snoc _ (.memory _) | _, .snoc _ (.selfBalance ..) | _, .snoc _ (.net ..)
  | _, .snoc _ (.pay ..) | _, .snoc _ (.netMt ..) | _, .snoc _ (.setBalance _) => none
  | _, .decl U _ _ | _, .pop U _ | _, .drop U _ => Upd.lastSt U

/-- **`sequentialToParallel`**: `{U}{V}` as one update, `V` read in `U`'s
state; `none` where a symbol of `V` reads a global part `U` writes. -/
def Upd.seqPar {Γ Δ₁ Δ₂ : Ctx} (U : Upd C Γ Δ₁) (V : Upd C Δ₁ Δ₂) : Option (Upd C Γ Δ₂) :=
  U.graft U.held U.envOnly U.lastSt V

section StGlob

open Semantics (MObj)

/-- A state with another storage, and nothing else changed. -/
abbrev StChg (τ τ' : Semantics.State) : Prop := τ' = { τ with storage := τ'.storage }

theorem StChg.trans {τ₁ τ₂ τ₃ : Semantics.State} (h₁ : StChg τ₁ τ₂) (h₂ : StChg τ₂ τ₃) :
    StChg τ₁ τ₃ := by
  rw [h₂]; rw [h₁]

theorem saveStorage_stChg {τ τ' : Semantics.State} {r : Name} {segs : List Semantics.Seg}
    {v : Semantics.SVal} (h : τ.saveStorage r segs v = .ok τ') : StChg τ τ' := by
  obtain ⟨_, _, _, _, rfl⟩ := SemanticsProperties.State.saveStorage_ok_inv h
  rfl

theorem writeStorage_stChg {τ τ' : Semantics.State} {r : Name} {segs : List Semantics.Seg}
    {v : Semantics.SVal} (h : τ.writeStorage r segs v = .ok τ') : StChg τ τ' := by
  rcases Semantics.State.writeStorage_ok_inv h with h | ⟨_, _, h⟩ <;> exact saveStorage_stChg h

theorem pushAt_stChg {τ τ' : Semantics.State} {E : Ty} {r : Name} {segs : List Semantics.Seg}
    {val : Semantics.SVal → Res Semantics.SVal} (h : Solidity.pushAt τ E r segs val = .ok τ') :
    StChg τ τ' := by
  unfold Solidity.pushAt at h
  obtain ⟨v, -, h⟩ := Semantics.bind_ok_inv h
  cases v with
  | array es sh fx =>
    obtain ⟨x, -, h⟩ := Semantics.bind_ok_inv h
    exact saveStorage_stChg h
  | _ => cases h

theorem pushPlaceAt_stChg {τ : Semantics.State} {p : Semantics.State × Int} {E : Ty} {r : Name}
    {segs : List Semantics.Seg} (h : Solidity.pushPlaceAt τ E r segs = .ok p) : StChg τ p.1 := by
  unfold Solidity.pushPlaceAt at h
  obtain ⟨v, -, h⟩ := Semantics.bind_ok_inv h
  cases v with
  | array es sh fx =>
    obtain ⟨τ', h₁, h⟩ := Semantics.bind_ok_inv h
    cases h
    exact saveStorage_stChg h₁
  | _ => cases h

theorem popAt_stChg {τ τ' : Semantics.State} {keep : Bool} {r : Name} {segs : List Semantics.Seg}
    (h : Solidity.popAt τ keep r segs = .ok τ') : StChg τ τ' := by
  unfold Solidity.popAt at h
  cases hf : τ.findStorage r segs with
  | error e => rw [hf] at h; cases h
  | ok v =>
    rw [hf] at h
    cases v with
    | array es sh fx =>
      dsimp only [bind, Except.bind] at h
      cases hrev : es.reverse with
      | nil => rw [hrev] at h; cases h
      | cons last restRev => rw [hrev] at h; exact saveStorage_stChg h
    | _ => cases h

/-- What a storage reading changed of the global part `g₀`: its storage
only, for a storage term. -/
def Srt.StChgOf (g₀ : Semantics.State) : (s : Srt) → s.Ev → Prop
  | .st, r => ∀ g, r = .ok g → StChg g₀ g
  | _, _ => True

/-- **A storage term changes only the storage** of the typed state it is
read in. -/
theorem Tm.evalT_stChg {Γ : Ctx} (σ : State C Γ) : {s : Srt} → (t : Tm C Γ s) →
    Srt.StChgOf σ.globE s (t.evalT σ)
  | _, .pvV _ | _, .pvP _ | _, .pvI _ | _, .netOf .. => trivial
  | _, .pvS i => fun g h => by cases h; rfl
  | _, .app0 o => by
    cases o with
    | storage => intro g h; cases h; rfl
    | mtSt vs => intro g h; cases h; rfl
    | _ => trivial
  | _, .app1 o _ x => by
    have ih := Tm.evalT_stChg σ x
    cases o with
    | select r =>
      intro g h
      obtain ⟨τ, hτ, h⟩ := Semantics.bind_ok_inv h
      obtain ⟨v, -, h⟩ := Semantics.bind_ok_inv h
      cases v with
      | struct fields => cases h; exact (ih τ hτ).trans rfl
      | _ => cases h
    | _ => trivial
  | _, .app2 o x y => by
    have ih := Tm.evalT_stChg σ x
    cases o with
    | delAt =>
      intro g h
      obtain ⟨τ, hτ, h⟩ := Semantics.bind_ok_inv h
      obtain ⟨⟨r, segs⟩, -, h⟩ := Semantics.bind_ok_inv h
      obtain ⟨cur, -, h⟩ := Semantics.bind_ok_inv h
      exact (ih τ hτ).trans (saveStorage_stChg h)
    | pushSlot E =>
      intro g h
      obtain ⟨τ, hτ, h⟩ := Semantics.bind_ok_inv h
      obtain ⟨⟨r, segs⟩, -, h⟩ := Semantics.bind_ok_inv h
      exact (ih τ hτ).trans (pushAt_stChg h)
    | pop | shrink =>
      intro g h
      obtain ⟨τ, hτ, h⟩ := Semantics.bind_ok_inv h
      obtain ⟨⟨r, segs⟩, -, h⟩ := Semantics.bind_ok_inv h
      exact (ih τ hτ).trans (popAt_stChg h)
    | extend E =>
      intro g h
      obtain ⟨τ, hτ, h⟩ := Semantics.bind_ok_inv h
      obtain ⟨⟨r, segs⟩, -, h⟩ := Semantics.bind_ok_inv h
      obtain ⟨p, hp, h⟩ := Semantics.bind_ok_inv h
      cases h
      exact (ih τ hτ).trans (pushPlaceAt_stChg hp)
    | _ => trivial
  | _, .app3 o x y z => by
    have ih := Tm.evalT_stChg σ x
    cases o with
    | save =>
      intro g h
      obtain ⟨sv, -, h⟩ := Semantics.bind_ok_inv h
      obtain ⟨τ, hτ, h⟩ := Semantics.bind_ok_inv h
      obtain ⟨⟨r, segs⟩, -, h⟩ := Semantics.bind_ok_inv h
      exact (ih τ hτ).trans (writeStorage_stChg h)
    | push =>
      intro g h
      obtain ⟨τ, hτ, h⟩ := Semantics.bind_ok_inv h
      obtain ⟨⟨r, segs⟩, -, h⟩ := Semantics.bind_ok_inv h
      exact (ih τ hτ).trans (pushAt_stChg h)
    | _ => trivial

theorem Tm.evalT_st_glob {Γ : Ctx} (σ : State C Γ) (t : Tm C Γ .st) (g : Semantics.State)
    (h : t.evalT σ = .ok g) : StChg σ.globE g :=
  Tm.evalT_stChg σ t g h

/-- An update that writes no global part but the storage leaves the global
part with another storage. -/
theorem Upd.stOnly_globT {Γ : Ctx} {σ₀ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) →
    U.stOnly = true → {g : Semantics.State} → U.globT σ₀ = .ok g → StChg σ₀.globE g
  | _, .nil, _, _, h => by cases h; rfl
  | _, .snoc U e, hU, g, h => by
    have hU' : U.stOnly = true ∧ e.stOnly = true := Bool.and_eq_true_iff.mp hU
    obtain ⟨τ, hτ, h⟩ := Semantics.bind_ok_inv h
    have ih := Upd.stOnly_globT U hU'.1 hτ
    cases e with
    | «local» k r =>
      obtain ⟨v, _, h⟩ := Semantics.bind_ok_inv h
      cases h
      exact ih
    | storage x =>
      obtain ⟨g, _, h⟩ := Semantics.bind_ok_inv h
      cases h
      exact ih.trans rfl
    | _ => cases hU'.2
  | _, .decl U _ r, hU, g, h => by
    obtain ⟨τ, hτ, h⟩ := Semantics.bind_ok_inv h
    obtain ⟨v, _, h⟩ := Semantics.bind_ok_inv h
    cases h
    exact Upd.stOnly_globT U hU hτ
  | _, .pop U _, hU, _, h => Upd.stOnly_globT U hU h
  | _, .drop U _, hU, _, h => Upd.stOnly_globT U hU h

/-- **The storage an update last wrote, read before it, is the global part
it leaves.** -/
theorem Upd.lastSt_evalT {Γ : Ctx} {σ₀ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) →
    {g : Semantics.State} → U.globT σ₀ = .ok g → ∀ x, U.lastSt = some x → x.evalT σ₀ = pure g
  | _, .nil, _, _, _, h => by cases h
  | _, .snoc U e, g, h, x, hx => by
    obtain ⟨τ, hτ, h⟩ := Semantics.bind_ok_inv h
    cases e with
    | «local» k r =>
      obtain ⟨v, _, h⟩ := Semantics.bind_ok_inv h
      cases h
      exact Upd.lastSt_evalT U hτ x hx
    | storage y =>
      simp only [Upd.lastSt] at hx
      split at hx
      · rename_i hs
        cases hx
        obtain ⟨g', hg, h⟩ := Semantics.bind_ok_inv h
        cases h
        rw [hg]
        have h₁ : StChg σ₀.globE τ := Upd.stOnly_globT U hs hτ
        have h₂ : StChg σ₀.globE g' := Tm.evalT_st_glob σ₀ x g' hg
        show Except.ok g' = Except.ok { τ with storage := g'.storage }
        rw [h₁, h₂]
      · cases hx
    | _ => cases hx
  | _, .decl U _ r, g, h, x, hx => by
    obtain ⟨τ, hτ, h⟩ := Semantics.bind_ok_inv h
    obtain ⟨v, _, h⟩ := Semantics.bind_ok_inv h
    cases h
    exact Upd.lastSt_evalT U hτ x hx
  | _, .pop U _, _, h, x, hx => Upd.lastSt_evalT U h x hx
  | _, .drop U _, _, h, x, hx => Upd.lastSt_evalT U h x hx

end StGlob

/-- **The merged update gives the two**: `{U ‖ {U}V} φ` gives `{U}{V} φ`
under the modality of both, `st` the storage `U` leaves where any. -/
theorem holds_upd_graft {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} {st : Option (Tm C Γ .st)}
    (hst : ∀ (σ₀ : State C Γ) g, U.globT σ₀ = .ok g → ∀ x, st = some x → x.evalT σ₀ = pure g)
    (hW : U.graft U.held U.envOnly st V = some W) {φ : Fml C Δ₂} (σ : State C Γ)
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) :=
  Upd.afterT_seq (fun e he => ⟨e, Upd.globT_graft_error he V hW⟩)
    (fun _ _ hL => Upd.globT_graft hL (hst σ _ hL.1) V hW)
    (fun _ _ hL => Upd.held_graft hL (hst σ _ hL.1) V hW) h

/-! ## Hidden binders between two updates

A declaration's hidden binder sits between the update before it and the
one its assignment leaves (`{U} ∀x. {x := e} …`), so the two merge with
`U` moved under the binders between (`Upd.liftBinds?`). -/

/-- The scope past the hidden binders `bs`, the first one innermost. -/
def Binds.ctx : List (Modality × Var × LTy) → Ctx → Ctx
  | [], Γ => Γ
  | (_, _, t) :: bs, Γ => Binds.ctx bs (t :: Γ)

/-- The hidden binders `bs` in front of a formula, the first one outermost. -/
def Fml.binds {Γ : Ctx} : (bs : List (Modality × Var × LTy)) → Fml C (Binds.ctx bs Γ) → Fml C Γ
  | [], φ => φ
  | (m, x, t) :: bs, φ => .bind m x t (Fml.binds (Γ := t :: Γ) bs φ)

/-- An update moved under the hidden binders `bs`, each at a type other
than a memory one or the update allocating nothing. -/
def Upd.liftBinds? {Γ Δ : Ctx} : (bs : List (Modality × Var × LTy)) → Upd C Γ Δ →
    Option (Upd C (Binds.ctx bs Γ) (Binds.ctx bs Δ))
  | [], U => some U
  | (_, _, t) :: bs, U =>
    if (t.notMem || U.keepsNext) = true then (U.liftG? (t := t)).bind (Upd.liftBinds? bs) else none

/-- **An update moved under hidden binders reads as the update in front of
them.** -/
theorem holds_liftBinds {m : Modality} : {Γ Δ : Ctx} → (bs : List (Modality × Var × LTy)) →
    {U : Upd C Γ Δ} → {U' : Upd C (Binds.ctx bs Γ) (Binds.ctx bs Δ)} → U.liftBinds? bs = some U' →
    {ψ : Fml C (Binds.ctx bs Δ)} → ∀ σ : State C Γ,
      holds σ (Fml.binds bs (.upd m U' ψ)) → holds σ (.upd m U (Fml.binds bs ψ))
  | _, _, [], _, _, h, _, _, hσ => by cases h; exact hσ
  | _, _, (m', x, t) :: bs, U, U', h, ψ, σ, hσ => by
    simp only [Upd.liftBinds?] at h
    split at h
    · rename_i ht
      obtain ⟨U₁, hU₁, h⟩ := Option.bind_eq_some_iff.1 h
      exact Fml.upd_bind_of_liftG hU₁ ht σ
        (Modality.forallB_imp (fun v hv => holds_liftBinds bs h _ hv) hσ)
    · cases h

/-- `holds_upd_graft` for `sequentialToParallel`. -/
theorem holds_upd_seqPar {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} (hW : U.seqPar V = some W) {φ : Fml C Δ₂} (σ : State C Γ)
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) :=
  holds_upd_graft (fun _ _ hU x hx => Upd.lastSt_evalT U hU x hx) hW σ h

end Solidity
