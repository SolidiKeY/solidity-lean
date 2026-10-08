import Solidity.Calculus.Core.CloseErase
import Solidity.Calculus.UpdateRules

/-!
# One update for two: `sequentialToParallel`'s side conditions on scoped updates

KeY's `sequentialToParallel2` (`{u}{u2}φ ⇝ {u ‖ {u}u2}φ`) on the scoped
updates of `Calculus/Core/Fml.lean`: what the sequent's `merge`
(`Calculus/Core/Proves.lean`) and the chains' `~[sequentialToParallel]~>`
(`Calculus/Core/Merge.lean`) compute, and why it is sound.

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

The last box update's right-hand sides are rewritten by a term taclet whose
right side cannot halt (`Upd.rwC`, `Proves.updRw`): every closed occurrence
of `t`, read on its erasure, becomes `t'` (`Tm.rwC`), and where the update
returns, the rewritten one returns the same state (`Upd.rwC_apply`).

The functions use `match` on the indexed families, against Gate G0's first
condition: an exemption (`docs/intrinsic.md`, W3b's merge, extended to the
sequent's update rules in W3c `tactics`, both timed), since they run once a
rule and not once a step.
-/

namespace Solidity.Core

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)
open Semantics (Res)

variable {C : Contract}

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

/-! ## What an update leaves in a local -/

/-- What a local of type `t` holds after an update applied in `Γ`: a local
of `Γ` it kept, or the right-hand side last written to it. -/
inductive Held (C : Contract) (Γ : Ctx) (t : LTy) : Type where
  | pos (i : Idx Γ t)
  | rhs (r : Rhs C Γ t)

/-- What every local of `Δ` holds after an update from `Γ` to `Δ`. -/
def Subst (C : Contract) (Γ Δ : Ctx) : Type := {t : LTy} → Idx Δ t → Held C Γ t

theorem Idx.ty_eq_of_toNat {Γ : Ctx} {t u : LTy} {i : Idx Γ t} {j : Idx Γ u}
    (h : i.toNat = j.toNat) : t = u := by
  have hi := i.getElem?_toNat
  have hj := j.getElem?_toNat
  rw [h, hj] at hi
  exact (Option.some.inj hi).symm

/-- The local `i` holds `r`. -/
def Subst.set {Γ Δ : Ctx} (s : Subst C Γ Δ) {t : LTy} (i : Idx Δ t) (r : Rhs C Γ t) :
    Subst C Γ Δ :=
  fun j => if h : i.toNat = j.toNat then .rhs (Idx.ty_eq_of_toNat h ▸ r) else s j

/-- A local pushed, holding `h`. -/
def Subst.cons {Γ Δ : Ctx} {t : LTy} (s : Subst C Γ Δ) (h : Held C Γ t) : Subst C Γ (t :: Δ)
  | _, .here => h
  | _, .there j => s j

/-- What an update leaves in each local. -/
def Upd.held {Γ : Ctx} : {Δ : Ctx} → Upd C Γ Δ → Subst C Γ Δ
  | _, .nil => fun i => .pos i
  | _, .snoc U (.local i r) => Subst.set (Upd.held U) i r
  | _, .snoc U _ => Upd.held U
  | _, .decl U _ r => Subst.cons (Upd.held U) (.rhs r)
  | _, .pop U h => fun j => Upd.held U (j.ext h)
  | _, .drop U h => fun j => Upd.held U (j.wk h)

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

/-! ## The merge is sound -/

section Sound

variable {Γ : Ctx}

/-- What `U` left in a local, read in the states before (`σ₀`) and after
(`σ₁`). -/
def Held.OK {Δ : Ctx} (σ₀ : State C Γ) (σ₁ : State C Δ) {t : LTy} (i : Idx Δ t) :
    Held C Γ t → Prop
  | .pos j => Env.get i σ₁.env = Env.get j σ₀.env
  | .rhs r => r.eval σ₀ = .ok (Env.get i σ₁.env)

theorem Env.get_set_other {Δ : Ctx} {t u : LTy} (i : Idx Δ t) (j : Idx Δ u) (h : i.toNat ≠ j.toNat)
    (v : t.Denote C) (e : Env C Δ) : Env.get j (Env.set i v e) = Env.get j e := by
  induction i with
  | here =>
    cases j with
    | here => exact absurd rfl h
    | there j => rfl
  | there i ih =>
    cases j with
    | here => rfl
    | there j => exact ih j (fun h' => h (congrArg (· + 1) h')) v e.2

theorem Env.get_drop {Δ Δ' : Ctx} {t : LTy} (h : Ext Δ' Δ) (j : Idx Δ' t) (e : Env C Δ) :
    Env.get j (Env.drop h e) = Env.get (j.ext h) e := by
  induction h with
  | refl => rfl
  | push h ih => exact ih e.2

theorem Env.get_thin : {Δ Δ' : Ctx} → (h : Thin Δ' Δ) → {t : LTy} → (j : Idx Δ' t) → (e : Env C Δ) →
    Env.get j (Env.thin h e) = Env.get (j.wk h) e
  | _, _, .refl, _, _, _ => rfl
  | _, _, .keep _, _, .here, _ => rfl
  | _, _, .keep h, _, .there j, e => Env.get_thin h j e.2
  | _, _, .drop h, _, j, e => Env.get_thin h j e.2

/-- A local read alike in two states keeps what it holds. -/
theorem Held.OK.congr {Δ Δ' : Ctx} {σ₀ : State C Γ} {σ₁ : State C Δ} {σ₁' : State C Δ'} {t : LTy}
    {i : Idx Δ t} {i' : Idx Δ' t} (he : Env.get i' σ₁'.env = Env.get i σ₁.env) :
    (x : Held C Γ t) → Held.OK σ₀ σ₁ i x → Held.OK σ₀ σ₁' i' x
  | .pos _, h => he.trans h
  | .rhs _, h => h.trans (congrArg _ he.symm)

/-- **What `U` leaves in each local** is what `Upd.held` says. -/
theorem Upd.held_ok {σ₀ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) → {σ₁ : State C Δ} →
    U.apply σ₀ = .ok σ₁ → ∀ {t : LTy} (i : Idx Δ t), Held.OK σ₀ σ₁ i (U.held i)
  | _, .nil, _, h, _, i => by cases h; rfl
  | _, .snoc U e, σ₁, h, t, i => by
    change (do e.write σ₀ (← U.apply σ₀)) = .ok σ₁ at h
    obtain ⟨τ, hτ, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    cases e with
    | «local» k r =>
      change (do pure (τ.setLocal k (← r.eval σ₀))) = .ok σ₁ at h
      obtain ⟨v, hv, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
      cases h
      show Held.OK σ₀ _ i (Subst.set (Upd.held U) k r i)
      unfold Subst.set
      split
      · rename_i hki
        obtain rfl := Idx.ty_eq_of_toNat hki
        obtain rfl := Idx.toNat_inj k i hki
        show r.eval σ₀ = .ok (Env.get k (Env.set k v τ.env))
        rw [Env.get_set]; exact hv
      · rename_i hki
        exact Held.OK.congr (Env.get_set_other k i hki v τ.env) _ (Upd.held_ok U hτ i)
    | storage x | memory x | selfBalance op x | net r op x | pay r x | netMt r x | setBalance x =>
      have henv : σ₁.env = τ.env := by
        simp only [UpdElem.write, bind, Except.bind, pure, Except.pure] at h
        repeat' split at h
        all_goals first | (cases h; rfl) | cases h
      exact Held.OK.congr (by rw [henv]) _ (Upd.held_ok U hτ i)
  | _, .decl U _ r, σ₁, h, t, i => by
    change (do let τ ← U.apply σ₀; pure (τ.push (← r.eval σ₀))) = .ok σ₁ at h
    obtain ⟨τ, hτ, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    obtain ⟨v, hv, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    cases h
    cases i with
    | here => exact hv
    | there j => exact Held.OK.congr (σ₁ := τ) (i := j) rfl _ (Upd.held_ok U hτ j)
  | _, .pop U e, σ₁, h, t, i => by
    change (U.apply σ₀).map (State.drop e) = .ok σ₁ at h
    cases hτ : U.apply σ₀ with
    | error => rw [hτ] at h; cases h
    | ok τ =>
      rw [hτ] at h; cases h
      exact Held.OK.congr (Env.get_drop e i τ.env) _ (Upd.held_ok U hτ (i.ext e))
  | _, .drop U e, σ₁, h, t, i => by
    change (U.apply σ₀).map (State.thin e) = .ok σ₁ at h
    cases hτ : U.apply σ₀ with
    | error => rw [hτ] at h; cases h
    | ok τ =>
      rw [hτ] at h; cases h
      exact Held.OK.congr (Env.get_thin e i τ.env) _ (Upd.held_ok U hτ (i.wk e))

/-- An update of locals only leaves the global part as it found it. -/
theorem Upd.envOnly_glob {σ₀ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) → U.envOnly = true →
    {σ₁ : State C Δ} → U.apply σ₀ = .ok σ₁ → σ₁.glob = σ₀.glob
  | _, .nil, _, _, h => by cases h; rfl
  | _, .snoc U e, hU, σ₁, h => by
    change (do e.write σ₀ (← U.apply σ₀)) = .ok σ₁ at h
    obtain ⟨τ, hτ, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    cases e with
    | «local» k r =>
      change (do pure (τ.setLocal k (← r.eval σ₀))) = .ok σ₁ at h
      obtain ⟨v, _, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
      cases h
      have := Upd.envOnly_glob U hU hτ
      exact this
    | _ => exact absurd hU Bool.false_ne_true
  | _, .decl U _ r, hU, σ₁, h => by
    change (do let τ ← U.apply σ₀; pure (τ.push (← r.eval σ₀))) = .ok σ₁ at h
    obtain ⟨τ, hτ, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    obtain ⟨v, _, h⟩ := Solidity.SemanticsProperties.Res.bind_eq_ok.1 h
    cases h
    have := Upd.envOnly_glob U hU hτ
    exact this
  | _, .pop U e, hU, σ₁, h => by
    change (U.apply σ₀).map (State.drop e) = .ok σ₁ at h
    cases hτ : U.apply σ₀ with
    | error => rw [hτ] at h; cases h
    | ok τ =>
      rw [hτ] at h; cases h
      have := Upd.envOnly_glob U hU hτ
      exact this
  | _, .drop U e, hU, σ₁, h => by
    change (U.apply σ₀).map (State.thin e) = .ok σ₁ at h
    cases hτ : U.apply σ₀ with
    | error => rw [hτ] at h; cases h
    | ok τ =>
      rw [hτ] at h; cases h
      have := Upd.envOnly_glob U hU hτ
      exact this

variable {Δ : Ctx} {σ₀ : State C Γ} {σ₁ : State C Δ}

theorem Tm.eval_substH_pvV {p : PrimTy} {i : Idx Δ (.val p)} {t' : Tm C Γ .val} :
    (x : Held C Γ (.val p)) → Held.OK σ₀ σ₁ i x →
      (match x with | .pos j => some (Tm.pvV j) | .rhs (.val t) => some t) = some t' →
      t'.eval σ₀ = (Tm.pvV i).eval σ₁
  | .pos j, hok, h => by cases h; show pure _ = pure _; rw [hok]
  | .rhs (.val t), hok, h => by cases h; exact hok

theorem Tm.eval_substH_pvP {R : RefTy} {i : Idx Δ (.alias R)} {t' : Tm C Γ .path} :
    (x : Held C Γ (.alias R)) → Held.OK σ₀ σ₁ i x →
      (match x with
        | .pos j => some (Tm.pvP j) | .rhs (.path p) => some p | .rhs .unset => none) = some t' →
      t'.eval σ₀ = (Tm.pvP i).eval σ₁
  | .pos j, hok, h => by
    cases h
    show aliasPath _ _ = aliasPath _ _
    unfold aliasPath
    rw [hok]
  | .rhs (.path p), hok, h => by
    cases h
    show _ = aliasPath _ _
    unfold aliasPath
    have hok : (do pure (some (← t'.eval σ₀))) = Except.ok (Env.get i σ₁.env) := hok
    cases hp : t'.eval σ₀ with
    | error e => rw [hp] at hok; cases hok
    | ok q =>
      rw [hp] at hok
      injection hok with hq
      rw [← hq]
      rfl
  | .rhs .unset, _, h => by cases h

theorem Tm.eval_substH_pvI {R : RefTy} {i : Idx Δ (.mem R)} {t' : Tm C Γ .ident} :
    (x : Held C Γ (.mem R)) → Held.OK σ₀ σ₁ i x →
      (match x with | .pos j => some (Tm.pvI j) | .rhs (.mref t) => some t) = some t' →
      t'.eval σ₀ = (Tm.pvI i).eval σ₁
  | .pos j, hok, h => by
    cases h
    have hok : Env.get i σ₁.env = Env.get j σ₀.env := hok
    show memRef σ₀ j = memRef σ₁ i
    simp only [memRef, hok]
  | .rhs (.mref t), hok, h => by
    cases h
    have hok : (do pure (some (← t'.eval σ₀))) = Except.ok (Env.get i σ₁.env) := hok
    show _ = memRef σ₁ i
    unfold memRef
    cases hp : t'.eval σ₀ with
    | error e => rw [hp] at hok; cases hok
    | ok q =>
      rw [hp] at hok
      injection hok with hq
      rw [← hq]
      rfl

theorem Tm.eval_substH_pvS {g : Bool} (hg : g = true → σ₁.glob = σ₀.glob) {i : Idx Δ .old}
    {t' : Tm C Γ .st} :
    (x : Held C Γ .old) → Held.OK σ₀ σ₁ i x →
      (match x with | .pos j => if g then some (Tm.pvS j) else none | .rhs _ => none) = some t' →
      t'.eval σ₀ = (Tm.pvS i).eval σ₁
  | .pos j, hok, h => by
    cases g with
    | false => cases h
    | true =>
      cases h
      show pure _ = pure _
      have hgl := hg rfl
      have hok : Env.get i σ₁.env = Env.get j σ₀.env := hok
      rw [hok, hgl]
  | .rhs _, _, h => by cases h

variable {U : Upd C Γ Δ} {st : Option (Tm C Γ .st)}

/-- **A term read in the state before is the term read after.** -/
theorem Tm.eval_substH (hU : U.apply σ₀ = .ok σ₁)
    (hst : ∀ x, st = some x → x.eval σ₀ = pure σ₁.glob) :
    {k : Srt} → (t : Tm C Δ k) → {t' : Tm C Γ k} → t.substH U.held U.envOnly st = some t' →
      t'.eval σ₀ = t.eval σ₁
  | _, .pvV i, _, h => Tm.eval_substH_pvV _ (Upd.held_ok U hU i) h
  | _, .pvP i, _, h => Tm.eval_substH_pvP _ (Upd.held_ok U hU i) h
  | _, .pvS i, _, h =>
    Tm.eval_substH_pvS (fun hg => Upd.envOnly_glob U hg hU) _ (Upd.held_ok U hU i) h
  | _, .pvI i, _, h => Tm.eval_substH_pvI _ (Upd.held_ok U hU i) h
  | _, .netOf i a, t', h => by
    have hx := Upd.held_ok U hU i
    have h : (match U.held i with
        | .pos j => (a.substH U.held U.envOnly st).map (Tm.netOf j) | .rhs _ => none) = some t' := h
    generalize U.held i = x at h hx
    cases x with
    | rhs _ => cases h
    | pos j =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      have hx : Env.get i σ₁.env = Env.get j σ₀.env := hx
      simp only [Tm.eval]
      rw [Tm.eval_substH hU hst a ha, hx]
  | _, .app0 o, t', h => by
    simp only [Tm.substH] at h
    split at h
    · rename_i hc
      cases h
      show o.eval σ₀.glob = o.eval σ₁.glob
      rcases Bool.or_eq_true _ _ ▸ hc with hg | hg
      · rw [Upd.envOnly_glob U hg hU]
      · exact Op0.eval_globFree hg _ _
    · revert h
      cases o with
      | storage => exact fun h => hst t' h
      | _ => exact fun h => nomatch h
  | _, .app1 o ho x, t', h => by
    simp only [Tm.substH] at h
    split at h
    · rename_i hc
      obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
      show o.eval σ₀.glob (x'.eval σ₀) = o.eval σ₁.glob (x.eval σ₁)
      rw [Tm.eval_substH hU hst x hx]
      rcases Bool.or_eq_true _ _ ▸ hc with hg | hg
      · rw [Upd.envOnly_glob U hg hU]
      · exact Op1.eval_globFree hg _ _ _
    · cases h
  | _, .app2 o x y, t', h => by
    simp only [Tm.substH] at h
    split at h
    · rename_i hc
      obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      show o.eval σ₀.glob (x'.eval σ₀) (y'.eval σ₀) = o.eval σ₁.glob (x.eval σ₁) (y.eval σ₁)
      rw [Tm.eval_substH hU hst x hx, Tm.eval_substH hU hst y hy]
      rcases Bool.or_eq_true _ _ ▸ hc with hg | hg
      · rw [Upd.envOnly_glob U hg hU]
      · exact Op2.eval_globFree hg _ _ _ _
    · cases h
  | _, .app3 o x y z, t', h => by
    simp only [Tm.substH] at h
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z', hz, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show o.eval σ₀.glob (x'.eval σ₀) (y'.eval σ₀) (z'.eval σ₀) =
      o.eval σ₁.glob (x.eval σ₁) (y.eval σ₁) (z.eval σ₁)
    rw [Tm.eval_substH hU hst x hx, Tm.eval_substH hU hst y hy, Tm.eval_substH hU hst z hz]
    exact Op3.eval_any o _ _ _ _ _

theorem Rhs.eval_substH (hU : U.apply σ₀ = .ok σ₁)
    (hst : ∀ x, st = some x → x.eval σ₀ = pure σ₁.glob) :
    {t : LTy} → (r : Rhs C Δ t) → {r' : Rhs C Γ t} → r.substH U.held U.envOnly st = some r' →
      r'.eval σ₀ = r.eval σ₁
  | _, .val t, r', h => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Tm.eval_substH hU hst t ht
  | _, .path p, r', h => by
    obtain ⟨p', hp, rfl⟩ := Option.map_eq_some_iff.1 h
    show (do pure (some (← p'.eval σ₀))) = (do pure (some (← p.eval σ₁)))
    rw [Tm.eval_substH hU hst p hp]
  | _, .unset, r', h => by cases h; rfl
  | _, .mref i, r', h => by
    obtain ⟨i', hi, rfl⟩ := Option.map_eq_some_iff.1 h
    show (do pure (some (← i'.eval σ₀))) = (do pure (some (← i.eval σ₁)))
    rw [Tm.eval_substH hU hst i hi]
  | _, .store x, r', h => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    show (do pure (← x'.eval σ₀).storage) = (do pure (← x.eval σ₁).storage)
    rw [Tm.eval_substH hU hst x hx]
  | _, .saveNet, r', h => by
    simp only [Rhs.substH] at h
    split at h
    · rename_i hg
      cases h
      show pure σ₀.net = pure σ₁.net
      have := Upd.envOnly_glob U hg hU
      rw [show σ₀.net = σ₀.glob.net from rfl, show σ₁.net = σ₁.glob.net from rfl, this]
    · cases h
  | _, .saveNetMt, r', h => by cases h; rfl

theorem UpdElem.write_substH (hU : U.apply σ₀ = .ok σ₁)
    (hst : ∀ x, st = some x → x.eval σ₀ = pure σ₁.glob) {Ε : Ctx} (e : UpdElem C Δ Ε)
    {e' : UpdElem C Γ Ε} (h : e.substH U.held U.envOnly st = some e') (τ : State C Ε) :
    e'.write σ₀ τ = e.write σ₁ τ := by
  cases e with
  | «local» i r =>
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
    show (do pure (τ.setLocal i (← r'.eval σ₀))) = (do pure (τ.setLocal i (← r.eval σ₁)))
    rw [Rhs.eval_substH hU hst r hr]
  | storage x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.write, Tm.eval_substH hU hst x hx]
  | memory x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.write, Tm.eval_substH hU hst x hx]
  | selfBalance op a =>
    simp only [UpdElem.substH] at h
    split at h
    · rename_i hg
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      have hgl := Upd.envOnly_glob U hg hU
      have hsb : σ₀.selfBalance = σ₁.selfBalance := by
        rw [show σ₀.selfBalance = σ₀.glob.selfBalance from rfl,
          show σ₁.selfBalance = σ₁.glob.selfBalance from rfl, hgl]
      simp only [UpdElem.write, Tm.eval_substH hU hst a ha, hsb]
    · cases h
  | net r op a =>
    simp only [UpdElem.substH] at h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [UpdElem.write, Tm.eval_substH hU hst r hr, Tm.eval_substH hU hst a ha]
  | pay r a =>
    simp only [UpdElem.substH] at h
    split at h
    · rename_i hg
      obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      have hgl := Upd.envOnly_glob U hg hU
      have htx : σ₀.tx = σ₁.tx := by
        rw [show σ₀.tx = σ₀.glob.tx from rfl, show σ₁.tx = σ₁.glob.tx from rfl, hgl]
      simp only [UpdElem.write, Tm.eval_substH hU hst r hr, Tm.eval_substH hU hst a ha, htx]
    · cases h
  | netMt r a =>
    simp only [UpdElem.substH] at h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [UpdElem.write, Tm.eval_substH hU hst r hr, Tm.eval_substH hU hst a ha]
  | setBalance a =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.write, Tm.eval_substH hU hst a ha]

end Sound

/-- **The grafted update runs as the two in turn.** -/
theorem Upd.apply_graft {Γ Δ₁ : Ctx} (U : Upd C Γ Δ₁) (σ₀ : State C Γ) {st : Option (Tm C Γ .st)}
    (hst : ∀ σ₁, U.apply σ₀ = .ok σ₁ → ∀ x, st = some x → x.eval σ₀ = pure σ₁.glob) :
    {Δ₂ : Ctx} → (V : Upd C Δ₁ Δ₂) → {W : Upd C Γ Δ₂} → U.graft U.held U.envOnly st V = some W →
      W.apply σ₀ = (U.apply σ₀ >>= V.apply)
  | _, .nil, W, h => by
    cases h
    cases U.apply σ₀ <;> rfl
  | _, .snoc V e, W, h => by
    simp only [Upd.graft] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    change (do e'.write σ₀ (← W'.apply σ₀)) = _
    rw [Upd.apply_graft U σ₀ hst V hW]
    cases hU : U.apply σ₀ with
    | error => rfl
    | ok σ₁ =>
      change (do e'.write σ₀ (← V.apply σ₁)) = (do e.write σ₁ (← V.apply σ₁))
      cases V.apply σ₁ with
      | error => rfl
      | ok τ => exact UpdElem.write_substH hU (hst σ₁ hU) e he τ
  | _, .decl V x r, W, h => by
    simp only [Upd.graft] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    change (do let τ ← W'.apply σ₀; pure (τ.push (← r'.eval σ₀))) = _
    rw [Upd.apply_graft U σ₀ hst V hW]
    cases hU : U.apply σ₀ with
    | error => rfl
    | ok σ₁ =>
      change (do let τ ← V.apply σ₁; pure (τ.push (← r'.eval σ₀))) =
        (do let τ ← V.apply σ₁; pure (τ.push (← r.eval σ₁)))
      rw [Rhs.eval_substH hU (hst σ₁ hU) r hr]
  | _, .pop V e, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    change (W'.apply σ₀).map (State.drop e) = _
    rw [Upd.apply_graft U σ₀ hst V hW]
    cases U.apply σ₀ <;> rfl
  | _, .drop V e, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    change (W'.apply σ₀).map (State.thin e) = _
    rw [Upd.apply_graft U σ₀ hst V hW]
    cases U.apply σ₀ <;> rfl

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

section Lift

variable {Γ : Ctx} {t : LTy}

theorem Upd.dropTop_apply (σ : State C Γ) (v : t.Denote C) :
    (Upd.dropTop (C := C) Γ t).apply (σ.push v) = .ok σ := rfl

theorem Upd.dropTop_envOnly : (Upd.dropTop (C := C) Γ t).envOnly = true := rfl

theorem UpdElem.write_lift? {Δ : Ctx} (σ : State C Γ) (v : t.Denote C) (e : UpdElem C Γ Δ)
    {e' : UpdElem C (t :: Γ) (t :: Δ)} (h : e.lift? = some e') (τ : State C Δ) :
    e'.write (σ.push v) (τ.push v) = (e.write σ τ).map (·.push v) := by
  have hD := Upd.dropTop_apply (C := C) (t := t) σ v
  have ev := fun {k : Srt} (x : Tm C Γ k) {x' : Tm C (t :: Γ) k}
    (hx : x.substH (Upd.dropTop (C := C) Γ t).held true none = some x') =>
      Tm.eval_substH (U := Upd.dropTop (C := C) Γ t) (st := none) hD (fun _ h => nomatch h) x
        (by rw [Upd.dropTop_envOnly]; exact hx)
  cases e with
  | «local» i r =>
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
    have := Rhs.eval_substH (U := Upd.dropTop (C := C) Γ t) (st := none) hD (fun _ h => nomatch h) r
      (by rw [Upd.dropTop_envOnly]; exact hr)
    show (do pure ((τ.push v).setLocal i.there (← r'.eval (σ.push v)))) =
      (do pure (τ.setLocal i (← r.eval σ))).map (fun τ' : State C Δ => τ'.push v)
    rw [this]
    cases r.eval σ <;> rfl
  | storage x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.write, ev x hx]
    cases x.eval σ <;> rfl
  | memory x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.write, ev x hx]
    cases x.eval σ <;> rfl
  | selfBalance _ _ => cases h
  | net _ _ _ => cases h
  | pay _ _ => cases h
  | netMt _ _ => cases h
  | setBalance _ => cases h

/-- **The moved update runs as the update, the local kept on top.** -/
theorem Upd.apply_lift? (σ : State C Γ) (v : t.Denote C) : {Δ : Ctx} → (U : Upd C Γ Δ) →
    {U' : Upd C (t :: Γ) (t :: Δ)} → U.lift? = some U' →
      U'.apply (σ.push v) = (U.apply σ).map (·.push v)
  | _, .nil, _, h => by cases h; rfl
  | _, .snoc U e, _, h => by
    simp only [Upd.lift?] at h
    obtain ⟨U', hU, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    change (do e'.write (σ.push v) (← U'.apply (σ.push v))) = (do e.write σ (← U.apply σ)).map _
    rw [Upd.apply_lift? σ v U hU]
    cases U.apply σ with
    | error => rfl
    | ok τ => exact UpdElem.write_lift? σ v e he τ
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

theorem Upd.apply_nextId (σ₀ : State C Γ) : {Δ : Ctx} → (U : Upd C Γ Δ) → U.keepsNext = true →
    ∀ τ, U.apply σ₀ = .ok τ → τ.nextId = σ₀.nextId
  | _, .nil, _, τ, h => by cases h; rfl
  | _, .snoc U e, hk, τ, h => by
    have hk' : U.keepsNext = true ∧ e.keepsNext = true := Bool.and_eq_true_iff.mp hk
    obtain ⟨τ', h₁, h₂⟩ := Semantics.bind_ok_inv h
    have ih := Upd.apply_nextId σ₀ U hk'.1 τ' h₁
    cases e with
    | «local» i r =>
      obtain ⟨v, -, h₂⟩ := Semantics.bind_ok_inv h₂
      cases h₂
      exact ih
    | storage s =>
      obtain ⟨st, -, h₂⟩ := Semantics.bind_ok_inv h₂
      cases h₂
      exact ih
    | _ => cases hk'.2
  | _, .decl U _ r, hk, τ, h => by
    obtain ⟨τ', h₁, h₂⟩ := Semantics.bind_ok_inv h
    obtain ⟨v, -, h₂⟩ := Semantics.bind_ok_inv h₂
    cases h₂
    exact Upd.apply_nextId σ₀ U hk τ' h₁
  | _, .pop U e, hk, τ, h => by
    cases h₁ : U.apply σ₀ with
    | error => rw [Upd.apply, h₁] at h; cases h
    | ok τ' =>
      rw [Upd.apply, h₁] at h
      cases h
      exact Upd.apply_nextId σ₀ U hk τ' h₁
  | _, .drop U e, hk, τ, h => by
    cases h₁ : U.apply σ₀ with
    | error => rw [Upd.apply, h₁] at h; cases h
    | ok τ' =>
      rw [Upd.apply, h₁] at h
      cases h
      exact Upd.apply_nextId σ₀ U hk τ' h₁

/-- A local's value, cast along an equal heap typing, erases as it did. -/
theorem LTy.TDenote.erase_rec {H H' : HTy} (h : H' = H) (t : LTy) (v' : t.TDenote C H') :
    LTy.TDenote.erase t (h ▸ v' : t.TDenote C H) = LTy.TDenote.erase t v' := by
  subst h; rfl

/-- `{U} ∀x. ψ` from `∀x. {U↑} ψ`, `U↑` the update moved under the binder.
A value of the binder after `U` is one before it: its type is not a memory
one, or `U` allocates nothing, so the heap typing after it, which extends
the one before, is that one. -/
theorem Fml.upd_bind_of_apply {m m' : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} {t : LTy} {x : Var}
    {U' : Upd C (t :: Γ) (t :: Δ)}
    (hap : ∀ (τ : State C Γ) (w : t.Denote C), U'.apply (τ.push w) = (U.apply τ).map (·.push w))
    (ht : (t.notMem || U.keepsNext) = true)
    {ψ : Fml C (t :: Δ)} (σ : TState C Γ)
    (hψ : m'.forallB fun v : t.TDenote C σ.H => holds (σ.push v) (.upd m U' ψ)) :
    holds σ (.upd m U (.bind m' x t ψ)) := by
  have hg : ∀ v : t.TDenote C σ.H, U'.apply (σ.push v).erase =
      (U.apply σ.erase).map (·.push (LTy.TDenote.erase t v)) :=
    fun v => hap σ.erase _
  obtain ⟨v₀⟩ := LTy.tdenote_nonempty (C := C) (H := σ.H) t
  show m.afterC
    (fun τ => ∀ σ' : TState C _, σ'.erase = τ → σ.H <+: σ'.H → holds σ' (.bind m' x t ψ))
    (U.apply σ.erase)
  cases hU : U.apply σ.erase with
  | error e =>
    have h₀ : m.afterC
        (fun τ => ∀ σ' : TState C _, σ'.erase = τ → (σ.push v₀).H <+: σ'.H → holds σ' ψ)
        (U'.apply (σ.push v₀).erase) := Modality.forallB_all hψ v₀
    rw [hg, hU] at h₀
    exact h₀
  | ok σ₁ =>
    intro σ' he hext
    refine Modality.forallB_intro fun v' => ?_
    have hv : ∃ v : t.TDenote C σ.H, LTy.TDenote.erase t v = LTy.TDenote.erase t v' := by
      rcases Bool.or_eq_true_iff.mp ht with ht | hk
      · exact LTy.erase_of_notMem ht v'
      · have hn : σ'.H.length = σ.H.length := by
          have h₁ := Upd.apply_nextId σ.erase U hk σ₁ hU
          rw [← he] at h₁
          exact h₁
        have hH : σ'.H = σ.H := (hext.eq_of_length hn.symm).symm
        exact ⟨hH ▸ v', LTy.TDenote.erase_rec hH t v'⟩
    obtain ⟨v, hv⟩ := hv
    have h : m.afterC
        (fun τ => ∀ σ' : TState C _, σ'.erase = τ → (σ.push v).H <+: σ'.H → holds σ' ψ)
        (U'.apply (σ.push v).erase) := Modality.forallB_all hψ v
    rw [hg, hU] at h
    refine h (σ'.push v') ?_ hext
    show (σ'.erase.push (LTy.TDenote.erase t v') : State C _) = σ₁.push (LTy.TDenote.erase t v)
    rw [he, hv]

theorem Fml.upd_bind_of_lift {m m' : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} {t : LTy} {x : Var}
    {U' : Upd C (t :: Γ) (t :: Δ)} (hU' : U.lift? = some U') (ht : (t.notMem || U.keepsNext) = true)
    {ψ : Fml C (t :: Δ)} (σ : TState C Γ)
    (hψ : m'.forallB fun v : t.TDenote C σ.H => holds (σ.push v) (.upd m U' ψ)) :
    holds σ (.upd m U (.bind m' x t ψ)) :=
  Fml.upd_bind_of_apply (fun τ w => Upd.apply_lift? τ w U hU') ht σ hψ

/-- An update moved under a pushed local, its scope ends too: a pop or a
drop below the local is a thinning that keeps it (the sequent's merge; a
chain's moves `Upd.lift?`'s). -/
def Upd.liftG? {Γ : Ctx} {t : LTy} : {Δ : Ctx} → Upd C Γ Δ → Option (Upd C (t :: Γ) (t :: Δ))
  | _, .nil => some .nil
  | _, .snoc U e => do pure (.snoc (← Upd.liftG? U) (← e.lift?))
  | _, .pop U h => (Upd.liftG? U).map (.drop · (.keep (Thin.ofExt h)))
  | _, .drop U h => (Upd.liftG? U).map (.drop · (.keep h))
  | _, .decl .. => none

theorem Env.thin_ofExt {Γ : Ctx} : {Δ : Ctx} → (h : Ext Γ Δ) → (e : Env C Δ) →
    Env.thin (Thin.ofExt h) e = Env.drop h e
  | _, .refl, _ => rfl
  | _, .push h, e => Env.thin_ofExt h e.2

/-- **The moved update runs as the update, the local kept on top.** -/
theorem Upd.apply_liftG? {Γ : Ctx} {t : LTy} (σ : State C Γ) (v : t.Denote C) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → {U' : Upd C (t :: Γ) (t :: Δ)} → U.liftG? = some U' →
      U'.apply (σ.push v) = (U.apply σ).map (·.push v)
  | _, .nil, _, h => by cases h; rfl
  | _, .snoc U e, _, h => by
    simp only [Upd.liftG?] at h
    obtain ⟨U', hU, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    change (do e'.write (σ.push v) (← U'.apply (σ.push v))) = (do e.write σ (← U.apply σ)).map _
    rw [Upd.apply_liftG? σ v U hU]
    cases U.apply σ with
    | error => rfl
    | ok τ => exact UpdElem.write_lift? σ v e he τ
  | _, .pop U h, _, hh => by
    obtain ⟨U', hU, rfl⟩ := Option.map_eq_some_iff.1 hh
    change (U'.apply (σ.push v)).map (State.thin _) = ((U.apply σ).map (State.drop h)).map _
    rw [Upd.apply_liftG? σ v U hU]
    cases U.apply σ with
    | error => rfl
    | ok τ =>
      show Except.ok (State.thin _ (τ.push v)) = Except.ok ((τ.drop h).push v)
      simp only [State.thin, State.push, State.drop, State.withEnv, Env.thin, Env.thin_ofExt]
  | _, .drop U h, _, hh => by
    obtain ⟨U', hU, rfl⟩ := Option.map_eq_some_iff.1 hh
    change (U'.apply (σ.push v)).map (State.thin _) = ((U.apply σ).map (State.thin h)).map _
    rw [Upd.apply_liftG? σ v U hU]
    cases U.apply σ with
    | error => rfl
    | ok τ => rfl
  | _, .decl .., _, h => by cases h

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

/-- **A storage term changes only the storage** of the state it is read in. -/
theorem Tm.eval_stChg {Γ : Ctx} (σ : State C Γ) : {s : Srt} → (t : Tm C Γ s) →
    Srt.StChgOf σ.glob s (t.eval σ)
  | _, .pvV _ | _, .pvP _ | _, .pvI _ | _, .netOf .. => trivial
  | _, .pvS i => fun g h => by cases h; rfl
  | _, .app0 o => by
    cases o with
    | storage => intro g h; cases h; rfl
    | mtSt vs => intro g h; cases h; rfl
    | _ => trivial
  | _, .app1 o _ x => by
    have ih := Tm.eval_stChg σ x
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
    have ih := Tm.eval_stChg σ x
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
    have ih := Tm.eval_stChg σ x
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

theorem Tm.eval_st_glob {Γ : Ctx} (σ : State C Γ) (t : Tm C Γ .st) (g : Semantics.State)
    (h : t.eval σ = .ok g) : StChg σ.glob g :=
  Tm.eval_stChg σ t g h

/-- An update that writes no global part but the storage leaves the global
part with another storage. -/
theorem Upd.stOnly_glob {Γ : Ctx} {σ₀ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) →
    U.stOnly = true → {σ₁ : State C Δ} → U.apply σ₀ = .ok σ₁ → StChg σ₀.glob σ₁.glob
  | _, .nil, _, _, h => by cases h; rfl
  | _, .snoc U e, hU, σ₁, h => by
    have hU' : U.stOnly = true ∧ e.stOnly = true := Bool.and_eq_true_iff.mp hU
    obtain ⟨τ, hτ, h⟩ := Semantics.bind_ok_inv h
    have ih := Upd.stOnly_glob U hU'.1 hτ
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
  | _, .decl U _ r, hU, σ₁, h => by
    obtain ⟨τ, hτ, h⟩ := Semantics.bind_ok_inv h
    obtain ⟨v, _, h⟩ := Semantics.bind_ok_inv h
    cases h
    exact Upd.stOnly_glob U hU hτ
  | _, .pop U e, hU, σ₁, h => by
    cases hτ : U.apply σ₀ with
    | error => rw [Upd.apply, hτ] at h; cases h
    | ok τ =>
      rw [Upd.apply, hτ] at h; cases h
      exact Upd.stOnly_glob U hU hτ
  | _, .drop U e, hU, σ₁, h => by
    cases hτ : U.apply σ₀ with
    | error => rw [Upd.apply, hτ] at h; cases h
    | ok τ =>
      rw [Upd.apply, hτ] at h; cases h
      exact Upd.stOnly_glob U hU hτ

/-- **The storage an update last wrote, read before it, is the global part
after it.** -/
theorem Upd.lastSt_eval {Γ : Ctx} {σ₀ : State C Γ} : {Δ : Ctx} → (U : Upd C Γ Δ) →
    {σ₁ : State C Δ} → U.apply σ₀ = .ok σ₁ → ∀ x, U.lastSt = some x → x.eval σ₀ = pure σ₁.glob
  | _, .nil, _, _, _, h => by cases h
  | _, .snoc U e, σ₁, h, x, hx => by
    obtain ⟨τ, hτ, h⟩ := Semantics.bind_ok_inv h
    cases e with
    | «local» k r =>
      obtain ⟨v, _, h⟩ := Semantics.bind_ok_inv h
      cases h
      exact Upd.lastSt_eval U hτ x hx
    | storage y =>
      simp only [Upd.lastSt] at hx
      split at hx
      · rename_i hs
        cases hx
        obtain ⟨g, hg, h⟩ := Semantics.bind_ok_inv h
        cases h
        rw [hg]
        have h₁ : StChg σ₀.glob τ.glob := Upd.stOnly_glob U hs hτ
        have h₂ : StChg σ₀.glob g := Tm.eval_st_glob σ₀ x g hg
        show Except.ok g = Except.ok { τ.glob with storage := g.storage }
        rw [h₁, h₂]
      · cases hx
    | _ => cases hx
  | _, .decl U _ r, σ₁, h, x, hx => by
    obtain ⟨τ, hτ, h⟩ := Semantics.bind_ok_inv h
    obtain ⟨v, _, h⟩ := Semantics.bind_ok_inv h
    cases h
    exact Upd.lastSt_eval U hτ x hx
  | _, .pop U e, σ₁, h, x, hx => by
    cases hτ : U.apply σ₀ with
    | error => rw [Upd.apply, hτ] at h; cases h
    | ok τ =>
      rw [Upd.apply, hτ] at h; cases h
      exact Upd.lastSt_eval U hτ x hx
  | _, .drop U e, σ₁, h, x, hx => by
    cases hτ : U.apply σ₀ with
    | error => rw [Upd.apply, hτ] at h; cases h
    | ok τ =>
      rw [Upd.apply, hτ] at h; cases h
      exact Upd.lastSt_eval U hτ x hx

end StGlob

/-- **`sequentialToParallel` runs as the two updates in turn.** -/
theorem Upd.apply_seqPar {Γ Δ₁ Δ₂ : Ctx} (U : Upd C Γ Δ₁) (σ₀ : State C Γ) (V : Upd C Δ₁ Δ₂)
    {W : Upd C Γ Δ₂} (h : U.seqPar V = some W) : W.apply σ₀ = (U.apply σ₀ >>= V.apply) :=
  Upd.apply_graft U σ₀ (fun _ hU x hx => Upd.lastSt_eval U hU x hx) V h

/-- **The merged update gives the two**: `{U ‖ {U}V} φ` gives `{U}{V} φ`
under the modality of both, `st` the storage `U` leaves where any. -/
theorem holds_upd_graft {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} {st : Option (Tm C Γ .st)}
    (hst : ∀ σ₀ σ₁, U.apply σ₀ = .ok σ₁ → ∀ x, st = some x → x.eval σ₀ = pure σ₁.glob)
    (hW : U.graft U.held U.envOnly st V = some W) {φ : Fml C Δ₂} (σ : TState C Γ)
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) := by
  have hg := Upd.apply_graft U σ.erase (hst σ.erase) V hW
  show m.afterC
    (fun τ => ∀ σ' : TState C _, σ'.erase = τ → σ.H <+: σ'.H → holds σ' (.upd m V φ))
    (U.apply σ.erase)
  have h : m.afterC (fun τ => ∀ σ' : TState C _, σ'.erase = τ → σ.H <+: σ'.H → holds σ' φ)
    (W.apply σ.erase) := h
  rw [hg] at h
  cases hU : U.apply σ.erase with
  | error e => rw [hU] at h; exact h
  | ok σ₁ =>
    rw [hU] at h
    intro σ' he hext
    show m.afterC _ (V.apply σ'.erase)
    rw [he]
    exact Modality.afterC_imp h fun τ h σ'' e₂ hext₂ => h σ'' e₂ (hext.trans hext₂)

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
    {ψ : Fml C (Binds.ctx bs Δ)} → ∀ σ : TState C Γ,
      holds σ (Fml.binds bs (.upd m U' ψ)) → holds σ (.upd m U (Fml.binds bs ψ))
  | _, _, [], _, _, h, _, _, hσ => by cases h; exact hσ
  | _, _, (m', x, t) :: bs, U, U', h, ψ, σ, hσ => by
    simp only [Upd.liftBinds?] at h
    split at h
    · rename_i ht
      obtain ⟨U₁, hU₁, h⟩ := Option.bind_eq_some_iff.1 h
      exact Fml.upd_bind_of_apply (fun τ w => Upd.apply_liftG? τ w U hU₁) ht σ
        (Modality.forallB_imp (fun v hv => holds_liftBinds bs h _ hv) hσ)
    · cases h

/-! ## Rewriting the right-hand sides of an update

`Proves.updRw` rewrites the right-hand sides of the last box update with a
term taclet `t ⇝ t'` of today's terms (`Calculus/TermTaclets.lean`, or a
Theory law, `Calculus/TheoryRewrite.lean`) whose right side returns
wherever its left side does, the same value (`Term.EvalRefines`): every
closed occurrence of `t` (no local in it), read on its erasure, becomes
`t'` (`Tm.rwC`). -/

/-- A term with no local, at the empty scope. -/
def Tm.toNil? {Γ : Ctx} : {s : Srt} → Tm C Γ s → Option (Tm C [] s)
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .netOf .. => none
  | _, .app0 o => some (.app0 o)
  | _, .app1 o ho x => (Tm.toNil? x).map (.app1 o ho)
  | _, .app2 o x y => do pure (.app2 o (← Tm.toNil? x) (← Tm.toNil? y))
  | _, .app3 o x y z => do pure (.app3 o (← Tm.toNil? x) (← Tm.toNil? y) (← Tm.toNil? z))

/-- Today's term with no local, at the scope `Γ`. -/
def Tm.ofClosed? {Γ : Ctx} : {s : Srt} → Solidity.Tm C s → Option (Tm C Γ s)
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ => none
  | _, .app0 o => some (.app0 o)
  | _, .app1 o x => if ho : o.named = false then (Tm.ofClosed? x).map (.app1 o ho) else none
  | _, .app2 o x y => do pure (.app2 o (← Tm.ofClosed? x) (← Tm.ofClosed? y))
  | _, .app3 o x y z => do pure (.app3 o (← Tm.ofClosed? x) (← Tm.ofClosed? y) (← Tm.ofClosed? z))

/-- `t` where it is a closed value term reading `q.1` on its erasure: `q.2`;
`d` anywhere else. -/
def Tm.pickC {Γ : Ctx} (q : Solidity.Term C × Solidity.Term C) : {s : Srt} → Tm C Γ s → Tm C Γ s →
    Tm C Γ s
  | .val, t, d =>
    if (t.toNil?).isSome && t.erase [] == q.1 then (Tm.ofClosed? q.2).getD d else d
  | _, _, d => d

/-- Every closed occurrence of `q.1` in a term, replaced by `q.2`. -/
def Tm.rwC {Γ : Ctx} (q : Solidity.Term C × Solidity.Term C) : {s : Srt} → Tm C Γ s → Tm C Γ s
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
def Rhs.rwC {Γ : Ctx} (q : Solidity.Term C × Solidity.Term C) : {t : LTy} → Rhs C Γ t → Rhs C Γ t
  | _, .val t => .val (t.rwC q)
  | _, .path p => .path (p.rwC q)
  | _, .unset => .unset
  | _, .mref i => .mref (i.rwC q)
  | _, .store s => .store (s.rwC q)
  | _, .saveNet => .saveNet
  | _, .saveNetMt => .saveNetMt

/-- An element's right-hand sides rewritten. -/
def UpdElem.rwC {Γ Δ : Ctx} (q : Solidity.Term C × Solidity.Term C) : UpdElem C Γ Δ → UpdElem C Γ Δ
  | .local i r => .local i (r.rwC q)
  | .storage s => .storage (s.rwC q)
  | .memory m => .memory (m.rwC q)
  | .selfBalance op a => .selfBalance op (a.rwC q)
  | .net r op a => .net (r.rwC q) op (a.rwC q)
  | .pay r a => .pay (r.rwC q) (a.rwC q)
  | .netMt r a => .netMt (r.rwC q) (a.rwC q)
  | .setBalance a => .setBalance (a.rwC q)

/-- An update's right-hand sides rewritten. -/
def Upd.rwC {Γ : Ctx} (q : Solidity.Term C × Solidity.Term C) : {Δ : Ctx} → Upd C Γ Δ → Upd C Γ Δ
  | _, .nil => .nil
  | _, .snoc U e => .snoc (Upd.rwC q U) (e.rwC q)
  | _, .decl U x r => .decl (Upd.rwC q U) x (r.rwC q)
  | _, .pop U h => .pop (Upd.rwC q U) h
  | _, .drop U h => .drop (Upd.rwC q U) h

section RwC

variable {Γ : Ctx}

theorem State.glob_env (σ : State C Γ) : withLocals σ.glob [] = σ.glob := rfl

/-- A closed term reads as its erasure in the global part. -/
theorem Tm.eval_toNil (σ : State C Γ) : {s : Srt} → (t : Tm C Γ s) → {t₀ : Tm C [] s} →
    t.toNil? = some t₀ → t.eval σ = (t.erase []).eval σ.glob
  | _, .pvV _, _, h | _, .pvP _, _, h | _, .pvS _, _, h | _, .pvI _, _, h | _, .netOf .., _, h =>
    nomatch h
  | _, .app0 o, _, _ => rfl
  | _, .app1 o ho x, _, h => by
    obtain ⟨x₀, hx, -⟩ := Option.map_eq_some_iff.1 h
    show o.eval σ.glob (x.eval σ) = o.eval σ.glob ((x.erase []).eval σ.glob)
    rw [Tm.eval_toNil σ x hx]
  | _, .app2 o x y, _, h => by
    obtain ⟨x₀, hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y₀, hy, -⟩ := Option.bind_eq_some_iff.1 h
    show o.eval σ.glob (x.eval σ) (y.eval σ) =
      o.eval σ.glob ((x.erase []).eval σ.glob) ((y.erase []).eval σ.glob)
    rw [Tm.eval_toNil σ x hx, Tm.eval_toNil σ y hy]
  | _, .app3 o x y z, _, h => by
    obtain ⟨x₀, hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y₀, hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z₀, hz, -⟩ := Option.bind_eq_some_iff.1 h
    show o.eval σ.glob (x.eval σ) (y.eval σ) (z.eval σ) =
      o.eval σ.glob ((x.erase []).eval σ.glob) ((y.erase []).eval σ.glob) ((z.erase []).eval σ.glob)
    rw [Tm.eval_toNil σ x hx, Tm.eval_toNil σ y hy, Tm.eval_toNil σ z hz]

/-- Today's closed term, at a scope, reads as itself in the global part. -/
theorem Tm.eval_ofClosed (σ : State C Γ) : {s : Srt} → (q : Solidity.Tm C s) → {t : Tm C Γ s} →
    Tm.ofClosed? q = some t → t.eval σ = q.eval σ.glob
  | _, .pvV _, _, h | _, .pvP _, _, h | _, .pvS _, _, h | _, .pvI _, _, h => nomatch h
  | _, .app0 o, _, h => by cases h; rfl
  | _, .app1 o x, _, h => by
    simp only [Tm.ofClosed?] at h
    split at h
    · obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
      show o.eval σ.glob (x'.eval σ) = o.eval σ.glob (x.eval σ.glob)
      rw [Tm.eval_ofClosed σ x hx]
    · cases h
  | _, .app2 o x y, _, h => by
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show o.eval σ.glob (x'.eval σ) (y'.eval σ) = o.eval σ.glob (x.eval σ.glob) (y.eval σ.glob)
    rw [Tm.eval_ofClosed σ x hx, Tm.eval_ofClosed σ y hy]
  | _, .app3 o x y z, _, h => by
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z', hz, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show o.eval σ.glob (x'.eval σ) (y'.eval σ) (z'.eval σ) =
      o.eval σ.glob (x.eval σ.glob) (y.eval σ.glob) (z.eval σ.glob)
    rw [Tm.eval_ofClosed σ x hx, Tm.eval_ofClosed σ y hy, Tm.eval_ofClosed σ z hz]

variable {q : Solidity.Term C × Solidity.Term C}

theorem Tm.pickC_eval (hq : Term.EvalRefines q.1 q.2) (σ : State C Γ) :
    {s : Srt} → {t d : Tm C Γ s} → Srt.Le s (t.eval σ) (d.eval σ) →
      Srt.Le s (t.eval σ) ((Tm.pickC q t d).eval σ)
  | .val, t, d, hd => by
    simp only [Tm.pickC]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Option.isSome_iff_exists, beq_iff_eq] at hc
      obtain ⟨⟨t₀, ht₀⟩, he⟩ := hc
      cases ho : Tm.ofClosed? (Γ := Γ) q.2 with
      | none => exact hd
      | some u =>
        show Res.Le (t.eval σ) (u.eval σ)
        rw [Tm.eval_toNil σ t ht₀, he, Tm.eval_ofClosed σ q.2 ho]
        exact hq σ.glob
    · exact hd
  | .path, _, _, hd | .st, _, _, hd | .sv, _, _, hd | .ident, _, _, hd | .addr, _, _, hd
  | .mem, _, _, hd | .mv, _, _, hd => hd

/-- **Rewriting keeps every value a term returns.** -/
theorem Tm.rwC_eval (hq : Term.EvalRefines q.1 q.2) (σ : State C Γ) :
    {s : Srt} → (t : Tm C Γ s) → Srt.Le s (t.eval σ) ((t.rwC q).eval σ)
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ => Srt.Le.refl _ _
  | _, .netOf _ a => Res.Le.bind (Tm.rwC_eval hq σ a) fun _ => Res.Le.refl _
  | _, .app0 _ => Tm.pickC_eval hq σ (Srt.Le.refl _ _)
  | _, .app1 o _ x => Tm.pickC_eval hq σ (o.eval_le (Tm.rwC_eval hq σ x))
  | _, .app2 o x y => Tm.pickC_eval hq σ (o.eval_le (Tm.rwC_eval hq σ x) (Tm.rwC_eval hq σ y))
  | _, .app3 o x y z =>
    Tm.pickC_eval hq σ (o.eval_le (Tm.rwC_eval hq σ x) (Tm.rwC_eval hq σ y) (Tm.rwC_eval hq σ z))

theorem Rhs.rwC_eval (hq : Term.EvalRefines q.1 q.2) (σ : State C Γ) {t : LTy} (r : Rhs C Γ t) :
    Res.Le (r.eval σ) ((r.rwC q).eval σ) := by
  cases r with
  | val t => exact Tm.rwC_eval hq σ t
  | path p => exact Res.Le.bind (Tm.rwC_eval hq σ p) fun _ => Res.Le.refl _
  | unset => exact Res.Le.refl _
  | mref i => exact Res.Le.bind (Tm.rwC_eval hq σ i) fun _ => Res.Le.refl _
  | store s => exact Res.Le.bind (Tm.rwC_eval hq σ s) fun _ => Res.Le.refl _
  | saveNet => exact Res.Le.refl _
  | saveNetMt => exact Res.Le.refl _

theorem UpdElem.rwC_write (hq : Term.EvalRefines q.1 q.2) {Δ : Ctx} (σ₀ : State C Γ)
    (e : UpdElem C Γ Δ) (τ : State C Δ) : Res.Le (e.write σ₀ τ) ((e.rwC q).write σ₀ τ) := by
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
theorem Upd.rwC_apply (hq : Term.EvalRefines q.1 q.2) (σ₀ : State C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → Res.Le (U.apply σ₀) ((U.rwC q).apply σ₀)
  | _, .nil => Res.Le.refl _
  | _, .snoc U e => Res.Le.bind (Upd.rwC_apply hq σ₀ U) fun τ => UpdElem.rwC_write hq σ₀ e τ
  | _, .decl U x r => Res.Le.bind (Upd.rwC_apply hq σ₀ U) fun _ =>
      Res.Le.bind (Rhs.rwC_eval hq σ₀ r) fun _ => Res.Le.refl _
  | _, .pop U h => fun τ hτ => by
    change (U.apply σ₀).map (State.drop h) = .ok τ at hτ
    cases hU : U.apply σ₀ with
    | error => rw [hU] at hτ; cases hτ
    | ok τ₀ =>
      rw [hU] at hτ; cases hτ
      show ((U.rwC q).apply σ₀).map (State.drop h) = _
      rw [Upd.rwC_apply hq σ₀ U τ₀ hU]; rfl
  | _, .drop U h => fun τ hτ => by
    change (U.apply σ₀).map (State.thin h) = .ok τ at hτ
    cases hU : U.apply σ₀ with
    | error => rw [hU] at hτ; cases hτ
    | ok τ₀ =>
      rw [hU] at hτ; cases hτ
      show ((U.rwC q).apply σ₀).map (State.thin h) = _
      rw [Upd.rwC_apply hq σ₀ U τ₀ hU]; rfl

/-- **Under the box, a rewritten update gives the update.** -/
theorem holds_upd_rwC (hq : Term.EvalRefines q.1 q.2) {Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ}
    (σ : TState C Γ) (h : holds σ (.upd .box (U.rwC q) φ)) : holds σ (.upd .box U φ) := by
  show Modality.afterC .box _ (U.apply σ.erase)
  have h : Modality.afterC .box _ ((U.rwC q).apply σ.erase) := h
  cases hU : U.apply σ.erase with
  | error => trivial
  | ok τ => rw [Upd.rwC_apply hq σ.erase U τ hU] at h; exact h

end RwC

/-- `holds_upd_graft` for `sequentialToParallel`. -/
theorem holds_upd_seqPar {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} (hW : U.seqPar V = some W) {φ : Fml C Δ₂} (σ : TState C Γ)
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) :=
  holds_upd_graft (fun _ _ hU x hx => Upd.lastSt_eval U hU x hx) hW σ h

end Solidity.Core
