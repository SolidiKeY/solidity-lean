import Solidity.Calculus.Core.ProvesSound
import Solidity.Calculus.Core.Close

/-!
# `sequentialToParallel` on scoped updates

KeY's `sequentialToParallel2` (`{u}{u2}φ ⇝ {u ‖ {u}u2}φ`) on the scoped
updates of `Calculus/Core/Fml.lean`, so that a scoped chain merges its stack
while the program is still open (`Examples/Chains/StorageToMemory.lean`'s
`FieldCopy` and `TokenCopy`), as `Calculus/ChainRewrites.lean`'s merge does on
`Update.lean`'s lines past it.

`{U}{V}φ` becomes `{W}φ`, `W` the elements of `U` and then those of `V`, each
right-hand side of `V` read in `U`'s state: its locals replaced by what `U`
leaves in them (`Upd.held`: a local of the state `U` is applied in, or the
right-hand side `U` last wrote to it).  A symbol of `V` may read the global
part of the state (`storage`, `memory`, a bounds check) only where `U` writes
no global part (`Upd.envOnly`), so that both read the same; any other merge
is refused (`none`), never wrong.  Under the diamond the state between the
two updates must keep its `bool` locals `bool`s (`Upd.boolB`).

The merge is a function the kernel evaluates (`Fml.mergeRun`), and its
soundness one theorem: `Fml.mergeRun_leads`.
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
  cases o <;> first | rfl | simp [Op0.globFree, Op1.globFree, Op2.globFree] at h

theorem _root_.Solidity.Op1.eval_globFree {a s : Srt} {o : Op1 a s} (h : o.globFree = true)
    (g g' : Semantics.State) (x : a.Ev) : o.eval g x = o.eval g' x := by
  cases o <;> first | rfl | simp [Op0.globFree, Op1.globFree, Op2.globFree] at h

theorem _root_.Solidity.Op2.eval_globFree {a b s : Srt} {o : Op2 a b s} (h : o.globFree = true)
    (g g' : Semantics.State) (x : a.Ev) (y : b.Ev) : o.eval g x y = o.eval g' x y := by
  cases o <;> first | rfl | simp [Op0.globFree, Op1.globFree, Op2.globFree] at h

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
  fun {u} j => if h : i.toNat = j.toNat then .rhs (Idx.ty_eq_of_toNat h ▸ r) else s j

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

section Subst

variable {Γ Δ : Ctx} (s : Subst C Γ Δ) (g : Bool)

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
  | _, .app0 o => if g || o.globFree then some (.app0 o) else none
  | _, .app1 o ho x => if g || o.globFree then (Tm.substH x).map (.app1 o ho) else none
  | _, .app2 o x y =>
    if g || o.globFree then do pure (.app2 o (← Tm.substH x) (← Tm.substH y)) else none
  | _, .app3 o x y z => do pure (.app3 o (← Tm.substH x) (← Tm.substH y) (← Tm.substH z))

/-- A right-hand side of `Δ` read in `Γ`. -/
def Rhs.substH : {t : LTy} → Rhs C Δ t → Option (Rhs C Γ t)
  | _, .val t => (t.substH s g).map .val
  | _, .path p => (p.substH s g).map .path
  | _, .unset => some .unset
  | _, .mref i => (i.substH s g).map .mref
  | _, .store x => (x.substH s g).map .store
  | _, .saveNet => if g then some .saveNet else none
  | _, .saveNetMt => some .saveNetMt

/-- An element whose right-hand sides are read in `Δ`, read in `Γ`. -/
def UpdElem.substH {Ε : Ctx} : UpdElem C Δ Ε → Option (UpdElem C Γ Ε)
  | .local i r => (r.substH s g).map (.local i)
  | .storage x => (x.substH s g).map .storage
  | .memory m => (m.substH s g).map .memory
  | .selfBalance op a => if g then (a.substH s g).map (.selfBalance op) else none
  | .net r op a => do pure (.net (← r.substH s g) op (← a.substH s g))
  | .pay r a => if g then do pure (.pay (← r.substH s g) (← a.substH s g)) else none
  | .netMt r a => do pure (.netMt (← r.substH s g) (← a.substH s g))
  | .setBalance a => (a.substH s g).map .setBalance

end Subst

/-- `V` applied after `U`, as one update from `U`'s state: `U`'s elements,
then `V`'s, each read in `U`'s state (`s`, `g`: `U.held`, `U.envOnly`). -/
def Upd.graft {Γ Δ₁ : Ctx} (U : Upd C Γ Δ₁) (s : Subst C Γ Δ₁) (g : Bool) :
    {Δ₂ : Ctx} → Upd C Δ₁ Δ₂ → Option (Upd C Γ Δ₂)
  | _, .nil => some U
  | _, .snoc V e => do pure (.snoc (← Upd.graft U s g V) (← e.substH s g))
  | _, .decl V x r => do pure (.decl (← Upd.graft U s g V) x (← r.substH s g))
  | _, .pop V h => (Upd.graft U s g V).map (.pop · h)
  | _, .drop V h => (Upd.graft U s g V).map (.drop · h)

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
  | .pos j, hok, h => by cases h; show pure _ = pure _; rw [hok]
  | .rhs (.mref t), hok, h => by cases h; exact hok

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

variable {U : Upd C Γ Δ}

/-- **A term read in the state before is the term read after.** -/
theorem Tm.eval_substH (hU : U.apply σ₀ = .ok σ₁) :
    {k : Srt} → (t : Tm C Δ k) → {t' : Tm C Γ k} → t.substH U.held U.envOnly = some t' →
      t'.eval σ₀ = t.eval σ₁
  | _, .pvV i, _, h => Tm.eval_substH_pvV _ (Upd.held_ok U hU i) h
  | _, .pvP i, _, h => Tm.eval_substH_pvP _ (Upd.held_ok U hU i) h
  | _, .pvS i, _, h =>
    Tm.eval_substH_pvS (fun hg => Upd.envOnly_glob U hg hU) _ (Upd.held_ok U hU i) h
  | _, .pvI i, _, h => Tm.eval_substH_pvI _ (Upd.held_ok U hU i) h
  | _, .netOf i a, t', h => by
    have hx := Upd.held_ok U hU i
    have h : (match U.held i with
        | .pos j => (a.substH U.held U.envOnly).map (Tm.netOf j) | .rhs _ => none) = some t' := h
    generalize U.held i = x at h hx
    cases x with
    | rhs _ => cases h
    | pos j =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      have hx : Env.get i σ₁.env = Env.get j σ₀.env := hx
      simp only [Tm.eval]
      rw [Tm.eval_substH hU a ha, hx]
  | _, .app0 o, t', h => by
    simp only [Tm.substH] at h
    split at h
    · rename_i hc
      cases h
      show o.eval σ₀.glob = o.eval σ₁.glob
      rcases Bool.or_eq_true _ _ ▸ hc with hg | hg
      · rw [Upd.envOnly_glob U hg hU]
      · exact Op0.eval_globFree hg _ _
    · cases h
  | _, .app1 o ho x, t', h => by
    simp only [Tm.substH] at h
    split at h
    · rename_i hc
      obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
      show o.eval σ₀.glob (x'.eval σ₀) = o.eval σ₁.glob (x.eval σ₁)
      rw [Tm.eval_substH hU x hx]
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
      rw [Tm.eval_substH hU x hx, Tm.eval_substH hU y hy]
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
    rw [Tm.eval_substH hU x hx, Tm.eval_substH hU y hy, Tm.eval_substH hU z hz]
    exact Op3.eval_any o _ _ _ _ _

theorem Rhs.eval_substH (hU : U.apply σ₀ = .ok σ₁) :
    {t : LTy} → (r : Rhs C Δ t) → {r' : Rhs C Γ t} → r.substH U.held U.envOnly = some r' →
      r'.eval σ₀ = r.eval σ₁
  | _, .val t, r', h => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Tm.eval_substH hU t ht
  | _, .path p, r', h => by
    obtain ⟨p', hp, rfl⟩ := Option.map_eq_some_iff.1 h
    show (do pure (some (← p'.eval σ₀))) = (do pure (some (← p.eval σ₁)))
    rw [Tm.eval_substH hU p hp]
  | _, .unset, r', h => by cases h; rfl
  | _, .mref i, r', h => by
    obtain ⟨i', hi, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Tm.eval_substH hU i hi
  | _, .store x, r', h => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    show (do pure (← x'.eval σ₀).storage) = (do pure (← x.eval σ₁).storage)
    rw [Tm.eval_substH hU x hx]
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

theorem UpdElem.write_substH (hU : U.apply σ₀ = .ok σ₁) {Ε : Ctx} (e : UpdElem C Δ Ε)
    {e' : UpdElem C Γ Ε} (h : e.substH U.held U.envOnly = some e') (τ : State C Ε) :
    e'.write σ₀ τ = e.write σ₁ τ := by
  cases e with
  | «local» i r =>
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
    show (do pure (τ.setLocal i (← r'.eval σ₀))) = (do pure (τ.setLocal i (← r.eval σ₁)))
    rw [Rhs.eval_substH hU r hr]
  | storage x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.write, Tm.eval_substH hU x hx]
  | memory x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.write, Tm.eval_substH hU x hx]
  | selfBalance op a =>
    simp only [UpdElem.substH] at h
    split at h
    · rename_i hg
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      have hgl := Upd.envOnly_glob U hg hU
      have hsb : σ₀.selfBalance = σ₁.selfBalance := by
        rw [show σ₀.selfBalance = σ₀.glob.selfBalance from rfl,
          show σ₁.selfBalance = σ₁.glob.selfBalance from rfl, hgl]
      simp only [UpdElem.write, Tm.eval_substH hU a ha, hsb]
    · cases h
  | net r op a =>
    simp only [UpdElem.substH] at h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [UpdElem.write, Tm.eval_substH hU r hr, Tm.eval_substH hU a ha]
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
      simp only [UpdElem.write, Tm.eval_substH hU r hr, Tm.eval_substH hU a ha, htx]
    · cases h
  | netMt r a =>
    simp only [UpdElem.substH] at h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [UpdElem.write, Tm.eval_substH hU r hr, Tm.eval_substH hU a ha]
  | setBalance a =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.write, Tm.eval_substH hU a ha]

end Sound

/-- **The grafted update runs as the two in turn.** -/
theorem Upd.apply_graft {Γ Δ₁ : Ctx} (U : Upd C Γ Δ₁) (σ₀ : State C Γ) :
    {Δ₂ : Ctx} → (V : Upd C Δ₁ Δ₂) → {W : Upd C Γ Δ₂} → U.graft U.held U.envOnly V = some W →
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
    rw [Upd.apply_graft U σ₀ V hW]
    cases hU : U.apply σ₀ with
    | error => rfl
    | ok σ₁ =>
      change (do e'.write σ₀ (← V.apply σ₁)) = (do e.write σ₁ (← V.apply σ₁))
      cases V.apply σ₁ with
      | error => rfl
      | ok τ => exact UpdElem.write_substH hU e he τ
  | _, .decl V x r, W, h => by
    simp only [Upd.graft] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    change (do let τ ← W'.apply σ₀; pure (τ.push (← r'.eval σ₀))) = _
    rw [Upd.apply_graft U σ₀ V hW]
    cases hU : U.apply σ₀ with
    | error => rfl
    | ok σ₁ =>
      change (do let τ ← V.apply σ₁; pure (τ.push (← r'.eval σ₀))) =
        (do let τ ← V.apply σ₁; pure (τ.push (← r.eval σ₁)))
      rw [Rhs.eval_substH hU r hr]
  | _, .pop V e, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    change (W'.apply σ₀).map (State.drop e) = _
    rw [Upd.apply_graft U σ₀ V hW]
    cases U.apply σ₀ <;> rfl
  | _, .drop V e, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    change (W'.apply σ₀).map (State.thin e) = _
    rw [Upd.apply_graft U σ₀ V hW]
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
  | .local i r => (r.substH (Upd.dropTop (C := C) Γ t).held true).map (.local i.there)
  | .storage x => (x.substH (Upd.dropTop (C := C) Γ t).held true).map .storage
  | .memory x => (x.substH (Upd.dropTop (C := C) Γ t).held true).map .memory
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
    (hx : x.substH (Upd.dropTop (C := C) Γ t).held true = some x') =>
      Tm.eval_substH (U := Upd.dropTop (C := C) Γ t) hD x (by rw [Upd.dropTop_envOnly]; exact hx)
  cases e with
  | «local» i r =>
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
    have := Rhs.eval_substH (U := Upd.dropTop (C := C) Γ t) hD r (by rw [Upd.dropTop_envOnly]; exact hr)
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

/-- A local's type other than `bool`: every value is one a state keeps
(`LTy.BoolOK`), so a binder over it reads the same from any state. -/
def LTy.notBool : LTy → Bool
  | .val .bool => false
  | _ => true

theorem LTy.boolOK_of_notBool : {t : LTy} → t.notBool = true → (v : t.Denote C) → LTy.BoolOK t v
  | .val .bool, h, _ => absurd h Bool.false_ne_true
  | .val .uint, _, _ | .val .int, _, _ | .alias _, _, _ | .mem _, _, _
  | .old, _, _ | .oldNet, _, _ => trivial

/-- `{U}_m {V}_m ψ` merged into `{W}_m ψ`, through the hidden binders between
the two (`U` moved under each, `Upd.lift?`). -/
def Fml.merge2 (m : Modality) : {Γ Δ : Ctx} → Upd C Γ Δ → Fml C Δ → Option (Fml C Γ)
  | _, _, U, .upd m' V ψ =>
    if m' = m ∧ U.boolB = true then (U.graft U.held U.envOnly V).map (.upd m · ψ) else none
  | _, _, U, .bind m' x t ψ =>
    if U.boolB = true ∧ t.notBool = true then
      (U.lift? (t := t)).bind fun U' => (Fml.merge2 m U' ψ).map (.bind m' x t)
    else none
  | _, _, _, _ => none

/-- Every local's type has a value a state keeps (a `bool` local's a `bool`). -/
theorem LTy.boolOK_exists : (t : LTy) → ∃ v : t.Denote C, LTy.BoolOK t v
  | .val p => ⟨PrimTy.default p, LTy.BoolOK.default p⟩
  | .alias _ => ⟨none, trivial⟩
  | .mem _ => ⟨0, trivial⟩
  | .old => ⟨[], trivial⟩
  | .oldNet => ⟨[], trivial⟩

/-- `sequentialToParallel` on the updates at positions `k` and `k + 1` of
the line's update spine, under its quantifiers and hidden binders. -/
def Fml.mergeAt {Γ : Ctx} : Nat → Fml C Γ → Option (Fml C Γ)
  | k, .all x p φ => (Fml.mergeAt k φ).map (.all x p)
  | k, .bind m x t φ => (Fml.mergeAt k φ).map (.bind m x t)
  | 0, .upd m U φ => Fml.merge2 m U φ
  | k + 1, .upd m U φ => (Fml.mergeAt k φ).map (.upd m U)
  | _, _ => none

/-- `sequentialToParallel` `n` times at the position `k`: the `n + 1`
updates from there merged into one, the outermost pair first. -/
def Fml.mergeRun {Γ : Ctx} (k : Nat) : Nat → Fml C Γ → Option (Fml C Γ)
  | 0, φ => some φ
  | n + 1, φ => (φ.mergeAt k).bind (Fml.mergeRun k n)

/-- `φ ~[sequentialToParallel]~> ψ` on scoped lines: the `n + 1` updates
from position `k` of `φ`'s spine merge into `ψ`'s one. -/
def Fml.MergeBy {Γ : Ctx} (k n : Nat) (φ ψ : Fml C Γ) : Prop := φ.mergeRun k n = some ψ

section Leads

variable {Γ : Ctx}

/-- `{U} ∀x. ψ` from `∀x. {U↑} ψ`, `U↑` the update moved under the binder. -/
theorem Fml.upd_bind_of_lift {m m' : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} {t : LTy} {x : Var}
    {U' : Upd C (t :: Γ) (t :: Δ)} (hU' : U.lift? = some U') (hb : U.boolB = true)
    (ht : t.notBool = true) {ψ : Fml C (t :: Δ)} (σ : State C Γ)
    (hψ : m'.forallB fun v => holds (σ.push v) (.upd m U' ψ)) :
    holds σ (.upd m U (.bind m' x t ψ)) := by
  have hg : ∀ v, U'.apply (σ.push v) = (U.apply σ).map (·.push v) := fun v => Upd.apply_lift? σ v U hU'
  obtain ⟨v₀, hv₀⟩ := LTy.boolOK_exists (C := C) t
  have h₀ := Modality.forallB_all hψ v₀
  show Modality.afterT m σ.BoolOK State.BoolOK (fun σ₁ => holds σ₁ (.bind m' x t ψ)) (U.apply σ)
  cases hU : U.apply σ with
  | error e =>
    have he : U'.apply (σ.push v₀) = .error e := by rw [hg, hU]; rfl
    cases m with
    | box =>
      have h₀ : Modality.afterC .box (holds · ψ) (U'.apply (σ.push v₀)) := h₀
      rw [he] at h₀
      exact h₀
    | diamond =>
      intro hT
      have h₀ := h₀ (hT.push hv₀)
      rw [he] at h₀
      exact h₀
  | ok σ₁ =>
    have he : ∀ v, U'.apply (σ.push v) = .ok (σ₁.push v) := fun v => by rw [hg, hU]; rfl
    cases m with
    | box =>
      refine Modality.forallB_imp (fun v h => ?_) hψ
      have h : Modality.afterC .box (holds · ψ) (U'.apply (σ.push v)) := h
      rw [he v] at h
      exact h
    | diamond =>
      intro hT
      refine ⟨Upd.apply_boolOK hT U hb hU, ?_⟩
      refine Modality.forallB_imp (fun v h => ?_) hψ
      have h := h (hT.push (LTy.boolOK_of_notBool ht v))
      rw [he v] at h
      exact h.2

/-- **The merged update leads to the two.** -/
theorem Fml.merge2_leads {m : Modality} : {Γ Δ : Ctx} → (U : Upd C Γ Δ) →
    (φ : Fml C Δ) → {ψ : Fml C Γ} → Fml.merge2 m U φ = some ψ → ∀ σ, holds σ ψ → holds σ (.upd m U φ)
  | _, _, U, .upd m' V χ, ψ, h => by
    simp only [Fml.merge2] at h
    split at h
    · rename_i hc
      obtain ⟨rfl, hb⟩ := hc
      obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 h
      intro σ hψ
      have hg := Upd.apply_graft U σ V hW
      cases m' with
      | box =>
        show Modality.afterC .box _ (U.apply σ)
        have hψ : Modality.afterC .box (holds · χ) (W.apply σ) := hψ
        rw [hg] at hψ
        cases hU : U.apply σ with
        | error e => rw [hU] at hψ; exact hψ
        | ok σ₁ => rw [hU] at hψ; exact hψ
      | diamond =>
        intro hT
        have hψ := hψ hT
        rw [hg] at hψ
        cases hU : U.apply σ with
        | error e => rw [hU] at hψ; exact hψ
        | ok σ₁ =>
          rw [hU] at hψ
          exact ⟨Upd.apply_boolOK hT U hb hU, fun _ => hψ⟩
    · cases h
  | _, _, U, .bind m' x t χ, ψ, h => by
    simp only [Fml.merge2] at h
    split at h
    · rename_i hc
      obtain ⟨hb, ht⟩ := hc
      obtain ⟨U', hU', h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨χ', hχ', rfl⟩ := Option.map_eq_some_iff.1 h
      intro σ hψ
      exact Fml.upd_bind_of_lift hU' hb ht σ
        (Modality.forallB_imp (fun v h => Fml.merge2_leads U' χ hχ' _ h) hψ)
    · cases h
  | _, _, _, .tt, _, h | _, _, _, .eq .., _, h | _, _, _, .defined _, _, h | _, _, _, .not _, _, h
  | _, _, _, .and .., _, h | _, _, _, .imp .., _, h | _, _, _, .modal .., _, h
  | _, _, _, .havoc _, _, h | _, _, _, .all .., _, h | _, _, _, .anon .., _, h => nomatch h

theorem Fml.mergeAt_leads : {Γ : Ctx} → (k : Nat) → (φ : Fml C Γ) → {ψ : Fml C Γ} →
    φ.mergeAt k = some ψ → ∀ σ, holds σ ψ → holds σ φ
  | _, k, .all x p φ, ψ₀, h => by
    have h : (Fml.mergeAt k φ).map (Fml.all x p) = some ψ₀ := by rw [← h]; cases k <;> rfl
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs v hv => Fml.mergeAt_leads k φ hψ _ (hs v hv)
  | _, k, .bind m x t φ, ψ₀, h => by
    have h : (Fml.mergeAt k φ).map (Fml.bind m x t) = some ψ₀ := by rw [← h]; cases k <;> rfl
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs => Modality.forallB_imp (fun v => Fml.mergeAt_leads k φ hψ _) hs
  | _, 0, .upd m U φ, _, h => Fml.merge2_leads U φ h
  | _, k + 1, .upd m U φ, _, h => by
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs => Modality.afterT_and hs hs fun τ a _ => Fml.mergeAt_leads k φ hψ τ a
  | _, k, .tt, _, h | _, k, .eq .., _, h | _, k, .defined _, _, h | _, k, .not _, _, h
  | _, k, .and .., _, h | _, k, .imp .., _, h | _, k, .modal .., _, h | _, k, .havoc _, _, h
  | _, k, .anon .., _, h => by
    cases k <;> cases h

theorem Fml.mergeRun_leads (k : Nat) : (n : Nat) → (φ : Fml C Γ) → {ψ : Fml C Γ} →
    φ.mergeRun k n = some ψ → ∀ σ, holds σ ψ → holds σ φ
  | 0, φ, _, h => by cases h; exact fun _ h => h
  | n + 1, φ, _, h => by
    obtain ⟨χ, hχ, h⟩ := Option.bind_eq_some_iff.1 h
    exact fun σ hψ => Fml.mergeAt_leads k φ hχ σ (Fml.mergeRun_leads k n χ h σ hψ)

end Leads

end Solidity.Core
