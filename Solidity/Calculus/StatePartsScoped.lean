import Solidity.Calculus.UpdRuleScoped
import Solidity.Calculus.StateFacts

/-!
# Merges over a storage or memory write, on scoped updates

Two merges on `Upd C Γ Δ`, where
`Upd.seqPar` (`Calculus/Graft.lean`) refuses them: it reads `V` in `U`'s
state exactly, so a symbol of `V` that reads a global part `U` writes is
refused, but `storage` after a storage write.

* `{L ‖ storage := S}{V}`, `L` locals (`Upd.stOnly`, `Upd.lastSt`), is
  `{L ‖ storage := S ‖ V[L, S/storage]}` (`Upd.mergeSt?`): the locals and
  `storage` substituted in one pass (`Tm.substStS`), memory reads
  included, and a push slot `p[p.length]` or an index check `p[i]`, which
  read the storage of the state they run in, carried over as
  `p[p.length]@S` and `p[i]@S` (`nextIn`, `atIn`).  A storage variable
  `U` sets (`old := s`) reads `s`, as the erased form substitutes it.
* `{memory := M}{V}` is `{memory := M ‖ V[M/memory]}` (`Upd.mergeMem?`,
  `Tm.withMemS`).

Both are read where a write looks (`Srt.AgreePart`, the erased form's): a
storage term read before the write and after it return states of one
storage, a memory term of one heap, which is all an element writes.  The
grafts share one shape (`Upd.graftF`: `U`'s elements, then `V`'s, each
right-hand side mapped by a term map), whose run is `U`'s then `V`'s where
the map reads each term where a write looks (`GraftOK`,
`Upd.apply_graftF`); each merge gives the two updates in turn under one
modality (`holds_upd_mergeSt`, `holds_upd_mergeMem`), one way, as
`Calculus/UpdRuleScoped.lean`'s rules.

Gate G0's first two conditions hold as in `Calculus/UpdRuleScoped.lean`:
the walk over `V` (`Upd.graftF`) is the recursor, its `match` twin
`Upd.graftFM` linked by `Upd.graftF_eq_graftFM`; a head is read by
`Upd.casesOn` (`Upd.mergeMem?`) or `Fml.updHead?` (`MergeNameS.top`), and
`match` stays on one `Tm`, `Rhs` or `UpdElem`, whose context is a
parameter (`Tm` and `Rhs` are indexed by a sort or type only, `UpdElem`
not at all), so no cast compares contexts.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)
open Semantics (Res)

variable {C : Contract}

theorem Srt.AgreePart.refl : (s : Srt) → (x : s.Ev) → Srt.AgreePart s x x
  | .st, _ => ⟨rfl⟩
  | .mem, _ => ⟨rfl⟩
  | .val, _ | .path, _ | .sv, _ | .ident, _ | .addr, _ | .mv, _ => rfl

/-! ## An update grafted through a term map -/

section GraftF

variable {Γ Δ : Ctx} (F : {k : Srt} → Tm C Δ k → Option (Tm C Γ k))

/-- A right-hand side of `Δ` read in `Γ` through `F`. -/
def Rhs.mapF : {t : LTy} → Rhs C Δ t → Option (Rhs C Γ t)
  | _, .val t => (F t).map .val
  | _, .path p => (F p).map .path
  | _, .unset => some .unset
  | _, .mref i => (F i).map .mref
  | _, .store x => (F x).map .store
  | _, .saveNet => some .saveNet
  | _, .saveNetMt => some .saveNetMt

/-- An element whose right-hand sides are read in `Δ`, read in `Γ` through `F`. -/
def UpdElem.mapF {Ε : Ctx} : UpdElem C Δ Ε → Option (UpdElem C Γ Ε)
  | .local i r => (r.mapF F).map (.local i)
  | .storage x => (F x).map .storage
  | .memory m => (F m).map .memory
  | .selfBalance op a => (F a).map (.selfBalance op)
  | .net r op a => do pure (.net (← F r) op (← F a))
  | .pay r a => do pure (.pay (← F r) (← F a))
  | .netMt r a => do pure (.netMt (← F r) (← F a))
  | .setBalance a => (F a).map .setBalance

/-- `Upd.graftF`'s compiled twin. -/
def Upd.graftFM (U : Upd C Γ Δ) : {Δ₂ : Ctx} → Upd C Δ Δ₂ → Option (Upd C Γ Δ₂)
  | _, .nil => some U
  | _, .snoc V e => do pure (.snoc (← Upd.graftFM U V) (← e.mapF F))
  | _, .decl V x r => do pure (.decl (← Upd.graftFM U V) x (← r.mapF F))
  | _, .pop V h => (Upd.graftFM U V).map (.pop · h)
  | _, .drop V h => (Upd.graftFM U V).map (.drop · h)

/-- `V` after `U`, as one update from `U`'s state: `U`'s elements, then
`V`'s, each right-hand side read through `F`; by the recursor. -/
@[implemented_by Upd.graftFM]
def Upd.graftF (U : Upd C Γ Δ) {Δ₂ : Ctx} (V : Upd C Δ Δ₂) : Option (Upd C Γ Δ₂) :=
  Upd.rec (motive := fun Δ₂ _ => Option (Upd C Γ Δ₂)) (some U)
    (fun _ e ih => do pure (.snoc (← ih) (← e.mapF F)))
    (fun _ x r ih => do pure (.decl (← ih) x (← r.mapF F)))
    (fun _ h ih => ih.map (.pop · h)) (fun _ h ih => ih.map (.drop · h)) V

theorem Upd.graftF_eq_graftFM (U : Upd C Γ Δ) {Δ₂ : Ctx} (V : Upd C Δ Δ₂) :
    U.graftF F V = U.graftFM F V := by
  induction V with
  | nil => rfl
  | snoc V e ih | decl V x r ih | pop V h ih | drop V h ih =>
    simp only [Upd.graftFM, ← ih]; rfl

end GraftF

/-- `F` reads a term of the state after an update (`σ₁`) in the state
before it (`σ₀`), where a write looks; the update keeps the ledger, the
funds and the transaction. -/
structure GraftOK {Γ Δ : Ctx} (σ₀ : EState C Γ) (σ₁ : EState C Δ)
    (F : {k : Srt} → Tm C Δ k → Option (Tm C Γ k)) : Prop where
  tm : ∀ {k : Srt} (t : Tm C Δ k) {t' : Tm C Γ k}, F t = some t' →
    Srt.AgreePart k (t'.eval σ₀) (t.eval σ₁)
  net : σ₀.net = σ₁.net
  selfBalance : σ₀.selfBalance = σ₁.selfBalance
  tx : σ₀.tx = σ₁.tx

section GraftFSound

variable {Γ Δ : Ctx} {F : {k : Srt} → Tm C Δ k → Option (Tm C Γ k)} {σ₀ : EState C Γ}
  {σ₁ : EState C Δ}

theorem Rhs.eval_mapF (hF : GraftOK σ₀ σ₁ F) :
    {t : LTy} → (r : Rhs C Δ t) → {r' : Rhs C Γ t} → r.mapF F = some r' → r'.eval σ₀ = r.eval σ₁
  | _, .val t, r', h => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h
    exact hF.tm t ht
  | _, .path p, r', h => by
    obtain ⟨p', hp, rfl⟩ := Option.map_eq_some_iff.1 h
    have hp : p'.eval σ₀ = p.eval σ₁ := hF.tm p hp
    show (do pure (some (← p'.eval σ₀))) = (do pure (some (← p.eval σ₁)))
    rw [hp]
  | _, .unset, r', h => by cases h; rfl
  | _, .mref i, r', h => by
    obtain ⟨i', hi, rfl⟩ := Option.map_eq_some_iff.1 h
    have hi : i'.eval σ₀ = i.eval σ₁ := hF.tm i hi
    show (do pure (some (← i'.eval σ₀))) = (do pure (some (← i.eval σ₁)))
    rw [hi]
  | _, .store x, r', h => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    show (do pure (← x'.eval σ₀).storage) = (do pure (← x.eval σ₁).storage)
    rcases Res.stPart_cases (hF.tm x hx).eq with ⟨e, h₁, h₂⟩ | ⟨τ₁, τ₂, h₁, h₂, hs⟩
    · rw [h₁, h₂]
    · rw [h₁, h₂]; exact congrArg (fun st => (pure st : Res _)) hs
  | _, .saveNet, r', h => by cases h; show pure σ₀.net = pure σ₁.net; rw [hF.net]
  | _, .saveNetMt, r', h => by cases h; rfl

theorem UpdElem.write_mapF (hF : GraftOK σ₀ σ₁ F) {Ε : Ctx} (e : UpdElem C Δ Ε)
    {e' : UpdElem C Γ Ε} (h : e.mapF F = some e') (τ : EState C Ε) :
    e'.write σ₀ τ = e.write σ₁ τ := by
  cases e with
  | «local» i r =>
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
    show (do pure (τ.setLocal i (← r'.eval σ₀))) = (do pure (τ.setLocal i (← r.eval σ₁)))
    rw [Rhs.eval_mapF hF r hr]
  | storage x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    rcases Res.stPart_cases (hF.tm x hx).eq with ⟨e, h₁, h₂⟩ | ⟨τ₁, τ₂, h₁, h₂, hs⟩
    · simp only [UpdElem.write, h₁, h₂]
    · simp only [UpdElem.write, h₁, h₂, bind, Except.bind, hs]
  | memory x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    rcases Res.memPart_cases (hF.tm x hx).eq with ⟨e, h₁, h₂⟩ | ⟨τ₁, τ₂, h₁, h₂, hs⟩
    · simp only [UpdElem.write, h₁, h₂]
    · simp only [UpdElem.write, h₁, h₂, bind, Except.bind, hs.1, hs.2]
  | selfBalance op a =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
    have ha : a'.eval σ₀ = a.eval σ₁ := hF.tm a ha
    simp only [UpdElem.write, ha, hF.selfBalance]
  | net r op a =>
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    have hr : r'.eval σ₀ = r.eval σ₁ := hF.tm r hr
    have ha : a'.eval σ₀ = a.eval σ₁ := hF.tm a ha
    simp only [UpdElem.write, hr, ha]
  | pay r a =>
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    have hr : r'.eval σ₀ = r.eval σ₁ := hF.tm r hr
    have ha : a'.eval σ₀ = a.eval σ₁ := hF.tm a ha
    simp only [UpdElem.write, hr, ha, hF.tx]
  | netMt r a =>
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    have hr : r'.eval σ₀ = r.eval σ₁ := hF.tm r hr
    have ha : a'.eval σ₀ = a.eval σ₁ := hF.tm a ha
    simp only [UpdElem.write, hr, ha]
  | setBalance a =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
    have ha : a'.eval σ₀ = a.eval σ₁ := hF.tm a ha
    simp only [UpdElem.write, ha]

end GraftFSound

/-- The grafted update runs as the two in turn (on the twin). -/
theorem Upd.apply_graftFM {Γ Δ₁ : Ctx} {F : {k : Srt} → Tm C Δ₁ k → Option (Tm C Γ k)}
    (U : Upd C Γ Δ₁) (σ₀ : EState C Γ) (hF : ∀ σ₁, U.apply σ₀ = .ok σ₁ → GraftOK σ₀ σ₁ F) :
    {Δ₂ : Ctx} → (V : Upd C Δ₁ Δ₂) → {W : Upd C Γ Δ₂} → U.graftFM F V = some W →
      W.apply σ₀ = (U.apply σ₀ >>= V.apply)
  | _, .nil, W, h => by
    cases h
    cases U.apply σ₀ <;> rfl
  | _, .snoc V e, W, h => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    change (do e'.write σ₀ (← W'.apply σ₀)) = _
    rw [Upd.apply_graftFM U σ₀ hF V hW]
    cases hU : U.apply σ₀ with
    | error => rfl
    | ok σ₁ =>
      change (do e'.write σ₀ (← V.apply σ₁)) = (do e.write σ₁ (← V.apply σ₁))
      cases V.apply σ₁ with
      | error => rfl
      | ok τ => exact UpdElem.write_mapF (hF σ₁ hU) e he τ
  | _, .decl V x r, W, h => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    change (do let τ ← W'.apply σ₀; pure (τ.push (← r'.eval σ₀))) = _
    rw [Upd.apply_graftFM U σ₀ hF V hW]
    cases hU : U.apply σ₀ with
    | error => rfl
    | ok σ₁ =>
      change (do let τ ← V.apply σ₁; pure (τ.push (← r'.eval σ₀))) =
        (do let τ ← V.apply σ₁; pure (τ.push (← r.eval σ₁)))
      rw [Rhs.eval_mapF (hF σ₁ hU) r hr]
  | _, .pop V e, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    change (W'.apply σ₀).map (EState.drop e) = _
    rw [Upd.apply_graftFM U σ₀ hF V hW]
    cases U.apply σ₀ <;> rfl
  | _, .drop V e, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    change (W'.apply σ₀).map (EState.thin e) = _
    rw [Upd.apply_graftFM U σ₀ hF V hW]
    cases U.apply σ₀ <;> rfl

/-- **The grafted update runs as the two in turn**, where `F` reads each
term where a write looks. -/
theorem Upd.apply_graftF {Γ Δ₁ Δ₂ : Ctx} {F : {k : Srt} → Tm C Δ₁ k → Option (Tm C Γ k)}
    (U : Upd C Γ Δ₁) (σ₀ : EState C Γ) (hF : ∀ σ₁, U.apply σ₀ = .ok σ₁ → GraftOK σ₀ σ₁ F)
    (V : Upd C Δ₁ Δ₂) {W : Upd C Γ Δ₂} (h : U.graftF F V = some W) :
    W.apply σ₀ = (U.apply σ₀ >>= V.apply) :=
  Upd.apply_graftFM U σ₀ hF V (Upd.graftF_eq_graftFM F U V ▸ h)

/-! ## `{L ‖ storage := S}` substituted -/

section SubstSt

variable {Γ Δ : Ctx} (s : Subst C Γ Δ) (S : Tm C Γ .st)

/-- A term of `Δ` read in `Γ` before an update of locals and the storage:
its locals replaced by what they hold (a storage variable set to `x` by
`x`), `storage` by `S`, a push slot and an index check read in `S`'s
storage (`nextIn`, `atIn`); `none` past an unset alias or a ledger
variable the update sets. -/
def Tm.substStS : {k : Srt} → Tm C Δ k → Option (Tm C Γ k)
  | _, .pvV i => match s i with
    | .pos j => some (.pvV j)
    | .rhs (.val t) => some t
  | _, .pvP i => match s i with
    | .pos j => some (.pvP j)
    | .rhs (.path p) => some p
    | .rhs .unset => none
  | _, .pvS i => match s i with
    | .pos j => some (.pvS j)
    | .rhs (.store x) => some x
  | _, .pvI i => match s i with
    | .pos j => some (.pvI j)
    | .rhs (.mref t) => some t
  | _, .netOf i a => match s i with
    | .pos j => (Tm.substStS a).map (.netOf j)
    | .rhs _ => none
  | _, .app0 .storage => some S
  | _, .app0 o => some (.app0 o)
  | _, .app1 .next _ p => (Tm.substStS p).map (.app2 .nextIn S)
  | _, .app1 o ho x => (Tm.substStS x).map (.app1 o ho)
  | _, .app2 .«at» p i => do pure (.app3 .atIn S (← Tm.substStS p) (← Tm.substStS i))
  | _, .app2 o x y => do pure (.app2 o (← Tm.substStS x) (← Tm.substStS y))
  | _, .app3 o x y z => do pure (.app3 o (← Tm.substStS x) (← Tm.substStS y) (← Tm.substStS z))

end SubstSt

section SubstStSound

variable {Γ Δ : Ctx} {U : Upd C Γ Δ} {S : Tm C Γ .st} {σ₀ : EState C Γ} {σ₁ : EState C Δ}

theorem Tm.substStS_eval_app1 (hg : StChg σ₀.glob σ₁.glob)
    (hS : S.eval σ₀ = pure σ₁.glob) {a k : Srt} (o : Op1 a k) (ho : o.named = false) (x : Tm C Δ a)
    (ih : ∀ {x' : Tm C Γ a}, Tm.substStS U.held S x = some x' →
      Srt.AgreePart a (x'.eval σ₀) (x.eval σ₁))
    {t' : Tm C Γ k} (h : Tm.substStS U.held S (.app1 o ho x) = some t') :
    Srt.AgreePart k (t'.eval σ₀) ((Tm.app1 o ho x).eval σ₁) := by
  have hr : σ₁.glob = { σ₀.glob with storage := σ₁.glob.storage } := hg
  have hrest : σ₀.glob.Rest σ₁.glob := by rw [hr]; exact ⟨rfl, rfl, rfl⟩
  cases o with
  | next =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    have hp : x'.eval σ₀ = x.eval σ₁ := ih hx
    show Op2.eval σ₀.glob .nextIn (S.eval σ₀) (x'.eval σ₀) = Op1.eval σ₁.glob .next (x.eval σ₁)
    simp only [Op1.eval, Op2.eval, hS, hp, bind, Except.bind]
    rfl
  | _ =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Op1.eval_part hrest _ (fun _ _ => by rw [hr]; rfl) (by exact Or.inl rfl) (ih hx)

theorem Tm.substStS_eval_app2 (hS : S.eval σ₀ = pure σ₁.glob) {a b k : Srt} (o : Op2 a b k) (x : Tm C Δ a) (y : Tm C Δ b)
    (ihx : ∀ {x' : Tm C Γ a}, Tm.substStS U.held S x = some x' →
      Srt.AgreePart a (x'.eval σ₀) (x.eval σ₁))
    (ihy : ∀ {y' : Tm C Γ b}, Tm.substStS U.held S y = some y' →
      Srt.AgreePart b (y'.eval σ₀) (y.eval σ₁))
    {t' : Tm C Γ k} (h : Tm.substStS U.held S (.app2 o x y) = some t') :
    Srt.AgreePart k (t'.eval σ₀) ((Tm.app2 o x y).eval σ₁) := by
  cases o with
  | «at» =>
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    have hp : x'.eval σ₀ = x.eval σ₁ := ihx hx
    have hi : y'.eval σ₀ = y.eval σ₁ := ihy hy
    show Op3.eval σ₀.glob .atIn (S.eval σ₀) (x'.eval σ₀) (y'.eval σ₀) =
      Op2.eval σ₁.glob .«at» (x.eval σ₁) (y.eval σ₁)
    simp only [Op2.eval, Op3.eval, hS, hp, hi, bind, Except.bind]
    rfl
  | _ =>
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact Op2.eval_part _ (by exact Or.inl rfl) (ihx hx) (ihy hy)

/-- **Read before `{L ‖ storage := S}`, the substituted term reads as the
term after it**, where a write looks. -/
theorem Tm.substStS_eval (hU : U.apply σ₀ = .ok σ₁) (hg : StChg σ₀.glob σ₁.glob)
    (hS : S.eval σ₀ = pure σ₁.glob) :
    {k : Srt} → (t : Tm C Δ k) → {t' : Tm C Γ k} → Tm.substStS U.held S t = some t' →
      Srt.AgreePart k (t'.eval σ₀) (t.eval σ₁)
  | _, .pvV i, _, h => by
    simp only [Tm.substStS] at h
    exact Tm.eval_substH_pvV _ (Upd.held_ok U hU i) h
  | _, .pvP i, _, h => by
    simp only [Tm.substStS] at h
    exact Tm.eval_substH_pvP _ (Upd.held_ok U hU i) h
  | _, .pvI i, _, h => by
    simp only [Tm.substStS] at h
    exact Tm.eval_substH_pvI _ (Upd.held_ok U hU i) h
  | _, .pvS i, t', h => by
    have hx := Upd.held_ok U hU i
    have h : (match U.held i with
        | .pos j => some (Tm.pvS j) | .rhs (.store x) => some x) = some t' := h
    generalize U.held i = x at h hx
    show StPartEq _ _
    cases x with
    | pos j =>
      cases h
      have hx : Env.get i σ₁.env = Env.get j σ₀.env := hx
      exact Res.stPart_ok hx.symm
    | rhs r =>
      cases r with
      | store x =>
        cases h
        have hx : (do pure (← t'.eval σ₀).storage) = Except.ok (Env.get i σ₁.env) := hx
        cases ht : t'.eval σ₀ with
        | error e => rw [ht] at hx; cases hx
        | ok τ =>
          rw [ht] at hx
          injection hx with hτ
          exact Res.stPart_ok hτ
  | _, .netOf i a, t', h => by
    have hx := Upd.held_ok U hU i
    have h : (match U.held i with
        | .pos j => (Tm.substStS U.held S a).map (Tm.netOf j) | .rhs _ => none) = some t' := h
    generalize U.held i = x at h hx
    cases x with
    | rhs _ => cases h
    | pos j =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      have hx : Env.get i σ₁.env = Env.get j σ₀.env := hx
      have ha : a'.eval σ₀ = a.eval σ₁ := Tm.substStS_eval hU hg hS a ha
      show (do
          let l : List (Int × Int) := Env.get j σ₀.env
          pure (Semantics.Value.int ((Semantics.lookupBy (← (← a'.eval σ₀).asInt) l).getD 0))) =
        (do
          let l : List (Int × Int) := Env.get i σ₁.env
          pure (Semantics.Value.int ((Semantics.lookupBy (← (← a.eval σ₁).asInt) l).getD 0)))
      rw [ha, hx]
  | _, .app0 o, t', h => by
    have hr : σ₁.glob = { σ₀.glob with storage := σ₁.glob.storage } := hg
    cases o with
    | storage =>
      cases h
      show StPartEq _ _
      rw [hS]; exact ⟨rfl⟩
    | memory =>
      cases h
      show MemPartEq (pure σ₀.glob) (pure σ₁.glob)
      rw [hr]; exact ⟨rfl⟩
    | lit _ | root _ | env _ | mtSt _ =>
      cases h
      show Srt.AgreePart _ (Op0.eval σ₀.glob _) (Op0.eval σ₁.glob _)
      rw [hr]; exact Srt.AgreePart.refl _ _
  | _, .app1 o ho x, _, h =>
    Tm.substStS_eval_app1 hg hS o ho x (fun hx => Tm.substStS_eval hU hg hS x hx) h
  | _, .app2 o x y, _, h =>
    Tm.substStS_eval_app2 hS o x y (fun hx => Tm.substStS_eval hU hg hS x hx)
      (fun hy => Tm.substStS_eval hU hg hS y hy) h
  | _, .app3 o x y z, t', h => by
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z', hz, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact Op3.eval_part o (Tm.substStS_eval hU hg hS x hx) (Tm.substStS_eval hU hg hS y hy)
      (Tm.substStS_eval hU hg hS z hz)

end SubstStSound

/-- **`sequentialToParallel` over a storage write**: `{U}{V}` as one update
where `U` writes locals and the storage, last `S`, and no other global
part; `none` otherwise. -/
def Upd.mergeSt? {Γ Δ₁ Δ₂ : Ctx} (U : Upd C Γ Δ₁) (V : Upd C Δ₁ Δ₂) : Option (Upd C Γ Δ₂) :=
  if U.stOnly then
    match U.lastSt with
    | some S => U.graftF (Tm.substStS U.held S) V
    | none => none
  else none

/-- The storage merge runs as the two updates in turn. -/
theorem Upd.apply_mergeSt {Γ Δ₁ Δ₂ : Ctx} (U : Upd C Γ Δ₁) (V : Upd C Δ₁ Δ₂)
    {W : Upd C Γ Δ₂} (h : U.mergeSt? V = some W) (σ₀ : EState C Γ) :
    W.apply σ₀ = (U.apply σ₀ >>= V.apply) := by
  unfold Upd.mergeSt? at h
  split at h
  · rename_i hst
    split at h
    · rename_i S hS
      refine Upd.apply_graftF U σ₀ (fun σ₁ hU => ?_) V h
      have hg : StChg σ₀.glob σ₁.glob := Upd.stOnly_glob U hst hU
      have hSe : S.eval σ₀ = pure σ₁.glob := Upd.lastSt_eval U hU S hS
      have hr : σ₁.glob = { σ₀.glob with storage := σ₁.glob.storage } := hg
      exact ⟨fun t _ ht => Tm.substStS_eval hU hg hSe t ht,
        congrArg (·.net) hr.symm, congrArg (·.selfBalance) hr.symm, congrArg (·.tx) hr.symm⟩
    · cases h
  · cases h

/-- `{W} φ` gives `{U}{V} φ` for the storage merge `W`. -/
theorem holds_upd_mergeSt {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} (hW : U.mergeSt? V = some W) {φ : Fml C Δ₂} (σ : State C Γ)
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) :=
  holds_upd_of_apply σ (Upd.apply_mergeSt U V hW σ.erase) h

/-! ## `{memory := M}` substituted -/

section WithMem

variable {Γ : Ctx} (M : Tm C Γ .mem)

/-- `{memory := M}e`: `M` for every `memory` in `e`. -/
def Tm.withMemS : {k : Srt} → Tm C Γ k → Tm C Γ k
  | _, .pvV i => .pvV i
  | _, .pvP i => .pvP i
  | _, .pvS i => .pvS i
  | _, .pvI i => .pvI i
  | _, .netOf i a => .netOf i (Tm.withMemS a)
  | _, .app0 .memory => M
  | _, .app0 o => .app0 o
  | _, .app1 o ho x => .app1 o ho (Tm.withMemS x)
  | _, .app2 o x y => .app2 o (Tm.withMemS x) (Tm.withMemS y)
  | _, .app3 o x y z => .app3 o (Tm.withMemS x) (Tm.withMemS y) (Tm.withMemS z)

end WithMem

section WithMemSound

variable {Γ : Ctx} {M : Tm C Γ .mem} {σ₀ : EState C Γ} {μ : Semantics.State}

/-- **Read before `{memory := M}`, the substituted term reads as the term
after it**, where a write looks: the state after has the storage and the
locals of the state before, and the heap `M` leaves. -/
theorem Tm.withMemS_eval (hM : M.eval σ₀ = .ok μ) :
    {k : Srt} → (t : Tm C Γ k) → Srt.AgreePart k ((Tm.withMemS M t).eval σ₀)
      (t.eval (σ₀.withGlob { σ₀.glob with heap := μ.heap, nextId := μ.nextId }))
  | _, .pvV _ => rfl
  | _, .pvP _ => rfl
  | _, .pvI _ => rfl
  | _, .pvS _ => ⟨rfl⟩
  | _, .netOf i a => by
    have ha : (Tm.withMemS M a).eval σ₀ =
        a.eval (σ₀.withGlob { σ₀.glob with heap := μ.heap, nextId := μ.nextId }) :=
      Tm.withMemS_eval hM a
    show (do
        let l : List (Int × Int) := Env.get i σ₀.env
        pure (Semantics.Value.int ((Semantics.lookupBy (← (← (Tm.withMemS M a).eval σ₀).asInt) l).getD 0))) =
      (do
        let l : List (Int × Int) := Env.get i σ₀.env
        pure (Semantics.Value.int ((Semantics.lookupBy
          (← (← a.eval (σ₀.withGlob { σ₀.glob with heap := μ.heap, nextId := μ.nextId })).asInt)
          l).getD 0)))
    rw [ha]
  | _, .app0 o => by
    cases o with
    | memory =>
      show MemPartEq (M.eval σ₀) _
      rw [hM]; exact ⟨rfl⟩
    | storage | mtSt _ => exact ⟨rfl⟩
    | lit _ | root _ | env _ => exact Srt.AgreePart.refl _ _
  | _, .app1 o _ x =>
    Op1.eval_part ⟨rfl, rfl, rfl⟩ o (fun _ _ => rfl) (Or.inr rfl) (Tm.withMemS_eval hM x)
  | _, .app2 o x y =>
    Op2.eval_part o (Or.inr rfl) (Tm.withMemS_eval hM x) (Tm.withMemS_eval hM y)
  | _, .app3 o x y z =>
    Op3.eval_part o (Tm.withMemS_eval hM x) (Tm.withMemS_eval hM y) (Tm.withMemS_eval hM z)

end WithMemSound

/-- **`sequentialToParallel` over a memory write**: `{memory := M}{V}` as
one update, `M` substituted for `memory` in `V`; `none` for any other `U`. -/
def Upd.mergeMem? {Γ Δ₁ Δ₂ : Ctx} (U : Upd C Γ Δ₁) (V : Upd C Δ₁ Δ₂) : Option (Upd C Γ Δ₂) :=
  Upd.casesOn (motive := fun Δ₁ _ => Upd C Δ₁ Δ₂ → Option (Upd C Γ Δ₂)) U
    (nil := fun _ => none)
    (snoc := fun U e V =>
      Upd.casesOn (motive := fun Δ₁ _ => UpdElem C Γ Δ₁ → Upd C Δ₁ Δ₂ → Option (Upd C Γ Δ₂)) U
        (nil := fun e V => match e with
          | .memory M => (Upd.snoc .nil (.memory M)).graftF (fun t => some (Tm.withMemS M t)) V
          | _ => none)
        (snoc := fun _ _ _ _ => none) (decl := fun _ _ _ _ _ => none)
        (pop := fun _ _ _ _ => none) (drop := fun _ _ _ _ => none) e V)
    (decl := fun _ _ _ _ => none) (pop := fun _ _ _ => none) (drop := fun _ _ _ => none) V

/-- The memory merge runs as the two updates in turn. -/
theorem Upd.apply_mergeMem {Γ Δ₁ Δ₂ : Ctx} (U : Upd C Γ Δ₁) (V : Upd C Δ₁ Δ₂)
    {W : Upd C Γ Δ₂} (h : U.mergeMem? V = some W) (σ₀ : EState C Γ) :
    W.apply σ₀ = (U.apply σ₀ >>= V.apply) := by
  cases U with
  | snoc U e =>
    cases U with
    | nil =>
      cases e with
      | memory M =>
        refine Upd.apply_graftF _ σ₀ (fun σ₁ hU => ?_) _ h
        change (do UpdElem.write σ₀ (.memory M) σ₀) = .ok σ₁ at hU
        change (do
          let μ ← M.eval σ₀
          pure (σ₀.withGlob { σ₀.glob with heap := μ.heap, nextId := μ.nextId })) = .ok σ₁ at hU
        cases hM : M.eval σ₀ with
        | error => rw [hM] at hU; cases hU
        | ok μ =>
          rw [hM] at hU; cases hU
          exact ⟨fun t _ ht => by cases ht; exact Tm.withMemS_eval hM t, rfl, rfl, rfl⟩
      | _ => cases h
    | _ => cases h
  | _ => cases h

/-- `{W} φ` gives `{memory := M}{V} φ` for the memory merge `W`. -/
theorem holds_upd_mergeMem {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} (hW : U.mergeMem? V = some W) {φ : Fml C Δ₂} (σ : State C Γ)
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) :=
  holds_upd_of_apply σ (Upd.apply_mergeMem U V hW σ.erase) h

/-! ## `{L ‖ memory := M}` substituted

The locals-then-memory merge (`Upd.mergeMemL?`): `U` an update of locals with a memory write last, `{L ‖ memory := M}{V}` is
`{L ‖ memory := M ‖ V[L, M/memory]}`, the locals `L` leaves and `memory`
substituted in one pass (`Tm.substMemS`), read where a write looks. -/

section SubstMem

variable {Γ Δ : Ctx} (s : Subst C Γ Δ) (M : Tm C Γ .mem)

/-- A term of `Δ` read in `Γ` before an update of locals and a memory
write: its locals replaced by what they hold, `memory` by `M`; `none`
past an unset alias or a ledger variable the update sets. -/
def Tm.substMemS : {k : Srt} → Tm C Δ k → Option (Tm C Γ k)
  | _, .pvV i => match s i with
    | .pos j => some (.pvV j)
    | .rhs (.val t) => some t
  | _, .pvP i => match s i with
    | .pos j => some (.pvP j)
    | .rhs (.path p) => some p
    | .rhs .unset => none
  | _, .pvS i => match s i with
    | .pos j => some (.pvS j)
    | .rhs (.store x) => some x
  | _, .pvI i => match s i with
    | .pos j => some (.pvI j)
    | .rhs (.mref t) => some t
  | _, .netOf i a => match s i with
    | .pos j => (Tm.substMemS a).map (.netOf j)
    | .rhs _ => none
  | _, .app0 .memory => some M
  | _, .app0 o => some (.app0 o)
  | _, .app1 o ho x => (Tm.substMemS x).map (.app1 o ho)
  | _, .app2 o x y => do pure (.app2 o (← Tm.substMemS x) (← Tm.substMemS y))
  | _, .app3 o x y z => do pure (.app3 o (← Tm.substMemS x) (← Tm.substMemS y) (← Tm.substMemS z))

/-- The memory an update of locals writes last, its locals before it:
`{L ‖ memory := M}`, `L` an update of locals (`Upd.envOnly`); `none` for
any other update (`Upd.casesOn`). -/
def Upd.memLast? (U : Upd C Γ Δ) : Option (Tm C Γ .mem) :=
  Upd.casesOn (motive := fun _ _ => Option (Tm C Γ .mem)) U (nil := none)
    (snoc := fun L e => match e with
      | .memory M => if L.envOnly then some M else none
      | _ => none)
    (decl := fun _ _ _ => none) (pop := fun _ _ => none) (drop := fun _ _ => none)

end SubstMem

section SubstMemSound

variable {Γ Δ : Ctx} {U : Upd C Γ Δ} {M : Tm C Γ .mem} {σ₀ : EState C Γ} {σ₁ : EState C Δ}
  {μ : Semantics.State}

/-- After `{L ‖ memory := M}` the global part is the one before with the
heap `M` leaves. -/
theorem Upd.memLast?_glob (hm : U.memLast? = some M) (hU : U.apply σ₀ = .ok σ₁) :
    ∃ μ : Semantics.State, M.eval σ₀ = .ok μ ∧
      σ₁.glob = { σ₀.glob with heap := μ.heap, nextId := μ.nextId } := by
  cases U with
  | snoc L e =>
    cases e with
    | memory M' =>
      change (if L.envOnly then some M' else none) = some M at hm
      split at hm
      · rename_i hL
        cases hm
        obtain ⟨τ, hτ, h⟩ := Semantics.bind_ok_inv hU
        obtain ⟨μ, hμ, h⟩ := Semantics.bind_ok_inv h
        cases h
        refine ⟨μ, hμ, ?_⟩
        show { τ.glob with heap := μ.heap, nextId := μ.nextId } = _
        rw [Upd.envOnly_glob L hL hτ]
      · cases hm
    | _ => cases hm
  | _ => cases hm

theorem Tm.substMemS_eval (hU : U.apply σ₀ = .ok σ₁)
    (hg : σ₁.glob = { σ₀.glob with heap := μ.heap, nextId := μ.nextId })
    (hM : M.eval σ₀ = .ok μ) :
    {k : Srt} → (t : Tm C Δ k) → {t' : Tm C Γ k} → Tm.substMemS U.held M t = some t' →
      Srt.AgreePart k (t'.eval σ₀) (t.eval σ₁)
  | _, .pvV i, _, h => by
    simp only [Tm.substMemS] at h
    exact Tm.eval_substH_pvV _ (Upd.held_ok U hU i) h
  | _, .pvP i, _, h => by
    simp only [Tm.substMemS] at h
    exact Tm.eval_substH_pvP _ (Upd.held_ok U hU i) h
  | _, .pvI i, _, h => by
    simp only [Tm.substMemS] at h
    exact Tm.eval_substH_pvI _ (Upd.held_ok U hU i) h
  | _, .pvS i, t', h => by
    have hx := Upd.held_ok U hU i
    have h : (match U.held i with
        | .pos j => some (Tm.pvS j) | .rhs (.store x) => some x) = some t' := h
    generalize U.held i = x at h hx
    show StPartEq _ _
    cases x with
    | pos j =>
      cases h
      have hx : Env.get i σ₁.env = Env.get j σ₀.env := hx
      exact Res.stPart_ok hx.symm
    | rhs r =>
      cases r with
      | store x =>
        cases h
        have hx : (do pure (← t'.eval σ₀).storage) = Except.ok (Env.get i σ₁.env) := hx
        cases ht : t'.eval σ₀ with
        | error e => rw [ht] at hx; cases hx
        | ok τ =>
          rw [ht] at hx
          injection hx with hτ
          exact Res.stPart_ok hτ
  | _, .netOf i a, t', h => by
    have hx := Upd.held_ok U hU i
    have h : (match U.held i with
        | .pos j => (Tm.substMemS U.held M a).map (Tm.netOf j) | .rhs _ => none) = some t' := h
    generalize U.held i = x at h hx
    cases x with
    | rhs _ => cases h
    | pos j =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      have hx : Env.get i σ₁.env = Env.get j σ₀.env := hx
      have ha : a'.eval σ₀ = a.eval σ₁ := Tm.substMemS_eval hU hg hM a ha
      show (do
          let l : List (Int × Int) := Env.get j σ₀.env
          pure (Semantics.Value.int ((Semantics.lookupBy (← (← a'.eval σ₀).asInt) l).getD 0))) =
        (do
          let l : List (Int × Int) := Env.get i σ₁.env
          pure (Semantics.Value.int ((Semantics.lookupBy (← (← a.eval σ₁).asInt) l).getD 0)))
      rw [ha, hx]
  | _, .app0 o, t', h => by
    cases o with
    | memory =>
      cases h
      show MemPartEq (M.eval σ₀) (pure σ₁.glob)
      rw [hM, hg]; exact ⟨rfl⟩
    | storage =>
      cases h
      show StPartEq (pure σ₀.glob) (pure σ₁.glob)
      rw [hg]; exact ⟨rfl⟩
    | mtSt _ =>
      cases h
      show Srt.AgreePart _ (Op0.eval σ₀.glob _) (Op0.eval σ₁.glob _)
      rw [hg]; exact ⟨rfl⟩
    | lit _ | root _ | env _ =>
      cases h
      show Srt.AgreePart _ (Op0.eval σ₀.glob _) (Op0.eval σ₁.glob _)
      rw [hg]; exact Srt.AgreePart.refl _ _
  | _, .app1 o ho x, t', h => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    have hrest : σ₀.glob.Rest σ₁.glob := by rw [hg]; exact ⟨rfl, rfl, rfl⟩
    exact Op1.eval_part hrest o (fun _ _ => by rw [hg]; rfl) (Or.inr (by rw [hg]))
      (Tm.substMemS_eval hU hg hM x hx)
  | _, .app2 o x y, t', h => by
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact Op2.eval_part o (Or.inr (by rw [hg])) (Tm.substMemS_eval hU hg hM x hx)
      (Tm.substMemS_eval hU hg hM y hy)
  | _, .app3 o x y z, t', h => by
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z', hz, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact Op3.eval_part o (Tm.substMemS_eval hU hg hM x hx) (Tm.substMemS_eval hU hg hM y hy)
      (Tm.substMemS_eval hU hg hM z hz)

end SubstMemSound

/-- **`sequentialToParallel` over locals and a memory write**:
`{L ‖ memory := M}{V}` as one update (`Tm.substMemS`); `none` for any
other `U`. -/
def Upd.mergeMemL? {Γ Δ₁ Δ₂ : Ctx} (U : Upd C Γ Δ₁) (V : Upd C Δ₁ Δ₂) : Option (Upd C Γ Δ₂) :=
  match U.memLast? with
  | some M => U.graftF (Tm.substMemS U.held M) V
  | none => none

/-- The locals-then-memory merge runs as the two updates in turn. -/
theorem Upd.apply_mergeMemL {Γ Δ₁ Δ₂ : Ctx} (U : Upd C Γ Δ₁) (V : Upd C Δ₁ Δ₂)
    {W : Upd C Γ Δ₂} (h : U.mergeMemL? V = some W) (σ₀ : EState C Γ) :
    W.apply σ₀ = (U.apply σ₀ >>= V.apply) := by
  unfold Upd.mergeMemL? at h
  split at h
  · rename_i M hm
    refine Upd.apply_graftF U σ₀ (fun σ₁ hU => ?_) V h
    obtain ⟨μ, hM, hg⟩ := Upd.memLast?_glob hm hU
    exact ⟨fun t _ ht => Tm.substMemS_eval hU hg hM t ht,
      congrArg (·.net) hg.symm, congrArg (·.selfBalance) hg.symm, congrArg (·.tx) hg.symm⟩
  · cases h

/-- `{W} φ` gives `{L ‖ memory := M}{V} φ` for the merge `W`. -/
theorem holds_upd_mergeMemL {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} (hW : U.mergeMemL? V = some W) {φ : Fml C Δ₂} (σ : State C Γ)
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) :=
  holds_upd_of_apply σ (Upd.apply_mergeMemL U V hW σ.erase) h

/-! ## The merges at a position -/

/-- The merges, by the write they merge over. -/
inductive MergeNameS where
  | storage
  | memory
  /-- Locals, then a memory write (`Upd.mergeMemL?`). -/
  | localsMemory
  deriving DecidableEq, Repr

/-- Merge `r` on `{U}{V} ψ` under one modality. -/
def MergeNameS.top (r : MergeNameS) {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) :
    Option (Fml C Γ) :=
  match φ.updHead? with
  | some ⟨m', V, ψ⟩ =>
    if m' = m then
      (match r with
        | .storage => U.mergeSt? V
        | .memory => U.mergeMem? V
        | .localsMemory => U.mergeMemL? V).map fun W => .upd m W ψ
    else none
  | none => none

theorem MergeNameS.top_sound (r : MergeNameS) : UpdRw.Sound (C := C) fun m U φ => r.top m U φ := by
  intro Γ Δ m U φ ψ h σ hψ
  cases φ with
  | upd m' V ψ' =>
    change (if m' = m then
      (match r with
        | .storage => U.mergeSt? V
        | .memory => U.mergeMem? V
        | .localsMemory => U.mergeMemL? V).map fun W => Fml.upd m W ψ'
    else none) = some ψ at h
    split at h
    · rename_i hm; subst hm
      obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 h
      cases r with
      | storage => exact holds_upd_mergeSt hW σ hψ
      | memory => exact holds_upd_mergeMem hW σ hψ
      | localsMemory => exact holds_upd_mergeMemL hW σ hψ
    · cases h
  | _ => cases h

/-- Merge `r` at the first update where it fits (`Fml.rwAtS`). -/
def Fml.mergeAtS (r : MergeNameS) {Γ : Ctx} (φ : Fml C Γ) : Option (Fml C Γ) :=
  φ.rwAtS fun m U ψ => r.top m U ψ

/-- A merge where it fits first gives a formula that gives the original. -/
theorem Fml.mergeAtS_sound {r : MergeNameS} {Γ : Ctx} (φ : Fml C Γ) {ψ : Fml C Γ}
    (h : φ.mergeAtS r = some ψ) (σ : State C Γ) (hψ : holds σ ψ) : holds σ φ :=
  Fml.rwAtS_sound r.top_sound φ h σ hψ

/-- A scoped formula is valid where a merge of it is. -/
theorem Valid.of_mergeAtS {r : MergeNameS} {φ ψ : Fml C []} (hr : φ.mergeAtS r = some ψ)
    (h : Valid ψ) : Valid φ :=
  fun σ => Fml.mergeAtS_sound φ hr σ (h σ)

end Solidity
