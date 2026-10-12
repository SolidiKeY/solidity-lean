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
storage term read before the write and in a typed state it lands on return
states of one storage, a memory term of one heap, which is all an element
writes.  The grafts share one shape (`Upd.graftF`: `U`'s elements, then
`V`'s, each right-hand side mapped by a term map), which gives `U` then `V`
where the map reads each term where a write looks (`GraftOK`,
`holds_upd_graftF`: `Upd.afterT_seq`, `Calculus/Lands.lean`); each merge
gives the two updates in turn under one modality (`holds_upd_mergeSt`,
`holds_upd_mergeMem`), one way, as `Calculus/UpdRuleScoped.lean`'s rules.

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

/-- `F` reads a term of a typed state an update lands on (`σ₁`) in the
state before it (`σ₀`), where a write looks; the update keeps the ledger,
the funds and the transaction. -/
structure GraftOK {Γ Δ : Ctx} (σ₀ : State C Γ) (σ₁ : State C Δ)
    (F : {k : Srt} → Tm C Δ k → Option (Tm C Γ k)) : Prop where
  tm : ∀ {k : Srt} (t : Tm C Δ k) {t' : Tm C Γ k}, F t = some t' →
    Srt.AgreePart k (t'.evalT σ₀) (t.evalT σ₁)
  rest : σ₀.globE.Rest σ₁.globE

section GraftFSound

variable {Γ Δ : Ctx} {F : {k : Srt} → Tm C Δ k → Option (Tm C Γ k)} {σ₀ : State C Γ}
  {σ₁ : State C Δ}

theorem Rhs.evalT_mapF (hF : GraftOK σ₀ σ₁ F) :
    {t : LTy} → (r : Rhs C Δ t) → {r' : Rhs C Γ t} → r.mapF F = some r' →
      r'.evalT σ₀ = r.evalT σ₁
  | _, .val t, r', h => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h
    exact hF.tm t ht
  | _, .path p, r', h => by
    obtain ⟨p', hp, rfl⟩ := Option.map_eq_some_iff.1 h
    have hp : p'.evalT σ₀ = p.evalT σ₁ := hF.tm p hp
    show (do pure (some (← p'.evalT σ₀))) = (do pure (some (← p.evalT σ₁)))
    rw [hp]
  | _, .unset, r', h => by cases h; rfl
  | _, .mref i, r', h => by
    obtain ⟨i', hi, rfl⟩ := Option.map_eq_some_iff.1 h
    have hi : i'.evalT σ₀ = i.evalT σ₁ := hF.tm i hi
    show (do pure (some (← i'.evalT σ₀))) = (do pure (some (← i.evalT σ₁)))
    rw [hi]
  | _, .store x, r', h => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    show (do pure (← x'.evalT σ₀).storage) = (do pure (← x.evalT σ₁).storage)
    rcases Res.stPart_cases (hF.tm x hx).eq with ⟨e, h₁, h₂⟩ | ⟨τ₁, τ₂, h₁, h₂, hs⟩
    · rw [h₁, h₂]
    · rw [h₁, h₂]; exact congrArg (fun st => (pure st : Res _)) hs
  | _, .saveNet, r', h => by
    cases h; show pure σ₀.net = pure σ₁.net
    have hn : σ₀.globE.net = σ₁.globE.net := hF.rest.net
    exact congrArg pure hn
  | _, .saveNetMt, r', h => by cases h; rfl

theorem UpdElem.globT_mapF (hF : GraftOK σ₀ σ₁ F) {Ε : Ctx} (e : UpdElem C Δ Ε)
    {e' : UpdElem C Γ Ε} (h : e.mapF F = some e') (G : Semantics.State) :
    e'.globT σ₀ G = e.globT σ₁ G := by
  cases e with
  | «local» i r =>
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.globT, Rhs.evalT_mapF hF r hr]
  | storage x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    rcases Res.stPart_cases (hF.tm x hx).eq with ⟨e, h₁, h₂⟩ | ⟨τ₁, τ₂, h₁, h₂, hs⟩
    · simp only [UpdElem.globT, h₁, h₂]
    · simp only [UpdElem.globT, h₁, h₂, bind, Except.bind, hs]
  | memory x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    rcases Res.memPart_cases (hF.tm x hx).eq with ⟨e, h₁, h₂⟩ | ⟨τ₁, τ₂, h₁, h₂, hs⟩
    · simp only [UpdElem.globT, h₁, h₂]
    · simp only [UpdElem.globT, h₁, h₂, bind, Except.bind, hs.1, hs.2]
  | selfBalance op a =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
    have ha : a'.evalT σ₀ = a.evalT σ₁ := hF.tm a ha
    simp only [UpdElem.globT, ha, hF.rest.selfBalance]
  | net r op a =>
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    have hr : r'.evalT σ₀ = r.evalT σ₁ := hF.tm r hr
    have ha : a'.evalT σ₀ = a.evalT σ₁ := hF.tm a ha
    simp only [UpdElem.globT, hr, ha]
  | pay r a =>
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    have hr : r'.evalT σ₀ = r.evalT σ₁ := hF.tm r hr
    have ha : a'.evalT σ₀ = a.evalT σ₁ := hF.tm a ha
    simp only [UpdElem.globT, hr, ha, hF.rest.tx]
  | netMt r a =>
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    have hr : r'.evalT σ₀ = r.evalT σ₁ := hF.tm r hr
    have ha : a'.evalT σ₀ = a.evalT σ₁ := hF.tm a ha
    simp only [UpdElem.globT, hr, ha]
  | setBalance a =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
    have ha : a'.evalT σ₀ = a.evalT σ₁ := hF.tm a ha
    simp only [UpdElem.globT, ha]

end GraftFSound

section GraftFT

variable {Γ Δ₁ : Ctx} {F : {k : Srt} → Tm C Δ₁ k → Option (Tm C Γ k)} {σ₀ : State C Γ}
  {U : Upd C Γ Δ₁}

/-- The grafted update halts where `U` does (on the twin). -/
theorem Upd.globT_graftFM_error {e : Semantics.Halt} (hU : U.globT σ₀ = .error e) :
    {Δ₂ : Ctx} → (V : Upd C Δ₁ Δ₂) → {W : Upd C Γ Δ₂} → U.graftFM F V = some W →
      W.globT σ₀ = .error e
  | _, .nil, W, h => by cases h; exact hU
  | _, .snoc V e', W, h => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e'', -, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [Upd.globT, Upd.globT_graftFM_error hU V hW]
    rfl
  | _, .decl V x r, W, h => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', -, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [Upd.globT, Upd.globT_graftFM_error hU V hW]
    rfl
  | _, .pop V _, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.globT_graftFM_error hU V hW
  | _, .drop V _, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.globT_graftFM_error hU V hW

variable {σ₁ : State C Δ₁} {g₁ : Semantics.State}

/-- **The grafted update computes the global part `V` does** in a typed
state `U` lands on (on the twin). -/
theorem Upd.globT_graftFM (hL : U.Lands σ₀ g₁ σ₁) (hF : GraftOK σ₀ σ₁ F) :
    {Δ₂ : Ctx} → (V : Upd C Δ₁ Δ₂) → {W : Upd C Γ Δ₂} → U.graftFM F V = some W →
      W.globT σ₀ = V.globT σ₁
  | _, .nil, W, h => by
    cases h
    rw [hL.1]
    show _ = pure σ₁.globE
    rw [hL.2.1]
    rfl
  | _, .snoc V e, W, h => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [Upd.globT, Upd.globT_graftFM hL hF V hW, UpdElem.globT_mapF hF e he]
  | _, .decl V x r, W, h => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [Upd.globT, Upd.globT_graftFM hL hF V hW, Rhs.evalT_mapF hF r hr]
  | _, .pop V _, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.globT_graftFM hL hF V hW
  | _, .drop V _, W, h => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.globT_graftFM hL hF V hW

/-- **The grafted update leaves in each local what `V` does**, read in a
typed state `U` lands on (on the twin). -/
theorem Upd.held_graftFM (hL : U.Lands σ₀ g₁ σ₁) (hF : GraftOK σ₀ σ₁ F) :
    {Δ₂ : Ctx} → (V : Upd C Δ₁ Δ₂) → {W : Upd C Γ Δ₂} → U.graftFM F V = some W →
      ∀ {t : LTy} (i : Idx Δ₂ t) (v : t.Denote C), Held.OKV σ₁ v (V.held i) →
        Held.OKV σ₀ v (W.held i)
  | _, .nil, W, h, t, i, v, hv => by
    cases h
    have hi := (Held.OKT_iff_OKV σ₀ σ₁ i _).1 (hL.2.2 i)
    have hv : v = σ₁.getE i := hv
    rw [hv]
    exact hi
  | _, .snoc V e, W, h, t, i, v, hv => by
    simp only [Upd.graftFM] at h
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
        rw [Rhs.evalT_mapF hF r hr]
        exact hv
      · rename_i hki
        rw [dif_neg hki] at hv
        exact Upd.held_graftFM hL hF V hW i v hv
    | storage x | memory x | setBalance x =>
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 he
      exact Upd.held_graftFM hL hF V hW i v hv
    | selfBalance op a =>
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 he
      exact Upd.held_graftFM hL hF V hW i v hv
    | net r op a | netMt r a | pay r a =>
      simp only [UpdElem.mapF] at he
      obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 he
      obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 he
      cases he
      exact Upd.held_graftFM hL hF V hW i v hv
  | _, .decl V x r, W, h, t, i, v, hv => by
    simp only [Upd.graftFM] at h
    obtain ⟨W', hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    cases i with
    | here =>
      show r'.evalT σ₀ = .ok v
      rw [Rhs.evalT_mapF hF r hr]
      exact hv
    | there j => exact Upd.held_graftFM hL hF V hW j v hv
  | _, .pop V e, W, h, t, i, v, hv => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.held_graftFM hL hF V hW (i.ext e) v hv
  | _, .drop V e, W, h, t, i, v, hv => by
    obtain ⟨W', hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.held_graftFM hL hF V hW (i.wk e) v hv

end GraftFT

/-- **The grafted update gives the two in turn**, where `F` reads each
term where a write looks, in every typed state `U` lands on. -/
theorem holds_upd_graftF {m : Modality} {Γ Δ₁ Δ₂ : Ctx}
    {F : {k : Srt} → Tm C Δ₁ k → Option (Tm C Γ k)} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} (σ : State C Γ)
    (hF : ∀ g₁ (σ₁ : State C Δ₁), U.Lands σ g₁ σ₁ → GraftOK σ σ₁ F)
    (hW : U.graftF F V = some W) {φ : Fml C Δ₂} (h : holds σ (.upd m W φ)) :
    holds σ (.upd m U (.upd m V φ)) := by
  have hW : U.graftFM F V = some W := Upd.graftF_eq_graftFM F U V ▸ hW
  exact Upd.afterT_seq (fun e he => ⟨e, Upd.globT_graftFM_error he V hW⟩)
    (fun _ _ hL => Upd.globT_graftFM hL (hF _ _ hL) V hW)
    (fun _ _ hL => Upd.held_graftFM hL (hF _ _ hL) V hW) h

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

variable {Γ Δ : Ctx} {U : Upd C Γ Δ} {S : Tm C Γ .st} {σ₀ : State C Γ} {σ₁ : State C Δ}
  {g : Semantics.State}

theorem Tm.substStS_evalT_app1 (hg : StChg σ₀.globE σ₁.globE)
    (hS : S.evalT σ₀ = pure σ₁.globE) {a k : Srt} (o : Op1 a k) (ho : o.named = false)
    (x : Tm C Δ a)
    (ih : ∀ {x' : Tm C Γ a}, Tm.substStS U.held S x = some x' →
      Srt.AgreePart a (x'.evalT σ₀) (x.evalT σ₁))
    {t' : Tm C Γ k} (h : Tm.substStS U.held S (.app1 o ho x) = some t') :
    Srt.AgreePart k (t'.evalT σ₀) ((Tm.app1 o ho x).evalT σ₁) := by
  have hr : σ₁.globE = { σ₀.globE with storage := σ₁.globE.storage } := hg
  have hrest : σ₀.globE.Rest σ₁.globE := by rw [hr]; exact ⟨rfl, rfl, rfl⟩
  cases o with
  | next =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    have hp : x'.evalT σ₀ = x.evalT σ₁ := ih hx
    show Op2.eval σ₀.globE .nextIn (S.evalT σ₀) (x'.evalT σ₀) = Op1.eval σ₁.globE .next (x.evalT σ₁)
    simp only [Op1.eval, Op2.eval, hS, hp, bind, Except.bind]
    rfl
  | _ =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Op1.eval_part hrest _ (fun _ _ => by rw [hr]; rfl) (by exact Or.inl rfl) (ih hx)

theorem Tm.substStS_evalT_app2 (hS : S.evalT σ₀ = pure σ₁.globE) {a b k : Srt} (o : Op2 a b k)
    (x : Tm C Δ a) (y : Tm C Δ b)
    (ihx : ∀ {x' : Tm C Γ a}, Tm.substStS U.held S x = some x' →
      Srt.AgreePart a (x'.evalT σ₀) (x.evalT σ₁))
    (ihy : ∀ {y' : Tm C Γ b}, Tm.substStS U.held S y = some y' →
      Srt.AgreePart b (y'.evalT σ₀) (y.evalT σ₁))
    {t' : Tm C Γ k} (h : Tm.substStS U.held S (.app2 o x y) = some t') :
    Srt.AgreePart k (t'.evalT σ₀) ((Tm.app2 o x y).evalT σ₁) := by
  cases o with
  | «at» =>
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    have hp : x'.evalT σ₀ = x.evalT σ₁ := ihx hx
    have hi : y'.evalT σ₀ = y.evalT σ₁ := ihy hy
    show Op3.eval σ₀.globE .atIn (S.evalT σ₀) (x'.evalT σ₀) (y'.evalT σ₀) =
      Op2.eval σ₁.globE .«at» (x.evalT σ₁) (y.evalT σ₁)
    simp only [Op2.eval, Op3.eval, hS, hp, hi, bind, Except.bind]
    rfl
  | _ =>
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact Op2.eval_part _ (by exact Or.inl rfl) (ihx hx) (ihy hy)

/-- **Read before `{L ‖ storage := S}`, the substituted term reads as the
term in a typed state it lands on**, where a write looks. -/
theorem Tm.substStS_evalT (hL : U.Lands σ₀ g σ₁) (hg : StChg σ₀.globE σ₁.globE)
    (hS : S.evalT σ₀ = pure σ₁.globE) :
    {k : Srt} → (t : Tm C Δ k) → {t' : Tm C Γ k} → Tm.substStS U.held S t = some t' →
      Srt.AgreePart k (t'.evalT σ₀) (t.evalT σ₁)
  | _, .pvV i, _, h => by
    simp only [Tm.substStS] at h
    exact Tm.evalT_substH_pvV _ (hL.2.2 i) h
  | _, .pvP i, _, h => by
    simp only [Tm.substStS] at h
    exact Tm.evalT_substH_pvP _ (hL.2.2 i) h
  | _, .pvI i, _, h => by
    simp only [Tm.substStS] at h
    exact Tm.evalT_substH_pvI _ (hL.2.2 i) h
  | _, .pvS i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvS j) | .rhs (.store x) => some x) = some t' := h
    generalize U.held i = x at h hx
    show StPartEq _ _
    cases x with
    | pos j =>
      cases h
      have hx : σ₁.getE i = σ₀.getE j := hx
      exact Res.stPart_ok hx.symm
    | rhs r =>
      cases r with
      | store x =>
        cases h
        have hx : (do pure (← t'.evalT σ₀).storage) = Except.ok (σ₁.getE i) := hx
        cases ht : t'.evalT σ₀ with
        | error e => rw [ht] at hx; cases hx
        | ok τ =>
          rw [ht] at hx
          injection hx with hτ
          exact Res.stPart_ok hτ
  | _, .netOf i a, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => (Tm.substStS U.held S a).map (Tm.netOf j) | .rhs _ => none) = some t' := h
    generalize U.held i = x at h hx
    cases x with
    | rhs _ => cases h
    | pos j =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      have hx : σ₁.getE i = σ₀.getE j := hx
      have ha : a'.evalT σ₀ = a.evalT σ₁ := Tm.substStS_evalT hL hg hS a ha
      show Tm.evalT σ₀ (.netOf j a') = Tm.evalT σ₁ (.netOf i a)
      simp only [Tm.evalT, ha, hx]
  | _, .app0 o, t', h => by
    have hr : σ₁.globE = { σ₀.globE with storage := σ₁.globE.storage } := hg
    cases o with
    | storage =>
      cases h
      show StPartEq _ _
      rw [hS]; exact ⟨rfl⟩
    | memory =>
      cases h
      show MemPartEq (pure σ₀.globE) (pure σ₁.globE)
      rw [hr]; exact ⟨rfl⟩
    | lit _ | root _ | env _ | mtSt _ =>
      cases h
      show Srt.AgreePart _ (Op0.eval σ₀.globE _) (Op0.eval σ₁.globE _)
      rw [hr]; exact Srt.AgreePart.refl _ _
  | _, .app1 o ho x, _, h =>
    Tm.substStS_evalT_app1 hg hS o ho x (fun hx => Tm.substStS_evalT hL hg hS x hx) h
  | _, .app2 o x y, _, h =>
    Tm.substStS_evalT_app2 hS o x y (fun hx => Tm.substStS_evalT hL hg hS x hx)
      (fun hy => Tm.substStS_evalT hL hg hS y hy) h
  | _, .app3 o x y z, t', h => by
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z', hz, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact Op3.eval_part o (Tm.substStS_evalT hL hg hS x hx) (Tm.substStS_evalT hL hg hS y hy)
      (Tm.substStS_evalT hL hg hS z hz)

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

/-- `{W} φ` gives `{U}{V} φ` for the storage merge `W`. -/
theorem holds_upd_mergeSt {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} (hW : U.mergeSt? V = some W) {φ : Fml C Δ₂} (σ : State C Γ)
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) := by
  unfold Upd.mergeSt? at hW
  split at hW
  · rename_i hst
    split at hW
    · rename_i S hS
      refine holds_upd_graftF σ (fun g₁ σ₁ hL => ?_) hW h
      have hg : StChg σ.globE σ₁.globE := by rw [hL.2.1]; exact Upd.stOnly_globT U hst hL.1
      have hSe : S.evalT σ = pure σ₁.globE := by rw [hL.2.1]; exact Upd.lastSt_evalT U hL.1 S hS
      have hr : σ₁.globE = { σ.globE with storage := σ₁.globE.storage } := hg
      exact ⟨fun t _ ht => Tm.substStS_evalT hL hg hSe t ht, by rw [hr]; exact ⟨rfl, rfl, rfl⟩⟩
    · cases hW
  · cases hW

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

variable {Γ : Ctx} {M : Tm C Γ .mem} {σ₀ σ₁ : State C Γ} {μ : Semantics.State}

/-- **Read before `{memory := M}`, the substituted term reads as the term in
a typed state it lands on**, where a write looks: that state has the
storage and the locals of the state before, and the heap `M` leaves. -/
theorem Tm.withMemS_evalT (hM : M.evalT σ₀ = .ok μ)
    (hg : σ₁.globE = { σ₀.globE with heap := μ.heap, nextId := μ.nextId })
    (hl : ∀ {t : LTy} (i : Idx Γ t), σ₁.getE i = σ₀.getE i) :
    {k : Srt} → (t : Tm C Γ k) → Srt.AgreePart k ((Tm.withMemS M t).evalT σ₀) (t.evalT σ₁)
  | _, .pvV i => by
    show Tm.evalT σ₀ (.pvV i) = Tm.evalT σ₁ (.pvV i)
    simp only [Tm.evalT, hl i]
  | _, .pvP i => by
    show Tm.evalT σ₀ (.pvP i) = Tm.evalT σ₁ (.pvP i)
    simp only [Tm.evalT, State.aliasPathT_getE, hl i]
  | _, .pvI i => by
    show Tm.evalT σ₀ (.pvI i) = Tm.evalT σ₁ (.pvI i)
    simp only [Tm.evalT, State.memRefT_getE, hl i]
  | _, .pvS i => Res.stPart_ok (hl i).symm
  | _, .netOf i a => by
    have ha : (Tm.withMemS M a).evalT σ₀ = a.evalT σ₁ := Tm.withMemS_evalT hM hg hl a
    show Tm.evalT σ₀ (.netOf i (Tm.withMemS M a)) = Tm.evalT σ₁ (.netOf i a)
    simp only [Tm.evalT, ha, hl i]
  | _, .app0 o => by
    cases o with
    | memory =>
      show MemPartEq (M.evalT σ₀) (pure σ₁.globE)
      rw [hM, hg]; exact ⟨rfl⟩
    | storage =>
      show StPartEq (pure σ₀.globE) (pure σ₁.globE)
      rw [hg]; exact ⟨rfl⟩
    | mtSt _ =>
      show Srt.AgreePart _ (Op0.eval σ₀.globE _) (Op0.eval σ₁.globE _)
      rw [hg]; exact ⟨rfl⟩
    | lit _ | root _ | env _ =>
      show Srt.AgreePart _ (Op0.eval σ₀.globE _) (Op0.eval σ₁.globE _)
      rw [hg]; exact Srt.AgreePart.refl _ _
  | _, .app1 o _ x =>
    Op1.eval_part (by rw [hg]; exact ⟨rfl, rfl, rfl⟩) o (fun _ _ => by rw [hg]; rfl)
      (Or.inr (by rw [hg])) (Tm.withMemS_evalT hM hg hl x)
  | _, .app2 o x y =>
    Op2.eval_part o (Or.inr (by rw [hg])) (Tm.withMemS_evalT hM hg hl x)
      (Tm.withMemS_evalT hM hg hl y)
  | _, .app3 o x y z =>
    Op3.eval_part o (Tm.withMemS_evalT hM hg hl x) (Tm.withMemS_evalT hM hg hl y)
      (Tm.withMemS_evalT hM hg hl z)

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

/-- `{W} φ` gives `{memory := M}{V} φ` for the memory merge `W`. -/
theorem holds_upd_mergeMem {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} (hW : U.mergeMem? V = some W) {φ : Fml C Δ₂} (σ : State C Γ)
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) := by
  cases U with
  | snoc U e =>
    cases U with
    | nil =>
      cases e with
      | memory M =>
        refine holds_upd_graftF σ (fun g₁ σ₁ hL => ?_) hW h
        have h1 : (do
            let μ ← M.evalT σ
            pure { σ.globE with heap := μ.heap, nextId := μ.nextId }) = Except.ok g₁ := hL.1
        cases hM : M.evalT σ with
        | error => rw [hM] at h1; cases h1
        | ok μ =>
          rw [hM] at h1
          have hg : σ₁.globE = { σ.globE with heap := μ.heap, nextId := μ.nextId } :=
            hL.2.1.trans (Except.ok.inj h1).symm
          have hl : ∀ {t : LTy} (i : Idx Γ t), σ₁.getE i = σ.getE i := fun i => hL.2.2 i
          exact ⟨fun t _ ht => by cases ht; exact Tm.withMemS_evalT hM hg hl t,
            by rw [hg]; exact ⟨rfl, rfl, rfl⟩⟩
      | _ => cases hW
    | _ => cases hW
  | _ => cases hW

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

variable {Γ Δ : Ctx} {U : Upd C Γ Δ} {M : Tm C Γ .mem} {σ₀ : State C Γ} {σ₁ : State C Δ}
  {μ g : Semantics.State}

/-- After `{L ‖ memory := M}` the global part is the one before with the
heap `M` leaves. -/
theorem Upd.memLast?_globT (hm : U.memLast? = some M) (hU : U.globT σ₀ = .ok g) :
    ∃ μ : Semantics.State, M.evalT σ₀ = .ok μ ∧
      g = { σ₀.globE with heap := μ.heap, nextId := μ.nextId } := by
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
        rw [Upd.envOnly_globT L hL hτ]
      · cases hm
    | _ => cases hm
  | _ => cases hm

theorem Tm.substMemS_evalT (hL : U.Lands σ₀ g σ₁)
    (hg : σ₁.globE = { σ₀.globE with heap := μ.heap, nextId := μ.nextId })
    (hM : M.evalT σ₀ = .ok μ) :
    {k : Srt} → (t : Tm C Δ k) → {t' : Tm C Γ k} → Tm.substMemS U.held M t = some t' →
      Srt.AgreePart k (t'.evalT σ₀) (t.evalT σ₁)
  | _, .pvV i, _, h => by
    simp only [Tm.substMemS] at h
    exact Tm.evalT_substH_pvV _ (hL.2.2 i) h
  | _, .pvP i, _, h => by
    simp only [Tm.substMemS] at h
    exact Tm.evalT_substH_pvP _ (hL.2.2 i) h
  | _, .pvI i, _, h => by
    simp only [Tm.substMemS] at h
    exact Tm.evalT_substH_pvI _ (hL.2.2 i) h
  | _, .pvS i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvS j) | .rhs (.store x) => some x) = some t' := h
    generalize U.held i = x at h hx
    show StPartEq _ _
    cases x with
    | pos j =>
      cases h
      have hx : σ₁.getE i = σ₀.getE j := hx
      exact Res.stPart_ok hx.symm
    | rhs r =>
      cases r with
      | store x =>
        cases h
        have hx : (do pure (← t'.evalT σ₀).storage) = Except.ok (σ₁.getE i) := hx
        cases ht : t'.evalT σ₀ with
        | error e => rw [ht] at hx; cases hx
        | ok τ =>
          rw [ht] at hx
          injection hx with hτ
          exact Res.stPart_ok hτ
  | _, .netOf i a, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => (Tm.substMemS U.held M a).map (Tm.netOf j) | .rhs _ => none) = some t' := h
    generalize U.held i = x at h hx
    cases x with
    | rhs _ => cases h
    | pos j =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      have hx : σ₁.getE i = σ₀.getE j := hx
      have ha : a'.evalT σ₀ = a.evalT σ₁ := Tm.substMemS_evalT hL hg hM a ha
      show Tm.evalT σ₀ (.netOf j a') = Tm.evalT σ₁ (.netOf i a)
      simp only [Tm.evalT, ha, hx]
  | _, .app0 o, t', h => by
    cases o with
    | memory =>
      cases h
      show MemPartEq (M.evalT σ₀) (pure σ₁.globE)
      rw [hM, hg]; exact ⟨rfl⟩
    | storage =>
      cases h
      show StPartEq (pure σ₀.globE) (pure σ₁.globE)
      rw [hg]; exact ⟨rfl⟩
    | mtSt _ =>
      cases h
      show Srt.AgreePart _ (Op0.eval σ₀.globE _) (Op0.eval σ₁.globE _)
      rw [hg]; exact ⟨rfl⟩
    | lit _ | root _ | env _ =>
      cases h
      show Srt.AgreePart _ (Op0.eval σ₀.globE _) (Op0.eval σ₁.globE _)
      rw [hg]; exact Srt.AgreePart.refl _ _
  | _, .app1 o ho x, t', h => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    have hrest : σ₀.globE.Rest σ₁.globE := by rw [hg]; exact ⟨rfl, rfl, rfl⟩
    exact Op1.eval_part hrest o (fun _ _ => by rw [hg]; rfl) (Or.inr (by rw [hg]))
      (Tm.substMemS_evalT hL hg hM x hx)
  | _, .app2 o x y, t', h => by
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact Op2.eval_part o (Or.inr (by rw [hg])) (Tm.substMemS_evalT hL hg hM x hx)
      (Tm.substMemS_evalT hL hg hM y hy)
  | _, .app3 o x y z, t', h => by
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z', hz, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact Op3.eval_part o (Tm.substMemS_evalT hL hg hM x hx) (Tm.substMemS_evalT hL hg hM y hy)
      (Tm.substMemS_evalT hL hg hM z hz)

end SubstMemSound

/-- **`sequentialToParallel` over locals and a memory write**:
`{L ‖ memory := M}{V}` as one update (`Tm.substMemS`); `none` for any
other `U`. -/
def Upd.mergeMemL? {Γ Δ₁ Δ₂ : Ctx} (U : Upd C Γ Δ₁) (V : Upd C Δ₁ Δ₂) : Option (Upd C Γ Δ₂) :=
  match U.memLast? with
  | some M => U.graftF (Tm.substMemS U.held M) V
  | none => none

/-- `{W} φ` gives `{L ‖ memory := M}{V} φ` for the merge `W`. -/
theorem holds_upd_mergeMemL {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} (hW : U.mergeMemL? V = some W) {φ : Fml C Δ₂} (σ : State C Γ)
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) := by
  unfold Upd.mergeMemL? at hW
  split at hW
  · rename_i M hm
    refine holds_upd_graftF σ (fun g₁ σ₁ hL => ?_) hW h
    obtain ⟨μ, hM, hg⟩ := Upd.memLast?_globT hm hL.1
    have hg : σ₁.globE = { σ.globE with heap := μ.heap, nextId := μ.nextId } := hL.2.1.trans hg
    exact ⟨fun t _ ht => Tm.substMemS_evalT hL hg hM t ht, by rw [hg]; exact ⟨rfl, rfl, rfl⟩⟩
  · cases hW

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
