import Solidity.Calculus.RewriteScoped

/-!
# Rewrites of a scoped line past the program

The rewrites a chain takes once its program is done, on the scoped line
(`Fml C Γ`), where `Calculus/RewriteScoped.lean`'s stop: the line the
strategy leaves past a declaration keeps a hidden binder between two
updates, a merge leaves a storage write the next one shadows, a capture
stays declared after its scope ended.  Each rewrite is a `FmlRw`, sound one
way (`holds σ ψ → holds σ φ`).

| `FmlRw` | line before ⇝ line after | sound by | solkey |
|---|---|---|---|
| `mergePast k n` | the `n + 1` updates from position `k` merged into one, through hidden binders (`Fml.merge2P`), over a storage or memory write, a shadowed state write dropped (`Upd.dropSh`) | `Fml.mergeRunP_sound` | `sequentialToParallel1-3` |

**A hidden binder absorbed.**  `bind x ({x := e ‖ U} φ)`, `e` and `U` not
reading `x`, is `{x :=decl e ‖ U} φ` (`Upd.absorb`, `holds_bind_absorb`):
the binder reads every value of `x`, and the update overwrites it before
anything reads it.  Decision 101's merge across a hidden binder: the
binder's local declared by the update, the two updates then merge as any
two do.  An update of locals only moves under the binder instead
(`Upd.lift?`, `Calculus/Merge.lean`), where it declares nothing.

**A shadowed state write.**  `{… ‖ storage := S ‖ … ‖ storage := T ‖ …}`,
`S` read before anything else of `T` (`Tm.onSpineS`), is the update without
`storage := S` (`Upd.dropSh`): no element reads the state it writes into
but the ledger, `T` writes the storage over `S`'s, and `T` halts where `S`
does.  So for memory writes (`Tm.onMemSpineS`).

These functions run once a link and use `match` on the indexed families,
under the exemption of `Calculus/RewriteScoped.lean`'s walks (proposal 104).
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)
open Semantics (Res)

variable {C : Contract}

/-! ## Read with fewer locals

A term, a right-hand side read in a context with fewer locals, where it
reads none of those dropped (`Tm.thinS?`, `Rhs.thinS?`). -/

section ThinS

/-- A position of `Δ` read in `Γ`, where the thinning keeps it. -/
def Idx.unwk? : {Γ Δ : Ctx} → {t : LTy} → Thin Γ Δ → Idx Δ t → Option (Idx Γ t)
  | _, _, _, .refl, i => some i
  | _, _, _, .keep _, .here => some .here
  | _, _, _, .keep h, .there i => (Idx.unwk? h i).map .there
  | _, _, _, .drop _, .here => none
  | _, _, _, .drop h, .there i => Idx.unwk? h i

theorem Idx.unwk?_wk : {Γ Δ : Ctx} → {t : LTy} → (h : Thin Γ Δ) → (i : Idx Δ t) →
    {j : Idx Γ t} → Idx.unwk? h i = some j → j.wk h = i
  | _, _, _, .refl, _, _, hj => by cases hj; exact Idx.wk_refl _
  | _, _, _, .keep _, .here, _, hj => by cases hj; rfl
  | _, _, _, .keep h, .there i, _, hj => by
    obtain ⟨j', hj', rfl⟩ := Option.map_eq_some_iff.1 hj
    exact congrArg Idx.there (Idx.unwk?_wk h i hj')
  | _, _, _, .drop _, .here, _, hj => by cases hj
  | _, _, _, .drop h, .there i, _, hj => congrArg Idx.there (Idx.unwk?_wk h i hj)

variable {Γ Γ' : Ctx}

/-- A term of `Γ` read in `Γ'`, where it reads no local the thinning drops. -/
def Tm.thinS? (h : Thin Γ' Γ) : {s : Srt} → Tm C Γ s → Option (Tm C Γ' s)
  | _, .pvV i => (Idx.unwk? h i).map .pvV
  | _, .pvP i => (Idx.unwk? h i).map .pvP
  | _, .pvS i => (Idx.unwk? h i).map .pvS
  | _, .pvI i => (Idx.unwk? h i).map .pvI
  | _, .netOf i a => do pure (.netOf (← Idx.unwk? h i) (← Tm.thinS? h a))
  | _, .app0 o => some (.app0 o)
  | _, .app1 o ho x => (Tm.thinS? h x).map (.app1 o ho)
  | _, .app2 o x y => do pure (.app2 o (← Tm.thinS? h x) (← Tm.thinS? h y))
  | _, .app3 o x y z => do pure (.app3 o (← Tm.thinS? h x) (← Tm.thinS? h y) (← Tm.thinS? h z))

/-- `σ'` is `σ` with the locals the thinning drops left out, as a term reads
them: one global part, each kept local where `h` puts it. -/
def State.ThinOf (h : Thin Γ' Γ) (σ' : State C Γ') (σ : State C Γ) : Prop :=
  σ'.globE = σ.globE ∧ ∀ {t : LTy} (j : Idx Γ' t), σ'.getE j = σ.getE (j.wk h)

theorem State.ThinOf.thin (h : Thin Γ' Γ) (σ : State C Γ) : State.ThinOf h (σ.thin h) σ :=
  ⟨rfl, fun j => State.getE_thin h σ j⟩

theorem State.ThinOf.getE_unwk? {h : Thin Γ' Γ} {σ' : State C Γ'} {σ : State C Γ}
    (hr : State.ThinOf h σ' σ) {t : LTy} {i : Idx Γ t} {j : Idx Γ' t}
    (hj : Idx.unwk? h i = some j) : σ'.getE j = σ.getE i := by
  rw [hr.2 j, Idx.unwk?_wk h i hj]

/-- **A term that reads no dropped local reads alike with them dropped.** -/
theorem Tm.eval_thinS? {h : Thin Γ' Γ} {σ' : State C Γ'} {σ : State C Γ}
    (hr : State.ThinOf h σ' σ) :
    {s : Srt} → (t : Tm C Γ s) → {t' : Tm C Γ' s} → Tm.thinS? h t = some t' →
      t'.eval σ' = t.eval σ
  | _, .pvV i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    simp only [Tm.eval, hr.getE_unwk? hj]
  | _, .pvP i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    simp only [Tm.eval, State.aliasPathT_getE, hr.getE_unwk? hj]
  | _, .pvS i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    simp only [Tm.eval, hr.1, hr.getE_unwk? hj]
  | _, .pvI i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    simp only [Tm.eval, State.memRefT_getE, hr.getE_unwk? hj]
  | _, .netOf i a, _, ht => by
    obtain ⟨j, hj, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨a', ha, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    simp only [Tm.eval, hr.getE_unwk? hj, Tm.eval_thinS? hr a ha]
  | _, .app0 _, _, ht => by cases ht; simp only [Tm.eval, hr.1]
  | _, .app1 o ho x, _, ht => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 ht
    simp only [Tm.eval, hr.1, Tm.eval_thinS? hr x hx]
  | _, .app2 o x y, _, ht => by
    obtain ⟨x', hx, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨y', hy, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    simp only [Tm.eval, hr.1, Tm.eval_thinS? hr x hx, Tm.eval_thinS? hr y hy]
  | _, .app3 o x y z, _, ht => by
    obtain ⟨x', hx, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨y', hy, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨z', hz, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    simp only [Tm.eval, hr.1, Tm.eval_thinS? hr x hx, Tm.eval_thinS? hr y hy,
      Tm.eval_thinS? hr z hz]

/-- **A term that reads no dropped local denotes alike with them dropped.** -/
theorem Tm.denote_thinS? {h : Thin Γ' Γ} {σ' : State C Γ'} {σ : State C Γ}
    (hr : State.ThinOf h σ' σ) :
    {s : Srt} → (t : Tm C Γ s) → {t' : Tm C Γ' s} → Tm.thinS? h t = some t' →
      t'.denote σ' = t.denote σ
  | _, .pvV i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    simp only [Tm.denote, hr.getE_unwk? hj]
  | _, .pvP i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    simp only [Tm.denote, State.aliasPathT_getE, hr.getE_unwk? hj]
  | _, .pvS i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    simp only [Tm.denote, hr.getE_unwk? hj]
  | _, .pvI i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    rfl
  | _, .netOf i a, _, ht => by
    obtain ⟨j, hj, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨a', ha, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    simp only [Tm.denote, hr.getE_unwk? hj, Tm.denote_thinS? hr a ha]
  | _, .app0 _, _, ht => by cases ht; simp only [Tm.denote, hr.1]
  | _, .app1 o ho x, _, ht => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 ht
    simp only [Tm.denote, hr.1, Tm.denote_thinS? hr x hx]
  | _, .app2 o x y, _, ht => by
    obtain ⟨x', hx, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨y', hy, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    simp only [Tm.denote, hr.1, Tm.denote_thinS? hr x hx, Tm.denote_thinS? hr y hy,
      Tm.eval_thinS? hr x hx, Tm.eval_thinS? hr y hy]
  | _, .app3 o x y z, _, ht => by
    obtain ⟨x', hx, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨y', hy, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨z', hz, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    simp only [Tm.denote, Tm.denote_thinS? hr x hx, Tm.denote_thinS? hr y hy,
      Tm.denote_thinS? hr z hz]

/-- A right-hand side of `Γ` read in `Γ'`. -/
def Rhs.thinS? (h : Thin Γ' Γ) : {t : LTy} → Rhs C Γ t → Option (Rhs C Γ' t)
  | _, .val t => (Tm.thinS? h t).map .val
  | _, .path p => (Tm.thinS? h p).map .path
  | _, .unset => some .unset
  | _, .mref i => (Tm.thinS? h i).map .mref
  | _, .store s => (Tm.thinS? h s).map .store
  | _, .saveNet => some .saveNet
  | _, .saveNetMt => some .saveNetMt

theorem Rhs.eval_thinS? {h : Thin Γ' Γ} {σ' : State C Γ'} {σ : State C Γ}
    (hr : State.ThinOf h σ' σ) :
    {t : LTy} → (r : Rhs C Γ t) → {r' : Rhs C Γ' t} → Rhs.thinS? h r = some r' →
      r'.eval σ' = r.eval σ
  | _, .val t, _, hx => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 hx
    exact Tm.eval_thinS? hr t ht
  | _, .path p, _, hx => by
    obtain ⟨p', hp, rfl⟩ := Option.map_eq_some_iff.1 hx
    simp only [Rhs.eval, Tm.eval_thinS? hr p hp]
  | _, .unset, _, hx => by cases hx; rfl
  | _, .mref i, _, hx => by
    obtain ⟨i', hi, rfl⟩ := Option.map_eq_some_iff.1 hx
    simp only [Rhs.eval, Tm.eval_thinS? hr i hi]
  | _, .store s, _, hx => by
    obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 hx
    simp only [Rhs.eval, Tm.eval_thinS? hr s hs]
  | _, .saveNet, _, hx => by
    cases hx
    have hn : σ'.net = σ.net := congrArg Semantics.State.net hr.1
    simp only [Rhs.eval, hn]
  | _, .saveNetMt, _, hx => by cases hx; rfl

end ThinS

/-! ## Out of the top local's scope -/

section Down

variable {Γ : Ctx} {u : LTy}

/-- A position of `u :: Γ` read in `Γ`: none for the top one. -/
abbrev Idx.down? {t : LTy} (i : Idx (u :: Γ) t) : Option (Idx Γ t) := Idx.unwk? (.drop .refl) i

/-- A term of `u :: Γ` read in `Γ`, where it does not read the top local. -/
abbrev Tm.down? {s : Srt} (t : Tm C (u :: Γ) s) : Option (Tm C Γ s) := Tm.thinS? (.drop .refl) t

/-- A right-hand side of `u :: Γ` read in `Γ`. -/
abbrev Rhs.down? {t : LTy} (r : Rhs C (u :: Γ) t) : Option (Rhs C Γ t) :=
  Rhs.thinS? (.drop .refl) r

/-- An element whose right-hand sides are read in `u :: Γ`, read in `Γ`. -/
def UpdElem.down? {Δ : Ctx} : UpdElem C (u :: Γ) Δ → Option (UpdElem C Γ Δ)
  | .local i r => r.down?.map (.local i)
  | .storage s => s.down?.map .storage
  | .memory m => m.down?.map .memory
  | .selfBalance op a => a.down?.map (.selfBalance op)
  | .net r op a => do pure (.net (← r.down?) op (← a.down?))
  | .pay r a => do pure (.pay (← r.down?) (← a.down?))
  | .netMt r a => do pure (.netMt (← r.down?) (← a.down?))
  | .setBalance a => a.down?.map .setBalance

/-- A state below a pushed local is the state with it left out. -/
theorem State.ThinOf.push (σ : State C Γ) (v : u.TDenote C σ.H) :
    State.ThinOf (.drop .refl) σ (σ.push v) :=
  ⟨rfl, fun _ => rfl⟩

/-- **A term that does not read the top local reads alike below it.** -/
theorem Tm.eval_down? (σ : State C Γ) (v : u.TDenote C σ.H) {s : Srt} (t : Tm C (u :: Γ) s)
    {t' : Tm C Γ s} (h : t.down? = some t') : t'.eval σ = t.eval (σ.push v) :=
  Tm.eval_thinS? (State.ThinOf.push σ v) t h

theorem Rhs.eval_down? (σ : State C Γ) (v : u.TDenote C σ.H) {t : LTy} (r : Rhs C (u :: Γ) t)
    {r' : Rhs C Γ t} (h : r.down? = some r') : r'.eval σ = r.eval (σ.push v) :=
  Rhs.eval_thinS? (State.ThinOf.push σ v) r h

theorem UpdElem.globT_down? {Δ : Ctx} (σ : State C Γ) (v : u.TDenote C σ.H) :
    (e : UpdElem C (u :: Γ) Δ) → {e' : UpdElem C Γ Δ} → e.down? = some e' →
      ∀ G, e'.globT σ G = e.globT (σ.push v) G
  | .local i r, _, h, G => by
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.globT, Rhs.eval_down? σ v r hr]
  | .storage s, _, h, G => by
    obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.globT, Tm.eval_down? σ v s hs]
  | .memory m, _, h, G => by
    obtain ⟨m', hm, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.globT, Tm.eval_down? σ v m hm]
  | .selfBalance op a, _, h, G => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.globT, Tm.eval_down? σ v a ha]; rfl
  | .net r op a, _, h, G => by
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [UpdElem.globT, Tm.eval_down? σ v r hr, Tm.eval_down? σ v a ha]
  | .pay r a, _, h, G => by
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [UpdElem.globT, Tm.eval_down? σ v r hr, Tm.eval_down? σ v a ha]; rfl
  | .netMt r a, _, h, G => by
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [UpdElem.globT, Tm.eval_down? σ v r hr, Tm.eval_down? σ v a ha]
  | .setBalance a, _, h, G => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [UpdElem.globT, Tm.eval_down? σ v a ha]

end Down

/-! ## A hidden binder absorbed -/

section Absorb

variable {Γ : Ctx} {u : LTy}

/-- Where the binder's local sits after an update that only declares on top
of it. -/
def Upd.baseIdx : {Δ : Ctx} → Upd C (u :: Γ) Δ → Option (Idx Δ u)
  | _, .nil => some .here
  | _, .snoc V _ => Upd.baseIdx V
  | _, .decl V _ _ => (Upd.baseIdx V).map .there
  | _, .pop .. => none
  | _, .drop .. => none

/-- Whether an element writes the local at `j`. -/
def UpdElem.writesAt {Γ' Δ : Ctx} (j : Idx Δ u) : UpdElem C Γ' Δ → Bool
  | .local i _ => i.toNat == j.toNat
  | _ => false

/-- The update with `x :=decl b` beneath it in place of the binder: every
element read from above the binder, none writing its local, no scope ended
(`Upd.absorb`'s part before the binder's local is set). -/
def Upd.rebase (x : Var) (b : Rhs C Γ u) : {Δ : Ctx} → Upd C (u :: Γ) Δ → Option (Upd C Γ Δ)
  | _, .nil => some (.decl .nil x b)
  | _, .snoc V e => do
    let j ← Upd.baseIdx V
    if e.writesAt j then none else pure (.snoc (← Upd.rebase x b V) (← e.down?))
  | _, .decl V y r => do pure (.decl (← Upd.rebase x b V) y (← r.down?))
  | _, .pop .. => none
  | _, .drop .. => none

/-- Whether an update has no element. -/
def Upd.isNilB {Γ Δ : Ctx} : Upd C Γ Δ → Bool
  | .nil => true
  | _ => false

/-- `e`, the first write of the binder's local after `V`: `V` with the
local declared beneath it, set to what `e` sets it to; where `V` declares
locals, only if `reorder` (the local is then declared before them, so the
parallel update prints it first). -/
def Upd.absorbFirst (x : Var) (reorder : Bool) {Δ : Ctx} (V : Upd C (u :: Γ) Δ) :
    UpdElem C (u :: Γ) Δ → Option (Upd C Γ Δ)
  | .local (t := t) i r =>
    if h : t = u then by
      subst h
      exact (do
        let j ← Upd.baseIdx V
        if (reorder || V.isNilB) && i.toNat == j.toNat then Upd.rebase x (← r.down?) V else none)
    else none
  | _ => none

/-- `{V ‖ e}` absorbed, from `V` absorbed (`rec`); else `e` is the first
write of the binder's local (`Upd.absorbFirst`). -/
def Upd.absorbSnoc (x : Var) (reorder : Bool) {Δ : Ctx} (V : Upd C (u :: Γ) Δ)
    (e : UpdElem C (u :: Γ) Δ) : Option (Upd C Γ Δ) → Option (Upd C Γ Δ)
  | some V' => do pure (.snoc V' (← e.down?))
  | none => Upd.absorbFirst x reorder V e

/-- An update applied below a hidden binder of `x : u`, which sets `x`
before any element reads it, and reads it nowhere: the update from above
the binder, `x` declared beneath it to what its first write sets it to
(`bind x ({x := e ‖ U} φ) ⇝ {x :=decl e ‖ U} φ`, and `bind x ({y :=decl a ‖
x := e ‖ U} φ) ⇝ {x :=decl e ‖ y :=decl a ‖ U} φ`). -/
def Upd.absorb (x : Var) (reorder : Bool := false) : {Δ : Ctx} → Upd C (u :: Γ) Δ → Option (Upd C Γ Δ)
  | _, .nil => none
  | _, .snoc V e => Upd.absorbSnoc x reorder V e (Upd.absorb x reorder V)
  | _, .decl V y r => do pure (.decl (← Upd.absorb x reorder V) y (← r.down?))
  | _, .pop V h => (Upd.absorb x reorder V).map (.pop · h)
  | _, .drop V h => (Upd.absorb x reorder V).map (.drop · h)

/-- **The update rebased computes, from the state above the binder, the
binder's right-hand side and then the update's global part**, whatever the
binder's local holds. -/
theorem Upd.rebase_globT (x : Var) (b : Rhs C Γ u) (σ : State C Γ) (w : u.TDenote C σ.H) :
    {Δ : Ctx} → (V : Upd C (u :: Γ) Δ) → {V' : Upd C Γ Δ} → V.rebase x b = some V' →
      V'.globT σ = (b.eval σ >>= fun _ => V.globT (σ.push w))
  | _, .nil, _, h => by
    cases h
    show (do let g ← pure σ.globE; let _ ← b.eval σ; pure g) = _
    cases b.eval σ <;> rfl
  | _, .snoc V e, _, h => by
    simp only [Upd.rebase] at h
    obtain ⟨j, -, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · cases h
    · obtain ⟨W, hW, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      show (W.globT σ >>= e'.globT σ) = _
      rw [Upd.rebase_globT x b σ w V hW]
      have he' : e'.globT σ = e.globT (σ.push w) := funext (UpdElem.globT_down? σ w e he)
      rw [he']
      cases b.eval σ <;> rfl
  | _, .decl V y r, _, h => by
    obtain ⟨W, hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show (do let g ← W.globT σ; let _ ← r'.eval σ; pure g) = _
    rw [Upd.rebase_globT x b σ w V hW, Rhs.eval_down? σ w r hr]
    cases b.eval σ <;> rfl
  | _, .pop .., _, h => by cases h
  | _, .drop .., _, h => by cases h

/-- **The update rebased leaves the binder's local holding its right-hand
side, and every other local what the update leaves there.** -/
theorem Upd.rebase_held (x : Var) (b : Rhs C Γ u) (σ : State C Γ) (w : u.TDenote C σ.H) :
    {Δ : Ctx} → (V : Upd C (u :: Γ) Δ) → {V' : Upd C Γ Δ} → V.rebase x b = some V' →
      {j : Idx Δ u} → V.baseIdx = some j →
      V'.held j = .rhs b ∧ ∀ {t : LTy} (i : Idx Δ t), i.toNat ≠ j.toNat → ∀ v : t.Denote C,
        Held.OKV (σ.push w) v (V.held i) → Held.OKV σ v (V'.held i)
  | _, .nil, _, h, j, hj => by
    cases h
    cases hj
    refine ⟨rfl, fun i hi v hv => ?_⟩
    cases i with
    | here => exact absurd rfl hi
    | there k => exact hv
  | _, .snoc V e, _, h, j, hj => by
    simp only [Upd.rebase] at h
    obtain ⟨j', hj', h⟩ := Option.bind_eq_some_iff.1 h
    have hjj : j' = j := Option.some.inj (hj'.symm.trans hj)
    subst hjj
    split at h
    · cases h
    · rename_i hn
      obtain ⟨W, hW, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      have ih := Upd.rebase_held x b σ w V hW hj
      cases e with
      | «local» k r =>
        obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 he
        have hkj : k.toNat ≠ j'.toNat := fun hc => hn (by simp only [UpdElem.writesAt, hc,
          beq_self_eq_true])
        refine ⟨?_, fun i hi v hv => ?_⟩
        · show Subst.set (Upd.held W) k r' j' = _
          unfold Subst.set
          rw [dif_neg hkj]
          exact ih.1
        · show Held.OKV σ v (Subst.set (Upd.held W) k r' i)
          have hv : Held.OKV (σ.push w) v (Subst.set (Upd.held V) k r i) := hv
          unfold Subst.set at hv ⊢
          by_cases hki : k.toNat = i.toNat
          · obtain rfl := Idx.ty_eq_of_toNat hki
            obtain rfl := Idx.toNat_inj k i hki
            rw [dif_pos rfl] at hv ⊢
            show r'.eval σ = .ok v
            rw [Rhs.eval_down? σ w r hr]
            exact hv
          · rw [dif_neg hki] at hv ⊢
            exact ih.2 i hi v hv
      | storage s | memory s | setBalance s =>
        obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 he
        exact ih
      | selfBalance op a =>
        obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 he
        exact ih
      | net r op a | pay r a | netMt r a =>
        simp only [UpdElem.down?] at he
        obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 he
        obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 he
        cases he
        exact ih
  | _, .decl V y r, _, h, j, hj => by
    obtain ⟨W, hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    obtain ⟨j₀, hj₀, rfl⟩ := Option.map_eq_some_iff.1 hj
    have ih := Upd.rebase_held x b σ w V hW hj₀
    refine ⟨ih.1, fun i hi v hv => ?_⟩
    cases i with
    | here =>
      show r'.eval σ = .ok v
      rw [Rhs.eval_down? σ w r hr]
      exact hv
    | there k => exact ih.2 k (fun hc => hi (by simp only [Idx.toNat, hc])) v hv
  | _, .pop .., _, h, _, _ => by cases h
  | _, .drop .., _, h, _, _ => by cases h

theorem Semantics.Res.OkEq.bind' {α β : Type} {a b : Res α} (h : Res.OkEq a b) (f : α → Res β) :
    Res.OkEq (a >>= f) (b >>= f) := fun y => by
  cases ha : a with
  | ok x =>
    rw [(h x).1 ha]
  | error e =>
    cases hb : b with
    | ok x => rw [(h x).2 hb] at ha; cases ha
    | error e' => exact ⟨fun hh => (nomatch hh), fun hh => (nomatch hh)⟩

/-- **The absorbed update computes, from the state above the binder, the
global part the update computes from any value of the binder's local**, up
to which halt comes first. -/
theorem Upd.absorb_globT (x : Var) (reorder : Bool) (σ : State C Γ) (w : u.TDenote C σ.H) :
    {Δ : Ctx} → (V : Upd C (u :: Γ) Δ) → {V' : Upd C Γ Δ} → V.absorb x reorder = some V' →
      Res.OkEq (V'.globT σ) (V.globT (σ.push w))
  | _, .nil, _, h => by cases h
  | _, .snoc V e, V', h => by
    simp only [Upd.absorb] at h
    cases hr : Upd.absorb x reorder V with
    | some W =>
      rw [hr] at h
      obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      have ih := Upd.absorb_globT x reorder σ w V hr
      show Res.OkEq (W.globT σ >>= e'.globT σ) (V.globT (σ.push w) >>= e.globT (σ.push w))
      have he' : e'.globT σ = e.globT (σ.push w) := funext (UpdElem.globT_down? σ w e he)
      rw [he']
      exact ih.bind' _
    | none =>
      rw [hr] at h
      simp only [Upd.absorbSnoc, Upd.absorbFirst] at h
      cases e with
      | «local» i r =>
        rename_i t
        simp only at h
        split at h
        · rename_i htu
          subst htu
          simp only at h
          obtain ⟨j, hj, h⟩ := Option.bind_eq_some_iff.1 h
          split at h
          · rename_i hij
            have hij : i = j := Idx.toNat_inj i j
              (by simpa only [Bool.and_eq_true, beq_iff_eq] using (Bool.and_eq_true_iff.mp hij).2)
            subst hij
            obtain ⟨r', hr', h⟩ := Option.bind_eq_some_iff.1 h
            rw [Upd.rebase_globT x r' σ w V h]
            intro y
            show (do let _ ← r'.eval σ; V.globT (σ.push w)) = .ok y ↔
              (do let g ← V.globT (σ.push w); let _ ← r.eval (σ.push w); pure g) = .ok y
            rw [Rhs.eval_down? σ w r hr']
            cases r.eval (σ.push w) with
            | error e =>
              cases V.globT (σ.push w) <;> exact ⟨fun hh => (nomatch hh), fun hh => (nomatch hh)⟩
            | ok a => cases V.globT (σ.push w) <;> exact Iff.rfl
          · cases h
        · cases h
      | _ => cases h
  | _, .decl V y r, _, h => by
    obtain ⟨W, hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show Res.OkEq (do let g ← W.globT σ; let _ ← r'.eval σ; pure g)
      (do let g ← V.globT (σ.push w); let _ ← r.eval (σ.push w); pure g)
    rw [Rhs.eval_down? σ w r hr]
    exact (Upd.absorb_globT x reorder σ w V hW).bind' _
  | _, .pop V _, _, h => by
    obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.absorb_globT x reorder σ w V hW
  | _, .drop V _, _, h => by
    obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.absorb_globT x reorder σ w V hW

/-- **The absorbed update leaves in each local what the update leaves**,
read from the state above the binder. -/
theorem Upd.absorb_held (x : Var) (reorder : Bool) (σ : State C Γ) (w : u.TDenote C σ.H) :
    {Δ : Ctx} → (V : Upd C (u :: Γ) Δ) → {V' : Upd C Γ Δ} → V.absorb x reorder = some V' →
      ∀ {t : LTy} (i : Idx Δ t) (v : t.Denote C), Held.OKV (σ.push w) v (V.held i) →
        Held.OKV σ v (V'.held i)
  | _, .nil, _, h => by cases h
  | _, .snoc V e, V', h => by
    simp only [Upd.absorb] at h
    cases hr : Upd.absorb x reorder V with
    | some W =>
      rw [hr] at h
      obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      have ih : ∀ {t : LTy} (i : Idx _ t) (v : t.Denote C), Held.OKV (σ.push w) v (V.held i) →
          Held.OKV σ v (W.held i) := fun i v hv => Upd.absorb_held x reorder σ w V hr i v hv
      intro i v hv
      cases e with
      | «local» k r =>
        obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 he
        show Held.OKV σ v (Subst.set (Upd.held W) k r' i)
        have hv : Held.OKV (σ.push w) v (Subst.set (Upd.held V) k r i) := hv
        unfold Subst.set at hv ⊢
        by_cases hki : k.toNat = i.toNat
        · obtain rfl := Idx.ty_eq_of_toNat hki
          obtain rfl := Idx.toNat_inj k i hki
          rw [dif_pos rfl] at hv ⊢
          show r'.eval σ = .ok v
          rw [Rhs.eval_down? σ w r hr']
          exact hv
        · rw [dif_neg hki] at hv ⊢
          exact ih i v hv
      | storage s | memory s | setBalance s =>
        obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 he
        exact ih i v hv
      | selfBalance op a =>
        obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 he
        exact ih i v hv
      | net r op a | pay r a | netMt r a =>
        simp only [UpdElem.down?] at he
        obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 he
        obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 he
        cases he
        exact ih i v hv
    | none =>
      rw [hr] at h
      simp only [Upd.absorbSnoc, Upd.absorbFirst] at h
      cases e with
      | «local» i₀ r =>
        rename_i t₀
        simp only at h
        split at h
        · rename_i htu
          subst htu
          simp only at h
          obtain ⟨j, hj, h⟩ := Option.bind_eq_some_iff.1 h
          split at h
          · rename_i hij
            have hij : i₀ = j := Idx.toNat_inj i₀ j
              (by simpa only [Bool.and_eq_true, beq_iff_eq] using (Bool.and_eq_true_iff.mp hij).2)
            subst hij
            obtain ⟨r', hr', h⟩ := Option.bind_eq_some_iff.1 h
            have hb := Upd.rebase_held x r' σ w V h hj
            intro i v hv
            have hv : Held.OKV (σ.push w) v (Subst.set (Upd.held V) i₀ r i) := hv
            unfold Subst.set at hv
            by_cases hki : i₀.toNat = i.toNat
            · obtain rfl := Idx.ty_eq_of_toNat hki
              obtain rfl := Idx.toNat_inj i₀ i hki
              rw [dif_pos rfl] at hv
              rw [hb.1]
              show r'.eval σ = .ok v
              rw [Rhs.eval_down? σ w r hr']
              exact hv
            · rw [dif_neg hki] at hv
              exact hb.2 i (Ne.symm hki) v hv
          · cases h
        · cases h
      | _ => cases h
  | _, .decl V y r, _, h => by
    obtain ⟨W, hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    intro i v hv
    cases i with
    | here =>
      show r'.eval σ = .ok v
      rw [Rhs.eval_down? σ w r hr]
      exact hv
    | there k => exact Upd.absorb_held x reorder σ w V hW k v hv
  | _, .pop V e, _, h => by
    obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun i v hv => Upd.absorb_held x reorder σ w V hW (i.ext e) v hv
  | _, .drop V e, _, h => by
    obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun i v hv => Upd.absorb_held x reorder σ w V hW (i.wk e) v hv

/-- **`bind x ({x := e ‖ U} φ)` from `{x :=decl e ‖ U} φ`.** -/
theorem holds_bind_absorb {m m' : Modality} {x : Var} {reorder : Bool} {Δ : Ctx}
    {V : Upd C (u :: Γ) Δ} {V' : Upd C Γ Δ} (hV : V.absorb x reorder = some V') {ψ : Fml C Δ}
    (σ : State C Γ)
    (h : holds σ (.upd m' V' ψ)) : holds σ (.bind m x u (.upd m' V ψ)) :=
  Modality.forallB_intro fun w => by
    have hg := Upd.absorb_globT x reorder σ w V hV
    refine Upd.afterT_intro (fun e he => ?_) fun g σ' hL hH => ?_
    · cases hb : V'.globT σ with
      | error e' => exact h.of_error hb
      | ok y => rw [(hg y).1 hb] at he; cases he
    · refine h.of_lands (g := g) ⟨(hg g).2 hL.1, hL.2.1, fun i => ?_⟩ hH
      rw [Held.OKT_iff_OKV]
      exact Upd.absorb_held x reorder σ w V hV i _ ((Held.OKT_iff_OKV _ _ _ _).1 (hL.2.2 i))

end Absorb

/-! ## A shadowed state write dropped -/

section Shadow

variable {Γ : Ctx}

/-- A storage operation over its first argument (`select`, `delAt`, a push
or pop's slot, `save`): what a storage spine runs through. -/
def Op1.stSpine {a s : Srt} : Op1 a s → Bool
  | .select _ => true
  | _ => false

@[inherit_doc Op1.stSpine]
def Op2.stSpine {a b s : Srt} : Op2 a b s → Bool
  | .delAt | .pushSlot _ | .pop | .shrink | .extend _ => true
  | _ => false

@[inherit_doc Op1.stSpine]
def Op3.stSpine {a b c s : Srt} : Op3 a b c s → Bool
  | .save | .push => true
  | _ => false

/-- A memory operation over its first argument (`addM`, `copySt`, `write`). -/
def Op1.memSpine {a s : Srt} : Op1 a s → Bool
  | .addM _ => true
  | _ => false

@[inherit_doc Op1.memSpine]
def Op2.memSpine {a b s : Srt} : Op2 a b s → Bool
  | .copySt => true
  | _ => false

@[inherit_doc Op1.memSpine]
def Op3.memSpine {a b c s : Srt} : Op3 a b c s → Bool
  | .write => true
  | _ => false

/-- `Tm.spineHas`' compiled twin. -/
def Tm.spineHasM (S : Tm C Γ .st) : {s : Srt} → Tm C Γ s → Bool
  | _, .app1 o _ a => o.stSpine && (a.beqR S || Tm.spineHasM S a)
  | _, .app2 o a _ => o.stSpine && (a.beqR S || Tm.spineHasM S a)
  | _, .app3 o a _ _ => o.stSpine && (a.beqR S || Tm.spineHasM S a)
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .netOf .. | _, .app0 _ => false

/-- `S` is read first, strictly inside `T`: `T` a storage operation over `S`
or over a term with `S` on its spine (`Tm.spineAny`).  Generic in the
sort, by the recursor. -/
@[implemented_by Tm.spineHasM]
def Tm.spineHas (S : Tm C Γ .st) {s : Srt} (T : Tm C Γ s) : Bool :=
  Tm.rec (motive := fun _ _ => Bool)
    (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ _ _ => false)
    (fun _ => false)
    (fun o _ a ih => o.stSpine && (a.beqR S || ih))
    (fun o a _ iha _ => o.stSpine && (a.beqR S || iha))
    (fun o a _ _ iha _ _ => o.stSpine && (a.beqR S || iha)) T

theorem Tm.spineHas_eq_spineHasM (S : Tm C Γ .st) {s : Srt} (T : Tm C Γ s) :
    Tm.spineHas S T = Tm.spineHasM S T := by
  induction T with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ _ | app0 _ => rfl
  | app1 o _ a ih => simp only [Tm.spineHasM, ← ih]; rfl
  | app2 o a _ ih _ => simp only [Tm.spineHasM, ← ih]; rfl
  | app3 o a _ _ ih _ _ => simp only [Tm.spineHasM, ← ih]; rfl

/-- `S` is read before anything else of `T` (`Tm.onSpine`): `T` is `S`, or
`S` is on its spine. -/
def Tm.onSpineS (T S : Tm C Γ .st) : Bool := T.beqR S || Tm.spineHas S T

/-- `Tm.memSpineHas`' compiled twin. -/
def Tm.memSpineHasM (M : Tm C Γ .mem) : {s : Srt} → Tm C Γ s → Bool
  | _, .app1 o _ a => o.memSpine && (a.beqR M || Tm.memSpineHasM M a)
  | _, .app2 o a _ => o.memSpine && (a.beqR M || Tm.memSpineHasM M a)
  | _, .app3 o a _ _ => o.memSpine && (a.beqR M || Tm.memSpineHasM M a)
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .netOf .. | _, .app0 _ => false

/-- `M` is read first, strictly inside `N`, on the memory spine
(`Tm.memSpineAny`), by the recursor. -/
@[implemented_by Tm.memSpineHasM]
def Tm.memSpineHas (M : Tm C Γ .mem) {s : Srt} (N : Tm C Γ s) : Bool :=
  Tm.rec (motive := fun _ _ => Bool)
    (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ _ _ => false)
    (fun _ => false)
    (fun o _ a ih => o.memSpine && (a.beqR M || ih))
    (fun o a _ iha _ => o.memSpine && (a.beqR M || iha))
    (fun o a _ _ iha _ _ => o.memSpine && (a.beqR M || iha)) N

theorem Tm.memSpineHas_eq_memSpineHasM (M : Tm C Γ .mem) {s : Srt} (N : Tm C Γ s) :
    Tm.memSpineHas M N = Tm.memSpineHasM M N := by
  induction N with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ _ | app0 _ => rfl
  | app1 o _ a ih => simp only [Tm.memSpineHasM, ← ih]; rfl
  | app2 o a _ ih _ => simp only [Tm.memSpineHasM, ← ih]; rfl
  | app3 o a _ _ ih _ _ => simp only [Tm.memSpineHasM, ← ih]; rfl

/-- `M` is read before anything else of `N` on the memory spine. -/
def Tm.onMemSpineS (N M : Tm C Γ .mem) : Bool := N.beqR M || Tm.memSpineHas M N

/-- An outcome that halted, at any sort. -/
def Srt.Halts : (s : Srt) → s.Ev → Prop
  | .val, r => ∃ e, r = .error e
  | .path, r => ∃ e, r = .error e
  | .st, r => ∃ e, r = .error e
  | .sv, r => ∃ e, r = .error e
  | .ident, r => ∃ e, r = .error e
  | .addr, r => ∃ e, r = .error e
  | .mem, r => ∃ e, r = .error e
  | .mv, r => ∃ e, r = .error e

/-- A term with `S` on its spine halts wherever `S` does. -/
theorem Tm.spineHas_haltsM {S : Tm C Γ .st} {σ : State C Γ} {e : Semantics.Halt}
    (hS : S.eval σ = .error e) {s : Srt} (T : Tm C Γ s) (h : Tm.spineHasM S T = true) :
    Srt.Halts s (T.eval σ) := by
  induction T with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ _ | app0 _ => exact absurd h Bool.false_ne_true
  | app1 o ho a iha =>
    simp only [Tm.spineHasM, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨ho', h'⟩ := h
    cases o <;> simp only [Op1.stSpine, Bool.false_eq_true] at ho'
    all_goals
      obtain ⟨e', ha⟩ : ∃ e', a.eval σ = .error e' := by
        rcases h' with h' | h'
        · exact ⟨e, (Tm.eq_of_beqR h') ▸ hS⟩
        · exact iha h'
      exact ⟨e', by show Op1.eval _ _ (a.eval σ) = _; rw [ha]; rfl⟩
  | app2 o a b iha _ =>
    simp only [Tm.spineHasM, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨ho', h'⟩ := h
    cases o <;> simp only [Op2.stSpine, Bool.false_eq_true] at ho'
    all_goals
      obtain ⟨e', ha⟩ : ∃ e', a.eval σ = .error e' := by
        rcases h' with h' | h'
        · exact ⟨e, (Tm.eq_of_beqR h') ▸ hS⟩
        · exact iha h'
      first
        | exact ⟨e', by show Op2.eval _ _ (a.eval σ) (b.eval σ) = _; rw [ha]; rfl⟩
        | (show ∃ e'', Op2.eval _ _ (a.eval σ) (b.eval σ) = _
           rw [ha]
           generalize b.eval σ = r
           cases r <;> exact ⟨_, rfl⟩)
  | app3 o a b c iha _ _ =>
    simp only [Tm.spineHasM, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨ho', h'⟩ := h
    cases o <;> simp only [Op3.stSpine, Bool.false_eq_true] at ho'
    all_goals
      obtain ⟨e', ha⟩ : ∃ e', a.eval σ = .error e' := by
        rcases h' with h' | h'
        · exact ⟨e, (Tm.eq_of_beqR h') ▸ hS⟩
        · exact iha h'
      first
        | exact ⟨e', by show Op3.eval _ _ (a.eval σ) (b.eval σ) (c.eval σ) = _; rw [ha]; rfl⟩
        | (show ∃ e'', Op3.eval _ _ (a.eval σ) (b.eval σ) (c.eval σ) = _
           rw [ha]
           generalize c.eval σ = r
           cases r <;> exact ⟨_, rfl⟩)

/-- A term on the spine of `S` halts wherever `S` does. -/
theorem Tm.onSpineS_error {S : Tm C Γ .st} {σ : State C Γ} {e : Semantics.Halt}
    (hS : S.eval σ = .error e) (T : Tm C Γ .st) (h : T.onSpineS S = true) :
    ∃ e', T.eval σ = .error e' := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rw [Tm.eq_of_beqR h]; exact ⟨e, hS⟩
  · exact Tm.spineHas_haltsM hS T (Tm.spineHas_eq_spineHasM S T ▸ h)

/-- A term with `M` on its memory spine halts wherever `M` does. -/
theorem Tm.memSpineHas_haltsM {M : Tm C Γ .mem} {σ : State C Γ} {e : Semantics.Halt}
    (hM : M.eval σ = .error e) {s : Srt} (N : Tm C Γ s) (h : Tm.memSpineHasM M N = true) :
    Srt.Halts s (N.eval σ) := by
  induction N with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ _ | app0 _ => exact absurd h Bool.false_ne_true
  | app1 o ho a iha =>
    simp only [Tm.memSpineHasM, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨ho', h'⟩ := h
    cases o <;> simp only [Op1.memSpine, Bool.false_eq_true] at ho'
    all_goals
      obtain ⟨e', ha⟩ : ∃ e', a.eval σ = .error e' := by
        rcases h' with h' | h'
        · exact ⟨e, (Tm.eq_of_beqR h') ▸ hM⟩
        · exact iha h'
      exact ⟨e', by show Op1.eval _ _ (a.eval σ) = _; rw [ha]; rfl⟩
  | app2 o a b iha _ =>
    simp only [Tm.memSpineHasM, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨ho', h'⟩ := h
    cases o <;> simp only [Op2.memSpine, Bool.false_eq_true] at ho'
    all_goals
      obtain ⟨e', ha⟩ : ∃ e', a.eval σ = .error e' := by
        rcases h' with h' | h'
        · exact ⟨e, (Tm.eq_of_beqR h') ▸ hM⟩
        · exact iha h'
      first
        | exact ⟨e', by show Op2.eval _ _ (a.eval σ) (b.eval σ) = _; rw [ha]; rfl⟩
        | (show ∃ e'', Op2.eval _ _ (a.eval σ) (b.eval σ) = _
           rw [ha]
           generalize b.eval σ = r
           cases r <;> exact ⟨_, rfl⟩)
  | app3 o a b c iha _ _ =>
    simp only [Tm.memSpineHasM, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨ho', h'⟩ := h
    cases o <;> simp only [Op3.memSpine, Bool.false_eq_true] at ho'
    all_goals
      obtain ⟨e', ha⟩ : ∃ e', a.eval σ = .error e' := by
        rcases h' with h' | h'
        · exact ⟨e, (Tm.eq_of_beqR h') ▸ hM⟩
        · exact iha h'
      first
        | exact ⟨e', by show Op3.eval _ _ (a.eval σ) (b.eval σ) (c.eval σ) = _; rw [ha]; rfl⟩
        | (show ∃ e'', Op3.eval _ _ (a.eval σ) (b.eval σ) (c.eval σ) = _
           rw [ha]
           generalize c.eval σ = r
           cases r <;> exact ⟨_, rfl⟩)

/-- A term on the memory spine of `M` halts wherever `M` does. -/
theorem Tm.onMemSpineS_error {M : Tm C Γ .mem} {σ : State C Γ} {e : Semantics.Halt}
    (hM : M.eval σ = .error e) (N : Tm C Γ .mem) (h : N.onMemSpineS M = true) :
    ∃ e', N.eval σ = .error e' := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rw [Tm.eq_of_beqR h]; exact ⟨e, hM⟩
  · exact Tm.memSpineHas_haltsM hM N (Tm.memSpineHas_eq_memSpineHasM M N ▸ h)

/-- The update with each storage write whose storage a later one reads first
dropped (`P` the storage terms written later), and so each memory write
(`Q`). -/
def Upd.dropSh (P : List (Tm C Γ .st)) (Q : List (Tm C Γ .mem)) :
    {Δ : Ctx} → Upd C Γ Δ → Upd C Γ Δ
  | _, .nil => .nil
  | _, .snoc U e => match e with
    | .storage S =>
      if P.any (·.onSpineS S) then Upd.dropSh P Q U else .snoc (Upd.dropSh (S :: P) Q U) (.storage S)
    | .memory M =>
      if Q.any (·.onMemSpineS M) then Upd.dropSh P Q U else .snoc (Upd.dropSh P (M :: Q) U) (.memory M)
    | e => .snoc (Upd.dropSh P Q U) e
  | _, .decl U x r => .decl (Upd.dropSh P Q U) x r
  | _, .pop U h => .pop (Upd.dropSh P Q U) h
  | _, .drop U h => .drop (Upd.dropSh P Q U) h

/-- A global part with its storage and memory replaced. -/
abbrev Semantics.State.withSHN (τ : Semantics.State) (st : List (Name × Semantics.SVal))
    (hp : List (Nat × Semantics.MObj)) (n : Nat) : Semantics.State :=
  { τ with storage := st, heap := hp, nextId := n }

/-- An element that writes neither the storage nor the memory computes alike
from a global part with another storage and memory. -/
theorem UpdElem.globT_withSHN {Δ : Ctx} (σ₀ : State C Γ) (st : List (Name × Semantics.SVal))
    (hp : List (Nat × Semantics.MObj)) (n : Nat) (τ : Semantics.State) :
    (e : UpdElem C Γ Δ) → (∀ S, e ≠ .storage S) → (∀ M, e ≠ .memory M) →
      e.globT σ₀ (τ.withSHN st hp n) = (e.globT σ₀ τ).map (·.withSHN st hp n)
  | .local i r, _, _ => by
    simp only [UpdElem.globT]
    cases r.eval σ₀ <;> rfl
  | .storage S, h, _ => absurd rfl (h S)
  | .memory M, _, h => absurd rfl (h M)
  | .selfBalance op a, _, _ => by
    simp only [UpdElem.globT]
    cases a.eval σ₀ with
    | error => rfl
    | ok v => cases v <;> rfl
  | .net r op a, _, _ => by
    simp only [UpdElem.globT]
    cases r.eval σ₀ with
    | error => rfl
    | ok v =>
      cases v with
      | bool => rfl
      | int =>
        cases a.eval σ₀ with
        | error => rfl
        | ok w => cases w <;> rfl
  | .pay r a, _, _ => by
    simp only [UpdElem.globT]
    cases r.eval σ₀ with
    | error => rfl
    | ok v =>
      cases v with
      | bool => rfl
      | int =>
        cases a.eval σ₀ with
        | error => rfl
        | ok w =>
          cases w with
          | bool => rfl
          | int =>
            simp only [bind, Except.bind, Semantics.Value.asInt, pure, Except.pure]
            split <;> rfl
  | .netMt r a, _, _ => by
    simp only [UpdElem.globT]
    cases r.eval σ₀ with
    | error => rfl
    | ok v =>
      cases v with
      | bool => rfl
      | int =>
        cases a.eval σ₀ with
        | error => rfl
        | ok w => cases w <;> rfl
  | .setBalance a, _, _ => by
    simp only [UpdElem.globT]
    cases a.eval σ₀ with
    | error => rfl
    | ok v => cases v <;> rfl

theorem UpdElem.globT_storage_ok {Δ : Ctx} {σ₀ : State C Γ} {S : Tm C Γ .st}
    {g : Semantics.State} (hs : S.eval σ₀ = .ok g) (τ : Semantics.State) :
    (UpdElem.storage S : UpdElem C Γ Δ).globT σ₀ τ = .ok { τ with storage := g.storage } := by
  simp only [UpdElem.globT, hs]; rfl

theorem UpdElem.globT_storage_error {Δ : Ctx} {σ₀ : State C Γ} {S : Tm C Γ .st}
    {e : Semantics.Halt} (hs : S.eval σ₀ = .error e) (τ : Semantics.State) :
    (UpdElem.storage S : UpdElem C Γ Δ).globT σ₀ τ = .error e := by
  simp only [UpdElem.globT, hs]; rfl

theorem UpdElem.globT_memory_ok {Δ : Ctx} {σ₀ : State C Γ} {M : Tm C Γ .mem}
    {g : Semantics.State} (hs : M.eval σ₀ = .ok g) (τ : Semantics.State) :
    (UpdElem.memory M : UpdElem C Γ Δ).globT σ₀ τ =
      .ok { τ with heap := g.heap, nextId := g.nextId } := by
  simp only [UpdElem.globT, hs]; rfl

theorem UpdElem.globT_memory_error {Δ : Ctx} {σ₀ : State C Γ} {M : Tm C Γ .mem}
    {e : Semantics.Halt} (hs : M.eval σ₀ = .error e) (τ : Semantics.State) :
    (UpdElem.memory M : UpdElem C Γ Δ).globT σ₀ τ = .error e := by
  simp only [UpdElem.globT, hs]; rfl

/-- How the global part an update computes and the one with the shadowed
writes dropped (`P`, `Q` the writes still to come) relate: one but for the
storage (where a write is to come) and the memory, or both halted, or the
first halted on a write whose shadowing write halts too. -/
def ShRel (σ₀ : State C Γ) (P : List (Tm C Γ .st)) (Q : List (Tm C Γ .mem))
    (a b : Res Semantics.State) : Prop :=
  (∃ τ st hp n, a = .ok τ ∧ b = .ok (τ.withSHN st hp n) ∧ (P = [] → st = τ.storage) ∧
      (Q = [] → hp = τ.heap ∧ n = τ.nextId)) ∨
    ((∃ e, a = .error e) ∧ ((∃ e, b = .error e) ∨ (∃ T ∈ P, ∃ e, T.eval σ₀ = .error e) ∨
      (∃ M ∈ Q, ∃ e, M.eval σ₀ = .error e)))

theorem ShRel.bind_globT {σ₀ : State C Γ} {P : List (Tm C Γ .st)} {Q : List (Tm C Γ .mem)}
    {Δ : Ctx} {a b : Res Semantics.State} (h : ShRel σ₀ P Q a b) (e : UpdElem C Γ Δ)
    (hS : ∀ S, e ≠ .storage S) (hM : ∀ M, e ≠ .memory M) :
    ShRel σ₀ P Q (a >>= e.globT σ₀) (b >>= e.globT σ₀) := by
  rcases h with ⟨τ, st, hp, n, rfl, rfl, h₁, h₂⟩ | ⟨⟨e₁, rfl⟩, h⟩
  · show ShRel σ₀ P Q (e.globT σ₀ τ) (e.globT σ₀ (τ.withSHN st hp n))
    rw [UpdElem.globT_withSHN σ₀ st hp n τ e hS hM]
    have hτ := UpdElem.globT_withSHN σ₀ τ.storage τ.heap τ.nextId τ e hS hM
    cases hw : e.globT σ₀ τ with
    | error e₂ => exact .inr ⟨⟨e₂, rfl⟩, .inl ⟨e₂, rfl⟩⟩
    | ok ρ =>
      rw [hw] at hτ
      have hρ : ρ = ρ.withSHN τ.storage τ.heap τ.nextId := by
        simp only [Except.map] at hτ; exact Except.ok.inj hτ
      refine .inl ⟨ρ, st, hp, n, rfl, rfl, fun hP => ?_, fun hQ => ?_⟩
      · rw [h₁ hP, hρ]
      · obtain ⟨rfl, rfl⟩ := h₂ hQ; rw [hρ]; exact ⟨rfl, rfl⟩
  · refine .inr ⟨⟨e₁, rfl⟩, ?_⟩
    rcases h with ⟨e₂, rfl⟩ | h
    · exact .inl ⟨e₂, rfl⟩
    · exact .inr h

/-- **Dropping the shadowed writes leaves the global part, or a halt a
halt.** -/
theorem Upd.dropSh_rel (σ₀ : State C Γ) : {Δ : Ctx} → (U : Upd C Γ Δ) →
    (P : List (Tm C Γ .st)) → (Q : List (Tm C Γ .mem)) →
      ShRel σ₀ P Q (U.globT σ₀) ((U.dropSh P Q).globT σ₀)
  | _, .nil, P, Q => .inl ⟨σ₀.globE, σ₀.globE.storage, σ₀.globE.heap, σ₀.globE.nextId, rfl, rfl,
      fun _ => rfl, fun _ => ⟨rfl, rfl⟩⟩
  | Δ₁, .snoc U (.storage S), P, Q => by
    simp only [Upd.dropSh]
    split
    · rename_i hP
      obtain ⟨T, hT, hTS⟩ := List.any_eq_true.1 hP
      show ShRel σ₀ P Q (U.globT σ₀ >>= UpdElem.globT (Δ := Δ₁) σ₀ (.storage S)) ((U.dropSh P Q).globT σ₀)
      rcases Upd.dropSh_rel σ₀ U P Q with ⟨τ, st, hp, n, ha, hb, h₁, h₂⟩ | ⟨⟨e₁, ha⟩, h⟩
      · rw [ha, hb]
        show ShRel σ₀ P Q (UpdElem.globT (Δ := Δ₁) σ₀ (.storage S) τ) _
        cases hs : S.eval σ₀ with
        | error e₂ =>
          rw [UpdElem.globT_storage_error hs]
          exact .inr ⟨⟨e₂, rfl⟩, .inr (.inl ⟨T, hT, Tm.onSpineS_error hs T hTS⟩)⟩
        | ok g =>
          rw [UpdElem.globT_storage_ok hs]
          refine .inl ⟨{ τ with storage := g.storage }, st, hp, n, rfl, rfl,
            fun hP' => absurd hP' (List.ne_nil_of_mem hT), fun hQ => ?_⟩
          obtain ⟨rfl, rfl⟩ := h₂ hQ; exact ⟨rfl, rfl⟩
      · rw [ha]
        exact .inr ⟨⟨e₁, rfl⟩, h⟩
    · show ShRel σ₀ P Q (U.globT σ₀ >>= UpdElem.globT (Δ := Δ₁) σ₀ (.storage S))
        ((U.dropSh (S :: P) Q).globT σ₀ >>= UpdElem.globT (Δ := Δ₁) σ₀ (.storage S))
      rcases Upd.dropSh_rel σ₀ U (S :: P) Q with ⟨τ, st, hp, n, ha, hb, h₁, h₂⟩ | ⟨⟨e₁, ha⟩, h⟩
      · rw [ha, hb]
        show ShRel σ₀ P Q (UpdElem.globT (Δ := Δ₁) σ₀ (.storage S) τ)
          (UpdElem.globT (Δ := Δ₁) σ₀ (.storage S) (τ.withSHN st hp n))
        cases hs : S.eval σ₀ with
        | error e₂ =>
          rw [UpdElem.globT_storage_error hs, UpdElem.globT_storage_error hs]
          exact .inr ⟨⟨e₂, rfl⟩, .inl ⟨e₂, rfl⟩⟩
        | ok g =>
          rw [UpdElem.globT_storage_ok hs, UpdElem.globT_storage_ok hs]
          refine .inl ⟨{ τ with storage := g.storage }, g.storage, hp, n, rfl, rfl,
            fun _ => rfl, fun hQ => ?_⟩
          obtain ⟨rfl, rfl⟩ := h₂ hQ; exact ⟨rfl, rfl⟩
      · rw [ha]
        refine .inr ⟨⟨e₁, rfl⟩, ?_⟩
        rcases h with ⟨e₂, hb⟩ | ⟨T, hT, e₂, hTe⟩ | hM
        · rw [hb]; exact .inl ⟨e₂, rfl⟩
        · rcases List.mem_cons.1 hT with rfl | hT
          · cases hb : (U.dropSh (T :: P) Q).globT σ₀ with
            | error e₃ => exact .inl ⟨e₃, rfl⟩
            | ok ρ => exact .inl ⟨e₂, UpdElem.globT_storage_error (Δ := Δ₁) hTe ρ⟩
          · exact .inr (.inl ⟨T, hT, e₂, hTe⟩)
        · exact .inr (.inr hM)
  | Δ₁, .snoc U (.memory M), P, Q => by
    simp only [Upd.dropSh]
    split
    · rename_i hQ
      obtain ⟨N, hN, hNM⟩ := List.any_eq_true.1 hQ
      show ShRel σ₀ P Q (U.globT σ₀ >>= UpdElem.globT (Δ := Δ₁) σ₀ (.memory M)) ((U.dropSh P Q).globT σ₀)
      rcases Upd.dropSh_rel σ₀ U P Q with ⟨τ, st, hp, n, ha, hb, h₁, h₂⟩ | ⟨⟨e₁, ha⟩, h⟩
      · rw [ha, hb]
        show ShRel σ₀ P Q (UpdElem.globT (Δ := Δ₁) σ₀ (.memory M) τ) _
        cases hs : M.eval σ₀ with
        | error e₂ =>
          rw [UpdElem.globT_memory_error hs]
          exact .inr ⟨⟨e₂, rfl⟩, .inr (.inr ⟨N, hN, Tm.onMemSpineS_error hs N hNM⟩)⟩
        | ok g =>
          rw [UpdElem.globT_memory_ok hs]
          refine .inl ⟨{ τ with heap := g.heap, nextId := g.nextId }, st, hp, n, rfl,
            rfl, fun hP => ?_, fun hQ' => absurd hQ' (List.ne_nil_of_mem hN)⟩
          rw [h₁ hP]
      · rw [ha]
        exact .inr ⟨⟨e₁, rfl⟩, h⟩
    · show ShRel σ₀ P Q (U.globT σ₀ >>= UpdElem.globT (Δ := Δ₁) σ₀ (.memory M))
        ((U.dropSh P (M :: Q)).globT σ₀ >>= UpdElem.globT (Δ := Δ₁) σ₀ (.memory M))
      rcases Upd.dropSh_rel σ₀ U P (M :: Q) with ⟨τ, st, hp, n, ha, hb, h₁, h₂⟩ | ⟨⟨e₁, ha⟩, h⟩
      · rw [ha, hb]
        show ShRel σ₀ P Q (UpdElem.globT (Δ := Δ₁) σ₀ (.memory M) τ)
          (UpdElem.globT (Δ := Δ₁) σ₀ (.memory M) (τ.withSHN st hp n))
        cases hs : M.eval σ₀ with
        | error e₂ =>
          rw [UpdElem.globT_memory_error hs, UpdElem.globT_memory_error hs]
          exact .inr ⟨⟨e₂, rfl⟩, .inl ⟨e₂, rfl⟩⟩
        | ok g =>
          rw [UpdElem.globT_memory_ok hs, UpdElem.globT_memory_ok hs]
          refine .inl ⟨{ τ with heap := g.heap, nextId := g.nextId }, st, g.heap,
            g.nextId, rfl, rfl, fun hP => ?_, fun _ => ⟨rfl, rfl⟩⟩
          rw [h₁ hP]
      · rw [ha]
        refine .inr ⟨⟨e₁, rfl⟩, ?_⟩
        rcases h with ⟨e₂, hb⟩ | hP | ⟨N, hN, e₂, hNe⟩
        · rw [hb]; exact .inl ⟨e₂, rfl⟩
        · exact .inr (.inl hP)
        · rcases List.mem_cons.1 hN with rfl | hN
          · cases hb : (U.dropSh P (N :: Q)).globT σ₀ with
            | error e₃ => exact .inl ⟨e₃, rfl⟩
            | ok ρ => exact .inl ⟨e₂, UpdElem.globT_memory_error (Δ := Δ₁) hNe ρ⟩
          · exact .inr (.inr ⟨N, hN, e₂, hNe⟩)
  | _, .snoc U (.local i r), P, Q =>
    (Upd.dropSh_rel σ₀ U P Q).bind_globT _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  | _, .snoc U (.selfBalance op a), P, Q =>
    (Upd.dropSh_rel σ₀ U P Q).bind_globT _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  | _, .snoc U (.net r op a), P, Q =>
    (Upd.dropSh_rel σ₀ U P Q).bind_globT _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  | _, .snoc U (.pay r a), P, Q =>
    (Upd.dropSh_rel σ₀ U P Q).bind_globT _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  | _, .snoc U (.netMt r a), P, Q =>
    (Upd.dropSh_rel σ₀ U P Q).bind_globT _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  | _, .snoc U (.setBalance a), P, Q =>
    (Upd.dropSh_rel σ₀ U P Q).bind_globT _ (fun _ h => nomatch h) (fun _ h => nomatch h)
  | _, .decl U x r, P, Q => by
    have ih := Upd.dropSh_rel σ₀ U P Q
    show ShRel σ₀ P Q (do let g ← U.globT σ₀; let _ ← r.eval σ₀; pure g)
      (do let g ← (U.dropSh P Q).globT σ₀; let _ ← r.eval σ₀; pure g)
    rcases ih with ⟨τ, st, hp, n, ha, hb, h₁, h₂⟩ | ⟨⟨e₁, ha⟩, h⟩
    · rw [ha, hb]
      cases hr : r.eval σ₀ with
      | error e₂ => exact .inr ⟨⟨e₂, rfl⟩, .inl ⟨e₂, rfl⟩⟩
      | ok w => exact .inl ⟨τ, st, hp, n, rfl, rfl, h₁, h₂⟩
    · rw [ha]
      refine .inr ⟨⟨e₁, rfl⟩, ?_⟩
      rcases h with ⟨e₂, hb⟩ | h
      · rw [hb]
        cases r.eval σ₀ <;> exact .inl ⟨e₂, rfl⟩
      · exact .inr h
  | _, .pop U _, P, Q => Upd.dropSh_rel σ₀ U P Q
  | _, .drop U _, P, Q => Upd.dropSh_rel σ₀ U P Q

/-- Dropping the shadowed writes leaves every local as it was. -/
theorem Upd.dropSh_held : {Δ : Ctx} → (U : Upd C Γ Δ) → (P : List (Tm C Γ .st)) →
    (Q : List (Tm C Γ .mem)) → ∀ {t : LTy} (i : Idx Δ t), (U.dropSh P Q).held i = U.held i
  | _, .nil, _, _, _, _ => rfl
  | _, .snoc U (.storage S), P, Q, _, i => by
    simp only [Upd.dropSh]
    split
    · exact Upd.dropSh_held U P Q i
    · exact Upd.dropSh_held U (S :: P) Q i
  | _, .snoc U (.memory M), P, Q, _, i => by
    simp only [Upd.dropSh]
    split
    · exact Upd.dropSh_held U P Q i
    · exact Upd.dropSh_held U P (M :: Q) i
  | _, .snoc U (.local k r), P, Q, _, i => by
    show Subst.set (Upd.held (U.dropSh P Q)) k r i = Subst.set (Upd.held U) k r i
    unfold Subst.set
    split
    · rfl
    · exact Upd.dropSh_held U P Q i
  | _, .snoc U (.selfBalance _ _), P, Q, _, i | _, .snoc U (.net _ _ _), P, Q, _, i
  | _, .snoc U (.pay _ _), P, Q, _, i | _, .snoc U (.netMt _ _), P, Q, _, i
  | _, .snoc U (.setBalance _), P, Q, _, i => Upd.dropSh_held U P Q i
  | _, .decl U x r, P, Q, _, i => by
    cases i with
    | here => rfl
    | there j => exact Upd.dropSh_held U P Q j
  | _, .pop U e, P, Q, _, i => Upd.dropSh_held U P Q (i.ext e)
  | _, .drop U e, P, Q, _, i => Upd.dropSh_held U P Q (i.wk e)

/-- **`{U} φ` from `U` with its shadowed writes dropped.** -/
theorem holds_upd_dropSh {m : Modality} {Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ} (σ : State C Γ)
    (h : holds σ (.upd m (U.dropSh [] []) φ)) : holds σ (.upd m U φ) := by
  have hr := Upd.dropSh_rel σ U [] []
  refine Upd.afterT_of_lands (fun e he h' => ?_) (fun g σ' hL => ?_) h
  · rcases hr with ⟨τ, _, _, _, ha, _⟩ | ⟨_, h'' | ⟨_, hT, _⟩ | ⟨_, hM, _⟩⟩
    · rw [he] at ha; cases ha
    · obtain ⟨e₂, hb⟩ := h''
      exact h'.of_error hb
    · nomatch hT
    · nomatch hM
  · refine ⟨?_, hL.2.1, fun i => ?_⟩
    · rcases hr with ⟨τ, st, hp, n, ha, hb, h₁, h₂⟩ | ⟨⟨e₁, ha⟩, _⟩
      · rw [hL.1] at ha
        cases ha
        obtain ⟨rfl, rfl⟩ := h₂ rfl
        rw [h₁ rfl] at hb
        exact hb
      · rw [hL.1] at ha; cases ha
    · rw [Upd.dropSh_held]
      exact hL.2.2 i

end Shadow

/-! ## Two updates merged -/

section Merge

/-- The modality `{U}_m {V}_m'` merges under: theirs where they agree, the
other's where one cannot halt (`Upd.totalB`, `ut`, `vt`). -/
def Modality.mergeP (m : Modality) (ut : Bool) (m' : Modality) (vt : Bool) : Option Modality :=
  if m' = m then some m else if ut then some m' else if vt then some m else none

/-- An update that cannot halt reads alike under either modality. -/
theorem holds_upd_total {m m' : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} (hU : U.totalB = true)
    {φ : Fml C Δ} (σ : State C Γ) (h : holds σ (.upd m U φ)) : holds σ (.upd m' U φ) := by
  obtain ⟨g, hg⟩ := Upd.totalB_globT σ U hU
  refine Upd.afterT_intro (fun e he => ?_) fun _ σ' hL hH => h.of_lands hL hH
  rw [hg] at he; cases he

/-- `{U}{V}` as one update, by the first merge that reads it: `V` read in
`U`'s state (`Upd.seqPar`), over a storage write (`Upd.mergeSt?`), a memory
write (`Upd.mergeMem?`), locals then a memory write (`Upd.mergeMemL?`). -/
def Upd.mergeK? {Γ Δ₁ Δ₂ : Ctx} (U : Upd C Γ Δ₁) (V : Upd C Δ₁ Δ₂) : Option (Upd C Γ Δ₂) :=
  match U.seqPar V with
  | some W => some W
  | none => match U.mergeSt? V with
    | some W => some W
    | none => match U.mergeMem? V with
      | some W => some W
      | none => U.mergeMemL? V

theorem holds_upd_mergeK {m : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {W : Upd C Γ Δ₂} (hW : U.mergeK? V = some W) {φ : Fml C Δ₂} (σ : State C Γ)
    (h : holds σ (.upd m W φ)) : holds σ (.upd m U (.upd m V φ)) := by
  unfold Upd.mergeK? at hW
  split at hW
  · rename_i hs; cases hW; exact holds_upd_seqPar hs σ h
  · split at hW
    · rename_i hs; cases hW; exact holds_upd_mergeSt hs σ h
    · split at hW
      · rename_i hs; cases hW; exact holds_upd_mergeMem hs σ h
      · exact holds_upd_mergeMemL hW σ h

/-- **`sequentialToParallel` past the program**: `{U}_m {V}_m'` as one
update and its modality, the shadowed state writes dropped. -/
def Upd.mergeP? {Γ Δ₁ Δ₂ : Ctx} (m : Modality) (U : Upd C Γ Δ₁) (m' : Modality)
    (V : Upd C Δ₁ Δ₂) : Option (Modality × Upd C Γ Δ₂) :=
  (Modality.mergeP m U.totalB m' V.totalB).bind fun mm =>
    (U.mergeK? V).map fun W => (mm, W.dropSh [] [])

theorem holds_upd_mergeP {m m' : Modality} {Γ Δ₁ Δ₂ : Ctx} {U : Upd C Γ Δ₁} {V : Upd C Δ₁ Δ₂}
    {r : Modality × Upd C Γ Δ₂} (hr : Upd.mergeP? m U m' V = some r) {φ : Fml C Δ₂}
    (σ : State C Γ) (h : holds σ (.upd r.1 r.2 φ)) : holds σ (.upd m U (.upd m' V φ)) := by
  obtain ⟨mm, hmm, hr⟩ := Option.bind_eq_some_iff.1 hr
  obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 hr
  have h₂ : holds σ (.upd mm U (.upd mm V φ)) := holds_upd_mergeK hW σ (holds_upd_dropSh σ h)
  unfold Modality.mergeP at hmm
  split at hmm
  · rename_i he; cases hmm; rw [he]; exact h₂
  · split at hmm
    · rename_i hu; cases hmm; exact holds_upd_total hu σ h₂
    · split at hmm
      · rename_i hv; cases hmm
        exact holds_upd_mono (fun τ hτ => holds_upd_total hv τ hτ) σ h₂
      · cases hmm

/-- `{U}_m bind x ψ` merged where `ψ` is an update that sets `x` first: the
binder absorbed (`Upd.absorb`), then the two merged. -/
def Fml.absorbMergeP (m : Modality) {Γ Δ : Ctx} (U : Upd C Γ Δ) (x : Var) {t : LTy}
    (ψ : Fml C (t :: Δ)) : Option (Fml C Γ) :=
  match ψ with
  | .upd m'' V χ => (V.absorb x).bind fun V' => (Upd.mergeP? m U m'' V').map fun r => .upd r.1 r.2 χ
  | _ => none

theorem Fml.absorbMergeP_sound {m m' : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} {x : Var} {t : LTy}
    {ψ : Fml C (t :: Δ)} {φ : Fml C Γ} (h : Fml.absorbMergeP m U x ψ = some φ) (σ : State C Γ)
    (hφ : holds σ φ) : holds σ (.upd m U (.bind m' x t ψ)) := by
  unfold Fml.absorbMergeP at h
  split at h
  · rename_i m'' V χ
    obtain ⟨V', hV', h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
    exact holds_upd_mono (fun τ hτ => holds_bind_absorb hV' τ hτ) σ (holds_upd_mergeP hr σ hφ)
  · cases h

/-- `bind x ψ` with its local absorbed into the update `ψ` begins with,
where that update sets it before reading it (`Upd.absorb`). -/
def Fml.absorbBind {Δ : Ctx} (m : Modality) (x : Var) (t : LTy) : Fml C (t :: Δ) → Fml C Δ
  | .upd m'' V χ => match V.absorb x true with
    | some V' => .upd m'' V' χ
    | none => .bind m x t (.upd m'' V χ)
  | ψ => .bind m x t ψ

theorem Fml.absorbBind_holds {Δ : Ctx} {m : Modality} {x : Var} {t : LTy} (ψ : Fml C (t :: Δ))
    (σ : State C Δ) (h : holds σ (Fml.absorbBind m x t ψ)) : holds σ (.bind m x t ψ) := by
  unfold Fml.absorbBind at h
  split at h
  · rename_i m'' V χ
    split at h
    · rename_i V' hV
      exact holds_bind_absorb hV σ h
    · exact h
  · exact h

/-- The hidden binders a formula begins with absorbed, innermost first, into
the update under them (`Fml.absorbBind`). -/
def Fml.absorbBinds : {Δ : Ctx} → Fml C Δ → Fml C Δ
  | _, .bind m x t ψ => Fml.absorbBind m x t (Fml.absorbBinds ψ)
  | _, φ => φ

theorem Fml.absorbBinds_holds : {Δ : Ctx} → (φ : Fml C Δ) → (σ : State C Δ) →
    holds σ (Fml.absorbBinds φ) → holds σ φ
  | _, .bind m x t ψ, σ, h => by
    have h' := Fml.absorbBind_holds (Fml.absorbBinds ψ) σ h
    exact Modality.forallB_imp (fun w hw => Fml.absorbBinds_holds ψ _ hw) h'
  | _, .tt, _, h | _, .eq .., _, h | _, .defined _, _, h | _, .not _, _, h | _, .and .., _, h
  | _, .imp .., _, h | _, .upd .., _, h | _, .modal .., _, h | _, .havoc _, _, h
  | _, .all .., _, h | _, .anon .., _, h => h

/-- `{U}_m φ` merged with the update `φ` begins with once the hidden binders
in front of it are absorbed into it, innermost first (`Fml.absorbBinds`): a
local an update sets after declaring others is declared before them. -/
def Fml.absorbAllMergeP (m : Modality) {Γ Δ : Ctx} (U : Upd C Γ Δ) (φ : Fml C Δ) :
    Option (Fml C Γ) :=
  match Fml.absorbBinds φ with
  | .upd m'' V χ => (Upd.mergeP? m U m'' V).map fun r => .upd r.1 r.2 χ
  | _ => none

theorem Fml.absorbAllMergeP_sound {m : Modality} {Γ Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ}
    {ψ : Fml C Γ} (h : Fml.absorbAllMergeP m U φ = some ψ) (σ : State C Γ) (hψ : holds σ ψ) :
    holds σ (.upd m U φ) := by
  unfold Fml.absorbAllMergeP at h
  split at h
  · rename_i m'' V χ hab
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
    refine holds_upd_mono (fun τ hτ => Fml.absorbBinds_holds φ τ ?_) σ (holds_upd_mergeP hr σ hψ)
    rw [hab]
    exact hτ
  · cases h

/-- `{U}_m φ` merged with the update at the head of `φ`, through a hidden
binder: absorbed where the update sets its local first (`Fml.absorbMergeP`),
or `U` moved under it with its scope ends (`Upd.liftG?`, as
`Calculus/Merge.lean`'s `Fml.merge2` moves one); with `reorder`, first every
binder absorbed, which may declare a local before the ones its update
declares first (`Fml.absorbAllMergeP`). -/
def Fml.merge2P (m : Modality) (reorder : Bool) :
    {Γ Δ : Ctx} → Upd C Γ Δ → Fml C Δ → Option (Fml C Γ)
  | _, _, U, .upd m' V ψ => (Upd.mergeP? m U m' V).map fun r => .upd r.1 r.2 ψ
  | _, _, U, .bind m' x t ψ =>
    match Fml.absorbMergeP m U x ψ with
    | some φ => some φ
    | none =>
      match (if reorder then Fml.absorbAllMergeP m U (.bind m' x t ψ) else none) with
      | some φ => some φ
      | none =>
        if (t.notMem || U.keepsNext) = true then
          (U.liftG? (t := t)).bind fun U' => (Fml.merge2P m reorder U' ψ).map (.bind m' x t)
        else none
  | _, _, _, _ => none

theorem Fml.merge2P_sound {m : Modality} {reorder : Bool} : {Γ Δ : Ctx} → (U : Upd C Γ Δ) →
    (φ : Fml C Δ) → {ψ : Fml C Γ} → Fml.merge2P m reorder U φ = some ψ →
      ∀ σ, holds σ ψ → holds σ (.upd m U φ)
  | _, _, U, .upd m' V χ, ψ, h => by
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hψ => holds_upd_mergeP hr σ hψ
  | _, _, U, .bind m' x t χ, ψ, h => by
    simp only [Fml.merge2P] at h
    split at h
    · rename_i φ hφ
      cases h
      exact fun σ hψ => Fml.absorbMergeP_sound hφ σ hψ
    · split at h
      · rename_i φ' hφ'
        cases h
        split at hφ'
        · exact fun σ hψ => Fml.absorbAllMergeP_sound hφ' σ hψ
        · cases hφ'
      · split at h
        · rename_i ht
          obtain ⟨U', hU', h⟩ := Option.bind_eq_some_iff.1 h
          obtain ⟨χ', hχ', rfl⟩ := Option.map_eq_some_iff.1 h
          intro σ hψ
          exact Fml.upd_bind_of_liftG hU' ht σ
            (Modality.forallB_imp (fun v h => Fml.merge2P_sound U' χ hχ' _ h) hψ)
        · cases h
  | _, _, _, .tt, _, h | _, _, _, .eq .., _, h | _, _, _, .defined _, _, h | _, _, _, .not _, _, h
  | _, _, _, .and .., _, h | _, _, _, .imp .., _, h | _, _, _, .modal .., _, h
  | _, _, _, .havoc _, _, h | _, _, _, .all .., _, h | _, _, _, .anon .., _, h => nomatch h

/-- `sequentialToParallel` past the program on the updates at positions `k`
and `k + 1` of the line's update spine, under its quantifiers and hidden
binders. -/
def Fml.mergeAtP {Γ : Ctx} (reorder : Bool) : Nat → Fml C Γ → Option (Fml C Γ)
  | k, .all x p φ => (Fml.mergeAtP reorder k φ).map (.all x p)
  | k, .bind m x t φ => (Fml.mergeAtP reorder k φ).map (.bind m x t)
  | 0, .upd m U φ => Fml.merge2P m reorder U φ
  | k + 1, .upd m U φ => (Fml.mergeAtP reorder k φ).map (.upd m U)
  | _, _ => none

/-- `Fml.mergeAtP` `n` times: the `n + 1` updates from position `k` merged
into one, the innermost pair first (a merge over
a memory write asks the write last in the update before, which the pair
after it is merged into first). -/
def Fml.mergeRunP {Γ : Ctx} (reorder : Bool) (k : Nat) : Nat → Fml C Γ → Option (Fml C Γ)
  | 0, φ => some φ
  | n + 1, φ => (φ.mergeAtP reorder (k + n)).bind (Fml.mergeRunP reorder k n)

theorem Fml.mergeAtP_sound (reorder : Bool) : {Γ : Ctx} → (k : Nat) → (φ : Fml C Γ) → {ψ : Fml C Γ} →
    φ.mergeAtP reorder k = some ψ → ∀ σ, holds σ ψ → holds σ φ
  | _, k, .all x p φ, ψ₀, h => by
    have h : (Fml.mergeAtP reorder k φ).map (Fml.all x p) = some ψ₀ := by rw [← h]; cases k <;> rfl
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs v => Fml.mergeAtP_sound reorder k φ hψ _ (hs v)
  | _, k, .bind m x t φ, ψ₀, h => by
    have h : (Fml.mergeAtP reorder k φ).map (Fml.bind m x t) = some ψ₀ := by rw [← h]; cases k <;> rfl
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs => Modality.forallB_imp (fun v => Fml.mergeAtP_sound reorder k φ hψ _) hs
  | _, 0, .upd m U φ, _, h => Fml.merge2P_sound U φ h
  | _, k + 1, .upd m U φ, _, h => by
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs => Upd.afterT_imp hs fun σ' a => Fml.mergeAtP_sound reorder k φ hψ σ' a
  | _, k, .tt, _, h | _, k, .eq .., _, h | _, k, .defined _, _, h | _, k, .not _, _, h
  | _, k, .and .., _, h | _, k, .imp .., _, h | _, k, .modal .., _, h | _, k, .havoc _, _, h
  | _, k, .anon .., _, h => by
    cases k <;> cases h

theorem Fml.mergeRunP_sound {Γ : Ctx} (reorder : Bool) (k : Nat) : (n : Nat) → (φ : Fml C Γ) →
    {ψ : Fml C Γ} → φ.mergeRunP reorder k n = some ψ → ∀ σ, holds σ ψ → holds σ φ
  | 0, φ, _, h => by cases h; exact fun _ h => h
  | n + 1, φ, _, h => by
    obtain ⟨χ, hχ, h⟩ := Option.bind_eq_some_iff.1 h
    exact fun σ hψ => Fml.mergeAtP_sound reorder (k + n) φ hχ σ (Fml.mergeRunP_sound reorder k n χ h σ hψ)

/-- **`sequentialToParallel` past the program**: the `n + 1` updates from
position `k` of the spine merged (`Fml.mergeRunP`), each local where its
update declares it; where that leaves a hidden binder unmerged, every binder
absorbed (`Fml.absorbAllMergeP`: a local an update sets late is declared,
and printed, first). -/
def FmlRw.mergePast (k n : Nat) : FmlRw C where
  apply := fun φ => match φ.mergeRunP false k (n + 1) with
    | some ψ => some ψ
    | none => φ.mergeRunP true k (n + 1)
  sound := fun {_ φ _} h σ hψ => by
    split at h
    · cases h
      exact Fml.mergeRunP_sound false k (n + 1) φ (by assumption) σ hψ
    · exact Fml.mergeRunP_sound true k (n + 1) φ h σ hψ

end Merge

/-! ## A storage write applied to a first-order line (`applyStorageBox`)

`[{storage := S}] φ ⇝ φ[S/storage]`, `φ` first-order and every storage
read of it a `storage` term (`Tm.stExplicitS`).  An equation reads its terms
through `denote`, so the substitution is exact up to `Equiv`: `S` denotes
the storage its run leaves (`Tm.denote_eval`), and the rest of the state is
the one before (`Semantics.State.Keeps`, `Tm.eval_st_glob`). -/

section WithSt

variable {Γ : Ctx}

open Theory Theory.StValue

/-- `storage` replaced by `S`. -/
def Op0.withStS (S : Tm C Γ .st) : {s : Srt} → Op0 s → Tm C Γ s
  | _, .storage => S
  | _, .lit v => .app0 (.lit v)
  | _, .env k => .app0 (.env k)
  | _, .root r => .app0 (.root r)
  | _, .memory => .app0 .memory
  | _, .mtSt vs => .app0 (.mtSt vs)

/-- A term with `S` for every `storage`. -/
def Tm.withStS (S : Tm C Γ .st) : {s : Srt} → Tm C Γ s → Tm C Γ s
  | _, .pvV i => .pvV i
  | _, .pvP i => .pvP i
  | _, .pvS i => .pvS i
  | _, .pvI i => .pvI i
  | _, .netOf i a => .netOf i (Tm.withStS S a)
  | _, .app0 o => o.withStS S
  | _, .app1 o ho a => .app1 o ho (Tm.withStS S a)
  | _, .app2 o a b => .app2 o (Tm.withStS S a) (Tm.withStS S b)
  | _, .app3 o a b c => .app3 o (Tm.withStS S a) (Tm.withStS S b) (Tm.withStS S c)

/-- Every storage read of the term is a `storage` term, and no ledger
variable is read. -/
def Tm.stExplicitS : {s : Srt} → Tm C Γ s → Bool
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ => true
  | _, .netOf _ _ => false
  | _, .app0 o => o.stExplicit
  | _, .app1 o _ a => o.stExplicit && a.stExplicitS
  | _, .app2 o a b => o.stExplicit && a.stExplicitS && b.stExplicitS
  | _, .app3 _ a b c => a.stExplicitS && b.stExplicitS && c.stExplicitS

variable {σ σ' : State C Γ} {S : Tm C Γ .st} {τ : Semantics.State}

/-- **Read before `{storage := S}`, the substituted term reads what the term
reads in every typed state it lands on.** -/
theorem Tm.withStS_eval (hs : S.eval σ = .ok τ) (hk : σ.globE.Keeps τ)
    (hg : σ'.globE = τ) (hl : ∀ {t : LTy} (i : Idx Γ t), σ'.getE i = σ.getE i) :
    {s : Srt} → (t : Tm C Γ s) → t.stExplicitS = true →
      (Tm.withStS S t).eval σ = t.eval σ'
  | _, .pvV i, _ => by simp only [Tm.withStS, Tm.eval, hl i]
  | _, .pvP i, _ => by simp only [Tm.withStS, Tm.eval, State.aliasPathT_getE, hl i]
  | _, .pvS i, _ => by
    show pure { σ.globE with storage := σ.getE i } = pure { σ'.globE with storage := σ'.getE i }
    rw [hl i, hg, ← hk]
  | _, .pvI i, _ => by simp only [Tm.withStS, Tm.eval, State.memRefT_getE, hl i]
  | _, .netOf _ _, he => absurd he Bool.false_ne_true
  | _, .app0 o, he => by
    cases o with
    | storage => show S.eval σ = pure σ'.globE; rw [hs, hg]; rfl
    | memory => exact absurd he Bool.false_ne_true
    | lit _ | root _ => rfl
    | env _ | mtSt _ => show _ = Op0.eval σ'.globE _; rw [hg, ← hk]; rfl
  | _, .app1 o ho a, he => by
    simp only [Tm.stExplicitS, Bool.and_eq_true] at he
    show o.eval σ.globE ((Tm.withStS S a).eval σ) = o.eval σ'.globE (a.eval σ')
    rw [Tm.withStS_eval hs hk hg hl a he.2, hg]
    exact o.eval_keeps hk he.1 _
  | _, .app2 o a b, he => by
    simp only [Tm.stExplicitS, Bool.and_eq_true] at he
    show o.eval σ.globE ((Tm.withStS S a).eval σ) ((Tm.withStS S b).eval σ) =
      o.eval σ'.globE (a.eval σ') (b.eval σ')
    rw [Tm.withStS_eval hs hk hg hl a he.1.2, Tm.withStS_eval hs hk hg hl b he.2, hg]
    exact o.eval_keeps hk he.1.1 _ _
  | _, .app3 o a b c, he => by
    simp only [Tm.stExplicitS, Bool.and_eq_true] at he
    show o.eval σ.globE ((Tm.withStS S a).eval σ) ((Tm.withStS S b).eval σ)
        ((Tm.withStS S c).eval σ) =
      o.eval σ'.globE (a.eval σ') (b.eval σ') (c.eval σ')
    rw [Tm.withStS_eval hs hk hg hl a he.1.1, Tm.withStS_eval hs hk hg hl b he.1.2,
      Tm.withStS_eval hs hk hg hl c he.2]
    rfl

/-- **Read before `{storage := S}`, the substituted term denotes, up to
`Equiv`, what the term denotes in every typed state it lands on.** -/
theorem Tm.withStS_denote (hs : S.eval σ = .ok τ) (hk : σ.globE.Keeps τ)
    (hg : σ'.globE = τ) (hl : ∀ {t : LTy} (i : Idx Γ t), σ'.getE i = σ.getE i) :
    {s : Srt} → (t : Tm C Γ s) → t.stExplicitS = true →
      Srt.DEquiv s ((Tm.withStS S t).denote σ) (t.denote σ')
  | _, .pvV i, _ => by
    have he : (Tm.pvV i).denote σ' = (Tm.pvV (C := C) i).denote σ := by
      simp only [Tm.denote, hl i]
    rw [show Tm.withStS S (.pvV i) = .pvV i from rfl, he]
    exact Srt.DEquiv.refl _ _
  | _, .pvS i, _ => by
    have he : (Tm.pvS i).denote σ' = (Tm.pvS (C := C) i).denote σ := by
      simp only [Tm.denote, hl i]
    rw [show Tm.withStS S (.pvS i) = .pvS i from rfl, he]
    exact Srt.DEquiv.refl _ _
  | _, .pvP i, _ => by
    show (Tm.pvP i).denote σ = (Tm.pvP i).denote σ'
    simp only [Tm.denote, State.aliasPathT_getE, hl i]
  | _, .pvI _, _ => trivial
  | _, .netOf _ _, he => absurd he Bool.false_ne_true
  | _, .app0 o, he => by
    cases o with
    | storage =>
      show Struct.Equiv (S.denote σ) (Op0.denote σ'.globE .storage)
      rw [hg]
      exact Tm.denote_eval σ S τ hs
    | memory => exact absurd he Bool.false_ne_true
    | lit _ | root _ | mtSt _ => exact Srt.DEquiv.refl _ _
    | env _ =>
      show Srt.DEquiv _ (Op0.denote σ.globE _) (Op0.denote σ'.globE _)
      rw [hg, ← hk]; exact Srt.DEquiv.refl _ _
  | _, .app1 o ho a, he => by
    simp only [Tm.stExplicitS, Bool.and_eq_true] at he
    show Srt.DEquiv _ (o.denote σ.globE ((Tm.withStS S a).denote σ))
      (o.denote σ'.globE (a.denote σ'))
    rw [hg]
    exact Srt.DEquiv.of_eq (o.denote_keeps hk he.1 _)
      (o.denote_congr (Tm.withStS_denote hs hk hg hl a he.2))
  | _, .app2 o a b, he => by
    simp only [Tm.stExplicitS, Bool.and_eq_true] at he
    show Srt.DEquiv _ (o.denote σ.globE ((Tm.withStS S a).eval σ) ((Tm.withStS S b).eval σ)
        ((Tm.withStS S a).denote σ) ((Tm.withStS S b).denote σ))
      (o.denote σ'.globE (a.eval σ') (b.eval σ') (a.denote σ') (b.denote σ'))
    rw [hg]
    exact Srt.DEquiv.of_eq (o.denote_keeps hk he.1.1 _ (a.eval σ') _ (b.eval σ') _ _)
      (o.denote_congr (Op2.opaque_of_stExplicit he.1.1) (Tm.withStS_denote hs hk hg hl a he.1.2)
        (Tm.withStS_denote hs hk hg hl b he.2))
  | _, .app3 o a b c, he => by
    simp only [Tm.stExplicitS, Bool.and_eq_true] at he
    exact o.denote_congr (Tm.withStS_denote hs hk hg hl a he.1.1)
      (Tm.withStS_denote hs hk hg hl b he.1.2) (Tm.withStS_denote hs hk hg hl c he.2)

/-- A first-order formula with `S` for every `storage`, where every storage
read of it is a `storage` term; `none` past anything else. -/
def Fml.withStS (S : Tm C Γ .st) : Fml C Γ → Option (Fml C Γ)
  | .tt => some .tt
  | .eq a b => if (a.stExplicitS && b.stExplicitS) = true then some (.eq (Tm.withStS S a) (Tm.withStS S b))
    else none
  | .defined t => if t.stExplicitS = true then some (.defined (Tm.withStS S t)) else none
  | .not φ => (Fml.withStS S φ).map .not
  | .and φ ψ => do pure (.and (← Fml.withStS S φ) (← Fml.withStS S ψ))
  | .imp φ ψ => do pure (.imp (← Fml.withStS S φ) (← Fml.withStS S ψ))
  | _ => none

/-- **A first-order formula with `S` for `storage` holds before the write as
the formula holds in every typed state it lands on.** -/
theorem Fml.withStS_holds (hs : S.eval σ = .ok τ) (hg : σ'.globE = τ)
    (hl : ∀ {t : LTy} (i : Idx Γ t), σ'.getE i = σ.getE i) :
    (φ : Fml C Γ) → {φ' : Fml C Γ} → Fml.withStS S φ = some φ' → (holds σ φ' ↔ holds σ' φ)
  | .tt, _, h => by cases h; exact Iff.rfl
  | .eq a b, _, h => by
    simp only [Fml.withStS] at h
    split at h
    · rename_i hab
      cases h
      simp only [Bool.and_eq_true] at hab
      have hk : σ.globE.Keeps τ := (Tm.eval_st_glob σ S τ hs).symm
      have ea := Tm.withStS_denote hs hk hg hl a hab.1
      have eb := Tm.withStS_denote hs hk hg hl b hab.2
      rw [holds_eq, holds_eq]
      exact ⟨fun e => (ea.symm.trans e).trans eb, fun e => (ea.trans e).trans eb.symm⟩
    · cases h
  | .defined t, _, h => by
    simp only [Fml.withStS] at h
    split at h
    · rename_i ht
      cases h
      have hk : σ.globE.Keeps τ := (Tm.eval_st_glob σ S τ hs).symm
      rw [holds_defined, holds_defined, Tm.withStS_eval hs hk hg hl t ht]
    · cases h
  | .not φ, _, h => by
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact not_congr (Fml.withStS_holds hs hg hl φ hφ)
  | .and φ ψ, _, h => by
    obtain ⟨φ', hφ, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ψ', hψ, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact and_congr (Fml.withStS_holds hs hg hl φ hφ) (Fml.withStS_holds hs hg hl ψ hψ)
  | .imp φ ψ, _, h => by
    obtain ⟨φ', hφ, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ψ', hψ, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact imp_congr (Fml.withStS_holds hs hg hl φ hφ) (Fml.withStS_holds hs hg hl ψ hψ)
  | .upd .., _, h | .modal .., _, h | .havoc _, _, h | .all .., _, h | .bind .., _, h
  | .anon .., _, h => by cases h

/-- `[{storage := S}] φ ⇝ φ[S/storage]` on the update in front. -/
def Fml.applyStTop {Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) : Option (Fml C Γ) :=
  match m, U with
  | .box, .snoc .nil (.storage S) => Fml.withStS S φ
  | _, _ => none

theorem Fml.applyStTop_sound {Δ : Ctx} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ}
    {ψ : Fml C Γ} (h : Fml.applyStTop m U φ = some ψ) (σ : State C Γ) (hψ : holds σ ψ) :
    holds σ (.upd m U φ) := by
  cases m with
  | diamond => cases h
  | box =>
    cases U with
    | snoc U e =>
      cases U with
      | nil =>
        cases e with
        | storage S =>
          have h : Fml.withStS S φ = some ψ := h
          refine Upd.afterT_intro (fun _ _ => trivial) fun g σ' hL _ => ?_
          have h1 : (do let st ← S.eval σ; pure { σ.globE with storage := st.storage }) =
              Except.ok g := hL.1
          cases hs : S.eval σ with
          | error e => rw [hs] at h1; cases h1
          | ok τ =>
            rw [hs] at h1
            have hk : σ.globE.Keeps τ := (Tm.eval_st_glob σ S τ hs).symm
            have hg : σ'.globE = τ := hL.2.1.trans ((Except.ok.inj h1).symm.trans hk)
            exact (Fml.withStS_holds hs hg (fun i => hL.2.2 i) φ h).1 hψ
        | _ => cases h
      | _ => cases h
    | _ => cases h

/-- **`applyStorageBox`** past the program, at position `i` of the spine:
`[{storage := S}] φ ⇝ φ[S/storage]` (`Fml.applyStTop`). -/
def FmlRw.applyStorageBoxP (i : Nat) : FmlRw C :=
  FmlRw.atSpine (fun m U φ => Fml.applyStTop m U φ) (fun h σ hψ => Fml.applyStTop_sound h σ hψ) i

end WithSt

/-! ## Out of a thinning's scope

The locals a thinning `h : Thin Γ' Γ` drops, taken out of a term, an update
and a formula (`Tm.thinS?`, `Upd.thinIO`, `Fml.thinS?`): where nothing reads
them, the formula reads the state with them dropped (`State.thin`) as the
formula read the state with them.  An update may also drop locals it
declares (`Upd.thinIO`'s `dropDecl`): every write to one goes, and a scope
end pops what is left of its scope (`Thin.popExt`).  A dropped write must
not halt (`Rhs.totalB`), so the update halts where it did. -/

section Thinning

/-- A position a thinning keeps is found back. -/
theorem Idx.unwk?_wk_self : {Γ Δ : Ctx} → {t : LTy} → (h : Thin Γ Δ) → (j : Idx Γ t) →
    Idx.unwk? h (j.wk h) = some j
  | _, _, _, .refl, _ => rfl
  | _, _, _, .keep _, .here => rfl
  | _, _, _, .keep h, .there j => by
    show (Idx.unwk? h (j.wk h)).map Idx.there = _
    rw [Idx.unwk?_wk_self h j]; rfl
  | _, _, _, .drop h, j => Idx.unwk?_wk_self h j

/-- A position not found back is no kept one. -/
theorem Idx.toNat_ne_of_unwk?_none {Γ Δ : Ctx} {t u : LTy} {h : Thin Γ Δ} {i : Idx Δ t}
    (hi : Idx.unwk? h i = none) (k : Idx Γ u) : i.toNat ≠ (k.wk h).toNat := fun hc => by
  obtain rfl := Idx.ty_eq_of_toNat hc
  obtain rfl := Idx.toNat_inj _ _ hc
  rw [Idx.unwk?_wk_self] at hi
  cases hi

/-- A scope end's top local over a thinning (`Thin.popExt`), the rest of
the scope end popped by `rec`. -/
def Thin.popCons {Δo Δ₁ : Ctx} {t : LTy} (h : Ext Δo Δ₁)
    (rec : {Δ' : Ctx} → Thin Δ' Δ₁ → (Δo' : Ctx) × Thin Δo' Δo × Ext Δo' Δ') :
    {Δ' : Ctx} → Thin Δ' (t :: Δ₁) → (Δo' : Ctx) × Thin Δo' Δo × Ext Δo' Δ'
  | _, .refl => ⟨_, .refl, .push h⟩
  | _, .keep th =>
    let r := rec th
    ⟨r.1, r.2.1, .push r.2.2⟩
  | _, .drop th => rec th

/-- A scope end over a thinning: what it pops of the locals kept, and the
thinning left. -/
def Thin.popExt {Δo : Ctx} : {Δ : Ctx} → Ext Δo Δ → {Δ' : Ctx} → Thin Δ' Δ →
    (Δo' : Ctx) × Thin Δo' Δo × Ext Δo' Δ'
  | _, .refl, _, th => ⟨_, th, .refl⟩
  | _, .push h, _, th => Thin.popCons h (fun th' => Thin.popExt h th') th

/-- A scope end over a thinning pops what the thinning keeps of it. -/
theorem Idx.wk_popExt {Δo : Ctx} : {Δ : Ctx} → (h : Ext Δo Δ) → {Δ' : Ctx} → (th : Thin Δ' Δ) →
    {t : LTy} → (k : Idx (Thin.popExt h th).1 t) →
      (k.ext (Thin.popExt h th).2.2).wk th = (k.wk (Thin.popExt h th).2.1).ext h
  | _, .refl, _, _, _, _ => rfl
  | _, .push _, _, .refl, _, _ => rfl
  | _, .push h, _, .keep th, _, k => congrArg Idx.there (Idx.wk_popExt h th k)
  | _, .push h, _, .drop th, _, k => congrArg Idx.there (Idx.wk_popExt h th k)

/-- `Thin.meet`'s step at a kept local. -/
def Thin.meetKeep {Δ₁ Δo₁ : Ctx} {t : LTy} (h : Thin Δo₁ Δ₁)
    (rec : {Δ' : Ctx} → Thin Δ' Δ₁ → (X : Ctx) × Thin X Δo₁ × Thin X Δ') :
    {Δ' : Ctx} → Thin Δ' (t :: Δ₁) → (X : Ctx) × Thin X (t :: Δo₁) × Thin X Δ'
  | _, .refl => ⟨_, .refl, .keep h⟩
  | _, .keep th =>
    let r := rec th
    ⟨_, .keep r.2.1, .keep r.2.2⟩
  | _, .drop th =>
    let r := rec th
    ⟨r.1, .drop r.2.1, r.2.2⟩

/-- `Thin.meet`'s step at a dropped local. -/
def Thin.meetDrop {Δ₁ Δo : Ctx} {t : LTy} (h : Thin Δo Δ₁)
    (rec : {Δ' : Ctx} → Thin Δ' Δ₁ → (X : Ctx) × Thin X Δo × Thin X Δ') :
    {Δ' : Ctx} → Thin Δ' (t :: Δ₁) → (X : Ctx) × Thin X Δo × Thin X Δ'
  | _, .refl => ⟨_, .refl, .drop h⟩
  | _, .keep th =>
    let r := rec th
    ⟨r.1, r.2.1, .drop r.2.2⟩
  | _, .drop th => rec th

/-- A scope's frame end (`Upd.drop`'s thinning `h`) over a thinning `th`:
the locals both keep, as kept by each. -/
def Thin.meet : {Δo Δ : Ctx} → Thin Δo Δ → {Δ' : Ctx} → Thin Δ' Δ →
    (X : Ctx) × Thin X Δo × Thin X Δ'
  | _, _, .refl, _, th => ⟨_, th, .refl⟩
  | _, _, .keep h, _, th => Thin.meetKeep h (fun th' => Thin.meet h th') th
  | _, _, .drop h, _, th => Thin.meetDrop h (fun th' => Thin.meet h th') th

/-- A frame end over a thinning keeps what both keep. -/
theorem Idx.wk_meet : {Δo Δ : Ctx} → (h : Thin Δo Δ) → {Δ' : Ctx} → (th : Thin Δ' Δ) →
    {t : LTy} → (k : Idx (Thin.meet h th).1 t) →
      (k.wk (Thin.meet h th).2.2).wk th = (k.wk (Thin.meet h th).2.1).wk h
  | _, _, .refl, _, _, _, _ => rfl
  | _, _, .keep _, _, .refl, _, _ => rfl
  | _, _, .keep h, _, .keep th, _, k => by
    cases k with
    | here => rfl
    | there k => exact congrArg Idx.there (Idx.wk_meet h th k)
  | _, _, .keep h, _, .drop th, _, k => congrArg Idx.there (Idx.wk_meet h th k)
  | _, _, .drop _, _, .refl, _, _ => rfl
  | _, _, .drop h, _, .keep th, _, k => congrArg Idx.there (Idx.wk_meet h th k)
  | _, _, .drop h, _, .drop th, _, k => congrArg Idx.there (Idx.wk_meet h th k)

/-- An element that sets no local, its right-hand sides read in `Γ'`, at
another target context. -/
def UpdElem.thinG? (h : Thin Γ' Γ) {Δ Δ' : Ctx} : UpdElem C Γ Δ → Option (UpdElem C Γ' Δ')
  | .local .. => none
  | .storage s => (Tm.thinS? h s).map .storage
  | .memory m => (Tm.thinS? h m).map .memory
  | .selfBalance op a => (Tm.thinS? h a).map (.selfBalance op)
  | .net r op a => do pure (.net (← Tm.thinS? h r) op (← Tm.thinS? h a))
  | .pay r a => do pure (.pay (← Tm.thinS? h r) (← Tm.thinS? h a))
  | .netMt r a => do pure (.netMt (← Tm.thinS? h r) (← Tm.thinS? h a))
  | .setBalance a => (Tm.thinS? h a).map .setBalance

/-- An element that sets no local, read in a state with locals dropped,
computes the global part it did. -/
theorem UpdElem.globT_thinG? {h : Thin Γ' Γ} {σ₀' : State C Γ'} {σ₀ : State C Γ}
    (hr : State.ThinOf h σ₀' σ₀) {Δ Δ' : Ctx} (G : Semantics.State) :
    (e : UpdElem C Γ Δ) → {e' : UpdElem C Γ' Δ'} → e.thinG? h = some e' →
      e'.globT σ₀' G = e.globT σ₀ G
  | .local .., _, he => by cases he
  | .storage s, _, he => by
    obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 he
    simp only [UpdElem.globT, Tm.eval_thinS? hr s hs]
  | .memory m, _, he => by
    obtain ⟨m', hm, rfl⟩ := Option.map_eq_some_iff.1 he
    simp only [UpdElem.globT, Tm.eval_thinS? hr m hm]
  | .selfBalance op a, _, he => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 he
    simp only [UpdElem.globT, Tm.eval_thinS? hr a ha, hr.1]
  | .net r op a, _, he => by
    obtain ⟨r', hr', he⟩ := Option.bind_eq_some_iff.1 he
    obtain ⟨a', ha, he⟩ := Option.bind_eq_some_iff.1 he
    cases he
    simp only [UpdElem.globT, Tm.eval_thinS? hr r hr', Tm.eval_thinS? hr a ha]
  | .pay r a, _, he => by
    obtain ⟨r', hr', he⟩ := Option.bind_eq_some_iff.1 he
    obtain ⟨a', ha, he⟩ := Option.bind_eq_some_iff.1 he
    cases he
    simp only [UpdElem.globT, Tm.eval_thinS? hr r hr', Tm.eval_thinS? hr a ha, hr.1]
  | .netMt r a, _, he => by
    obtain ⟨r', hr', he⟩ := Option.bind_eq_some_iff.1 he
    obtain ⟨a', ha, he⟩ := Option.bind_eq_some_iff.1 he
    cases he
    simp only [UpdElem.globT, Tm.eval_thinS? hr r hr', Tm.eval_thinS? hr a ha]
  | .setBalance a, _, he => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 he
    simp only [UpdElem.globT, Tm.eval_thinS? hr a ha]

/-- What an element `thinG?` gives sets no local. -/
theorem UpdElem.thinG?_held {h : Thin Γ' Γ} {Δ' : Ctx} {Δ : Ctx} (U : Upd C Γ' Δ') :
    (e : UpdElem C Γ Δ) → {e' : UpdElem C Γ' Δ'} → e.thinG? h = some e' →
      ∀ {t : LTy} (k : Idx Δ' t), (Upd.snoc U e').held k = U.held k
  | .local .., _, he, _, _ => by cases he
  | .storage _, _, he, _, _ | .memory _, _, he, _, _ | .selfBalance .., _, he, _, _
  | .setBalance _, _, he, _, _ => by
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 he; rfl
  | .net .., _, he, _, _ | .pay .., _, he, _, _ | .netMt .., _, he, _, _ => by
    obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 he
    obtain ⟨_, -, he⟩ := Option.bind_eq_some_iff.1 he
    cases he; rfl

/-- A scope end, none where it pops nothing. -/
def Upd.popOrSkip {Δ' : Ctx} : {Δ : Ctx} → Upd C Γ' Δ → Ext Δ' Δ → Upd C Γ' Δ'
  | _, U, .refl => U
  | _, U, .push h => .pop U (.push h)

theorem Upd.popOrSkip_held {Δ' : Ctx} : {Δ : Ctx} → (U : Upd C Γ' Δ) → (h : Ext Δ' Δ) →
    ∀ {t : LTy} (k : Idx Δ' t), (U.popOrSkip h).held k = U.held (k.ext h)
  | _, _, .refl, _, _ => rfl
  | _, _, .push _, _, _ => rfl

theorem Upd.popOrSkip_globT {Δ' : Ctx} (σ : State C Γ') : {Δ : Ctx} → (U : Upd C Γ' Δ) →
    (h : Ext Δ' Δ) → (U.popOrSkip h).globT σ = U.globT σ
  | _, _, .refl => rfl
  | _, _, .push _ => rfl

/-- A frame end, none where it drops nothing. -/
def Upd.dropOrSkip {Δ' : Ctx} : {Δ : Ctx} → Upd C Γ' Δ → Thin Δ' Δ → Upd C Γ' Δ'
  | _, U, .refl => U
  | _, U, .keep h => .drop U (.keep h)
  | _, U, .drop h => .drop U (.drop h)

theorem Upd.dropOrSkip_held {Δ' : Ctx} : {Δ : Ctx} → (U : Upd C Γ' Δ) → (h : Thin Δ' Δ) →
    ∀ {t : LTy} (k : Idx Δ' t), (U.dropOrSkip h).held k = U.held (k.wk h)
  | _, _, .refl, _, _ => rfl
  | _, _, .keep _, _, _ | _, _, .drop _, _, _ => rfl

theorem Upd.dropOrSkip_globT {Δ' : Ctx} (σ : State C Γ') : {Δ : Ctx} → (U : Upd C Γ' Δ) →
    (h : Thin Δ' Δ) → (U.dropOrSkip h).globT σ = U.globT σ
  | _, _, .refl => rfl
  | _, _, .keep _ | _, _, .drop _ => rfl

/-- An update thinned: the context it leaves, that context's thinning into
the update's, and the update. -/
structure UThin (C : Contract) (Γ' Δ : Ctx) where
  {Δ' : Ctx}
  th : Thin Δ' Δ
  U : Upd C Γ' Δ'

/-- `Thin.norm`'s step at a kept local: a thinning that keeps everything
below is the identity. -/
def Thin.normKeep {t : LTy} : {Δ' Δ : Ctx} → Thin Δ' Δ → Thin (t :: Δ') (t :: Δ)
  | _, _, .refl => .refl
  | _, _, .keep h => .keep (.keep h)
  | _, _, .drop h => .keep (.drop h)

/-- A thinning that drops nothing written as the identity. -/
def Thin.norm : {Δ' Δ : Ctx} → Thin Δ' Δ → Thin Δ' Δ
  | _, _, .refl => .refl
  | _, _, .keep h => Thin.normKeep (Thin.norm h)
  | _, _, .drop h => .drop (Thin.norm h)

theorem Idx.wk_normKeep {t u : LTy} : {Δ' Δ : Ctx} → (h : Thin Δ' Δ) → (k : Idx (t :: Δ') u) →
    k.wk (Thin.normKeep h) = k.wk (Thin.keep h)
  | _, _, .refl, .here => rfl
  | _, _, .refl, .there k => congrArg Idx.there (Idx.wk_refl k).symm
  | _, _, .keep _, _ | _, _, .drop _, _ => rfl

theorem Idx.wk_norm : {Δ' Δ : Ctx} → (h : Thin Δ' Δ) → {t : LTy} → (k : Idx Δ' t) →
    k.wk (Thin.norm h) = k.wk h
  | _, _, .refl, _, _ => rfl
  | _, _, .keep h, _, k => by
    show k.wk (Thin.normKeep (Thin.norm h)) = _
    rw [Idx.wk_normKeep]
    cases k with
    | here => rfl
    | there k => exact congrArg Idx.there (Idx.wk_norm h k)
  | _, _, .drop h, _, k => congrArg Idx.there (Idx.wk_norm h k)

/-- The update, where the thinning is the identity. -/
def Thin.closeU {Δ' Δ : Ctx} : Thin Δ' Δ → Upd C Γ' Δ' → Option (Upd C Γ' Δ)
  | .refl, U => some U
  | .keep _, _ => none
  | .drop _, _ => none

/-- The update, where its thinning drops nothing. -/
def UThin.close? {Δ : Ctx} (R : UThin C Γ' Δ) : Option (Upd C Γ' Δ) :=
  Thin.closeU (Thin.norm R.th) R.U

/-- What the update, its thinning dropping nothing, is. -/
theorem Thin.closeU_spec {Δ' Δ : Ctx} {n : Thin Δ' Δ} {U : Upd C Γ' Δ'} {U' : Upd C Γ' Δ}
    (h : Thin.closeU n U = some U') (σ : State C Γ') :
    U'.globT σ = U.globT σ ∧ ∀ {t : LTy} (i : Idx Δ t), ∃ j : Idx Δ' t, j.wk n = i ∧ U'.held i = U.held j := by
  cases n with
  | refl => cases h; exact ⟨rfl, fun i => ⟨i, rfl, rfl⟩⟩
  | keep _ => cases h
  | drop _ => cases h

/-- **An update with locals dropped**: its right-hand sides read in `Γ'`
(`h`), the declarations `dropDecl` names left out (counted from the first),
every write to a dropped local left out, which must not halt, and each scope
end popping what is left of its scope.  The number of declarations seen, and
the update. -/
def Upd.thinIO (h : Thin Γ' Γ) (dropDecl : Nat → Bool) : {Δ : Ctx} → Upd C Γ Δ →
    Option (Nat × UThin C Γ' Δ)
  | _, .nil => some (0, ⟨h, .nil⟩)
  | _, .snoc U e => do
    let (n, R) ← Upd.thinIO h dropDecl U
    match e with
    | .local i r =>
      match Idx.unwk? R.th i with
      | some j => pure (n, ⟨R.th, .snoc R.U (.local j (← Rhs.thinS? h r))⟩)
      | none => if r.totalB then pure (n, R) else none
    | e => pure (n, ⟨R.th, .snoc R.U (← e.thinG? h)⟩)
  | _, .decl U y r => do
    let (n, R) ← Upd.thinIO h dropDecl U
    if dropDecl n then
      if r.totalB then pure (n + 1, ⟨.drop R.th, R.U⟩) else none
    else pure (n + 1, ⟨.keep R.th, .decl R.U y (← Rhs.thinS? h r)⟩)
  | _, .pop U e => do
    let (n, R) ← Upd.thinIO h dropDecl U
    let r := Thin.popExt e R.th
    pure (n, ⟨r.2.1, R.U.popOrSkip r.2.2⟩)
  | _, .drop U e => do
    let (n, R) ← Upd.thinIO h dropDecl U
    let r := Thin.meet e R.th
    pure (n, ⟨r.2.1, R.U.dropOrSkip r.2.2⟩)

/-- **The thinned update computes, read with locals dropped, the global part
the update computes**: a write it leaves out cannot halt. -/
theorem Upd.globT_thinIO (h : Thin Γ' Γ) (dd : Nat → Bool) {σ₀' : State C Γ'} {σ₀ : State C Γ}
    (hr : State.ThinOf h σ₀' σ₀) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → {n : Nat} → {R : UThin C Γ' Δ} →
      U.thinIO h dd = some (n, R) → R.U.globT σ₀' = U.globT σ₀
  | _, .nil, _, _, hU => by cases hU; exact congrArg pure hr.1
  | _, .snoc U e, n', R', hU => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    have ih := Upd.globT_thinIO h dd hr U hR
    cases e with
    | «local» i r =>
      simp only at hU
      split at hU
      · rename_i j hj
        obtain ⟨r', hr', hU⟩ := Option.bind_eq_some_iff.1 hU
        cases hU
        show (R.U.globT σ₀' >>= fun g => do let _ ← r'.eval σ₀'; pure g) =
          (U.globT σ₀ >>= fun g => do let _ ← r.eval σ₀; pure g)
        rw [ih, Rhs.eval_thinS? hr r hr']
      · split at hU
        · rename_i ht
          cases hU
          obtain ⟨v, hv⟩ := Rhs.totalB_eval σ₀ r ht
          change _ = (U.globT σ₀ >>= fun g => do let _ ← r.eval σ₀; pure g)
          rw [ih, hv]
          cases U.globT σ₀ <;> rfl
        · cases hU
    | _ =>
      obtain ⟨e', he, hU⟩ := Option.bind_eq_some_iff.1 hU
      cases hU
      show (R.U.globT σ₀' >>= e'.globT σ₀') = (U.globT σ₀ >>= UpdElem.globT σ₀ _)
      rw [ih]
      congr 1
      funext G
      exact UpdElem.globT_thinG? hr G _ he
  | _, .decl U y r, n', R', hU => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    have ih := Upd.globT_thinIO h dd hr U hR
    simp only at hU
    split at hU
    · split at hU
      · rename_i ht
        cases hU
        obtain ⟨v, hv⟩ := Rhs.totalB_eval σ₀ r ht
        change _ = (do let g ← U.globT σ₀; let _ ← r.eval σ₀; pure g)
        rw [ih, hv]
        cases U.globT σ₀ <;> rfl
      · cases hU
    · obtain ⟨r', hr', hU⟩ := Option.bind_eq_some_iff.1 hU
      cases hU
      show (do let g ← R.U.globT σ₀'; let _ ← r'.eval σ₀'; pure g) =
        (do let g ← U.globT σ₀; let _ ← r.eval σ₀; pure g)
      rw [ih, Rhs.eval_thinS? hr r hr']
  | _, .pop U e, n', R', hU => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    cases hU
    exact (Upd.popOrSkip_globT σ₀' R.U _).trans (Upd.globT_thinIO h dd hr U hR)
  | _, .drop U e, n', R', hU => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    cases hU
    exact (Upd.dropOrSkip_globT σ₀' R.U _).trans (Upd.globT_thinIO h dd hr U hR)

/-- **The thinned update leaves in each local it keeps what the update
leaves there.** -/
theorem Upd.held_thinIO (h : Thin Γ' Γ) (dd : Nat → Bool) {σ₀' : State C Γ'} {σ₀ : State C Γ}
    (hr : State.ThinOf h σ₀' σ₀) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → {n : Nat} → {R : UThin C Γ' Δ} →
      U.thinIO h dd = some (n, R) → ∀ {t : LTy} (k : Idx R.Δ' t) (v : t.Denote C),
        Held.OKV σ₀ v (U.held (k.wk R.th)) → Held.OKV σ₀' v (R.U.held k)
  | _, .nil, _, _, hU, _, k, v, hv => by
    cases hU
    have hv : v = σ₀.getE (k.wk h) := hv
    show v = σ₀'.getE k
    rw [hv, hr.2 k]
  | _, .snoc U e, n', R', hU, _, k, v, hv => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    have ih : ∀ {t : LTy} (k : Idx R.Δ' t) (v : t.Denote C),
        Held.OKV σ₀ v (U.held (k.wk R.th)) → Held.OKV σ₀' v (R.U.held k) :=
      fun k v hv => Upd.held_thinIO h dd hr U hR k v hv
    cases e with
    | «local» i r =>
      simp only at hU
      split at hU
      · rename_i j hj
        obtain ⟨r', hr', hU⟩ := Option.bind_eq_some_iff.1 hU
        cases hU
        show Held.OKV σ₀' v (Subst.set (Upd.held R.U) j r' k)
        have hv : Held.OKV σ₀ v (Subst.set (Upd.held U) i r (k.wk R.th)) := hv
        have hi : j.wk R.th = i := Idx.unwk?_wk R.th i hj
        subst hi
        unfold Subst.set at hv ⊢
        by_cases hjk : j.toNat = k.toNat
        · obtain rfl := Idx.ty_eq_of_toNat hjk
          obtain rfl := Idx.toNat_inj j k hjk
          rw [dif_pos rfl] at hv ⊢
          show r'.eval σ₀' = .ok v
          rw [Rhs.eval_thinS? hr r hr']
          exact hv
        · have hjk' : ¬ (j.wk R.th).toNat = (k.wk R.th).toNat := fun hc => by
            obtain rfl := Idx.ty_eq_of_toNat hc
            have heq := congrArg (Idx.unwk? R.th) (Idx.toNat_inj _ _ hc)
            rw [Idx.unwk?_wk_self, Idx.unwk?_wk_self] at heq
            cases heq
            exact hjk rfl
          rw [dif_neg hjk'] at hv
          rw [dif_neg hjk]
          exact ih k v hv
      · rename_i hj
        split at hU
        · cases hU
          have hv : Held.OKV σ₀ v (Subst.set (Upd.held U) i r _) := hv
          unfold Subst.set at hv
          rw [dif_neg (Idx.toNat_ne_of_unwk?_none hj k)] at hv
          exact ih k v hv
        · cases hU
    | _ =>
      obtain ⟨e', he, hU⟩ := Option.bind_eq_some_iff.1 hU
      cases hU
      rw [UpdElem.thinG?_held R.U _ he k]
      exact ih k v hv
  | _, .decl U y r, n', R', hU, _, k, v, hv => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    have ih : ∀ {t : LTy} (k : Idx R.Δ' t) (v : t.Denote C),
        Held.OKV σ₀ v (U.held (k.wk R.th)) → Held.OKV σ₀' v (R.U.held k) :=
      fun k v hv => Upd.held_thinIO h dd hr U hR k v hv
    simp only at hU
    split at hU
    · split at hU
      · cases hU
        exact ih k v hv
      · cases hU
    · obtain ⟨r', hr', hU⟩ := Option.bind_eq_some_iff.1 hU
      cases hU
      cases k with
      | here =>
        show r'.eval σ₀' = .ok v
        rw [Rhs.eval_thinS? hr r hr']
        exact hv
      | there k => exact ih k v hv
  | _, .pop U e, n', R', hU, _, k, v, hv => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    cases hU
    rw [Upd.popOrSkip_held]
    refine Upd.held_thinIO h dd hr U hR _ v ?_
    rw [Idx.wk_popExt]
    exact hv
  | _, .drop U e, n', R', hU, _, k, v, hv => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    cases hU
    rw [Upd.dropOrSkip_held]
    refine Upd.held_thinIO h dd hr U hR _ v ?_
    rw [Idx.wk_meet]
    exact hv

/-- **Where the update lands, its thinning lands on the state with the
locals it drops left out.** -/
theorem Upd.lands_thinIO (h : Thin Γ' Γ) (dd : Nat → Bool) {σ₀' : State C Γ'} {σ₀ : State C Γ}
    (hr : State.ThinOf h σ₀' σ₀) {Δ : Ctx} {U : Upd C Γ Δ} {n : Nat} {R : UThin C Γ' Δ}
    (hU : U.thinIO h dd = some (n, R)) {g : Semantics.State} {σ' : State C Δ}
    (hL : U.Lands σ₀ g σ') : R.U.Lands σ₀' g (σ'.thin R.th) := by
  refine ⟨(Upd.globT_thinIO h dd hr U hU).trans hL.1, hL.2.1, fun k => ?_⟩
  rw [Held.OKT_iff_OKV, State.getE_thin]
  exact Upd.held_thinIO h dd hr U hU k _ ((Held.OKT_iff_OKV _ _ _ _).1 (hL.2.2 (k.wk R.th)))

/-- …and where its thinning drops nothing, the closed update lands where the
update does. -/
theorem Upd.lands_thinIO_close (h : Thin Γ' Γ) (dd : Nat → Bool) {σ₀' : State C Γ'}
    {σ₀ : State C Γ} (hr : State.ThinOf h σ₀' σ₀) {Δ : Ctx} {U : Upd C Γ Δ} {n : Nat}
    {R : UThin C Γ' Δ} (hU : U.thinIO h dd = some (n, R)) {U' : Upd C Γ' Δ}
    (hc : R.close? = some U') {g : Semantics.State} {σ' : State C Δ}
    (hL : U.Lands σ₀ g σ') : U'.Lands σ₀' g σ' := by
  obtain ⟨hcg, hch⟩ := Thin.closeU_spec hc σ₀'
  refine ⟨hcg.trans ((Upd.globT_thinIO h dd hr U hU).trans hL.1), hL.2.1, fun i => ?_⟩
  obtain ⟨j, hj, he⟩ := hch i
  rw [Idx.wk_norm] at hj
  subst hj
  rw [Held.OKT_iff_OKV, he]
  exact Upd.held_thinIO h dd hr U hU j _ ((Held.OKT_iff_OKV _ _ _ _).1 (hL.2.2 (j.wk R.th)))

/-- …and the closed update computes the update's global part. -/
theorem Upd.globT_thinIO_close (h : Thin Γ' Γ) (dd : Nat → Bool) {σ₀' : State C Γ'}
    {σ₀ : State C Γ} (hr : State.ThinOf h σ₀' σ₀) {Δ : Ctx} {U : Upd C Γ Δ} {n : Nat}
    {R : UThin C Γ' Δ} (hU : U.thinIO h dd = some (n, R)) {U' : Upd C Γ' Δ}
    (hc : R.close? = some U') : U'.globT σ₀' = U.globT σ₀ :=
  (Thin.closeU_spec hc σ₀').1.trans (Upd.globT_thinIO h dd hr U hU)

/-- A first-order formula of `Γ` read in `Γ'` (no update, no modality). -/
def Fml.thinFO? : {Γ' Γ : Ctx} → Thin Γ' Γ → Fml C Γ → Option (Fml C Γ')
  | _, _, _, .tt => some .tt
  | _, _, h, .eq a b => do pure (.eq (← Tm.thinS? h a) (← Tm.thinS? h b))
  | _, _, h, .defined t => (Tm.thinS? h t).map .defined
  | _, _, h, .not φ => (Fml.thinFO? h φ).map .not
  | _, _, h, .and φ ψ => do pure (.and (← Fml.thinFO? h φ) (← Fml.thinFO? h ψ))
  | _, _, h, .imp φ ψ => do pure (.imp (← Fml.thinFO? h φ) (← Fml.thinFO? h ψ))
  | _, _, h, .all x p φ => (Fml.thinFO? (.keep h) φ).map (.all x p)
  | _, _, _, _ => none

/-- **A first-order formula that reads no dropped local holds alike with
them dropped.** -/
theorem Fml.thinFO?_holds : {Γ' Γ : Ctx} → (h : Thin Γ' Γ) → (φ : Fml C Γ) → {φ' : Fml C Γ'} →
    Fml.thinFO? h φ = some φ' → ∀ σ : State C Γ, (holds (σ.thin h) φ' ↔ holds σ φ)
  | _, _, _, .tt, _, hφ, _ => by cases hφ; exact Iff.rfl
  | _, _, h, .eq a b, _, hφ, σ => by
    obtain ⟨a', ha, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    obtain ⟨b', hb, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    cases hφ
    rw [holds_eq, holds_eq, Tm.denote_thinS? (State.ThinOf.thin h σ) a ha,
      Tm.denote_thinS? (State.ThinOf.thin h σ) b hb]
  | _, _, h, .defined t, _, hφ, σ => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 hφ
    rw [holds_defined, holds_defined, Tm.eval_thinS? (State.ThinOf.thin h σ) t ht]
  | _, _, h, .not φ, _, hφ, σ => by
    obtain ⟨φ', hφ', rfl⟩ := Option.map_eq_some_iff.1 hφ
    exact not_congr (Fml.thinFO?_holds h φ hφ' σ)
  | _, _, h, .and φ ψ, _, hφ, σ => by
    obtain ⟨φ', h₁, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    obtain ⟨ψ', h₂, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    cases hφ
    exact and_congr (Fml.thinFO?_holds h φ h₁ σ) (Fml.thinFO?_holds h ψ h₂ σ)
  | _, _, h, .imp φ ψ, _, hφ, σ => by
    obtain ⟨φ', h₁, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    obtain ⟨ψ', h₂, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    cases hφ
    exact imp_congr (Fml.thinFO?_holds h φ h₁ σ) (Fml.thinFO?_holds h ψ h₂ σ)
  | _, _, h, .all x p φ, _, hφ, σ => by
    obtain ⟨φ', hφ', rfl⟩ := Option.map_eq_some_iff.1 hφ
    exact forall_congr' fun v => Fml.thinFO?_holds (.keep h) φ hφ' (σ.push (t := .val p) v)
  | _, _, _, .upd .., _, hφ, _ | _, _, _, .modal .., _, hφ, _ | _, _, _, .havoc _, _, hφ, _
  | _, _, _, .bind .., _, hφ, _ | _, _, _, .anon .., _, hφ, _ => by cases hφ

/-- A formula of `Γ` read in `Γ'`: first-order where it is read both ways
(under `¬`, left of `→`), and through updates and binders elsewhere. -/
def Fml.thinS? : {Γ' Γ : Ctx} → Thin Γ' Γ → Fml C Γ → Option (Fml C Γ')
  | _, _, _, .tt => some .tt
  | _, _, h, .eq a b => do pure (.eq (← Tm.thinS? h a) (← Tm.thinS? h b))
  | _, _, h, .defined t => (Tm.thinS? h t).map .defined
  | _, _, h, .not φ => (Fml.thinFO? h φ).map .not
  | _, _, h, .and φ ψ => do pure (.and (← Fml.thinS? h φ) (← Fml.thinS? h ψ))
  | _, _, h, .imp φ ψ => do pure (.imp (← Fml.thinFO? h φ) (← Fml.thinS? h ψ))
  | _, _, h, .upd m U φ => do
    let (_, R) ← U.thinIO h (fun _ => false)
    match R.close? with
    | some U' => pure (.upd m U' φ)
    | none => pure (.upd m R.U (← Fml.thinS? R.th φ))
  | _, _, h, .all x p φ => (Fml.thinS? (.keep h) φ).map (.all x p)
  | _, _, h, .bind m x t φ => (Fml.thinS? (.keep h) φ).map (.bind m x t)
  | _, _, _, _ => none

/-- **A formula that reads no dropped local holds where it holds with them
dropped.** -/
theorem Fml.thinS?_holds : {Γ' Γ : Ctx} → (h : Thin Γ' Γ) → (φ : Fml C Γ) → {φ' : Fml C Γ'} →
    Fml.thinS? h φ = some φ' → ∀ σ : State C Γ, holds (σ.thin h) φ' → holds σ φ
  | _, _, _, .tt, _, _, _, _ => trivial
  | _, _, h, .eq a b, _, hφ, σ, hs => by
    obtain ⟨a', ha, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    obtain ⟨b', hb, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    cases hφ
    exact (Fml.thinFO?_holds h (.eq a b) (by simp only [Fml.thinFO?, ha, hb]; rfl) σ).1 hs
  | _, _, h, .defined t, _, hφ, σ, hs => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 hφ
    exact (Fml.thinFO?_holds h (.defined t) (by simp only [Fml.thinFO?, ht]; rfl) σ).1 hs
  | _, _, h, .not φ, _, hφ, σ, hs => by
    obtain ⟨φ', hφ', rfl⟩ := Option.map_eq_some_iff.1 hφ
    exact fun hn => hs ((Fml.thinFO?_holds h φ hφ' σ).2 hn)
  | _, _, h, .and φ ψ, _, hφ, σ, hs => by
    obtain ⟨φ', h₁, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    obtain ⟨ψ', h₂, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    cases hφ
    exact ⟨Fml.thinS?_holds h φ h₁ σ hs.1, Fml.thinS?_holds h ψ h₂ σ hs.2⟩
  | _, _, h, .imp φ ψ, _, hφ, σ, hs => by
    obtain ⟨φ', h₁, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    obtain ⟨ψ', h₂, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    cases hφ
    exact fun ha => Fml.thinS?_holds h ψ h₂ σ (hs ((Fml.thinFO?_holds h φ h₁ σ).2 ha))
  | _, _, h, .upd m U φ, _, hφ, σ, hs => by
    obtain ⟨⟨n, R⟩, hR, hφ⟩ := Option.bind_eq_some_iff.1 hφ
    have hr := State.ThinOf.thin h σ
    simp only at hφ
    split at hφ
    · rename_i U' hc
      cases hφ
      refine Upd.afterT_intro (fun e he => hs.of_error (e := e) ?_) fun g σ' hL hH =>
        hs.of_lands (Upd.lands_thinIO_close h _ hr hR hc hL) hH
      rw [Upd.globT_thinIO_close h _ hr hR hc, he]
    · obtain ⟨φ', h₁, hφ⟩ := Option.bind_eq_some_iff.1 hφ
      cases hφ
      refine Upd.afterT_intro (fun e he => hs.of_error (e := e) ?_) fun g σ' hL hH =>
        Fml.thinS?_holds R.th φ h₁ σ' (hs.of_lands (Upd.lands_thinIO h _ hr hR hL) hH)
      rw [Upd.globT_thinIO h _ hr U hR, he]
  | _, _, h, .all x p φ, _, hφ, σ, hs => by
    obtain ⟨φ', hφ', rfl⟩ := Option.map_eq_some_iff.1 hφ
    exact fun v => Fml.thinS?_holds (.keep h) φ hφ' (σ.push (t := .val p) v) (hs v)
  | _, _, h, .bind m x t φ, _, hφ, σ, hs => by
    obtain ⟨φ', hφ', rfl⟩ := Option.map_eq_some_iff.1 hφ
    exact Modality.forallB_intro fun v =>
      Fml.thinS?_holds (.keep h) φ hφ' (σ.push v) (Modality.forallB_all hs v)
  | _, _, _, .modal .., _, hφ, _, _ | _, _, _, .havoc _, _, hφ, _, _
  | _, _, _, .anon .., _, hφ, _, _ => by cases hφ

end Thinning

/-! ## `simplifyUpdate` past the program

`{U}_m ψ` with the locals `U` declares and no one reads afterwards dropped,
with every write to them (`Upd.thinIO`): those `U` pops itself, and those
`ψ` does not read (`Fml.thinS?`, `ψ` read without them): KeY's
`dropEffectless`.  Before, the scope
ends `ψ` begins with are merged into `U` (`Fml.absorbPops`) and the writes
a later one shadows dropped (`Upd.shadow`); a hidden binder in front of
`U` whose local `U` sets first is absorbed (`Upd.absorb`), so its local
goes too where nothing reads it.  A dropped write must not halt
(`Rhs.totalB`). -/

section SimpPast

variable {Γ : Ctx}

/-- Which positions of `Δ` a thinning keeps, the newest first. -/
def Thin.mask : {Δ' Δ : Ctx} → Thin Δ' Δ → List Bool
  | _, Δ, .refl => List.replicate Δ.length true
  | _, _, .keep h => true :: Thin.mask h
  | _, _, .drop h => false :: Thin.mask h

/-- The declarations an update ends itself, counted from the first: a
stack of the context's positions (`some k` the `k`th declaration), popped
at each scope end and thinned at each drop. -/
def Upd.declStack : {Δ : Ctx} → Upd C Γ Δ → Nat × List (Option Nat) × List Nat
  | _, .nil => (0, List.replicate Γ.length none, [])
  | _, .snoc U _ => Upd.declStack U
  | _, .decl U _ _ =>
    let r := Upd.declStack U
    (r.1 + 1, some r.1 :: r.2.1, r.2.2)
  | _, .pop U h =>
    let r := Upd.declStack U
    (r.1, r.2.1.drop h.depth, r.2.2 ++ (r.2.1.take h.depth).filterMap id)
  | _, .drop U h =>
    let r := Upd.declStack U
    let ps := r.2.1.zip (Thin.mask h)
    (r.1, (ps.filter (·.2)).map (·.1), r.2.2 ++ (ps.filter (!·.2)).filterMap (·.1))

/-- `{U}_m ψ` with the declarations of `U` that `drop` names dropped, `ψ`
read without those still in scope. -/
def Fml.dropDeclsTop {Δ : Ctx} (drop : Nat → Bool) (m : Modality) (U : Upd C Γ Δ) (ψ : Fml C Δ) :
    Option (Fml C Γ) := do
  let (_, R) ← U.thinIO .refl drop
  match R.close? with
  | some U' => pure (.upd m U' ψ)
  | none => pure (.upd m R.U (← Fml.thinS? R.th ψ))

theorem Fml.dropDeclsTop_sound {Δ : Ctx} {drop : Nat → Bool} {m : Modality} {U : Upd C Γ Δ}
    {ψ : Fml C Δ} {φ : Fml C Γ} (h : Fml.dropDeclsTop drop m U ψ = some φ) (σ : State C Γ)
    (hφ : holds σ φ) : holds σ (.upd m U ψ) := by
  obtain ⟨⟨n, R⟩, hR, h⟩ := Option.bind_eq_some_iff.1 h
  have hr : State.ThinOf .refl σ σ := ⟨rfl, fun _ => rfl⟩
  simp only at h
  split at h
  · rename_i U' hc
    cases h
    refine Upd.afterT_intro (fun e he => hφ.of_error (e := e) ?_) fun g σ' hL hH =>
      hφ.of_lands (Upd.lands_thinIO_close .refl drop hr hR hc hL) hH
    rw [Upd.globT_thinIO_close .refl drop hr hR hc, he]
  · obtain ⟨ψ', hψ, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    refine Upd.afterT_intro (fun e he => hφ.of_error (e := e) ?_) fun g σ' hL hH =>
      Fml.thinS?_holds R.th ψ hψ σ' (hφ.of_lands (Upd.lands_thinIO .refl drop hr hR hL) hH)
    rw [Upd.globT_thinIO .refl drop hr U hR, he]

/-- `{U}_m ψ`, the scope ends `ψ` begins with merged in where `absorb`
(`Fml.absorbPops`): asked only where `ψ` is an update, so that the kernel
never looks into a postcondition. -/
def Fml.absorbIf {Δ : Ctx} (absorb : Bool) (m : Modality) (U : Upd C Γ Δ) (ψ : Fml C Δ) : Fml C Γ :=
  if absorb then Fml.absorbPops m U ψ else .upd m U ψ

theorem Fml.absorbIf_holds {Δ : Ctx} {absorb : Bool} {m : Modality} {U : Upd C Γ Δ} {ψ : Fml C Δ}
    (σ : State C Γ) (h : holds σ (Fml.absorbIf absorb m U ψ)) : holds σ (.upd m U ψ) := by
  cases absorb
  · exact h
  · exact Fml.absorbPops_holds σ h

/-- **`simplifyUpdate`** on `{U}_m ψ` past the program: the scope ends after
it merged in (where `absorb`), the shadowed writes dropped, then every
declaration nothing reads afterwards (`every`), else the ones `U` ends
itself; `none` where nothing goes. -/
def Fml.simpPastTop {Δ : Ctx} (every absorb : Bool) (m : Modality) (U : Upd C Γ Δ) (ψ : Fml C Δ) :
    Option (Fml C Γ) :=
  match (Fml.absorbIf absorb m U ψ).updHead? with
  | some ⟨m', W, ψ'⟩ =>
    let W' := W.shadow m'.isBoxS
    let popped := (Upd.declStack W').2.2
    let r := Fml.dropDeclsTop (fun k => every || popped.contains k) m' W' ψ'
    r.bind fun φ => match φ.updHead? with
      | some h => if h.U.size < W'.size then some φ else none
      | none => none
  | none => none

theorem Fml.simpPastTop_sound {Δ : Ctx} {every absorb : Bool} {m : Modality} {U : Upd C Γ Δ}
    {ψ : Fml C Δ} {φ : Fml C Γ} (h : Fml.simpPastTop every absorb m U ψ = some φ) (σ : State C Γ)
    (hφ : holds σ φ) : holds σ (.upd m U ψ) := by
  unfold Fml.simpPastTop at h
  split at h
  · rename_i m' W ψ' hW
    refine Fml.absorbIf_holds (absorb := absorb) σ ?_
    rw [Fml.updHead?_eq hW]
    refine holds_upd_shadow σ ?_
    dsimp only at h
    obtain ⟨φ'', hφ'', hr'⟩ := Option.bind_eq_some_iff.1 h
    have heq : φ'' = φ := by
      split at hr'
      · split at hr'
        · exact Option.some.inj hr'
        · cases hr'
      · cases hr'
    subst heq
    exact Fml.dropDeclsTop_sound hφ'' σ hφ
  · cases h

/-- `bind x ({U} χ)` with the binder dropped, where `U` pops its local and
reads it nowhere (`Upd.thinIO`, the binder's local thinned out of `U`'s
state). -/
def Fml.dropBindTop {Δ : Ctx} {t : LTy} : Fml C (t :: Δ) → Option (Fml C Δ)
  | .upd m U χ => match U.thinIO (Thin.drop .refl) (fun _ => false) with
    | some (_, ⟨.refl, U'⟩) => some (.upd m U' χ)
    | _ => none
  | _ => none

theorem Fml.dropBindTop_sound {Δ : Ctx} {t : LTy} {m₀ : Modality} {x : Var} {ψ : Fml C (t :: Δ)}
    {φ : Fml C Δ} (h : Fml.dropBindTop ψ = some φ) (σ : State C Δ) (hφ : holds σ φ) :
    holds σ (.bind m₀ x t ψ) := by
  cases ψ with
  | upd m U χ =>
    simp only [Fml.dropBindTop] at h
    split at h
    · rename_i n U' hU
      cases h
      refine Modality.forallB_intro fun w => ?_
      have hr := State.ThinOf.push σ w
      refine Upd.afterT_intro (fun e he => hφ.of_error (e := e) ?_) fun g σ' hL hH => hφ.of_lands (g := g) ?_ hH
      · rw [Upd.globT_thinIO (Thin.drop .refl) _ hr U hU, he]
      · exact Upd.lands_thinIO (Thin.drop .refl) _ hr hU hL
    · cases h
  | _ => cases h

/-- `{U}_m ψ` simplified where it can be, else as it is. -/
def Fml.simpPastD {Γ : Ctx} (every absorb : Bool) : Fml C Γ → Fml C Γ
  | .upd m U ψ => (Fml.simpPastTop every absorb m U ψ).getD (.upd m U ψ)
  | φ => φ

theorem Fml.simpPastD_sound {Γ : Ctx} (every absorb : Bool) (φ : Fml C Γ) (σ : State C Γ)
    (h : holds σ (φ.simpPastD every absorb)) : holds σ φ := by
  cases φ with
  | upd m U ψ =>
    simp only [Fml.simpPastD] at h
    cases hs : Fml.simpPastTop every absorb m U ψ with
    | none => rw [hs] at h; exact h
    | some χ => rw [hs] at h; exact Fml.simpPastTop_sound hs σ h
  | _ => exact h

/-- `simplifyUpdate` past the program at position `n` of the spine, a hidden
binder in front of the update absorbed where the update sets it first, or
dropped where the update pops its local and reads it nowhere. -/
def Fml.simpPastAt (every absorb : Bool) : {Γ : Ctx} → Nat → Fml C Γ → Option (Fml C Γ)
  | _, n, .all x p φ => (Fml.simpPastAt every absorb n φ).map (.all x p)
  | _, 0, .bind m x t φ =>
    match (match φ with
      | .upd m' V ψ => (V.absorb x).bind fun V' => Fml.simpPastTop every absorb m' V' ψ
      | _ => none) with
    | some ψ => some ψ
    | none => match Fml.dropBindTop φ with
      | some ψ => some (ψ.simpPastD every absorb)
      | none => (Fml.simpPastAt every absorb 0 φ).map (.bind m x t)
  | _, n + 1, .bind m x t φ => (Fml.simpPastAt every absorb (n + 1) φ).map (.bind m x t)
  | _, 0, .upd m U φ => Fml.simpPastTop every absorb m U φ
  | _, n + 1, .upd m U φ => (Fml.simpPastAt every absorb n φ).map (.upd m U)
  | _, _, _ => none

theorem Fml.simpPastAt_sound (every absorb : Bool) : {Γ : Ctx} → (n : Nat) → (φ : Fml C Γ) → {ψ : Fml C Γ} →
    Fml.simpPastAt every absorb n φ = some ψ → ∀ σ, holds σ ψ → holds σ φ
  | _, n, .all x p φ, ψ₀, h => by
    have h : (Fml.simpPastAt every absorb n φ).map (Fml.all x p) = some ψ₀ := by rw [← h]; cases n <;> rfl
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs v => Fml.simpPastAt_sound every absorb n φ hψ _ (hs v)
  | _, 0, .bind m x t φ, ψ₀, h => by
    simp only [Fml.simpPastAt] at h
    split at h
    · rename_i ψ hψ
      cases h
      split at hψ
      · rename_i m' V χ
        obtain ⟨V', hV', hψ⟩ := Option.bind_eq_some_iff.1 hψ
        exact fun σ hs => holds_bind_absorb hV' σ (Fml.simpPastTop_sound hψ σ hs)
      · cases hψ
    · split at h
      · rename_i ψ hψ
        cases h
        exact fun σ hs => Fml.dropBindTop_sound hψ σ (Fml.simpPastD_sound every absorb ψ σ hs)
      · obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
        exact fun σ hs => Modality.forallB_imp (fun v => Fml.simpPastAt_sound every absorb 0 φ hψ _) hs
  | _, n + 1, .bind m x t φ, ψ₀, h => by
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs => Modality.forallB_imp (fun v => Fml.simpPastAt_sound every absorb (n + 1) φ hψ _) hs
  | _, 0, .upd m U φ, _, h => fun σ hs => Fml.simpPastTop_sound h σ hs
  | _, n + 1, .upd m U φ, _, h => by
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun σ hs => Upd.afterT_imp hs fun σ' a => Fml.simpPastAt_sound every absorb n φ hψ σ' a
  | _, n, .tt, _, h | _, n, .eq .., _, h | _, n, .defined _, _, h | _, n, .not _, _, h
  | _, n, .and .., _, h | _, n, .imp .., _, h | _, n, .modal .., _, h | _, n, .havoc _, _, h
  | _, n, .anon .., _, h => by
    cases n <;> cases h

/-- **`simplifyUpdate`** past the program, at position `n` of the spine
(`Fml.simpPastAt`): every declaration nothing reads afterwards (`every`),
else the ones the update ends itself, which does not ask the line after
what it reads; the scope ends after it merged in where `absorb`. -/
def FmlRw.simplifyPast (n : Nat) (every absorb : Bool) : FmlRw C where
  apply := fun φ => Fml.simpPastAt every absorb n φ
  sound := fun h σ hψ => Fml.simpPastAt_sound every absorb n _ h σ hψ

end SimpPast

end Solidity
