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
  | _, .pvZ i => (Idx.unwk? h i).map .pvZ
  | _, .netOf i a => do pure (.netOf (← Idx.unwk? h i) (← Tm.thinS? h a))
  | _, .app0 o => some (.app0 o)
  | _, .app1 o x => (Tm.thinS? h x).map (.app1 o)
  | _, .app2 o x y => do pure (.app2 o (← Tm.thinS? h x) (← Tm.thinS? h y))
  | _, .app3 o x y z => do pure (.app3 o (← Tm.thinS? h x) (← Tm.thinS? h y) (← Tm.thinS? h z))

/-- `σ'` is `σ` with the locals the thinning drops left out. -/
def State.ThinOf (h : Thin Γ' Γ) (σ' : State C Γ') (σ : State C Γ) : Prop := σ' = σ.thin h

theorem State.ThinOf.thin (h : Thin Γ' Γ) (σ : State C Γ) : State.ThinOf h (σ.thin h) σ := rfl

/-- A local the thinning keeps reads alike with the rest dropped. -/
theorem TEnv.get_unwk? {H : HTy} {h : Thin Γ' Γ} (e : TEnv C H Γ) {t : LTy} {i : Idx Γ t}
    {j : Idx Γ' t} (hj : Idx.unwk? h i = some j) : TEnv.get j (TEnv.thin h e) = TEnv.get i e := by
  rw [TEnv.get_thin_wk, Idx.unwk?_wk h i hj]

/-- **A term that reads no dropped local reads alike with them dropped.** -/
theorem Tm.eval_thinS? (h : Thin Γ' Γ) (σ : State C Γ) :
    {s : Srt} → (t : Tm C Γ s) → {t' : Tm C Γ' s} → Tm.thinS? h t = some t' →
      t'.eval (σ.thin h) = t.eval σ
  | _, .pvV i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    show some (TEnv.get j (TEnv.thin h σ.env)) = _
    rw [TEnv.get_unwk? σ.env hj]
    rfl
  | _, .pvP i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    show TEnv.get j (TEnv.thin h σ.env) = _
    rw [TEnv.get_unwk? σ.env hj]
    rfl
  | _, .pvS i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    show some (TEnv.get j (TEnv.thin h σ.env)) = _
    rw [TEnv.get_unwk? σ.env hj]
    rfl
  | _, .pvI i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    show (TEnv.get j (TEnv.thin h σ.env)).map (·.id) = _
    rw [TEnv.get_unwk? σ.env hj]
    rfl
  | _, .pvZ i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    show some (TEnv.get j (TEnv.thin h σ.env)) = _
    rw [TEnv.get_unwk? σ.env hj]
    rfl
  | _, .netOf i a, _, ht => by
    obtain ⟨j, hj, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨a', ha, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    show (a'.eval (σ.thin h)).bind (Tm.netOfT (TEnv.get j (TEnv.thin h σ.env))) = _
    rw [TEnv.get_unwk? σ.env hj, Tm.eval_thinS? h σ a ha]
    rfl
  | _, .app0 _, _, ht => by cases ht; rfl
  | _, .app1 o x, _, ht => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 ht
    show o.eval σ.glob (x'.eval (σ.thin h)) = o.eval σ.glob (x.eval σ)
    rw [Tm.eval_thinS? h σ x hx]
  | _, .app2 o x y, _, ht => by
    obtain ⟨x', hx, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨y', hy, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    show o.eval σ.glob (x'.eval (σ.thin h)) (y'.eval (σ.thin h)) = o.eval σ.glob (x.eval σ) (y.eval σ)
    rw [Tm.eval_thinS? h σ x hx, Tm.eval_thinS? h σ y hy]
  | _, .app3 o x y z, _, ht => by
    obtain ⟨x', hx, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨y', hy, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨z', hz, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    show o.eval σ.glob (x'.eval (σ.thin h)) (y'.eval (σ.thin h)) (z'.eval (σ.thin h)) =
      o.eval σ.glob (x.eval σ) (y.eval σ) (z.eval σ)
    rw [Tm.eval_thinS? h σ x hx, Tm.eval_thinS? h σ y hy, Tm.eval_thinS? h σ z hz]

/-- **A term that reads no dropped local denotes alike with them dropped.** -/
theorem Tm.denote_thinS? (h : Thin Γ' Γ) (σ : State C Γ) :
    {s : Srt} → (t : Tm C Γ s) → {t' : Tm C Γ' s} → Tm.thinS? h t = some t' →
      t'.denote (σ.thin h) = t.denote σ
  | _, .pvV i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    simp only [Tm.denote, State.thin, State.withEnv, TEnv.get_unwk? σ.env hj]
  | _, .pvP i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    simp only [Tm.denote, State.thin, State.withEnv, TEnv.get_unwk? σ.env hj]
    split <;> rfl
  | _, .pvS i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    simp only [Tm.denote, State.thin, State.withEnv, TEnv.get_unwk? σ.env hj]
  | _, .pvI i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    rfl
  | _, .pvZ i, _, ht => by
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 ht
    simp only [Tm.denote, State.thin, State.withEnv, TEnv.get_unwk? σ.env hj]
  | _, .netOf i a, _, ht => by
    obtain ⟨j, hj, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨a', ha, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    simp only [Tm.denote]
    rw [Tm.denote_thinS? h σ a ha]
    simp only [State.thin, State.withEnv, TEnv.get_unwk? σ.env hj]
  | _, .app0 _, _, ht => by cases ht; rfl
  | _, .app1 o x, _, ht => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 ht
    show o.denote σ.glob (x'.denote (σ.thin h)) = o.denote σ.glob (x.denote σ)
    rw [Tm.denote_thinS? h σ x hx]
  | _, .app2 o x y, _, ht => by
    obtain ⟨x', hx, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨y', hy, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    show o.denote σ.glob (x'.eval (σ.thin h)) (y'.eval (σ.thin h)) (x'.denote (σ.thin h))
        (y'.denote (σ.thin h)) = o.denote σ.glob (x.eval σ) (y.eval σ) (x.denote σ) (y.denote σ)
    rw [Tm.denote_thinS? h σ x hx, Tm.denote_thinS? h σ y hy, Tm.eval_thinS? h σ x hx,
      Tm.eval_thinS? h σ y hy]
  | _, .app3 o x y z, _, ht => by
    obtain ⟨x', hx, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨y', hy, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨z', hz, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    show o.denote (x'.denote (σ.thin h)) (y'.denote (σ.thin h)) (z'.denote (σ.thin h)) =
      o.denote (x.denote σ) (y.denote σ) (z.denote σ)
    rw [Tm.denote_thinS? h σ x hx, Tm.denote_thinS? h σ y hy, Tm.denote_thinS? h σ z hz]

/-- A right-hand side of `Γ` read in `Γ'`. -/
def Rhs.thinS? (h : Thin Γ' Γ) : {t : LTy} → Rhs C Γ t → Option (Rhs C Γ' t)
  | _, .val t => (Tm.thinS? h t).map .val
  | _, .path p => (Tm.thinS? h p).map .path
  | _, .unset => some .unset
  | _, .mref i => (Tm.thinS? h i).map .mref
  | _, .store s => (Tm.thinS? h s).map .store
  | _, .saveNet => some .saveNet
  | _, .saveNetMt => some .saveNetMt
  | _, .zint t => (Tm.thinS? h t).map .zint

theorem Rhs.eval_thinS? (h : Thin Γ' Γ) (σ : State C Γ) :
    {t : LTy} → (r : Rhs C Γ t) → {r' : Rhs C Γ' t} → Rhs.thinS? h r = some r' →
      r'.eval (σ.thin h) = r.eval σ
  | _, .val t, _, hx => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 hx
    exact Tm.eval_thinS? h σ t ht
  | _, .path p, _, hx => by
    obtain ⟨p', hp, rfl⟩ := Option.map_eq_some_iff.1 hx
    show (p'.eval (σ.thin h)).bind _ = (p.eval σ).bind _
    rw [Tm.eval_thinS? h σ p hp]
  | _, .unset, _, hx => by cases hx; rfl
  | _, .mref i, _, hx => by
    obtain ⟨i', hi, rfl⟩ := Option.map_eq_some_iff.1 hx
    show (i'.eval (σ.thin h)).bind _ = (i.eval σ).bind _
    rw [Tm.eval_thinS? h σ i hi]
  | _, .store s, _, hx => by
    obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 hx
    show (s'.eval (σ.thin h)).bind _ = (s.eval σ).bind _
    rw [Tm.eval_thinS? h σ s hs]
  | _, .saveNet, _, hx => by cases hx; rfl
  | _, .saveNetMt, _, hx => by cases hx; rfl
  | _, .zint t, _, hx => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 hx
    exact Tm.eval_thinS? h σ t ht

end ThinS

/-! ## Out of the top local's scope -/

section Down

variable {Γ : Ctx} {u : LTy}

/-- A term read with locals dropped is out of gas where it was. -/
theorem Tm.exhB_thinS? (h : Thin Γ' Γ) (σ : State C Γ) :
    {s : Srt} → (t : Tm C Γ s) → {t' : Tm C Γ' s} → Tm.thinS? h t = some t' →
      t'.exhB (σ.thin h) = t.exhB σ
  | _, .pvV _, _, ht | _, .pvP _, _, ht | _, .pvS _, _, ht | _, .pvI _, _, ht
  | _, .pvZ _, _, ht => by
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 ht; rfl
  | _, .app0 _, _, ht => by cases ht; rfl
  | _, .netOf i a, _, ht => by
    have hw := Tm.eval_thinS? h σ (.netOf i a) ht
    obtain ⟨j, -, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨a', ha, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    simp only [Tm.exhB, hw, Tm.exhB_thinS? h σ a ha]
  | _, .app1 o x, _, ht => by
    have hw := Tm.eval_thinS? h σ (.app1 o x) ht
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 ht
    simp only [Tm.exhB, hw, Tm.exhB_thinS? h σ x hx]
  | _, .app2 o x y, _, ht => by
    have hw := Tm.eval_thinS? h σ (.app2 o x y) ht
    obtain ⟨x', hx, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨y', hy, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    simp only [Tm.exhB, hw, Tm.exhB_thinS? h σ x hx, Tm.exhB_thinS? h σ y hy,
      Tm.eval_thinS? h σ x hx, Tm.eval_thinS? h σ y hy]
  | _, .app3 o x y z, _, ht => by
    have hw := Tm.eval_thinS? h σ (.app3 o x y z) ht
    obtain ⟨x', hx, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨y', hy, ht⟩ := Option.bind_eq_some_iff.1 ht
    obtain ⟨z', hz, ht⟩ := Option.bind_eq_some_iff.1 ht
    cases ht
    simp only [Tm.exhB, hw, Tm.exhB_thinS? h σ x hx, Tm.exhB_thinS? h σ y hy,
      Tm.exhB_thinS? h σ z hz, Tm.eval_thinS? h σ x hx, Tm.eval_thinS? h σ y hy,
      Tm.eval_thinS? h σ z hz]

theorem Rhs.exhB_thinS? (h : Thin Γ' Γ) (σ : State C Γ) {t : LTy} (r : Rhs C Γ t)
    {r' : Rhs C Γ' t} (hr : Rhs.thinS? h r = some r') : r'.exhB (σ.thin h) = r.exhB σ := by
  cases r with
  | val x | path x | mref x | store x | zint x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 hr
    exact Tm.exhB_thinS? h σ x hx
  | unset | saveNet | saveNetMt => cases hr; rfl

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
theorem State.thin_push (σ : State C Γ) (v : u.TDenote C σ.H) :
    (σ.push v).thin (.drop .refl) = σ := rfl

/-- **A term that does not read the top local reads alike below it.** -/
theorem Tm.eval_down? (σ : State C Γ) (v : u.TDenote C σ.H) {s : Srt} (t : Tm C (u :: Γ) s)
    {t' : Tm C Γ s} (h : t.down? = some t') : t'.eval σ = t.eval (σ.push v) :=
  Tm.eval_thinS? (.drop .refl) (σ.push v) t h

theorem Rhs.eval_down? (σ : State C Γ) (v : u.TDenote C σ.H) {t : LTy} (r : Rhs C (u :: Γ) t)
    {r' : Rhs C Γ t} (h : r.down? = some r') : r'.eval σ = r.eval (σ.push v) :=
  Rhs.eval_thinS? (.drop .refl) (σ.push v) r h

theorem UpdElem.globT_down? {Δ : Ctx} (σ : State C Γ) (v : u.TDenote C σ.H) :
    (e : UpdElem C (u :: Γ) Δ) → {e' : UpdElem C Γ Δ} → e.down? = some e' →
      ∀ G, e'.globT σ G = e.globT (σ.push v) G
  | .local i r, _, h, G => by
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM, Rhs.eval_down? σ v r hr]
  | .storage s, _, h, G => by
    obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM, Tm.eval_down? σ v s hs]
  | .memory m, _, h, G => by
    obtain ⟨m', hm, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM, Tm.eval_down? σ v m hm]
    rfl
  | .selfBalance op a, _, h, G => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM, Tm.eval_down? σ v a ha]
    rfl
  | .net r op a, _, h, G => by
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM, Tm.eval_down? σ v r hr, Tm.eval_down? σ v a ha]
  | .pay r a, _, h, G => by
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM, Tm.eval_down? σ v r hr, Tm.eval_down? σ v a ha]
    rfl
  | .netMt r a, _, h, G => by
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM, Tm.eval_down? σ v r hr, Tm.eval_down? σ v a ha]
  | .setBalance a, _, h, G => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM, Tm.eval_down? σ v a ha]

theorem Tm.exhB_down? (σ : State C Γ) (v : u.TDenote C σ.H) {k : Srt} (x : Tm C (u :: Γ) k)
    {x' : Tm C Γ k} (h : x.down? = some x') : x'.exhB σ = x.exhB (σ.push v) :=
  Tm.exhB_thinS? (.drop .refl) (σ.push v) x h

theorem Rhs.exhB_down? (σ : State C Γ) (v : u.TDenote C σ.H) {t : LTy} (r : Rhs C (u :: Γ) t)
    {r' : Rhs C Γ t} (h : r.down? = some r') : r'.exhB σ = r.exhB (σ.push v) :=
  Rhs.exhB_thinS? (.drop .refl) (σ.push v) r h

theorem UpdElem.exhB_down? {Δ : Ctx} (σ : State C Γ) (v : u.TDenote C σ.H)
    (e : UpdElem C (u :: Γ) Δ) {e' : UpdElem C Γ Δ} (h : e.down? = some e') :
    e'.exhB σ = e.exhB (σ.push v) := by
  have hT := @Tm.exhB_down? C Γ u σ v
  cases e with
  | «local» _ r =>
    obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Rhs.exhB_down? σ v r hr
  | storage x | memory x | selfBalance _ x | setBalance x =>
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    exact hT x hx
  | net r _ a | pay r a | netMt r a =>
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    simp only [UpdElem.exhB, hT r hr, hT a ha, Tm.eval_down? σ v r hr, Tm.eval_down? σ v a ha]

theorem UpdElem.okB_down? {Δ : Ctx} (σ : State C Γ) (v : u.TDenote C σ.H)
    (e : UpdElem C (u :: Γ) Δ) {e' : UpdElem C Γ Δ} (h : e.down? = some e') :
    e'.okB σ = e.okB (σ.push v) := by
  rw [← UpdElem.globT_isSome σ e' σ.globG, ← UpdElem.globT_isSome (σ.push v) e σ.globG]
  exact congrArg Option.isSome (UpdElem.globT_down? σ v e h σ.globG)

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
      V'.globT σ = (b.eval σ).bind fun _ => V.globT (σ.push w)
  | _, .nil, _, h => by
    cases h
    show (some σ.globG).bind (fun g => (b.eval σ).bind fun _ => some g) = _
    cases b.eval σ <;> rfl
  | _, .snoc V e, _, h => by
    simp only [Upd.rebase] at h
    obtain ⟨j, -, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · cases h
    · obtain ⟨W, hW, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      show (W.globT σ).bind (e'.globT σ) = _
      rw [Upd.rebase_globT x b σ w V hW]
      have he' : e'.globT σ = e.globT (σ.push w) := funext (UpdElem.globT_down? σ w e he)
      rw [he']
      cases b.eval σ <;> rfl
  | _, .decl V y r, _, h => by
    obtain ⟨W, hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show (W.globT σ).bind (fun g => (r'.eval σ).bind fun _ => some g) = _
    rw [Upd.rebase_globT x b σ w V hW, Rhs.eval_down? σ w r hr]
    cases b.eval σ <;> rfl
  | _, .pop .., _, h => by cases h
  | _, .drop .., _, h => by cases h

/-- **The update rebased leaves the binder's local holding its right-hand
side, and every other local what the update leaves there.** -/
theorem Upd.rebase_held (x : Var) (b : Rhs C Γ u) (σ : State C Γ) (w : u.TDenote C σ.H) :
    {Δ : Ctx} → (V : Upd C (u :: Γ) Δ) → {V' : Upd C Γ Δ} → V.rebase x b = some V' →
      {j : Idx Δ u} → V.baseIdx = some j →
      V'.held j = .rhs b ∧ ∀ {t : LTy} (i : Idx Δ t), i.toNat ≠ j.toNat → ∀ v : t.VDen C,
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
            show r'.eval σ = some v
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
      show r'.eval σ = some v
      rw [Rhs.eval_down? σ w r hr]
      exact hv
    | there k => exact ih.2 k (fun hc => hi (by simp only [Idx.toNat, hc])) v hv
  | _, .pop .., _, h, _, _ => by cases h
  | _, .drop .., _, h, _, _ => by cases h

/-- **The absorbed update computes, from the state above the binder, the
global part the update computes from any value of the binder's local.** -/
theorem Upd.absorb_globT (x : Var) (reorder : Bool) (σ : State C Γ) (w : u.TDenote C σ.H) :
    {Δ : Ctx} → (V : Upd C (u :: Γ) Δ) → {V' : Upd C Γ Δ} → V.absorb x reorder = some V' →
      V'.globT σ = V.globT (σ.push w)
  | _, .nil, _, h => by cases h
  | _, .snoc V e, V', h => by
    simp only [Upd.absorb] at h
    cases hr : Upd.absorb x reorder V with
    | some W =>
      rw [hr] at h
      obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      have ih := Upd.absorb_globT x reorder σ w V hr
      show (W.globT σ).bind (e'.globT σ) = (V.globT (σ.push w)).bind (e.globT (σ.push w))
      have he' : e'.globT σ = e.globT (σ.push w) := funext (UpdElem.globT_down? σ w e he)
      rw [he', ih]
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
            show (r'.eval σ).bind (fun _ => V.globT (σ.push w)) =
              (V.globT (σ.push w)).bind fun g => (r.eval (σ.push w)).bind fun _ => some g
            rw [Rhs.eval_down? σ w r hr']
            cases r.eval (σ.push w) with
            | none => cases V.globT (σ.push w) <;> rfl
            | some a => cases V.globT (σ.push w) <;> rfl
          · cases h
        · cases h
      | _ => cases h
  | _, .decl V y r, _, h => by
    obtain ⟨W, hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show (W.globT σ).bind (fun g => (r'.eval σ).bind fun _ => some g) =
      (V.globT (σ.push w)).bind fun g => (r.eval (σ.push w)).bind fun _ => some g
    rw [Rhs.eval_down? σ w r hr, Upd.absorb_globT x reorder σ w V hW]
    rfl
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
      ∀ {t : LTy} (i : Idx Δ t) (v : t.VDen C), Held.OKV (σ.push w) v (V.held i) →
        Held.OKV σ v (V'.held i)
  | _, .nil, _, h => by cases h
  | _, .snoc V e, V', h => by
    simp only [Upd.absorb] at h
    cases hr : Upd.absorb x reorder V with
    | some W =>
      rw [hr] at h
      obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      have ih : ∀ {t : LTy} (i : Idx _ t) (v : t.VDen C), Held.OKV (σ.push w) v (V.held i) →
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
          show r'.eval σ = some v
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
              show r'.eval σ = some v
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
      show r'.eval σ = some v
      rw [Rhs.eval_down? σ w r hr]
      exact hv
    | there k => exact Upd.absorb_held x reorder σ w V hW k v hv
  | _, .pop V e, _, h => by
    obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun i v hv => Upd.absorb_held x reorder σ w V hW (i.ext e) v hv
  | _, .drop V e, _, h => by
    obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact fun i v hv => Upd.absorb_held x reorder σ w V hW (i.wk e) v hv

/-- The update rebased is out of gas where the binder's right-hand side or
the update is. -/
theorem Upd.rebase_exh (x : Var) (b : Rhs C Γ u) (σ : State C Γ) (w : u.TDenote C σ.H) :
    {Δ : Ctx} → (V : Upd C (u :: Γ) Δ) → {V' : Upd C Γ Δ} → V.rebase x b = some V' →
      V'.exhAny σ = (b.exhB σ || V.exhAny (σ.push w)) ∧
        V'.exhOk σ = (((b.eval σ).isSome || b.exhB σ) && V.exhOk (σ.push w))
  | _, .nil, _, h => by
    cases h
    simp only [Upd.exhAny, Upd.exhOk, Bool.false_or, Bool.or_false, Bool.true_and,
      Bool.and_true, and_self]
  | _, .snoc V e, _, h => by
    simp only [Upd.rebase] at h
    obtain ⟨j, -, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · cases h
    · obtain ⟨W, hW, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      obtain ⟨ih₁, ih₂⟩ := Upd.rebase_exh x b σ w V hW
      simp only [Upd.exhAny, Upd.exhOk, ih₁, ih₂, UpdElem.exhB_down? σ w e he,
        UpdElem.okB_down? σ w e he, Bool.or_assoc, Bool.and_assoc, and_self]
  | _, .decl V y r, _, h => by
    obtain ⟨W, hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    obtain ⟨ih₁, ih₂⟩ := Upd.rebase_exh x b σ w V hW
    simp only [Upd.exhAny, Upd.exhOk, ih₁, ih₂, Rhs.eval_down? σ w r hr,
      Rhs.exhB_down? σ w r hr, Bool.or_assoc, Bool.and_assoc, and_self]
  | _, .pop .., _, h => by cases h
  | _, .drop .., _, h => by cases h

/-- **The absorbed update is out of gas where the update is**, read from the
state above the binder. -/
theorem Upd.absorb_exh (x : Var) (reorder : Bool) (σ : State C Γ) (w : u.TDenote C σ.H) :
    {Δ : Ctx} → (V : Upd C (u :: Γ) Δ) → {V' : Upd C Γ Δ} → V.absorb x reorder = some V' →
      V'.exhAny σ = V.exhAny (σ.push w) ∧ V'.exhOk σ = V.exhOk (σ.push w)
  | _, .nil, _, h => by cases h
  | _, .snoc V e, V', h => by
    simp only [Upd.absorb] at h
    cases hr : Upd.absorb x reorder V with
    | some W =>
      rw [hr] at h
      obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      obtain ⟨ih₁, ih₂⟩ := Upd.absorb_exh x reorder σ w V hr
      simp only [Upd.exhAny, Upd.exhOk, ih₁, ih₂, UpdElem.exhB_down? σ w e he,
        UpdElem.okB_down? σ w e he, and_self]
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
          · obtain ⟨r', hr', h⟩ := Option.bind_eq_some_iff.1 h
            obtain ⟨h₁, h₂⟩ := Upd.rebase_exh x r' σ w V h
            simp only [Upd.exhAny, Upd.exhOk, h₁, h₂, UpdElem.exhB, UpdElem.okB,
              Rhs.eval_down? σ w r hr', Rhs.exhB_down? σ w r hr',
              Bool.or_comm (Rhs.exhB (σ.push w) r), Bool.and_comm (V.exhOk (σ.push w)),
              and_self]
          · cases h
        · cases h
      | _ => cases h
  | _, .decl V y r, _, h => by
    obtain ⟨W, hW, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨r', hr, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    obtain ⟨ih₁, ih₂⟩ := Upd.absorb_exh x reorder σ w V hW
    simp only [Upd.exhAny, Upd.exhOk, ih₁, ih₂, Rhs.eval_down? σ w r hr,
      Rhs.exhB_down? σ w r hr, and_self]
  | _, .pop V _, _, h => by
    obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.absorb_exh x reorder σ w V hW
  | _, .drop V _, _, h => by
    obtain ⟨W, hW, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Upd.absorb_exh x reorder σ w V hW

/-- **`bind x ({x := e ‖ U} φ)` from `{x :=decl e ‖ U} φ`.** -/
theorem holds_bind_absorb {m m' : Modality} {x : Var} {reorder : Bool} {Δ : Ctx}
    {V : Upd C (u :: Γ) Δ} {V' : Upd C Γ Δ} (hV : V.absorb x reorder = some V') {ψ : Fml C Δ}
    (σ : State C Γ)
    (h : holds σ (.upd m' V' ψ)) : holds σ (.bind m x u (.upd m' V ψ)) :=
  Modality.forallB_intro fun w => by
    have hg := Upd.absorb_globT x reorder σ w V hV
    refine Upd.afterT_introX (fun he => (h.of_none (hg.trans he)).imp_right fun hx => ?_)
      fun g σ' hL => ?_
    · obtain ⟨h₁, h₂⟩ := Upd.absorb_exh x reorder σ w V hV
      simp only [Upd.exh, h₁, h₂] at hx
      exact hx
    exact h.of_lands (g := g) ⟨hg.trans hL.1, hL.2.1, fun i => (Held.OK_iff_OKV _ _ _ _).2
      (Upd.absorb_held x reorder σ w V hV i _ ((Held.OK_iff_OKV _ _ _ _).1 (hL.2.2 i)))⟩

end Absorb

/-! ## A shadowed state write dropped -/

section Shadow

variable {Γ : Ctx}

/-- `Tm.spineHas`' compiled twin. -/
def Tm.spineHasM {k : Srt} (S : Tm C Γ k) : {s : Srt} → Tm C Γ s → Bool
  | _, .app1 _ a => a.beqR S || Tm.spineHasM S a
  | _, .app2 _ a _ => a.beqR S || Tm.spineHasM S a
  | _, .app3 _ a _ _ => a.beqR S || Tm.spineHasM S a
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .netOf .. | _, .app0 _ | _, .pvZ _ => false

/-- `S` is read first, strictly inside `T`: the first argument of a symbol of
`T`, or of one below it (every symbol reads its first argument first: where
it halts, the symbol does).  Generic in both sorts, by the recursor. -/
@[implemented_by Tm.spineHasM]
def Tm.spineHas {k : Srt} (S : Tm C Γ k) {s : Srt} (T : Tm C Γ s) : Bool :=
  Tm.rec (motive := fun _ _ => Bool)
    (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false) (fun _ _ _ => false)
    (fun _ => false)
    (fun _ a ih => a.beqR S || ih)
    (fun _ a _ iha _ => a.beqR S || iha)
    (fun _ a _ _ iha _ _ => a.beqR S || iha) (fun _ => false) T

theorem Tm.spineHas_eq_spineHasM {k : Srt} (S : Tm C Γ k) {s : Srt} (T : Tm C Γ s) :
    Tm.spineHas S T = Tm.spineHasM S T := by
  induction T with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ _ | app0 _ | pvZ _ => rfl
  | app1 o a ih => simp only [Tm.spineHasM, ← ih]; rfl
  | app2 o a _ ih _ => simp only [Tm.spineHasM, ← ih]; rfl
  | app3 o a _ _ ih _ _ => simp only [Tm.spineHasM, ← ih]; rfl

/-- `S` is read before anything else of `T`: `T` is `S`, or `S` is on its
spine. -/
def Tm.onSpineS {k : Srt} (T S : Tm C Γ k) : Bool := T.beqR S || Tm.spineHas S T

/-- A term with `S` on its spine halts wherever `S` does. -/
theorem Tm.spineHas_none {k : Srt} {S : Tm C Γ k} {σ : State C Γ} (hS : S.eval σ = none)
    {s : Srt} (T : Tm C Γ s) (h : Tm.spineHasM S T = true) : T.eval σ = none := by
  induction T with
  | pvV _ | pvP _ | pvS _ | pvI _ | netOf _ _ _ | app0 _ | pvZ _ =>
    exact absurd h Bool.false_ne_true
  | app1 o a iha =>
    simp only [Tm.spineHasM, Bool.or_eq_true] at h
    refine Tm.eval_app1_none o a ?_
    rcases h with h | h
    · cases Tm.sigma_eq_of_beqR h; exact hS
    · exact iha h
  | app2 o a b iha _ =>
    simp only [Tm.spineHasM, Bool.or_eq_true] at h
    refine Tm.eval_app2_none o a b ?_
    rcases h with h | h
    · cases Tm.sigma_eq_of_beqR h; exact hS
    · exact iha h
  | app3 o a b c iha _ _ =>
    simp only [Tm.spineHasM, Bool.or_eq_true] at h
    refine Tm.eval_app3_none o a b c ?_
    rcases h with h | h
    · cases Tm.sigma_eq_of_beqR h; exact hS
    · exact iha h

/-- A term on the spine of `S` halts wherever `S` does. -/
theorem Tm.onSpineS_none {k : Srt} {S : Tm C Γ k} {σ : State C Γ} (hS : S.eval σ = none)
    (T : Tm C Γ k) (h : T.onSpineS S = true) : T.eval σ = none := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rw [Tm.eq_of_beqR h]; exact hS
  · exact Tm.spineHas_none hS T (Tm.spineHas_eq_spineHasM S T ▸ h)

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
      if Q.any (·.onSpineS M) then Upd.dropSh P Q U else .snoc (Upd.dropSh P (M :: Q) U) (.memory M)
    | e => .snoc (Upd.dropSh P Q U) e
  | _, .decl U x r => .decl (Upd.dropSh P Q U) x r
  | _, .pop U h => .pop (Upd.dropSh P Q U) h
  | _, .drop U h => .drop (Upd.dropSh P Q U) h

/-- A typed global part's memory, as a heap grown from `H`. -/
def GlobT.memG {H : HTy} (g : GlobT C H) : Grown H (fun _ => Unit) := ⟨g.2, g.1.heap, ()⟩

/-- A typed global part with its storage and memory replaced. -/
def GlobT.withSM {H : HTy} (g : GlobT C H) (st : Storage C) (μ : Grown H (fun _ => Unit)) :
    GlobT C H :=
  ⟨State.mk st μ.H' μ.heap () g.1.net g.1.selfBalance g.1.tx, μ.ext⟩

theorem GlobT.withSM_self {H : HTy} (g : GlobT C H) : g.withSM g.1.storage g.memG = g := rfl

/-- An element that writes neither the storage nor the memory computes alike
from a global part with another storage and memory. -/
theorem UpdElem.globT_withSM {Δ : Ctx} (σ₀ : State C Γ) (st : Storage C)
    (μ : Grown σ₀.H (fun _ => Unit)) (τ : GlobT C σ₀.H) :
    (e : UpdElem C Γ Δ) → (∀ S, e ≠ .storage S) → (∀ M, e ≠ .memory M) →
      e.globT σ₀ (τ.withSM st μ) = (e.globT σ₀ τ).map (·.withSM st μ)
  | .local i r, _, _ => by
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM]
    cases r.eval σ₀ <;> rfl
  | .storage S, h, _ => absurd rfl (h S)
  | .memory M, _, h => absurd rfl (h M)
  | .selfBalance op a, _, _ => by
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM]
    cases a.eval σ₀ with
    | none => rfl
    | some v =>
      simp only [Option.bind_some]
      cases PrimTy.uint.ofInt? (op.apply σ₀.selfBalance.1 v.1) <;> rfl
  | .net r op a, _, _ => by
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM]
    cases r.eval σ₀ <;> cases a.eval σ₀ <;> rfl
  | .pay r a, _, _ => by
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM]
    cases r.eval σ₀ with
    | none => rfl
    | some v =>
      cases a.eval σ₀ with
      | none => rfl
      | some w =>
        simp only [Option.bind_some, Option.map_some]
        split <;> rfl
  | .netMt r a, _, _ => by
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM]
    cases r.eval σ₀ <;> cases a.eval σ₀ <;> rfl
  | .setBalance a, _, _ => by
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM]
    cases a.eval σ₀ <;> rfl

theorem UpdElem.globT_storage {Δ : Ctx} (σ₀ : State C Γ) (S : Tm C Γ .st) (τ : GlobT C σ₀.H) :
    (UpdElem.storage S : UpdElem C Γ Δ).globT σ₀ τ = (S.eval σ₀).map τ.withStorage := by
  rw [UpdElem.globT_eq_globTM]
  simp only [UpdElem.globTM]
  cases S.eval σ₀ <;> rfl

theorem UpdElem.globT_memory {Δ : Ctx} (σ₀ : State C Γ) (M : Tm C Γ .mem) (τ : GlobT C σ₀.H) :
    (UpdElem.memory M : UpdElem C Γ Δ).globT σ₀ τ = (M.eval σ₀).map τ.withMem := by
  rw [UpdElem.globT_eq_globTM]
  simp only [UpdElem.globTM]
  cases M.eval σ₀ <;> rfl

/-- How the global part an update computes and the one with the shadowed
writes dropped (`P`, `Q` the writes still to come) relate: one but for the
storage (where a write is to come) and the memory, or the first halted, and
the second too or on a shadowing write that halts. -/
def ShRel (σ₀ : State C Γ) (P : List (Tm C Γ .st)) (Q : List (Tm C Γ .mem))
    (a b : Option (GlobT C σ₀.H)) : Prop :=
  (∃ τ st μ, a = some τ ∧ b = some (τ.withSM st μ) ∧ (P = [] → st = τ.1.storage) ∧
      (Q = [] → μ = τ.memG)) ∨
    (a = none ∧ (b = none ∨ (∃ T ∈ P, T.eval σ₀ = none) ∨ (∃ M ∈ Q, M.eval σ₀ = none)))

theorem ShRel.bind_globT {σ₀ : State C Γ} {P : List (Tm C Γ .st)} {Q : List (Tm C Γ .mem)}
    {Δ : Ctx} {a b : Option (GlobT C σ₀.H)} (h : ShRel σ₀ P Q a b) (e : UpdElem C Γ Δ)
    (hS : ∀ S, e ≠ .storage S) (hM : ∀ M, e ≠ .memory M) :
    ShRel σ₀ P Q (a.bind (e.globT σ₀)) (b.bind (e.globT σ₀)) := by
  rcases h with ⟨τ, st, μ, rfl, rfl, h₁, h₂⟩ | ⟨rfl, h⟩
  · simp only [Option.bind_some]
    rw [UpdElem.globT_withSM σ₀ st μ τ e hS hM]
    cases hw : e.globT σ₀ τ with
    | none => exact .inr ⟨rfl, .inl rfl⟩
    | some ρ =>
      have hρ : ρ.withSM ρ.1.storage ρ.memG = ρ := rfl
      have hτ := UpdElem.globT_withSM σ₀ τ.1.storage τ.memG τ e hS hM
      rw [GlobT.withSM_self, hw] at hτ
      have hτ : ρ = ρ.withSM τ.1.storage τ.memG := Option.some.inj hτ
      refine .inl ⟨ρ, st, μ, rfl, rfl, fun hP => ?_, fun hQ => ?_⟩
      · rw [h₁ hP, hτ]; rfl
      · rw [h₂ hQ, hτ]; rfl
  · refine .inr ⟨rfl, ?_⟩
    rcases h with rfl | h
    · exact .inl rfl
    · exact .inr h

/-- **Dropping the shadowed writes leaves the global part, or a halt a
halt.** -/
theorem Upd.dropSh_rel (σ₀ : State C Γ) : {Δ : Ctx} → (U : Upd C Γ Δ) →
    (P : List (Tm C Γ .st)) → (Q : List (Tm C Γ .mem)) →
      ShRel σ₀ P Q (U.globT σ₀) ((U.dropSh P Q).globT σ₀)
  | _, .nil, P, Q => .inl ⟨σ₀.globG, σ₀.globG.1.storage, σ₀.globG.memG, rfl, rfl,
      fun _ => rfl, fun _ => rfl⟩
  | Δ₁, .snoc U (.storage S), P, Q => by
    simp only [Upd.dropSh]
    split
    · rename_i hP
      obtain ⟨T, hT, hTS⟩ := List.any_eq_true.1 hP
      show ShRel σ₀ P Q ((U.globT σ₀).bind (UpdElem.globT (Δ := Δ₁) σ₀ (.storage S)))
        ((U.dropSh P Q).globT σ₀)
      rcases Upd.dropSh_rel σ₀ U P Q with ⟨τ, st, μ, ha, hb, h₁, h₂⟩ | ⟨ha, h⟩
      · rw [ha, hb, Option.bind_some, UpdElem.globT_storage]
        cases hs : S.eval σ₀ with
        | none => exact .inr ⟨rfl, .inr (.inl ⟨T, hT, Tm.onSpineS_none hs T hTS⟩)⟩
        | some g =>
          refine .inl ⟨τ.withStorage g, st, μ, rfl, rfl,
            fun hP' => absurd hP' (List.ne_nil_of_mem hT), fun hQ => ?_⟩
          rw [h₂ hQ]; rfl
      · rw [ha]
        exact .inr ⟨rfl, h⟩
    · show ShRel σ₀ P Q ((U.globT σ₀).bind (UpdElem.globT (Δ := Δ₁) σ₀ (.storage S)))
        (((U.dropSh (S :: P) Q).globT σ₀).bind (UpdElem.globT (Δ := Δ₁) σ₀ (.storage S)))
      rcases Upd.dropSh_rel σ₀ U (S :: P) Q with ⟨τ, st, μ, ha, hb, h₁, h₂⟩ | ⟨ha, h⟩
      · rw [ha, hb, Option.bind_some, Option.bind_some, UpdElem.globT_storage,
          UpdElem.globT_storage]
        cases hs : S.eval σ₀ with
        | none => exact .inr ⟨rfl, .inl rfl⟩
        | some g =>
          refine .inl ⟨τ.withStorage g, g, μ, rfl, rfl, fun _ => rfl, fun hQ => ?_⟩
          rw [h₂ hQ]; rfl
      · rw [ha]
        refine .inr ⟨rfl, ?_⟩
        rcases h with hb | ⟨T, hT, hTe⟩ | hM
        · rw [hb]; exact .inl rfl
        · rcases List.mem_cons.1 hT with rfl | hT
          · cases (U.dropSh (T :: P) Q).globT σ₀ with
            | none => exact .inl rfl
            | some ρ =>
              refine .inl ?_
              rw [Option.bind_some, UpdElem.globT_storage, hTe]
              rfl
          · exact .inr (.inl ⟨T, hT, hTe⟩)
        · exact .inr (.inr hM)
  | Δ₁, .snoc U (.memory M), P, Q => by
    simp only [Upd.dropSh]
    split
    · rename_i hQ
      obtain ⟨N, hN, hNM⟩ := List.any_eq_true.1 hQ
      show ShRel σ₀ P Q ((U.globT σ₀).bind (UpdElem.globT (Δ := Δ₁) σ₀ (.memory M)))
        ((U.dropSh P Q).globT σ₀)
      rcases Upd.dropSh_rel σ₀ U P Q with ⟨τ, st, μ, ha, hb, h₁, h₂⟩ | ⟨ha, h⟩
      · rw [ha, hb, Option.bind_some, UpdElem.globT_memory]
        cases hs : M.eval σ₀ with
        | none => exact .inr ⟨rfl, .inr (.inr ⟨N, hN, Tm.onSpineS_none hs N hNM⟩)⟩
        | some g =>
          refine .inl ⟨τ.withMem g, st, μ, rfl, rfl, fun hP => ?_,
            fun hQ' => absurd hQ' (List.ne_nil_of_mem hN)⟩
          rw [h₁ hP]; rfl
      · rw [ha]
        exact .inr ⟨rfl, h⟩
    · show ShRel σ₀ P Q ((U.globT σ₀).bind (UpdElem.globT (Δ := Δ₁) σ₀ (.memory M)))
        (((U.dropSh P (M :: Q)).globT σ₀).bind (UpdElem.globT (Δ := Δ₁) σ₀ (.memory M)))
      rcases Upd.dropSh_rel σ₀ U P (M :: Q) with ⟨τ, st, μ, ha, hb, h₁, h₂⟩ | ⟨ha, h⟩
      · rw [ha, hb, Option.bind_some, Option.bind_some, UpdElem.globT_memory,
          UpdElem.globT_memory]
        cases hs : M.eval σ₀ with
        | none => exact .inr ⟨rfl, .inl rfl⟩
        | some g =>
          refine .inl ⟨τ.withMem g, st, g, rfl, rfl, fun hP => ?_, fun _ => rfl⟩
          rw [h₁ hP]; rfl
      · rw [ha]
        refine .inr ⟨rfl, ?_⟩
        rcases h with hb | hP | ⟨N, hN, hNe⟩
        · rw [hb]; exact .inl rfl
        · exact .inr (.inl hP)
        · rcases List.mem_cons.1 hN with rfl | hN
          · cases (U.dropSh P (N :: Q)).globT σ₀ with
            | none => exact .inl rfl
            | some ρ =>
              refine .inl ?_
              rw [Option.bind_some, UpdElem.globT_memory, hNe]
              rfl
          · exact .inr (.inr ⟨N, hN, hNe⟩)
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
    show ShRel σ₀ P Q ((U.globT σ₀).bind fun g => (r.eval σ₀).bind fun _ => some g)
      (((U.dropSh P Q).globT σ₀).bind fun g => (r.eval σ₀).bind fun _ => some g)
    rcases ih with ⟨τ, st, μ, ha, hb, h₁, h₂⟩ | ⟨ha, h⟩
    · rw [ha, hb, Option.bind_some, Option.bind_some]
      cases r.eval σ₀ with
      | none => exact .inr ⟨rfl, .inl rfl⟩
      | some w => exact .inl ⟨τ, st, μ, rfl, rfl, h₁, h₂⟩
    · rw [ha]
      refine .inr ⟨rfl, ?_⟩
      rcases h with hb | h
      · rw [hb]; exact .inl rfl
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

/-- A term out of gas with `S` on its spine, `S` halting: `S` is out of gas
(what halts the term first is `S`). -/
theorem Tm.spineHas_exhB {k : Srt} {S : Tm C Γ k} {σ : State C Γ} (hS : S.eval σ = none) :
    {s : Srt} → (T : Tm C Γ s) → Tm.spineHasM S T = true → T.exhB σ = true → S.exhB σ = true
  | _, .app1 o a, h, hx => by
    simp only [Tm.spineHasM, Bool.or_eq_true] at h
    simp only [Tm.exhB, Bool.and_eq_true] at hx
    rcases h with h | h
    · cases Tm.sigma_eq_of_beqR h; exact hx.2
    · exact Tm.spineHas_exhB hS a h hx.2
  | _, .app2 o a b, h, hx => by
    simp only [Tm.spineHasM, Bool.or_eq_true] at h
    have ha : a.eval σ = none := by
      rcases h with h | h
      · cases Tm.sigma_eq_of_beqR h; exact hS
      · exact Tm.spineHas_none hS a h
    simp only [Tm.exhB, ha, Op2.exhB_none_fst, Option.isSome_none, Bool.and_false,
      Bool.or_false, Bool.false_or, Bool.and_eq_true] at hx
    rcases h with h | h
    · cases Tm.sigma_eq_of_beqR h; exact hx.2.1
    · exact Tm.spineHas_exhB hS a h hx.2.1
  | _, .app3 o a b c, h, hx => by
    simp only [Tm.spineHasM, Bool.or_eq_true] at h
    have ha : a.eval σ = none := by
      rcases h with h | h
      · cases Tm.sigma_eq_of_beqR h; exact hS
      · exact Tm.spineHas_none hS a h
    simp only [Tm.exhB, ha, Op3.exhB_none_fst, Option.isSome_none, Bool.and_false,
      Bool.false_and, Bool.or_false, Bool.false_or, Bool.and_eq_true] at hx
    rcases h with h | h
    · cases Tm.sigma_eq_of_beqR h; exact hx.2.1.1
    · exact Tm.spineHas_exhB hS a h hx.2.1.1
  | _, .pvV _, h, _ | _, .pvP _, h, _ | _, .pvS _, h, _ | _, .pvI _, h, _ | _, .netOf .., h, _
  | _, .app0 _, h, _ => by simp only [Tm.spineHasM, Bool.false_eq_true] at h

/-- What a term that returns or is out of gas reads first returns or is out
of gas. -/
theorem Tm.onSpineS_okx {k : Srt} {T S : Tm C Γ k} {σ : State C Γ} (h : T.onSpineS S = true)
    (hT : (T.eval σ).isSome = true ∨ T.exhB σ = true) :
    (S.eval σ).isSome = true ∨ S.exhB σ = true := by
  rcases Bool.or_eq_true_iff.mp h with h | h
  · obtain rfl := Tm.eq_of_beqR h; exact hT
  · cases hS : S.eval σ with
    | some _ => exact .inl rfl
    | none =>
      have hT' := Tm.spineHas_none hS T (Tm.spineHas_eq_spineHasM S T ▸ h)
      rw [hT'] at hT
      exact .inr (Tm.spineHas_exhB hS T (Tm.spineHas_eq_spineHasM S T ▸ h)
        (hT.resolve_left (by simp only [Option.isSome_none, Bool.false_eq_true, not_false_eq_true])))

/-- **Dropping shadowed writes keeps exhaustion**: a dropped write lies on
the spine of a later one, which returns or is out of gas where the dropped
update reverts nowhere. -/
theorem Upd.dropSh_exh (σ₀ : State C Γ) : {Δ : Ctx} → (U : Upd C Γ Δ) →
    (P : List (Tm C Γ .st)) → (Q : List (Tm C Γ .mem)) →
    (∀ T ∈ P, (T.eval σ₀).isSome = true ∨ T.exhB σ₀ = true) →
    (∀ M ∈ Q, (M.eval σ₀).isSome = true ∨ M.exhB σ₀ = true) →
    (U.dropSh P Q).exhOk σ₀ = true →
      U.exhOk σ₀ = true ∧ ((U.dropSh P Q).exhAny σ₀ = true → U.exhAny σ₀ = true)
  | _, .nil, _, _, _, _, _ => ⟨rfl, id⟩
  | _, .snoc U (.storage S), P, Q, hP, hQ, hk => by
    simp only [Upd.dropSh] at hk ⊢
    by_cases hp : (P.any fun x => x.onSpineS S) = true
    · rw [if_pos hp] at hk ⊢
      obtain ⟨T, hT, hTS⟩ := List.any_eq_true.1 hp
      obtain ⟨ih₁, ih₂⟩ := Upd.dropSh_exh σ₀ U P Q hP hQ hk
      have hS := Tm.onSpineS_okx hTS (hP T hT)
      refine ⟨?_, fun h => ?_⟩
      · simp only [Upd.exhOk, ih₁, Bool.true_and, UpdElem.okB, UpdElem.exhB, Bool.or_eq_true]
        exact hS
      · simp only [Upd.exhAny, ih₂ h, Bool.true_or]
    · rw [if_neg hp] at hk ⊢
      simp only [Upd.exhOk, Bool.and_eq_true, Bool.or_eq_true, UpdElem.okB, UpdElem.exhB] at hk
      have hS : (S.eval σ₀).isSome = true ∨ S.exhB σ₀ = true := hk.2
      obtain ⟨ih₁, ih₂⟩ := Upd.dropSh_exh σ₀ U (S :: P) Q
        (fun T hT => (List.mem_cons.1 hT).elim (fun e => e ▸ hS) (hP T)) hQ hk.1
      refine ⟨?_, fun h => ?_⟩
      · simp only [Upd.exhOk, ih₁, Bool.true_and, UpdElem.okB, UpdElem.exhB, Bool.or_eq_true]
        exact hS
      · simp only [Upd.exhAny, Bool.or_eq_true] at h ⊢
        exact h.imp_left ih₂
  | _, .snoc U (.memory M), P, Q, hP, hQ, hk => by
    simp only [Upd.dropSh] at hk ⊢
    by_cases hq : (Q.any fun x => x.onSpineS M) = true
    · rw [if_pos hq] at hk ⊢
      obtain ⟨N, hN, hNM⟩ := List.any_eq_true.1 hq
      obtain ⟨ih₁, ih₂⟩ := Upd.dropSh_exh σ₀ U P Q hP hQ hk
      have hM := Tm.onSpineS_okx hNM (hQ N hN)
      refine ⟨?_, fun h => ?_⟩
      · simp only [Upd.exhOk, ih₁, Bool.true_and, UpdElem.okB, UpdElem.exhB, Bool.or_eq_true]
        exact hM
      · simp only [Upd.exhAny, ih₂ h, Bool.true_or]
    · rw [if_neg hq] at hk ⊢
      simp only [Upd.exhOk, Bool.and_eq_true, Bool.or_eq_true, UpdElem.okB, UpdElem.exhB] at hk
      have hM : (M.eval σ₀).isSome = true ∨ M.exhB σ₀ = true := hk.2
      obtain ⟨ih₁, ih₂⟩ := Upd.dropSh_exh σ₀ U P (M :: Q) hP
        (fun N hN => (List.mem_cons.1 hN).elim (fun e => e ▸ hM) (hQ N)) hk.1
      refine ⟨?_, fun h => ?_⟩
      · simp only [Upd.exhOk, ih₁, Bool.true_and, UpdElem.okB, UpdElem.exhB, Bool.or_eq_true]
        exact hM
      · simp only [Upd.exhAny, Bool.or_eq_true] at h ⊢
        exact h.imp_left ih₂
  | _, .snoc U (.local _ _), P, Q, hP, hQ, hk | _, .snoc U (.selfBalance _ _), P, Q, hP, hQ, hk
  | _, .snoc U (.net _ _ _), P, Q, hP, hQ, hk | _, .snoc U (.pay _ _), P, Q, hP, hQ, hk
  | _, .snoc U (.netMt _ _), P, Q, hP, hQ, hk | _, .snoc U (.setBalance _), P, Q, hP, hQ, hk => by
    simp only [Upd.dropSh, Upd.exhOk, Bool.and_eq_true] at hk
    obtain ⟨ih₁, ih₂⟩ := Upd.dropSh_exh σ₀ U P Q hP hQ hk.1
    refine ⟨?_, fun h => ?_⟩
    · simp only [Upd.exhOk, ih₁, hk.2, Bool.and_self]
    · simp only [Upd.dropSh, Upd.exhAny, Bool.or_eq_true] at h ⊢
      exact h.imp_left ih₂
  | _, .decl U x r, P, Q, hP, hQ, hk => by
    simp only [Upd.dropSh, Upd.exhOk, Bool.and_eq_true] at hk
    obtain ⟨ih₁, ih₂⟩ := Upd.dropSh_exh σ₀ U P Q hP hQ hk.1
    refine ⟨?_, fun h => ?_⟩
    · simp only [Upd.exhOk, ih₁, hk.2, Bool.and_self]
    · simp only [Upd.dropSh, Upd.exhAny, Bool.or_eq_true] at h ⊢
      exact h.imp_left ih₂
  | _, .pop U e, P, Q, hP, hQ, hk => Upd.dropSh_exh σ₀ U P Q hP hQ hk
  | _, .drop U e, P, Q, hP, hQ, hk => Upd.dropSh_exh σ₀ U P Q hP hQ hk

/-- **`{U} φ` from `U` with its shadowed writes dropped.** -/
theorem holds_upd_dropSh {m : Modality} {Δ : Ctx} {U : Upd C Γ Δ} {φ : Fml C Δ} (σ : State C Γ)
    (h : holds σ (.upd m (U.dropSh [] []) φ)) : holds σ (.upd m U φ) := by
  have hr := Upd.dropSh_rel σ U [] []
  refine Upd.afterT_of_lands (fun he h' => ?_) (fun g σ' hL => ?_) h
  · rcases hr with ⟨τ, _, _, ha, _⟩ | ⟨_, hb | ⟨_, hT, _⟩ | ⟨_, hM, _⟩⟩
    · rw [he] at ha; cases ha
    · refine (h'.of_none hb).imp_right fun hx => ?_
      obtain ⟨hx₁, hx₂⟩ := Bool.and_eq_true_iff.1 hx
      obtain ⟨h₁, h₂⟩ := Upd.dropSh_exh σ U [] [] nofun nofun hx₂
      exact Bool.and_eq_true_iff.2 ⟨h₂ hx₁, h₁⟩
    · nomatch hT
    · nomatch hM
  · refine ⟨?_, hL.2.1, fun i => ?_⟩
    · rcases hr with ⟨τ, st, μ, ha, hb, h₁, h₂⟩ | ⟨ha, _⟩
      · rw [hL.1] at ha
        cases ha
        rw [h₁ rfl, h₂ rfl, GlobT.withSM_self] at hb
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
  refine Upd.afterT_intro (fun he => ?_) fun _ σ' hL => h.of_lands hL
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

`[{storage := S}] φ ⇝ φ[S/storage]`, past the program, `φ` first-order.
The substitution is the storage merge's (`Tm.substP`,
`Calculus/StatePartsScoped.lean`: `storage` by `S`, a push slot and an index
check read in `S`), so a substituted term reads before the write as the term
reads where it lands (`Tm.substP_eval`).  An equation reads its terms
through `denote`, which the substitution keeps up to `Equiv`
(`Tm.substP_denote`): each typed symbol's denotation respects `Equiv` of its
arguments' (`Srt.DEquiv`, `Op0.denote_congrP` … `Op3.denote_congr`), and
`S` denotes, up to `Equiv`, the storage it leaves (`Tm.denote_eval`). -/

section WithSt

open Theory Theory.StValue

/-- Two denotations of a sort agree in the Theory: `Equiv` for a value or a
storage, equal paths. -/
def Srt.DEquiv : (s : Srt) → s.TDen → s.TDen → Prop
  | .val _ => StValue.Equiv
  | .path _ => Eq
  | .st => Struct.Equiv
  | .sv _ => StValue.Equiv
  | .sts _ => Struct.Equiv
  | .spath _ _ => Eq
  | .kint => StValue.Equiv
  | .ident _ | .addr _ | .mem | .mv _ => fun _ _ => True

theorem Srt.DEquiv.refl : (s : Srt) → (d : s.TDen) → Srt.DEquiv s d d
  | .val _, _ | .st, _ | .sv _, _ | .sts _, _ | .kint, _ => StValue.Equiv.refl _
  | .path _, _ | .spath _ _, _ => rfl
  | .ident _, _ | .addr _, _ | .mem, _ | .mv _, _ => trivial

theorem Srt.sameO_sv {H₀ H₁ : HTy} {T : Ty} {x : Option ((Srt.sv T).Den C H₀)}
    {y : Option ((Srt.sv T).Den C H₁)} : Srt.SameO (.sv T) x y ↔ x = y :=
  ⟨fun h => by
    cases x <;> cases y <;>
      first | rfl | exact Option.noConfusion h | exact congrArg some (Option.some.inj h),
   fun h => by rw [h]; rfl⟩

variable {g₀ g₁ : State C []}

/-- A constant that reads no storage denotes alike in two global parts with
one ledger, funds and transaction. -/
theorem Op0.denote_congrP {s : Srt} (o : Op0 C s) (hr : g₀.SameRest g₁)
    (hs : g₁.storage = g₀.storage ∨ o.stFree = true) :
    Srt.DEquiv s (o.denote g₀) (o.denote g₁) := by
  rcases g₀ with ⟨st₀, H₀, hp₀, ⟨⟩, n₀, b₀, t₀⟩
  rcases g₁ with ⟨st₁, H₁, hp₁, ⟨⟩, n₁, b₁, t₁⟩
  obtain ⟨hn, hb, ht⟩ := hr
  dsimp only at hn hb ht
  subst hn hb ht
  cases o with
  | storage =>
    rcases hs with hs | hs
    · dsimp only at hs; subst hs; exact Srt.DEquiv.refl _ _
    · exact absurd hs Bool.false_ne_true
  | _ => exact Srt.DEquiv.refl _ _

/-- A unary symbol respects `Equiv` of its argument's denotation, in two
global parts with one ledger, funds and transaction. -/
theorem Op1.denote_congrP {a s : Srt} (o : Op1 C a s) (hr : g₀.SameRest g₁)
    (hs : g₁.storage = g₀.storage ∨ o.stFree = true) {d d' : a.TDen}
    (h : Srt.DEquiv a d d') : Srt.DEquiv s (o.denote g₀ d) (o.denote g₁ d') := by
  rcases g₀ with ⟨st₀, H₀, hp₀, ⟨⟩, n₀, b₀, t₀⟩
  rcases g₁ with ⟨st₁, H₁, hp₁, ⟨⟩, n₁, b₁, t₁⟩
  obtain ⟨hn, hb, ht⟩ := hr
  dsimp only at hn hb ht
  subst hn hb ht
  cases o with
  | unop op ho =>
    simp only [Srt.DEquiv, Op1.denote] at h ⊢
    rw [h.toRes]
    exact StValue.Equiv.refl _
  | net =>
    simp only [Srt.DEquiv] at h ⊢
    rcases h.eq_or_st with h | ⟨s, t, hs, ht⟩
    · rw [h]; exact StValue.Equiv.refl _
    · simp only [Op1.denote, hs, ht]; exact StValue.Equiv.refl _
  | delValue =>
    simp only [Srt.DEquiv, Op1.denote] at h ⊢
    exact StValue.Equiv.delValue h
  | field hf | fieldIn hf =>
    simp only [Srt.DEquiv, Op1.denote] at h ⊢; rw [h]
  | next =>
    rcases hs with hs | hs
    · dsimp only at hs; subst hs
      simp only [Srt.DEquiv, Op1.denote] at h ⊢; rw [h]
    · exact absurd hs Bool.false_ne_true
  | sval => exact h
  | newArr hR =>
    simp only [Srt.DEquiv, Op1.denote] at h ⊢
    rw [h.asInt]
    exact StValue.Equiv.refl _
  | select r hr' | selectIn hr' =>
    simp only [Srt.DEquiv, Op1.denote] at h ⊢
    exact StValue.Equiv.asStruct (StValue.Equiv.select h _)
  | alloc _ _ | mfield _ | addM _ _ | mval | ref => trivial
  | wt => exact StValue.Equiv.refl _
  | toInt => simp only [Srt.DEquiv, Op1.denote] at h ⊢; exact h

/-- A binary symbol respects `Equiv` of its arguments' denotations, and a
memory read its arguments' readings, in two global parts with one ledger,
funds and transaction. -/
theorem Op2.denote_congrP {a b s : Srt} (o : Op2 C a b s) (hr : g₀.SameRest g₁)
    {x : Option (a.Den C g₀.H)} {x' : Option (a.Den C g₁.H)} {y : Option (b.Den C g₀.H)}
    {y' : Option (b.Den C g₁.H)} (hx : Srt.SameO a x x') (hy : Srt.SameO b y y')
    {da da' : a.TDen} {db db' : b.TDen} (ha : Srt.DEquiv a da da') (hb : Srt.DEquiv b db db') :
    Srt.DEquiv s (o.denote g₀ x y da db) (o.denote g₁ x' y' da' db') := by
  cases o with
  | binop op ho =>
    simp only [Srt.DEquiv, Op2.denote] at ha hb ⊢
    rw [ha.toRes, hb.toRes]
    exact StValue.Equiv.refl _
  | find | sfind | len | findIn | sfindIn =>
    simp only [Srt.DEquiv, Op2.denote] at ha hb ⊢
    rw [hb]
    exact StValue.Equiv.findSt ha _
  | read =>
    have he := Srt.sameO_val.1 (Op2.eval_sameP .read hr (.inr rfl) hx hy)
    simp only [Srt.DEquiv, Op2.denote]
    rw [he]
    exact StValue.Equiv.refl _
  | mlen =>
    have he := Srt.sameO_val.1 (Op2.eval_sameP .mlen hr (.inr rfl) hx hy)
    simp only [Srt.DEquiv, Op2.denote]
    rw [he]
    exact StValue.Equiv.refl _
  | copyMem =>
    have he := Srt.sameO_sv.1 (Op2.eval_sameP .copyMem hr (.inr rfl) hx hy)
    simp only [Srt.DEquiv, Op2.denote]
    revert he
    generalize Op2.eval g₀ .copyMem x y = u
    generalize Op2.eval g₁ .copyMem x' y' = v
    intro he
    subst he
    cases u <;> exact StValue.Equiv.refl _
  | «at» it =>
    simp only [Srt.DEquiv, Op2.denote] at ha hb ⊢
    rw [ha, hb.asInt]
  | nextIn =>
    simp only [Srt.DEquiv, Op2.denote] at ha hb ⊢
    rw [hb, Struct.Equiv.lenAt ha]
  | delAt | delAtIn =>
    simp only [Srt.DEquiv, Op2.denote] at ha hb ⊢
    rw [hb]
    exact Struct.Equiv.delAt ha _
  | pushSlot | extend =>
    simp only [Srt.DEquiv, Op2.denote] at ha hb ⊢
    rw [hb]
    exact Struct.Equiv.pushSlotT _ _ ha _
  | pop =>
    simp only [Srt.DEquiv, Op2.denote] at ha hb ⊢
    rw [hb]
    exact Struct.Equiv.popT ha _
  | shrink =>
    simp only [Srt.DEquiv, Op2.denote] at ha hb ⊢
    rw [hb]
    exact Struct.Equiv.shrinkT ha _
  | iread | copy _ | mat _ | copySt _ => trivial
  | zbin op ho | zcmp op ho =>
    simp only [Srt.DEquiv, Op2.denote] at ha hb ⊢
    rcases ha.eq_or_st with rfl | ⟨s, t, rfl, rfl⟩ <;>
      rcases hb.eq_or_st with rfl | ⟨s', t', rfl, rfl⟩ <;>
      first
      | exact StValue.Equiv.refl _
      | (split <;> (try split) <;> first | exact StValue.Equiv.refl _ | simp_all)

/-- A ternary symbol respects `Equiv` of its arguments' denotations. -/
theorem Op3.denote_congr {a b c s : Srt} (o : Op3 C a b c s) {da da' : a.TDen}
    {db db' : b.TDen} {dc dc' : c.TDen} (ha : Srt.DEquiv a da da') (hb : Srt.DEquiv b db db')
    (hc : Srt.DEquiv c dc dc') : Srt.DEquiv s (o.denote da db dc) (o.denote da' db' dc') := by
  cases o with
  | ite =>
    simp only [Srt.DEquiv, Op3.denote] at ha hb hc ⊢
    rcases ha.eq_or_st with h | ⟨s, t, hs, ht⟩
    · rw [h]
      split
      · exact hb
      · exact hc
      · exact StValue.Equiv.refl _
    · simp only [hs, ht]
      exact StValue.Equiv.refl _
  | atIn it =>
    simp only [Srt.DEquiv, Op3.denote] at hb hc ⊢
    rw [hb, hc.asInt]
  | save | saveIn =>
    simp only [Srt.DEquiv, Op3.denote] at ha hb hc ⊢
    rw [hb]
    exact Struct.Equiv.copyTo ha hc _
  | push =>
    simp only [Srt.DEquiv, Op3.denote] at ha hb hc ⊢
    rw [hb]
    exact Struct.Equiv.pushT ha (StValue.Equiv.stripVal hc) _
  | write => trivial

variable {Γ Δ : Ctx} {U : Upd C Γ Δ} {σ₀ : State C Γ} {σ₁ : State C Δ} {g : GlobT C σ₀.H}
  {stS : Option (Tm C Γ .st)} {memS : Option (Tm C Γ .mem)}

/-- **Read before the update, the substituted term denotes, up to `Equiv`,
what the term denotes in a typed state it lands on.** -/
theorem Tm.substP_denote (hL : U.Lands σ₀ g σ₁) (hr : σ₀.glob.SameRest σ₁.glob)
    (hst : StOK σ₀ σ₁ stS) (hmem : MemOK σ₀ σ₁ memS) :
    {k : Srt} → (t : Tm C Δ k) → {t' : Tm C Γ k} → Tm.substP U.held stS memS t = some t' →
      Srt.DEquiv k (t'.denote σ₀) (t.denote σ₁)
  | _, .pvV i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvV j) | .rhs (.val t) => some t) = some t' := h
    generalize U.held i = x at h hx
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      show StValue.Equiv (.prim (PrimTy.erase (TEnv.get j σ₀.env)))
        (.prim (PrimTy.erase (TEnv.get i σ₁.env)))
      rw [hx]
      exact StValue.Equiv.refl _
    | .rhs (.val t), hx, h =>
      cases h
      have hb := Tm.denote_eval σ₀ t' _ hx
      show StValue.Equiv _ (.prim (PrimTy.erase (TEnv.get i σ₁.env)))
      rw [hb]
      exact StValue.Equiv.refl _
  | _, .pvP i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvP j) | .rhs (.path p) => some p | .rhs .unset => none) =
          some t' := h
    generalize U.held i = x at h hx
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      show (Tm.pvP j).denote σ₀ = (Tm.pvP i).denote σ₁
      simp only [Tm.denote, hx]
      split <;> rfl
    | .rhs (.path p), hx, h =>
      cases h
      have hx : (t'.eval σ₀).bind (fun r => some (some r)) = some (TEnv.get i σ₁.env) := hx
      cases hp : t'.eval σ₀ with
      | none => rw [hp] at hx; cases hx
      | some q =>
        rw [hp] at hx
        have hq : TEnv.get i σ₁.env = some q := (Option.some.inj hx).symm
        show t'.denote σ₀ = (Tm.pvP i).denote σ₁
        simp only [Tm.denote, hq]
        exact Tm.denote_eval σ₀ t' q hp
  | _, .pvS i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvS j) | .rhs (.store x) => some x) = some t' := h
    generalize U.held i = x at h hx
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      show Struct.Equiv (Storage.absT (TEnv.get j σ₀.env : Storage C))
        (Storage.absT (TEnv.get i σ₁.env : Storage C))
      rw [hx]
      exact StValue.Equiv.refl _
    | .rhs (.store x), hx, h =>
      cases h
      have hx : (t'.eval σ₀).bind (fun st => some st) = some (TEnv.get i σ₁.env) := hx
      cases hp : t'.eval σ₀ with
      | none => rw [hp] at hx; cases hx
      | some q =>
        rw [hp] at hx
        have hq : q = TEnv.get i σ₁.env := Option.some.inj hx
        show Struct.Equiv (t'.denote σ₀) (Storage.absT (TEnv.get i σ₁.env : Storage C))
        rw [← hq]
        exact Tm.denote_eval σ₀ t' q hp
  | _, .pvI _, _, _ => trivial
  | _, .netOf i a, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => (Tm.substP U.held stS memS a).map (Tm.netOf j) | .rhs _ => none) =
          some t' := h
    generalize U.held i = x at h hx
    match x, hx, h with
    | .rhs _, _, h => cases h
    | .pos j, hx, h =>
      obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      have ih : StValue.Equiv (a'.denote σ₀) (a.denote σ₁) :=
        Tm.substP_denote hL hr hst hmem a ha
      show StValue.Equiv (Tm.denote σ₀ (.netOf j a')) (Tm.denote σ₁ (.netOf i a))
      rcases ih.eq_or_st with e | ⟨s, t, hs, ht⟩
      · simp only [Tm.denote, e, hx]; exact StValue.Equiv.refl _
      · simp only [Tm.denote, hs, ht]; exact StValue.Equiv.refl _
  | _, .app0 o, t', h => by
    cases h
    cases o with
    | storage =>
      cases stS with
      | some S => exact Tm.denote_eval σ₀ S σ₁.storage hst
      | none => exact Op0.denote_congrP .storage hr (.inl hst)
    | memory => trivial
    | lit v => exact Op0.denote_congrP (.lit v) hr (.inr rfl)
    | env k => exact Op0.denote_congrP (.env k) hr (.inr rfl)
    | root r hr' => exact Op0.denote_congrP (.root r hr') hr (.inr rfl)
    | mtSt => exact Op0.denote_congrP .mtSt hr (.inr rfl)
    | member s f hf => exact Op0.denote_congrP (.member s f hf) hr (.inr rfl)
    | zlit n => exact Op0.denote_congrP (.zlit n) hr (.inr rfl)
  | _, .app1 o x, t', h => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    have ihx := Tm.substP_denote hL hr hst hmem x hx
    by_cases hn : o.stFree = true
    · rw [Op1.substStep_of_stFree stS hn]
      exact Op1.denote_congrP o hr (.inr hn) ihx
    cases o with
    | next =>
      cases stS with
      | some S =>
        have hS : Struct.Equiv (S.denote σ₀) σ₁.storage.absT := Tm.denote_eval σ₀ S σ₁.storage hst
        have ihx : x'.denote σ₀ = x.denote σ₁ := ihx
        show Tm.denote σ₀ (Tm.app2 .nextIn S x') = Tm.denote σ₁ (Tm.app1 .next x)
        simp only [Tm.denote, Op2.denote, Op1.denote, ihx, Struct.Equiv.lenAt hS]
        rfl
      | none => exact Op1.denote_congrP .next hr (.inl hst) ihx
    | _ => exact absurd rfl hn
  | _, .app2 o x y, t', h => by
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    have ihx := Tm.substP_denote hL hr hst hmem x hx
    have ihy := Tm.substP_denote hL hr hst hmem y hy
    have evx := Tm.substP_eval hL hr hst hmem x hx
    have evy := Tm.substP_eval hL hr hst hmem y hy
    by_cases hn : o.stFree = true
    · rw [Op2.substStep_of_stFree stS hn]
      exact Op2.denote_congrP o hr evx evy ihx ihy
    cases o with
    | «at» it =>
      cases stS with
      | some S =>
        have ihx : x'.denote σ₀ = x.denote σ₁ := ihx
        have ihy : StValue.Equiv (y'.denote σ₀) (y.denote σ₁) := ihy
        show Tm.denote σ₀ (Tm.app3 (.atIn it) S x' y') = Tm.denote σ₁ (Tm.app2 (.at it) x y)
        simp only [Tm.denote, Op3.denote, Op2.denote, ihx, ihy.asInt]
      | none => exact Op2.denote_congrP (.at it) hr evx evy ihx ihy
    | _ => exact absurd rfl hn
  | _, .app3 o x y z, t', h => by
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z', hz, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact Op3.denote_congr o (Tm.substP_denote hL hr hst hmem x hx)
      (Tm.substP_denote hL hr hst hmem y hy) (Tm.substP_denote hL hr hst hmem z hz)
  | _, .pvZ i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvZ j) | .rhs (.zint t) => some t) = some t' := h
    generalize U.held i = x at h hx
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      show StValue.Equiv (.prim (.int (TEnv.get j σ₀.env))) (.prim (.int (TEnv.get i σ₁.env)))
      rw [hx]
      exact StValue.Equiv.refl _
    | .rhs (.zint t), hx, h =>
      cases h
      have hb := Tm.denote_eval σ₀ t' _ hx
      show StValue.Equiv _ (.prim (.int (TEnv.get i σ₁.env)))
      rw [hb]
      exact StValue.Equiv.refl _

/-- A first-order formula of `Δ` read in `Γ` before an update of locals and
the storage (`Tm.substP`); `none` past anything else. -/
def Fml.substSt (s : Subst C Γ Δ) (S : Tm C Γ .st) : Fml C Δ → Option (Fml C Γ)
  | .tt => some .tt
  | .eq a b => do pure (.eq (← Tm.substP s (some S) none a) (← Tm.substP s (some S) none b))
  | .defined t => (Tm.substP s (some S) none t).map .defined
  | .not φ => (Fml.substSt s S φ).map .not
  | .and φ ψ => do pure (.and (← Fml.substSt s S φ) (← Fml.substSt s S ψ))
  | .imp φ ψ => do pure (.imp (← Fml.substSt s S φ) (← Fml.substSt s S ψ))
  | _ => none

/-- **A first-order formula substituted holds before the update as the
formula holds in a typed state it lands on.** -/
theorem Fml.substSt_holds {S : Tm C Γ .st} (hL : U.Lands σ₀ g σ₁)
    (hr : σ₀.glob.SameRest σ₁.glob) (hst : StOK σ₀ σ₁ (some S))
    (hmem : MemOK σ₀ σ₁ (none : Option (Tm C Γ .mem))) :
    (φ : Fml C Δ) → {φ' : Fml C Γ} → Fml.substSt U.held S φ = some φ' →
      (holds σ₀ φ' ↔ holds σ₁ φ)
  | .tt, _, h => by cases h; exact Iff.rfl
  | .eq a b, _, h => by
    obtain ⟨a', ha, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    have ea : StValue.Equiv (a'.denote σ₀) (a.denote σ₁) := Tm.substP_denote hL hr hst hmem a ha
    have eb : StValue.Equiv (b'.denote σ₀) (b.denote σ₁) := Tm.substP_denote hL hr hst hmem b hb
    rw [holds_eq, holds_eq]
    exact ⟨fun e => (ea.symm.trans e).trans eb, fun e => (ea.trans e).trans eb.symm⟩
  | .defined t, _, h => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [holds_defined, holds_defined, Srt.sameO_val.1 (Tm.substP_eval hL hr hst hmem t ht)]
  | .not φ, _, h => by
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 h
    exact not_congr (Fml.substSt_holds hL hr hst hmem φ hφ)
  | .and φ ψ, _, h => by
    obtain ⟨φ', hφ, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ψ', hψ, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact and_congr (Fml.substSt_holds hL hr hst hmem φ hφ) (Fml.substSt_holds hL hr hst hmem ψ hψ)
  | .imp φ ψ, _, h => by
    obtain ⟨φ', hφ, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨ψ', hψ, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact imp_congr (Fml.substSt_holds hL hr hst hmem φ hφ) (Fml.substSt_holds hL hr hst hmem ψ hψ)
  | .upd .., _, h | .modal .., _, h | .havoc _, _, h | .all .., _, h | .bind .., _, h
  | .anon .., _, h => by cases h

/-- `[{storage := S}] φ ⇝ φ[S/storage]` on the update in front. -/
def Fml.applyStTop {Γ Δ : Ctx} (m : Modality) (U : Upd C Γ Δ) (φ : Fml C Δ) : Option (Fml C Γ) :=
  match m, U with
  | .box, .snoc .nil (.storage S) => Fml.substSt (Upd.snoc .nil (.storage S)).held S φ
  | _, _ => none

theorem Fml.applyStTop_sound {Γ Δ : Ctx} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ}
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
          have h : Fml.substSt (Upd.snoc .nil (.storage S)).held S φ = some ψ := h
          refine Upd.afterT_intro (fun _ => trivial) fun g σ₁ hL => ?_
          obtain ⟨hr, hm⟩ := Upd.stOnly_glob (Upd.snoc (C := C) .nil (.storage S)) rfl hL.1
          have hg : σ₁.glob = g.1 := hL.2.1
          have hr' : σ.glob.SameRest σ₁.glob := hg ▸ hr
          have hS : StOK σ σ₁ (some S) := by
            show S.eval σ = some σ₁.storage
            rw [Upd.lastSt_eval _ hL.1 S rfl, ← hg]
            rfl
          have hm' : MemOK σ σ₁ (none : Option (Tm C Γ .mem)) := by
            show Srt.forget .mem σ₁.glob.memT = _
            rw [hg]
            exact hm
          exact (Fml.substSt_holds hL hr' hS hm' φ h).1 hψ
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
theorem UpdElem.globT_thinG? (h : Thin Γ' Γ) (σ₀ : State C Γ) {Δ Δ' : Ctx} (G : GlobT C σ₀.H) :
    (e : UpdElem C Γ Δ) → {e' : UpdElem C Γ' Δ'} → e.thinG? h = some e' →
      e'.globT (σ₀.thin h) G = e.globT σ₀ G
  | .local .., _, he => by cases he
  | .storage s, _, he => by
    obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 he
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM, Tm.eval_thinS? h σ₀ s hs]
  | .memory m, _, he => by
    obtain ⟨m', hm, rfl⟩ := Option.map_eq_some_iff.1 he
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM, Tm.eval_thinS? h σ₀ m hm]
    rfl
  | .selfBalance op a, _, he => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 he
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM, Tm.eval_thinS? h σ₀ a ha]
    rfl
  | .net r op a, _, he => by
    obtain ⟨r', hr', he⟩ := Option.bind_eq_some_iff.1 he
    obtain ⟨a', ha, he⟩ := Option.bind_eq_some_iff.1 he
    cases he
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM, Tm.eval_thinS? h σ₀ r hr', Tm.eval_thinS? h σ₀ a ha]
  | .pay r a, _, he => by
    obtain ⟨r', hr', he⟩ := Option.bind_eq_some_iff.1 he
    obtain ⟨a', ha, he⟩ := Option.bind_eq_some_iff.1 he
    cases he
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM, Tm.eval_thinS? h σ₀ r hr', Tm.eval_thinS? h σ₀ a ha]
    rfl
  | .netMt r a, _, he => by
    obtain ⟨r', hr', he⟩ := Option.bind_eq_some_iff.1 he
    obtain ⟨a', ha, he⟩ := Option.bind_eq_some_iff.1 he
    cases he
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM, Tm.eval_thinS? h σ₀ r hr', Tm.eval_thinS? h σ₀ a ha]
  | .setBalance a, _, he => by
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.1 he
    rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
    simp only [UpdElem.globTM, Tm.eval_thinS? h σ₀ a ha]

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

theorem UpdElem.okB_thinG? (h : Thin Γ' Γ) (σ₀ : State C Γ) {Δ Δ' : Ctx} (e : UpdElem C Γ Δ)
    {e' : UpdElem C Γ' Δ'} (he : e.thinG? h = some e') : e'.okB (σ₀.thin h) = e.okB σ₀ := by
  rw [← UpdElem.globT_isSome _ e' σ₀.globG, ← UpdElem.globT_isSome σ₀ e σ₀.globG]
  exact congrArg Option.isSome (UpdElem.globT_thinG? h σ₀ σ₀.globG e he)

theorem UpdElem.exhB_thinG? (h : Thin Γ' Γ) (σ₀ : State C Γ) {Δ Δ' : Ctx} :
    (e : UpdElem C Γ Δ) → {e' : UpdElem C Γ' Δ'} → e.thinG? h = some e' →
      e'.exhB (σ₀.thin h) = e.exhB σ₀
  | .local .., _, he => by cases he
  | .storage x, _, he | .memory x, _, he | .selfBalance _ x, _, he | .setBalance x, _, he => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 he
    exact Tm.exhB_thinS? h σ₀ x hx
  | .net r _ a, _, he | .pay r a, _, he | .netMt r a, _, he => by
    obtain ⟨r', hr', he⟩ := Option.bind_eq_some_iff.1 he
    obtain ⟨a', ha, he⟩ := Option.bind_eq_some_iff.1 he
    cases he
    simp only [UpdElem.exhB, Tm.exhB_thinS? h σ₀ r hr', Tm.exhB_thinS? h σ₀ a ha,
      Tm.eval_thinS? h σ₀ r hr', Tm.eval_thinS? h σ₀ a ha]

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
theorem Upd.globT_thinIO (h : Thin Γ' Γ) (dd : Nat → Bool) (σ₀ : State C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → {n : Nat} → {R : UThin C Γ' Δ} →
      U.thinIO h dd = some (n, R) → R.U.globT (σ₀.thin h) = U.globT σ₀
  | _, .nil, _, _, hU => by cases hU; rfl
  | _, .snoc U e, n', R', hU => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    have ih := Upd.globT_thinIO h dd σ₀ U hR
    cases e with
    | «local» i r =>
      simp only at hU
      split at hU
      · rename_i j hj
        obtain ⟨r', hr', hU⟩ := Option.bind_eq_some_iff.1 hU
        cases hU
        show (R.U.globT (σ₀.thin h)).bind (UpdElem.globT (σ₀.thin h) (.local j r')) =
          (U.globT σ₀).bind (UpdElem.globT σ₀ (.local i r))
        rw [ih]
        congr 1
        funext G
        rw [UpdElem.globT_eq_globTM, UpdElem.globT_eq_globTM]
        simp only [UpdElem.globTM, Rhs.eval_thinS? h σ₀ r hr']
      · split at hU
        · rename_i ht
          cases hU
          obtain ⟨v, hv⟩ := Rhs.totalB_eval σ₀ r ht
          show _ = (U.globT σ₀).bind (UpdElem.globT σ₀ (.local i r))
          rw [ih]
          cases U.globT σ₀ with
          | none => rfl
          | some G =>
            rw [Option.bind_some, UpdElem.globT_eq_globTM]
            simp only [UpdElem.globTM, hv, Option.bind_some]
        · cases hU
    | _ =>
      obtain ⟨e', he, hU⟩ := Option.bind_eq_some_iff.1 hU
      cases hU
      show (R.U.globT (σ₀.thin h)).bind (e'.globT (σ₀.thin h)) = (U.globT σ₀).bind (UpdElem.globT σ₀ _)
      rw [ih]
      congr 1
      funext G
      exact UpdElem.globT_thinG? h σ₀ G _ he
  | _, .decl U y r, n', R', hU => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    have ih := Upd.globT_thinIO h dd σ₀ U hR
    simp only at hU
    split at hU
    · split at hU
      · rename_i ht
        cases hU
        obtain ⟨v, hv⟩ := Rhs.totalB_eval σ₀ r ht
        show _ = (U.globT σ₀).bind fun g => (r.eval σ₀).bind fun _ => some g
        rw [ih, hv]
        cases U.globT σ₀ <;> rfl
      · cases hU
    · obtain ⟨r', hr', hU⟩ := Option.bind_eq_some_iff.1 hU
      cases hU
      show ((R.U.globT (σ₀.thin h)).bind fun g => (r'.eval (σ₀.thin h)).bind fun _ => some g) =
        (U.globT σ₀).bind fun g => (r.eval σ₀).bind fun _ => some g
      rw [ih, Rhs.eval_thinS? h σ₀ r hr']
      rfl
  | _, .pop U e, n', R', hU => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    cases hU
    exact (Upd.popOrSkip_globT (σ₀.thin h) R.U _).trans (Upd.globT_thinIO h dd σ₀ U hR)
  | _, .drop U e, n', R', hU => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    cases hU
    exact (Upd.dropOrSkip_globT (σ₀.thin h) R.U _).trans (Upd.globT_thinIO h dd σ₀ U hR)

/-- **The thinned update leaves in each local it keeps what the update
leaves there.** -/
theorem Upd.held_thinIO (h : Thin Γ' Γ) (dd : Nat → Bool) (σ₀ : State C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → {n : Nat} → {R : UThin C Γ' Δ} →
      U.thinIO h dd = some (n, R) → ∀ {t : LTy} (k : Idx R.Δ' t) (v : t.VDen C),
        Held.OKV σ₀ v (U.held (k.wk R.th)) → Held.OKV (σ₀.thin h) v (R.U.held k)
  | _, .nil, _, _, hU, _, k, v, hv => by
    cases hU
    have hv : v = σ₀.getV (k.wk h) := hv
    show v = (σ₀.thin h).getV k
    rw [hv, State.getV_thin]
  | _, .snoc U e, n', R', hU, _, k, v, hv => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    have ih : ∀ {t : LTy} (k : Idx R.Δ' t) (v : t.VDen C),
        Held.OKV σ₀ v (U.held (k.wk R.th)) → Held.OKV (σ₀.thin h) v (R.U.held k) :=
      fun k v hv => Upd.held_thinIO h dd σ₀ U hR k v hv
    cases e with
    | «local» i r =>
      simp only at hU
      split at hU
      · rename_i j hj
        obtain ⟨r', hr', hU⟩ := Option.bind_eq_some_iff.1 hU
        cases hU
        show Held.OKV (σ₀.thin h) v (Subst.set (Upd.held R.U) j r' k)
        have hv : Held.OKV σ₀ v (Subst.set (Upd.held U) i r (k.wk R.th)) := hv
        have hi : j.wk R.th = i := Idx.unwk?_wk R.th i hj
        subst hi
        unfold Subst.set at hv ⊢
        by_cases hjk : j.toNat = k.toNat
        · obtain rfl := Idx.ty_eq_of_toNat hjk
          obtain rfl := Idx.toNat_inj j k hjk
          rw [dif_pos rfl] at hv ⊢
          show r'.eval (σ₀.thin h) = some v
          rw [Rhs.eval_thinS? h σ₀ r hr']
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
    have ih : ∀ {t : LTy} (k : Idx R.Δ' t) (v : t.VDen C),
        Held.OKV σ₀ v (U.held (k.wk R.th)) → Held.OKV (σ₀.thin h) v (R.U.held k) :=
      fun k v hv => Upd.held_thinIO h dd σ₀ U hR k v hv
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
        show r'.eval (σ₀.thin h) = some v
        rw [Rhs.eval_thinS? h σ₀ r hr']
        exact hv
      | there k => exact ih k v hv
  | _, .pop U e, n', R', hU, _, k, v, hv => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    cases hU
    rw [Upd.popOrSkip_held]
    refine Upd.held_thinIO h dd σ₀ U hR _ v ?_
    rw [Idx.wk_popExt]
    exact hv
  | _, .drop U e, n', R', hU, _, k, v, hv => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    cases hU
    rw [Upd.dropOrSkip_held]
    refine Upd.held_thinIO h dd σ₀ U hR _ v ?_
    rw [Idx.wk_meet]
    exact hv

/-- **Where the update lands, its thinning lands on the state with the
locals it drops left out.** -/
theorem Upd.lands_thinIO (h : Thin Γ' Γ) (dd : Nat → Bool) (σ₀ : State C Γ) {Δ : Ctx}
    {U : Upd C Γ Δ} {n : Nat} {R : UThin C Γ' Δ}
    (hU : U.thinIO h dd = some (n, R)) {g : GlobT C σ₀.H} {σ' : State C Δ}
    (hL : U.Lands σ₀ g σ') : R.U.Lands (σ₀.thin h) g (σ'.thin R.th) := by
  refine ⟨(Upd.globT_thinIO h dd σ₀ U hU).trans hL.1, hL.2.1, fun k => ?_⟩
  rw [Held.OK_iff_OKV, State.getV_thin]
  exact Upd.held_thinIO h dd σ₀ U hU k _ ((Held.OK_iff_OKV _ _ _ _).1 (hL.2.2 (k.wk R.th)))

/-- …and where its thinning drops nothing, the closed update lands where the
update does. -/
theorem Upd.lands_thinIO_close (h : Thin Γ' Γ) (dd : Nat → Bool) (σ₀ : State C Γ) {Δ : Ctx}
    {U : Upd C Γ Δ} {n : Nat}
    {R : UThin C Γ' Δ} (hU : U.thinIO h dd = some (n, R)) {U' : Upd C Γ' Δ}
    (hc : R.close? = some U') {g : GlobT C σ₀.H} {σ' : State C Δ}
    (hL : U.Lands σ₀ g σ') : U'.Lands (σ₀.thin h) g σ' := by
  obtain ⟨hcg, hch⟩ := Thin.closeU_spec hc (σ₀.thin h)
  refine ⟨hcg.trans ((Upd.globT_thinIO h dd σ₀ U hU).trans hL.1), hL.2.1, fun i => ?_⟩
  obtain ⟨j, hj, he⟩ := hch i
  rw [Idx.wk_norm] at hj
  subst hj
  rw [Held.OK_iff_OKV, he]
  exact Upd.held_thinIO h dd σ₀ U hU j _ ((Held.OK_iff_OKV _ _ _ _).1 (hL.2.2 (j.wk R.th)))

/-- …and the closed update computes the update's global part. -/
theorem Upd.globT_thinIO_close (h : Thin Γ' Γ) (dd : Nat → Bool) (σ₀ : State C Γ) {Δ : Ctx}
    {U : Upd C Γ Δ} {n : Nat}
    {R : UThin C Γ' Δ} (hU : U.thinIO h dd = some (n, R)) {U' : Upd C Γ' Δ}
    (hc : R.close? = some U') : U'.globT (σ₀.thin h) = U.globT σ₀ :=
  (Thin.closeU_spec hc (σ₀.thin h)).1.trans (Upd.globT_thinIO h dd σ₀ U hU)

theorem Upd.popOrSkip_exhAny {Δ' : Ctx} (σ : State C Γ') : {Δ : Ctx} → (U : Upd C Γ' Δ) →
    (h : Ext Δ' Δ) → (U.popOrSkip h).exhAny σ = U.exhAny σ ∧ (U.popOrSkip h).exhOk σ = U.exhOk σ
  | _, _, .refl => ⟨rfl, rfl⟩
  | _, _, .push _ => ⟨rfl, rfl⟩

theorem Upd.dropOrSkip_exhAny {Δ' : Ctx} (σ : State C Γ') : {Δ : Ctx} → (U : Upd C Γ' Δ) →
    (h : Thin Δ' Δ) → (U.dropOrSkip h).exhAny σ = U.exhAny σ ∧ (U.dropOrSkip h).exhOk σ = U.exhOk σ
  | _, _, .refl => ⟨rfl, rfl⟩
  | _, _, .keep _ | _, _, .drop _ => ⟨rfl, rfl⟩

/-- **The thinned update is out of gas where the update is**: what it
leaves out cannot halt. -/
theorem Upd.exh_thinIO (h : Thin Γ' Γ) (dd : Nat → Bool) (σ₀ : State C Γ) :
    {Δ : Ctx} → (U : Upd C Γ Δ) → {n : Nat} → {R : UThin C Γ' Δ} →
      U.thinIO h dd = some (n, R) →
        R.U.exhAny (σ₀.thin h) = U.exhAny σ₀ ∧ R.U.exhOk (σ₀.thin h) = U.exhOk σ₀
  | _, .nil, _, _, hU => by cases hU; exact ⟨rfl, rfl⟩
  | _, .snoc U e, n', R', hU => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    obtain ⟨ih₁, ih₂⟩ := Upd.exh_thinIO h dd σ₀ U hR
    cases e with
    | «local» i r =>
      simp only at hU
      split at hU
      · rename_i j hj
        obtain ⟨r', hr', hU⟩ := Option.bind_eq_some_iff.1 hU
        cases hU
        simp only [Upd.exhAny, Upd.exhOk, ih₁, ih₂, UpdElem.exhB, UpdElem.okB,
          Rhs.exhB_thinS? h σ₀ r hr', Rhs.eval_thinS? h σ₀ r hr', and_self]
      · split at hU
        · rename_i ht
          cases hU
          obtain ⟨v, hv⟩ := Rhs.totalB_eval σ₀ r ht
          simp only [Upd.exhAny, Upd.exhOk, ih₁, ih₂, UpdElem.exhB, UpdElem.okB,
            Rhs.exhB_of_eval σ₀ r hv, hv, Option.isSome_some, Bool.or_false, Bool.true_or,
            Bool.and_true, and_self]
        · cases hU
    | _ =>
      obtain ⟨e', he, hU⟩ := Option.bind_eq_some_iff.1 hU
      cases hU
      simp only [Upd.exhAny, Upd.exhOk, ih₁, ih₂, UpdElem.exhB_thinG? h σ₀ _ he,
        UpdElem.okB_thinG? h σ₀ _ he, and_self]
  | _, .decl U y r, n', R', hU => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    obtain ⟨ih₁, ih₂⟩ := Upd.exh_thinIO h dd σ₀ U hR
    simp only at hU
    split at hU
    · split at hU
      · rename_i ht
        cases hU
        obtain ⟨v, hv⟩ := Rhs.totalB_eval σ₀ r ht
        simp only [Upd.exhAny, Upd.exhOk, ih₁, ih₂, Rhs.exhB_of_eval σ₀ r hv, hv,
          Option.isSome_some, Bool.or_false, Bool.true_or, Bool.and_true, and_self]
      · cases hU
    · obtain ⟨r', hr', hU⟩ := Option.bind_eq_some_iff.1 hU
      cases hU
      simp only [Upd.exhAny, Upd.exhOk, ih₁, ih₂, Rhs.exhB_thinS? h σ₀ r hr',
        Rhs.eval_thinS? h σ₀ r hr', and_self]
  | _, .pop U e, n', R', hU => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    cases hU
    obtain ⟨ih₁, ih₂⟩ := Upd.exh_thinIO h dd σ₀ U hR
    obtain ⟨h₁, h₂⟩ := Upd.popOrSkip_exhAny (σ₀.thin h) R.U (Thin.popExt e R.th).2.2
    exact ⟨h₁.trans ih₁, h₂.trans ih₂⟩
  | _, .drop U e, n', R', hU => by
    obtain ⟨⟨n, R⟩, hR, hU⟩ := Option.bind_eq_some_iff.1 hU
    cases hU
    obtain ⟨ih₁, ih₂⟩ := Upd.exh_thinIO h dd σ₀ U hR
    obtain ⟨h₁, h₂⟩ := Upd.dropOrSkip_exhAny (σ₀.thin h) R.U (Thin.meet e R.th).2.2
    exact ⟨h₁.trans ih₁, h₂.trans ih₂⟩

theorem Upd.exh_thinIO' (h : Thin Γ' Γ) (dd : Nat → Bool) (σ₀ : State C Γ) {Δ : Ctx}
    {U : Upd C Γ Δ} {n : Nat} {R : UThin C Γ' Δ} (hU : U.thinIO h dd = some (n, R)) :
    R.U.exh (σ₀.thin h) = U.exh σ₀ := by
  obtain ⟨h₁, h₂⟩ := Upd.exh_thinIO h dd σ₀ U hU
  simp only [Upd.exh, h₁, h₂]

theorem Thin.closeU_exh {Δ' Δ : Ctx} {n : Thin Δ' Δ} {U : Upd C Γ' Δ'} {U' : Upd C Γ' Δ}
    (h : Thin.closeU n U = some U') (σ : State C Γ') : U'.exh σ = U.exh σ := by
  cases n with
  | refl => cases h; rfl
  | keep _ => cases h
  | drop _ => cases h

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
    rw [holds_eq, holds_eq, Tm.denote_thinS? h σ a ha, Tm.denote_thinS? h σ b hb]
  | _, _, h, .defined t, _, hφ, σ => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 hφ
    rw [holds_defined, holds_defined, Tm.eval_thinS? h σ t ht]
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
    simp only at hφ
    split at hφ
    · rename_i U' hc
      cases hφ
      refine Upd.afterT_introX (fun he => (hs.of_none ?_).imp_right fun hx => ?_) fun g σ' hL =>
        hs.of_lands (Upd.lands_thinIO_close h _ σ hR hc hL)
      · rw [Upd.globT_thinIO_close h _ σ hR hc, he]
      · rw [Thin.closeU_exh hc, Upd.exh_thinIO' h _ σ hR] at hx
        exact hx
    · obtain ⟨φ', h₁, hφ⟩ := Option.bind_eq_some_iff.1 hφ
      cases hφ
      refine Upd.afterT_introX (fun he => (hs.of_none ?_).imp_right fun hx => ?_) fun g σ' hL =>
        Fml.thinS?_holds R.th φ h₁ σ' (hs.of_lands (Upd.lands_thinIO h _ σ hR hL))
      · rw [Upd.globT_thinIO h _ σ U hR, he]
      · rw [Upd.exh_thinIO' h _ σ hR] at hx
        exact hx
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
  simp only at h
  split at h
  · rename_i U' hc
    cases h
    refine Upd.afterT_introX (fun he => (hφ.of_none ?_).imp_right fun hx => ?_) fun g σ' hL =>
      hφ.of_lands (Upd.lands_thinIO_close .refl drop σ hR hc hL)
    · exact (Upd.globT_thinIO_close .refl drop σ hR hc).trans he
    · rw [Thin.closeU_exh hc] at hx
      exact (Upd.exh_thinIO' .refl drop σ hR).symm.trans hx
  · obtain ⟨ψ', hψ, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    refine Upd.afterT_introX (fun he => (hφ.of_none ?_).imp_right fun hx => ?_) fun g σ' hL =>
      Fml.thinS?_holds R.th ψ hψ σ' (hφ.of_lands (Upd.lands_thinIO .refl drop σ hR hL))
    · exact (Upd.globT_thinIO .refl drop σ U hR).trans he
    · exact (Upd.exh_thinIO' .refl drop σ hR).symm.trans hx

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
      refine Upd.afterT_introX (fun he => (hφ.of_none ?_).imp_right fun hx => ?_) fun g σ' hL =>
        hφ.of_lands (g := g) ?_
      · exact (Upd.globT_thinIO (Thin.drop .refl) _ (σ.push w) U hU).trans he
      · exact (Upd.exh_thinIO' (Thin.drop .refl) _ (σ.push w) hU).symm.trans hx
      · exact Upd.lands_thinIO (Thin.drop .refl) _ (σ.push w) hU hL
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
