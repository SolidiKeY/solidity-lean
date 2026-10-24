import Solidity.Calculus.RewriteScoped

/-!
# Rewrites past the program: scopes

Read with fewer locals, out of the top local's scope, and a hidden binder
absorbed.

A piece of `Calculus/RewritePast.lean`, whose docstring describes the whole.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)

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

end Solidity
