import Solidity.Calculus.RewritePast.Merge

/-!
# Rewrites past the program: storage writes and `simplifyUpdate`

A storage write applied to a first-order line, out of a thinning's scope,
and `simplifyUpdate` past the program.

A piece of `Calculus/RewritePast.lean`, whose docstring describes the whole.
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3 Modality)

variable {C : Contract}

/-! ## A storage write applied to a first-order line (`applyStorageBox`)

`[{storage := S}] φ ⇝ φ[S/storage]`, past the program, `φ` first-order.
The substitution is the storage merge's (`Tm.substP`,
`Calculus/StatePartsScoped.lean`: `storage` by `S`, a push slot and an index
check read in `S`), so a substituted term reads before the write as the term
reads where it lands (`Tm.substP_eval`).  An equation reads its terms
through `denote`, which the substitution keeps (`Tm.substP_denote`): a
symbol that reads no storage denotes alike in the two global parts
(`Op0.denote_congrP` … `Op2.denote_congrP`), and `S` denotes the storage it
leaves (`Tm.denote_eval`). -/

section WithSt

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
    (hs : g₁.storage = g₀.storage ∨ o.stFree = true) : o.denote g₀ = o.denote g₁ := by
  rcases g₀ with ⟨st₀, H₀, hp₀, ⟨⟩, n₀, b₀, t₀⟩
  rcases g₁ with ⟨st₁, H₁, hp₁, ⟨⟩, n₁, b₁, t₁⟩
  obtain ⟨hn, hb, ht⟩ := hr
  dsimp only at hn hb ht
  subst hn hb ht
  cases o with
  | storage =>
    rcases hs with hs | hs
    · dsimp only at hs; subst hs; rfl
    · exact absurd hs Bool.false_ne_true
  | _ => rfl

/-- A unary symbol denotes alike in two global parts with one ledger, funds
and transaction, where it reads no storage. -/
theorem Op1.denote_congrP {a s : Srt} (o : Op1 C a s) (hr : g₀.SameRest g₁)
    (hs : g₁.storage = g₀.storage ∨ o.stFree = true) (d : a.TDen C) :
    o.denote g₀ d = o.denote g₁ d := by
  rcases g₀ with ⟨st₀, H₀, hp₀, ⟨⟩, n₀, b₀, t₀⟩
  rcases g₁ with ⟨st₁, H₁, hp₁, ⟨⟩, n₁, b₁, t₁⟩
  obtain ⟨hn, hb, ht⟩ := hr
  dsimp only at hn hb ht
  subst hn hb ht
  cases o with
  | next =>
    rcases hs with hs | hs
    · dsimp only at hs; subst hs; rfl
    · exact absurd hs Bool.false_ne_true
  | _ => rfl

/-- A binary symbol denotes alike in two global parts with one ledger, funds
and transaction, a memory read its arguments' readings alike. -/
theorem Op2.denote_congrP {a b s : Srt} (o : Op2 C a b s) (hr : g₀.SameRest g₁)
    {x : Option (a.Den C g₀.H)} {x' : Option (a.Den C g₁.H)} {y : Option (b.Den C g₀.H)}
    {y' : Option (b.Den C g₁.H)} (hx : Srt.SameO a x x') (hy : Srt.SameO b y y')
    (da : a.TDen C) (db : b.TDen C) : o.denote g₀ x y da db = o.denote g₁ x' y' da db := by
  cases o with
  | read =>
    exact Srt.sameO_val.1 (Op2.eval_sameP .read hr (.inr rfl) hx hy)
  | mlen =>
    exact Srt.sameO_val.1 (Op2.eval_sameP .mlen hr (.inr rfl) hx hy)
  | hash k =>
    exact Srt.sameO_val.1 (Op2.eval_sameP (.hash k) hr (.inr rfl) hx hy)
  | copyMem =>
    have he := Srt.sameO_sv.1 (Op2.eval_sameP .copyMem hr (.inr rfl) hx hy)
    simp only [Op2.denote]
    revert he
    generalize Op2.eval g₀ .copyMem x y = u
    generalize Op2.eval g₁ .copyMem x' y' = v
    intro he
    subst he
    cases u <;> rfl
  | _ => rfl

variable {Γ Δ : Ctx} {U : Upd C Γ Δ} {σ₀ : State C Γ} {σ₁ : State C Δ} {g : GlobT C σ₀.H}
  {stS : Option (Tm C Γ .st)} {memS : Option (Tm C Γ .mem)}

/-- **Read before the update, the substituted term denotes what the term
denotes in a typed state it lands on.** -/
theorem Tm.substP_denote (hL : U.Lands σ₀ g σ₁) (hr : σ₀.glob.SameRest σ₁.glob)
    (hst : StOK σ₀ σ₁ stS) (hmem : MemOK σ₀ σ₁ memS) :
    {k : Srt} → (t : Tm C Δ k) → {t' : Tm C Γ k} → Tm.substP U.held stS memS t = some t' →
      t'.denote σ₀ = t.denote σ₁
  | _, .pvV i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvV j) | .rhs (.val t) => some t) = some t' := h
    generalize U.held i = x at h hx
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      show some _ = some _
      rw [hx]
    | .rhs (.val t), hx, h =>
      cases h
      exact Tm.denote_eval σ₀ t' _ hx
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
      show Storage.obs (TEnv.get j σ₀.env : Storage C) = Storage.obs (TEnv.get i σ₁.env : Storage C)
      rw [hx]
    | .rhs (.store x), hx, h =>
      cases h
      have hx : (t'.eval σ₀).bind (fun st => some st) = some (TEnv.get i σ₁.env) := hx
      cases hp : t'.eval σ₀ with
      | none => rw [hp] at hx; cases hx
      | some q =>
        rw [hp] at hx
        have hq : q = TEnv.get i σ₁.env := Option.some.inj hx
        show t'.denote σ₀ = Storage.obs (TEnv.get i σ₁.env : Storage C)
        rw [← hq]
        exact Tm.denote_eval σ₀ t' q hp
  | _, .pvI _, _, _ => rfl
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
      have ih : a'.denote σ₀ = a.denote σ₁ := Tm.substP_denote hL hr hst hmem a ha
      show Tm.denote σ₀ (.netOf j a') = Tm.denote σ₁ (.netOf i a)
      simp only [Tm.denote, ih, hx]
  | _, .app0 o, t', h => by
    cases h
    cases o with
    | storage =>
      cases stS with
      | some S => exact Tm.denote_eval σ₀ S σ₁.storage hst
      | none => exact Op0.denote_congrP .storage hr (.inl hst)
    | memory => rfl
    | lit v => exact Op0.denote_congrP (.lit v) hr (.inr rfl)
    | env k => exact Op0.denote_congrP (.env k) hr (.inr rfl)
    | root r hr' => exact Op0.denote_congrP (.root r hr') hr (.inr rfl)
    | mtSt => exact Op0.denote_congrP .mtSt hr (.inr rfl)
    | member s f hf => exact Op0.denote_congrP (.member s f hf) hr (.inr rfl)
    | zlit n => exact Op0.denote_congrP (.zlit n) hr (.inr rfl)
  | _, .app1 o x, t', h => by
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h
    have ihx : x'.denote σ₀ = x.denote σ₁ := Tm.substP_denote hL hr hst hmem x hx
    by_cases hn : o.stFree = true
    · rw [Op1.substStep_of_stFree stS hn]
      show o.denote σ₀.glob (x'.denote σ₀) = o.denote σ₁.glob (x.denote σ₁)
      rw [ihx]
      exact Op1.denote_congrP o hr (.inr hn) _
    cases o with
    | next =>
      cases stS with
      | some S =>
        have hS : S.denote σ₀ = σ₁.storage.obs := Tm.denote_eval σ₀ S σ₁.storage hst
        show Tm.denote σ₀ (Tm.app2 .nextIn S x') = Tm.denote σ₁ (Tm.app1 .next x)
        simp only [Tm.denote, Op2.denote, Op1.denote, ihx, hS]
        rfl
      | none =>
        show Op1.denote σ₀.glob .next (x'.denote σ₀) = Op1.denote σ₁.glob .next (x.denote σ₁)
        rw [ihx]
        exact Op1.denote_congrP .next hr (.inl hst) _
    | _ => exact absurd rfl hn
  | _, .app2 o x y, t', h => by
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    have ihx : x'.denote σ₀ = x.denote σ₁ := Tm.substP_denote hL hr hst hmem x hx
    have ihy : y'.denote σ₀ = y.denote σ₁ := Tm.substP_denote hL hr hst hmem y hy
    have evx := Tm.substP_eval hL hr hst hmem x hx
    have evy := Tm.substP_eval hL hr hst hmem y hy
    by_cases hn : o.stFree = true
    · rw [Op2.substStep_of_stFree stS hn]
      show o.denote σ₀.glob (x'.eval σ₀) (y'.eval σ₀) (x'.denote σ₀) (y'.denote σ₀) =
        o.denote σ₁.glob (x.eval σ₁) (y.eval σ₁) (x.denote σ₁) (y.denote σ₁)
      rw [ihx, ihy]
      exact Op2.denote_congrP o hr evx evy _ _
    cases o with
    | «at» it =>
      cases stS with
      | some S =>
        show Tm.denote σ₀ (Tm.app3 (.atIn it) S x' y') = Tm.denote σ₁ (Tm.app2 (.at it) x y)
        simp only [Tm.denote, Op3.denote, Op2.denote, ihx, ihy]
      | none =>
        show Op2.denote σ₀.glob (.at it) (x'.eval σ₀) (y'.eval σ₀) (x'.denote σ₀) (y'.denote σ₀) =
          Op2.denote σ₁.glob (.at it) (x.eval σ₁) (y.eval σ₁) (x.denote σ₁) (y.denote σ₁)
        rw [ihx, ihy]
        exact Op2.denote_congrP (.at it) hr evx evy _ _
    | _ => exact absurd rfl hn
  | _, .app3 o x y z, t', h => by
    obtain ⟨x', hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨y', hy, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨z', hz, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    show o.denote (x'.denote σ₀) (y'.denote σ₀) (z'.denote σ₀) =
      o.denote (x.denote σ₁) (y.denote σ₁) (z.denote σ₁)
    rw [Tm.substP_denote hL hr hst hmem x hx, Tm.substP_denote hL hr hst hmem y hy,
      Tm.substP_denote hL hr hst hmem z hz]
  | _, .pvZ i, t', h => by
    have hx := hL.2.2 i
    have h : (match U.held i with
        | .pos j => some (Tm.pvZ j) | .rhs (.zint t) => some t) = some t' := h
    generalize U.held i = x at h hx
    match x, hx, h with
    | .pos j, hx, h =>
      cases h
      have hx : TEnv.get i σ₁.env = TEnv.get j σ₀.env := hx
      show some _ = some _
      rw [hx]
    | .rhs (.zint t), hx, h =>
      cases h
      exact Tm.denote_eval σ₀ t' _ hx

/-- A first-order formula of `Δ` read in `Γ` before an update of locals and
the storage (`Tm.substP`); `none` past anything else. -/
def Fml.substSt (s : Subst C Γ Δ) (S : Tm C Γ .st) : Fml C Δ → Option (Fml C Γ)
  | .tt => some .tt
  | .eq a b => do pure (.eq (← Tm.substP s (some S) none a) (← Tm.substP s (some S) none b))
  | .wellFormed t => (Tm.substP s (some S) none t).map .wellFormed
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
    rw [holds_eq, holds_eq, Tm.substP_denote hL hr hst hmem a ha,
      Tm.substP_denote hL hr hst hmem b hb]
  | .wellFormed t, _, h => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [holds_wellFormed, holds_wellFormed, Srt.sameO_st.1 (Tm.substP_eval hL hr hst hmem t ht)]
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
  | .anon .., _, h | .allocAll .., _, h | .grow .., _, h => by cases h

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
  | _, _, h, .wellFormed t => (Tm.thinS? h t).map .wellFormed
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
  | _, _, h, .wellFormed t, _, hφ, σ => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 hφ
    rw [holds_wellFormed, holds_wellFormed, Tm.eval_thinS? h σ t ht]
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
  | _, _, _, .bind .., _, hφ, _ | _, _, _, .anon .., _, hφ, _
  | _, _, _, .allocAll .., _, hφ, _ | _, _, _, .grow .., _, hφ, _ => by cases hφ

/-- A formula of `Γ` read in `Γ'`: first-order where it is read both ways
(under `¬`, left of `→`), and through updates and binders elsewhere. -/
def Fml.thinS? : {Γ' Γ : Ctx} → Thin Γ' Γ → Fml C Γ → Option (Fml C Γ')
  | _, _, _, .tt => some .tt
  | _, _, h, .eq a b => do pure (.eq (← Tm.thinS? h a) (← Tm.thinS? h b))
  | _, _, h, .wellFormed t => (Tm.thinS? h t).map .wellFormed
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
  | _, _, h, .wellFormed t, _, hφ, σ, hs => by
    obtain ⟨t', ht, rfl⟩ := Option.map_eq_some_iff.1 hφ
    exact (Fml.thinFO?_holds h (.wellFormed t) (by simp only [Fml.thinFO?, ht]; rfl) σ).1 hs
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
  | _, _, _, .anon .., _, hφ, _, _ | _, _, _, .allocAll .., _, hφ, _, _ | _, _, _, .grow .., _, hφ, _, _ => by cases hφ

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
  | _, n, .tt, _, h | _, n, .eq .., _, h | _, n, .wellFormed _, _, h | _, n, .not _, _, h
  | _, n, .and .., _, h | _, n, .imp .., _, h | _, n, .modal .., _, h | _, n, .havoc _, _, h
  | _, n, .anon .., _, h | _, n, .allocAll .., _, h | _, n, .grow .., _, h => by
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
