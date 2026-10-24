import Solidity.Calculus.SoundArms
import Solidity.Calculus.Graft
import Solidity.Calculus.CallSummary

/-!
# A call's summary is its run (`internalCallSummary`)

`Calculus/CallSummary.lean` runs a callee's body symbolically, in its own
frame, to the term its return variable holds.  Here that run is read on the
typed one (`Prog.runR`): a symbolic frame `E` over `Γ₀` *agrees* with a
typed frame `e` at a state `σ₀` of `Γ₀` when each value local's term reads,
in `σ₀`, what `e` holds (`SEnv.Ev`), and its *owed* terms return when every
pending local's term does (`SEnv.D`).  From a frame that agrees, a body
with a symbolic run either ends in a frame that agrees with the run's, the
global part unchanged, or reverts where an owed term does not return
(`Stmt.sym_sound`, `Prog.sym_sound`), and what is owed after is owed
before (`SymMono`).  So a callee's summary returns exactly where its run
does, with its return value (`CallRet.sumOf_sound`), and the call's
update fails exactly where the call reverts (`CallRet.summary_agrees`).
-/

namespace Solidity

open Solidity (Srt Op0 Op1 Op2 Op3)

variable {C : Contract}

/-! ## A symbolic frame against a typed one -/

section Frames

variable {Γ₀ : Ctx} (σ₀ : State C Γ₀)

/-- A local's term reads its value (a value local; any other is free). -/
def LTy.SEv {H : HTy} : (t : LTy) → LTy.STm C Γ₀ t → t.TDenote C H → Prop
  | .val _, x, v => x.1.eval σ₀ = some v
  | .alias _, _, _ => True
  | .mem _, _, _ => True
  | .old, _, _ => True
  | .oldNet, _, _ => True
  | .kint, _, _ => True

/-- **The symbolic frame agrees with the typed one at `σ₀`**: every value
local's term reads, in `σ₀`, the value the frame holds. -/
def SEnv.Ev {H : HTy} : (Δ : Ctx) → SEnv C Γ₀ Δ → TEnv C H Δ → Prop
  | [], _, _ => True
  | t :: Δ, x, v => LTy.SEv σ₀ t x.1 v.1 ∧ SEnv.Ev Δ x.2 v.2

/-- A pending local's term returns. -/
def LTy.SD : (t : LTy) → LTy.STm C Γ₀ t → Prop
  | .val _, x => x.2 = true → x.1.eval σ₀ ≠ none
  | .alias _, _ => True
  | .mem _, _ => True
  | .old, _ => True
  | .oldNet, _ => True
  | .kint, _ => True

/-- **What the frame owes returns** at `σ₀`: every pending local's term. -/
def SEnv.D : (Δ : Ctx) → SEnv C Γ₀ Δ → Prop
  | [], _ => True
  | t :: Δ, x => LTy.SD σ₀ t x.1 ∧ SEnv.D Δ x.2

variable {σ₀}

theorem SEnv.Ev.get {H : HTy} : {Δ : Ctx} → {E : SEnv C Γ₀ Δ} → {e : TEnv C H Δ} →
    SEnv.Ev σ₀ Δ E e → {p : PrimTy} → (i : Idx Δ (.val p)) →
    (E.get i).1.eval σ₀ = some (TEnv.get i e)
  | _ :: _, _, _, h, _, .here => h.1
  | _ :: _, _, _, h, _, .there i => SEnv.Ev.get h.2 i

theorem SEnv.Ev.set {H : HTy} : {Δ : Ctx} → {E : SEnv C Γ₀ Δ} → {e : TEnv C H Δ} →
    SEnv.Ev σ₀ Δ E e → {p : PrimTy} → (i : Idx Δ (.val p)) → {t : Tm C Γ₀ (.val p)} →
    {v : p.Denote} → t.eval σ₀ = some v → (b : Bool) →
    SEnv.Ev σ₀ Δ (E.set i (t, b)) (TEnv.set i v e)
  | _ :: _, _, _, h, _, .here, _, _, ht, _ => ⟨ht, h.2⟩
  | _ :: _, _, _, h, _, .there i, _, _, ht, b => ⟨h.1, SEnv.Ev.set h.2 i ht b⟩

theorem LTy.SEv_sclear {H : HTy} (c : Bool) : (t : LTy) → (x : LTy.STm C Γ₀ t) →
    (v : t.TDenote C H) → LTy.SEv σ₀ t (LTy.sclear c t x) v ↔ LTy.SEv σ₀ t x v
  | .val _, _, _ | .alias _, _, _ | .mem _, _, _ | .old, _, _ | .oldNet, _, _ | .kint, _, _ =>
    Iff.rfl

theorem SEnv.Ev_clear {H : HTy} (c : Nat → Bool) : (n : Nat) → (Δ : Ctx) → (E : SEnv C Γ₀ Δ) →
    (e : TEnv C H Δ) → SEnv.Ev σ₀ Δ (E.clear c n Δ) e ↔ SEnv.Ev σ₀ Δ E e
  | _, [], _, _ => Iff.rfl
  | n, t :: Δ, E, e => by
    show (LTy.SEv σ₀ t (LTy.sclear (c n) t E.1) e.1 ∧ SEnv.Ev σ₀ Δ (E.2.clear c (n + 1) Δ) e.2) ↔ _
    rw [LTy.SEv_sclear, SEnv.Ev_clear c (n + 1) Δ E.2 e.2]; rfl

theorem LTy.SEv_wk {H H' : HTy} (h : H <+: H') : (t : LTy) → (x : LTy.STm C Γ₀ t) →
    (v : t.TDenote C H) → LTy.SEv σ₀ t x v → LTy.SEv σ₀ t x (LTy.TDenote.wk h t v)
  | .val _, _, _, hv => hv
  | .alias _, _, _, _ | .mem _, _, _, _ | .old, _, _, _ | .oldNet, _, _, _ | .kint, _, _, _ =>
    trivial

theorem SEnv.Ev.wk {H H' : HTy} (h : H <+: H') : {Δ : Ctx} → {E : SEnv C Γ₀ Δ} →
    {e : TEnv C H Δ} → SEnv.Ev σ₀ Δ E e → SEnv.Ev σ₀ Δ E (TEnv.wk h Δ e)
  | [], _, _, _ => trivial
  | t :: _, _, _, he => ⟨LTy.SEv_wk h t _ _ he.1, SEnv.Ev.wk h he.2⟩

theorem SEnv.D.get : {Δ : Ctx} → {E : SEnv C Γ₀ Δ} → SEnv.D σ₀ Δ E → {p : PrimTy} →
    (i : Idx Δ (.val p)) → (E.get i).2 = true → (E.get i).1.eval σ₀ ≠ none
  | _ :: _, _, h, _, .here => h.1
  | _ :: _, _, h, _, .there i => SEnv.D.get h.2 i

theorem LTy.SD_of {t : LTy} {x : LTy.STm C Γ₀ t}
    (h : ∀ {p : PrimTy} (hp : t = .val p), (hp ▸ x : LTy.STm C Γ₀ (.val p)).2 = true →
      (hp ▸ x : LTy.STm C Γ₀ (.val p)).1.eval σ₀ ≠ none) : LTy.SD σ₀ t x := by
  cases t with
  | val p => exact h rfl
  | _ => trivial

/-- The frame owes nothing that does not return, read local by local. -/
theorem SEnv.D_of_get : {Δ : Ctx} → {E : SEnv C Γ₀ Δ} →
    (∀ {p : PrimTy} (i : Idx Δ (.val p)), (E.get i).2 = true → (E.get i).1.eval σ₀ ≠ none) →
    SEnv.D σ₀ Δ E
  | [], _, _ => trivial
  | t :: _, _, h => ⟨LTy.SD_of fun hp hx => by subst hp; exact h .here hx,
      SEnv.D_of_get fun i hx => h (.there i) hx⟩

theorem SEnv.get_set_same : {Δ : Ctx} → {p : PrimTy} → (i : Idx Δ (.val p)) →
    (w : LTy.STm C Γ₀ (.val p)) → (E : SEnv C Γ₀ Δ) → (E.set i w).get i = w
  | _ :: _, _, .here, _, _ => rfl
  | _ :: _, _, .there i, w, E => SEnv.get_set_same i w E.2

theorem SEnv.get_set_ne : {Δ : Ctx} → {t u : LTy} → (i : Idx Δ t) → (j : Idx Δ u) →
    (w : LTy.STm C Γ₀ t) → (E : SEnv C Γ₀ Δ) → i.toNat ≠ j.toNat → (E.set i w).get j = E.get j
  | _ :: _, _, _, .here, .here, _, _, h => absurd rfl h
  | _ :: _, _, _, .here, .there _, _, _, _ => rfl
  | _ :: _, _, _, .there _, .here, _, _, _ => rfl
  | _ :: _, _, _, .there i, .there j, w, E, h =>
    SEnv.get_set_ne i j w E.2 fun h' => h (congrArg (· + 1) h')

theorem SEnv.get_clear (c : Nat → Bool) : (n : Nat) → {Δ : Ctx} → {p : PrimTy} →
    (i : Idx Δ (.val p)) → (E : SEnv C Γ₀ Δ) →
    (E.clear c n Δ).get i = ((E.get i).1, (E.get i).2 && !c (n + i.toNat))
  | _, _ :: _, _, .here, _ => rfl
  | n, _ :: _, _, .there i, E => by
    show (E.2.clear c (n + 1) _).get i = _
    rw [SEnv.get_clear c (n + 1) i E.2]
    simp only [Idx.toNat, Nat.add_assoc, Nat.add_comm 1]
    rfl

end Frames

/-! ## Terms read through a frame -/

section Subst

variable {Γ₀ Δ : Ctx} {σ₀ : State C Γ₀}

/-- **A term read through a frame that agrees reads as in the frame's
state**, the global part being the same. -/
theorem Tm.eval_substE {E : SEnv C Γ₀ Δ} {τ : State C Δ} (hg : σ₀.glob = τ.glob)
    (hE : SEnv.Ev σ₀ Δ E τ.env) : {k : Srt} → (t : Tm C Δ k) → {t' : Tm C Γ₀ k} →
    t.substE E = some t' → Srt.SameO k (t'.eval σ₀) (t.eval τ)
  | _, .pvV i, t', h => by
    cases h
    rw [Srt.sameO_val]
    exact hE.get i
  | _, .pvP _, _, h | _, .pvS _, _, h | _, .pvI _, _, h | _, .netOf _ _, _, h
  | _, .pvZ _, _, h => nomatch h
  | _, .app0 o, t', h => by
    cases h
    exact Op0.eval_same o (.inl hg)
  | _, .app1 o x, t', h => by
    have h' : (x.substE E).map (Tm.app1 o) = some t' := h
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h'
    exact Op1.eval_same o (.inl hg) (Tm.eval_substE hg hE x hx)
  | _, .app2 o x y, t', h => by
    have h' : (x.substE E).bind (fun x' => (y.substE E).map fun y' => Tm.app2 o x' y') =
      some t' := h
    obtain ⟨x', hx, h''⟩ := Option.bind_eq_some_iff.1 h'
    obtain ⟨y', hy, rfl⟩ := Option.map_eq_some_iff.1 h''
    exact Op2.eval_same o (.inl hg) (Tm.eval_substE hg hE x hx) (Tm.eval_substE hg hE y hy)
  | _, .app3 o x y z, t', h => by
    have h' : (x.substE E).bind (fun x' => (y.substE E).bind fun y' =>
      (z.substE E).map fun z' => Tm.app3 o x' y' z') = some t' := h
    obtain ⟨x', hx, h''⟩ := Option.bind_eq_some_iff.1 h'
    obtain ⟨y', hy, h'''⟩ := Option.bind_eq_some_iff.1 h''
    obtain ⟨z', hz, rfl⟩ := Option.map_eq_some_iff.1 h'''
    exact Op3.eval_same o (.inl hg) (Tm.eval_substE hg hE x hx) (Tm.eval_substE hg hE y hy)
      (Tm.eval_substE hg hE z hz)

/-- At a value sort, the same reading. -/
theorem Tm.eval_substE_val {E : SEnv C Γ₀ Δ} {τ : State C Δ} (hg : σ₀.glob = τ.glob)
    (hE : SEnv.Ev σ₀ Δ E τ.env) {p : PrimTy} {t : Tm C Δ (.val p)} {t' : Tm C Γ₀ (.val p)}
    (h : t.substE E = some t') : t'.eval σ₀ = t.eval τ :=
  Srt.sameO_val.1 (Tm.eval_substE hg hE t h)

theorem Op1.eval_none (g : State C []) {a s : Srt} (o : Op1 C a s) : o.eval g none = none := by
  cases o <;> rfl

theorem BinOp.shortT_of_lazyB {op : BinOp} (h : op.lazyB = false) {p : PrimTy} (a : p.Denote) :
    op.shortT a = none := by
  cases op <;> first | (cases p <;> rfl) | (simp only [BinOp.lazyB, Bool.true_eq_false] at h)

theorem Op2.eval_none_of_strictB (g : State C []) {a b s : Srt} {o : Op2 C a b s}
    (ho : o.strictB = true) (x : Option (a.Den C g.H)) (y : Option (b.Den C g.H))
    (h : x = none ∨ y = none) : o.eval g x y = none := by
  cases o with
  | binop op hop =>
    have hl : op.lazyB = false := by simpa only [Op2.strictB, Bool.not_eq_true'] using ho
    show x.bind (fun a => binopT op hop a y) = none
    rcases h with rfl | rfl
    · rfl
    · cases x with
      | none => rfl
      | some a =>
        show binopT op hop a none = none
        unfold binopT
        rw [BinOp.shortT_of_lazyB hl]
        rfl
  | _ => exact absurd ho Bool.false_ne_true

/-- **A term that reads a local wherever it is read**: where the term, read
through a frame, returns, so does the local's term. -/
theorem Tm.strictReads_eval {E : SEnv C Γ₀ Δ} {q : PrimTy} (z : Idx Δ (.val q)) :
    {k : Srt} → (t : Tm C Δ k) → t.strictReads z.toNat = true → {t' : Tm C Γ₀ k} →
    t.substE E = some t' → t'.eval σ₀ ≠ none → (E.get z).1.eval σ₀ ≠ none
  | _, .pvV i, hr, t', h, hd => by
    have hn : i.toNat = z.toNat := by simpa only [Tm.strictReads, beq_iff_eq] using hr
    have hty := Idx.ty_eq_of_toNat hn
    cases hty
    cases Idx.toNat_inj i z hn
    cases h
    exact hd
  | _, .pvP _, hr, _, _, _ | _, .pvS _, hr, _, _, _ | _, .pvI _, hr, _, _, _
  | _, .netOf _ _, hr, _, _, _ | _, .pvZ _, hr, _, _, _ | _, .app0 _, hr, _, _, _
  | _, .app3 .., hr, _, _, _ => nomatch hr
  | _, .app1 o x, hr, t', h, hd => by
    have h' : (x.substE E).map (Tm.app1 o) = some t' := h
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h'
    refine Tm.strictReads_eval z x hr hx fun hn => hd ?_
    show o.eval σ₀.glob (x'.eval σ₀) = none
    rw [hn]; exact Op1.eval_none _ o
  | _, .app2 o x y, hr, t', h, hd => by
    have h' : (x.substE E).bind (fun x' => (y.substE E).map fun y' => Tm.app2 o x' y') =
      some t' := h
    obtain ⟨x', hx, h''⟩ := Option.bind_eq_some_iff.1 h'
    obtain ⟨y', hy, rfl⟩ := Option.map_eq_some_iff.1 h''
    have hr' : o.strictB = true ∧ (x.strictReads z.toNat = true ∨ y.strictReads z.toNat = true) := by
      simpa only [Tm.strictReads, Bool.and_eq_true, Bool.or_eq_true] using hr
    rcases hr'.2 with hxr | hyr
    · refine Tm.strictReads_eval z x hxr hx fun hn => hd ?_
      exact Op2.eval_none_of_strictB _ hr'.1 _ _ (.inl hn)
    · refine Tm.strictReads_eval z y hyr hy fun hn => hd ?_
      exact Op2.eval_none_of_strictB _ hr'.1 _ _ (.inr hn)

theorem Tm.alwaysB_eval {k : Srt} (σ : State C Γ₀) : (t : Tm C Γ₀ k) → t.alwaysB = true →
    t.eval σ ≠ none
  | .pvV _, _ => Option.some_ne_none _
  | .app0 o, h => by
    cases o <;> simp only [Tm.alwaysB, Op0.litB, Bool.false_eq_true] at h
    exact Option.some_ne_none _
  | .pvP _, h | .pvS _, h | .pvI _, h | .netOf _ _, h | .pvZ _, h | .app1 .., h | .app2 .., h
  | .app3 .., h => nomatch h

end Subst

/-! ## Offsets folded keep a term's reading -/

section Fold

variable {Γ : Ctx}

theorem Tm.litInt?_eval (σ : State C Γ) (w : Tm C Γ (.val .uint)) {c : Int} (h : w.litInt? = some c) :
    ∃ hc, w.eval σ = some ⟨c, hc⟩ := by
  cases w with
  | app0 o =>
    cases o with
    | lit v => cases h; exact ⟨v.2, rfl⟩
    | env k => exact nomatch h
  | _ => exact nomatch h

theorem Tm.addParts?_spec {p : PrimTy} (x : Tm C Γ (.val p)) {u : Tm C Γ (.val p)} {c : Int}
    (h : x.addParts? = some (u, c)) :
    ∃ (h' : BinOp.add.accepts p = true) (w : Tm C Γ (.val p)), w.litInt? = some c ∧
      x = .app2 (.binop .add h') u w := by
  cases x with
  | app2 o u' w =>
    cases o with
    | binop op h'' =>
      cases op with
      | add =>
        have h1 : w.litInt?.map (fun c => (u', c)) = some (u, c) := h
        obtain ⟨c', hc, he⟩ := Option.map_eq_some_iff.1 h1
        cases he
        exact ⟨h'', w, hc, rfl⟩
      | _ => exact nomatch h
    | _ => exact nomatch h
  | _ => exact nomatch h

theorem PrimTy.uint_ofInt?_add_assoc (a c₁ c₂ : Int) (ha : 0 ≤ a) (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂) :
    PrimTy.uint.ofInt? (a + (c₁ + c₂)) =
      (PrimTy.uint.ofInt? (a + c₁)).bind fun b => PrimTy.uint.ofInt? (b.1 + c₂) := by
  simp only [PrimTy.ofInt?]
  by_cases hx : PrimTy.uint.inRange (a + c₁) = true
  · rw [dif_pos hx, Option.bind_some]
    show _ = (if h : PrimTy.uint.inRange (a + c₁ + c₂) = true then _ else _)
    rw [Int.add_assoc]
  · rw [dif_neg hx, Option.bind_none, dif_neg]
    intro hy
    apply hx
    simp only [PrimTy.inRange, decide_eq_true_eq] at hy ⊢
    omega

theorem Op2.mk2_eval (σ : State C Γ) {a b s : Srt} (o : Op2 C a b s) (x : Tm C Γ a)
    (y : Tm C Γ b) : (o.mk2 x y).eval σ = (Tm.app2 o x y).eval σ := by
  cases o with
  | binop op h =>
    rename_i p
    cases op <;> cases p <;> try rfl
    simp only [Op2.mk2]
    cases hy : y.litInt? with
    | none => rfl
    | some c₂ =>
      cases hx : x.addParts? with
      | none => rfl
      | some q =>
        obtain ⟨u, c₁⟩ := q
        dsimp only
        split
        · rename_i hr
          obtain ⟨h', w, hw, rfl⟩ := Tm.addParts?_spec x hx
          obtain ⟨hc₁, hw'⟩ := Tm.litInt?_eval σ w hw
          obtain ⟨hc₂, hy'⟩ := Tm.litInt?_eval σ y hy
          show (u.eval σ).bind (fun a => binopT .add h a (some ⟨c₁ + c₂, hr⟩)) =
            (((u.eval σ).bind fun a => binopT .add h' a (w.eval σ))).bind
              (fun b => binopT .add h b (y.eval σ))
          rw [hy', hw']
          cases u.eval σ with
          | none => rfl
          | some a =>
            show PrimTy.uint.ofInt? (a.1 + (c₁ + c₂)) =
              (PrimTy.uint.ofInt? (a.1 + c₁)).bind fun b => PrimTy.uint.ofInt? (b.1 + c₂)
            have ha := a.2
            simp only [PrimTy.inRange, decide_eq_true_eq] at ha hc₁ hc₂
            exact PrimTy.uint_ofInt?_add_assoc a.1 c₁ c₂ ha.1 hc₁.1 hc₂.1
        · rfl
  | _ => rfl

/-- Folding offsets keeps a term's reading. -/
theorem Tm.eval_norm (σ : State C Γ) : {s : Srt} → (t : Tm C Γ s) → t.norm.eval σ = t.eval σ
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ | _, .app0 _ | _, .pvZ _ => rfl
  | _, .netOf i a => by
    show (a.norm.eval σ).bind _ = (a.eval σ).bind _
    rw [Tm.eval_norm σ a]
  | _, .app1 o x => by
    show o.eval σ.glob (x.norm.eval σ) = o.eval σ.glob (x.eval σ)
    rw [Tm.eval_norm σ x]
  | _, .app2 o x y => by
    show (o.mk2 x.norm y.norm).eval σ = o.eval σ.glob (x.eval σ) (y.eval σ)
    rw [Op2.mk2_eval]
    show o.eval σ.glob (x.norm.eval σ) (y.norm.eval σ) = _
    rw [Tm.eval_norm σ x, Tm.eval_norm σ y]
  | _, .app3 o x y z => by
    show o.eval σ.glob (x.norm.eval σ) (y.norm.eval σ) (z.norm.eval σ) = _
    rw [Tm.eval_norm σ x, Tm.eval_norm σ y, Tm.eval_norm σ z]; rfl

end Fold

/-! ## The frame's operations -/

section Ops

variable {Γ₀ : Ctx} {σ₀ : State C Γ₀}

theorem SEnv.Ev_idAt {H : HTy} : (Δ : Ctx) → (f : {t : LTy} → Idx Δ t → Idx Γ₀ t) →
    (e : TEnv C H Δ) →
    (∀ {p : PrimTy} (i : Idx Δ (.val p)), TEnv.get (f i) σ₀.env = TEnv.get i e) →
    SEnv.Ev σ₀ Δ (SEnv.idAt Δ f) e
  | [], _, _, _ => trivial
  | t :: Δ, f, e, hf => by
    refine ⟨?_, SEnv.Ev_idAt Δ (fun i => f (.there i)) e.2 fun i => hf (.there i)⟩
    cases t with
    | val p => exact congrArg some (hf .here)
    | _ => trivial

/-- Every local as itself agrees with the state's own locals. -/
theorem SEnv.Ev_id {Δ : Ctx} (τ : State C Δ) : SEnv.Ev τ Δ (SEnv.id Δ) τ.env :=
  SEnv.Ev_idAt Δ _ τ.env fun _ => rfl

theorem LTy.SD_of_spend {t : LTy} {x : LTy.STm C Γ₀ t} (h : LTy.spend t x = false) :
    LTy.SD σ₀ t x := by
  cases t with
  | val p => exact fun hx => absurd (h.symm.trans hx) Bool.false_ne_true
  | _ => trivial

theorem SEnv.D_of_clean : (Δ : Ctx) → (E : SEnv C Γ₀ Δ) → SEnv.clean Δ E = true → SEnv.D σ₀ Δ E
  | [], _, _ => trivial
  | t :: Δ, E, h => by
    have h' : (!LTy.spend t E.1 && SEnv.clean Δ E.2) = true := h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h'
    exact ⟨LTy.SD_of_spend h'.1, SEnv.D_of_clean Δ E.2 h'.2⟩

theorem SEnv.dropChk_ev {H : HTy} {Δ : Ctx} : {Δ' : Ctx} → (h : Ext Δ Δ') →
    {E : SEnv C Γ₀ Δ'} → {E' : SEnv C Γ₀ Δ} → SEnv.dropChk h E = some E' →
    {e : TEnv C H Δ'} → SEnv.Ev σ₀ Δ' E e → SEnv.Ev σ₀ Δ E' (TEnv.drop h e)
  | _, .refl, _, _, hd, _, he => by cases hd; exact he
  | _, .push h, E, _, hd, _, he => by
    have hd' : (if LTy.spend _ E.1 then none else SEnv.dropChk h E.2) = some _ := hd
    split at hd'
    · cases hd'
    · exact SEnv.dropChk_ev h hd' he.2

theorem SEnv.dropChk_D {Δ : Ctx} : {Δ' : Ctx} → (h : Ext Δ Δ') →
    {E : SEnv C Γ₀ Δ'} → {E' : SEnv C Γ₀ Δ} → SEnv.dropChk h E = some E' →
    SEnv.D σ₀ Δ E' → SEnv.D σ₀ Δ' E
  | _, .refl, _, _, hd, hD => by cases hd; exact hD
  | _, .push h, E, _, hd, hD => by
    have hd' : (if LTy.spend _ E.1 then none else SEnv.dropChk h E.2) = some _ := hd
    split at hd'
    · cases hd'
    · rename_i hs
      exact ⟨LTy.SD_of_spend (by simpa only [Bool.not_eq_true] using hs),
        SEnv.dropChk_D h hd' hD⟩

theorem SEnv.D_clear_get {Δ : Ctx} {E : SEnv C Γ₀ Δ} (c : Nat → Bool)
    (hD : SEnv.D σ₀ Δ (E.clear c 0 Δ)) {q : PrimTy} (z : Idx Δ (.val q))
    (hz : (E.get z).2 = true) (hc : c z.toNat = false) : (E.get z).1.eval σ₀ ≠ none := by
  have h := hD.get z
  rw [SEnv.get_clear c 0 z E, Nat.zero_add, hc, hz] at h
  exact h rfl

/-- **A local set** (`v = e;`): the new term agrees where it reads the
value set. -/
theorem SEnv.assign_ev {H : HTy} {Δ : Ctx} {p : PrimTy} {E E' : SEnv C Γ₀ Δ} {src : Nat → Bool}
    {i : Idx Δ (.val p)} {t : Tm C Γ₀ (.val p)} (h : E.assign src i t = some E')
    {e : TEnv C H Δ} (he : SEnv.Ev σ₀ Δ E e) {v : p.Denote} (ht : t.eval σ₀ = some v) :
    SEnv.Ev σ₀ Δ E' (TEnv.set i v e) := by
  unfold SEnv.assign at h
  split at h
  · cases h
  · cases h
    exact SEnv.Ev.set ((SEnv.Ev_clear src 0 Δ E e).2 he) i ht _

/-- A local set to a term that does not return owes it. -/
theorem SEnv.assign_notD {Δ : Ctx} {p : PrimTy} {E E' : SEnv C Γ₀ Δ} {src : Nat → Bool}
    {i : Idx Δ (.val p)} {t : Tm C Γ₀ (.val p)} (h : E.assign src i t = some E')
    (ht : t.eval σ₀ = none) : ¬ SEnv.D σ₀ Δ E' := by
  unfold SEnv.assign at h
  split at h
  · cases h
  · cases h
    intro hD
    have hd := hD.get i
    rw [SEnv.get_set_same] at hd
    have htot : t.alwaysB = false := by
      cases hb : t.alwaysB with
      | false => rfl
      | true => exact absurd ht (Tm.alwaysB_eval σ₀ t hb)
    exact hd (by rw [htot]; rfl) ht

/-- What a set owes, where its term returns, is what was owed. -/
theorem SEnv.assign_mono {Δ : Ctx} {p : PrimTy} {E E' : SEnv C Γ₀ Δ} {src : Nat → Bool}
    {i : Idx Δ (.val p)} {t : Tm C Γ₀ (.val p)} (h : E.assign src i t = some E')
    (hsrc : ∀ {q : PrimTy} (z : Idx Δ (.val q)), src z.toNat = true → t.eval σ₀ ≠ none →
      (E.get z).1.eval σ₀ ≠ none)
    (hD : SEnv.D σ₀ Δ E') : SEnv.D σ₀ Δ E := by
  unfold SEnv.assign at h
  split at h
  · cases h
  · rename_i hi
    cases h
    have htd : t.eval σ₀ ≠ none := by
      cases hb : t.alwaysB with
      | true => exact Tm.alwaysB_eval σ₀ t hb
      | false =>
        have hd := hD.get i
        rw [SEnv.get_set_same, hb] at hd
        exact hd rfl
    refine SEnv.D_of_get fun {q} z hz => ?_
    cases hc : src z.toNat with
    | true => exact hsrc z hc htd
    | false =>
      have hne : i.toNat ≠ z.toNat := by
        intro hn
        have hty := Idx.ty_eq_of_toNat hn
        cases hty
        cases Idx.toNat_inj i z hn
        rw [SEnv.get_clear src 0 i E, Nat.zero_add, hc, hz] at hi
        exact hi rfl
      have hd := hD.get z
      rw [SEnv.get_set_ne i z _ _ hne, SEnv.get_clear src 0 z E, Nat.zero_add, hc, hz] at hd
      exact hd rfl

end Ops

/-! ## Arguments -/

section Arguments

variable {Γ₀ Δ : Ctx} {σ₀ : State C Γ₀}

/-- The arguments read through a frame that agrees: they return, and agree. -/
theorem Args.sym_ev {E : SEnv C Γ₀ Δ} {τ : State C Δ} (hg : σ₀.glob = τ.glob)
    (hE : SEnv.Ev σ₀ Δ E τ.env) : {ps : Ctx} → (args : Args C Δ ps) → {θ : SEnv C Γ₀ ps} →
    Args.sym E args = some θ → ∃ a, Args.evalT τ args = .ok a ∧ SEnv.Ev σ₀ ps θ a
  | _, .nil, _, _ => ⟨(), rfl, trivial⟩
  | _, .snoc as p x e, θ, h => by
    cases e with
    | simple s =>
      have h' : (s.lower.substE E).bind (fun t => (Args.sym E as).map fun θ => ((t, false), θ)) =
        some θ := h
      obtain ⟨t, ht, h''⟩ := Option.bind_eq_some_iff.1 h'
      obtain ⟨θ', hθ', rfl⟩ := Option.map_eq_some_iff.1 h''
      obtain ⟨a, ha, hev⟩ := Args.sym_ev hg hE as hθ'
      refine ⟨(s.evalT τ, a), ?_, ?_, hev⟩
      · show (do let r ← Args.evalT τ as; let v ← (Val.simple s).evalT τ; pure (v, r)) = _
        rw [ha]; rfl
      · show t.eval σ₀ = some (s.evalT τ)
        rw [Tm.eval_substE_val hg hE ht, Simple.lower_evalT]
    | _ => exact nomatch h
  | _, .snocStorage .., _, h | _, .snocMemory .., _, h => nomatch h

/-- A local the call takes over through its arguments is the term the frame
gives a parameter the callee reads wherever it reads it. -/
theorem Args.takes_spec {E : SEnv C Γ₀ Δ} {q : PrimTy} (z : Idx Δ (.val q)) :
    {ps : Ctx} → (c : Nat → Bool) → (args : Args C Δ ps) → {θ : SEnv C Γ₀ ps} →
    Args.sym E args = some θ → Args.takes c args z.toNat = true →
    ∃ w : Idx ps (.val q), c w.toNat = true ∧ (θ.get w).1 = (E.get z).1
  | _, _, .nil, _, _, hk => nomatch hk
  | _, c, .snoc as p x e, θ, h, hk => by
    cases e with
    | simple s =>
      have h' : (s.lower.substE E).bind (fun t => (Args.sym E as).map fun θ => ((t, false), θ)) =
        some θ := h
      obtain ⟨t, ht, h''⟩ := Option.bind_eq_some_iff.1 h'
      obtain ⟨θ', hθ', rfl⟩ := Option.map_eq_some_iff.1 h''
      have hk' : ((match Val.simple s with
          | .simple (.local i) => c 0 && i.toNat == z.toNat
          | _ => false) || Args.takes (fun n => c (n + 1)) as z.toNat) = true := hk
      rcases Bool.or_eq_true _ _ ▸ hk' with h1 | h2
      · cases s with
        | «local» i =>
          have h1' : c 0 = true ∧ i.toNat = z.toNat := by
            simpa only [Bool.and_eq_true, beq_iff_eq] using h1
          have hty := Idx.ty_eq_of_toNat h1'.2
          cases hty
          cases Idx.toNat_inj i z h1'.2
          cases ht
          exact ⟨.here, h1'.1, rfl⟩
        | _ => exact nomatch h1
      · obtain ⟨w, hw, hθw⟩ := Args.takes_spec z (fun n => c (n + 1)) as hθ' h2
        exact ⟨w.there, hw, hθw⟩
    | _ => exact nomatch h
  | _, _, .snocStorage .., _, h, _ | _, _, .snocMemory .., _, h, _ => nomatch h

end Arguments

/-! ## The symbolic run against the typed one -/

section Runs

/-- **What a symbolic run from `E` to `E'` says of a typed run**: from a
state whose frame `E` agrees with at `σ₀` (the global part `σ₀`'s), the run
ends in a frame `E'` agrees with, the global part unchanged, or reverts where
`E'` owes a term that does not return. -/
def SymRuns {Δ Δ' : Ctx} (run : TStep C Δ Δ') (Γ₀ : Ctx) (E : SEnv C Γ₀ Δ)
    (E' : SEnv C Γ₀ Δ') : Prop :=
  ∀ (σ₀ : State C Γ₀) (τ : State C Δ), σ₀.glob = τ.glob → SEnv.Ev σ₀ Δ E τ.env →
    (∃ o, run τ = .ok o ∧ σ₀.glob = o.st.glob ∧ SEnv.Ev σ₀ Δ' E' o.st.env) ∨
    (run τ = .error .revert ∧ ¬ SEnv.D σ₀ Δ' E')

/-- What is owed after a symbolic run, where it returns, was owed before. -/
def SymMono {Δ Δ' : Ctx} (Γ₀ : Ctx) (E : SEnv C Γ₀ Δ) (E' : SEnv C Γ₀ Δ') : Prop :=
  ∀ σ₀ : State C Γ₀, SEnv.D σ₀ Δ' E' → SEnv.D σ₀ Δ E

/-- A symbolic run is sound for a typed one. -/
def SymSound {Δ Δ' : Ctx} (run : TStep C Δ Δ') (sym : SymM C Δ Δ') : Prop :=
  ∀ (Γ₀ : Ctx) (E : SEnv C Γ₀ Δ) (E' : SEnv C Γ₀ Δ'), sym Γ₀ E = some E' →
    SymRuns run Γ₀ E E' ∧ SymMono Γ₀ E E'

/-- **A callee's summary returns where its body does**, with the value its
return variable is left with. -/
theorem CallRet.sumOf_sound {ps Γf : Ctx} {p : PrimTy} {body : Prog C (.val p :: ps) Γf}
    (hS : SymSound body.runR body.sym) {R : Tm C (.val p :: ps) (.val p)}
    (h : CallRet.sumOf body.ext (body.sym _ (SEnv.id _)) = some R) (τc : State C (.val p :: ps)) :
    (∃ o, body.runR τc = .ok o ∧ τc.glob = o.st.glob ∧
      R.eval τc = some (TEnv.drop body.ext o.st.env).1) ∨
    (body.runR τc = .error .revert ∧ R.eval τc = Option.none) := by
  unfold CallRet.sumOf at h
  obtain ⟨Ed, hd, h'⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨Ec, hc, hd⟩ := Option.bind_eq_some_iff.1 hd
  split at h'
  · rename_i hcl
    cases h'
    rcases (hS _ _ _ hc).1 τc τc rfl (SEnv.Ev_id τc) with ⟨o, ho, hg, hev⟩ | ⟨hr, hnd⟩
    · exact .inl ⟨o, ho, hg, (SEnv.dropChk_ev body.ext hd hev).1⟩
    · refine .inr ⟨hr, ?_⟩
      have hnd' : ¬ SEnv.D τc (.val p :: ps) Ed := fun hD => hnd (SEnv.dropChk_D body.ext hd hD)
      exact Classical.byContradiction fun hne =>
        hnd' ⟨fun _ => hne, SEnv.D_of_clean ps Ed.2 hcl⟩
  · cases h'

/-- **A call with a summary runs as it**: the call returns where the
summary read at its arguments does, its target set to that value, and
reverts where it does not. -/
theorem CallRet.sym_call {Γ₀ Δ ps Γf : Ctx} {σ₀ : State C Γ₀} {p : PrimTy} {r : Var}
    {j : Idx Δ (.val p)} {args : Args C Δ ps} {body : Prog C (.val p :: ps) Γf}
    (hS : SymSound body.runR body.sym) {E : SEnv C Γ₀ Δ} {R : Tm C (.val p :: ps) (.val p)}
    {θ : SEnv C Γ₀ ps} {t : Tm C Γ₀ (.val p)}
    (hR : CallRet.sumOf body.ext (body.sym _ (SEnv.id _)) = some R) (hθ : Args.sym E args = some θ)
    (ht : Tm.substE (Δ := .val p :: ps) ((Tm.app0 (.lit (PrimTy.dflt p)), false), θ) R = some t)
    {τ : State C Δ} (hg : σ₀.glob = τ.glob) (hE : SEnv.Ev σ₀ Δ E τ.env) :
    (∃ v o, TRun.call args (.val p r (some j)) body.ext body.runR τ = .ok o ∧
      t.eval σ₀ = some v ∧ σ₀.glob = o.st.glob ∧
      o.st.env = TEnv.set j v (TEnv.wk o.ext Δ τ.env)) ∨
    (TRun.call args (.val p r (some j)) body.ext body.runR τ = .error .revert ∧
      t.eval σ₀ = Option.none) := by
  obtain ⟨a, ha, hθa⟩ := Args.sym_ev hg hE args hθ
  let τc : State C (.val p :: ps) := (τ.withEnv a).push (t := .val p) (PrimTy.dflt p)
  have hfr : SEnv.Ev σ₀ (.val p :: ps) ((Tm.app0 (.lit (PrimTy.dflt p)), false), θ) τc.env :=
    ⟨Tm.eval_lit σ₀ _, hθa⟩
  have htR : t.eval σ₀ = R.eval τc := Tm.eval_substE_val (τ := τc) hg hfr ht
  have hcall : TRun.call args (.val p r (some j)) body.ext body.runR τ =
      (body.runR τc).bind fun o => .ok ⟨o.st.withEnv (TEnv.set j (TEnv.drop body.ext o.st.env).1
        (TEnv.wk o.ext Δ τ.env)), o.ext⟩ := by
    simp only [TRun.call, ha]
    rfl
  rcases CallRet.sumOf_sound hS hR τc with ⟨o, ho, hgo, hRv⟩ | ⟨hr, hRn⟩
  · refine .inl ⟨_, _, by rw [hcall, ho]; rfl, htR.trans hRv, hg.trans (show τ.glob = o.st.glob from hgo), rfl⟩
  · exact .inr ⟨by rw [hcall, hr]; rfl, htR.trans hRn⟩

end Runs

/-! ## Every statement with a symbolic run -/

section Sound

variable {Γ₀ : Ctx}

/-- `v = e;`. -/
theorem Stmt.assignLocal_symSound {Δ : Ctx} {p : PrimTy} (i : Idx Δ (.val p)) (v : Val C Δ p) :
    SymSound (Stmt.assignLocal i v).runR (Stmt.assignLocal i v).sym := by
  intro Γ₀ E E' h
  have h' : (v.lower.substE E).bind (fun t => E.assign (fun n => v.lower.strictReads n) i t.norm) =
    some E' := h
  obtain ⟨t, ht, ha⟩ := Option.bind_eq_some_iff.1 h'
  refine ⟨fun σ₀ τ hg hE => ?_, fun σ₀ hD => ?_⟩
  · have htv : t.norm.eval σ₀ = v.lower.eval τ :=
      (Tm.eval_norm σ₀ t).trans (Tm.eval_substE_val hg hE ht)
    have hag := Val.lower_evalT τ v
    show (∃ o, TRun.assignLocal i v τ = .ok o ∧ _) ∨ (TRun.assignLocal i v τ = .error .revert ∧ _)
    unfold TRun.assignLocal
    cases hv : v.evalT τ with
    | ok w =>
      rw [hv] at hag
      have hw : t.norm.eval σ₀ = some w := htv.trans (hag : v.lower.eval τ = some w)
      exact .inl ⟨_, rfl, hg, SEnv.assign_ev ha hE hw⟩
    | error e =>
      have he : e = .revert := Val.evalT_revertOnly τ v e hv
      subst he
      rw [hv] at hag
      exact .inr ⟨rfl, SEnv.assign_notD ha (htv.trans (hag : v.lower.eval τ = none))⟩
  · exact SEnv.assign_mono ha (fun z hz hd =>
      Tm.strictReads_eval z v.lower hz ht (by rwa [Tm.eval_norm] at hd)) hD

theorem TRun.declLocal_some {Δ : Ctx} {p : PrimTy} (v : Val C Δ p) (τ : State C Δ) :
    TRun.declLocal p (some v) τ =
      (v.evalT τ).bind fun w => .ok ⟨τ.push (t := .val p) w, List.prefix_refl _⟩ := rfl

theorem TRun.seq_ok {Δ Δ₁ Δ₂ : Ctx} {s : TStep C Δ Δ₁} {P : TStep C Δ₁ Δ₂} {τ : State C Δ}
    {o : Out C τ.H Δ₁} (h : s τ = .ok o) :
    TRun.seq s P τ = (P o.st).map fun o' => ⟨o'.st, o.ext.trans o'.ext⟩ := by
  unfold TRun.seq; rw [h]

theorem TRun.seq_err {Δ Δ₁ Δ₂ : Ctx} {s : TStep C Δ Δ₁} {P : TStep C Δ₁ Δ₂} {τ : State C Δ}
    {e : THalt} (h : s τ = .error e) : TRun.seq s P τ = .error e := by
  unfold TRun.seq; rw [h]

/-- `T x;` and `T x = e;`. -/
theorem Stmt.declLocal_symSound {Δ : Ctx} (p : PrimTy) (x : Var) (init : Option (Val C Δ p)) :
    SymSound (Stmt.declLocal p x init).runR (Stmt.declLocal p x init).sym := by
  intro Γ₀ E E' h
  cases init with
  | none =>
    cases h
    exact ⟨fun σ₀ τ hg hE => .inl ⟨_, rfl, hg, Tm.eval_lit σ₀ _, hE⟩, fun _ hD => hD.2⟩
  | some v =>
    have h' : (v.lower.substE E).bind (fun t =>
        some ((t.norm, !t.norm.alwaysB), SEnv.clear (fun n => v.lower.strictReads n) 0 _ E)) =
        some E' := h
    obtain ⟨t, ht, ha⟩ := Option.bind_eq_some_iff.1 h'
    cases ha
    refine ⟨fun σ₀ τ hg hE => ?_, fun σ₀ hD => ?_⟩
    · have htv : t.norm.eval σ₀ = v.lower.eval τ :=
        (Tm.eval_norm σ₀ t).trans (Tm.eval_substE_val hg hE ht)
      have hag := Val.lower_evalT τ v
      show (∃ o, TRun.declLocal p (some v) τ = .ok o ∧ _) ∨
        (TRun.declLocal p (some v) τ = .error .revert ∧ _)
      rw [TRun.declLocal_some]
      cases hv : v.evalT τ with
      | ok w =>
        rw [hv] at hag
        exact .inl ⟨_, rfl, hg, htv.trans (hag : v.lower.eval τ = some w),
          (SEnv.Ev_clear _ 0 _ E τ.env).2 hE⟩
      | error e =>
        have he : e = .revert := Val.evalT_revertOnly τ v e hv
        subst he
        rw [hv] at hag
        refine .inr ⟨rfl, fun hD => ?_⟩
        have hn : t.norm.eval σ₀ = none := htv.trans (hag : v.lower.eval τ = none)
        have htot : t.norm.alwaysB = false := by
          cases hb : t.norm.alwaysB with
          | false => rfl
          | true => exact absurd hn (Tm.alwaysB_eval σ₀ t.norm hb)
        exact hD.1 (by rw [htot]; rfl) hn
    · have htd : t.norm.eval σ₀ ≠ none := by
        cases hb : t.norm.alwaysB with
        | true => exact Tm.alwaysB_eval σ₀ t.norm hb
        | false => exact hD.1 (by rw [hb]; rfl)
      rw [Tm.eval_norm] at htd
      refine SEnv.D_of_get fun {q} z hz => ?_
      cases hc : v.lower.strictReads z.toNat with
      | true => exact Tm.strictReads_eval z v.lower hc ht htd
      | false => exact SEnv.D_clear_get _ hD.2 z hz hc

/-- A block: its body, its locals popped. -/
theorem Stmt.block_symSound {Δ Δ₁ : Ctx} (body : Prog C Δ Δ₁)
    (hS : SymSound body.runR body.sym) :
    SymSound (Stmt.block body).runR (Stmt.block body).sym := by
  intro Γ₀ E E' h
  have h' : (body.sym Γ₀ E).bind (SEnv.dropChk body.ext) = some E' := h
  obtain ⟨E₁, h₁, hd⟩ := Option.bind_eq_some_iff.1 h'
  have ⟨hR, hM⟩ := hS Γ₀ E E₁ h₁
  refine ⟨fun σ₀ τ hg hE => ?_, fun σ₀ hD => hM σ₀ (SEnv.dropChk_D body.ext hd hD)⟩
  show (∃ o, TRun.block body.ext body.runR τ = .ok o ∧ _) ∨
    (TRun.block body.ext body.runR τ = .error .revert ∧ _)
  unfold TRun.block
  rcases hR σ₀ τ hg hE with ⟨o, ho, hgo, hev⟩ | ⟨hr, hnd⟩
  · rw [ho]
    exact .inl ⟨_, rfl, hgo, SEnv.dropChk_ev body.ext hd hev⟩
  · rw [hr]
    exact .inr ⟨rfl, fun hD => hnd (SEnv.dropChk_D body.ext hd hD)⟩

/-- A call of one value assigned to a value local. -/
theorem Stmt.call_symSound {Δ Δ' ps rs Γf : Ctx} (f : Name) (args : Args C Δ ps)
    (ret : CallRet Δ rs Δ') (body : Prog C (rs ++ ps) Γf) (hS : SymSound body.runR body.sym) :
    SymSound (Stmt.call f args ret body).runR (Stmt.call f args ret body).sym := by
  intro Γ₀ E E' h
  cases ret with
  | none => exact nomatch h
  | rets bs => exact nomatch h
  | mem R r hd hm => exact nomatch h
  | storage R r => exact nomatch h
  | val p r res =>
    cases res with
    | none => exact nomatch h
    | some j =>
      have h' : (CallRet.sumOf body.ext (body.sym _ (SEnv.id _))).bind (fun R =>
          (Args.sym E args).bind fun θ =>
            (Tm.substE (Δ := .val p :: ps) ((Tm.app0 (.lit (PrimTy.dflt p)), false), θ) R).bind
              fun t => E.assign (Args.takes (fun n => R.strictReads (n + 1)) args) j t.norm) =
          some E' := h
      obtain ⟨R, hR, h₁⟩ := Option.bind_eq_some_iff.1 h'
      obtain ⟨θ, hθ, h₂⟩ := Option.bind_eq_some_iff.1 h₁
      obtain ⟨t, ht, ha⟩ := Option.bind_eq_some_iff.1 h₂
      refine ⟨fun σ₀ τ hg hE => ?_, fun σ₀ hD => ?_⟩
      · show (∃ o, TRun.call args (.val p r (some j)) body.ext body.runR τ = .ok o ∧ _) ∨
          (TRun.call args (.val p r (some j)) body.ext body.runR τ = .error .revert ∧ _)
        rcases CallRet.sym_call hS hR hθ ht hg hE with ⟨v, o, ho, hv, hgo, henv⟩ | ⟨hr, hn⟩
        · refine .inl ⟨o, ho, hgo, ?_⟩
          rw [henv]
          exact SEnv.assign_ev ha (hE.wk o.ext) ((Tm.eval_norm σ₀ t).trans hv)
        · exact .inr ⟨hr, SEnv.assign_notD ha ((Tm.eval_norm σ₀ t).trans hn)⟩
      · refine SEnv.assign_mono ha (fun {q} z hz hd => ?_) hD
        obtain ⟨w, hw, hθw⟩ := Args.takes_spec z _ args hθ hz
        have := Tm.strictReads_eval (E := (show SEnv C Γ₀ (.val p :: ps) from
          ((Tm.app0 (.lit (PrimTy.dflt p)), false), θ))) w.there R hw ht
          (by rwa [Tm.eval_norm] at hd)
        rw [← hθw]
        exact this

mutual

/-- **Every statement's symbolic run is sound for its typed run.** -/
theorem Stmt.sym_sound : {Δ Δ' : Ctx} → (s : Stmt C Δ Δ') → SymSound s.runR s.sym
  | _, _, .assignLocal i v => Stmt.assignLocal_symSound i v
  | _, _, .declLocal p x init => Stmt.declLocal_symSound p x init
  | _, _, .block body => Stmt.block_symSound body (Prog.sym_sound body)
  | _, _, .call f args ret body => Stmt.call_symSound f args ret body (Prog.sym_sound body)
  | _, _, .assign .. | _, _, .rebind .. | _, _, .declStorage .. | _, _, .opAssign ..
  | _, _, .incDec .. | _, _, .assignIncDec .. | _, _, .pushOpAssign .. | _, _, .pushIncDec ..
  | _, _, .assignLocalPush .. | _, _, .push .. | _, _, .pop .. | _, _, .transfer ..
  | _, _, .send .. | _, _, .declMem .. | _, _, .rebindMem .. | _, _, .assignFromMem ..
  | _, _, .assignMem .. | _, _, .delete .. | _, _, .deleteMem .. | _, _, .assignNew ..
  | _, _, .ite .. | _, _, .require .. | _, _, .assert .. | _, _, .revert | _, _, .assumeFalse
  | _, _, .tryCall .. | _, _, .loop .. | _, _, .callReceiver .. | _, _, .callReceiverPush ..
  | _, _, .callRec .. | _, _, .revertData _ | _, _, .catchData .. => fun _ _ _ h => nomatch h

/-- **Every sequence's symbolic run is sound for its typed run.** -/
theorem Prog.sym_sound : {Δ Δ' : Ctx} → (P : Prog C Δ Δ') → SymSound P.runR P.sym
  | _, _, .nil => fun _ _ _ h => by
    cases h
    exact ⟨fun _ τ hg hE => .inl ⟨_, rfl, hg, hE⟩, fun _ hD => hD⟩
  | _, _, .cons s P => fun Γ₀ E E' h => by
    have h' : (s.sym Γ₀ E).bind (P.sym Γ₀) = some E' := h
    obtain ⟨E₁, h₁, h₂⟩ := Option.bind_eq_some_iff.1 h'
    have ⟨hR₁, hM₁⟩ := Stmt.sym_sound s Γ₀ E E₁ h₁
    have ⟨hR₂, hM₂⟩ := Prog.sym_sound P Γ₀ E₁ E' h₂
    refine ⟨fun σ₀ τ hg hE => ?_, fun σ₀ hD => hM₁ σ₀ (hM₂ σ₀ hD)⟩
    show (∃ o, TRun.seq s.runR P.runR τ = .ok o ∧ _) ∨ (TRun.seq s.runR P.runR τ = .error .revert ∧ _)
    rcases hR₁ σ₀ τ hg hE with ⟨o, ho, hgo, hev⟩ | ⟨hr, hnd⟩
    · rw [TRun.seq_ok ho]
      rcases hR₂ σ₀ o.st hgo hev with ⟨o', ho', hgo', hev'⟩ | ⟨hr', hnd'⟩
      · rw [ho']
        exact .inl ⟨_, rfl, hgo', hev'⟩
      · rw [hr']
        exact .inr ⟨rfl, hnd'⟩
    · rw [TRun.seq_err hr]
      exact .inr ⟨rfl, fun hD => hnd (hM₂ σ₀ hD)⟩

end

end Sound

/-! ## The call's update -/

section Update

variable {Γ₀ Δ : Ctx}

/-- Every value local's term pushes nothing. -/
def SEnv.PF (E : SEnv C Γ₀ Δ) : Prop :=
  ∀ {p : PrimTy} (i : Idx Δ (.val p)), (E.get i).1.pushFree = true

theorem SEnv.id_PF (Δ : Ctx) : SEnv.PF (SEnv.id (C := C) Δ) := fun i => by
  rw [SEnv.id, SEnv.get_idAt]; rfl

theorem Tm.substE_pushFree {E : SEnv C Γ₀ Δ} (hE : E.PF) : {s : Srt} → (t : Tm C Δ s) →
    t.valOnly = true → {t' : Tm C Γ₀ s} → t.substE E = some t' → t'.pushFree = true
  | _, .pvV i, _, _, h => by cases h; exact hE i
  | _, .app0 _, _, _, h => by cases h; rfl
  | _, .app1 o x, hv, t', h => by
    have h' : (x.substE E).map (Tm.app1 o) = some t' := h
    obtain ⟨x', hx, rfl⟩ := Option.map_eq_some_iff.1 h'
    exact Tm.substE_pushFree hE x hv hx
  | _, .app2 o x y, hv, t', h => by
    have hv' : (o.noPushB && x.valOnly && y.valOnly) = true := hv
    simp only [Bool.and_eq_true] at hv'
    have h' : (x.substE E).bind (fun x' => (y.substE E).map fun y' => Tm.app2 o x' y') =
      some t' := h
    obtain ⟨x', hx, h₁⟩ := Option.bind_eq_some_iff.1 h'
    obtain ⟨y', hy, rfl⟩ := Option.map_eq_some_iff.1 h₁
    have ho : o.pushFree = true := by
      have := hv'.1.1; cases o <;> first | rfl | exact absurd this Bool.false_ne_true
    simp only [Tm.pushFree, ho, Tm.substE_pushFree hE x hv'.1.2 hx,
      Tm.substE_pushFree hE y hv'.2 hy, Bool.and_self]
  | _, .app3 o x y z, hv, t', h => by
    have hv' : (o.noPushB && x.valOnly && y.valOnly && z.valOnly) = true := hv
    simp only [Bool.and_eq_true] at hv'
    have h' : (x.substE E).bind (fun x' => (y.substE E).bind fun y' =>
      (z.substE E).map fun z' => Tm.app3 o x' y' z') = some t' := h
    obtain ⟨x', hx, h₁⟩ := Option.bind_eq_some_iff.1 h'
    obtain ⟨y', hy, h₂⟩ := Option.bind_eq_some_iff.1 h₁
    obtain ⟨z', hz, rfl⟩ := Option.map_eq_some_iff.1 h₂
    have ho : o.pushFree = true := by
      have := hv'.1.1.1; cases o <;> first | rfl | exact absurd this Bool.false_ne_true
    simp only [Tm.pushFree, ho, Tm.substE_pushFree hE x hv'.1.1.2 hx,
      Tm.substE_pushFree hE y hv'.1.2 hy, Tm.substE_pushFree hE z hv'.2 hz, Bool.and_self]
  | _, .pvP _, hv, _, _ | _, .pvS _, hv, _, _ | _, .pvI _, hv, _, _ | _, .netOf _ _, hv, _, _
  | _, .pvZ _, hv, _, _ => nomatch hv

theorem Simple.lower_valOnly {Γ : Ctx} {p : PrimTy} (s : Simple C Γ p) : s.lower.valOnly = true := by
  cases s with
  | env k hp => subst hp; rfl
  | _ => rfl

theorem Args.sym_PF {E : SEnv C Γ₀ Δ} (hE : E.PF) : {ps : Ctx} → (args : Args C Δ ps) →
    {θ : SEnv C Γ₀ ps} → Args.sym E args = some θ → θ.PF
  | _, .nil, _, _ => fun i => nomatch i
  | _, .snoc as p x e, θ, h => by
    cases e with
    | simple s =>
      have h' : (s.lower.substE E).bind (fun t => (Args.sym E as).map fun θ => ((t, false), θ)) =
        some θ := h
      obtain ⟨t, ht, h₁⟩ := Option.bind_eq_some_iff.1 h'
      obtain ⟨θ', hθ', rfl⟩ := Option.map_eq_some_iff.1 h₁
      intro i
      cases i with
      | here => exact Tm.substE_pushFree hE s.lower (Simple.lower_valOnly s) ht
      | there i => exact Args.sym_PF hE as hθ' i
    | _ => exact nomatch h
  | _, .snocStorage .., _, h | _, .snocMemory .., _, h => nomatch h

theorem Rhs.eval_val_sum {Γ : Ctx} (σ : State C Γ) {p : PrimTy} (t : Tm C Γ (.val p)) :
    Rhs.eval σ (.val t) = t.eval σ := rfl

/-- **The summary's update agrees with the call's run**: it fails exactly
where the call reverts, and leaves its target the value the call does. -/
theorem CallRet.summary_agrees {ps Γf : Ctx} {p : PrimTy} {r : Var} {j : Idx Γ₀ (.val p)}
    {args : Args C Γ₀ ps} {body : Prog C ([.val p] ++ ps) Γf} {U : Upd C Γ₀ Γ₀}
    (h : CallRet.summary? args (.val p r (some j)) body = some U) (σ : State C Γ₀) :
    TRes.AgreesO (fun o : Out C σ.H Γ₀ => (o.st.glob, o.st.locV))
      (TRun.call args (.val p r (some j)) body.ext body.runR σ) (U.applyP σ) ∧
    (TRun.call args (.val p r (some j)) body.ext body.runR σ).NoDiv ∧ U.pushFree = true := by
  have h' : (if body.hasCall then
      (CallRet.sumOf body.ext (body.sym _ (SEnv.id _))).bind fun R =>
        if Tm.sumGate body R then
          (Args.sym (SEnv.id Γ₀) args).bind fun θ =>
            (Tm.substE (Γ₀ := Γ₀) (Δ := .val p :: ps)
              ((Tm.app0 (.lit (PrimTy.dflt p)), false), θ) R).map fun t =>
                Upd.nil.snoc (.local j (.val t))
        else Option.none
      else Option.none) = some U := h
  split at h'
  · obtain ⟨R, hR, h₁⟩ := Option.bind_eq_some_iff.1 h'
    split at h₁
    · rename_i hgate
      obtain ⟨θ, hθ, h₂⟩ := Option.bind_eq_some_iff.1 h₁
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h₂
      have hv : R.valOnly = true := by
        simp only [Tm.sumGate, Bool.and_eq_true] at hgate; exact hgate.1
      have hpf : t.pushFree = true := by
        refine Tm.substE_pushFree (E := (show SEnv C Γ₀ (.val p :: ps) from
          ((Tm.app0 (.lit (PrimTy.dflt p)), false), θ))) ?_ R hv ht
        intro _ i
        cases i with
        | here => rfl
        | there i => exact Args.sym_PF (SEnv.id_PF Γ₀) args hθ i
      have hU : (Upd.nil.snoc (UpdElem.local j (Rhs.val t))).pushFree = true := by
        simp only [Upd.pushFree, UpdElem.pushFree, Rhs.pushFree, hpf, Bool.and_self]
      refine ⟨?_, ?_, hU⟩ <;>
      rcases CallRet.sym_call (Prog.sym_sound body) hR hθ ht (τ := σ) rfl (SEnv.Ev_id σ) with
        ⟨v, o, ho, hvv, hgo, henv⟩ | ⟨hr, hn⟩
      · rw [ho, applyP_local1, Rhs.eval_val_sum, hvv]
        show some (σ.glob, σ.locV.set j v) = some (o.st.glob, o.st.locV)
        refine congrArg some (Prod.ext hgo ?_)
        funext u i
        show (σ.locV.set j v) u i = LTy.VDen.ofT u (TEnv.get i o.st.env)
        rw [henv]
        by_cases hji : j.toNat = i.toNat
        · obtain rfl := Idx.ty_eq_of_toNat hji
          obtain rfl := Idx.toNat_inj j i hji
          rw [LocsV.set_same, TEnv.get_set]; rfl
        · rw [LocsV.set_ne _ j i hji, TEnv.get_set_ne j i v _ hji, TEnv.get_wk,
            LTy.VDen.ofT_wk]
          rfl
      · rw [hr, applyP_local1, Rhs.eval_val_sum, hn]; rfl
      · rw [ho]; exact nofun
      · rw [hr]; exact nofun
    · cases h₁
  · cases h'

/-- **`internalCallSummary` is sound**: the call's summary is the update
of its run (`CallRet.summary_agrees`). -/
theorem Premise.sound_callSummary {m : Modality} {Γ ps Γf : Ctx} (f : Name) (args : Args C Γ ps)
    (p : PrimTy) (r : Var) (res : Option (Idx Γ (.val p))) (body : Prog C ([.val p] ++ ps) Γf)
    {U : Upd C Γ Γ} (h : CallRet.summary? args (.val p r res) body = some U) (σ : State C Γ) :
    Premise.Runs m (.call f args (.val p r res) body) (.update U) σ := by
  cases res with
  | none => exact nomatch h
  | some j =>
    obtain ⟨ha, hd, hpf⟩ := CallRet.summary_agrees h σ
    exact Premise.sound_update_typed σ ha (fun _ => hd) rfl (fun _ => Upd.exh_of_pushFree hpf)

end Update

end Solidity
