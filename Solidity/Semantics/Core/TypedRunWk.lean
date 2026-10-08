import Solidity.Semantics.Core.TypedRun
import Solidity.Calculus.Core.WkOver

/-!
# A weakened program runs as the program, typed

`Calculus/Core/RunWk.lean`'s `Prog.run_wk` for the typed run
(`docs/intrinsic.md`, W1 lane `runlemmas`): `Stmt.wk h` run from a state of
`Δ` does what the statement does from that state's locals of `Γ`
(`TState.thin h`), and leaves the other locals of `Δ` as they were:
`Stmt.trun_wk`, `Prog.trun_wk`.

The state of `Δ` is `τ.lift h d`: `τ`'s locals at the positions `h` keeps,
`d`'s at the others (`TEnv.put`).  A run grows the heap, so the locals it
does not touch come out weakened along the heap's extension (`TEnv.wk`): a
memory reference keeps its identity and only its proof moves, so the
relation of two outcomes (`TWkRel`) asks for what the dropped positions hold
weakened (`offWk`).  The syntax of a scope's end on both sides (`Thin.Over`,
`Prog.wk_over`) is `Calculus/Core/WkOver.lean`'s.

The loop lemmas the soundness of the loop rules reads are here too, on
`TLoop`: a loop every turn of which is lifted runs lifted (`TLoop.run_map`),
induction on its heads (`TLoop.run_induct`), and a loop with a variant ends
(`TLoop.run_variant`).
-/

namespace Solidity.Core

open Semantics (Value lookupBy)

variable {C : Contract}

/-! ## Values over a grown heap -/

namespace LTy

theorem TDenote.wk_trans {H₁ H₂ H₃ : HTy} (e₁ : H₁ <+: H₂) (e₂ : H₂ <+: H₃) :
    (t : LTy) → (v : t.TDenote C H₁) →
      TDenote.wk e₂ t (TDenote.wk e₁ t v) = TDenote.wk (e₁.trans e₂) t v
  | .val _, _ | .alias _, _ | .mem _, _ | .old, _ | .oldNet, _ => rfl

theorem TDenote.wk_self {H : HTy} (e : H <+: H) :
    (t : LTy) → (v : t.TDenote C H) → TDenote.wk e t v = v
  | .val _, _ | .alias _, _ | .mem _, _ | .old, _ | .oldNet, _ => rfl

/-- Over an equal heap typing, a weakened value is the value. -/
theorem TDenote.wk_heq {H H' : HTy} (e : H <+: H') (hH : H' = H) (t : LTy)
    (v : t.TDenote C H) : HEq (TDenote.wk e t v) v := by
  subst hH
  rw [TDenote.wk_self]

end LTy

/-- What the dropped positions hold, over a grown heap. -/
def offWk {H H' : HTy} (e : H <+: H') (o : List ((t : LTy) × t.TDenote C H)) :
    List ((t : LTy) × t.TDenote C H') :=
  o.map fun x => ⟨x.1, LTy.TDenote.wk e x.1 x.2⟩

theorem offWk_trans {H₁ H₂ H₃ : HTy} (e₁ : H₁ <+: H₂) (e₂ : H₂ <+: H₃)
    (o : List ((t : LTy) × t.TDenote C H₁)) :
    offWk e₂ (offWk e₁ o) = offWk (e₁.trans e₂) o := by
  simp only [offWk, List.map_map, Function.comp_def, LTy.TDenote.wk_trans]

theorem offWk_self {H : HTy} (e : H <+: H) (o : List ((t : LTy) × t.TDenote C H)) :
    offWk e o = o := by
  simp only [offWk, LTy.TDenote.wk_self, List.map_id']

/-! ## The locals a thinning drops -/

namespace TEnv

variable {H : HTy}

/-- `e` at the positions `h` keeps, `d` at the others. -/
def put : {Γ Δ : Ctx} → Thin Γ Δ → TEnv C H Γ → TEnv C H Δ → TEnv C H Δ
  | _, _, .refl, e, _ => e
  | _, _, .keep h, e, d => (e.1, TEnv.put h e.2 d.2)
  | _, _, .drop h, e, d => (d.1, TEnv.put h e d.2)

/-- What the positions `h` drops hold. -/
def off : {Γ Δ : Ctx} → Thin Γ Δ → TEnv C H Δ → List ((t : LTy) × t.TDenote C H)
  | _, _, .refl, _ => []
  | _, _, .keep h, d => TEnv.off h d.2
  | _, _, .drop h, d => ⟨_, d.1⟩ :: TEnv.off h d.2

/-- The locals a thinning keeps. -/
def thin : {Γ Δ : Ctx} → Thin Γ Δ → TEnv C H Δ → TEnv C H Γ
  | _, _, .refl, e => e
  | _, _, .keep h, e => (e.1, TEnv.thin h e.2)
  | _, _, .drop h, e => TEnv.thin h e.2

theorem get_put {t : LTy} : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (i : Idx Γ t) → (e : TEnv C H Γ) →
    (d : TEnv C H Δ) → TEnv.get (i.wk h) (TEnv.put h e d) = TEnv.get i e
  | _, _, .refl, _, _, _ => rfl
  | _, _, .keep _, .here, _, _ => rfl
  | _, _, .keep h, .there i, e, d => get_put h i e.2 d.2
  | _, _, .drop h, i, e, d => get_put h i e d.2

theorem set_put {t : LTy} : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (i : Idx Γ t) → (v : t.TDenote C H) →
    (e : TEnv C H Γ) → (d : TEnv C H Δ) →
    TEnv.set (i.wk h) v (TEnv.put h e d) = TEnv.put h (TEnv.set i v e) d
  | _, _, .refl, _, _, _, _ => rfl
  | _, _, .keep _, .here, _, _, _ => rfl
  | _, _, .keep h, .there i, v, e, d => by
    show (e.1, TEnv.set (i.wk h) v (TEnv.put h e.2 d.2)) = (e.1, TEnv.put h (TEnv.set i v e.2) d.2)
    rw [set_put h i v e.2 d.2]
  | _, _, .drop h, i, v, e, d => by
    show (d.1, TEnv.set (i.wk h) v (TEnv.put h e d.2)) = (d.1, TEnv.put h (TEnv.set i v e) d.2)
    rw [set_put h i v e d.2]

theorem thin_put : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (e : TEnv C H Γ) → (d : TEnv C H Δ) →
    TEnv.thin h (TEnv.put h e d) = e
  | _, _, .refl, _, _ => rfl
  | _, _, .keep h, e, d => by
    show (e.1, TEnv.thin h (TEnv.put h e.2 d.2)) = e
    rw [thin_put h e.2 d.2]
    rfl
  | _, _, .drop h, e, d => thin_put h e d.2

theorem off_put : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (e : TEnv C H Γ) → (d : TEnv C H Δ) →
    TEnv.off h (TEnv.put h e d) = TEnv.off h d
  | _, _, .refl, _, _ => rfl
  | _, _, .keep h, e, d => off_put h e.2 d.2
  | _, _, .drop h, e, d => by
    show ⟨_, d.1⟩ :: TEnv.off h (TEnv.put h e d.2) = ⟨_, d.1⟩ :: TEnv.off h d.2
    rw [off_put h e d.2]

theorem put_thin : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (d : TEnv C H Δ) →
    TEnv.put h (TEnv.thin h d) d = d
  | _, _, .refl, _ => rfl
  | _, _, .keep h, d => by
    show (d.1, TEnv.put h (TEnv.thin h d.2) d.2) = d
    rw [put_thin h d.2]
    rfl
  | _, _, .drop h, d => by
    show (d.1, TEnv.put h (TEnv.thin h d.2) d.2) = d
    rw [put_thin h d.2]
    rfl

/-- Only what `h` drops of the background matters. -/
theorem put_congr : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (e : TEnv C H Γ) → {d d' : TEnv C H Δ} →
    TEnv.off h d = TEnv.off h d' → TEnv.put h e d = TEnv.put h e d'
  | _, _, .refl, _, _, _, _ => rfl
  | _, _, .keep h, e, d, d', hd => by
    show (e.1, TEnv.put h e.2 d.2) = (e.1, TEnv.put h e.2 d'.2)
    rw [put_congr h e.2 hd]
  | _, _, .drop h, e, d, d', hd => by
    have h' : (⟨_, d.1⟩ : (t : LTy) × t.TDenote C H) = ⟨_, d'.1⟩ ∧
        TEnv.off h d.2 = TEnv.off h d'.2 := List.cons.inj hd
    have h1 : d.1 = d'.1 := eq_of_heq (Sigma.mk.inj h'.1).2
    show (d.1, TEnv.put h e d.2) = (d'.1, TEnv.put h e d'.2)
    rw [h1, put_congr h e h'.2]

theorem put_keepAll {Γ Δ : Ctx} (h : Thin Γ Δ) : (ρ : Ctx) → (r r' : TEnv C H ρ) →
    (e : TEnv C H Γ) → (d : TEnv C H Δ) →
    TEnv.put (Thin.keepAll ρ h) (TEnv.append ρ r e) (TEnv.append ρ r' d) =
      TEnv.append ρ r (TEnv.put h e d)
  | [], _, _, _, _ => rfl
  | _ :: ρ, r, r', e, d => by
    show (r.1, TEnv.put (Thin.keepAll ρ h) (TEnv.append ρ r.2 e) (TEnv.append ρ r'.2 d)) = _
    rw [put_keepAll h ρ r.2 r'.2 e d]
    rfl

theorem off_keepAll {Γ Δ : Ctx} (h : Thin Γ Δ) : (ρ : Ctx) → (r : TEnv C H ρ) →
    (d : TEnv C H Δ) → TEnv.off (Thin.keepAll ρ h) (TEnv.append ρ r d) = TEnv.off h d
  | [], _, _ => rfl
  | _ :: ρ, r, d => off_keepAll h ρ r.2 d

/-! ### Over a grown heap -/

theorem wk_trans {H₂ H₃ : HTy} (e₁ : H <+: H₂) (e₂ : H₂ <+: H₃) : (Γ : Ctx) → (x : TEnv C H Γ) →
    TEnv.wk e₂ Γ (TEnv.wk e₁ Γ x) = TEnv.wk (e₁.trans e₂) Γ x
  | [], _ => rfl
  | t :: Γ, x => by
    show (LTy.TDenote.wk e₂ t (LTy.TDenote.wk e₁ t x.1), TEnv.wk e₂ Γ (TEnv.wk e₁ Γ x.2)) = _
    rw [LTy.TDenote.wk_trans, wk_trans e₁ e₂ Γ x.2]
    rfl

theorem wk_self (e : H <+: H) : (Γ : Ctx) → (x : TEnv C H Γ) → TEnv.wk e Γ x = x
  | [], _ => rfl
  | t :: Γ, x => by
    show (LTy.TDenote.wk e t x.1, TEnv.wk e Γ x.2) = x
    rw [LTy.TDenote.wk_self, wk_self e Γ x.2]
    rfl

theorem get_wk {H' : HTy} (e : H <+: H') {t : LTy} : {Γ : Ctx} → (i : Idx Γ t) →
    (x : TEnv C H Γ) → TEnv.get i (TEnv.wk e Γ x) = LTy.TDenote.wk e t (TEnv.get i x)
  | _, .here, _ => rfl
  | _, .there i, x => get_wk e i x.2

theorem set_wk {H' : HTy} (e : H <+: H') {t : LTy} : {Γ : Ctx} → (i : Idx Γ t) →
    (v : t.TDenote C H) → (x : TEnv C H Γ) →
    TEnv.wk e Γ (TEnv.set i v x) = TEnv.set i (LTy.TDenote.wk e t v) (TEnv.wk e Γ x)
  | _, .here, _, _ => rfl
  | _ :: Γ, .there i, v, x => by
    show (_, TEnv.wk e Γ (TEnv.set i v x.2)) = (_, TEnv.set i _ (TEnv.wk e Γ x.2))
    rw [set_wk e i v x.2]
    rfl

theorem drop_wk {H' : HTy} (e : H <+: H') {Γ : Ctx} : {Δ : Ctx} → (h : Ext Γ Δ) →
    (x : TEnv C H Δ) → TEnv.drop h (TEnv.wk e Δ x) = TEnv.wk e Γ (TEnv.drop h x)
  | _, .refl, _ => rfl
  | _, .push h, x => drop_wk e h x.2

theorem append_wk {H' : HTy} (e : H <+: H') {Γ : Ctx} : (ρ : Ctx) → (r : TEnv C H ρ) →
    (x : TEnv C H Γ) →
    TEnv.wk e (ρ ++ Γ) (TEnv.append ρ r x) = TEnv.append ρ (TEnv.wk e ρ r) (TEnv.wk e Γ x)
  | [], _, _ => rfl
  | _ :: ρ, r, x => by
    show (_, TEnv.wk e (ρ ++ Γ) (TEnv.append ρ r.2 x)) = (_, TEnv.append ρ (TEnv.wk e ρ r.2) _)
    rw [append_wk e ρ r.2 x]
    rfl

theorem take_wk {H' : HTy} (e : H <+: H') {Γ : Ctx} : (ρ : Ctx) → (x : TEnv C H (ρ ++ Γ)) →
    TEnv.take ρ (TEnv.wk e (ρ ++ Γ) x) = TEnv.wk e ρ (TEnv.take ρ x)
  | [], _ => rfl
  | _ :: ρ, x => by
    show (_, TEnv.take ρ (TEnv.wk e (ρ ++ Γ) x.2)) = (_, TEnv.wk e ρ (TEnv.take ρ x.2))
    rw [take_wk e ρ x.2]
    rfl

theorem put_wk {H' : HTy} (e : H <+: H') : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (x : TEnv C H Γ) →
    (d : TEnv C H Δ) → TEnv.wk e Δ (TEnv.put h x d) = TEnv.put h (TEnv.wk e Γ x) (TEnv.wk e Δ d)
  | _, _, .refl, _, _ => rfl
  | _, _, .keep h, x, d => congrArg (Prod.mk _) (put_wk e h x.2 d.2)
  | _, _, .drop h, x, d => congrArg (Prod.mk _) (put_wk e h x d.2)

theorem off_wk {H' : HTy} (e : H <+: H') : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (d : TEnv C H Δ) →
    TEnv.off h (TEnv.wk e Δ d) = offWk e (TEnv.off h d)
  | _, _, .refl, _ => rfl
  | _, _, .keep h, d => off_wk e h d.2
  | _, _, .drop h, d => congrArg (List.cons _) (off_wk e h d.2)

theorem thin_wk {H' : HTy} (e : H <+: H') : {Γ Δ : Ctx} → (h : Thin Γ Δ) → (d : TEnv C H Δ) →
    TEnv.thin h (TEnv.wk e Δ d) = TEnv.wk e Γ (TEnv.thin h d)
  | _, _, .refl, _ => rfl
  | _, _, .keep h, d => congrArg (Prod.mk _) (thin_wk e h d.2)
  | _, _, .drop h, d => thin_wk e h d.2

theorem drop_append {Γ : Ctx} (ρ : Ctx) (r : TEnv C H ρ) (e : TEnv C H Γ) :
    TEnv.drop (Ext.append Γ ρ) (TEnv.append ρ r e) = e := by
  induction ρ with
  | nil => rfl
  | cons t ρ ih => exact ih r.2

end TEnv

/-! ## A state of `Δ` from one of `Γ` -/

namespace TState

variable {Γ Δ : Ctx}

/-- `τ`'s locals at the positions `h` keeps, `d`'s at the others. -/
def lift (h : Thin Γ Δ) (τ : TState C Γ) (d : TEnv C τ.H Δ) : TState C Δ :=
  τ.withEnv (TEnv.put h τ.env d)

theorem lift_storage (h : Thin Γ Δ) (τ : TState C Γ) (d : TEnv C τ.H Δ) :
    (τ.lift h d).storage = τ.storage := rfl

/-- The locals a thinning keeps. -/
def thin (h : Thin Γ Δ) (σ : TState C Δ) : TState C Γ := σ.withEnv (TEnv.thin h σ.env)

theorem lift_thin (h : Thin Γ Δ) (σ : TState C Δ) : (σ.thin h).lift h σ.env = σ := by
  cases σ
  simp only [lift, thin, withEnv, TEnv.put_thin]

theorem lift_setLocal (h : Thin Γ Δ) (τ : TState C Γ) (d : TEnv C τ.H Δ) {t : LTy}
    (i : Idx Γ t) (v : t.TDenote C τ.H) :
    (τ.lift h d).setLocal (i.wk h) v = (τ.setLocal i v).lift h d := by
  simp only [lift, setLocal, withEnv, TEnv.set_put]

theorem lift_pay (h : Thin Γ Δ) (τ : TState C Γ) (d : TEnv C τ.H Δ) (a m : Int) :
    (τ.lift h d).pay a m = (τ.pay a m).lift h d := rfl

theorem lift_withStorage (h : Thin Γ Δ) (τ : TState C Γ) (d : TEnv C τ.H Δ) (st : Storage C) :
    (τ.lift h d).withStorage st = (τ.withStorage st).lift h d := rfl

theorem lift_push (h : Thin Γ Δ) (τ : TState C Γ) (d : TEnv C τ.H Δ) {t : LTy}
    (v w : t.TDenote C τ.H) : (τ.lift h d).push v = (τ.push v).lift (.keep h) (w, d) := rfl

theorem get_lift (h : Thin Γ Δ) (τ : TState C Γ) (d : TEnv C τ.H Δ) {t : LTy} (i : Idx Γ t) :
    TEnv.get (i.wk h) (τ.lift h d).env = TEnv.get i τ.env :=
  TEnv.get_put h i τ.env d

theorem lift_congr (h : Thin Γ Δ) (τ : TState C Γ) {d d' : TEnv C τ.H Δ}
    (hd : TEnv.off h d = TEnv.off h d') : τ.lift h d = τ.lift h d' := by
  simp only [lift, TEnv.put_congr h τ.env hd]

/-- The lifted state grown: the background weakened along the growth. -/
theorem lift_grow {α : HTy → Type} (h : Thin Γ Δ) (τ : TState C Γ) (d : TEnv C τ.H Δ)
    (g : Grown τ.H α) :
    (τ.lift h d).grow g = ⟨(τ.grow g).st.lift h (TEnv.wk g.ext Δ d), g.ext, g.val⟩ := by
  simp only [grow, adopt, lift, withEnv]
  rw [TEnv.put_wk]

end TState

/-! ## Frames, run -/

/-- What the frames after a program do (`Frames.run`, typed): the rest run,
a scope's locals popped or thinned, the heap's growth carried. -/
def Frames.trun {Γ₀ : Ctx} : {Γ : Ctx} → (σ : TState C Γ) → Frames C Γ Γ₀ → TRes (Out C σ.H Γ₀)
  | _, σ, .nil => .ok ⟨σ, List.prefix_refl _⟩
  | _, σ, .seq ω κ => TRun.seq (fun τ => Prog.trun τ ω) (fun τ => Frames.trun τ κ) σ
  | _, σ, .pop _ h κ => Frames.trun (σ.drop h) κ
  | _, σ, .drop h κ => Frames.trun (σ.thin h) κ

/-! ## Outcomes, lifted -/

theorem TRes.map_bind {α β γ : Type} (f : β → γ) (x : TRes α) (g : α → TRes β) :
    (x >>= g).map f = x >>= fun a => (g a).map f := by
  cases x <;> rfl

theorem TRes.map_pure {α β : Type} (f : α → β) (a : α) :
    (pure a : TRes α).map f = pure (f a) := rfl

section Lifted

variable {Γ Δ : Ctx}

/-- An outcome's state lifted, the background weakened along its heap. -/
def Out.lift (h : Thin Γ Δ) {H : HTy} (d : TEnv C H Δ) (a : Out C H Γ) : Out C H Δ :=
  ⟨a.st.lift h (TEnv.wk a.ext Δ d), a.ext⟩

/-- An outcome, its state lifted. -/
abbrev liftedT (h : Thin Γ Δ) {H : HTy} (d : TEnv C H Δ) (r : TRes (Out C H Γ)) :
    TRes (Out C H Δ) :=
  r.map (Out.lift h d)

theorem liftedT_bind (h : Thin Γ Δ) {H : HTy} (d : TEnv C H Δ) {α : Type} (x : TRes α)
    (f : α → TRes (Out C H Γ)) : liftedT h d (x >>= f) = x >>= fun a => liftedT h d (f a) := by
  cases x <;> rfl

/-- An outcome with a value, its state lifted. -/
abbrev liftedT₂ {α : Type} (h : Thin Γ Δ) {H : HTy} (d : TEnv C H Δ)
    (r : TRes (Out C H Γ × α)) : TRes (Out C H Δ × α) :=
  r.map fun x => (Out.lift h d x.1, x.2)

theorem liftedT₂_bind {α β : Type} (h : Thin Γ Δ) {H : HTy} (d : TEnv C H Δ) (x : TRes β)
    (f : β → TRes (Out C H Γ × α)) :
    liftedT₂ h d (x >>= f) = x >>= fun a => liftedT₂ h d (f a) := by
  cases x <;> rfl

theorem liftedT_pure (h : Thin Γ Δ) {H : HTy} (d : TEnv C H Δ) (a : Out C H Γ) :
    liftedT h d (pure a) = pure (Out.lift h d a) := rfl

theorem liftedT₂_pure {α : Type} (h : Thin Γ Δ) {H : HTy} (d : TEnv C H Δ) (a : Out C H Γ × α) :
    liftedT₂ h d (pure a) = pure (Out.lift h d a.1, a.2) := rfl

theorem liftedT_ite (h : Thin Γ Δ) {H : HTy} (d : TEnv C H Δ) (c : Prop) [Decidable c]
    (x y : TRes (Out C H Γ)) :
    liftedT h d (if c then x else y) = if c then liftedT h d x else liftedT h d y := by
  split <;> rfl

theorem liftedT_error (h : Thin Γ Δ) {H : HTy} (d : TEnv C H Δ) (e : THalt) :
    liftedT h d (.error e : TRes (Out C H Γ)) = .error e := rfl

/-- A declaration's outcome, lifted: the declared local kept on top. -/
def Out.liftTop (h : Thin Γ Δ) {H : HTy} {t : LTy} (d : TEnv C H Δ) (a : Out C H (t :: Γ)) :
    Out C H (t :: Δ) :=
  ⟨a.st.lift (.keep h) (a.st.env.1, TEnv.wk a.ext Δ d), a.ext⟩

/-- What the lift lemmas leave: the states' modifiers unfolded, the
background over an unchanged heap unweakened. -/
macro "lift_fin" : tactic =>
  `(tactic| (simp only [liftedT_pure, liftedT₂_pure, Out.lift, Out.liftTop,
    TState.withStorage, TState.withHeap, TState.setLocal, TState.pay, TState.push,
    TEnv.wk_self]; try rfl))

/-- A state that kept the heap, lifted. -/
theorem Out.lift_refl (h : Thin Γ Δ) (τ : TState C Γ) (d : TEnv C τ.H Δ) :
    Out.lift h d ⟨τ, List.prefix_refl _⟩ = ⟨τ.lift h d, List.prefix_refl _⟩ := by
  simp only [Out.lift, TEnv.wk_self]

end Lifted

/-! ## Parts read in a weakened context -/

section Parts

variable {Γ Δ : Ctx} (h : Thin Γ Δ) (τ : TState C Γ) (d : TEnv C τ.H Δ)

theorem Simple.evalT_wk {p : PrimTy} (s : Simple C Γ p) :
    (s.wk h).evalT (τ.lift h d) = s.evalT τ := by
  cases s with
  | «local» i => exact TState.get_lift h τ d i
  | _ => rfl

mutual

theorem SPath.resolveT_wk : {T : Ty} → (b : SPath C Γ T) →
    (b.wk h).resolveT (τ.lift h d) = b.resolveT τ
  | _, .alias i => by
    simp only [SPath.wk, SPath.resolveT, TState.get_lift]
    split <;> rfl
  | _, .loc l => Loc.resolveT_wk l

theorem Loc.resolveT_wk : {T : Ty} → (l : Loc C Γ T) → (l.wk h).resolveT (τ.lift h d) = l.resolveT τ
  | _, .root .. => rfl
  | _, .field b f _ => by simp only [Loc.wk, Loc.resolveT, SPath.resolveT_wk b]
  | _, .index _ b i => by
    simp only [Loc.wk, Loc.resolveT, SPath.resolveT_wk b, Val.evalT_wk i]
    rfl

theorem MPath.mvalT_wk : {T : Ty} → (b : MPath C Γ T) → (b.wk h).mvalT (τ.lift h d) = b.mvalT τ
  | _, .var i _ => by simp only [MPath.wk, MPath.mvalT, TState.get_lift]
  | _, .loc l => by
    simp only [MPath.wk, MPath.mvalT, MLoc.addrT_wk l]
    rfl

theorem MLoc.addrT_wk : {T : Ty} → (l : MLoc C Γ T) → (l.wk h).addrT (τ.lift h d) = l.addrT τ
  | _, .field b f _ => by
    simp only [MLoc.wk, MLoc.addrT, MPath.mvalT_wk b]
    rfl
  | _, .index _ b i => by
    simp only [MLoc.wk, MLoc.addrT, MPath.mvalT_wk b, Val.evalT_wk i]
    rfl

theorem Val.evalT_wk : {p : PrimTy} → (v : Val C Γ p) → (v.wk h).evalT (τ.lift h d) = v.evalT τ
  | _, .simple s => by simp only [Val.wk, Val.evalT, Simple.evalT_wk]
  | _, .read l => by
    simp only [Val.wk, Val.evalT, Loc.resolveT_wk l]
    rfl
  | _, .binop .. => by simp only [Val.wk, Val.evalT, Val.evalT_wk]
  | _, .unop .. => by simp only [Val.wk, Val.evalT, Val.evalT_wk]
  | _, .ternary .. => by simp only [Val.wk, Val.evalT, Val.evalT_wk]
  | _, .readMem l => by
    simp only [Val.wk, Val.evalT, MLoc.addrT_wk l]
    rfl
  | _, .len b _ => by
    simp only [Val.wk, Val.evalT, SPath.resolveT_wk b]
    rfl
  | _, .mlen b _ => by
    simp only [Val.wk, Val.evalT, MPath.mvalT_wk b]
    rfl

end

theorem Src.valueT_wk {T : Ty} (r : Src C Γ T) : (r.wk h).valueT (τ.lift h d) = r.valueT τ := by
  cases r with
  | val v => simp only [Src.wk, Src.valueT, Val.evalT_wk]
  | copy p _ =>
    simp only [Src.wk, Src.valueT, SPath.resolveT_wk]
    rfl

theorem MSrc.mvalT_wk {T : Ty} (r : MSrc C Γ T) : (r.wk h).mvalT (τ.lift h d) = r.mvalT τ := by
  cases r with
  | val v => exact Val.evalT_wk h τ d v
  | ref p => exact MPath.mvalT_wk h τ d p

theorem ARhs.evalT_wk {R : RefTy} (r : ARhs C Γ R) : (r.wk h).evalT (τ.lift h d) = r.evalT τ := by
  cases r with
  | path p =>
    simp only [ARhs.wk, ARhs.evalT, SPath.resolveT_wk]
    rfl
  | push b _ =>
    simp only [ARhs.wk, ARhs.evalT, SPath.resolveT_wk]
    rfl

theorem ExtCall.keyT_wk (c : ExtCall C Γ) : (c.wk h).keyT (τ.lift h d) = c.keyT τ := by
  simp only [ExtCall.keyT, ExtCall.wk, Simple.evalT_wk, List.map_map,
    Function.comp_def]

theorem Args.evalT_wk : {ps : Ctx} → (as : Args C Γ ps) →
    (as.wk h).evalT (τ.lift h d) = as.evalT τ
  | _, .nil => rfl
  | _, .snoc as p x e => by
    show (do
        let r ← Args.evalT (τ.lift h d) (as.wk h)
        let v ← (e.wk h).evalT (τ.lift h d)
        pure (v, r)) = (do
        let r ← Args.evalT τ as
        let v ← e.evalT τ
        pure (v, r))
    rw [Args.evalT_wk as, Val.evalT_wk]
    rfl

end Parts

/-! ## Allocation, lifted -/

section Grow

variable {Γ Δ : Ctx}

/-- A grown state, lifted: the background weakened along the growth. -/
def Grew.lift (h : Thin Γ Δ) {H : HTy} {α : HTy → Type} (d : TEnv C H Δ) (g : Grew C Γ H α) :
    Grew C Δ H α :=
  ⟨g.st.lift h (TEnv.wk g.ext Δ d), g.ext, g.val⟩

variable (h : Thin Γ Δ) (τ : TState C Γ) (d : TEnv C τ.H Δ)

theorem TState.allocDefaultG_lift (R : RefTy) (hm : (Ty.ref R).mapFree = true) :
    (τ.lift h d).allocDefaultG R hm = Grew.lift h d (τ.allocDefaultG R hm) :=
  TState.lift_grow h τ d _

theorem TState.copyStToMG_lift {T : Ty} (v : SVal T) (hm : T.mapFree = true) :
    (τ.lift h d).copyStToMG v hm = Grew.lift h d (τ.copyStToMG v hm) :=
  TState.lift_grow h τ d _

theorem MRhs.evalT_wk {R : RefTy} (r : MRhs C Γ R) :
    (r.wk h).evalT (τ.lift h d) = (r.evalT τ).map (Grew.lift h d) := by
  cases r with
  | «alias» p =>
    simp only [MRhs.wk, MRhs.evalT, MPath.mvalT_wk]
    cases MPath.mvalT τ p with
    | error => rfl
    | ok x =>
      show Except.ok (⟨τ.lift h d, List.prefix_refl _, x⟩ : Grew C Δ τ.H (HRef · R)) =
        Except.ok (Grew.lift h d (⟨τ, List.prefix_refl _, x⟩ : Grew C Γ τ.H (HRef · R)))
      simp only [Grew.lift]
      rw [TEnv.wk_self]
  | copy p hm =>
    show (do
        let r ← (p.wk h).resolveT (τ.lift h d)
        let sv ← TRes.ofOpt (τ.storage.find r)
        pure ((τ.lift h d).copyStToMG sv hm)) = Except.map (Grew.lift h d) (do
        let r ← p.resolveT τ
        let sv ← TRes.ofOpt (τ.storage.find r)
        pure (τ.copyStToMG sv hm))
    simp only [SPath.resolveT_wk, TState.copyStToMG_lift, TRes.map_bind]
    rfl
  | newArr n hn =>
    show Except.ok ((τ.lift h d).copyStToMG (newArrT R ((n.wk h).evalT (τ.lift h d)) hn) _) =
      Except.ok (Grew.lift h d (τ.copyStToMG (newArrT R (n.evalT τ) hn) _))
    rw [Simple.evalT_wk, TState.copyStToMG_lift]

end Grow

/-! ## Statements that open no scope -/

section Stmts

variable {Γ Δ : Ctx} (h : Thin Γ Δ) (τ : TState C Γ) (d : TEnv C τ.H Δ)

theorem opStoreT_lift (op : BinOp) {p : PrimTy} (r : SRef C (.prim p)) (v : p.Denote) :
    opStoreT (τ.lift h d) op r v = liftedT h d (opStoreT τ op r v) := by
  simp only [opStoreT, liftedT_bind]
  lift_fin

theorem opMemT_lift (op : BinOp) {p : PrimTy} (a : MAddr τ.H (.prim p)) (v : p.Denote) :
    opMemT (τ.lift h d) op a v = liftedT h d (opMemT τ op a v) := by
  simp only [opMemT, liftedT_bind]
  lift_fin

theorem OpLoc.storeT_wk (op : BinOp) {p : PrimTy} (l : OpLoc C Γ p) (v : p.Denote) :
    (l.wk h).storeT (τ.lift h d) op v = liftedT h d (l.storeT τ op v) := by
  cases l with
  | «local» i =>
    simp only [OpLoc.wk, OpLoc.storeT, TState.get_lift, liftedT_bind, TState.lift_setLocal]
    lift_fin
  | root r _ => exact opStoreT_lift h τ d op _ v
  | field b f _ =>
    simp only [OpLoc.wk, OpLoc.storeT, Loc.resolveT, SPath.resolveT_wk, opStoreT_lift,
      TRes.map_bind]
  | index _ b i =>
    simp only [OpLoc.wk, OpLoc.storeT, Loc.resolveT, SPath.resolveT_wk, Val.evalT,
      Simple.evalT_wk, liftedT_bind, opStoreT_lift]
    rfl
  | mfield b f _ =>
    simp only [OpLoc.wk, OpLoc.storeT, MLoc.addrT, MPath.mvalT_wk, liftedT_bind, opMemT_lift]
    rfl
  | mindex _ b i =>
    simp only [OpLoc.wk, OpLoc.storeT, MLoc.addrT, MPath.mvalT_wk, Val.evalT, Simple.evalT_wk,
      liftedT_bind, opMemT_lift]
    rfl

theorem bumpStoreT_lift (op : IncDec) {p : PrimTy} (r : SRef C (.prim p)) :
    bumpStoreT (τ.lift h d) op r = liftedT₂ h d (bumpStoreT τ op r) := by
  simp only [bumpStoreT, liftedT₂_bind]
  lift_fin

theorem bumpMemT_lift (op : IncDec) {p : PrimTy} (a : MAddr τ.H (.prim p)) :
    bumpMemT (τ.lift h d) op a = liftedT₂ h d (bumpMemT τ op a) := by
  simp only [bumpMemT, liftedT₂_bind]
  lift_fin

theorem OpLoc.bumpT_wk (op : IncDec) {p : PrimTy} (l : OpLoc C Γ p) :
    (l.wk h).bumpT (τ.lift h d) op = liftedT₂ h d (l.bumpT τ op) := by
  cases l with
  | «local» i =>
    simp only [OpLoc.wk, OpLoc.bumpT, TState.get_lift, liftedT₂_bind, TState.lift_setLocal]
    lift_fin
  | root r _ => exact bumpStoreT_lift h τ d op _
  | field b f _ =>
    simp only [OpLoc.wk, OpLoc.bumpT, Loc.resolveT, SPath.resolveT_wk, liftedT₂_bind,
      bumpStoreT_lift]
  | index _ b i =>
    simp only [OpLoc.wk, OpLoc.bumpT, Loc.resolveT, SPath.resolveT_wk, Val.evalT,
      Simple.evalT_wk, liftedT₂_bind, bumpStoreT_lift]
    rfl
  | mfield b f _ =>
    simp only [OpLoc.wk, OpLoc.bumpT, MLoc.addrT, MPath.mvalT_wk, liftedT₂_bind, bumpMemT_lift]
    rfl
  | mindex _ b i =>
    simp only [OpLoc.wk, OpLoc.bumpT, MLoc.addrT, MPath.mvalT_wk, Val.evalT, Simple.evalT_wk,
      liftedT₂_bind, bumpMemT_lift]
    rfl

theorem sendT_lift (pv : Idx Γ (.val .bool)) (addr amt : Int) :
    sendT (τ.lift h d) (pv.wk h) addr amt = Out.lift h d (sendT τ pv addr amt) := by
  unfold sendT
  rw [show (τ.lift h d).tx = τ.tx from rfl]
  split <;> simp only [TState.lift_pay, TState.lift_setLocal] <;> lift_fin

theorem clearT_lift : {T : Ty} → (a : MAddr τ.H T) → (hm : T.mapFree = true) →
    TRun.clearT (τ.lift h d) a hm = liftedT h d (TRun.clearT τ a hm)
  | .prim _, a, _ => by
    simp only [TRun.clearT, liftedT_bind]
    lift_fin
  | .ref R, a, hm => by
    simp only [TRun.clearT, TState.allocDefaultG, TState.grow, TState.adopt, TState.lift,
      TState.withEnv]
    split <;> rename_i hw <;> rw [hw]
    · simp only [TState.withHeap, TEnv.put_wk]
      rfl
    · rfl

end Stmts

section Stmts2

variable {Γ Δ : Ctx} (h : Thin Γ Δ) (τ : TState C Γ) (d : TEnv C τ.H Δ)

/-- A declaration's outcome, lifted. -/
abbrev liftedTopT {H : HTy} {t : LTy} (d : TEnv C H Δ) (r : TRes (Out C H (t :: Γ))) :
    TRes (Out C H (t :: Δ)) :=
  r.map (Out.liftTop h d)

theorem liftedTopT_bind {H : HTy} {t : LTy} (d : TEnv C H Δ) {α : Type} (x : TRes α)
    (f : α → TRes (Out C H (t :: Γ))) :
    liftedTopT h d (x >>= f) = x >>= fun a => liftedTopT h d (f a) := by
  cases x <;> rfl

theorem liftedTopT_pure {H : HTy} {t : LTy} (d : TEnv C H Δ) (a : Out C H (t :: Γ)) :
    liftedTopT h d (pure a) = pure (Out.liftTop h d a) := rfl

theorem TRun.assign_wk {T : Ty} (l : Loc C Γ T) (r : Src C Γ T) :
    TRun.assign (l.wk h) (r.wk h) (τ.lift h d) = liftedT h d (TRun.assign l r τ) := by
  simp only [TRun.assign, Src.valueT_wk, Loc.resolveT_wk, liftedT_bind]
  lift_fin

theorem TRun.rebind_wk {R : RefTy} (i : Idx Γ (.alias R)) (r : ARhs C Γ R) :
    TRun.rebind (i.wk h) (r.wk h) (τ.lift h d) = liftedT h d (TRun.rebind i r τ) := by
  simp only [TRun.rebind, ARhs.evalT_wk, liftedT_bind, TState.lift_withStorage,
    TState.lift_setLocal]
  lift_fin

theorem TRun.assignLocal_wk {p : PrimTy} (i : Idx Γ (.val p)) (r : Val C Γ p) :
    TRun.assignLocal (i.wk h) (r.wk h) (τ.lift h d) = liftedT h d (TRun.assignLocal i r τ) := by
  simp only [TRun.assignLocal, Val.evalT_wk, liftedT_bind, TState.lift_setLocal]
  lift_fin

theorem TRun.opAssign_wk {p : PrimTy} (op : BinOp) (l : OpLoc C Γ p) (r : Val C Γ p) :
    TRun.opAssign op (l.wk h) (r.wk h) (τ.lift h d) = liftedT h d (TRun.opAssign op l r τ) := by
  simp only [TRun.opAssign, Val.evalT_wk, liftedT_bind, OpLoc.storeT_wk]

theorem TRun.incDec_wk {p : PrimTy} (op : IncDec) (l : OpLoc C Γ p) :
    TRun.incDec op (l.wk h) (τ.lift h d) = liftedT h d (TRun.incDec op l τ) := by
  simp only [TRun.incDec, OpLoc.bumpT_wk]
  cases l.bumpT τ op <;> rfl

theorem TRun.assignIncDec_wk {p : PrimTy} (i : Idx Γ (.val p)) (op : IncDec) (l : OpLoc C Γ p) :
    TRun.assignIncDec (i.wk h) op (l.wk h) (τ.lift h d) =
      liftedT h d (TRun.assignIncDec i op l τ) := by
  simp only [TRun.assignIncDec, OpLoc.bumpT_wk]
  cases l.bumpT τ op with
  | error => rfl
  | ok x =>
    show Except.ok (⟨(x.1.st.lift h (TEnv.wk x.1.ext Δ d)).setLocal (i.wk h) x.2, x.1.ext⟩ :
        Out C τ.H Δ) = Except.ok ⟨(x.1.st.setLocal i x.2).lift h (TEnv.wk x.1.ext Δ d), x.1.ext⟩
    simp only [TState.lift_setLocal]

theorem TRun.push_wk {E : Ty} (b : SPath C Γ (.array E)) (v : Option (Src C Γ E)) :
    TRun.push (b.wk h) (v.map (·.wk h)) (τ.lift h d) = liftedT h d (TRun.push b v τ) := by
  cases v with
  | none =>
    simp only [TRun.push, Option.map, SPath.resolveT_wk, liftedT_bind, liftedT_ite,
      liftedT_error, TState.lift_storage]
    lift_fin
  | some r =>
    simp only [TRun.push, Option.map, SPath.resolveT_wk, Src.valueT_wk, liftedT_bind,
      liftedT_ite, liftedT_error, TState.lift_storage]
    lift_fin

theorem TRun.pop_wk {E : Ty} (b : SPath C Γ (.array E)) :
    TRun.pop (b.wk h) (τ.lift h d) = liftedT h d (TRun.pop b τ) := by
  simp only [TRun.pop, SPath.resolveT_wk, liftedT_bind]
  lift_fin

theorem TRun.transfer_wk (r a : Val C Γ .uint) :
    TRun.transfer (r.wk h) (a.wk h) (τ.lift h d) = liftedT h d (TRun.transfer r a τ) := by
  simp only [TRun.transfer, Val.evalT_wk, liftedT_bind, TState.lift_pay]
  lift_fin

theorem TRun.send_wk (pv : Idx Γ (.val .bool)) (r a : Val C Γ .uint) :
    TRun.send (pv.wk h) (r.wk h) (a.wk h) (τ.lift h d) = liftedT h d (TRun.send pv r a τ) := by
  simp only [TRun.send, Val.evalT_wk, liftedT_bind, sendT_lift, liftedT_pure]

theorem TRun.assignFromMem_wk {R : RefTy} (l : Loc C Γ (.ref R)) (q : MPath C Γ (.ref R)) :
    TRun.assignFromMem (l.wk h) (q.wk h) (τ.lift h d) =
      liftedT h d (TRun.assignFromMem l q τ) := by
  simp only [TRun.assignFromMem, MPath.mvalT_wk, Loc.resolveT_wk, liftedT_bind]
  lift_fin

theorem TRun.assignMem_wk {T : Ty} (l : MLoc C Γ T) (r : MSrc C Γ T) :
    TRun.assignMem (l.wk h) (r.wk h) (τ.lift h d) = liftedT h d (TRun.assignMem l r τ) := by
  simp only [TRun.assignMem, MSrc.mvalT_wk, MLoc.addrT_wk, liftedT_bind]
  lift_fin

theorem TRun.delete_wk {T : Ty} (l : Loc C Γ T) :
    TRun.delete (l.wk h) (τ.lift h d) = liftedT h d (TRun.delete l τ) := by
  simp only [TRun.delete, Loc.resolveT_wk, liftedT_bind]
  lift_fin

theorem TRun.require_wk (c : Val C Γ .bool) :
    TRun.require (c.wk h) (τ.lift h d) = liftedT h d (TRun.require c τ) := by
  simp only [TRun.require, Val.evalT_wk, liftedT_bind, liftedT_ite, liftedT_pure, Out.lift_refl]
  rfl

theorem TRun.assert_wk (c : Val C Γ .bool) :
    TRun.assert (c.wk h) (τ.lift h d) = liftedT h d (TRun.assert c τ) := by
  simp only [TRun.assert, Val.evalT_wk, liftedT_bind, liftedT_ite, liftedT_pure, Out.lift_refl]
  rfl

theorem TRun.declLocal_wk (p : PrimTy) (init : Option (Val C Γ p)) :
    TRun.declLocal p (init.map (·.wk h)) (τ.lift h d) = liftedTopT h d (TRun.declLocal p init τ) := by
  cases init with
  | none =>
    simp only [TRun.declLocal, Option.map, liftedTopT_bind, liftedTopT_pure]
    lift_fin
  | some e =>
    simp only [TRun.declLocal, Option.map, Val.evalT_wk, liftedTopT_bind, liftedTopT_pure]
    lift_fin

theorem TRun.declStorage_wk (R : RefTy) (init : Option (ARhs C Γ R)) :
    TRun.declStorage R (init.map (·.wk h)) (τ.lift h d) =
      liftedTopT h d (TRun.declStorage R init τ) := by
  cases init with
  | none =>
    simp only [TRun.declStorage, Option.map, liftedTopT_pure]
    lift_fin
  | some r =>
    simp only [TRun.declStorage, Option.map, ARhs.evalT_wk, liftedTopT_bind, liftedTopT_pure]
    lift_fin

theorem TRun.declMem_wk (R : RefTy) (init : Option (MRhs C Γ R)) (hm : (Ty.ref R).mapFree = true) :
    TRun.declMem R (init.map (·.wk h)) hm (τ.lift h d) =
      liftedTopT h d (TRun.declMem R init hm τ) := by
  cases init with
  | none =>
    simp only [TRun.declMem, Option.map, TState.allocDefaultG, TState.grow, TState.adopt,
      TState.lift, TState.withEnv, TState.push, liftedTopT_pure, Out.liftTop, TEnv.put_wk]
    rfl
  | some r =>
    simp only [TRun.declMem, Option.map, MRhs.evalT_wk]
    cases r.evalT τ <;> rfl

theorem TRun.rebindMem_wk {R : RefTy} (i : Idx Γ (.mem R)) (r : MRhs C Γ R) :
    TRun.rebindMem (i.wk h) (r.wk h) (τ.lift h d) = liftedT h d (TRun.rebindMem i r τ) := by
  simp only [TRun.rebindMem, MRhs.evalT_wk]
  cases r.evalT τ with
  | error => rfl
  | ok g =>
    show Except.ok (⟨(g.st.lift h (TEnv.wk g.ext Δ d)).setLocal (i.wk h) g.val, g.ext⟩ :
        Out C τ.H Δ) = Except.ok ⟨(g.st.setLocal i g.val).lift h (TEnv.wk g.ext Δ d), g.ext⟩
    simp only [TState.lift_setLocal]

theorem TRun.deleteMem_wk {T : Ty} (q : MPath C Γ T) :
    TRun.deleteMem (q.wk h) (τ.lift h d) = liftedT h d (TRun.deleteMem q τ) := by
  cases q with
  | var i hm =>
    simp only [TRun.deleteMem, MPath.wk, TState.allocDefaultG, TState.grow, TState.adopt,
      TState.lift, TState.withEnv, TState.setLocal, liftedT_pure, Out.lift, TEnv.put_wk,
      TEnv.set_put]
  | loc l =>
    simp only [TRun.deleteMem, MPath.wk, MLoc.addrT_wk, liftedT_bind, clearT_lift]
    rfl

/-- `new`'s write of the fresh array `g` into its target (`TRun.assignNew`
after the allocation). -/
def TRun.newWrite {Γ : Ctx} {H : HTy} {R : RefTy} (l : NewLhs C Γ R)
    (g : Grew C Γ H (MVal · (.ref R))) : TRes (Out C H Γ) :=
  match l with
  | .store l => do
    let ref ← l.resolveT g.st
    let st ← TRes.ofOpt (g.st.storage.write ref (MVal.copyMToSt g.st.heap g.val))
    pure ⟨g.st.withStorage st, g.ext⟩
  | .mem l => do
    let a ← l.addrT g.st
    let hp ← TRes.ofOpt (g.st.heap.writeAddr a g.val)
    pure ⟨g.st.withHeap hp, g.ext⟩

theorem TRun.assignNew_eq {Γ : Ctx} {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint)
    (hn : R.newArrOk = true) (σ : TState C Γ) :
    TRun.assignNew l n hn σ =
      TRun.newWrite l (σ.copyStToMG (newArrT R (n.evalT σ) hn) (RefTy.mapFree_of_newArrOk hn)) := by
  cases l <;> rfl

theorem TRun.newWrite_wk {R : RefTy} (l : NewLhs C Γ R) (g : Grew C Γ τ.H (MVal · (.ref R))) :
    TRun.newWrite (l.wk h) (Grew.lift h d g) = liftedT h d (TRun.newWrite l g) := by
  cases l with
  | store l =>
    simp only [TRun.newWrite, NewLhs.wk, Grew.lift, Loc.resolveT_wk, liftedT_bind,
      TState.lift_withStorage]
    lift_fin
  | mem l =>
    simp only [TRun.newWrite, NewLhs.wk, Grew.lift, MLoc.addrT_wk, liftedT_bind]
    lift_fin

theorem TRun.assignNew_wk {R : RefTy} (l : NewLhs C Γ R) (n : Simple C Γ .uint)
    (hn : R.newArrOk = true) :
    TRun.assignNew (l.wk h) (n.wk h) hn (τ.lift h d) = liftedT h d (TRun.assignNew l n hn τ) := by
  rw [TRun.assignNew_eq, TRun.assignNew_eq, Simple.evalT_wk, TState.copyStToMG_lift,
    TRun.newWrite_wk]

end Stmts2

/-! ## Outcomes related by a weakening -/

section Rel

variable {Γ Δ : Ctx} {H : HTy}

/-- A scope's locals popped from an outcome. -/
def Out.drop {Γ' : Ctx} (e : Ext Γ Γ') (a : Out C H Γ') : Out C H Γ := ⟨a.st.drop e, a.ext⟩

/-- Two outcomes, the second the first's run weakened by `h`: the same halt,
or states the first's lifted over locals whose dropped ones hold `o`,
weakened along the heap the run grew. -/
def TWkRel (h : Thin Γ Δ) (o : List ((t : LTy) × t.TDenote C H)) :
    TRes (Out C H Γ) → TRes (Out C H Δ) → Prop
  | .ok a, .ok b => ∃ d : TEnv C a.st.H Δ, TEnv.off h d = offWk a.ext o ∧ b = ⟨a.st.lift h d, a.ext⟩
  | .error e, .error e' => e = e'
  | _, _ => False

theorem TWkRel.of_eq {h : Thin Γ Δ} {d : TEnv C H Δ} {r₀ : TRes (Out C H Γ)}
    {r : TRes (Out C H Δ)} (he : r = liftedT h d r₀) : TWkRel h (TEnv.off h d) r₀ r := by
  subst he
  cases r₀ with
  | error => rfl
  | ok a => exact ⟨TEnv.wk a.ext Δ d, TEnv.off_wk a.ext h d, rfl⟩

theorem TWkRel.of_top {t : LTy} {h : Thin Γ Δ} {d : TEnv C H Δ} {r₀ : TRes (Out C H (t :: Γ))}
    {r : TRes (Out C H (t :: Δ))} (he : r = liftedTopT h d r₀) :
    TWkRel (.keep h) (TEnv.off h d) r₀ r := by
  subst he
  cases r₀ with
  | error => rfl
  | ok a => exact ⟨(a.st.env.1, TEnv.wk a.ext Δ d), TEnv.off_wk a.ext h d, rfl⟩

/-- The run lifted, when the background is fixed. -/
theorem TWkRel.eq_lifted {h : Thin Γ Δ} {d : TEnv C H Δ} {r₀ : TRes (Out C H Γ)}
    {r : TRes (Out C H Δ)} (hr : TWkRel h (TEnv.off h d) r₀ r) : r = liftedT h d r₀ := by
  cases r₀ with
  | error e => cases r with
    | error e' => cases hr; rfl
    | ok => cases hr
  | ok a => cases r with
    | error => cases hr
    | ok b =>
      obtain ⟨d', hd, rfl⟩ := hr
      rw [← TEnv.off_wk] at hd
      show Except.ok (⟨a.st.lift h d', a.ext⟩ : Out C H Δ) = Except.ok ⟨a.st.lift h _, a.ext⟩
      simp only [TState.lift_congr h a.st hd]

theorem TWkRel.bind_same {α : Type} {h : Thin Γ Δ} {o : List ((t : LTy) × t.TDenote C H)}
    (x : TRes α) {f : α → TRes (Out C H Γ)} {g : α → TRes (Out C H Δ)}
    (hfg : ∀ a, TWkRel h o (f a) (g a)) : TWkRel h o (x >>= f) (x >>= g) := by
  cases x with
  | error => rfl
  | ok a => exact hfg a

/-- A sequence's two halves related: the second run from the first's
states. -/
theorem TWkRel.seq {Γ₁ Δ₁ Γ₂ Δ₂ : Ctx} {h : Thin Γ Δ} {h₁ : Thin Γ₁ Δ₁} {h₂ : Thin Γ₂ Δ₂}
    {τ : TState C Γ} {d₀ : TEnv C τ.H Δ} {o : List ((t : LTy) × t.TDenote C τ.H)}
    {F : TStep C Γ Γ₁} {G : TStep C Δ Δ₁} (hr : TWkRel h₁ o (F τ) (G (τ.lift h d₀)))
    {f : TStep C Γ₁ Γ₂} {g : TStep C Δ₁ Δ₂}
    (hfg : ∀ (a : TState C Γ₁) (d' : TEnv C a.H Δ₁),
      TWkRel h₂ (TEnv.off h₁ d') (f a) (g (a.lift h₁ d'))) :
    TWkRel h₂ o (TRun.seq F f τ) (TRun.seq G g (τ.lift h d₀)) := by
  unfold TRun.seq
  generalize F τ = r₀ at hr ⊢
  generalize G (τ.lift h d₀) = r at hr ⊢
  cases r₀ with
  | error e => cases r with
    | error e' => exact hr
    | ok => cases hr
  | ok a => cases r with
    | error => cases hr
    | ok b =>
      obtain ⟨d', hd', rfl⟩ := hr
      have h2 := hfg a.st d'
      dsimp only
      revert h2
      cases f a.st with
      | error e => cases g (a.st.lift h₁ d') with
        | error e' => exact id
        | ok => exact False.elim
      | ok c => cases g (a.st.lift h₁ d') with
        | error => exact False.elim
        | ok c' =>
          rintro ⟨d'', hd'', rfl⟩
          refine ⟨d'', ?_, rfl⟩
          rw [hd'', hd', offWk_trans]

/-! ### A scope's end on both sides -/

theorem Thin.Over.tenv {Γ Γ' Δ Δ' : Ctx} {e : Ext Γ Γ'} {h : Thin Γ Δ} {e' : Ext Δ Δ'}
    {h' : Thin Γ' Δ'} (ho : Thin.Over e h e' h') (x : TEnv C H Γ') (d' : TEnv C H Δ') :
    TEnv.drop e' (TEnv.put h' x d') = TEnv.put h (TEnv.drop e x) (TEnv.drop e' d') ∧
      TEnv.off h (TEnv.drop e' d') = TEnv.off h' d' := by
  induction ho with
  | refl => exact ⟨rfl, rfl⟩
  | push _ ih => exact ih x.2 d'.2

theorem TWkRel.drop {Γ' Δ' : Ctx} {e : Ext Γ Γ'} {h : Thin Γ Δ} {e' : Ext Δ Δ'}
    {h' : Thin Γ' Δ'} (ho : Thin.Over e h e' h') {o : List ((t : LTy) × t.TDenote C H)}
    {r₀ : TRes (Out C H Γ')} {r : TRes (Out C H Δ')} (hr : TWkRel h' o r₀ r) :
    TWkRel h o (r₀.map (Out.drop e)) (r.map (Out.drop e')) := by
  cases r₀ with
  | error e => cases r with
    | error e' => exact hr
    | ok => cases hr
  | ok a => cases r with
    | error => cases hr
    | ok b =>
      obtain ⟨d', hd, rfl⟩ := hr
      obtain ⟨h1, h2⟩ := ho.tenv a.st.env d'
      refine ⟨TEnv.drop e' d', h2.trans hd, ?_⟩
      show (⟨(a.st.lift h' d').drop e', a.ext⟩ : Out C H Δ) = ⟨(a.st.drop e).lift h _, a.ext⟩
      simp only [TState.lift, TState.drop, TState.withEnv, h1]

/-- A loop body's run, related by `TWkRel.drop` and its background fixed,
is a lifted turn of the loop (`TRun.loop`'s body). -/
theorem loopTurn_lift {Γ₁ Δ₁ : Ctx} {e : Ext Γ Γ₁} {e' : Ext Δ Δ₁} {h : Thin Γ Δ}
    (d : TEnv C H Δ) (a : Out C H Γ) {X : TRes (Out C a.st.H Γ₁)} {Y : TRes (Out C a.st.H Δ₁)}
    (hr : Y.map (Out.drop e') = liftedT h (TEnv.wk a.ext Δ d) (X.map (Out.drop e))) :
    Y.map (fun o' => (⟨o'.st.drop e', a.ext.trans o'.ext⟩ : Out C H Δ)) =
      (X.map (fun o' => (⟨o'.st.drop e, a.ext.trans o'.ext⟩ : Out C H Γ))).map (Out.lift h d) := by
  cases X with
  | error e => cases Y with
    | error e' => cases hr; rfl
    | ok => cases hr
  | ok x => cases Y with
    | error => cases hr
    | ok y =>
      have hy : y.st.drop e' = (x.st.drop e).lift h (TEnv.wk x.ext Δ (TEnv.wk a.ext Δ d)) :=
        congrArg Out.st (Except.ok.inj hr)
      show Except.ok (⟨y.st.drop e', a.ext.trans y.ext⟩ : Out C H Δ) =
        Except.ok ⟨(x.st.drop e).lift h (TEnv.wk (a.ext.trans x.ext) Δ d), _⟩
      simp only [hy, TEnv.wk_trans]

end Rel

/-! ## A loop whose every turn is lifted -/

namespace TLoop

variable {α β : Type} {body : α → TRes α} {c : α → TRes Bool} {body' : β → TRes β}
  {c' : β → TRes Bool} (f : α → β)

theorem iterN_map (hc : ∀ a, c' (f a) = c a) (hb : ∀ a, body' (f a) = (body a).map f) :
    (n : Nat) → (σ : α) → iterN body' c' n (f σ) = Sum.map f (Except.map f) (iterN body c n σ)
  | 0, _ => rfl
  | n + 1, σ => by
    simp only [iterN, step, hc, hb]
    cases c σ with
    | error => rfl
    | ok v =>
      cases v with
      | false => rfl
      | true =>
        simp only
        cases body σ with
        | error => rfl
        | ok τ => exact iterN_map hc hb n τ

/-- **A loop every turn of which is lifted by `f` runs lifted.** -/
theorem run_map (hc : ∀ a, c' (f a) = c a) (hb : ∀ a, body' (f a) = (body a).map f) (σ : α) :
    run body' c' (f σ) = (run body c σ).map f := by
  by_cases hex : ∃ r n, iterN body c n σ = .inr r
  · obtain ⟨r, n, hn⟩ := hex
    rw [run_of_iterN hn]
    apply run_of_iterN (n := n)
    rw [iterN_map f hc hb n σ, hn]
    rfl
  · have hex' : ¬ ∃ r n, iterN body' c' n (f σ) = .inr r := by
      rintro ⟨r, n, hn⟩
      rw [iterN_map f hc hb n σ] at hn
      cases hi : iterN body c n σ with
      | inl => rw [hi] at hn; cases hn
      | inr r₀ => exact hex ⟨r₀, n, hi⟩
    simp only [run, hex, hex', dite_false]
    rfl

end TLoop

/-! ## Loops: unfolding, induction, a variant -/

namespace TLoop

variable {α : Type} {body : α → TRes α} {c : α → TRes Bool}

/-- **One turn of a loop**: the loop is its first step, then the loop again
from where the body left it. -/
theorem run_unfold (σ : α) :
    run body c σ = match step body c σ with
      | .inl τ => run body c τ
      | .inr r => r := by
  cases hs : step body c σ with
  | inr r =>
    show run body c σ = r
    exact run_of_iterN (n := 1) (by simp only [iterN, hs])
  | inl τ =>
    show run body c σ = run body c τ
    have hshift : ∀ n, iterN body c (n + 1) σ = iterN body c n τ := fun n => by
      simp only [iterN, hs]
    by_cases hex : ∃ r n, iterN body c n τ = .inr r
    · obtain ⟨r, n, h⟩ := hex
      rw [run_of_iterN h, run_of_iterN ((hshift n).trans h)]
    · have hex' : ¬ ∃ r n, iterN body c n σ = .inr r := by
        rintro ⟨r, n, h⟩
        cases n with
        | zero => simp only [iterN, reduceCtorEq] at h
        | succ n => exact hex ⟨r, n, (hshift n).symm.trans h⟩
      simp only [run, hex, hex', dite_false]

/-- **Induction over a loop's run**: `P` holds of the first state and of
every state an iteration from a state in `P` goes on in, and `Q` of every
outcome an iteration from a state in `P` is done with, and of a divergence:
then `Q` holds of the loop's run. -/
theorem run_induct {P : α → Prop} {Q : TRes α → Prop} {σ : α} (h0 : P σ)
    (hstep : ∀ τ, P τ →
      match step body c τ with
      | .inl τ' => P τ'
      | .inr r => Q r)
    (hdiv : Q (.error .diverge)) : Q (run body c σ) := by
  have key : ∀ (n : Nat) (τ : α) (r : TRes α), P τ → iterN body c n τ = .inr r → Q r := by
    intro n
    induction n with
    | zero => intro τ r _ h; exact nomatch h
    | succ n ih =>
      intro τ r hp h
      have hs := hstep τ hp
      simp only [iterN] at h
      revert hs h
      cases step body c τ with
      | inl τ' => exact fun he hp => ih τ' r hp he
      | inr r' =>
        intro he hp
        cases (show Sum.inr r' = (Sum.inr r : α ⊕ TRes α) from he)
        exact hp
  unfold run
  split
  · rename_i hex
    obtain ⟨n, hn⟩ := Classical.choose_spec hex
    exact key n σ _ h0 hn
  · exact hdiv

/-- **A loop with a variant ends**: from every head in `H` the variant `D`
is defined and the condition is read, the loop ends well (`G`) where it is
false, and where it is true the body runs to a head in `H` where, if the
condition holds again, the variant is smaller and not negative
(`Calculus/Core/SoundLoops.lean`'s `Loop.run_variant`, the condition a
`Bool`). -/
theorem run_variant {H G : α → Prop} {D : α → TRes Int}
    (hstep : ∀ τ, H τ → ∃ d, D τ = .ok d ∧
      (c τ = .ok true ∨ c τ = .ok false) ∧
      (c τ = .ok false → G τ) ∧
      (c τ = .ok true → ∃ τ₁, body τ = .ok τ₁ ∧ H τ₁ ∧
        (c τ₁ = .ok true → ∃ a : Int, D τ₁ = .ok a ∧ 0 ≤ a ∧ a < d)))
    {σ : α} (h0 : H σ) : ∃ τ, run body c σ = .ok τ ∧ G τ := by
  have exit : ∀ τ, c τ = .ok false → run body c τ = .ok τ := fun τ hc => by
    rw [run_unfold]; simp only [step, hc]
  have next : ∀ τ τ₁, c τ = .ok true → body τ = .ok τ₁ → run body c τ = run body c τ₁ :=
    fun τ τ₁ hc hb => by
      rw [run_unfold (σ := τ)]; simp only [step, hc, hb]
  have T : ∀ n : Nat, ∀ τ, H τ →
      (c τ = .ok true → ∃ a : Int, D τ = .ok a ∧ 0 ≤ a ∧ a < n) →
      ∃ τf, run body c τ = .ok τf ∧ G τf := by
    intro n
    induction n with
    | zero =>
      intro τ hH hb
      obtain ⟨_, _, hcov, hex, _⟩ := hstep τ hH
      rcases hcov with hc | hc
      · obtain ⟨a, _, h₁, h₂⟩ := hb hc
        omega
      · exact ⟨τ, exit τ hc, hex hc⟩
    | succ n ih =>
      intro τ hH hb
      obtain ⟨d, hd, hcov, hex, hbody⟩ := hstep τ hH
      rcases hcov with hc | hc
      · obtain ⟨a, hda, h₁, h₂⟩ := hb hc
        obtain ⟨τ₁, hb₁, hH₁, hdec⟩ := hbody hc
        rw [next τ τ₁ hc hb₁]
        refine ih τ₁ hH₁ fun hc₁ => ?_
        obtain ⟨a₁, hd₁, h₃, h₄⟩ := hdec hc₁
        rw [hda] at hd
        cases hd
        exact ⟨a₁, hd₁, h₃, by omega⟩
      · exact ⟨τ, exit τ hc, hex hc⟩
  obtain ⟨d, _, hcov, hex, hbody⟩ := hstep σ h0
  rcases hcov with hc | hc
  · obtain ⟨τ₁, hb₁, hH₁, hdec⟩ := hbody hc
    rw [next σ τ₁ hc hb₁]
    refine T d.toNat τ₁ hH₁ fun hc₁ => ?_
    obtain ⟨a₁, hd₁, h₃, h₄⟩ := hdec hc₁
    exact ⟨a₁, hd₁, h₃, by omega⟩
  · exact ⟨σ, exit σ hc, hex hc⟩

end TLoop

/-! ## A weakened statement runs as the statement -/

theorem CallRet.enterT_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {rs Γ' : Ctx} (ret : CallRet Γ rs Γ')
    {ps : Ctx} (τ : TState C ps) : (ret.wk h).2.2.enterT τ = ret.enterT τ := by
  cases ret <;> rfl

theorem CallRet.leaveT_wk {Γ Δ : Ctx} {H : HTy} (h : Thin Γ Δ) (e : TEnv C H Γ) (d : TEnv C H Δ)
    {rs Γ' : Ctx} (ret : CallRet Γ rs Γ') (x : TEnv C H rs) :
    ∃ d', TEnv.off (ret.wk h).2.1 d' = TEnv.off h d ∧
      (ret.wk h).2.2.leaveT (TEnv.put h e d) x = TEnv.put (ret.wk h).2.1 (ret.leaveT e x) d' := by
  cases ret with
  | none => exact ⟨d, rfl, rfl⟩
  | val p r res =>
    cases res with
    | none => exact ⟨d, rfl, rfl⟩
    | some i => exact ⟨d, rfl, TEnv.set_put h i x.1 e d⟩
  | rets bs =>
    exact ⟨TEnv.append _ x d, TEnv.off_keepAll h _ x d, (TEnv.put_keepAll h _ x x e d).symm⟩
  | mem R r hd hm => exact ⟨(x.1, d), rfl, rfl⟩

/-- A call after its arguments: the frame entered (`o₁`), the body run, the
caller's locals given back (`TRun.call`). -/
def TRun.callFrom {Γ Γ' ps rs Γf : Ctx} (ret : CallRet Γ rs Γ') (hb : Ext (rs ++ ps) Γf)
    (body : TStep C (rs ++ ps) Γf) (σ : TState C Γ) (o₁ : Out C σ.H (rs ++ ps)) :
    TRes (Out C σ.H Γ') := do
  let o ← body o₁.st
  let e : σ.H <+: o.st.H := o₁.ext.trans o.ext
  pure ⟨o.st.withEnv (ret.leaveT (TEnv.wk e Γ σ.env) (TEnv.take rs (TEnv.drop hb o.st.env))), e⟩

theorem TRun.call_eq {Γ Γ' ps rs Γf : Ctx} (args : Args C Γ ps) (ret : CallRet Γ rs Γ')
    (hb : Ext (rs ++ ps) Γf) (body : TStep C (rs ++ ps) Γf) (σ : TState C Γ) :
    TRun.call args ret hb body σ =
      args.evalT σ >>= fun a => TRun.callFrom ret hb body σ (ret.enterT (σ.withEnv a)) := rfl

theorem TRun.callFrom_wk {Γ Δ Γ' ps rs Γf : Ctx} (h : Thin Γ Δ) (τ : TState C Γ)
    (d : TEnv C τ.H Δ) (ret : CallRet Γ rs Γ') (hb : Ext (rs ++ ps) Γf)
    (body : TStep C (rs ++ ps) Γf) (o₁ : Out C τ.H (rs ++ ps)) :
    TWkRel (ret.wk h).2.1 (TEnv.off h d) (TRun.callFrom ret hb body τ o₁)
      (TRun.callFrom (ret.wk h).2.2 hb body (τ.lift h d) o₁) := by
  unfold TRun.callFrom
  cases body o₁.st with
  | error => rfl
  | ok o =>
    have ee : τ.H <+: o.st.H := o₁.ext.trans o.ext
    obtain ⟨d', hd', he⟩ := CallRet.leaveT_wk h (TEnv.wk ee _ τ.env) (TEnv.wk ee _ d) ret
      (TEnv.take _ (TEnv.drop hb o.st.env))
    refine ⟨d', by rw [hd', TEnv.off_wk], ?_⟩
    show (⟨o.st.withEnv ((ret.wk h).2.2.leaveT (TEnv.wk ee _ (TEnv.put h τ.env d)) _), ee⟩ :
      Out C τ.H _) = _
    rw [TEnv.put_wk, he]
    rfl

mutual

/-- **A weakened statement runs as the statement**: from a state of `Δ`, it
does what the statement does from that state's locals of `Γ`, and keeps the
others, weakened along the heap it grew. -/
theorem Stmt.trun_wk : {Γ Γ' : Ctx} → (s : Stmt C Γ Γ') → ∀ {Δ : Ctx} (h : Thin Γ Δ)
    (τ : TState C Γ) (d : TEnv C τ.H Δ),
    TWkRel (s.wk h).2.1 (TEnv.off h d) (s.trun τ) ((s.wk h).2.2.trun (τ.lift h d))
  | _, _, .assign l r, _, h, τ, d => TWkRel.of_eq (TRun.assign_wk h τ d l r)
  | _, _, .rebind i r, _, h, τ, d => TWkRel.of_eq (TRun.rebind_wk h τ d i r)
  | _, _, .assignLocal i r, _, h, τ, d => TWkRel.of_eq (TRun.assignLocal_wk h τ d i r)
  | _, _, .declLocal p _ init, _, h, τ, d => TWkRel.of_top (TRun.declLocal_wk h τ d p init)
  | _, _, .declStorage R _ init, _, h, τ, d => TWkRel.of_top (TRun.declStorage_wk h τ d R init)
  | _, _, .opAssign op _ _ l r, _, h, τ, d => TWkRel.of_eq (TRun.opAssign_wk h τ d op l r)
  | _, _, .incDec op _ l, _, h, τ, d => TWkRel.of_eq (TRun.incDec_wk h τ d op l)
  | _, _, .assignIncDec i op _ l _, _, h, τ, d =>
    TWkRel.of_eq (TRun.assignIncDec_wk h τ d i op l)
  | _, _, .push b v _, _, h, τ, d => TWkRel.of_eq (TRun.push_wk h τ d b v)
  | _, _, .pop b, _, h, τ, d => TWkRel.of_eq (TRun.pop_wk h τ d b)
  | _, _, .transfer r a, _, h, τ, d => TWkRel.of_eq (TRun.transfer_wk h τ d r a)
  | _, _, .send pv r a, _, h, τ, d => TWkRel.of_eq (TRun.send_wk h τ d pv r a)
  | _, _, .declMem R _ init _ hm, _, h, τ, d => TWkRel.of_top (TRun.declMem_wk h τ d R init hm)
  | _, _, .rebindMem i r, _, h, τ, d => TWkRel.of_eq (TRun.rebindMem_wk h τ d i r)
  | _, _, .assignFromMem l q, _, h, τ, d => TWkRel.of_eq (TRun.assignFromMem_wk h τ d l q)
  | _, _, .assignMem l r, _, h, τ, d => TWkRel.of_eq (TRun.assignMem_wk h τ d l r)
  | _, _, .delete l, _, h, τ, d => TWkRel.of_eq (TRun.delete_wk h τ d l)
  | _, _, .deleteMem q _, _, h, τ, d => TWkRel.of_eq (TRun.deleteMem_wk h τ d q)
  | _, _, .assignNew l n hn, _, h, τ, d => TWkRel.of_eq (TRun.assignNew_wk h τ d l n hn)
  | _, _, .require c, _, h, τ, d => TWkRel.of_eq (TRun.require_wk h τ d c)
  | _, _, .assert c, _, h, τ, d => TWkRel.of_eq (TRun.assert_wk h τ d c)
  | _, _, .revert, _, h, τ, d => rfl
  | _, _, .ite c thn els, _, h, τ, d => by
    show TWkRel h _ (TRun.ite c thn.ext thn.trunR els.ext els.trunR τ)
      (TRun.ite (c.wk h) (thn.wk h).2.2.ext (thn.wk h).2.2.trunR (els.wk h).2.2.ext
        (els.wk h).2.2.trunR (τ.lift h d))
    unfold TRun.ite
    rw [Val.evalT_wk]
    refine TWkRel.bind_same _ fun v => ?_
    cases boolT v
    · exact TWkRel.drop (Prog.wk_over els h) (Prog.trun_wk els h τ d)
    · exact TWkRel.drop (Prog.wk_over thn h) (Prog.trun_wk thn h τ d)
  | _, _, .call f args ret body, _, h, τ, d => by
    show TWkRel (ret.wk h).2.1 (TEnv.off h d) (TRun.call args ret body.ext body.trunR τ)
      (TRun.call (args.wk h) (ret.wk h).2.2 body.ext body.trunR (τ.lift h d))
    rw [TRun.call_eq, TRun.call_eq, Args.evalT_wk]
    refine TWkRel.bind_same _ fun a => ?_
    rw [CallRet.enterT_wk]
    exact TRun.callFrom_wk h τ d ret body.ext body.trunR _
  | _, _, .tryCall call rets ok err code pnc other, _, h, τ, d => by
    show TWkRel h (TEnv.off h d)
      (TRun.tryCall call rets ok.ext ok.trunR err.ext err.trunR code pnc.ext pnc.trunR other.ext
        other.trunR τ)
      (TRun.tryCall (call.wk h) rets (ok.wk (Thin.keepAll _ h)).2.2.ext
        (ok.wk (Thin.keepAll _ h)).2.2.trunR (err.wk h).2.2.ext (err.wk h).2.2.trunR code
        (pnc.wk (Thin.keepAll _ h)).2.2.ext (pnc.wk (Thin.keepAll _ h)).2.2.trunR
        (other.wk h).2.2.ext (other.wk h).2.2.trunR (τ.lift h d))
    unfold TRun.tryCall
    rw [ExtCall.keyT_wk, show (τ.lift h d).tx = τ.tx from rfl]
    cases lookupBy (call.keyT τ) τ.tx.ext with
    | none => rfl
    | some o =>
      cases o with
      | ok vs =>
        refine TWkRel.bind_same _ fun ⟨r, _⟩ => ?_
        show TWkRel h _ (Except.map (Out.drop _) _) (Except.map (Out.drop _) _)
        rw [show (τ.lift h d).env = TEnv.put h τ.env d from rfl, ← TEnv.put_keepAll h _ r r τ.env d]
        have := TWkRel.drop (Thin.Over.trans (Thin.Over.append h _) (Prog.wk_over ok _))
          (Prog.trun_wk ok (Thin.keepAll _ h) (τ.withEnv (TEnv.append _ r τ.env))
            (TEnv.append _ r d))
        rwa [TEnv.off_keepAll] at this
      | error => exact TWkRel.drop (Prog.wk_over err h) (Prog.trun_wk err h τ d)
      | panic c =>
        refine TWkRel.bind_same _ fun r => ?_
        show TWkRel h _ (Except.map (Out.drop _) _) (Except.map (Out.drop _) _)
        rw [show (τ.lift h d).env = TEnv.put h τ.env d from rfl, ← TEnv.put_keepAll h _ r r τ.env d]
        have := TWkRel.drop (Thin.Over.trans (Thin.Over.append h _) (Prog.wk_over pnc _))
          (Prog.trun_wk pnc (Thin.keepAll _ h) (τ.withEnv (TEnv.append _ r τ.env))
            (TEnv.append _ r d))
        rwa [TEnv.off_keepAll] at this
      | other => exact TWkRel.drop (Prog.wk_over other h) (Prog.trun_wk other h τ d)
  | _, _, .loop a c body, _, h, τ, d => by
    apply TWkRel.of_eq
    show TLoop.run (fun o : Out C τ.H _ => ((body.wk h).2.2.trunR o.st).map
          fun o' => ⟨o'.st.drop (body.wk h).2.2.ext, o.ext.trans o'.ext⟩)
        (fun o => (c.wk h).evalT o.st) ⟨τ.lift h d, List.prefix_refl _⟩ =
      liftedT h d (TLoop.run (fun o : Out C τ.H _ => (body.trunR o.st).map
          fun o' => ⟨o'.st.drop body.ext, o.ext.trans o'.ext⟩)
        (fun o => c.evalT o.st) ⟨τ, List.prefix_refl _⟩)
    rw [← Out.lift_refl h τ d]
    refine TLoop.run_map (Out.lift h d) (fun a => Val.evalT_wk h a.st _ c) (fun a => ?_) _
    exact loopTurn_lift d a (TWkRel.drop (Prog.wk_over body h)
      (Prog.trun_wk body h a.st (TEnv.wk a.ext _ d))).eq_lifted
  | _, _, .block body, _, h, τ, d =>
    TWkRel.drop (Prog.wk_over body h) (Prog.trun_wk body h τ d)

/-- **A weakened sequence runs as the sequence.** -/
theorem Prog.trun_wk : {Γ Γ' : Ctx} → (P : Prog C Γ Γ') → ∀ {Δ : Ctx} (h : Thin Γ Δ)
    (τ : TState C Γ) (d : TEnv C τ.H Δ),
    TWkRel (P.wk h).2.1 (TEnv.off h d) (P.trun τ) ((P.wk h).2.2.trun (τ.lift h d))
  | _, _, .nil, _, h, τ, d => ⟨d, (offWk_self _ _).symm, rfl⟩
  | _, _, .cons s P, _, h, τ, d => by
    show TWkRel (P.wk (s.wk h).2.1).2.1 _ (TRun.seq s.trunR P.trunR τ)
      (TRun.seq (s.wk h).2.2.trunR (P.wk (s.wk h).2.1).2.2.trunR (τ.lift h d))
    exact TWkRel.seq (Stmt.trun_wk s h τ d) fun a d' => Prog.trun_wk P _ a d'

end

end Solidity.Core
