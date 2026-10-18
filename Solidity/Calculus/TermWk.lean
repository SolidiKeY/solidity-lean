import Solidity.Calculus.Lands

/-!
# Terms read with more locals around them

`Tm.wk` reads a term in a context with more locals (`Thin`), and what it
reads there, by the interpreter (`Tm.eval_wk`) and in the Theory
(`Tm.denote_wk`), is what it read in the thinned state.  A lowered program
value weakens as its term does (`Val.lower_wk`), so a rule's formula over a
value read under a fresh local (`Val.up`) reads as the formula without it
(`Val.lower_denote_up`).
-/

namespace Solidity

open Solidity (Srt)

variable {C : Contract}

section Wk

/-- A term read with more locals around it (`Thin`). -/
def Tm.wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {s : Srt} → Tm C Γ s → Tm C Δ s
  | _, t => Tm.casesOn (motive := fun s _ => Tm C Δ s) t
    (pvV := fun i => .pvV (i.wk h)) (pvP := fun i => .pvP (i.wk h))
    (pvS := fun i => .pvS (i.wk h)) (pvI := fun i => .pvI (i.wk h))
    (netOf := fun i a => .netOf (i.wk h) (Tm.wk h a)) (app0 := fun o => .app0 o)
    (app1 := fun o a => .app1 o (Tm.wk h a))
    (app2 := fun o a b => .app2 o (Tm.wk h a) (Tm.wk h b))
    (app3 := fun o a b c => .app3 o (Tm.wk h a) (Tm.wk h b) (Tm.wk h c))
    (pvZ := fun i => .pvZ (i.wk h))
  termination_by structural _ t => t

/-! `Tm.wk`'s equations, one a constructor: its own equation unfolds to
the `casesOn`, which `simp` would unfold again inside it. -/

section WkEqns

variable {Γ Δ : Ctx} (h : Thin Γ Δ)

theorem Tm.wk_pvV {p : PrimTy} (i : Idx Γ (.val p)) : (Tm.pvV (C := C) i).wk h = .pvV (i.wk h) :=
  rfl
theorem Tm.wk_pvP {R : RefTy} (i : Idx Γ (.alias R)) :
    (Tm.pvP (C := C) i).wk h = .pvP (i.wk h) := rfl
theorem Tm.wk_pvS (i : Idx Γ .old) : (Tm.pvS (C := C) i).wk h = .pvS (i.wk h) := rfl
theorem Tm.wk_pvI {R : RefTy} (i : Idx Γ (.mem R)) :
    (Tm.pvI (C := C) i).wk h = .pvI (i.wk h) := rfl
theorem Tm.wk_netOf (i : Idx Γ .oldNet) (a : Tm C Γ (.val .uint)) :
    (Tm.netOf i a).wk h = .netOf (i.wk h) (a.wk h) := rfl
theorem Tm.wk_app0 {s : Srt} (o : Op0 C s) : (Tm.app0 (C := C) (Γ := Γ) o).wk h = .app0 o := rfl
theorem Tm.wk_app1 {a s : Srt} (o : Op1 C a s) (x : Tm C Γ a) :
    (Tm.app1 o x).wk h = .app1 o (x.wk h) := rfl
theorem Tm.wk_app2 {a b s : Srt} (o : Op2 C a b s) (x : Tm C Γ a) (y : Tm C Γ b) :
    (Tm.app2 o x y).wk h = .app2 o (x.wk h) (y.wk h) := rfl
theorem Tm.wk_app3 {a b c s : Srt} (o : Op3 C a b c s) (x : Tm C Γ a) (y : Tm C Γ b)
    (z : Tm C Γ c) : (Tm.app3 o x y z).wk h = .app3 o (x.wk h) (y.wk h) (z.wk h) := rfl
theorem Tm.wk_pvZ (i : Idx Γ .kint) : (Tm.pvZ (C := C) i).wk h = .pvZ (i.wk h) := rfl

end WkEqns

theorem Tm.eval_wk {Γ Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) :
    {s : Srt} → (t : Tm C Γ s) → (t.wk h).eval σ = t.eval (σ.thin h)
  | _, .pvV i => by
    show some (TEnv.get (i.wk h) σ.env) = some (TEnv.get i (TEnv.thin h σ.env))
    rw [TEnv.get_thin_wk]
  | _, .pvP i => by
    show TEnv.get (i.wk h) σ.env = TEnv.get i (TEnv.thin h σ.env)
    rw [TEnv.get_thin_wk]
  | _, .pvS i => by
    show some (TEnv.get (i.wk h) σ.env) = some (TEnv.get i (TEnv.thin h σ.env))
    rw [TEnv.get_thin_wk]
  | _, .pvI i => by
    show (TEnv.get (i.wk h) σ.env).map (·.id) = (TEnv.get i (TEnv.thin h σ.env)).map (·.id)
    rw [TEnv.get_thin_wk]
  | _, .netOf i a => by
    show ((a.wk h).eval σ).bind _ = (a.eval (σ.thin h)).bind (Tm.netOfT (TEnv.get i (TEnv.thin h σ.env)))
    rw [Tm.eval_wk h σ a, TEnv.get_thin_wk]
  | _, .app0 o => rfl
  | _, .app1 o a => by
    show o.eval σ.glob ((a.wk h).eval σ) = o.eval σ.glob (a.eval (σ.thin h))
    rw [Tm.eval_wk h σ a]
  | _, .app2 o a b => by
    show o.eval σ.glob ((a.wk h).eval σ) ((b.wk h).eval σ) =
      o.eval σ.glob (a.eval (σ.thin h)) (b.eval (σ.thin h))
    rw [Tm.eval_wk h σ a, Tm.eval_wk h σ b]
  | _, .app3 o a b c => by
    show o.eval σ.glob ((a.wk h).eval σ) ((b.wk h).eval σ) ((c.wk h).eval σ) =
      o.eval σ.glob (a.eval (σ.thin h)) (b.eval (σ.thin h)) (c.eval (σ.thin h))
    rw [Tm.eval_wk h σ a, Tm.eval_wk h σ b, Tm.eval_wk h σ c]
  | _, .pvZ i => by
    show some (TEnv.get (i.wk h) σ.env) = some (TEnv.get i (TEnv.thin h σ.env))
    rw [TEnv.get_thin_wk]

theorem Tm.denote_wk {Γ Δ : Ctx} (h : Thin Γ Δ) (σ : State C Δ) :
    {s : Srt} → (t : Tm C Γ s) → (t.wk h).denote σ = t.denote (σ.thin h)
  | _, .pvV i => by simp only [Tm.wk_pvV, Tm.denote, State.thin, State.withEnv, TEnv.get_thin_wk]
  | _, .pvP i => by simp only [Tm.wk_pvP, Tm.denote, State.thin, State.withEnv, TEnv.get_thin_wk]; split <;> rfl
  | _, .pvS i => by simp only [Tm.wk_pvS, Tm.denote, State.thin, State.withEnv, TEnv.get_thin_wk]
  | _, .pvI i => rfl
  | _, .netOf i a => by
    simp only [Tm.wk_netOf, Tm.denote, Tm.denote_wk h σ a, State.thin, State.withEnv,
      TEnv.get_thin_wk]
  | _, .app0 o => rfl
  | _, .app1 o a => by
    show o.denote σ.glob ((a.wk h).denote σ) = o.denote σ.glob (a.denote (σ.thin h))
    rw [Tm.denote_wk h σ a]
  | _, .app2 o a b => by
    show o.denote σ.glob ((a.wk h).eval σ) ((b.wk h).eval σ) ((a.wk h).denote σ) ((b.wk h).denote σ) =
      o.denote σ.glob (a.eval (σ.thin h)) (b.eval (σ.thin h)) (a.denote (σ.thin h))
        (b.denote (σ.thin h))
    rw [Tm.denote_wk h σ a, Tm.denote_wk h σ b, Tm.eval_wk h σ a, Tm.eval_wk h σ b]
  | _, .app3 o a b c => by
    show o.denote ((a.wk h).denote σ) ((b.wk h).denote σ) ((c.wk h).denote σ) =
      o.denote (a.denote (σ.thin h)) (b.denote (σ.thin h)) (c.denote (σ.thin h))
    rw [Tm.denote_wk h σ a, Tm.denote_wk h σ b, Tm.denote_wk h σ c]
  | _, .pvZ i => by simp only [Tm.wk_pvZ, Tm.denote, State.thin, State.withEnv, TEnv.get_thin_wk]

/-! ## Lowered values, weakened -/

theorem Tm.castV_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {p q : PrimTy} (e : p = q) (t : Tm C Γ (.val p)) :
    (Tm.castV e t).wk h = Tm.castV e (t.wk h) := by
  subst e; rfl

theorem Simple.lower_wk {Γ Δ : Ctx} (h : Thin Γ Δ) {p : PrimTy} :
    (s : Simple C Γ p) → (s.wk h).lower = s.lower.wk h
  | .lit _ _ => rfl
  | .bool _ => rfl
  | .local _ => rfl
  | .env _ hp => by simp only [Simple.wk, Simple.lower, Tm.castV_wk, Tm.wk_app0]

mutual

theorem SPath.lower_wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {T : Ty} → (b : SPath C Γ T) →
    (b.wk h).lower = b.lower.wk h
  | _, .alias _ => rfl
  | _, .loc l => Loc.lower_wk h l

theorem Loc.lower_wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {T : Ty} → (l : Loc C Γ T) →
    (l.wk h).lower = l.lower.wk h
  | _, .root _ _ => rfl
  | _, .field b _ _ => by
    simp only [Loc.wk, Loc.lower, SPath.lower_wk h b, Tm.wk_app1]
  | _, .index _ b i => by
    simp only [Loc.wk, Loc.lower, SPath.lower_wk h b, Val.lower_wk h i, Tm.wk_app2]

theorem MPath.lower_wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {T : Ty} → (b : MPath C Γ T) →
    (b.wk h).lower = b.lower.wk h
  | _, .var _ _ => rfl
  | T, .loc l => by
    simp only [MPath.wk, MPath.lower, MLoc.lower_wk h l]
    cases T <;> rfl

theorem MLoc.lower_wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {T : Ty} → (l : MLoc C Γ T) →
    (l.wk h).lower = l.lower.wk h
  | _, .field b _ _ => by
    simp only [MLoc.wk, MLoc.lower, MPath.lower_wk h b, Tm.wk_app1]
  | _, .index _ b i => by
    simp only [MLoc.wk, MLoc.lower, MPath.lower_wk h b, Val.lower_wk h i, Tm.wk_app2]

theorem Val.lower_wk {Γ Δ : Ctx} (h : Thin Γ Δ) : {p : PrimTy} → (v : Val C Γ p) →
    (v.wk h).lower = v.lower.wk h
  | _, .simple s => Simple.lower_wk h s
  | _, .read l => by
    simp only [Val.wk, Val.lower, Loc.lower_wk h l, Tm.wk_app2, Tm.wk_app0]
  | _, .binop _ _ hq a b => by
    simp only [Val.wk, Val.lower, Val.lower_wk h a, Val.lower_wk h b, Tm.castV_wk, Tm.wk_app2]
  | _, .unop _ _ hq a => by
    simp only [Val.wk, Val.lower, Val.lower_wk h a, Tm.castV_wk, Tm.wk_app1]
  | _, .ternary c a b => by
    simp only [Val.wk, Val.lower, Val.lower_wk h c, Val.lower_wk h a, Val.lower_wk h b,
      Tm.wk_app3]
  | _, .readMem l => by
    simp only [Val.wk, Val.lower, MLoc.lower_wk h l, Tm.wk_app2, Tm.wk_app0]
  | _, .len b hp => by
    simp only [Val.wk, Val.lower, SPath.lower_wk h b, Tm.castV_wk, Tm.wk_app2, Tm.wk_app0]
  | _, .mlen b hp => by
    simp only [Val.wk, Val.lower, MPath.lower_wk h b, Tm.castV_wk, Tm.wk_app2, Tm.wk_app0]
  | _, .modular _ a b k => by
    simp only [Val.wk, Val.lower, Val.lower_wk h a, Val.lower_wk h b, Val.lower_wk h k,
      Tm.wk_app3]

end

/-- A value read under a fresh local reads, in the Theory, as it did
without it. -/
theorem Val.lower_denote_up {Γ : Ctx} {t : LTy} {p : PrimTy} (v : Val C Γ p) (σ : State C Γ)
    (w : t.TDenote C σ.H) : (v.up (t := t)).lower.denote (σ.push w) = v.lower.denote σ := by
  rw [Val.up_eq, Val.lower_wk, Tm.denote_wk]
  rfl

end Wk

end Solidity
