import Solidity.Calculus.CondLift

/-!
# Fallbacks lifted out of equations (M7, step 6)

An element read as the Theory reads it (`Calculus/TheoryRead.lean`) is
`orElse(find(S, q[i]), 0)`: the read, or the default where nothing is
there.  The arithmetic stages take no `orElse`.  `LFml.orLift` lifts each
out of its equation as `LFml.liftCond` lifts a conditional: an equation
`A[orElse(a, b)]` holds iff `a` returns and `A[a]` holds, or `a` halts and
`A[b]` holds (`OrSplit.cases`).  This is exact in every context, since
`LTm.eval` is compositional (`LTm.orSplit_eval`, `LFml.orLift_holds`).
-/

namespace Solidity.Decide

variable {C : Contract}

/-- A term read as one fallback: its value is `val`'s where `test` returns,
`alt`'s where it halts. -/
structure OrSplit (C : Contract) (s : Srt) where
  {q : PrimTy}
  test : LTm C (.val q)
  val : LTm C s
  alt : LTm C s

namespace OrSplit

/-- The value the split selects. -/
noncomputable def Eval {s : Srt} (r : OrSplit C s) (g : State C []) (ν : AEnv) :
    Option (s.Den C g.H) :=
  match (r.test.eval g ν : Option r.q.Denote) with
  | some _ => r.val.eval g ν
  | none => r.alt.eval g ν

/-- The same split under a context. -/
def map {s u : Srt} (f : LTm C s → LTm C u) (r : OrSplit C s) : OrSplit C u :=
  ⟨r.test, f r.val, f r.alt⟩

theorem eval_map {s u : Srt} (g : State C []) (ν : AEnv) (f : LTm C s → LTm C u)
    (F : Option (s.Den C g.H) → Option (u.Den C g.H))
    (hf : ∀ t : LTm C s, (f t).eval g ν = F (t.eval g ν)) (r : OrSplit C s) :
    (r.map f).Eval g ν = F (r.Eval g ν) := by
  unfold Eval map
  cases (r.test.eval g ν : Option r.q.Denote) with
  | none => exact hf r.alt
  | some _ => exact hf r.val

/-- The first of two: the left one's under its context, else the right one. -/
def first {s a : Srt} (ix : Option (OrSplit C a)) (iy : Option (OrSplit C s))
    (fx : LTm C a → LTm C s) : Option (OrSplit C s) :=
  match ix with
  | some r => some (r.map fx)
  | none => iy

/-- A split under a context. -/
def lift {s a : Srt} (iy : Option (OrSplit C a)) (fy : LTm C a → LTm C s) : Option (OrSplit C s) :=
  iy.map (·.map fy)

/-- An `orElse` at a value: the split it is. -/
def here : {s : Srt} → LTm C s → LTm C s → Option (OrSplit C s)
  | .val _, a, b => some ⟨a, a, b⟩
  | _, _, _ => none

end OrSplit

/-- **The first fallback of a term** at a value, in pre-order, with the term
it leaves in each case. -/
def LTm.orSplit : {s : Srt} → LTm C s → Option (OrSplit C s)
  | _, .var _ => none
  | _, .app0 _ => none
  | _, .err => none
  | _, .app1 o x => OrSplit.lift x.orSplit (.app1 o)
  | _, .app2 o x y => OrSplit.first x.orSplit (OrSplit.lift y.orSplit (.app2 o x ·)) (.app2 o · y)
  | _, .app3 o x y z => OrSplit.first x.orSplit
      (OrSplit.first y.orSplit (OrSplit.lift z.orSplit (.app3 o x y ·)) (.app3 o x · z)) (.app3 o · y z)
  | _, .index it q i =>
    OrSplit.first q.orSplit (OrSplit.lift i.orSplit (.index it q ·)) (.index it · i)
  | _, .obsW q => OrSplit.lift q.orSplit .obsW
  | _, .obsL q => OrSplit.lift q.orSplit .obsL
  | _, .obsH q => OrSplit.lift q.orSplit .obsH
  | _, .seq d a => OrSplit.first d.orSplit (OrSplit.lift a.orSplit (.seq d ·)) (.seq · a)
  | _, .orElse a b => OrSplit.here a b
  | _, .kite a b t e => OrSplit.first a.orSplit (OrSplit.first b.orSplit
      (OrSplit.first t.orSplit (OrSplit.lift e.orSplit (.kite a b t ·)) (.kite a b · e))
      (.kite a · t e)) (.kite · b t e)

section Eval

variable (g : State C []) (ν : AEnv)

theorem OrSplit.lift_eval {s a : Srt} {y : LTm C a} {w : LTm C s} (iy : Option (OrSplit C a))
    (fy : LTm C a → LTm C s) (Fy : Option (a.Den C g.H) → Option (s.Den C g.H))
    (hfy : ∀ t, (fy t).eval g ν = Fy (t.eval g ν))
    (hy : ∀ r, iy = some r → y.eval g ν = r.Eval g ν) (hw : w.eval g ν = Fy (y.eval g ν)) :
    ∀ r, OrSplit.lift iy fy = some r → w.eval g ν = r.Eval g ν := by
  intro r hr
  cases hiy : iy with
  | none => rw [hiy] at hr; cases hr
  | some r' =>
    rw [hiy] at hr
    cases hr
    rw [OrSplit.eval_map g ν fy Fy hfy, ← hy r' hiy, hw]

theorem OrSplit.first_eval {s a : Srt} {x : LTm C a} {w : LTm C s} (ix : Option (OrSplit C a))
    (iy : Option (OrSplit C s)) (fx : LTm C a → LTm C s)
    (Fx : Option (a.Den C g.H) → Option (s.Den C g.H))
    (hfx : ∀ t, (fx t).eval g ν = Fx (t.eval g ν))
    (hx : ∀ r, ix = some r → x.eval g ν = r.Eval g ν)
    (hy : ∀ r, iy = some r → w.eval g ν = r.Eval g ν) (hw : w.eval g ν = Fx (x.eval g ν)) :
    ∀ r, OrSplit.first ix iy fx = some r → w.eval g ν = r.Eval g ν := by
  intro r hr
  cases hix : ix with
  | some r' =>
    rw [hix] at hr
    cases hr
    rw [OrSplit.eval_map g ν fx Fx hfx, ← hx r' hix, hw]
  | none =>
    rw [hix] at hr
    exact hy r hr

/-- **A term reads what its split selects.** -/
theorem LTm.orSplit_eval {s : Srt} (t : LTm C s) :
    ∀ r, t.orSplit = some r → t.eval g ν = r.Eval g ν := by
  induction t with
  | var | app0 | err => intro r h; cases h
  | app1 o x ih =>
    exact OrSplit.lift_eval g ν _ _ (o.eval g) (fun _ => rfl) ih rfl
  | app2 o x y ihx ihy =>
    exact OrSplit.first_eval g ν _ _ _ (fun u => o.eval g u (y.eval g ν)) (fun _ => rfl) ihx
      (OrSplit.lift_eval g ν _ _ (o.eval g (x.eval g ν)) (fun _ => rfl) ihy rfl) rfl
  | app3 o x y z ihx ihy ihz =>
    exact OrSplit.first_eval g ν _ _ _ (fun u => o.eval g u (y.eval g ν) (z.eval g ν))
      (fun _ => rfl) ihx
      (OrSplit.first_eval g ν _ _ _ (fun u => o.eval g (x.eval g ν) u (z.eval g ν)) (fun _ => rfl)
        ihy (OrSplit.lift_eval g ν _ _ (o.eval g (x.eval g ν) (y.eval g ν)) (fun _ => rfl) ihz rfl)
        rfl) rfl
  | index it q i ihq ihi =>
    exact OrSplit.first_eval g ν _ _ _
      (fun u => u.bind fun r => (i.eval g ν).bind fun j => some (r.index it j)) (fun _ => rfl) ihq
      (OrSplit.lift_eval g ν _ _ (fun u => (q.eval g ν).bind fun r => u.bind fun j =>
        some (r.index it j)) (fun _ => rfl) ihi rfl) rfl
  | obsW q ih =>
    exact OrSplit.lift_eval g ν _ _ (fun u => u.bind fun r => some (g.storage.obs.word (.ref r)))
      (fun _ => rfl) ih rfl
  | obsL q ih =>
    exact OrSplit.lift_eval g ν _ _
      (fun u => u.bind fun r => some (uintOfNat (g.storage.obs.len (.ref r)))) (fun _ => rfl) ih rfl
  | obsH q ih =>
    exact OrSplit.lift_eval g ν _ _ (fun u => u.bind fun r => some (g.storage.obs.has (.ref r)))
      (fun _ => rfl) ih rfl
  | seq d a ihd iha =>
    exact OrSplit.first_eval g ν _ _ _ (fun u => u.bind fun _ => a.eval g ν) (fun _ => rfl) ihd
      (OrSplit.lift_eval g ν _ _ (fun u => (d.eval g ν).bind fun _ => u) (fun _ => rfl) iha rfl) rfl
  | @orElse s a b _ _ =>
    intro r h
    cases s with
    | val p =>
      cases h
      show (a.eval g ν).or (b.eval g ν) = OrSplit.Eval ⟨a, a, b⟩ g ν
      unfold OrSplit.Eval
      cases (a.eval g ν : Option p.Denote) <;> rfl
    | _ => cases h
  | kite a b t e iha ihb iht ihe =>
    exact OrSplit.first_eval g ν _ _ _
      (fun u => u.bind fun x => (b.eval g ν).bind fun y => if x = y then t.eval g ν else e.eval g ν)
      (fun _ => rfl) iha
      (OrSplit.first_eval g ν _ _ _
        (fun u => (a.eval g ν).bind fun x => u.bind fun y => if x = y then t.eval g ν else e.eval g ν)
        (fun _ => rfl) ihb
        (OrSplit.first_eval g ν _ _ _
          (fun u => (a.eval g ν).bind fun x => (b.eval g ν).bind fun y =>
            if x = y then u else e.eval g ν) (fun _ => rfl) iht
          (OrSplit.lift_eval g ν _ _
            (fun u => (a.eval g ν).bind fun x => (b.eval g ν).bind fun y =>
              if x = y then t.eval g ν else u) (fun _ => rfl) ihe rfl) rfl) rfl) rfl

end Eval

/-! ## Lifting -/

/-- The two cases of a split: `P` where its test returns, `Q` where it
halts. -/
def OrSplit.cases {s : Srt} (r : OrSplit C s) (P Q : LFml C) : LFml C :=
  .and (.imp (.eq r.test r.test) P) (.imp (.not (.eq r.test r.test)) Q)

theorem OrSplit.cases_holds (g : State C []) (ν : AEnv) {s : Srt} (r : OrSplit C s) (P Q : LFml C) :
    (r.cases P Q).holds g ν ↔ match (r.test.eval g ν : Option r.q.Denote) with
      | some _ => P.holds g ν
      | none => Q.holds g ν := by
  show ((LFml.eq r.test r.test).holds g ν → P.holds g ν) ∧
    (¬ (LFml.eq r.test r.test).holds g ν → Q.holds g ν) ↔ _
  rw [LFml.holds_rets]
  cases (r.test.eval g ν : Option r.q.Denote) with
  | none => simp only [reduceCtorEq, exists_false, false_implies, not_false_eq_true, true_implies,
      true_and]
  | some v => simp only [Option.some.injEq, exists_eq', true_implies, not_true_eq_false,
      false_implies, and_true]

/-- One equation: its first fallback (left side first) lifted, the cases
continued by `k`. -/
def LFml.orEq (k : LFml C → LFml C) {p : PrimTy} (a b : LTm C (.val p)) : LFml C :=
  match a.orSplit with
  | some r => k (r.cases (.eq r.val b) (.eq r.alt b))
  | none =>
    match b.orSplit with
    | some r => k (r.cases (.eq a r.val) (.eq a r.alt))
    | none => .eq a b

/-- **Fallbacks lifted** out of every equation, to the nesting depth
`fuel`. -/
def LFml.orLift : Nat → LFml C → LFml C
  | 0, φ => φ
  | n + 1, φ => φ.mapEq (LFml.orEq (LFml.orLift n))

/-- **Lifting is exact.** -/
theorem LFml.orLift_holds (g : State C []) :
    ∀ (n : Nat) (φ : LFml C) (ν : AEnv), (φ.orLift n).holds g ν ↔ φ.holds g ν
  | 0, _, _ => Iff.rfl
  | n + 1, φ, ν => by
    apply LFml.mapEq_holds g _ _ φ ν
    intro ν p a b
    unfold LFml.orEq
    cases ha : a.orSplit with
    | some r =>
      refine (LFml.orLift_holds g n _ ν).trans ?_
      rw [OrSplit.cases_holds]
      have e := LTm.orSplit_eval g ν a r ha
      unfold OrSplit.Eval at e
      split
      · rename_i v hv; rw [hv] at e; rw [LFml.holds_eq_iff, LFml.holds_eq_iff, e]
      · rename_i hv; rw [hv] at e; rw [LFml.holds_eq_iff, LFml.holds_eq_iff, e]
    | none =>
      cases hb : b.orSplit with
      | some r =>
        refine (LFml.orLift_holds g n _ ν).trans ?_
        rw [OrSplit.cases_holds]
        have e := LTm.orSplit_eval g ν b r hb
        unfold OrSplit.Eval at e
        split
        · rename_i v hv; rw [hv] at e; rw [LFml.holds_eq_iff, LFml.holds_eq_iff, e]
        · rename_i hv; rw [hv] at e; rw [LFml.holds_eq_iff, LFml.holds_eq_iff, e]
      | none => exact Iff.rfl

/-- The fallbacks of a term. -/
def LTm.ors : {s : Srt} → LTm C s → Nat
  | _, .var _ | _, .app0 _ | _, .err => 0
  | _, .app1 _ a | _, .obsW a | _, .obsL a | _, .obsH a => a.ors
  | _, .app2 _ a b | _, .index _ a b | _, .seq a b => a.ors + b.ors
  | _, .orElse a b => a.ors + b.ors + 1
  | _, .app3 _ a b c => a.ors + b.ors + c.ors
  | _, .kite a b t e => a.ors + b.ors + t.ors + e.ors

/-- The fallbacks of a formula. -/
def LFml.ors : LFml C → Nat
  | .tt => 0
  | .eq a b => a.ors + b.ors
  | .not φ | .all _ _ φ => φ.ors
  | .and φ ψ | .imp φ ψ => φ.ors + ψ.ors

end Solidity.Decide
