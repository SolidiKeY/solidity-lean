import Solidity.Calculus.Decide

/-!
# Conditionals lifted out of equations

The elimination (`LTm.elim`, `Calculus/Decide.lean`) answers a read after a
write at a symbolic key with a conditional term: `kite x y t e` (`t` where
the keys `x` and `y` are equal, `e` where they differ) and `ite c t e` (the
`has` test of a location).  The checked arithmetic compiler
(`Calculus/CheckedLinear.lean`) reads affine values only, so it refuses
them.  This module lifts each conditional out of the equation it sits in
into a case split of the formula, which the compiler reads.

**Why a case split, and not a compiler case.**  A conditional value is not
affine in its inputs, so `CheckedScalar` cannot encode it; a compiler case
would have to return a disjunction of encodings, which is the case split
done inside the compiler.  Lifting at the formula level keeps the compiler
as it is, and keeps the lifted formula in the language every later stage
(flattening, alias constraints, arithmetic) already reads.

**Definedness.**  The split is by the guard's three outcomes, not two: an
equation `A[K]` with `K := kite x y t e` holds iff

* `x`, `y` return and are equal, and `A[t]` holds; or
* `x`, `y` return and differ, and `A[e]` holds; or
* one of them halts, and `A[err]` holds,

since `A`'s value depends on `K` only through `K`'s value (`LTm.eval` is
compositional), so this holds in every context, strict or not (`seq`,
`orElse`, a short-circuit `&&`).  `ite c t e` splits the same way on `c`.
The first conditional in pre-order is lifted; the guard's own equations are
lifted again, so every conditional goes.  The fuel bounds the nesting depth;
when it runs out a formula is kept as it is, which is still equivalent, and
the compiler refuses what is left.

`LTm.condSplit` is kernel-evaluated (inside `dependentReduction?`), so it
is written with the recursor, with a `match` twin and a link theorem
(Gate G0, `docs/intrinsic.md`).
-/

namespace Solidity.Decide

variable {C : Contract}

/-- The test of a lifted conditional: two words compared, or a Boolean. -/
inductive CondGuard (C : Contract) where
  | kite {p : PrimTy} (x y : LTm C (.val p))
  | ite (c : LTm C (.val .bool))

/-- The guard's outcome: `none` where its operands halt. -/
noncomputable def CondGuard.case (g : State C []) (ν : AEnv) : CondGuard C → Option Bool
  | @CondGuard.kite _ p x y =>
    (x.eval g ν : Option p.Denote).bind fun a =>
      (y.eval g ν : Option p.Denote).bind fun b => some (if a = b then true else false)
  | .ite c => (c.eval g ν : Option Bool)

/-- A term read as one conditional: its value is `thn`'s, `els`'s or `bad`'s,
as the guard holds, fails or halts. -/
structure CondSplit (C : Contract) (s : Srt) where
  guard : CondGuard C
  thn : LTm C s
  els : LTm C s
  bad : LTm C s

namespace CondSplit

/-- The value the split selects. -/
noncomputable def Eval {s : Srt} (r : CondSplit C s) (g : State C []) (ν : AEnv) :
    Option (s.Den C g.H) :=
  match r.guard.case g ν with
  | some true => r.thn.eval g ν
  | some false => r.els.eval g ν
  | none => r.bad.eval g ν

/-- The same split under a context. -/
def map {s u : Srt} (f : LTm C s → LTm C u) (r : CondSplit C s) : CondSplit C u :=
  ⟨r.guard, f r.thn, f r.els, f r.bad⟩

theorem eval_map {s u : Srt} (g : State C []) (ν : AEnv) (f : LTm C s → LTm C u)
    (F : Option (s.Den C g.H) → Option (u.Den C g.H))
    (hf : ∀ t : LTm C s, (f t).eval g ν = F (t.eval g ν)) (r : CondSplit C s) :
    (r.map f).Eval g ν = F (r.Eval g ν) := by
  unfold Eval map
  cases r.guard.case g ν with
  | none => exact hf r.bad
  | some b => cases b
              · exact hf r.els
              · exact hf r.thn

end CondSplit

/-- The first of two operands' conditionals. -/
def CondSplit.first {s a b : Srt} (ix : Option (CondSplit C a)) (iy : Option (CondSplit C b))
    (fx : LTm C a → LTm C s) (fy : LTm C b → LTm C s) : Option (CondSplit C s) :=
  match ix with
  | some r => some (r.map fx)
  | none => iy.map (·.map fy)

/-- The first of three operands' conditionals. -/
def CondSplit.first3 {s a b c : Srt} (ix : Option (CondSplit C a)) (iy : Option (CondSplit C b))
    (iz : Option (CondSplit C c)) (fx : LTm C a → LTm C s) (fy : LTm C b → LTm C s)
    (fz : LTm C c → LTm C s) : Option (CondSplit C s) :=
  match ix with
  | some r => some (r.map fx)
  | none => CondSplit.first iy iz fy fz

/-- The first conditional of an `app3`: the operator's own, if it is `ite`,
else the first of its operands'. -/
def LTm.app3Split : {a b c s : Srt} → (o : Op3 C a b c s) → (x : LTm C a) → (y : LTm C b) →
    (z : LTm C c) → Option (CondSplit C a) → Option (CondSplit C b) →
    Option (CondSplit C c) → Option (CondSplit C s)
  | _, _, _, _, .ite, x, y, z, _, _, _ => some ⟨.ite x, y, z, .err⟩
  | _, _, _, _, o, x, y, z, ix, iy, iz =>
    CondSplit.first3 ix iy iz (LTm.app3 o · y z) (LTm.app3 o x · z) (LTm.app3 o x y ·)

/-- The compiled twin of `LTm.condSplit`. -/
def LTm.condSplitM : {s : Srt} → LTm C s → Option (CondSplit C s)
  | _, .var _ | _, .app0 _ | _, .err => none
  | _, .app1 o x => x.condSplitM.map (·.map (LTm.app1 o))
  | _, .app2 o x y => CondSplit.first x.condSplitM y.condSplitM (LTm.app2 o · y) (LTm.app2 o x ·)
  | _, .app3 o x y z => LTm.app3Split o x y z x.condSplitM y.condSplitM z.condSplitM
  | _, .index it q i =>
    CondSplit.first q.condSplitM i.condSplitM (LTm.index it · i) (LTm.index it q ·)
  | _, .obsW q => q.condSplitM.map (·.map LTm.obsW)
  | _, .obsL q => q.condSplitM.map (·.map LTm.obsL)
  | _, .obsH q => q.condSplitM.map (·.map LTm.obsH)
  | _, .seq d a => CondSplit.first d.condSplitM a.condSplitM (LTm.seq · a) (LTm.seq d ·)
  | _, .orElse a b => CondSplit.first a.condSplitM b.condSplitM (LTm.orElse · b) (LTm.orElse a ·)
  | _, .kite a b t e => some ⟨.kite a b, t, e, .err⟩

/-- **The first conditional** of a term, in pre-order, with the term it
leaves in each case. -/
@[implemented_by LTm.condSplitM]
def LTm.condSplit {s : Srt} (t : LTm C s) : Option (CondSplit C s) :=
  @LTm.rec C (fun s _ => Option (CondSplit C s))
    (fun _ => none)
    (fun _ => none)
    (fun o _ ix => ix.map (·.map (LTm.app1 o)))
    (fun o x y ix iy => CondSplit.first ix iy (LTm.app2 o · y) (LTm.app2 o x ·))
    (fun o x y z ix iy iz => LTm.app3Split o x y z ix iy iz)
    (fun it q i iq ii => CondSplit.first iq ii (LTm.index it · i) (LTm.index it q ·))
    (fun _ iq => iq.map (·.map LTm.obsW))
    (fun _ iq => iq.map (·.map LTm.obsL))
    (fun _ iq => iq.map (·.map LTm.obsH))
    (fun d a id ia => CondSplit.first id ia (LTm.seq · a) (LTm.seq d ·))
    (fun a b ia ib => CondSplit.first ia ib (LTm.orElse · b) (LTm.orElse a ·))
    (fun a b t e _ _ _ _ => some ⟨.kite a b, t, e, .err⟩)
    none s t

theorem LTm.condSplit_eq_condSplitM {s : Srt} (t : LTm C s) : t.condSplit = t.condSplitM := by
  induction t with
  | var | app0 | err | kite => rfl
  | app1 o x ih => simp only [LTm.condSplitM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [LTm.condSplitM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [LTm.condSplitM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => simp only [LTm.condSplitM, ← ihq, ← ihi]; rfl
  | obsW q ih | obsL q ih | obsH q ih => simp only [LTm.condSplitM, ← ih]; rfl
  | seq d a ihd iha => simp only [LTm.condSplitM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => simp only [LTm.condSplitM, ← iha, ← ihb]; rfl

section Eval

variable (g : State C []) (ν : AEnv)

theorem CondSplit.first_eval {s a b : Srt} {x : LTm C a} {y : LTm C b}
    (ix : Option (CondSplit C a)) (iy : Option (CondSplit C b))
    (fx : LTm C a → LTm C s) (fy : LTm C b → LTm C s)
    (Fx : Option (a.Den C g.H) → Option (s.Den C g.H))
    (Fy : Option (b.Den C g.H) → Option (s.Den C g.H))
    (hfx : ∀ t, (fx t).eval g ν = Fx (t.eval g ν)) (hfy : ∀ t, (fy t).eval g ν = Fy (t.eval g ν))
    (hx : ∀ r, ix = some r → x.eval g ν = r.Eval g ν)
    (hy : ∀ r, iy = some r → y.eval g ν = r.Eval g ν)
    (h0 : Fx (x.eval g ν) = Fy (y.eval g ν)) {w : LTm C s} (hw : w.eval g ν = Fx (x.eval g ν)) :
    ∀ r, CondSplit.first ix iy fx fy = some r → w.eval g ν = r.Eval g ν := by
  intro r hr
  cases hix : ix with
  | some r' =>
    rw [hix] at hr
    cases hr
    rw [CondSplit.eval_map g ν fx Fx hfx, ← hx r' hix, hw]
  | none =>
    rw [hix] at hr
    cases hiy : iy with
    | none => rw [hiy] at hr; cases hr
    | some r' =>
      rw [hiy] at hr
      cases hr
      rw [CondSplit.eval_map g ν fy Fy hfy, ← hy r' hiy, hw, h0]

theorem CondSplit.first3_eval {s a b c : Srt} {x : LTm C a} {y : LTm C b} {z : LTm C c}
    (ix : Option (CondSplit C a)) (iy : Option (CondSplit C b)) (iz : Option (CondSplit C c))
    (fx : LTm C a → LTm C s) (fy : LTm C b → LTm C s) (fz : LTm C c → LTm C s)
    (Fx : Option (a.Den C g.H) → Option (s.Den C g.H))
    (Fy : Option (b.Den C g.H) → Option (s.Den C g.H))
    (Fz : Option (c.Den C g.H) → Option (s.Den C g.H))
    (hfx : ∀ t, (fx t).eval g ν = Fx (t.eval g ν)) (hfy : ∀ t, (fy t).eval g ν = Fy (t.eval g ν))
    (hfz : ∀ t, (fz t).eval g ν = Fz (t.eval g ν))
    (hx : ∀ r, ix = some r → x.eval g ν = r.Eval g ν)
    (hy : ∀ r, iy = some r → y.eval g ν = r.Eval g ν)
    (hz : ∀ r, iz = some r → z.eval g ν = r.Eval g ν)
    (h0 : Fx (x.eval g ν) = Fy (y.eval g ν)) (h1 : Fy (y.eval g ν) = Fz (z.eval g ν))
    {w : LTm C s} (hw : w.eval g ν = Fx (x.eval g ν)) :
    ∀ r, CondSplit.first3 ix iy iz fx fy fz = some r → w.eval g ν = r.Eval g ν := by
  intro r hr
  cases hix : ix with
  | some r' =>
    rw [hix] at hr
    cases hr
    rw [CondSplit.eval_map g ν fx Fx hfx, ← hx r' hix, hw]
  | none =>
    rw [hix] at hr
    exact CondSplit.first_eval g ν iy iz fy fz Fy Fz hfy hfz hy hz h1 (hw.trans h0) r hr

theorem CondSplit.eval_eq {s : Srt} (r : CondSplit C s) :
    r.Eval g ν = match r.guard.case g ν with
      | some true => r.thn.eval g ν
      | some false => r.els.eval g ν
      | none => r.bad.eval g ν := rfl

theorem CondSplit.eval_ite {p : PrimTy} (c : LTm C (.val .bool)) (t e : LTm C (.val p)) :
    (⟨.ite c, t, e, .err⟩ : CondSplit C (.val p)).Eval g ν =
      (c.eval g ν : Option Bool).bind (fun b => cond b (t.eval g ν) (e.eval g ν)) := by
  rw [CondSplit.eval_eq]
  simp only [CondGuard.case]
  cases (c.eval g ν : Option Bool) with
  | none => rfl
  | some v => cases v <;> rfl

theorem CondSplit.eval_kite {p : PrimTy} {s : Srt} (a b : LTm C (.val p)) (t e : LTm C s) :
    (⟨.kite a b, t, e, .err⟩ : CondSplit C s).Eval g ν =
      (a.eval g ν : Option p.Denote).bind (fun x => (b.eval g ν : Option p.Denote).bind
        fun y => if x = y then t.eval g ν else e.eval g ν) := by
  rw [CondSplit.eval_eq]
  simp only [CondGuard.case]
  cases (a.eval g ν : Option p.Denote) with
  | none => rfl
  | some x =>
    cases (b.eval g ν : Option p.Denote) with
    | none => rfl
    | some y => by_cases hxy : x = y <;> simp only [hxy, Option.bind_some, if_true, if_false]

theorem LTm.app3Split_eval {a b c s : Srt} (o : Op3 C a b c s) (x : LTm C a) (y : LTm C b)
    (z : LTm C c) (ix : Option (CondSplit C a)) (iy : Option (CondSplit C b))
    (iz : Option (CondSplit C c))
    (hx : ∀ r, ix = some r → x.eval g ν = r.Eval g ν)
    (hy : ∀ r, iy = some r → y.eval g ν = r.Eval g ν)
    (hz : ∀ r, iz = some r → z.eval g ν = r.Eval g ν) :
    ∀ r, LTm.app3Split o x y z ix iy iz = some r → (LTm.app3 o x y z).eval g ν = r.Eval g ν := by
  have hcong : ∀ r, CondSplit.first3 ix iy iz (LTm.app3 o · y z) (LTm.app3 o x · z)
      (LTm.app3 o x y ·) = some r → (LTm.app3 o x y z).eval g ν = r.Eval g ν :=
    CondSplit.first3_eval g ν ix iy iz _ _ _ (fun v => o.eval g v (y.eval g ν) (z.eval g ν))
      (fun v => o.eval g (x.eval g ν) v (z.eval g ν)) (fun v => o.eval g (x.eval g ν) (y.eval g ν) v)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hx hy hz rfl rfl rfl
  cases o with
  | ite =>
    intro r hr
    cases hr
    exact (CondSplit.eval_ite g ν x y z).symm
  | _ => exact hcong

/-- **The split is exact**: a term's value is the value its split selects. -/
theorem LTm.condSplit_eval {s : Srt} (t : LTm C s) :
    ∀ r, t.condSplit = some r → t.eval g ν = r.Eval g ν := by
  induction t with
  | var | app0 | err => intro r hr; cases hr
  | app1 o x ih =>
    intro r hr
    change (x.condSplit).map (·.map (LTm.app1 o)) = some r at hr
    cases hx : x.condSplit with
    | none => rw [hx] at hr; cases hr
    | some q =>
      rw [hx] at hr
      cases hr
      rw [CondSplit.eval_map g ν _ (fun v => o.eval g v) (fun _ => rfl), ← ih q hx]
      rfl
  | app2 o x y ihx ihy =>
    exact CondSplit.first_eval g ν _ _ _ _ (fun v => o.eval g v (y.eval g ν))
      (fun v => o.eval g (x.eval g ν) v) (fun _ => rfl) (fun _ => rfl) ihx ihy rfl rfl
  | app3 o x y z ihx ihy ihz => exact LTm.app3Split_eval g ν o x y z _ _ _ ihx ihy ihz
  | @index R k V it q i ihq ihi =>
    exact CondSplit.first_eval g ν _ _ _ _
      (fun (v : Option ((Srt.path (.ref R)).Den C g.H)) =>
        (Option.bind (α := SRef C (.ref R)) v fun r => (i.eval g ν : Option k.Denote).bind
          fun j => some (r.index it j) : Option ((Srt.path V).Den C g.H)))
      (fun (v : Option ((Srt.val k).Den C g.H)) =>
        (Option.bind (α := SRef C (.ref R)) (q.eval g ν) fun r =>
          Option.bind (α := k.Denote) v fun j => some (r.index it j) : Option ((Srt.path V).Den C g.H)))
      (fun _ => rfl) (fun _ => rfl) ihq ihi rfl rfl
  | @obsW p q ih =>
    intro r hr
    change (q.condSplit).map _ = some r at hr
    cases hq : q.condSplit with
    | none => rw [hq] at hr; cases hr
    | some w =>
      rw [hq] at hr
      cases hr
      rw [CondSplit.eval_map g ν _
        (fun (v : Option ((Srt.path (.prim p)).Den C g.H)) =>
          (Option.bind (α := SRef C (.prim p)) v fun r => some (g.storage.obs.word (.ref r)) :
            Option ((Srt.val p).Den C g.H)))
        (fun _ => rfl), ← ih w hq]
      rfl
  | @obsL E q ih =>
    intro r hr
    change (q.condSplit).map _ = some r at hr
    cases hq : q.condSplit with
    | none => rw [hq] at hr; cases hr
    | some w =>
      rw [hq] at hr
      cases hr
      rw [CondSplit.eval_map g ν _
        (fun (v : Option ((Srt.path (.ref (.array E))).Den C g.H)) =>
          (Option.bind (α := SRef C (.ref (.array E))) v fun r =>
            some (uintOfNat (g.storage.obs.len (.ref r))) : Option ((Srt.val .uint).Den C g.H)))
        (fun _ => rfl), ← ih w hq]
      rfl
  | @obsH T q ih =>
    intro r hr
    change (q.condSplit).map _ = some r at hr
    cases hq : q.condSplit with
    | none => rw [hq] at hr; cases hr
    | some w =>
      rw [hq] at hr
      cases hr
      rw [CondSplit.eval_map g ν _
        (fun (v : Option ((Srt.path T).Den C g.H)) =>
          (Option.bind (α := SRef C T) v fun r => some (g.storage.obs.has (.ref r)) :
            Option ((Srt.val .bool).Den C g.H)))
        (fun _ => rfl), ← ih w hq]
      rfl
  | seq d a ihd iha =>
    exact CondSplit.first_eval g ν _ _ _ _ (fun v => v.bind fun _ => a.eval g ν)
      (fun v => (d.eval g ν).bind fun _ => v) (fun _ => rfl) (fun _ => rfl) ihd iha rfl rfl
  | orElse a b iha ihb =>
    exact CondSplit.first_eval g ν _ _ _ _ (fun v => v.or (b.eval g ν))
      (fun v => (a.eval g ν).or v) (fun _ => rfl) (fun _ => rfl) iha ihb rfl rfl
  | kite a b t e =>
    intro r hr
    cases hr
    exact (CondSplit.eval_kite g ν a b t e).symm

end Eval

/-! ## The case split -/

/-- The three cases of a guard as a formula: `P` where it holds, `Q` where
it fails, `R` where its operands halt. -/
def CondGuard.cases (G : CondGuard C) (P Q R : LFml C) : LFml C :=
  match G with
  | .kite x y =>
    let D : LFml C := .and (.eq x x) (.eq y y)
    .and (.imp (.and D (.eq x y)) P)
      (.and (.imp (.and D (.not (.eq x y))) Q) (.imp (.not D) R))
  | .ite c =>
    .and (.imp (.eq c (.app0 (.lit true))) P)
      (.and (.imp (.eq c (.app0 (.lit false))) Q) (.imp (.not (.eq c c)) R))

theorem CondGuard.cases_holds (g : State C []) (ν : AEnv) (G : CondGuard C) (P Q R : LFml C) :
    (G.cases P Q R).holds g ν ↔
      match G.case g ν with
      | some true => P.holds g ν
      | some false => Q.holds g ν
      | none => R.holds g ν := by
  cases G with
  | @kite p x y =>
    show ((((LFml.eq x x).holds g ν ∧ (LFml.eq y y).holds g ν) ∧ (LFml.eq x y).holds g ν →
        P.holds g ν) ∧ ((((LFml.eq x x).holds g ν ∧ (LFml.eq y y).holds g ν) ∧
        ¬ (LFml.eq x y).holds g ν → Q.holds g ν) ∧
        (¬ ((LFml.eq x x).holds g ν ∧ (LFml.eq y y).holds g ν) → R.holds g ν))) ↔
      match ((x.eval g ν : Option p.Denote).bind fun a =>
        (y.eval g ν : Option p.Denote).bind fun b => some (if a = b then true else false)) with
      | some true => P.holds g ν
      | some false => Q.holds g ν
      | none => R.holds g ν
    simp only [LFml.holds]
    cases (x.eval g ν : Option p.Denote) with
    | none => simp only [Option.bind_none, false_and, false_implies, not_false_eq_true,
        true_implies, true_and]
    | some a =>
      cases (y.eval g ν : Option p.Denote) with
      | none => simp only [Option.bind_none, Option.bind_some, and_false, false_and,
          false_implies, not_false_eq_true, true_implies, true_and]
      | some b =>
        by_cases hab : a = b <;>
          simp only [hab, Option.bind_some, if_true, if_false, and_self, true_and,
            true_implies, not_true_eq_false, false_implies, and_true, not_false_eq_true,
            iff_self]
  | ite c =>
    simp only [CondGuard.cases, CondGuard.case]
    simp only [LFml.holds, LTm.eval_app0]
    cases (c.eval g ν : Option Bool) with
    | none => simp only [false_implies, not_false_eq_true, true_implies, true_and]
    | some v =>
      cases v with
      | false => simp only [Op0.eval, reduceCtorEq, false_implies, true_implies,
          true_and, and_true, not_true_eq_false, iff_self]
      | true => simp only [Op0.eval, reduceCtorEq, false_implies, true_implies,
          and_true, not_true_eq_false, iff_self]

/-- A term that always returns: an atom or a literal. -/
def LTm.total {s : Srt} (t : LTm C s) : Bool :=
  match s, t with
  | _, .var _ => true
  | _, .app0 (.lit _) => true
  | _, _ => false

theorem LTm.total_eval (g : State C []) (ν : AEnv) {p : PrimTy} (t : LTm C (.val p))
    (h : t.total = true) : ∃ v, (t.eval g ν : Option p.Denote) = some v := by
  cases t with
  | var k => exact ⟨_, rfl⟩
  | app0 o =>
    cases o with
    | lit v => exact ⟨v, rfl⟩
    | _ => cases h
  | _ => cases h

/-- The cases of a guard whose operands always return: two, not three. -/
def CondGuard.split (G : CondGuard C) (P Q R : LFml C) : LFml C :=
  match G with
  | .kite x y =>
    if x.total && y.total then .and (.imp (.eq x y) P) (.imp (.not (.eq x y)) Q)
    else G.cases P Q R
  | .ite c =>
    if c.total then .and (.imp (.eq c (.app0 (.lit true))) P) (.imp (.eq c (.app0 (.lit false))) Q)
    else G.cases P Q R

theorem CondGuard.split_holds (g : State C []) (ν : AEnv) (G : CondGuard C) (P Q R : LFml C) :
    (G.split P Q R).holds g ν ↔
      match G.case g ν with
      | some true => P.holds g ν
      | some false => Q.holds g ν
      | none => R.holds g ν := by
  cases G with
  | @kite p x y =>
    simp only [CondGuard.split]
    by_cases ht : (x.total && y.total) = true
    · rw [if_pos ht]
      obtain ⟨hx, hy⟩ := Bool.and_eq_true_iff.mp ht
      obtain ⟨a, ha⟩ := LTm.total_eval g ν x hx
      obtain ⟨b, hb⟩ := LTm.total_eval g ν y hy
      simp only [CondGuard.case, LFml.holds, ha, hb, Option.bind_some]
      by_cases hab : a = b <;>
        simp only [hab, if_true, if_false, not_true_eq_false, not_false_eq_true,
          false_implies, true_implies, and_true, true_and]
    · rw [if_neg ht]
      exact CondGuard.cases_holds g ν _ P Q R
  | ite c =>
    simp only [CondGuard.split]
    by_cases ht : c.total = true
    · rw [if_pos ht]
      obtain ⟨v, hv⟩ := LTm.total_eval g ν c ht
      simp only [CondGuard.case, LFml.holds, LTm.eval_app0, hv]
      cases v with
      | false => simp only [Op0.eval, reduceCtorEq, false_implies, true_implies, true_and]
      | true => simp only [Op0.eval, reduceCtorEq, false_implies, true_implies, and_true]
    · rw [if_neg ht]
      exact CondGuard.cases_holds g ν _ P Q R

/-- The equation's three cases, read through the split's value. -/
theorem LFml.holds_eq_split (g : State C []) (ν : AEnv) {p : PrimTy} (a b : LTm C (.val p))
    (r : CondSplit C (.val p)) (ha : (a.eval g ν : Option p.Denote) = r.Eval g ν) :
    (LFml.eq a b).holds g ν ↔ (r.guard.split (.eq r.thn b) (.eq r.els b) (.eq r.bad b)).holds g ν := by
  rw [CondGuard.split_holds]
  unfold CondSplit.Eval at ha
  simp only [LFml.holds, ha]
  cases r.guard.case g ν with
  | none => exact Iff.rfl
  | some v => cases v <;> exact Iff.rfl

theorem LFml.holds_eq_split' (g : State C []) (ν : AEnv) {p : PrimTy} (a b : LTm C (.val p))
    (r : CondSplit C (.val p)) (hb : (b.eval g ν : Option p.Denote) = r.Eval g ν) :
    (LFml.eq a b).holds g ν ↔ (r.guard.split (.eq a r.thn) (.eq a r.els) (.eq a r.bad)).holds g ν := by
  rw [CondGuard.split_holds]
  unfold CondSplit.Eval at hb
  simp only [LFml.holds, hb]
  cases r.guard.case g ν with
  | none => exact Iff.rfl
  | some v => cases v <;> exact Iff.rfl

/-! ## Folding trivial conditionals

Before lifting, a conditional whose outcome does not matter is folded: a
`kite` comparing two always-returning operands with equal branches is that
branch, an `ite` on a literal is its branch.  The elimination emits them
for a location's presence after a save (`true` either way), and lifting
them would only duplicate the formula. -/

/-- `kite a b t e`, folded where both branches are one term and the
operands return. -/
def LTm.mkKite {p : PrimTy} {s : Srt} (a b : LTm C (.val p)) (t e : LTm C s) : LTm C s :=
  if a.total && b.total && t.beqR e then t else .kite a b t e

/-- A ternary symbol, folded where it is `ite` on a literal. -/
def LTm.mkApp3 : {a b c s : Srt} → Op3 C a b c s → LTm C a → LTm C b → LTm C c → LTm C s
  | _, _, _, _, .ite, x, y, z =>
    match x.litV? with
    | some true => y
    | some false => z
    | none => .app3 .ite x y z
  | _, _, _, _, o, x, y, z => .app3 o x y z

/-- `LTm.condSimp`'s compiled twin. -/
def LTm.condSimpM : {s : Srt} → LTm C s → LTm C s
  | _, .var k => .var k
  | _, .app0 o => .app0 o
  | _, .app1 o x => .app1 o x.condSimpM
  | _, .app2 o x y => .app2 o x.condSimpM y.condSimpM
  | _, .app3 o x y z => LTm.mkApp3 o x.condSimpM y.condSimpM z.condSimpM
  | _, .index it q i => .index it q.condSimpM i.condSimpM
  | _, .obsW q => .obsW q.condSimpM
  | _, .obsL q => .obsL q.condSimpM
  | _, .obsH q => .obsH q.condSimpM
  | _, .seq d a => .seq d.condSimpM a.condSimpM
  | _, .orElse a b => .orElse a.condSimpM b.condSimpM
  | _, .kite a b t e => LTm.mkKite a.condSimpM b.condSimpM t.condSimpM e.condSimpM
  | _, .err => .err

/-- **Trivial conditionals folded**, bottom up, by the recursor. -/
@[implemented_by LTm.condSimpM]
def LTm.condSimp {s : Srt} (t : LTm C s) : LTm C s :=
  @LTm.rec C (fun s _ => LTm C s)
    (fun k => .var k)
    (fun o => .app0 o)
    (fun o _ x => .app1 o x)
    (fun o _ _ x y => .app2 o x y)
    (fun o _ _ _ x y z => LTm.mkApp3 o x y z)
    (fun it _ _ q i => .index it q i)
    (fun _ q => .obsW q)
    (fun _ q => .obsL q)
    (fun _ q => .obsH q)
    (fun _ _ d a => .seq d a)
    (fun _ _ a b => .orElse a b)
    (fun _ _ _ _ a b t e => LTm.mkKite a b t e)
    .err s t

theorem LTm.condSimp_eq_condSimpM {s : Srt} (t : LTm C s) : t.condSimp = t.condSimpM := by
  induction t with
  | var | app0 | err => rfl
  | app1 o x ih => simp only [LTm.condSimpM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [LTm.condSimpM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [LTm.condSimpM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => simp only [LTm.condSimpM, ← ihq, ← ihi]; rfl
  | obsW q ih | obsL q ih | obsH q ih => simp only [LTm.condSimpM, ← ih]; rfl
  | seq d a ihd iha => simp only [LTm.condSimpM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => simp only [LTm.condSimpM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe => simp only [LTm.condSimpM, ← iha, ← ihb, ← iht, ← ihe]; rfl

section Fold

variable (g : State C []) (ν : AEnv)

theorem LTm.eval_mkKite {p : PrimTy} {s : Srt} (a b : LTm C (.val p)) (t e : LTm C s) :
    (LTm.mkKite a b t e).eval g ν = (LTm.kite a b t e).eval g ν := by
  unfold LTm.mkKite
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨ha, hb⟩, hte⟩ := h
    have hte' : t = e := LTm.eq_of_beqR hte
    subst hte'
    obtain ⟨x, hx⟩ := LTm.total_eval g ν a ha
    obtain ⟨y, hy⟩ := LTm.total_eval g ν b hb
    rw [LTm.eval_kite, hx, hy]
    by_cases hxy : x = y <;> simp only [hxy, Option.bind_some, if_true, if_false]
  · rfl

theorem LTm.eval_mkApp3 {a b c s : Srt} (o : Op3 C a b c s) (x : LTm C a) (y : LTm C b)
    (z : LTm C c) : (LTm.mkApp3 o x y z).eval g ν = (LTm.app3 o x y z).eval g ν := by
  cases o with
  | ite =>
    show (match x.litV? with
      | some true => y
      | some false => z
      | none => .app3 .ite x y z).eval g ν = _
    cases hx : x.litV? with
    | none => rfl
    | some v =>
      rw [LTm.eq_of_litV? hx]
      cases v <;> rfl
  | _ => rfl

/-- **Folding keeps every value.** -/
theorem LTm.eval_condSimp {s : Srt} (t : LTm C s) : t.condSimp.eval g ν = t.eval g ν := by
  induction t with
  | var | app0 | err => rfl
  | app1 o x ih =>
    show (LTm.app1 o x.condSimp).eval g ν = _
    rw [LTm.eval_app1, LTm.eval_app1, ih]
  | app2 o x y ihx ihy =>
    show (LTm.app2 o x.condSimp y.condSimp).eval g ν = _
    rw [LTm.eval_app2, LTm.eval_app2, ihx, ihy]
  | app3 o x y z ihx ihy ihz =>
    show (LTm.mkApp3 o x.condSimp y.condSimp z.condSimp).eval g ν = _
    rw [LTm.eval_mkApp3, LTm.eval_app3, LTm.eval_app3, ihx, ihy, ihz]
  | index it q i ihq ihi =>
    show (LTm.index it q.condSimp i.condSimp).eval g ν = _
    rw [LTm.eval_index, LTm.eval_index, ihq, ihi]
  | obsW q ih =>
    show (LTm.obsW q.condSimp).eval g ν = _
    rw [LTm.eval_obsW, LTm.eval_obsW, ih]
  | obsL q ih =>
    show (LTm.obsL q.condSimp).eval g ν = _
    rw [LTm.eval_obsL, LTm.eval_obsL, ih]
  | obsH q ih =>
    show (LTm.obsH q.condSimp).eval g ν = _
    rw [LTm.eval_obsH, LTm.eval_obsH, ih]
  | seq d a ihd iha =>
    show (LTm.seq d.condSimp a.condSimp).eval g ν = _
    rw [LTm.eval_seq, LTm.eval_seq, ihd, iha]
  | orElse a b iha ihb =>
    show (LTm.orElse a.condSimp b.condSimp).eval g ν = _
    rw [LTm.eval_orElse, LTm.eval_orElse, iha, ihb]
  | kite a b t e iha ihb iht ihe =>
    show (LTm.mkKite a.condSimp b.condSimp t.condSimp e.condSimp).eval g ν = _
    rw [LTm.eval_mkKite, LTm.eval_kite, LTm.eval_kite, iha, ihb, iht, ihe]

end Fold

/-- Trivial conditionals folded in every equation. -/
def LFml.condSimp : LFml C → LFml C
  | .tt => .tt
  | .eq a b => .eq a.condSimp b.condSimp
  | .not φ => .not φ.condSimp
  | .and φ ψ => .and φ.condSimp ψ.condSimp
  | .imp φ ψ => .imp φ.condSimp ψ.condSimp
  | .all k p φ => .all k p φ.condSimp

theorem LFml.condSimp_holds (g : State C []) :
    ∀ (φ : LFml C) (ν : AEnv), φ.condSimp.holds g ν ↔ φ.holds g ν
  | .tt, _ => Iff.rfl
  | .eq a b, ν => by simp only [LFml.condSimp, LFml.holds, LTm.eval_condSimp]
  | .not φ, ν => not_congr (LFml.condSimp_holds g φ ν)
  | .and φ ψ, ν => and_congr (LFml.condSimp_holds g φ ν) (LFml.condSimp_holds g ψ ν)
  | .imp φ ψ, ν => imp_congr (LFml.condSimp_holds g φ ν) (LFml.condSimp_holds g ψ ν)
  | .all _ _ φ, _ => forall_congr' fun _ => LFml.condSimp_holds g φ _

/-! ## Lifting -/

/-- Every equation of a formula replaced. -/
def LFml.mapEq (f : {p : PrimTy} → LTm C (.val p) → LTm C (.val p) → LFml C) : LFml C → LFml C
  | .tt => .tt
  | .eq a b => f a b
  | .not φ => .not (φ.mapEq f)
  | .and φ ψ => .and (φ.mapEq f) (ψ.mapEq f)
  | .imp φ ψ => .imp (φ.mapEq f) (ψ.mapEq f)
  | .all k p φ => .all k p (φ.mapEq f)

theorem LFml.mapEq_holds (g : State C [])
    (f : {p : PrimTy} → LTm C (.val p) → LTm C (.val p) → LFml C)
    (hf : ∀ (ν : AEnv) {p : PrimTy} (a b : LTm C (.val p)), (f a b).holds g ν ↔ (LFml.eq a b).holds g ν) :
    ∀ (φ : LFml C) (ν : AEnv), (φ.mapEq f).holds g ν ↔ φ.holds g ν
  | .tt, _ => Iff.rfl
  | .eq a b, ν => hf ν a b
  | .not φ, ν => not_congr (mapEq_holds g f hf φ ν)
  | .and φ ψ, ν => and_congr (mapEq_holds g f hf φ ν) (mapEq_holds g f hf ψ ν)
  | .imp φ ψ, ν => imp_congr (mapEq_holds g f hf φ ν) (mapEq_holds g f hf ψ ν)
  | .all _ _ φ, _ => forall_congr' fun _ => mapEq_holds g f hf φ _

/-- One equation: its first conditional (left side first) lifted, the
cases continued by `k`. -/
def LFml.liftEq (k : LFml C → LFml C) {p : PrimTy} (a b : LTm C (.val p)) : LFml C :=
  match a.condSplit with
  | some r => k (r.guard.split (.eq r.thn b) (.eq r.els b) (.eq r.bad b))
  | none =>
    match b.condSplit with
    | some r => k (r.guard.split (.eq a r.thn) (.eq a r.els) (.eq a r.bad))
    | none => .eq a b

/-- **Conditionals lifted** out of every equation, to the nesting depth
`fuel`; past it a formula is kept. -/
def LFml.liftCond : Nat → LFml C → LFml C
  | 0, φ => φ
  | n + 1, φ => φ.mapEq (LFml.liftEq (LFml.liftCond n))

/-- **Lifting is exact.** -/
theorem LFml.liftCond_holds (g : State C []) :
    ∀ (n : Nat) (φ : LFml C) (ν : AEnv), (φ.liftCond n).holds g ν ↔ φ.holds g ν
  | 0, _, _ => Iff.rfl
  | n + 1, φ, ν => by
    apply LFml.mapEq_holds g _ _ φ ν
    intro ν p a b
    unfold LFml.liftEq
    cases ha : a.condSplit with
    | some r =>
      exact (LFml.liftCond_holds g n _ ν).trans
        (LFml.holds_eq_split g ν a b r (LTm.condSplit_eval g ν a r ha)).symm
    | none =>
      cases hb : b.condSplit with
      | some r =>
        exact (LFml.liftCond_holds g n _ ν).trans
          (LFml.holds_eq_split' g ν a b r (LTm.condSplit_eval g ν b r hb)).symm
      | none => exact Iff.rfl

theorem LFml.liftCond_valid (n : Nat) (φ : LFml C) : (φ.liftCond n).Valid ↔ φ.Valid :=
  forall_congr' fun g => forall_congr' fun ν => LFml.liftCond_holds g n φ ν

end Solidity.Decide
