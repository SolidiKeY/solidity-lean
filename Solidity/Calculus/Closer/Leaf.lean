import Solidity.Calculus.Closer.Bytes

/-!
# Closing a leaf

What a premise tells, and closing a leaf (`LFml.close`, `LFml.verdict_sound`).

A piece of `Calculus/Closer.lean`, whose docstring describes the whole.
-/

namespace Solidity

namespace Decide

variable {C : Contract}

/-! ## What a premise tells -/

section Premises

variable {g : State C []}

/-- `LTm.strict`'s compiled twin. -/
def LTm.strictM : {s : Srt} → LTm C s → List ((s : Srt) × LTm C s)
  | _, @LTm.var _ p k => [⟨.val p, .var k⟩]
  | _, .app0 o => [⟨_, .app0 o⟩]
  | _, .app1 o x => ⟨_, .app1 o x⟩ :: x.strictM
  | _, .app2 o x y => ⟨_, .app2 o x y⟩ :: (x.strictM ++ if o.strictR then y.strictM else [])
  | _, .app3 o x y z => ⟨_, .app3 o x y z⟩ ::
    (x.strictM ++ ((if o.strictY then y.strictM else []) ++ if o.strictZ then z.strictM else []))
  | _, .index it q i => ⟨_, .index it q i⟩ :: (q.strictM ++ i.strictM)
  | _, .obsW q => ⟨_, .obsW q⟩ :: q.strictM
  | _, .obsL q => ⟨_, .obsL q⟩ :: q.strictM
  | _, .obsH q => ⟨_, .obsH q⟩ :: q.strictM
  | _, .seq d a => ⟨_, .seq d a⟩ :: (d.strictM ++ a.strictM)
  | _, .orElse a b => [⟨_, .orElse a b⟩]
  | _, .kite a b t e => ⟨_, .kite a b t e⟩ :: (a.strictM ++ b.strictM)
  | _, .err => []

/-- **The terms that return wherever `t` does**: `t` and, below it, every
subterm its symbols read (not a conditional's branches, nor the right side
of `&&`/`||`, nor either side of `orElse`).  By the recursor. -/
@[implemented_by LTm.strictM]
def LTm.strict {s : Srt} (t : LTm C s) : List ((s : Srt) × LTm C s) :=
  @LTm.rec C (fun _ _ => List ((s : Srt) × LTm C s))
    (@fun p k => [⟨.val p, .var k⟩])
    (@fun _ o => [⟨_, .app0 o⟩])
    (@fun _ _ o x ihx => ⟨_, .app1 o x⟩ :: ihx)
    (@fun _ _ _ o x y ihx ihy => ⟨_, .app2 o x y⟩ :: (ihx ++ if o.strictR then ihy else []))
    (@fun _ _ _ _ o x y z ihx ihy ihz => ⟨_, .app3 o x y z⟩ ::
      (ihx ++ ((if o.strictY then ihy else []) ++ if o.strictZ then ihz else [])))
    (@fun _ _ _ it q i ihq ihi => ⟨_, .index it q i⟩ :: (ihq ++ ihi))
    (@fun _ q ih => ⟨_, .obsW q⟩ :: ih)
    (@fun _ q ih => ⟨_, .obsL q⟩ :: ih)
    (@fun _ q ih => ⟨_, .obsH q⟩ :: ih)
    (@fun _ _ d a ihd iha => ⟨_, .seq d a⟩ :: (ihd ++ iha))
    (@fun _ a b _ _ => [⟨_, .orElse a b⟩])
    (@fun _ _ a b t e iha ihb _ _ => ⟨_, .kite a b t e⟩ :: (iha ++ ihb))
    (@fun _ => []) s t

theorem LTm.strict_eq_strictM {s : Srt} (t : LTm C s) : t.strict = t.strictM := by
  induction t with
  | var | app0 | err | orElse => rfl
  | app1 o x ih => simp only [LTm.strictM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [LTm.strictM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [LTm.strictM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => simp only [LTm.strictM, ← ihq, ← ihi]; rfl
  | obsW q ih | obsL q ih | obsH q ih => simp only [LTm.strictM, ← ih]; rfl
  | seq d a ihd iha => simp only [LTm.strictM, ← ihd, ← iha]; rfl
  | kite a b t e iha ihb iht ihe => simp only [LTm.strictM, ← iha, ← ihb]; rfl

theorem isSome_of_bind {α β : Type} {x : Option α} {f : α → Option β}
    (h : (x.bind f).isSome = true) : x.isSome = true := by
  cases x with
  | none => cases h
  | some _ => rfl

theorem isSome_of_bind_some {α β : Type} {x : Option α} {f : α → Option β}
    (h : (x.bind f).isSome = true) : ∃ a, x = some a ∧ (f a).isSome = true := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- **Below a term that returns, its strict subterms return.** -/
theorem LTm.strict_isSome (ν : AEnv) {s : Srt} (t : LTm C s) (h : (t.eval g ν).isSome = true) :
    ∀ u ∈ t.strict, (u.2.eval g ν).isSome = true := by
  induction t with
  | var k | app0 o =>
    intro u hu
    rcases List.mem_singleton.1 (show u ∈ [_] from hu) with rfl
    exact h
  | err => intro u hu; cases hu
  | orElse a b =>
    intro u hu
    rcases List.mem_singleton.1 (show u ∈ [_] from hu) with rfl
    exact h
  | app1 o x ih =>
    have hx : (x.eval g ν).isSome = true := by
      cases hx : x.eval g ν with
      | none => rw [LTm.eval_app1, hx, Op1.eval_none] at h; cases h
      | some _ => rfl
    intro u hu
    rcases List.mem_cons.1 (show u ∈ _ :: _ from hu) with rfl | hu
    · exact h
    · exact ih hx u hu
  | app2 o x y ihx ihy =>
    have hx : (x.eval g ν).isSome = true := by
      cases hx : x.eval g ν with
      | none => rw [LTm.eval_app2, hx, Op2.eval_none_left] at h; cases h
      | some _ => rfl
    intro u hu
    rcases List.mem_cons.1 (show u ∈ _ :: _ from hu) with rfl | hu
    · exact h
    rcases List.mem_append.1 hu with hu | hu
    · exact ihx hx u hu
    · split at hu
      · rename_i hs
        have hy : (y.eval g ν).isSome = true := by
          cases hy : y.eval g ν with
          | none => rw [LTm.eval_app2, hy, Op2.eval_none_right g o hs] at h; cases h
          | some _ => rfl
        exact ihy hy u hu
      · cases hu
  | app3 o x y z ihx ihy ihz =>
    have hx : (x.eval g ν).isSome = true := by
      cases hx : x.eval g ν with
      | none => rw [LTm.eval_app3, hx, Op3.eval_none_x] at h; cases h
      | some _ => rfl
    intro u hu
    rcases List.mem_cons.1 (show u ∈ _ :: _ from hu) with rfl | hu
    · exact h
    rcases List.mem_append.1 hu with hu | hu
    · exact ihx hx u hu
    rcases List.mem_append.1 hu with hu | hu
    · split at hu
      · rename_i hs
        have hy : (y.eval g ν).isSome = true := by
          cases hy : y.eval g ν with
          | none => rw [LTm.eval_app3, hy, Op3.eval_none_y g o hs] at h; cases h
          | some _ => rfl
        exact ihy hy u hu
      · cases hu
    · split at hu
      · rename_i hs
        have hz : (z.eval g ν).isSome = true := by
          cases hz : z.eval g ν with
          | none => rw [LTm.eval_app3, hz, Op3.eval_none_z g o hs] at h; cases h
          | some _ => rfl
        exact ihz hz u hu
      · cases hu
  | index it q i ihq ihi =>
    rw [LTm.eval_index] at h
    obtain ⟨r, hr, h'⟩ := isSome_of_bind_some h
    have hi := isSome_of_bind h'
    intro u hu
    rcases List.mem_cons.1 (show u ∈ _ :: _ from hu) with rfl | hu
    · rw [LTm.eval_index, hr]; exact h'
    rcases List.mem_append.1 hu with hu | hu
    · exact ihq (by rw [hr]; rfl) u hu
    · exact ihi hi u hu
  | obsW q ih | obsL q ih | obsH q ih =>
    intro u hu
    rcases List.mem_cons.1 (show u ∈ _ :: _ from hu) with rfl | hu
    · exact h
    · exact ih (isSome_of_bind h) u hu
  | seq d a ihd iha =>
    rw [LTm.eval_seq] at h
    obtain ⟨r, hr, h'⟩ := isSome_of_bind_some h
    intro u hu
    rcases List.mem_cons.1 (show u ∈ _ :: _ from hu) with rfl | hu
    · rw [LTm.eval_seq, hr]; exact h'
    rcases List.mem_append.1 hu with hu | hu
    · exact ihd (by rw [hr]; rfl) u hu
    · exact iha h' u hu
  | kite a b t e iha ihb iht ihe =>
    rw [LTm.eval_kite] at h
    obtain ⟨r, hr, h'⟩ := isSome_of_bind_some h
    have hb := isSome_of_bind h'
    intro u hu
    rcases List.mem_cons.1 (show u ∈ _ :: _ from hu) with rfl | hu
    · rw [LTm.eval_kite, hr]; exact h'
    rcases List.mem_append.1 hu with hu | hu
    · exact iha (by rw [hr]; rfl) u hu
    · exact ihb hb u hu

/-- `LTm.mentions`' compiled twin. -/
def LTm.mentionsM (k : Nat) : {s : Srt} → LTm C s → Bool
  | _, .var j => j == k
  | _, .app0 _ | _, .err => false
  | _, .app1 _ x => x.mentionsM k
  | _, .app2 _ x y => x.mentionsM k || y.mentionsM k
  | _, .app3 _ x y z => x.mentionsM k || y.mentionsM k || z.mentionsM k
  | _, .index _ q i => q.mentionsM k || i.mentionsM k
  | _, .obsW q | _, .obsL q | _, .obsH q => q.mentionsM k
  | _, .seq d a => d.mentionsM k || a.mentionsM k
  | _, .orElse a b => a.mentionsM k || b.mentionsM k
  | _, .kite a b t e => a.mentionsM k || b.mentionsM k || t.mentionsM k || e.mentionsM k

/-- **The term reads the position `k`.**  By the recursor. -/
@[implemented_by LTm.mentionsM]
def LTm.mentions (k : Nat) {s : Srt} (t : LTm C s) : Bool :=
  @LTm.rec C (fun _ _ => Bool)
    (@fun _ j => j == k) (@fun _ _ => false)
    (@fun _ _ _ _ ihx => ihx)
    (@fun _ _ _ _ _ _ ihx ihy => ihx || ihy)
    (@fun _ _ _ _ _ _ _ _ ihx ihy ihz => ihx || ihy || ihz)
    (@fun _ _ _ _ _ _ ihq ihi => ihq || ihi)
    (@fun _ _ ih => ih) (@fun _ _ ih => ih) (@fun _ _ ih => ih)
    (@fun _ _ _ _ ihd iha => ihd || iha)
    (@fun _ _ _ iha ihb => iha || ihb)
    (@fun _ _ _ _ _ _ iha ihb iht ihe => iha || ihb || iht || ihe)
    (@fun _ => false) s t

theorem LTm.mentions_eq_mentionsM (k : Nat) {s : Srt} (t : LTm C s) :
    t.mentions k = t.mentionsM k := by
  induction t with
  | var | app0 | err => rfl
  | app1 o x ih => simp only [LTm.mentionsM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [LTm.mentionsM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [LTm.mentionsM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => simp only [LTm.mentionsM, ← ihq, ← ihi]; rfl
  | obsW q ih | obsL q ih | obsH q ih => simp only [LTm.mentionsM, ← ih]; rfl
  | seq d a ihd iha => simp only [LTm.mentionsM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => simp only [LTm.mentionsM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe => simp only [LTm.mentionsM, ← iha, ← ihb, ← iht, ← ihe]; rfl

/-- **A term that does not read `k` reads the same with `k` rebound.** -/
theorem LTm.eval_set_of_mentions (ν : AEnv) (k : Nat) (p : PrimTy) (v : p.Denote) {s : Srt}
    (t : LTm C s) (h : t.mentions k = false) : t.eval g (ν.set p k v) = t.eval g ν := by
  induction t with
  | var j =>
    have hj : j ≠ k := fun e => by simp only [LTm.mentions, e, beq_self_eq_true] at h; cases h
    rw [LTm.eval_var, LTm.eval_var, AEnv.get_set_ne _ _ _ _ hj]
  | app0 o | err => rfl
  | app1 o x ih => rw [LTm.eval_app1, LTm.eval_app1, ih h]
  | app2 o x y ihx ihy =>
    simp only [LTm.mentions, Bool.or_eq_false_iff] at h
    rw [LTm.eval_app2, LTm.eval_app2, ihx h.1, ihy h.2]
  | app3 o x y z ihx ihy ihz =>
    simp only [LTm.mentions, Bool.or_eq_false_iff] at h
    rw [LTm.eval_app3, LTm.eval_app3, ihx h.1.1, ihy h.1.2, ihz h.2]
  | index it q i ihq ihi =>
    simp only [LTm.mentions, Bool.or_eq_false_iff] at h
    rw [LTm.eval_index, LTm.eval_index, ihq h.1, ihi h.2]
  | obsW q ih => rw [LTm.eval_obsW, LTm.eval_obsW, ih h]
  | obsL q ih => rw [LTm.eval_obsL, LTm.eval_obsL, ih h]
  | obsH q ih => rw [LTm.eval_obsH, LTm.eval_obsH, ih h]
  | seq d a ihd iha =>
    simp only [LTm.mentions, Bool.or_eq_false_iff] at h
    rw [LTm.eval_seq, LTm.eval_seq, ihd h.1, iha h.2]
  | orElse a b iha ihb =>
    simp only [LTm.mentions, Bool.or_eq_false_iff] at h
    rw [LTm.eval_orElse, LTm.eval_orElse, iha h.1, ihb h.2]
  | kite a b t e iha ihb iht ihe =>
    simp only [LTm.mentions, Bool.or_eq_false_iff] at h
    rw [LTm.eval_kite, LTm.eval_kite, iha h.1.1.1, ihb h.1.1.2, iht h.1.2, ihe h.2]

/-- The facts that do not read the position `k`: what still holds once a
quantifier binds it. -/
def Facts.drop (F : Facts C) (k : Nat) : Facts C where
  eqs := F.eqs.filter fun e => !(e.l.mentions k || e.r.mentions k)
  nes := F.nes.filter fun e => !(e.l.mentions k || e.r.mentions k)
  rets := F.rets.filter fun u => !u.2.mentions k
  bnds := F.bnds.filter fun b => !b.t.mentions k

theorem Facts.drop_ok {F : Facts C} {ν : AEnv} (hF : F.Ok g ν) (k : Nat) (p : PrimTy)
    (v : p.Denote) : (F.drop k).Ok g (ν.set p k v) := by
  refine ⟨fun e he => ?_, fun e he => ?_, fun u hu => ?_, fun b hb => ?_⟩
  · simp only [Facts.drop, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
      Bool.or_eq_false_iff] at he
    rw [LTm.eval_set_of_mentions ν k p v _ he.2.1, LTm.eval_set_of_mentions ν k p v _ he.2.2]
    exact hF.eqs e he.1
  · simp only [Facts.drop, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
      Bool.or_eq_false_iff] at he
    rw [LTm.eval_set_of_mentions ν k p v _ he.2.1, LTm.eval_set_of_mentions ν k p v _ he.2.2]
    exact hF.nes e he.1
  · simp only [Facts.drop, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hu
    rw [LTm.eval_set_of_mentions ν k p v _ hu.2]
    exact hF.rets u hu.1
  · simp only [Facts.drop, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hb
    rw [LTm.eval_set_of_mentions ν k p v _ hb.2]
    exact hF.bnds b hb.1

/-- `t` returns, and so does every strict subterm of it. -/
def Facts.addRets (F : Facts C) {s : Srt} (t : LTm C s) : Facts C :=
  { F with rets := t.strict ++ F.rets }

theorem Facts.addRets_ok {F : Facts C} {ν : AEnv} (hF : F.Ok g ν) {s : Srt} {t : LTm C s}
    (h : (t.eval g ν).isSome = true) : (F.addRets t).Ok g ν := by
  refine ⟨hF.eqs, hF.nes, fun u hu => ?_, hF.bnds⟩
  rcases List.mem_append.1 hu with hu | hu
  · exact LTm.strict_isSome ν t h u hu
  · exact hF.rets u hu

/-- An equation between two normal forms rewrites right to left: its left
side is a literal, or a position above the right side's. -/
def swapQ {p : PrimTy} (a b : LTm C (.val p)) : Bool :=
  a.litV?.isSome ||
    match a, b with
    | .var i, .var j => decide (i < j)
    | _, _ => false

/-- The rewrite for an equation between two normal forms: a literal or a
lower position on the right. -/
def orient {p : PrimTy} (a b : LTm C (.val p)) : EqF C :=
  if swapQ a b then ⟨p, b, a⟩ else ⟨p, a, b⟩

theorem orient_ok {ν : AEnv} {p : PrimTy} (a b : LTm C (.val p)) {x : p.Denote}
    (ha : (a.eval g ν : Option p.Denote) = some x) (hb : (b.eval g ν : Option p.Denote) = some x) :
    ∃ y, ((orient a b).l.eval g ν : Option (orient a b).p.Denote) = some y ∧
      (orient a b).r.eval g ν = some y := by
  unfold orient
  cases swapQ a b
  · exact ⟨x, ha, hb⟩
  · exact ⟨x, hb, ha⟩

/-- The rewrite `a = b` gives, their normal forms oriented (`orient`). -/
def Facts.addEqR (F : Facts C) {p : PrimTy} (a b : LTm C (.val p)) : Facts C :=
  let a' := F.nf a
  let b' := F.nf b
  if a'.beqR b' then F else { F with eqs := orient a' b' :: F.eqs }

theorem Facts.addEqR_ok {F : Facts C} {ν : AEnv} (hF : F.Ok g ν) {p : PrimTy}
    {a b : LTm C (.val p)} (h : (LFml.eq a b).holds g ν) : (F.addEqR a b).Ok g ν := by
  obtain ⟨x, ha, hb⟩ := (LFml.holds_eq_iff g ν a b).1 h
  rw [← F.nf_eval hF] at ha hb
  dsimp only [Facts.addEqR]
  split
  · exact hF
  · refine ⟨fun e he => ?_, hF.nes, hF.rets, hF.bnds⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact orient_ok _ _ ha hb
    · exact hF.eqs e he

/-- The premise `a = b` alone: both normal forms return, with their strict
subterms, and the one rewrites to the other. -/
def Facts.addEq1 (F : Facts C) {p : PrimTy} (a b : LTm C (.val p)) : Facts C :=
  ((F.addRets (F.nf a)).addRets (F.nf b)).addEqR a b

theorem Facts.addEq1_ok {F : Facts C} {ν : AEnv} (hF : F.Ok g ν) {p : PrimTy}
    {a b : LTm C (.val p)} (h : (LFml.eq a b).holds g ν) : (F.addEq1 a b).Ok g ν := by
  obtain ⟨x, ha, hb⟩ := (LFml.holds_eq_iff g ν a b).1 h
  rw [← F.nf_eval hF] at ha hb
  exact Facts.addEqR_ok (Facts.addRets_ok (Facts.addRets_ok hF (by rw [ha]; rfl))
    (by rw [hb]; rfl)) h

/-- The premise `¬ a = b` alone: where both normal forms return, they are
apart. -/
def Facts.addNe1 (F : Facts C) {p : PrimTy} (a b : LTm C (.val p)) : Facts C :=
  let a' := F.nf a
  let b' := F.nf b
  if F.returns a' && F.returns b' then { F with nes := ⟨p, a', b'⟩ :: F.nes } else F

theorem Facts.addNe1_ok {F : Facts C} {ν : AEnv} (hF : F.Ok g ν) {p : PrimTy}
    {a b : LTm C (.val p)} (h : ¬ (LFml.eq a b).holds g ν) : (F.addNe1 a b).Ok g ν := by
  dsimp only [Facts.addNe1]
  split
  · rename_i hr
    simp only [Bool.and_eq_true] at hr
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF _ hr.1)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF _ hr.2)
    refine ⟨hF.eqs, fun e he => ?_, hF.rets, hF.bnds⟩
    rcases List.mem_cons.1 he with rfl | he
    · refine ⟨x, y, hx, hy, fun hxy => h ?_⟩
      rw [F.nf_eval hF] at hx hy
      exact (LFml.holds_eq_iff g ν a b).2 ⟨x, hx, hxy ▸ hy⟩
    · exact hF.nes e he
  · exact hF

/-! ### What a boolean premise tells

`c = true` with `c` an equation, a conjunction, a negation is taken apart
(KeY's `equal_literals`, `andLeft`, `notLeft` on the formula a boolean term
reads); `assert(c)` returning is `c = true`. -/

theorem evalT_eqB {p : PrimTy} (u w : p.Denote) :
    BinOp.evalT .eqB rfl u w = some (decide (u = w)) := by
  cases p
  · rfl
  · show some (decide (u.1 = w.1)) = _
    simp only [Option.some.injEq, decide_eq_decide]
    exact Subtype.ext_iff.symm
  · show some (decide (u.1 = w.1)) = _
    simp only [Option.some.injEq, decide_eq_decide]
    exact Subtype.ext_iff.symm

theorem evalT_neB {p : PrimTy} (u w : p.Denote) :
    BinOp.evalT .neB rfl u w = some (!decide (u = w)) := by
  cases p
  · rfl
  · show some (!decide (u.1 = w.1)) = _
    simp only [Option.some.injEq, Bool.not_inj_iff, decide_eq_decide]
    exact Subtype.ext_iff.symm
  · show some (!decide (u.1 = w.1)) = _
    simp only [Option.some.injEq, Bool.not_inj_iff, decide_eq_decide]
    exact Subtype.ext_iff.symm

/-- The premise `a < b` (`strict`) or `a <= b`: each side bounded by the
other's range. -/
def Facts.lessBnd (F : Facts C) {p : PrimTy} (a b : LTm C (.val p)) (strict : Bool) : Facts C :=
  let d : Int := if strict then 1 else 0
  { F with bnds := ⟨p, a, (F.range a).1, (F.range b).2 - d⟩ ::
      ⟨p, b, (F.range a).1 + d, (F.range b).2⟩ :: F.bnds }

theorem Facts.lessBnd_ok {ν : AEnv} {F : Facts C} (hF : F.Ok g ν) {p : PrimTy}
    {a b : LTm C (.val p)} {u w : p.Denote} (ha : (a.eval g ν : Option p.Denote) = some u)
    (hb : (b.eval g ν : Option p.Denote) = some w) (strict : Bool)
    (h : if strict then PrimTy.ival u < PrimTy.ival w else PrimTy.ival u ≤ PrimTy.ival w) :
    (F.lessBnd a b strict).Ok g ν := by
  have ru := F.range_sound hF a ha
  have rw' := F.range_sound hF b hb
  unfold InR at ru rw'
  refine ⟨hF.eqs, hF.nes, hF.rets, fun bd hbd v hv => ?_⟩
  simp only [Facts.lessBnd, List.mem_cons] at hbd
  rcases hbd with rfl | rfl | hbd
  · rw [ha] at hv; cases hv
    cases strict <;> simp only [if_true, if_false, Bool.false_eq_true] at h ⊢ <;> constructor <;> omega
  · rw [hb] at hv; cases hv
    cases strict <;> simp only [if_true, if_false, Bool.false_eq_true] at h ⊢ <;> constructor <;> omega
  · exact hF.bnds bd hbd v hv

/-- The premise `x < y` read as `v` (`strict`; `x <= y` without). -/
def Facts.cmpBnds (F : Facts C) {p : PrimTy} (x y : LTm C (.val p)) (strict v : Bool) : Facts C :=
  if v then F.lessBnd x y strict else F.lessBnd y x (!strict)

theorem Facts.cmpBnds_ok {ν : AEnv} {F : Facts C} (hF : F.Ok g ν) {p : PrimTy}
    {x y : LTm C (.val p)} {u w : p.Denote} (hx : (x.eval g ν : Option p.Denote) = some u)
    (hy : (y.eval g ν : Option p.Denote) = some w) (strict v : Bool)
    (hv : v = if strict then decide (PrimTy.ival u < PrimTy.ival w)
      else decide (PrimTy.ival u ≤ PrimTy.ival w)) :
    (F.cmpBnds x y strict v).Ok g ν := by
  unfold Facts.cmpBnds
  split
  · rename_i hvt
    subst hvt
    refine Facts.lessBnd_ok hF hx hy strict ?_
    cases strict <;> simp_all only [Bool.false_eq_true, ↓reduceIte, true_eq_decide_iff]
  · rename_i hvt
    refine Facts.lessBnd_ok hF hy hx (!strict) ?_
    cases v
    · cases strict
      · simp only [Bool.false_eq_true, if_false, Bool.not_false, if_true] at hv ⊢
        have := of_decide_eq_false hv.symm
        omega
      · simp only [if_true, Bool.not_true, Bool.false_eq_true, if_false] at hv ⊢
        have := of_decide_eq_false hv.symm
        omega
    · exact absurd rfl hvt

theorem _root_.Solidity.PrimTy.ival_inj : {p : PrimTy} → {u w : p.Denote} →
    PrimTy.ival u = PrimTy.ival w → u = w
  | .bool, u, w, h => by
    cases hu : (show Bool from u) <;> cases hw : (show Bool from w) <;>
      simp only [PrimTy.ival, hu, hw] at h <;> first | rfl | cases h |
      (exact (show (u : Bool) = w from hu.trans hw.symm))
  | .uint, _, _, h => Subtype.ext h
  | .int, _, _, h => Subtype.ext h

/-- The premise `¬ a = v`, `v` a literal at an edge of `a`'s range: the
range one narrower. -/
def Facts.neEdge (F : Facts C) {p : PrimTy} (a : LTm C (.val p)) (v : p.Denote) : Facts C :=
  let r := F.range a
  if r.1 = PrimTy.ival v then { F with bnds := ⟨p, a, r.1 + 1, r.2⟩ :: F.bnds }
  else if r.2 = PrimTy.ival v then { F with bnds := ⟨p, a, r.1, r.2 - 1⟩ :: F.bnds }
  else F

theorem Facts.neEdge_ok {ν : AEnv} {F : Facts C} (hF : F.Ok g ν) {p : PrimTy}
    {a : LTm C (.val p)} {v : p.Denote}
    (h : ∀ x, (a.eval g ν : Option p.Denote) = some x → x ≠ v) : (F.neEdge a v).Ok g ν := by
  dsimp only [Facts.neEdge]
  have key : ∀ x, (a.eval g ν : Option p.Denote) = some x →
      InR (F.range a) (PrimTy.ival x) ∧ PrimTy.ival x ≠ PrimTy.ival v :=
    fun x hx => ⟨F.range_sound hF a hx, fun e => h x hx (PrimTy.ival_inj e)⟩
  split
  · rename_i he
    refine ⟨hF.eqs, hF.nes, hF.rets, fun b hb x hx => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · obtain ⟨⟨h1, h2⟩, h3⟩ := key x hx
      dsimp only
      constructor <;> omega
    · exact hF.bnds b hb x hx
  · split
    · rename_i _ he
      refine ⟨hF.eqs, hF.nes, hF.rets, fun b hb x hx => ?_⟩
      rcases List.mem_cons.1 hb with rfl | hb
      · obtain ⟨⟨h1, h2⟩, h3⟩ := key x hx
        dsimp only
        constructor <;> omega
      · exact hF.bnds b hb x hx
    · exact hF

/-- The premise `¬ a = b` with a side a literal: the other's range narrowed. -/
def Facts.neBnd (F : Facts C) {p : PrimTy} (a b : LTm C (.val p)) : Facts C :=
  match b.litV?, a.litV? with
  | some v, _ => F.neEdge a v
  | none, some v => F.neEdge b v
  | none, none => F

theorem Facts.neBnd_ok {ν : AEnv} {F : Facts C} (hF : F.Ok g ν) {p : PrimTy}
    {a b : LTm C (.val p)} (h : ¬ (LFml.eq a b).holds g ν) : (F.neBnd a b).Ok g ν := by
  unfold Facts.neBnd
  split
  · rename_i v hv
    refine Facts.neEdge_ok hF fun x hx e => h ((LFml.holds_eq_iff g ν a b).2 ⟨x, hx, ?_⟩)
    rw [LTm.eval_litV? g ν hv, e]
  · rename_i v hv
    refine Facts.neEdge_ok hF fun x hx e => h ((LFml.holds_eq_iff g ν a b).2 ⟨x, ?_, hx⟩)
    rw [LTm.eval_litV? g ν hv, e]
  · exact hF

/-- `x ≠ y` known: the disequation, and the edge of a range it cuts. -/
def Facts.addNe2 (F : Facts C) {p : PrimTy} (x y : LTm C (.val p)) : Facts C :=
  (F.addNe1 x y).neBnd (F.nf x) (F.nf y)

theorem Facts.addNe2_ok {F : Facts C} {ν : AEnv} (hF : F.Ok g ν) {p : PrimTy}
    {a b : LTm C (.val p)} (h : ¬ (LFml.eq a b).holds g ν) : (F.addNe2 a b).Ok g ν := by
  have hn : ¬ (LFml.eq (F.nf a) (F.nf b)).holds g ν := by
    rw [LFml.holds_eq_iff, F.nf_eval hF, F.nf_eval hF, ← LFml.holds_eq_iff]; exact h
  exact Facts.neBnd_ok (Facts.addNe1_ok hF h) hn

/-- The facts a binary symbol on two values gives, read as `v`. -/
def Facts.boolStep (ih : Facts C → LTm C (.val .bool) → Bool → Facts C) (F : Facts C)
    {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) (v : Bool) : Facts C :=
  match o, x, y with
  | .binop .eqB _, x, y => if v then F.addEq1 x y else F.addNe2 x y
  | .binop .neB _, x, y => if v then F.addNe2 x y else F.addEq1 x y
  | @Op2.binop _ .and p _, x, y =>
    if hp : p = .bool then (if v then ih (ih F (hp ▸ x) true) (hp ▸ y) true else F) else F
  | @Op2.binop _ .or p _, x, y =>
    if hp : p = .bool then (if v then F else ih (ih F (hp ▸ x) false) (hp ▸ y) false) else F
  | .binop .lt _, x, y => F.cmpBnds x y true v
  | .binop .le _, x, y => F.cmpBnds x y false v
  | .binop .gt _, x, y => F.cmpBnds y x true v
  | .binop .ge _, x, y => F.cmpBnds y x false v
  | _, _, _ => F

/-- The facts a unary symbol on a value gives, read as `v`. -/
def Facts.boolStep1 (ih : Facts C → LTm C (.val .bool) → Bool → Facts C) (F : Facts C)
    {a s : Srt} (o : Op1 C a s) (x : LTm C a) (v : Bool) : Facts C :=
  match o, x with
  | @Op1.unop _ .not p _, x => if hp : p = .bool then ih F (hp ▸ x) (!v) else F
  | _, _ => F

theorem binopT_eqB {p : PrimTy} {u : p.Denote} {y : Option p.Denote} {v : Bool}
    (h : binopT .eqB rfl u y = some v) : ∃ w, y = some w ∧ v = decide (u = w) := by
  unfold binopT at h
  cases p <;> simp only [BinOp.shortT] at h <;>
  · cases y with
    | none => cases h
    | some w =>
      rw [Option.bind_some, evalT_eqB, Option.some.injEq] at h
      exact ⟨w, rfl, h.symm⟩

theorem binopT_neB {p : PrimTy} {u : p.Denote} {y : Option p.Denote} {v : Bool}
    (h : binopT .neB rfl u y = some v) : ∃ w, y = some w ∧ v = !decide (u = w) := by
  unfold binopT at h
  cases p <;> simp only [BinOp.shortT] at h <;>
  · cases y with
    | none => cases h
    | some w =>
      rw [Option.bind_some, evalT_neB, Option.some.injEq] at h
      exact ⟨w, rfl, h.symm⟩

theorem binopT_and {u : Bool} {y : Option Bool} (h : binopT (p := .bool) .and rfl u y = some true) :
    u = true ∧ y = some true := by
  unfold binopT at h
  cases u
  · cases h
  · cases y with
    | none => cases h
    | some w => cases w <;> first | exact ⟨rfl, rfl⟩ | cases h

theorem binopT_or {u : Bool} {y : Option Bool} (h : binopT (p := .bool) .or rfl u y = some false) :
    u = false ∧ y = some false := by
  unfold binopT at h
  cases u
  · cases y with
    | none => cases h
    | some w => cases w <;> first | exact ⟨rfl, rfl⟩ | cases h
  · cases h

/-- The premise `x = y` where `x == y` reads `v`. -/
theorem Facts.eqB_ok {ν : AEnv} {F : Facts C} (hF : F.Ok g ν) {p : PrimTy}
    {x y : LTm C (.val p)} {u w : p.Denote} (hx : (x.eval g ν : Option p.Denote) = some u)
    (hy : (y.eval g ν : Option p.Denote) = some w) (v : Bool) (hv : v = decide (u = w)) :
    (if v then F.addEq1 x y else F.addNe2 x y).Ok g ν := by
  split
  · rename_i hvt
    rw [hvt, eq_comm, decide_eq_true_iff] at hv
    exact Facts.addEq1_ok hF ((LFml.holds_eq_iff g ν x y).2 ⟨u, hx, hv ▸ hy⟩)
  · rename_i hvt
    refine Facts.addNe2_ok hF fun hh => hvt ?_
    obtain ⟨z, h1, h2⟩ := (LFml.holds_eq_iff g ν x y).1 hh
    rw [hx] at h1; rw [hy] at h2; cases h1; cases h2
    rw [hv]; exact decide_eq_true rfl

theorem Facts.boolStep_ok {ih : Facts C → LTm C (.val .bool) → Bool → Facts C}
    (hih : ∀ {ν : AEnv} {F : Facts C} {c : LTm C (.val .bool)} {v : Bool}, F.Ok g ν →
      (c.eval g ν : Option Bool) = some v → (ih F c v).Ok g ν)
    {ν : AEnv} {F : Facts C} (hF : F.Ok g ν) {a b s : Srt} (o : Op2 C a b s)
    (x : LTm C a) (y : LTm C b) {v : Bool} (hs : s = .val .bool)
    (h : (LTm.app2 o x y).eval g ν = hs ▸ (some v : Option ((Srt.val .bool).Den C g.H))) :
    (F.boolStep ih o x y v).Ok g ν := by
  cases o
  case binop op p hop =>
    rw [LTm.eval_app2] at h
    cases hx : (x.eval g ν : Option p.Denote) with
    | none =>
      rw [hx] at h
      cases op <;> (simp only [BinOp.ret, BinOp.isArith] at hs) <;> cases hs <;> cases h
    | some u =>
      rw [hx] at h
      have h' := h
      cases op
      case eqB =>
        cases hs
        obtain ⟨w, hy, hv⟩ := binopT_eqB h'
        exact Facts.eqB_ok hF hx hy v hv
      case neB =>
        cases hs
        obtain ⟨w, hy, hv⟩ := binopT_neB h'
        simp only [Facts.boolStep]
        have := Facts.eqB_ok hF hx hy (!v) (by rw [hv, Bool.not_not])
        cases v <;> simpa only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true] using this
      case and =>
        cases hs
        simp only [Facts.boolStep]
        split
        · rename_i hp
          subst hp
          split
          · rename_i hv
            subst hv
            obtain ⟨hu, hy⟩ := binopT_and h'
            exact hih (hih hF (by rw [hx, hu])) hy
          · exact hF
        · exact hF
      case or =>
        cases hs
        simp only [Facts.boolStep]
        split
        · rename_i hp
          subst hp
          split
          · exact hF
          · rename_i hv
            simp only [Bool.not_eq_true] at hv
            subst hv
            obtain ⟨hu, hy⟩ := binopT_or h'
            exact hih (hih hF (by rw [hx, hu])) hy
        · exact hF
      case lt | le | gt | ge =>
        cases hs
        have hnum : p.isNumeric = true := by
          cases p <;> first | rfl | cases hop
        simp only [Facts.boolStep]
        rw [Op2.eval_eq_evalM] at h'
        simp only [Op2.evalM, Option.bind_some] at h'
        unfold binopT at h'
        cases hy : (y.eval g ν : Option p.Denote) with
        | none => rw [hy] at h'; cases p <;> cases h'
        | some w =>
          rw [hy] at h'
          cases p with
          | bool => cases hnum
          | uint | int =>
            simp only [BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum,
              Option.some.injEq] at h'
            first
              | exact Facts.cmpBnds_ok hF hx hy true v h'.symm
              | exact Facts.cmpBnds_ok hF hx hy false v h'.symm
              | exact Facts.cmpBnds_ok hF hy hx true v h'.symm
              | exact Facts.cmpBnds_ok hF hy hx false v h'.symm
      all_goals exact hF
  all_goals exact hF

theorem Facts.boolStep1_ok {ih : Facts C → LTm C (.val .bool) → Bool → Facts C}
    (hih : ∀ {ν : AEnv} {F : Facts C} {c : LTm C (.val .bool)} {v : Bool}, F.Ok g ν →
      (c.eval g ν : Option Bool) = some v → (ih F c v).Ok g ν)
    {ν : AEnv} {F : Facts C} (hF : F.Ok g ν) {a s : Srt} (o : Op1 C a s)
    (x : LTm C a) {v : Bool} (hs : s = .val .bool)
    (h : (LTm.app1 o x).eval g ν = hs ▸ (some v : Option ((Srt.val .bool).Den C g.H))) :
    (F.boolStep1 ih o x v).Ok g ν := by
  cases o
  case unop op p hop =>
    cases op
    case not =>
      simp only [Facts.boolStep1]
      split
      · rename_i hp
        subst hp
        cases hs
        rw [LTm.eval_app1] at h
        cases hx : (x.eval g ν : Option Bool) with
        | none => rw [hx] at h; cases h
        | some u =>
          rw [hx] at h
          have hu : (!u) = v := by
            have := h; simp only [show Op1.eval g (.unop .not hop) (some u) = some (!u) from rfl,
              Option.some.injEq] at this; exact this
          exact hih hF (by rw [hx, ← hu, Bool.not_not])
      · exact hF
    all_goals exact hF
  all_goals exact hF

/-- `c` read apart as `v`: by its head symbol. -/
def Facts.boolDecomp (ih : Facts C → LTm C (.val .bool) → Bool → Facts C) (G : Facts C)
    {s : Srt} (c : LTm C s) (v : Bool) : Facts C :=
  match c with
  | .app2 o x y => G.boolStep ih o x y v
  | .app1 o x => G.boolStep1 ih o x v
  | _ => G

theorem Facts.boolDecomp_ok {ih : Facts C → LTm C (.val .bool) → Bool → Facts C}
    (hih : ∀ {ν : AEnv} {F : Facts C} {c : LTm C (.val .bool)} {v : Bool}, F.Ok g ν →
      (c.eval g ν : Option Bool) = some v → (ih F c v).Ok g ν)
    {ν : AEnv} {G : Facts C} (hG : G.Ok g ν) {s : Srt} (c : LTm C s) {v : Bool}
    (hs : s = .val .bool) (h : c.eval g ν = hs ▸ (some v : Option ((Srt.val .bool).Den C g.H))) :
    (G.boolDecomp ih c v).Ok g ν := by
  cases c with
  | app2 o x y => exact Facts.boolStep_ok hih hG o x y hs h
  | app1 o x => exact Facts.boolStep1_ok hih hG o x hs h
  | _ => exact hG

/-- **The premise `c = v`**, `c` boolean: the rewrite, and what `c` says
taken apart, `n` deep.  By the recursor. -/
def Facts.addBool (n : Nat) : Facts C → LTm C (.val .bool) → Bool → Facts C :=
  Nat.rec (motive := fun _ => Facts C → LTm C (.val .bool) → Bool → Facts C)
    (fun F c v => F.addEq1 c (.lit (p := .bool) v))
    (fun _ ih F c v => (F.addEq1 c (.lit (p := .bool) v)).boolDecomp ih c v) n

theorem Facts.addBool_ok (n : Nat) : ∀ {ν : AEnv} {F : Facts C} {c : LTm C (.val .bool)}
    {v : Bool}, F.Ok g ν → (c.eval g ν : Option Bool) = some v → (F.addBool n c v).Ok g ν := by
  induction n with
  | zero =>
    intro ν F c v hF h
    exact Facts.addEq1_ok hF ((LFml.holds_eq_iff g ν c _).2 ⟨v, h, rfl⟩)
  | succ n ih =>
    intro ν F c v hF h
    have hG := Facts.addEq1_ok (a := c) (b := .lit (p := .bool) v) hF
      ((LFml.holds_eq_iff g ν c _).2 ⟨v, h, rfl⟩)
    exact Facts.boolDecomp_ok ih hG c rfl h

/-- `assert(c)` (`ite(c, true, err)`), its condition: by the symbol. -/
def Op3.assertArg {a b c s : Srt} (o : Op3 C a b c s) (x : LTm C a) (y : LTm C b) (z : LTm C c) :
    Option (LTm C (.val .bool)) :=
  match o, x, y, z with
  | .ite, x, y, z => if y.beqR (LTm.tt : LTm C (.val .bool)) && z.isErr then some x else none
  | _, _, _, _ => none

/-- A guard `c = true ? a : err` (`kite(c, true, a, err)`), its
condition. -/
def kiteAssert {p : PrimTy} {s : Srt} (a b : LTm C (.val p)) (e : LTm C s) :
    Option (LTm C (.val .bool)) :=
  match p, a, b with
  | .bool, a, b => if b.beqR (LTm.tt : LTm C (.val .bool)) && e.isErr then some a else none
  | _, _, _ => none

/-- `assert(c)` (`ite(c, true, err)`), or a guard `kite(c, true, a, err)`,
its condition. -/
def assertArg? {s : Srt} (t : LTm C s) : Option (LTm C (.val .bool)) :=
  match t with
  | .app3 o x y z => Op3.assertArg o x y z
  | .kite a b _ e => kiteAssert a b e
  | _ => none

theorem assertArg?_eval {ν : AEnv} {s : Srt} {t : LTm C s} {c : LTm C (.val .bool)}
    (h : assertArg? t = some c) (ht : (t.eval g ν).isSome = true) :
    (c.eval g ν : Option Bool) = some true := by
  cases t with
  | app3 o x y z =>
    simp only [assertArg?] at h
    cases o with
    | ite =>
      simp only [Op3.assertArg] at h
      split at h
      · rename_i hb
        cases h
        simp only [Bool.and_eq_true] at hb
        cases LTm.sigma_eq_of_beqR hb.1
        rw [LTm.eval_app3] at ht
        cases hc : (c.eval g ν : Option Bool) with
        | none => rw [hc] at ht; cases ht
        | some b =>
          rw [hc] at ht
          cases b
          · rw [LTm.eval_of_isErr g ν hb.2] at ht; cases ht
          · rfl
      · cases h
    | _ => simp only [Op3.assertArg, reduceCtorEq] at h
  | @kite p _ a b t e =>
    simp only [assertArg?] at h
    cases p with
    | bool =>
      simp only [kiteAssert] at h
      split at h
      · rename_i hb
        cases h
        simp only [Bool.and_eq_true] at hb
        cases LTm.eq_of_beqR hb.1
        rw [LTm.eval_kite] at ht
        cases hc : (c.eval g ν : Option Bool) with
        | none => rw [hc] at ht; cases ht
        | some x =>
          rw [hc] at ht
          have htt : ((LTm.tt : LTm C (.val .bool)).eval g ν : Option Bool) = some true := rfl
          simp only [htt, Option.bind_some] at ht
          by_cases hx : x = true
          · rw [hx]
          · rw [if_neg hx, LTm.eval_of_isErr g ν hb.2] at ht; cases ht
      · cases h
    | uint | int => simp only [kiteAssert, reduceCtorEq] at h
  | _ => simp only [assertArg?, reduceCtorEq] at h

/-- How deep a boolean premise is taken apart. -/
def boolFuel : Nat := 2

/-- The conditions of the `assert`s among terms that return, each `true`. -/
def Facts.addAsserts (F : Facts C) (ts : List ((s : Srt) × LTm C s)) : Facts C :=
  ts.foldl (fun G u => match assertArg? u.2 with
    | some c => G.addBool boolFuel c true
    | none => G) F

theorem Facts.addAsserts_ok {ν : AEnv} : (ts : List ((s : Srt) × LTm C s)) → {F : Facts C} →
    F.Ok g ν → (∀ u ∈ ts, (u.2.eval g ν).isSome = true) → (F.addAsserts ts).Ok g ν
  | [], _, hF, _ => hF
  | u :: ts, F, hF, h => by
    simp only [Facts.addAsserts, List.foldl_cons]
    refine Facts.addAsserts_ok ts ?_ fun w hw => h w (List.mem_cons_of_mem _ hw)
    split
    · rename_i c hc
      exact Facts.addBool_ok _ hF (assertArg?_eval hc (h u List.mem_cons_self))
    · exact hF

/-- Every fact read again under the others: each rewrite normalized under
the rewrites newer than it and the pairs apart, each pair apart under the
rewrites, each term that returns under all (KeY's `applyEq` on the
antecedent). -/
def Facts.rebuild (F : Facts C) : Facts C :=
  let G1 := F.eqs.foldl (fun G e => G.addEqR e.l e.r) { F with eqs := [] }
  let G2 := F.nes.foldl (fun G e => G.addNe1 e.l e.r) { G1 with nes := [] }
  { G2 with rets := G2.rets.map fun u => ⟨u.1, G2.nf u.2⟩,
            bnds := G2.bnds.map fun b => { b with t := G2.nf b.t } }

theorem Facts.foldl_addEqR_ok {ν : AEnv} : (es : List (EqF C)) → {G : Facts C} → G.Ok g ν →
    (∀ e ∈ es, ∃ x, (e.l.eval g ν : Option e.p.Denote) = some x ∧ e.r.eval g ν = some x) →
    (es.foldl (fun G e => G.addEqR e.l e.r) G).Ok g ν
  | [], _, hG, _ => hG
  | e :: es, G, hG, h => by
    simp only [List.foldl_cons]
    refine Facts.foldl_addEqR_ok es ?_ fun e' he' => h e' (List.mem_cons_of_mem _ he')
    obtain ⟨x, h1, h2⟩ := h e List.mem_cons_self
    exact Facts.addEqR_ok hG ((LFml.holds_eq_iff g ν e.l e.r).2 ⟨x, h1, h2⟩)

theorem Facts.foldl_addNe1_ok {ν : AEnv} : (es : List (EqF C)) → {G : Facts C} → G.Ok g ν →
    (∀ e ∈ es, ∃ x y, (e.l.eval g ν : Option e.p.Denote) = some x ∧ e.r.eval g ν = some y ∧
      x ≠ y) →
    (es.foldl (fun G e => G.addNe1 e.l e.r) G).Ok g ν
  | [], _, hG, _ => hG
  | e :: es, G, hG, h => by
    simp only [List.foldl_cons]
    refine Facts.foldl_addNe1_ok es ?_ fun e' he' => h e' (List.mem_cons_of_mem _ he')
    obtain ⟨x, y, h1, h2, hne⟩ := h e List.mem_cons_self
    refine Facts.addNe1_ok hG fun hh => ?_
    obtain ⟨z, k1, k2⟩ := (LFml.holds_eq_iff g ν e.l e.r).1 hh
    rw [h1] at k1; rw [h2] at k2; cases k1; cases k2
    exact hne rfl

theorem Facts.rebuild_ok {ν : AEnv} {F : Facts C} (hF : F.Ok g ν) : F.rebuild.Ok g ν := by
  have h0 : ({ F with eqs := [] } : Facts C).Ok g ν :=
    ⟨fun _ h => (nomatch h), hF.nes, hF.rets, hF.bnds⟩
  have h1 := Facts.foldl_addEqR_ok F.eqs h0 hF.eqs
  have h1' : ({ F.eqs.foldl (fun G e => G.addEqR e.l e.r) { F with eqs := [] } with nes := [] } :
      Facts C).Ok g ν := ⟨h1.eqs, fun _ h => (nomatch h), h1.rets, h1.bnds⟩
  have h2 := Facts.foldl_addNe1_ok F.nes h1' hF.nes
  refine ⟨h2.eqs, h2.nes, fun u hu => ?_, fun b hb v hv => ?_⟩
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
    show ((Facts.nf _ w.2).eval g ν).isSome = true
    rw [Facts.nf_eval h2]
    exact h2.rets w hw
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hb
    have hv' : (w.t.eval g ν : Option w.p.Denote) = some v := by
      rw [← Facts.nf_eval h2]; exact hv
    exact h2.bnds w hw v hv'

/-- `p = v` at `bool`, a side a literal: the other side and `v`. -/
def boolLit? {p : PrimTy} (a b : LTm C (.val p)) : Option (LTm C (.val .bool) × Bool) :=
  match p, a, b with
  | .bool, a, b =>
    match b.litV? with
    | some v => some (a, v)
    | none =>
      match a.litV? with
      | some v => some (b, v)
      | none => none
  | _, _, _ => none

theorem boolLit?_eval {ν : AEnv} {p : PrimTy} {a b : LTm C (.val p)} {c : LTm C (.val .bool)}
    {v : Bool} (h : boolLit? a b = some (c, v)) (hh : (LFml.eq a b).holds g ν) :
    (c.eval g ν : Option Bool) = some v := by
  cases p with
  | bool =>
    obtain ⟨x, ha, hb⟩ := (LFml.holds_eq_iff g ν a b).1 hh
    simp only [boolLit?] at h
    split at h
    · rename_i w hw
      cases h
      rw [LTm.eval_litV? g ν hw] at hb
      cases hb; exact ha
    · split at h
      · rename_i w hw
        cases h
        rw [LTm.eval_litV? g ν hw] at ha
        cases ha; exact hb
      · cases h
  | uint | int => simp only [boolLit?, reduceCtorEq] at h

/-- **The premise `a = b`**: `addEq1`, the `assert`s among its terms, a
boolean side read apart, and the facts read again (`rebuild`). -/
def Facts.addEqn (F : Facts C) {p : PrimTy} (a b : LTm C (.val p)) : Facts C :=
  let F1 := (F.addEq1 a b).addAsserts ((F.nf a).strict ++ (F.nf b).strict)
  let F2 := match boolLit? (F.nf a) (F.nf b) with
    | some (c, v) => F1.addBool boolFuel c v
    | none => F1
  F2.rebuild

theorem Facts.addEqn_ok {F : Facts C} {ν : AEnv} (hF : F.Ok g ν) {p : PrimTy}
    {a b : LTm C (.val p)} (h : (LFml.eq a b).holds g ν) : (F.addEqn a b).Ok g ν := by
  obtain ⟨x, ha, hb⟩ := (LFml.holds_eq_iff g ν a b).1 h
  have hn : (LFml.eq (F.nf a) (F.nf b)).holds g ν := by
    rw [LFml.holds_eq_iff, F.nf_eval hF, F.nf_eval hF]; exact ⟨x, ha, hb⟩
  rw [← F.nf_eval hF] at ha hb
  have h1 := Facts.addAsserts_ok (F := F.addEq1 a b) ((F.nf a).strict ++ (F.nf b).strict)
    (Facts.addEq1_ok hF h) fun u hu => by
      rcases List.mem_append.1 hu with hu | hu
      · exact LTm.strict_isSome ν _ (by rw [ha]; rfl) u hu
      · exact LTm.strict_isSome ν _ (by rw [hb]; rfl) u hu
  refine Facts.rebuild_ok ?_
  split
  · rename_i c v hc
    exact Facts.addBool_ok _ h1 (boolLit?_eval hc hn)
  · exact h1

/-- **The premise `¬ a = b`**: `addNe1`, a boolean side read apart, and the
facts read again. -/
def Facts.addNeq (F : Facts C) {p : PrimTy} (a b : LTm C (.val p)) : Facts C :=
  let F1 := (F.addNe1 a b).neBnd (F.nf a) (F.nf b)
  let F2 := match boolLit? (F.nf a) (F.nf b) with
    | some (c, v) => if F.returns c then F1.addBool boolFuel c (!v) else F1
    | none => F1
  F2.rebuild

theorem boolLit?_neg {ν : AEnv} {p : PrimTy} {a b : LTm C (.val p)} {c : LTm C (.val .bool)}
    {v w : Bool} (h : boolLit? a b = some (c, v)) (hh : ¬ (LFml.eq a b).holds g ν)
    (hw : (c.eval g ν : Option Bool) = some w) : w = !v := by
  cases p with
  | bool =>
    simp only [boolLit?] at h
    split at h
    · rename_i u hu
      cases h
      refine Bool.eq_not.2 fun e => hh ((LFml.holds_eq_iff g ν c b).2 ⟨w, hw, ?_⟩)
      rw [LTm.eval_litV? g ν hu, e]
    · split at h
      · rename_i u _ hu
        cases h
        refine Bool.eq_not.2 fun e => hh ((LFml.holds_eq_iff g ν a c).2 ⟨w, ?_, hw⟩)
        rw [LTm.eval_litV? g ν hu, e]
      · cases h
  | uint | int => simp only [boolLit?, reduceCtorEq] at h

theorem Facts.addNeq_ok {F : Facts C} {ν : AEnv} (hF : F.Ok g ν) {p : PrimTy}
    {a b : LTm C (.val p)} (h : ¬ (LFml.eq a b).holds g ν) : (F.addNeq a b).Ok g ν := by
  have hn : ¬ (LFml.eq (F.nf a) (F.nf b)).holds g ν := by
    rw [LFml.holds_eq_iff, F.nf_eval hF, F.nf_eval hF, ← LFml.holds_eq_iff]; exact h
  have h1 := Facts.neBnd_ok (Facts.addNe1_ok hF h) hn
  refine Facts.rebuild_ok ?_
  split
  · rename_i c v hc
    split
    · rename_i hr
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF c hr)
      exact Facts.addBool_ok _ h1 (by rw [hw, boolLit?_neg hc hn hw])
    · exact h1
  · exact h1

end Premises

/-! ## Closing a leaf -/

section Close

variable {g : State C []}

/-- A `bool` atom to split on: `x = true` or not. -/
def boolSplit (p : PrimTy) (k : Nat) : Option (EqF C) :=
  match p with
  | .bool => some ⟨.bool, .var k, .tt⟩
  | _ => none

/-- `LTm.pick`'s compiled twin. -/
def LTm.pickM (F : Facts C) : {s : Srt} → LTm C s → Option (EqF C)
  | _, @LTm.var _ p k => boolSplit p k
  | _, .app0 _ | _, .err => none
  | _, .app1 _ x => x.pickM F
  | _, .app2 _ x y => x.pickM F <|> y.pickM F
  | _, .app3 _ x y z => x.pickM F <|> y.pickM F <|> z.pickM F
  | _, .index _ q i => q.pickM F <|> i.pickM F
  | _, .obsW q | _, .obsL q | _, .obsH q => q.pickM F
  | _, .seq d a => d.pickM F <|> a.pickM F
  | _, .orElse a b => a.pickM F <|> b.pickM F
  | _, @LTm.kite _ p _ a b t e =>
    a.pickM F <|> b.pickM F <|> (if F.returns a && F.returns b then some ⟨p, a, b⟩ else none) <|>
      t.pickM F <|> e.pickM F

/-- **A key comparison to split on**: the first conditional whose keys
return, the innermost first.  By the recursor. -/
@[implemented_by LTm.pickM]
def LTm.pick (F : Facts C) {s : Srt} (t : LTm C s) : Option (EqF C) :=
  @LTm.rec C (fun _ _ => Option (EqF C))
    (@fun p k => boolSplit p k) (@fun _ _ => none)
    (@fun _ _ _ _ ihx => ihx)
    (@fun _ _ _ _ _ _ ihx ihy => ihx <|> ihy)
    (@fun _ _ _ _ _ _ _ _ ihx ihy ihz => ihx <|> ihy <|> ihz)
    (@fun _ _ _ _ _ _ ihq ihi => ihq <|> ihi)
    (@fun _ _ ih => ih) (@fun _ _ ih => ih) (@fun _ _ ih => ih)
    (@fun _ _ _ _ ihd iha => ihd <|> iha)
    (@fun _ _ _ iha ihb => iha <|> ihb)
    (@fun p _ a b _ _ iha ihb iht ihe =>
      iha <|> ihb <|> (if F.returns a && F.returns b then some ⟨p, a, b⟩ else none) <|> iht <|> ihe)
    (@fun _ => none) s t

theorem LTm.pick_eq_pickM (F : Facts C) {s : Srt} (t : LTm C s) : t.pick F = t.pickM F := by
  induction t with
  | var | app0 | err => rfl
  | app1 o x ih | obsW x ih | obsL x ih | obsH x ih => simp only [LTm.pickM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [LTm.pickM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [LTm.pickM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => simp only [LTm.pickM, ← ihq, ← ihi]; rfl
  | seq d a ihd iha => simp only [LTm.pickM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => simp only [LTm.pickM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe => simp only [LTm.pickM, ← iha, ← ihb, ← iht, ← ihe]; rfl

/-- `a = b` by the normal forms: one term, which returns. -/
def Facts.direct (F : Facts C) {p : PrimTy} (a b : LTm C (.val p)) : Bool :=
  (F.nf a).beqR (F.nf b) && F.returns (F.nf a)

theorem Facts.direct_sound {F : Facts C} {ν : AEnv} (hF : F.Ok g ν) {p : PrimTy}
    {a b : LTm C (.val p)} (h : F.direct a b = true) : (LFml.eq a b).holds g ν := by
  simp only [Facts.direct, Bool.and_eq_true] at h
  have e := LTm.eq_of_beqR h.1
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF _ h.2)
  have hb := hx
  rw [e] at hb
  rw [F.nf_eval hF] at hx hb
  exact (LFml.holds_eq_iff g ν a b).2 ⟨x, hx, hb⟩

/-- `a = b` by the normal forms, splitting on a key comparison at most
`n` deep (KeY's `cut` on `k = j`).  By the recursor. -/
def Facts.proveEqN {p : PrimTy} (a b : LTm C (.val p)) (n : Nat) : Facts C → Bool :=
  Nat.rec (motive := fun _ => Facts C → Bool) (fun F => F.direct a b)
    (fun _ ih F => F.direct a b ||
      match (F.nf a).pick F <|> (F.nf b).pick F with
      | some e => F.returns e.l && F.returns e.r && ih (F.addEqn e.l e.r) && ih (F.addNeq e.l e.r)
      | none => false) n

theorem Facts.proveEqN_sound {p : PrimTy} (a b : LTm C (.val p)) (n : Nat) :
    ∀ {ν : AEnv} {F : Facts C}, F.Ok g ν → Facts.proveEqN a b n F = true →
      (LFml.eq a b).holds g ν := by
  induction n with
  | zero => intro ν F hF h; exact F.direct_sound hF h
  | succ n ih =>
    intro ν F hF h
    simp only [Facts.proveEqN, Bool.or_eq_true] at h
    rcases h with h | h
    · exact F.direct_sound hF h
    · split at h
      · rename_i e _
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨⟨hl, hr⟩, h1⟩, h2⟩ := h
        by_cases he : (LFml.eq e.l e.r).holds g ν
        · exact ih (Facts.addEqn_ok hF he) h1
        · exact ih (Facts.addNeq_ok hF he) h2
      · cases h

/-- How deep `proveEqN` splits. -/
def closeFuel : Nat := 3

/-- `a = b` is false by the normal forms: two literals that differ, a
pair the facts hold apart, or a side that halts. -/
def Facts.refuteEq (F : Facts C) {p : PrimTy} (a b : LTm C (.val p)) : Bool :=
  let a' := F.nf a
  let b' := F.nf b
  (match a'.litV?, b'.litV? with
    | some x, some y => !decide (x = y)
    | _, _ => false) || F.apart a' b' || a'.isErr || b'.isErr ||
    decide ((F.range a').2 < (F.range b').1) || decide ((F.range b').2 < (F.range a').1)

theorem Facts.refuteEq_sound {F : Facts C} {ν : AEnv} (hF : F.Ok g ν) {p : PrimTy}
    {a b : LTm C (.val p)} (h : F.refuteEq a b = true) : ¬ (LFml.eq a b).holds g ν := by
  intro hh
  obtain ⟨x, ha, hb⟩ := (LFml.holds_eq_iff g ν a b).1 hh
  rw [← F.nf_eval hF] at ha hb
  simp only [Facts.refuteEq, Bool.or_eq_true] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · split at h
    · rename_i u v hu hv
      rw [LTm.eval_litV? g ν hu] at ha
      rw [LTm.eval_litV? g ν hv] at hb
      cases ha; cases hb
      simp only [decide_true, Bool.not_true, Bool.false_eq_true] at h
    · cases h
  · obtain ⟨u, v, hu, hv, hne⟩ := F.apart_sound hF h
    rw [ha] at hu; rw [hb] at hv
    cases hu; cases hv
    exact hne rfl
  · rw [LTm.eval_of_isErr g ν h] at ha; cases ha
  · rw [LTm.eval_of_isErr g ν h] at hb; cases hb
  · have r1 := F.range_sound hF _ ha
    have r2 := F.range_sound hF _ hb
    unfold InR at r1 r2
    have := of_decide_eq_true h
    omega
  · have r1 := F.range_sound hF _ ha
    have r2 := F.range_sound hF _ hb
    unfold InR at r1 r2
    have := of_decide_eq_true h
    omega

theorem Facts.ok_empty (ν : AEnv) : ({} : Facts C).Ok g ν := by
  exact ⟨fun _ h => (nomatch h), fun _ h => (nomatch h), fun _ h => (nomatch h),
    fun _ h => (nomatch h)⟩

/-- What a formula is to the closer under the facts: whether they prove
it, whether they refute it, and the facts with it assumed true and assumed
false. -/
structure Verdict (C : Contract) where
  prove : Bool
  refute : Bool
  yes : Facts C
  no : Facts C

mutual
/-- `LFml.verdict`'s compiled twin, its four parts each by itself, so that
compiled code computes only the parts it reads. -/
def LFml.proveM : LFml C → Facts C → Bool
  | .tt, _ => true
  | .eq a b, F => Facts.proveEqN a b closeFuel F
  | .not φ, F => φ.refuteM F
  | .and φ ψ, F => φ.proveM F && ψ.proveM (φ.yesM F)
  | .imp φ ψ, F => φ.refuteM F || ψ.proveM (φ.yesM F)
  | .all k _ φ, F => φ.proveM (F.drop k)

/-- `LFml.verdict`'s refutation, compiled. -/
def LFml.refuteM : LFml C → Facts C → Bool
  | .tt, _ => false
  | .eq a b, F => F.refuteEq a b
  | .not φ, F => φ.proveM F
  | .and φ ψ, F => φ.refuteM F || ψ.refuteM (φ.yesM F)
  | .imp φ ψ, F => φ.proveM F && ψ.refuteM (φ.yesM F)
  | .all _ _ _, _ => false

/-- `LFml.verdict`'s facts with the formula true, compiled. -/
def LFml.yesM : LFml C → Facts C → Facts C
  | .tt, F => F
  | .eq a b, F => F.addEqn a b
  | .not φ, F => φ.noM F
  | .and φ ψ, F => ψ.yesM (φ.yesM F)
  | .imp φ ψ, F => if φ.proveM F then ψ.yesM F else F
  | .all _ _ _, F => F

/-- `LFml.verdict`'s facts with the formula false, compiled. -/
def LFml.noM : LFml C → Facts C → Facts C
  | .tt, F => F
  | .eq a b, F => F.addNeq a b
  | .not φ, F => φ.yesM F
  | .and φ ψ, F => if φ.proveM F then ψ.noM F else if ψ.proveM F then φ.noM F else F
  | .imp φ ψ, F => ψ.noM (φ.yesM F)
  | .all _ _ _, F => F
end

/-- **The closer on a formula**: whether the facts prove it, whether they
refute it, and the facts with it assumed true and false (KeY's `impRight`,
`andLeft`, `notLeft`, `impLeft`, `applyEq`, `closeFalse`, `allRight`).  By
the recursor. -/
noncomputable def LFml.verdict (φ : LFml C) : Facts C → Verdict C :=
  @LFml.rec C (fun _ => Facts C → Verdict C)
    (fun F => ⟨true, false, F, F⟩)
    (@fun _ a b F => ⟨Facts.proveEqN a b closeFuel F, F.refuteEq a b, F.addEqn a b, F.addNeq a b⟩)
    (fun _ ih F => ⟨(ih F).refute, (ih F).prove, (ih F).no, (ih F).yes⟩)
    (fun _ _ ihφ ihψ F =>
      ⟨(ihφ F).prove && (ihψ (ihφ F).yes).prove, (ihφ F).refute || (ihψ (ihφ F).yes).refute,
        (ihψ (ihφ F).yes).yes,
        if (ihφ F).prove then (ihψ F).no else if (ihψ F).prove then (ihφ F).no else F⟩)
    (fun _ _ ihφ ihψ F =>
      ⟨(ihφ F).refute || (ihψ (ihφ F).yes).prove, (ihφ F).prove && (ihψ (ihφ F).yes).refute,
        if (ihφ F).prove then (ihψ F).yes else F, (ihψ (ihφ F).yes).no⟩)
    (fun k _ _ ih F => ⟨(ih (F.drop k)).prove, false, F, F⟩) φ

theorem LFml.verdict_eq_M (φ : LFml C) (F : Facts C) :
    φ.verdict F = ⟨φ.proveM F, φ.refuteM F, φ.yesM F, φ.noM F⟩ := by
  induction φ generalizing F with
  | tt | eq => rfl
  | not φ ih =>
    show (⟨(φ.verdict F).refute, (φ.verdict F).prove, (φ.verdict F).no, (φ.verdict F).yes⟩ :
      Verdict C) = _
    rw [ih]; rfl
  | and φ ψ ihφ ihψ =>
    show (⟨(φ.verdict F).prove && (ψ.verdict (φ.verdict F).yes).prove,
      (φ.verdict F).refute || (ψ.verdict (φ.verdict F).yes).refute,
      (ψ.verdict (φ.verdict F).yes).yes,
      if (φ.verdict F).prove then (ψ.verdict F).no
      else if (ψ.verdict F).prove then (φ.verdict F).no else F⟩ : Verdict C) = _
    rw [ihφ, ihψ, ihψ]; simp only [LFml.proveM, LFml.refuteM, LFml.yesM, LFml.noM]
  | imp φ ψ ihφ ihψ =>
    show (⟨(φ.verdict F).refute || (ψ.verdict (φ.verdict F).yes).prove,
      (φ.verdict F).prove && (ψ.verdict (φ.verdict F).yes).refute,
      if (φ.verdict F).prove then (ψ.verdict F).yes else F,
      (ψ.verdict (φ.verdict F).yes).no⟩ : Verdict C) = _
    rw [ihφ, ihψ, ihψ]; simp only [LFml.proveM, LFml.refuteM, LFml.yesM, LFml.noM]
  | all k p φ ih =>
    show (⟨(φ.verdict (F.drop k)).prove, false, F, F⟩ : Verdict C) = _
    rw [ih]; simp only [LFml.proveM, LFml.refuteM, LFml.yesM, LFml.noM]

/-- **The verdict is sound**: what it proves holds, what it refutes does
not, and what it assumes keeps the facts. -/
theorem LFml.verdict_sound (φ : LFml C) : ∀ (ν : AEnv) (F : Facts C), F.Ok g ν →
    ((φ.verdict F).prove = true → φ.holds g ν) ∧ ((φ.verdict F).refute = true → ¬ φ.holds g ν) ∧
      (φ.holds g ν → (φ.verdict F).yes.Ok g ν) ∧ (¬ φ.holds g ν → (φ.verdict F).no.Ok g ν) := by
  induction φ with
  | tt => intro ν F hF; exact ⟨fun _ => trivial, (fun h => by cases h), fun _ => hF, fun _ => hF⟩
  | eq a b =>
    intro ν F hF
    exact ⟨Facts.proveEqN_sound a b closeFuel hF, Facts.refuteEq_sound hF,
      Facts.addEqn_ok hF, Facts.addNeq_ok hF⟩
  | not φ ih =>
    intro ν F hF
    obtain ⟨h1, h2, h3, h4⟩ := ih ν F hF
    exact ⟨h2, fun h hn => hn (h1 h), h4, fun hn => h3 (Classical.not_not.1 hn)⟩
  | and φ ψ ihφ ihψ =>
    intro ν F hF
    obtain ⟨h1, h2, h3, h4⟩ := ihφ ν F hF
    obtain ⟨k1, _, _, k4⟩ := ihψ ν F hF
    refine ⟨fun h => ?_, fun h hh => ?_, fun hh => ?_, fun hn => ?_⟩
    · simp only [LFml.verdict, Bool.and_eq_true] at h
      have hp : φ.holds g ν := h1 h.1
      exact ⟨hp, (ihψ ν _ (h3 hp)).1 h.2⟩
    · simp only [LFml.verdict, Bool.or_eq_true] at h
      rcases h with h | h
      · exact h2 h hh.1
      · exact (ihψ ν _ (h3 hh.1)).2.1 h hh.2
    · exact (ihψ ν _ (h3 hh.1)).2.2.1 hh.2
    · show (if (φ.verdict F).prove then (ψ.verdict F).no
        else if (ψ.verdict F).prove then (φ.verdict F).no else F).Ok g ν
      split
      · rename_i hp
        exact k4 fun hq => hn ⟨h1 hp, hq⟩
      · split
        · rename_i hq
          exact h4 fun hp => hn ⟨hp, k1 hq⟩
        · exact hF
  | imp φ ψ ihφ ihψ =>
    intro ν F hF
    obtain ⟨h1, h2, h3, _⟩ := ihφ ν F hF
    obtain ⟨_, _, k3, _⟩ := ihψ ν F hF
    refine ⟨fun h hp => ?_, fun h hh => ?_, fun hh => ?_, fun hn => ?_⟩
    · simp only [LFml.verdict, Bool.or_eq_true] at h
      rcases h with h | h
      · exact absurd hp (h2 h)
      · exact (ihψ ν _ (h3 hp)).1 h
    · simp only [LFml.verdict, Bool.and_eq_true] at h
      have hp : φ.holds g ν := h1 h.1
      exact (ihψ ν _ (h3 hp)).2.1 h.2 (hh hp)
    · show (if (φ.verdict F).prove then (ψ.verdict F).yes else F).Ok g ν
      split
      · rename_i hp
        exact k3 (hh (h1 hp))
      · exact hF
    · have hp : φ.holds g ν := Classical.byContradiction fun hp => hn fun h => absurd h hp
      exact (ihψ ν _ (h3 hp)).2.2.2 fun hq => hn fun _ => hq
  | all k p φ ih =>
    intro ν F hF
    refine ⟨fun h v => ?_, (fun h => by cases h), fun _ => hF, fun _ => hF⟩
    exact (ih (ν.set p k v) (F.drop k) (Facts.drop_ok hF k p v)).1 h

/-- `LFml.close`'s compiled twin. -/
def LFml.closeM (φ : LFml C) : Bool := φ.proveM {}

/-- **The closer**: the facts of no premise prove the formula. -/
@[implemented_by LFml.closeM]
def LFml.close (φ : LFml C) : Bool := (φ.verdict {}).prove

theorem LFml.close_eq_closeM (φ : LFml C) : φ.close = φ.closeM := by
  rw [LFml.close, LFml.verdict_eq_M]; rfl

/-- **What the closer closes is valid.** -/
theorem LFml.close_valid {φ : LFml C} (h : φ.close = true) : φ.Valid := fun g ν =>
  (φ.verdict_sound ν {} (Facts.ok_empty ν)).1 h

end Close

end Decide

end Solidity
