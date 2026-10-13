import Solidity.Calculus.DecideLang
import Solidity.Calculus.TermEq

/-!
# The closer: a reduction closed by its terms

`sol_prove`'s leaves, reduced (`Fml.reduceS`), are typed first-order
formulas over the starting state (`LFml`, `Calculus/DecideLang.lean`).
KeY closes them with its simplification taclets, each a proof step; here
they are clauses of one function, `LFml.close`, proved sound once
(`LFml.close_valid`), so that the kernel checks a leaf by evaluation.

What it knows at a point of a leaf is a `Facts`: terms that return, pairs
of terms equal (a rewrite, left to right: KeY's `applyEq`) or apart.  A
premise adds to it (`Facts.assume`); a term is read in its normal form
under the facts (`Facts.nf`): every symbol on literals evaluated (KeY's
literal and `intSimplification` taclets), a guard that returns dropped, a
key compared with itself or with one it is apart from read as its branch
(`select(store(h, k, v), j)` under `k = j` or `k ≠ j`), and a subterm the
premises know rewritten.  A conclusion `a ≐ b` holds where the two normal
forms are one term that returns; where a key comparison is left open, the
closer splits on it (`Facts.split`, KeY's `cut` on `k = j`).

Since W10.4 the terms are typed: a value is in range by its type, the
storage has the shape its contract declares, so no layout premise and no
kind test is left to the closer.

The functions the kernel evaluates are written with their recursors, each
with a `match` twin for compiled code (Gate G0).
-/

namespace Solidity

namespace Decide

variable {C : Contract}

/-! ## Terms compared -/

section Beq

/-- `LTm.beqR`'s compiled twin. -/
def LTm.beqM : {s s' : Srt} → LTm C s → LTm C s' → Bool
  | _, _, @LTm.var _ p k, t' => match t' with
    | @LTm.var _ p' k' => p == p' && k == k'
    | _ => false
  | _, _, .app0 o, t' => match t' with
    | .app0 o' => Op0.hbeq o o'
    | _ => false
  | _, _, .app1 o x, t' => match t' with
    | .app1 o' x' => Op1.hbeq o o' && x.beqM x'
    | _ => false
  | _, _, .app2 o x y, t' => match t' with
    | .app2 o' x' y' => Op2.hbeq o o' && x.beqM x' && y.beqM y'
    | _ => false
  | _, _, .app3 o x y z, t' => match t' with
    | .app3 o' x' y' z' => Op3.hbeq o o' && x.beqM x' && y.beqM y' && z.beqM z'
    | _ => false
  | _, _, @LTm.index _ R k V _ q i, t' => match t' with
    | @LTm.index _ R' k' V' _ q' i' => decide (R = R' ∧ k = k' ∧ V = V') && q.beqM q' && i.beqM i'
    | _ => false
  | _, _, .obsW q, t' => match t' with
    | .obsW q' => q.beqM q'
    | _ => false
  | _, _, .obsL q, t' => match t' with
    | .obsL q' => q.beqM q'
    | _ => false
  | _, _, .obsH q, t' => match t' with
    | .obsH q' => q.beqM q'
    | _ => false
  | _, _, .seq d a, t' => match t' with
    | .seq d' a' => d.beqM d' && a.beqM a'
    | _ => false
  | _, _, .orElse a b, t' => match t' with
    | .orElse a' b' => a.beqM a' && b.beqM b'
    | _ => false
  | _, _, .kite a b t e, t' => match t' with
    | .kite a' b' t'' e' => a.beqM a' && b.beqM b' && t.beqM t'' && e.beqM e'
    | _ => false
  | s, _, .err, t' => match t' with
    | @LTm.err _ s' => s == s'
    | _ => false

/-- **Structural equality of two terms**, their sorts compared too, by the
recursor. -/
@[implemented_by LTm.beqM]
def LTm.beqR {s s' : Srt} (t : LTm C s) (t' : LTm C s') : Bool :=
  @LTm.rec C (fun _ _ => {s' : Srt} → LTm C s' → Bool)
    (@fun p k _ t' => match t' with
      | @LTm.var _ p' k' => p == p' && k == k'
      | _ => false)
    (@fun _ o _ t' => match t' with
      | .app0 o' => Op0.hbeq o o'
      | _ => false)
    (@fun _ _ o _ ih _ t' => match t' with
      | .app1 o' x' => Op1.hbeq o o' && ih x'
      | _ => false)
    (@fun _ _ _ o _ _ ihx ihy _ t' => match t' with
      | .app2 o' x' y' => Op2.hbeq o o' && ihx x' && ihy y'
      | _ => false)
    (@fun _ _ _ _ o _ _ _ ihx ihy ihz _ t' => match t' with
      | .app3 o' x' y' z' => Op3.hbeq o o' && ihx x' && ihy y' && ihz z'
      | _ => false)
    (@fun R k V _ _ _ ihq ihi _ t' => match t' with
      | @LTm.index _ R' k' V' _ q' i' => decide (R = R' ∧ k = k' ∧ V = V') && ihq q' && ihi i'
      | _ => false)
    (@fun _ _ ih _ t' => match t' with
      | .obsW q' => ih q'
      | _ => false)
    (@fun _ _ ih _ t' => match t' with
      | .obsL q' => ih q'
      | _ => false)
    (@fun _ _ ih _ t' => match t' with
      | .obsH q' => ih q'
      | _ => false)
    (@fun _ _ _ _ ihd iha _ t' => match t' with
      | .seq d' a' => ihd d' && iha a'
      | _ => false)
    (@fun _ _ _ iha ihb _ t' => match t' with
      | .orElse a' b' => iha a' && ihb b'
      | _ => false)
    (@fun _ _ _ _ _ _ iha ihb iht ihe _ t' => match t' with
      | .kite a' b' t'' e' => iha a' && ihb b' && iht t'' && ihe e'
      | _ => false)
    (@fun s _ t' => match t' with
      | @LTm.err _ s' => s == s'
      | _ => false) s t s' t'

theorem LTm.beqR_eq_beqM {s s' : Srt} (t : LTm C s) (t' : LTm C s') : t.beqR t' = t.beqM t' := by
  induction t generalizing s' with
  | var | app0 | err => cases t' <;> rfl
  | app1 o x ih => cases t' <;> first | rfl | (simp only [LTm.beqM, ← ih]; rfl)
  | app2 o x y ihx ihy => cases t' <;> first | rfl | (simp only [LTm.beqM, ← ihx, ← ihy]; rfl)
  | app3 o x y z ihx ihy ihz =>
    cases t' <;> first | rfl | (simp only [LTm.beqM, ← ihx, ← ihy, ← ihz]; rfl)
  | index it q i ihq ihi => cases t' <;> first | rfl | (simp only [LTm.beqM, ← ihq, ← ihi]; rfl)
  | obsW q ih | obsL q ih | obsH q ih => cases t' <;> first | rfl | (simp only [LTm.beqM, ← ih]; rfl)
  | seq d a ihd iha => cases t' <;> first | rfl | (simp only [LTm.beqM, ← ihd, ← iha]; rfl)
  | orElse a b iha ihb => cases t' <;> first | rfl | (simp only [LTm.beqM, ← iha, ← ihb]; rfl)
  | kite a b t e iha ihb iht ihe =>
    cases t' <;> first | rfl | (simp only [LTm.beqM, ← iha, ← ihb, ← iht, ← ihe]; rfl)

/-- What `beqM` accepts is one term, its sort and all. -/
theorem LTm.eq_of_beqM {s s' : Srt} (t : LTm C s) (t' : LTm C s') (h : t.beqM t' = true) :
    (⟨s, t⟩ : (s : Srt) × LTm C s) = ⟨s', t'⟩ := by
  induction t generalizing s' with
  | var k =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | app0 o =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true] at h
    cases eq_of_hbeqAt h
    rfl
  | err =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true, beq_iff_eq] at h
    cases h
    rfl
  | app1 o x ih =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases ih _ h2
    cases Op1.eq_of_hbeq h1
    rfl
  | app2 o x y ihx ihy =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases ihx _ h2
    cases ihy _ h3
    cases Op2.eq_of_hbeq h1
    rfl
  | app3 o x y z ihx ihy ihz =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    cases ihx _ h2
    cases ihy _ h3
    cases ihz _ h4
    cases Op3.eq_of_hbeq h1
    rfl
  | index it q i ihq ihi =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, rfl, rfl⟩, h2⟩, h3⟩ := h
    cases ihq _ h2
    cases ihi _ h3
    rename_i it'
    cases IndexTy.eq it it'
    rfl
  | obsW q ih | obsL q ih | obsH q ih =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true] at h
    cases ih _ h
    rfl
  | seq d a ihd iha =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    cases ihd _ h.1
    cases iha _ h.2
    rfl
  | orElse a b iha ihb =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    cases iha _ h.1
    cases ihb _ h.2
    rfl
  | kite a b t e iha ihb iht ihe =>
    cases t' <;> simp only [LTm.beqM, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    cases iha _ h1
    cases ihb _ h2
    cases iht _ h3
    cases ihe _ h4
    rfl

/-- What `beqR` accepts across two sorts is one sort and one term. -/
theorem LTm.sigma_eq_of_beqR {s s' : Srt} {t : LTm C s} {t' : LTm C s'} (h : t.beqR t' = true) :
    (⟨s, t⟩ : (s : Srt) × LTm C s) = ⟨s', t'⟩ :=
  LTm.eq_of_beqM t t' ((LTm.beqR_eq_beqM t t').symm.trans h)

/-- **`beqR` is equality**: what it accepts is one term. -/
theorem LTm.eq_of_beqR {s : Srt} {t t' : LTm C s} (h : t.beqR t' = true) : t = t' :=
  eq_of_heq (Sigma.mk.inj (LTm.sigma_eq_of_beqR h)).2

end Beq

/-! ## What the symbols read -/

section Symbols

variable (g : State C [])

/-- A literal, read at its own type. -/
def LTm.litV? {p : PrimTy} (t : LTm C (.val p)) : Option p.Denote :=
  match t with
  | .app0 (.lit v) => some v
  | _ => none

theorem LTm.eq_of_litV? {p : PrimTy} {t : LTm C (.val p)} {v : p.Denote} (h : t.litV? = some v) :
    t = .lit v := by
  unfold LTm.litV? at h
  split at h
  · cases h; rfl
  · cases h

theorem LTm.eval_litV? (ν : AEnv) {p : PrimTy} {t : LTm C (.val p)} {v : p.Denote}
    (h : t.litV? = some v) : (t.eval g ν : Option p.Denote) = some v := by
  rw [LTm.eq_of_litV? h]; rfl

/-- The term is `err`. -/
def LTm.isErr {s : Srt} (t : LTm C s) : Bool :=
  match t with
  | .err => true
  | _ => false

theorem LTm.eval_of_isErr (ν : AEnv) {s : Srt} {t : LTm C s} (h : t.isErr = true) :
    t.eval g ν = none := by
  cases t <;> simp only [LTm.isErr, Bool.false_eq_true] at h
  rfl

theorem _root_.Solidity.Op1.eval_none {a s : Srt} (o : Op1 C a s) : o.eval g none = none := by
  cases o <;> rfl

theorem _root_.Solidity.Op2.eval_none_left {a b s : Srt} (o : Op2 C a b s) (y : Option (b.Den C g.H)) :
    o.eval g none y = none := by
  cases o <;> rfl

/-- The right operand is read wherever the symbol returns: all but `&&`, `||`. -/
def _root_.Solidity.Op2.strictR {a b s : Srt} : Op2 C a b s → Bool
  | .binop .and _ | .binop .or _ => false
  | _ => true

theorem _root_.Solidity.Op2.eval_none_right {a b s : Srt} (o : Op2 C a b s) (h : o.strictR = true)
    (x : Option (a.Den C g.H)) : o.eval g x none = none := by
  cases x with
  | none => exact Op2.eval_none_left g o none
  | some x =>
    cases o <;> try rfl
    rename_i op p _
    show binopT op x none = none
    unfold binopT
    cases op <;> simp only [Op2.strictR, Bool.false_eq_true] at h <;> cases p <;> rfl

/-- The second and third operands are read wherever the symbol returns:
not a conditional's branches, not a push's value. -/
def _root_.Solidity.Op3.strictY {a b c s : Srt} : Op3 C a b c s → Bool
  | .ite => false
  | _ => true

def _root_.Solidity.Op3.strictZ {a b c s : Srt} : Op3 C a b c s → Bool
  | .ite | .push => false
  | _ => true

theorem _root_.Solidity.Op3.eval_none_x {a b c s : Srt} (o : Op3 C a b c s) (y : Option (b.Den C g.H))
    (z : Option (c.Den C g.H)) : o.eval g none y z = none := by
  cases o <;> rfl

theorem _root_.Solidity.Op3.eval_none_y {a b c s : Srt} (o : Op3 C a b c s) (h : o.strictY = true)
    (x : Option (a.Den C g.H)) (z : Option (c.Den C g.H)) : o.eval g x none z = none := by
  cases x <;> cases o <;> first | rfl | simp only [Op3.strictY, Bool.false_eq_true] at h

theorem _root_.Solidity.Op3.eval_none_z {a b c s : Srt} (o : Op3 C a b c s) (h : o.strictZ = true)
    (x : Option (a.Den C g.H)) (y : Option (b.Den C g.H)) : o.eval g x y none = none := by
  cases x <;> cases y <;> cases o <;> first | rfl | simp only [Op3.strictZ, Bool.false_eq_true] at h

/-- A unary symbol that returns on every value. -/
def _root_.Solidity.Op1.total {a s : Srt} : Op1 C a s → Bool
  | .unop op _ => op == .not
  | .next => false
  | .wt => false
  | _ => true

theorem _root_.Solidity.Op1.total_isSome {a s : Srt} (o : Op1 C a s) (h : o.total = true)
    (x : a.Den C g.H) : (o.eval g (some x)).isSome = true := by
  cases o
  case unop op p hp =>
    simp only [Op1.total, beq_iff_eq] at h
    subst h
    cases p <;> first | exact absurd hp (by decide) | rfl
  case next => simp only [Op1.total, Bool.false_eq_true] at h
  case wt => simp only [Op1.total, Bool.false_eq_true] at h
  all_goals rfl

/-- An operator that returns on every pair of values: the comparisons and
the connectives. -/
def _root_.Solidity.BinOp.totalB : BinOp → Bool
  | .lt | .gt | .le | .ge | .eqB | .neB | .and | .or => true
  | _ => false

/-- A binary symbol that returns on every pair of values: the comparisons,
the connectives, the integer symbols of the ledger. -/
def _root_.Solidity.Op2.total {a b s : Srt} : Op2 C a b s → Bool
  | .binop op _ => op.totalB
  | .zbin _ _ | .zcmp _ _ | .mat _ | .copy _ | .copySt _ => true
  | _ => false

theorem _root_.Solidity.Op2.total_isSome {a b s : Srt} (o : Op2 C a b s) (h : o.total = true)
    (x : a.Den C g.H) (y : b.Den C g.H) : (o.eval g (some x) (some y)).isSome = true := by
  cases o
  case binop op p hp =>
    simp only [Op2.total] at h
    show (binopT op x (some y)).isSome = true
    unfold binopT
    cases op <;> simp only [BinOp.totalB, Bool.false_eq_true] at h <;>
      cases p <;> first | exact absurd hp (by decide) | skip <;>
      first | rfl | (cases (x : Bool) <;> rfl)
  case zbin | zcmp | mat | copy | copySt => rfl
  all_goals simp only [Op2.total, Bool.false_eq_true] at h

/-- `a ⊖`, folded on a literal. -/
def fold1 {a s : Srt} (o : Op1 C a s) (x : LTm C a) : LTm C s :=
  match o, x with
  | .unop op h, x =>
    match x.litV? with
    | some v =>
      match op.evalT v with
      | some r => .lit r
      | none => .err
    | none => .app1 (.unop op h) x
  | o, x => .app1 o x

theorem fold1_eval (ν : AEnv) {a s : Srt} (o : Op1 C a s) (x : LTm C a) :
    (fold1 o x).eval g ν = (LTm.app1 o x).eval g ν := by
  cases o <;> try rfl
  rename_i op p h
  simp only [fold1]
  split
  · rename_i v hv
    obtain rfl := LTm.eq_of_litV? hv
    split <;> rename_i r hr
    · show some r = (some v).bind op.evalT
      rw [Option.bind_some, hr]
    · show none = (some v).bind op.evalT
      rw [Option.bind_some, hr]
  · rfl

/-- `a ⊕ b`, folded on literals: `&&`/`||` on a literal left operand,
any operator on two. -/
def fold2 {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) : LTm C s :=
  match o, x, y with
  | .binop op h, x, y =>
    match x.litV? with
    | some u =>
      match op.shortT u with
      | some r => .lit r
      | none =>
        match y.litV? with
        | some v =>
          match op.evalT u v with
          | some r => .lit r
          | none => .err
        | none => .app2 (.binop op h) x y
    | none => .app2 (.binop op h) x y
  | o, x, y => .app2 o x y

theorem fold2_eval (ν : AEnv) {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    (fold2 o x y).eval g ν = (LTm.app2 o x y).eval g ν := by
  cases o <;> try rfl
  rename_i op p h
  simp only [fold2]
  split
  · rename_i u hu
    obtain rfl := LTm.eq_of_litV? hu
    show _ = binopT op u _
    unfold binopT
    split
    · rename_i r hr
      rw [hr]; rfl
    · rename_i hr
      rw [hr]
      split
      · rename_i v hv
        obtain rfl := LTm.eq_of_litV? hv
        show _ = (some v).bind (op.evalT u)
        rw [Option.bind_some]
        split <;> rename_i r' hr' <;> rw [hr'] <;> rfl
      · show binopT op u _ = _
        unfold binopT
        rw [hr]
  · rfl

end Symbols

/-! ## The facts -/

/-- Two value terms at one type. -/
structure EqF (C : Contract) where
  p : PrimTy
  l : LTm C (.val p)
  r : LTm C (.val p)

/-- A range a value term is known to lie in, where it returns: its integer
(`PrimTy.ival`) between `lo` and `hi`. -/
structure RangeB (C : Contract) where
  p : PrimTy
  t : LTm C (.val p)
  lo : Int
  hi : Int

/-- **What the closer knows** at a point of a leaf: rewrites (the left side
is the right one, which returns), pairs apart (both return, to different
values), terms that return, and ranges. -/
structure Facts (C : Contract) where
  eqs : List (EqF C) := []
  nes : List (EqF C) := []
  rets : List ((s : Srt) × LTm C s) := []
  bnds : List (RangeB C) := []

/-- A value as an integer: a word, a `bool` as `0` or `1`. -/
def _root_.Solidity.PrimTy.ival : {p : PrimTy} → p.Denote → Int
  | .bool, b => if (show Bool from b) then 1 else 0
  | .uint, v => (v : {n : Int // PrimTy.uint.inRange n = true}).1
  | .int, v => (v : {n : Int // PrimTy.int.inRange n = true}).1

/-- The facts hold. -/
structure Facts.Ok (g : State C []) (ν : AEnv) (F : Facts C) : Prop where
  eqs : ∀ e ∈ F.eqs, ∃ x, (e.l.eval g ν : Option e.p.Denote) = some x ∧ e.r.eval g ν = some x
  nes : ∀ e ∈ F.nes, ∃ x y, (e.l.eval g ν : Option e.p.Denote) = some x ∧ e.r.eval g ν = some y ∧
    x ≠ y
  rets : ∀ u ∈ F.rets, (u.2.eval g ν).isSome = true
  bnds : ∀ b ∈ F.bnds, ∀ v, (b.t.eval g ν : Option b.p.Denote) = some v →
    b.lo ≤ PrimTy.ival v ∧ PrimTy.ival v ≤ b.hi

/-- `t` is one the facts know returns. -/
def Facts.inRets (F : Facts C) {s : Srt} (t : LTm C s) : Bool := F.rets.any fun u => t.beqR u.2

theorem Facts.inRets_sound {g : State C []} {ν : AEnv} {F : Facts C} (hF : F.Ok g ν) {s : Srt}
    {t : LTm C s} (h : F.inRets t = true) : (t.eval g ν).isSome = true := by
  obtain ⟨u, hu, ht⟩ := List.any_eq_true.1 h
  have e := LTm.sigma_eq_of_beqR ht
  obtain ⟨s', u'⟩ := u
  cases e
  exact hF.rets _ hu

/-- `t` rewritten by the first fact whose left side it is. -/
def Facts.rwWith {s : Srt} (t : LTm C s) : List (EqF C) → LTm C s
  | [] => t
  | e :: es =>
    if h : s = .val e.p then
      if t.beqR e.l then h ▸ e.r else Facts.rwWith t es
    else Facts.rwWith t es

theorem Facts.rwWith_eval {g : State C []} {ν : AEnv} {s : Srt} (t : LTm C s) :
    (es : List (EqF C)) →
    (∀ e ∈ es, ∃ x, (e.l.eval g ν : Option e.p.Denote) = some x ∧ e.r.eval g ν = some x) →
    (Facts.rwWith t es).eval g ν = t.eval g ν
  | [], _ => rfl
  | e :: es, h => by
    unfold Facts.rwWith
    split
    · rename_i hs
      subst hs
      split
      · rename_i hb
        cases LTm.eq_of_beqR hb
        obtain ⟨x, h1, h2⟩ := h e List.mem_cons_self
        rw [h1]
        exact h2
      · exact Facts.rwWith_eval t es fun e he => h e (List.mem_cons_of_mem _ he)
    · exact Facts.rwWith_eval t es fun e he => h e (List.mem_cons_of_mem _ he)

/-- `t` rewritten by the facts. -/
def Facts.rw (F : Facts C) {s : Srt} (t : LTm C s) : LTm C s := Facts.rwWith t F.eqs

theorem Facts.rw_eval {g : State C []} {ν : AEnv} {F : Facts C} (hF : F.Ok g ν) {s : Srt}
    (t : LTm C s) : (F.rw t).eval g ν = t.eval g ν :=
  Facts.rwWith_eval t F.eqs hF.eqs

/-! ## Ranges

A numeric term lies in its type's range; a literal is itself; a premise
`a < b` bounds both sides; `a + b` and `a - b` lie in the sums of their
operands' ranges.  The closer reads a comparison of two ranges that do not
overlap (KeY's `intSimplification` on bounds), and an addition or
subtraction whose operands' ranges keep it in its type returns. -/

section Ranges

variable {g : State C []} {ν : AEnv}

/-- The least value of a type, as an integer. -/
def _root_.Solidity.PrimTy.lo : PrimTy → Int
  | .bool => 0
  | .uint => 0
  | .int => -((2 ^ 255 : Nat) : Int)

/-- The greatest value of a type, as an integer. -/
def _root_.Solidity.PrimTy.hi : PrimTy → Int
  | .bool => 1
  | .uint => ((2 ^ 256 : Nat) : Int) - 1
  | .int => ((2 ^ 255 : Nat) : Int) - 1

theorem _root_.Solidity.PrimTy.ival_mem : {p : PrimTy} → (v : p.Denote) →
    p.lo ≤ PrimTy.ival v ∧ PrimTy.ival v ≤ p.hi
  | .bool, b => by
    cases hb : (show Bool from b) <;> simp only [PrimTy.ival, PrimTy.lo, PrimTy.hi, hb] <;> omega
  | .uint, v => by
    have h := v.2
    simp only [PrimTy.inRange, decide_eq_true_eq] at h
    simp only [PrimTy.ival, PrimTy.lo, PrimTy.hi]; omega
  | .int, v => by
    have h := v.2
    simp only [PrimTy.inRange, decide_eq_true_eq] at h
    simp only [PrimTy.ival, PrimTy.lo, PrimTy.hi]; omega

/-- A range met with another. -/
def meetR (r r' : Int × Int) : Int × Int := (max r.1 r'.1, min r.2 r'.2)

/-- The facts' range of `t`, by its literal, its type and the bounds on it. -/
def Facts.rangeLeaf (F : Facts C) {p : PrimTy} (t : LTm C (.val p)) : Int × Int :=
  match t.litV? with
  | some v => (PrimTy.ival v, PrimTy.ival v)
  | none => F.bnds.foldl (fun r b => if t.beqR b.t then meetR r (b.lo, b.hi) else r) (p.lo, p.hi)

/-- In a range. -/
def InR (r : Int × Int) (n : Int) : Prop := r.1 ≤ n ∧ n ≤ r.2

theorem inR_meet {r r' : Int × Int} {n : Int} (h : InR r n) (h' : InR r' n) : InR (meetR r r') n :=
  ⟨Int.max_le.2 ⟨h.1, h'.1⟩, Int.le_min.2 ⟨h.2, h'.2⟩⟩

theorem Facts.rangeLeaf_sound {F : Facts C} (hF : F.Ok g ν) {p : PrimTy} (t : LTm C (.val p))
    {v : p.Denote} (hv : (t.eval g ν : Option p.Denote) = some v) :
    InR (F.rangeLeaf t) (PrimTy.ival v) := by
  unfold Facts.rangeLeaf
  split
  · rename_i w hw
    rw [LTm.eval_litV? g ν hw] at hv
    cases hv
    exact ⟨Int.le_refl _, Int.le_refl _⟩
  · have key : ∀ (bs : List (RangeB C)) (r : Int × Int), (∀ b ∈ bs, b ∈ F.bnds) →
        InR r (PrimTy.ival v) →
        InR (bs.foldl (fun r b => if t.beqR b.t then meetR r (b.lo, b.hi) else r) r)
          (PrimTy.ival v) := by
      intro bs
      induction bs with
      | nil => intro r _ h; exact h
      | cons b bs ih =>
        intro r hs h
        simp only [List.foldl_cons]
        refine ih _ (fun b' hb' => hs b' (List.mem_cons_of_mem _ hb')) ?_
        split
        · rename_i hb
          obtain ⟨q, bt, lo, hi⟩ := b
          cases LTm.sigma_eq_of_beqR hb
          exact inR_meet h (hF.bnds _ (hs _ List.mem_cons_self) v hv)
        · exact h
    exact key F.bnds _ (fun _ h => h) (PrimTy.ival_mem v)

/-- The range of a sum or difference, from its operands'. -/
def Facts.rangeOp (F : Facts C) {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    Option (Int × Int) :=
  match o, x, y with
  | .binop .add _, x, y =>
    some ((F.rangeLeaf x).1 + (F.rangeLeaf y).1, (F.rangeLeaf x).2 + (F.rangeLeaf y).2)
  | .binop .sub _, x, y =>
    some ((F.rangeLeaf x).1 - (F.rangeLeaf y).2, (F.rangeLeaf x).2 - (F.rangeLeaf y).1)
  | _, _, _ => none

theorem ofInt?_ival {p : PrimTy} {n : Int} {v : p.Denote} (h : p.ofInt? n = some v) :
    PrimTy.ival v = n := by
  cases p with
  | bool => simp only [PrimTy.ofInt?, PrimTy.ofValue?, reduceCtorEq] at h
  | uint =>
    simp only [PrimTy.ofInt?, PrimTy.ofValue?] at h
    split at h
    · cases h; rfl
    · cases h
  | int =>
    simp only [PrimTy.ofInt?, PrimTy.ofValue?] at h
    split at h
    · cases h; rfl
    · cases h

theorem ofInt?_isSome {p : PrimTy} (hp : p.isNumeric = true) {n : Int} (h1 : p.lo ≤ n)
    (h2 : n ≤ p.hi) : (p.ofInt? n).isSome = true := by
  cases p with
  | bool => cases hp
  | uint =>
    simp only [PrimTy.lo, PrimTy.hi] at h1 h2
    simp only [PrimTy.ofInt?, PrimTy.ofValue?]
    rw [dif_pos (by simp only [PrimTy.inRange, decide_eq_true_eq]; omega)]; rfl
  | int =>
    simp only [PrimTy.lo, PrimTy.hi] at h1 h2
    simp only [PrimTy.ofInt?, PrimTy.ofValue?]
    rw [dif_pos (by simp only [PrimTy.inRange, decide_eq_true_eq]; omega)]; rfl

theorem evalT_add {p : PrimTy} {u w v : p.Denote} (h : BinOp.evalT .add u w = some v) :
    PrimTy.ival v = PrimTy.ival u + PrimTy.ival w := by
  cases p with
  | bool => cases h
  | uint | int =>
    simp only [BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Option.bind_some] at h
    exact ofInt?_ival h

theorem evalT_sub {p : PrimTy} {u w v : p.Denote} (h : BinOp.evalT .sub u w = some v) :
    PrimTy.ival v = PrimTy.ival u - PrimTy.ival w := by
  cases p with
  | bool => cases h
  | uint | int =>
    simp only [BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Option.bind_some] at h
    exact ofInt?_ival h

theorem Facts.rangeOp_sound {F : Facts C} (hF : F.Ok g ν) {a b s : Srt} (o : Op2 C a b s)
    (x : LTm C a) (y : LTm C b) {p : PrimTy} {v : p.Denote} (hs : s = .val p)
    (h : (LTm.app2 o x y).eval g ν = hs ▸ (some v : Option ((Srt.val p).Den C g.H)))
    {r : Int × Int} (hr : F.rangeOp o x y = some r) : InR r (PrimTy.ival v) := by
  cases o
  case binop op q hop =>
    rw [LTm.eval_app2] at h
    cases op
    case add | sub =>
      cases hs
      simp only [Facts.rangeOp, Option.some.injEq] at hr
      subst hr
      cases hx : (x.eval g ν : Option q.Denote) with
      | none => rw [hx] at h; cases h
      | some u =>
        rw [hx] at h
        have h' : binopT _ u (y.eval g ν) = some v := h
        unfold binopT at h'
        simp only [BinOp.shortT] at h'
        cases hy : (y.eval g ν : Option q.Denote) with
        | none => rw [hy] at h'; cases h'
        | some w =>
          rw [hy, Option.bind_some] at h'
          have ru := F.rangeLeaf_sound hF x hx
          have rw' := F.rangeLeaf_sound hF y hy
          unfold InR at ru rw' ⊢
          first
            | (rw [evalT_add h']; constructor <;> omega)
            | (rw [evalT_sub h']; constructor <;> omega)
    all_goals simp only [Facts.rangeOp, reduceCtorEq] at hr
  all_goals simp only [Facts.rangeOp, reduceCtorEq] at hr

/-- **The facts' range of a numeric term**: its own, met with its operands'
where it is a sum or a difference. -/
def Facts.range (F : Facts C) {p : PrimTy} (t : LTm C (.val p)) : Int × Int :=
  match t with
  | .app2 o x y =>
    match F.rangeOp o x y with
    | some r => meetR (F.rangeLeaf (.app2 o x y)) r
    | none => F.rangeLeaf (.app2 o x y)
  | t => F.rangeLeaf t

theorem Facts.range_sound {F : Facts C} (hF : F.Ok g ν) {p : PrimTy} (t : LTm C (.val p))
    {v : p.Denote} (hv : (t.eval g ν : Option p.Denote) = some v) :
    InR (F.range t) (PrimTy.ival v) := by
  cases t with
  | app2 o x y =>
    simp only [Facts.range]
    split
    · rename_i r hr
      exact inR_meet (F.rangeLeaf_sound hF _ hv) (F.rangeOp_sound hF o x y rfl hv hr)
    · exact F.rangeLeaf_sound hF _ hv
  | _ => exact F.rangeLeaf_sound hF _ hv

/-- An addition or a subtraction that stays in its type wherever its
operands return in their ranges. -/
def Facts.arithOk (F : Facts C) {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    Bool :=
  match o, x, y with
  | @Op2.binop _ .add p _, x, y =>
    p.isNumeric && decide (p.lo ≤ (F.range x).1 + (F.range y).1) &&
      decide ((F.range x).2 + (F.range y).2 ≤ p.hi)
  | @Op2.binop _ .sub p _, x, y =>
    p.isNumeric && decide (p.lo ≤ (F.range x).1 - (F.range y).2) &&
      decide ((F.range x).2 - (F.range y).1 ≤ p.hi)
  | _, _, _ => false

theorem Facts.arithOk_isSome {F : Facts C} (hF : F.Ok g ν) {a b s : Srt} (o : Op2 C a b s)
    (x : LTm C a) (y : LTm C b) (h : F.arithOk o x y = true) {u : a.Den C g.H} {w : b.Den C g.H}
    (hx : x.eval g ν = some u) (hy : y.eval g ν = some w) :
    (o.eval g (some u) (some w)).isSome = true := by
  cases o
  case binop op q hop =>
    cases op
    case add | sub =>
      simp only [Facts.arithOk, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hq, h1⟩, h2⟩ := h
      have ru := F.range_sound hF x hx
      have rw' := F.range_sound hF y hy
      unfold InR at ru rw'
      show (binopT _ u (some w)).isSome = true
      unfold binopT
      cases q
      · cases hq
      all_goals
        simp only [BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum, BinOp.arithInt]
        exact ofInt?_isSome rfl (by simp only [PrimTy.ival] at ru rw'; omega)
          (by simp only [PrimTy.ival] at ru rw'; omega)
    all_goals simp only [Facts.arithOk, Bool.false_eq_true] at h
  all_goals simp only [Facts.arithOk, Bool.false_eq_true] at h

end Ranges


/-! ## What returns -/

section Returns

variable {g : State C []} {ν : AEnv}

/-- The conditional. -/
def _root_.Solidity.Op3.isIte {a b c s : Srt} : Op3 C a b c s → Bool
  | .ite => true
  | _ => false

theorem _root_.Solidity.Op3.ite_isSome {a b c s : Srt} (o : Op3 C a b c s) (h : o.isIte = true)
    (x : a.Den C g.H) (y : b.Den C g.H) (z : c.Den C g.H) :
    (o.eval g (some x) (some y) (some z)).isSome = true := by
  cases o <;> simp only [Op3.isIte, Bool.false_eq_true] at h
  show (cond (x : Bool) (some y) (some z)).isSome = true
  cases (x : Bool) <;> rfl

/-- `Facts.returns`' compiled twin. -/
def Facts.returnsM (F : Facts C) : {s : Srt} → LTm C s → Bool
  | _, .var _ | _, .app0 _ => true
  | _, .app1 o x => (o.total && F.returnsM x) || F.inRets (.app1 o x)
  | _, .app2 o x y =>
    ((o.total || F.arithOk o x y) && F.returnsM x && F.returnsM y) || F.inRets (.app2 o x y)
  | _, .app3 o x y z =>
    (o.isIte && F.returnsM x && F.returnsM y && F.returnsM z) || F.inRets (.app3 o x y z)
  | _, .index it q i => (F.returnsM q && F.returnsM i) || F.inRets (.index it q i)
  | _, .obsW q => F.returnsM q || F.inRets (.obsW q)
  | _, .obsL q => F.returnsM q || F.inRets (.obsL q)
  | _, .obsH q => F.returnsM q || F.inRets (.obsH q)
  | _, .seq d a => (F.returnsM d && F.returnsM a) || F.inRets (.seq d a)
  | _, .orElse a b => F.returnsM a || F.returnsM b || F.inRets (.orElse a b)
  | _, .kite a b t e =>
    (F.returnsM a && F.returnsM b && F.returnsM t && F.returnsM e) || F.inRets (.kite a b t e)
  | _, .err => false

/-- **The term returns**, by what the facts know and by its symbols: an
atom, a constant, a total symbol on terms that return, a term a premise
says returns. -/
@[implemented_by Facts.returnsM]
def Facts.returns (F : Facts C) {s : Srt} (t : LTm C s) : Bool :=
  @LTm.rec C (fun _ _ => Bool)
    (@fun _ _ => true) (@fun _ _ => true)
    (@fun _ _ o x ihx => (o.total && ihx) || F.inRets (.app1 o x))
    (@fun _ _ _ o x y ihx ihy =>
      ((o.total || F.arithOk o x y) && ihx && ihy) || F.inRets (.app2 o x y))
    (@fun _ _ _ _ o x y z ihx ihy ihz =>
      (o.isIte && ihx && ihy && ihz) || F.inRets (.app3 o x y z))
    (@fun _ _ _ it q i ihq ihi => (ihq && ihi) || F.inRets (.index it q i))
    (@fun _ q ih => ih || F.inRets (.obsW q))
    (@fun _ q ih => ih || F.inRets (.obsL q))
    (@fun _ q ih => ih || F.inRets (.obsH q))
    (@fun _ _ d a ihd iha => (ihd && iha) || F.inRets (.seq d a))
    (@fun _ a b iha ihb => iha || ihb || F.inRets (.orElse a b))
    (@fun _ _ a b t e iha ihb iht ihe => (iha && ihb && iht && ihe) || F.inRets (.kite a b t e))
    (@fun _ => false) s t

theorem Facts.returns_eq_returnsM (F : Facts C) {s : Srt} (t : LTm C s) :
    F.returns t = F.returnsM t := by
  induction t with
  | var | app0 | err => rfl
  | app1 o x ih => simp only [Facts.returnsM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [Facts.returnsM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [Facts.returnsM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => simp only [Facts.returnsM, ← ihq, ← ihi]; rfl
  | obsW q ih | obsL q ih | obsH q ih => simp only [Facts.returnsM, ← ih]; rfl
  | seq d a ihd iha => simp only [Facts.returnsM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => simp only [Facts.returnsM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe => simp only [Facts.returnsM, ← iha, ← ihb, ← iht, ← ihe]; rfl

theorem isSome_bind {α β : Type} {x : Option α} {f : α → Option β} (hx : x.isSome = true)
    (hf : ∀ a, (f a).isSome = true) : (x.bind f).isSome = true := by
  cases x with
  | none => cases hx
  | some a => exact hf a

/-- **What `returns` accepts returns.** -/
theorem Facts.returns_sound {F : Facts C} (hF : F.Ok g ν) {s : Srt} (t : LTm C s)
    (h : F.returns t = true) : (t.eval g ν).isSome = true := by
  induction t with
  | var k => rfl
  | app0 o => exact Op0.eval_isSome g o
  | err => cases h
  | app1 o x ih =>
    rcases Bool.or_eq_true_iff.1 h with h | h
    · rw [Bool.and_eq_true] at h
      rw [LTm.eval_app1]
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (ih h.2)
      rw [hv]; exact o.total_isSome g h.1 v
    · exact F.inRets_sound hF h
  | app2 o x y ihx ihy =>
    rcases Bool.or_eq_true_iff.1 h with h | h
    · simp only [Bool.and_eq_true, Bool.or_eq_true] at h
      rw [LTm.eval_app2]
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (ihx h.1.2)
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (ihy h.2)
      rw [hv, hw]
      rcases h.1.1 with ht | ht
      · exact o.total_isSome g ht v w
      · exact F.arithOk_isSome hF o x y ht hv hw
    · exact F.inRets_sound hF h
  | app3 o x y z ihx ihy ihz =>
    rcases Bool.or_eq_true_iff.1 h with h | h
    · simp only [Bool.and_eq_true] at h
      rw [LTm.eval_app3]
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (ihx h.1.1.2)
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (ihy h.1.2)
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (ihz h.2)
      rw [hv, hw, hu]; exact o.ite_isSome h.1.1.1 v w u
    · exact F.inRets_sound hF h
  | index it q i ihq ihi =>
    rcases Bool.or_eq_true_iff.1 h with h | h
    · simp only [Bool.and_eq_true] at h
      rw [LTm.eval_index]
      exact isSome_bind (ihq h.1) fun _ => isSome_bind (ihi h.2) fun _ => rfl
    · exact F.inRets_sound hF h
  | obsW q ih | obsL q ih | obsH q ih =>
    rcases Bool.or_eq_true_iff.1 h with h | h
    · exact isSome_bind (ih h) fun _ => rfl
    · exact F.inRets_sound hF h
  | seq d a ihd iha =>
    rcases Bool.or_eq_true_iff.1 h with h | h
    · simp only [Bool.and_eq_true] at h
      exact isSome_bind (ihd h.1) fun _ => iha h.2
    · exact F.inRets_sound hF h
  | orElse a b iha ihb =>
    rcases Bool.or_eq_true_iff.1 h with h | h
    · rw [LTm.eval_orElse]
      rcases Bool.or_eq_true_iff.1 h with h | h
      · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (iha h)
        rw [hv]; rfl
      · cases (a.eval g ν) with
        | some _ => rfl
        | none => exact ihb h
    · exact F.inRets_sound hF h
  | kite a b t e iha ihb iht ihe =>
    rcases Bool.or_eq_true_iff.1 h with h | h
    · simp only [Bool.and_eq_true] at h
      rw [LTm.eval_kite]
      refine isSome_bind (iha h.1.1.1) fun _ => isSome_bind (ihb h.1.1.2) fun _ => ?_
      split
      · exact iht h.1.2
      · exact ihe h.2
    · exact F.inRets_sound hF h

end Returns

/-! ## Where a typed storage has a location -/

section Has

/-- A location one path further has a location where its base has one, when
every value has the path: a struct its members, a mapping its keys. -/
theorem has_append (st : Storage C) {U W : Ty} (r : SRef C U) (p : Path U W)
    (hp : ∀ v : SVal U, (v.findM p).isSome = true) :
    st.obs.has (.ref (r.append p)) = st.obs.has (.ref r) := by
  rw [Storage.obs_has_ref, Storage.obs_has_ref, SVal.obs_has, SVal.obs_has]
  show ((st.get r.hroot).findM (r.path.append p)).isSome = _
  rw [SVal.findM_append]
  cases (st.get r.hroot).findM r.path with
  | none => rfl
  | some v => exact hp v

theorem has_root (st : Storage C) (r : Name) {T : Ty} (h : C.rootType r = some T) :
    st.obs.has (.ref (SRef.ofRoot r h)) = true := by
  rw [Storage.obs_has_ref, SVal.obs_has]
  show ((st.get h).findM .nil).isSome = true
  rw [SVal.findM_nil']; rfl

theorem findM_field {s f : Name} {T : Ty} (h : Semantics.lookupBy f (Semantics.structDef s) = some T)
    (v : SVal (.ref (.struct s))) : (v.findM (.field h .nil)).isSome = true := by
  cases v
  simp only [SVal.findM, SVal.findM_nil', Option.isSome_some]

theorem findM_key {K V : Ty} (k : Int) (v : SVal (.ref (.mapping K V))) :
    (v.findM (.key k .nil)).isSome = true := by
  cases v
  simp only [SVal.findM]
  split <;> rfl

/-- `has` at an entry: a mapping's where its base has one, its key
returning. -/
def hasIdx {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (q : LTm C (.path (.ref R)))
    (i : LTm C (.val k.keyTy)) : LTm C (.val .bool) :=
  @IndexTy.casesOn (fun R k V _ => LTm C (.path (.ref R)) → LTm C (.val k.keyTy) → LTm C (.val .bool))
    R k V it (fun {_} {_} q i => seqL i (.obsH q)) (fun a q i => .obsH (.index (.arr a) q i)) q i

/-- `has` at a path on a typed storage, one step up: a root has a
location, a member or a mapping's entry where its base has one. -/
def hasOf {T : Ty} (q : LTm C (.path T)) : LTm C (.val .bool) :=
  match q with
  | .app0 (.root _ _) => .tt
  | .app1 (.field _) q' => .obsH q'
  | .index it q' i => hasIdx it q' i
  | q => .obsH q

theorem hasOf_eval (g : State C []) (ν : AEnv) {T : Ty} (q : LTm C (.path T)) :
    ((hasOf q).eval g ν : Option Bool) = (LTm.obsH q).eval g ν := by
  cases q with
  | app0 o =>
    cases o with
    | root r h =>
      show some true = some (g.storage.obs.has (.ref (SRef.ofRoot r h)))
      rw [has_root]
    | _ => rfl
  | app1 o q =>
    cases o with
    | @field s f T h =>
      simp only [hasOf]
      rw [LTm.eval_obsH, LTm.eval_obsH, LTm.eval_app1]
      cases (q.eval g ν : Option (SRef C (.ref (.struct s)))) with
      | none => rfl
      | some r =>
        show some _ = some (g.storage.obs.has (.ref (r.append (.field h .nil))))
        rw [has_append _ _ _ (findM_field h)]
    | _ => rfl
  | index it q k =>
    cases it with
    | map =>
      show ((seqL k (LTm.obsH q)).eval g ν : Option Bool) = _
      rw [seqL_eval, LTm.eval_obsH, LTm.eval_obsH, LTm.eval_index]
      cases (k.eval g ν : Option _) with
      | none => cases (q.eval g ν : Option (SRef C _)) <;> rfl
      | some k =>
        cases (q.eval g ν : Option (SRef C _)) with
        | none => rfl
        | some r =>
          simp only [Option.bind_some]
          simp only [SRef.index, Path.index_map]
          exact congrArg some (has_append g.storage r _ (findM_key _)).symm
    | arr _ => rfl
  | _ => rfl

/-- One step of `has` on a typed storage. -/
def hasStep (t : LTm C (.val .bool)) : LTm C (.val .bool) :=
  match t with
  | .obsH q => hasOf q
  | t => t

theorem hasStep_eval (g : State C []) (ν : AEnv) (t : LTm C (.val .bool)) :
    ((hasStep t).eval g ν : Option Bool) = t.eval g ν := by
  cases t with
  | obsH q => exact hasOf_eval g ν q
  | _ => rfl

/-- `has` on a typed storage, a few steps up the path. -/
def hasN (t : LTm C (.val .bool)) : LTm C (.val .bool) :=
  hasStep (hasStep (hasStep (hasStep t)))

theorem hasN_eval (g : State C []) (ν : AEnv) (t : LTm C (.val .bool)) :
    ((hasN t).eval g ν : Option Bool) = t.eval g ν := by
  simp only [hasN, hasStep_eval]

end Has

/-! ## An index below the length

A dynamic array has a slot at every index below its live length: `has` at
`q[i]` is `true` where the ranges put `i` below `q.length` (KeY's
`arrayLengthNonNegative` with the bound a premise gives). -/

section Below

variable {g : State C []} {ν : AEnv}

theorem findM_at_isSome {E : Ty} (v : SVal (.ref (.array E))) {i : Int} (h0 : 0 ≤ i)
    (hi : i < ((SVal.view v : ArrView E).n : Int)) : (v.findM (.at i .nil)).isSome = true := by
  cases v with
  | array e sh hn =>
    simp only [SVal.view] at hi
    simp only [SVal.findM, if_pos h0]
    have hl : i.toNat < e.toList.length := by rw [SVec.length_toList]; omega
    rw [List.getElem?_append_left hl, List.getElem?_eq_getElem hl]
    simp only [SVal.findM_nil', Option.isSome_some]

theorem obs_len_lt' (st : Storage C) {E : Ty} (r : SRef C (.ref (.array E))) :
    st.obs.len (.ref r) < 2 ^ 256 := by
  rw [Storage.obs_len_ref, SVal.obs_len]
  cases (st.get r.hroot).findM r.path with
  | none => exact Nat.two_pow_pos 256
  | some w => cases w with | array e sh hn => exact hn

theorem has_below (st : Storage C) {E : Ty} (r : SRef C (.ref (.array E))) {i : Int}
    (h0 : 0 ≤ i) (hi : i < (st.obs.len (.ref r) : Int)) :
    st.obs.has (.ref (r.append (.at i .nil))) = true := by
  rw [Storage.obs_len_ref, SVal.obs_len] at hi
  rw [Storage.obs_has_ref, SVal.obs_has]
  show ((st.get r.hroot).findM (r.path.append (.at i .nil))).isSome = true
  rw [SVal.findM_append]
  cases hf : (st.get r.hroot).findM r.path with
  | none => rw [hf] at hi; simp only [SVal.lenOf] at hi; omega
  | some v =>
    rw [hf] at hi
    exact findM_at_isSome v h0 hi

theorem ival_uintOfNat {n : Nat} (h : n < 2 ^ 256) : PrimTy.ival (uintOfNat n) = n := by
  simp only [uintOfNat, dif_pos h, lenU, PrimTy.ival]

theorem findM_atF_isSome {E : Ty} {n : Nat} (v : SVal (.ref (.fixed E n))) {i : Int} (h0 : 0 ≤ i)
    (hi : i < (n : Int)) : (v.findM (.atF i .nil)).isSome = true := by
  cases v with
  | fixed e =>
    simp only [SVal.findM, if_pos h0]
    have hl : i.toNat < e.toList.length := by rw [SVec.length_toList]; omega
    rw [List.getElem?_eq_getElem hl]
    simp only [SVal.findM_nil', Option.isSome_some]

/-- `has` at a dynamic array's index the ranges put below its length. -/
def Facts.hasIdxDyn (F : Facts C) {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    (q : LTm C (.path (.ref R))) (i : LTm C (.val k.keyTy)) : LTm C (.val .bool) :=
  @IndexTy.casesOn
    (fun R k V _ => LTm C (.path (.ref R)) → LTm C (.val k.keyTy) → LTm C (.val .bool))
    R k V it (fun {_} {_} q i => .obsH (.index .map q i))
    (fun a => @ArrTy.casesOn
      (fun R E a => LTm C (.path (.ref R)) → LTm C (.val PrimTy.uint.keyTy) → LTm C (.val .bool))
      _ _ a
      (fun {_} q i =>
        if (F.range i).2 < (F.range (.obsL q)).1 then
          (if F.returns i && F.returns q then .tt else .seq i (.seq (.obsL q) .tt))
        else .obsH (.index (.arr .dyn) q i))
      (fun {_} {n} q i =>
        if (F.range i).2 < (n : Int) then
          (if F.returns i then hasN (.obsH q) else .seq i (hasN (.obsH q)))
        else .obsH (.index (.arr .fixed) q i))) q i

theorem Facts.hasDyn_core {F : Facts C} (hF : F.Ok g ν) {E : Ty}
    {q : LTm C (.path (.ref (.array E)))} {i : LTm C (.val PrimTy.uint.keyTy)}
    (hlt : (F.range i).2 < (F.range (.obsL q)).1) :
    ((i.eval g ν : Option PrimTy.uint.Denote).bind fun _ =>
      ((LTm.obsL q).eval g ν : Option PrimTy.uint.Denote).bind fun _ =>
        (LTm.tt.eval g ν : Option Bool)) =
    (((q.eval g ν : Option (SRef C (.ref (.array E)))).bind fun r =>
      (i.eval g ν : Option PrimTy.uint.Denote).bind fun j =>
        some (r.index (IndexTy.arr ArrTy.dyn) (PrimTy.key j))).bind fun r =>
          some (g.storage.obs.has (.ref r))) := by
  cases hi : (i.eval g ν : Option PrimTy.uint.Denote) with
  | none => cases (q.eval g ν : Option (SRef C _)) <;> rfl
  | some k =>
    cases hq : (q.eval g ν : Option (SRef C _)) with
    | none => simp only [Option.bind_some, LTm.eval_obsL, hq, Option.bind_none]
    | some r =>
      have hl : ((LTm.obsL q).eval g ν : Option PrimTy.uint.Denote) =
          some (uintOfNat (g.storage.obs.len (.ref r))) := by
        rw [LTm.eval_obsL, hq]; rfl
      have ri := F.range_sound hF i hi
      have rl := F.range_sound hF (.obsL q) hl
      unfold InR at ri rl
      rw [ival_uintOfNat (obs_len_lt' _ _)] at rl
      have hk : 0 ≤ PrimTy.ival k := (PrimTy.ival_mem k).1
      have hkey : PrimTy.key k = PrimTy.ival k := rfl
      simp only [Option.bind_some, hl, SRef.index, Path.index_dyn]
      rw [has_below g.storage r (by rw [hkey]; exact hk) (by rw [hkey]; omega)]
      rfl

/-- `has` read by the ranges: at a dynamic array's index below its length. -/
def Facts.hasRange (F : Facts C) (t : LTm C (.val .bool)) : LTm C (.val .bool) :=
  match t with
  | .obsH (.index it q i) => F.hasIdxDyn it q i
  | t => t

theorem Facts.hasRange_eval {F : Facts C} (hF : F.Ok g ν) (t : LTm C (.val .bool)) :
    ((F.hasRange t).eval g ν : Option Bool) = t.eval g ν := by
  cases t with
  | obsH q =>
    cases q with
    | index it q i =>
      simp only [Facts.hasRange]
      cases it with
      | map => rfl
      | arr a =>
        cases a with
        | @fixed E n =>
          simp only [Facts.hasIdxDyn]
          split
          · rename_i hlt
            have key : ((LTm.seq i (hasN (LTm.obsH q))).eval g ν : Option Bool) =
                (LTm.obsH (LTm.index (IndexTy.arr ArrTy.fixed) q i)).eval g ν := by
              rw [LTm.eval_seq, hasN_eval, LTm.eval_obsH, LTm.eval_obsH, LTm.eval_index]
              cases hi : (i.eval g ν : Option PrimTy.uint.Denote) with
              | none => cases (q.eval g ν : Option (SRef C _)) <;> rfl
              | some k =>
                cases hq : (q.eval g ν : Option (SRef C _)) with
                | none => rfl
                | some r =>
                  have ri := F.range_sound hF i hi
                  unfold InR at ri
                  have hk : 0 ≤ PrimTy.ival k := (PrimTy.ival_mem k).1
                  have hkey : PrimTy.key k = PrimTy.ival k := rfl
                  simp only [Option.bind_some, SRef.index, Path.index_fixed]
                  rw [has_append g.storage r _ fun v => findM_atF_isSome v (by rw [hkey]; exact hk)
                    (by rw [hkey]; omega)]
            split
            · rename_i hr
              obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF i hr)
              rw [← key, LTm.eval_seq, hk]
              rfl
            · exact key
          · rfl
        | dyn =>
          simp only [Facts.hasIdxDyn]
          split
          · rename_i hlt
            have key : ((LTm.seq i (LTm.seq (LTm.obsL q) LTm.tt)).eval g ν : Option Bool) =
                (LTm.obsH (LTm.index (IndexTy.arr ArrTy.dyn) q i)).eval g ν := by
              rw [LTm.eval_seq, LTm.eval_seq, LTm.eval_obsH, LTm.eval_index]
              exact Facts.hasDyn_core hF hlt
            split
            · rename_i hr
              simp only [Bool.and_eq_true] at hr
              obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF i hr.1)
              obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF q hr.2)
              rw [← key, LTm.eval_seq, LTm.eval_seq, hk, LTm.eval_obsL, hr']
              rfl
            · exact key
          · rfl
    | _ => rfl
  | _ => rfl


end Below

/-! ## Normal forms -/

section Normal

variable {g : State C []} {ν : AEnv}

/-- The two terms are a pair the facts hold apart. -/
def Facts.apart (F : Facts C) {p : PrimTy} (a b : LTm C (.val p)) : Bool :=
  F.nes.any fun e => (a.beqR e.l && b.beqR e.r) || (a.beqR e.r && b.beqR e.l)

theorem Facts.apart_sound {F : Facts C} (hF : F.Ok g ν) {p : PrimTy} {a b : LTm C (.val p)}
    (h : F.apart a b = true) : ∃ x y, (a.eval g ν : Option p.Denote) = some x ∧
      (b.eval g ν : Option p.Denote) = some y ∧ x ≠ y := by
  obtain ⟨e, he, h⟩ := List.any_eq_true.1 h
  obtain ⟨x, y, hx, hy, hne⟩ := hF.nes e he
  obtain ⟨q, l, r⟩ := e
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · cases LTm.sigma_eq_of_beqR h1
    cases LTm.eq_of_beqR h2
    exact ⟨x, y, hx, hy, hne⟩
  · cases LTm.sigma_eq_of_beqR h1
    cases LTm.eq_of_beqR h2
    exact ⟨y, x, hy, hx, fun e => hne e.symm⟩

/-- Two keys compared: `some true` where they are one, `some false` where
they are apart, `none` where the facts do not tell. -/
def Facts.keyCmp (F : Facts C) {p : PrimTy} (a b : LTm C (.val p)) : Option Bool :=
  match a.litV?, b.litV? with
  | some x, some y => some (decide (x = y))
  | _, _ =>
    if a.beqR b && F.returns a then some true
    else if F.apart a b then some false
    else none

theorem Facts.keyCmp_sound {F : Facts C} (hF : F.Ok g ν) {p : PrimTy} {a b : LTm C (.val p)}
    {c : Bool} (h : F.keyCmp a b = some c) : ∃ x y, (a.eval g ν : Option p.Denote) = some x ∧
      (b.eval g ν : Option p.Denote) = some y ∧ decide (x = y) = c := by
  unfold Facts.keyCmp at h
  split at h
  · rename_i x y hx hy
    cases h
    exact ⟨x, y, LTm.eval_litV? g ν hx, LTm.eval_litV? g ν hy, rfl⟩
  · split at h
    · rename_i hb
      cases h
      simp only [Bool.and_eq_true] at hb
      cases LTm.eq_of_beqR hb.1
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF a hb.2)
      exact ⟨x, x, hx, hx, decide_eq_true rfl⟩
    · split at h
      · cases h
        obtain ⟨x, y, hx, hy, hne⟩ := F.apart_sound hF ‹_›
        exact ⟨x, y, hx, hy, decide_eq_false hne⟩
      · cases h

/-- A conditional on keys, its keys compared. -/
def Facts.kiteN (F : Facts C) {p : PrimTy} {s : Srt} (a b : LTm C (.val p)) (t e : LTm C s) :
    LTm C s :=
  match F.keyCmp a b with
  | some true => t
  | some false => e
  | none => if t.beqR e && F.returns a && F.returns b then t else .kite a b t e

theorem Facts.kiteN_eval {F : Facts C} (hF : F.Ok g ν) {p : PrimTy} {s : Srt}
    (a b : LTm C (.val p)) (t e : LTm C s) :
    (F.kiteN a b t e).eval g ν = (LTm.kite a b t e).eval g ν := by
  unfold Facts.kiteN
  split
  · rename_i h
    obtain ⟨x, y, hx, hy, hc⟩ := F.keyCmp_sound hF h
    rw [LTm.eval_kite, hx, hy]
    simp only [Option.bind_some, of_decide_eq_true hc, if_true]
  · rename_i h
    obtain ⟨x, y, hx, hy, hc⟩ := F.keyCmp_sound hF h
    rw [LTm.eval_kite, hx, hy]
    simp only [Option.bind_some, of_decide_eq_false hc, if_false]
  · split
    · rename_i hb
      simp only [Bool.and_eq_true] at hb
      cases LTm.eq_of_beqR hb.1.1
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF a hb.1.2)
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF b hb.2)
      rw [LTm.eval_kite, hx, hy]
      simp only [Option.bind_some, ite_self]
    · rfl

/-- `d; a`, the guard dropped where it returns. -/
def Facts.seqN (F : Facts C) {s' s : Srt} (d : LTm C s') (a : LTm C s) : LTm C s :=
  if F.returns d then a else if d.isErr then .err else .seq d a

theorem Facts.seqN_eval {F : Facts C} (hF : F.Ok g ν) {s' s : Srt} (d : LTm C s') (a : LTm C s) :
    (F.seqN d a).eval g ν = (LTm.seq d a).eval g ν := by
  unfold Facts.seqN
  split
  · rename_i h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF d h)
    rw [LTm.eval_seq, hx]; rfl
  · split
    · rename_i h
      rw [LTm.eval_seq, LTm.eval_of_isErr g ν h]; rfl
    · rfl

/-- `a`, or `b` where it halts: `a` where it returns, `b` where it is `err`. -/
def Facts.orElseN (F : Facts C) {s : Srt} (a b : LTm C s) : LTm C s :=
  if F.returns a then a else if a.isErr then b else .orElse a b

theorem Facts.orElseN_eval {F : Facts C} (hF : F.Ok g ν) {s : Srt} (a b : LTm C s) :
    (F.orElseN a b).eval g ν = (LTm.orElse a b).eval g ν := by
  unfold Facts.orElseN
  split
  · rename_i h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF a h)
    rw [LTm.eval_orElse, hx]; rfl
  · split
    · rename_i h
      rw [LTm.eval_orElse, LTm.eval_of_isErr g ν h]; rfl
    · rfl

/-- A unary symbol folded: on a literal, and `delete`'s value of a term
that returns. -/
def Facts.fold1 (F : Facts C) {a s : Srt} (o : Op1 C a s) (x : LTm C a) : LTm C s :=
  match o, x with
  | @Op1.delValue _ p, x => if F.returns x then .lit (PrimTy.dflt p) else .app1 .delValue x
  | o, x => Decide.fold1 o x

theorem Facts.fold1_eval {F : Facts C} (hF : F.Ok g ν) {a s : Srt} (o : Op1 C a s)
    (x : LTm C a) : (F.fold1 o x).eval g ν = (LTm.app1 o x).eval g ν := by
  cases o
  case delValue p =>
    simp only [Facts.fold1]
    split
    · rename_i h
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF x h)
      rw [LTm.eval_app1, hv]; rfl
    · rfl
  all_goals simp only [Facts.fold1]; exact Decide.fold1_eval g ν _ x

/-- `a < b` by ranges: `true` where the first lies below the second,
`false` where it lies at or above it. -/
def ltDec (rx ry : Int × Int) : Option Bool :=
  if rx.2 < ry.1 then some true else if ry.2 ≤ rx.1 then some false else none

/-- `a <= b` by ranges. -/
def leDec (rx ry : Int × Int) : Option Bool :=
  if rx.2 ≤ ry.1 then some true else if ry.2 < rx.1 then some false else none

theorem ltDec_sound {rx ry : Int × Int} {a b : Int} (ha : InR rx a) (hb : InR ry b) {c : Bool}
    (h : ltDec rx ry = some c) : decide (a < b) = c := by
  unfold ltDec at h
  unfold InR at ha hb
  split at h
  · cases h; exact decide_eq_true (by omega)
  · split at h
    · cases h; exact decide_eq_false (by omega)
    · cases h

theorem leDec_sound {rx ry : Int × Int} {a b : Int} (ha : InR rx a) (hb : InR ry b) {c : Bool}
    (h : leDec rx ry = some c) : decide (a ≤ b) = c := by
  unfold leDec at h
  unfold InR at ha hb
  split at h
  · cases h; exact decide_eq_true (by omega)
  · split at h
    · cases h; exact decide_eq_false (by omega)
    · cases h

/-- The operands of an addition. -/
def Op2.addArgs {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) : Option (EqF C) :=
  match o, x, y with
  | @Op2.binop _ .add p _, x, y => some ⟨p, x, y⟩
  | _, _, _ => none

/-- The operands of an addition. -/
def LTm.addArgs? {s : Srt} (t : LTm C s) : Option (EqF C) :=
  match t with
  | .app2 o x y => Op2.addArgs o x y
  | _ => none

theorem LTm.addArgs?_eq {s : Srt} {t : LTm C s} {e : EqF C} (h : t.addArgs? = some e) :
    ∃ hp : BinOp.add.accepts e.p = true,
      (⟨s, t⟩ : (s : Srt) × LTm C s) = ⟨.val e.p, .app2 (.binop .add hp) e.l e.r⟩ := by
  cases t with
  | app2 o x y =>
    cases o with
    | @binop op p hp =>
      cases op <;> simp only [LTm.addArgs?, Op2.addArgs, reduceCtorEq, Option.some.injEq] at h
      subst h
      exact ⟨hp, rfl⟩
    | _ => simp only [LTm.addArgs?, Op2.addArgs, reduceCtorEq] at h
  | _ => simp only [LTm.addArgs?, reduceCtorEq] at h

/-- `t` at the sort `s'`, where it is that sort. -/
def LTm.castTo? {s s' : Srt} (t : LTm C s) : Option (LTm C s') :=
  if h : s = s' then some (h ▸ t) else none

theorem LTm.castTo?_eq {s s' : Srt} {t : LTm C s} {t' : LTm C s'} (h : t.castTo? = some t') :
    (⟨s, t⟩ : (s : Srt) × LTm C s) = ⟨s', t'⟩ := by
  unfold LTm.castTo? at h
  split at h
  · rename_i e
    subst e
    cases h; rfl
  · cases h

/-- `(a + b) - b`, cancelled to `a` where the sum returns. -/
def Facts.cancel (F : Facts C) {p : PrimTy} (x y : LTm C (.val p)) : Option (LTm C (.val p)) :=
  match x.addArgs? with
  | some e => if e.r.beqR y && F.returns x then e.l.castTo? else none
  | none => none

theorem ofInt?_ival_self {p : PrimTy} (hp : p.isNumeric = true) (v : p.Denote) :
    p.ofInt? (PrimTy.ival v) = some v := by
  cases p with
  | bool => cases hp
  | uint | int =>
    simp only [PrimTy.ofInt?, PrimTy.ofValue?, PrimTy.ival]
    rw [dif_pos v.2]
    rfl

theorem Facts.cancel_eval {F : Facts C} (hF : F.Ok g ν) {p : PrimTy} (hs : BinOp.sub.accepts p = true)
    {x y a : LTm C (.val p)} (h : F.cancel x y = some a) :
    (a.eval g ν : Option p.Denote) = (LTm.app2 (.binop .sub hs) x y).eval g ν := by
  unfold Facts.cancel at h
  split at h
  · rename_i e he
    split at h
    · rename_i hb
      simp only [Bool.and_eq_true] at hb
      obtain ⟨hp, hx⟩ := LTm.addArgs?_eq he
      obtain ⟨q, l, r⟩ := e
      cases hx
      cases LTm.castTo?_eq h
      cases LTm.eq_of_beqR hb.1
      obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF _ hb.2)
      have hnum : q.isNumeric = true := by
        cases q <;> first | rfl | cases hp
      rw [LTm.eval_app2] at hvx
      cases hl : (l.eval g ν : Option q.Denote) with
      | none => rw [hl] at hvx; cases hvx
      | some va =>
        rw [hl] at hvx
        have h1 : binopT .add va (r.eval g ν) = some vx := hvx
        unfold binopT at h1
        simp only [BinOp.shortT] at h1
        cases hr : (r.eval g ν : Option q.Denote) with
        | none => rw [hr] at h1; cases h1
        | some vb =>
          rw [hr, Option.bind_some] at h1
          have hsum := evalT_add h1
          rw [LTm.eval_app2, LTm.eval_app2, hl, hr]
          show some va = (binopT .add va (some vb)).bind fun z => binopT .sub z (some vb)
          unfold binopT
          simp only [BinOp.shortT, Option.bind_some]
          rw [h1, Option.bind_some]
          have hd : PrimTy.ival vx - PrimTy.ival vb = PrimTy.ival va := by omega
          cases q with
          | bool => cases hnum
          | uint =>
            show some va = PrimTy.uint.ofInt? (PrimTy.ival vx - PrimTy.ival vb)
            rw [hd]; exact (ofInt?_ival_self rfl va).symm
          | int =>
            show some va = PrimTy.int.ofInt? (PrimTy.ival vx - PrimTy.ival vb)
            rw [hd]; exact (ofInt?_ival_self rfl va).symm
    · cases h
  · cases h

/-- `x == true` as `x`, `x == false` as `!x`, at `bool`. -/
def eqBoolLit {p : PrimTy} (x y : LTm C (.val p)) : Option (LTm C (.val .bool)) :=
  match p, x, y with
  | .bool, x, y =>
    match y.litV? with
    | some v => some (if (show Bool from v) then x else .app1 (.unop .not rfl) x)
    | none => none
  | _, _, _ => none

theorem eqBoolLit_eval {p : PrimTy} {x y : LTm C (.val p)} {t : LTm C (.val .bool)}
    (h : eqBoolLit x y = some t) (hacc : BinOp.eqB.accepts p = true) :
    (t.eval g ν : Option Bool) = (LTm.app2 (.binop .eqB hacc) x y).eval g ν := by
  cases p with
  | bool =>
    simp only [eqBoolLit] at h
    split at h
    · rename_i v hv
      cases h
      obtain rfl := LTm.eq_of_litV? hv
      rw [LTm.eval_app2]
      cases hx : (x.eval g ν : Option Bool) with
      | none => cases hb : (show Bool from v) <;> simp only [hb, if_true, if_false,
          Bool.false_eq_true, LTm.eval_app1, hx] <;> rfl
      | some u =>
        have hl : ((LTm.lit (p := .bool) v).eval g ν : Option Bool) = some v := rfl
        rw [hl, Op2.eval_eq_evalM]
        simp only [Op2.evalM, Option.bind_some]
        unfold binopT
        simp only [BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalBool]
        cases hb : (show Bool from v) <;> cases u <;>
          simp only [hb, if_true, if_false, Bool.false_eq_true, LTm.eval_app1, hx] <;> rfl
    · cases h
  | uint | int => simp only [eqBoolLit, reduceCtorEq] at h

/-- A comparison folded by its operands' ranges, where both return. -/
def Facts.cmpFold (F : Facts C) {p : PrimTy} (dec : Int × Int → Int × Int → Option Bool)
    (x y : LTm C (.val p)) : Option Bool :=
  if F.returns x && F.returns y then dec (F.range x) (F.range y) else none

/-- A binary symbol folded: on literals, `a == a`, `a != a` on a term that
returns, a comparison of terms whose ranges decide it, and `(a + b) - b`. -/
def Facts.fold2 (F : Facts C) {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    LTm C s :=
  match o, x, y with
  | .binop .eqB h, x, y =>
    if x.beqR y && F.returns x then .lit (p := .bool) true
    else
      match eqBoolLit x y with
      | some t => t
      | none => Decide.fold2 (.binop .eqB h) x y
  | .binop .neB h, x, y =>
    if x.beqR y && F.returns x then .lit (p := .bool) false else Decide.fold2 (.binop .neB h) x y
  | .binop .lt h, x, y =>
    match F.cmpFold ltDec x y with
    | some c => .lit (p := .bool) c
    | none => Decide.fold2 (.binop .lt h) x y
  | .binop .gt h, x, y =>
    match F.cmpFold ltDec y x with
    | some c => .lit (p := .bool) c
    | none => Decide.fold2 (.binop .gt h) x y
  | .binop .le h, x, y =>
    match F.cmpFold leDec x y with
    | some c => .lit (p := .bool) c
    | none => Decide.fold2 (.binop .le h) x y
  | .binop .ge h, x, y =>
    match F.cmpFold leDec y x with
    | some c => .lit (p := .bool) c
    | none => Decide.fold2 (.binop .ge h) x y
  | .binop .sub h, x, y =>
    match F.cancel x y with
    | some t => t
    | none => Decide.fold2 (.binop .sub h) x y
  | o, x, y => Decide.fold2 o x y

theorem Facts.cmpFold_sound {F : Facts C} (hF : F.Ok g ν) {p : PrimTy}
    {dec : Int × Int → Int × Int → Option Bool} {x y : LTm C (.val p)} {c : Bool}
    (h : F.cmpFold dec x y = some c) : ∃ u w, (x.eval g ν : Option p.Denote) = some u ∧
      (y.eval g ν : Option p.Denote) = some w ∧ InR (F.range x) (PrimTy.ival u) ∧
      InR (F.range y) (PrimTy.ival w) ∧ dec (F.range x) (F.range y) = some c := by
  unfold Facts.cmpFold at h
  split at h
  · rename_i hr
    simp only [Bool.and_eq_true] at hr
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF _ hr.1)
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF _ hr.2)
    exact ⟨u, w, hu, hw, F.range_sound hF _ hu, F.range_sound hF _ hw, h⟩
  · cases h

theorem Facts.fold2_eval {F : Facts C} (hF : F.Ok g ν) {a b s : Srt} (o : Op2 C a b s)
    (x : LTm C a) (y : LTm C b) : (F.fold2 o x y).eval g ν = (LTm.app2 o x y).eval g ν := by
  cases o
  case binop op p h =>
    cases op
    case eqB | neB =>
      simp only [Facts.fold2]
      split
      · rename_i hb
        simp only [Bool.and_eq_true] at hb
        cases LTm.eq_of_beqR hb.1
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF x hb.2)
        rw [LTm.eval_app2, hv]
        refine Eq.trans (b := some _) rfl ?_
        show _ = binopT _ v (some v)
        cases p <;> simp only [binopT, BinOp.shortT, Option.bind_some, BinOp.evalT,
          BinOp.evalNum, BinOp.evalBool, decide_true, Bool.not_true]
      · first
          | (split
             · rename_i t ht
               exact eqBoolLit_eval ht h
             · exact Decide.fold2_eval g ν _ x y)
          | exact Decide.fold2_eval g ν _ x y
    case lt | gt | le | ge =>
      have hnum : p.isNumeric = true := by
        cases p <;> first | rfl | cases h
      simp only [Facts.fold2]
      split
      · rename_i c hc
        obtain ⟨u, w, hu, hw, ru, rw', hd⟩ := F.cmpFold_sound hF hc
        simp only [LTm.eval_app2, hu, hw]
        rw [Op2.eval_eq_evalM]
        simp only [Op2.evalM, Option.bind_some]
        unfold binopT
        cases p with
        | bool => cases hnum
        | uint | int =>
          simp only [BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum]
          first
            | exact congrArg some (ltDec_sound ru rw' hd).symm
            | exact congrArg some (leDec_sound ru rw' hd).symm
      · exact Decide.fold2_eval g ν _ x y
    case sub =>
      simp only [Facts.fold2]
      split
      · rename_i t ht
        exact Facts.cancel_eval hF h ht
      · exact Decide.fold2_eval g ν _ x y
    all_goals simp only [Facts.fold2]; exact Decide.fold2_eval g ν _ x y
  all_goals simp only [Facts.fold2]; exact Decide.fold2_eval g ν _ x y

/-- A ternary symbol folded: a conditional on a literal, or with one
branch twice. -/
def Facts.fold3 (F : Facts C) {a b c s : Srt} (o : Op3 C a b c s) (x : LTm C a) (y : LTm C b)
    (z : LTm C c) : LTm C s :=
  match o, x, y, z with
  | .ite, x, y, z =>
    match x.litV? with
    | some v => cond (v : Bool) y z
    | none =>
      if y.beqR z && F.returns x then y
      else if y.beqR x && z.beqR (LTm.tt : LTm C (.val .bool)) && F.returns x then
        match (LTm.tt : LTm C (.val .bool)).castTo? with
        | some t => t
        | none => .app3 .ite x y z
      else .app3 .ite x y z
  | o, x, y, z => .app3 o x y z

theorem Facts.fold3_eval {F : Facts C} (hF : F.Ok g ν) {a b c s : Srt} (o : Op3 C a b c s)
    (x : LTm C a) (y : LTm C b) (z : LTm C c) :
    (F.fold3 o x y z).eval g ν = (LTm.app3 o x y z).eval g ν := by
  cases o
  case ite p =>
    simp only [Facts.fold3]
    split
    · rename_i v hv
      obtain rfl := LTm.eq_of_litV? hv
      show _ = cond (v : Bool) _ _
      cases (v : Bool) <;> rfl
    · split
      · rename_i hb
        simp only [Bool.and_eq_true] at hb
        cases LTm.eq_of_beqR hb.1
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF x hb.2)
        rw [LTm.eval_app3, hv]
        show _ = cond (v : Bool) _ _
        cases (v : Bool) <;> rfl
      · split
        · rename_i hb
          simp only [Bool.and_eq_true] at hb
          obtain ⟨⟨h1, h2⟩, h3⟩ := hb
          cases LTm.sigma_eq_of_beqR h1
          cases LTm.sigma_eq_of_beqR h2
          split
          · rename_i t ht
            cases LTm.castTo?_eq ht
            obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF x h3)
            rw [LTm.eval_app3, hv]
            show some true = cond (v : Bool) _ _
            cases (v : Bool) <;> rfl
          · rfl
        · rfl
  all_goals rfl

/-- `Facts.nf`'s compiled twin. -/
def Facts.nfM (F : Facts C) : {s : Srt} → LTm C s → LTm C s
  | _, .var k => F.rw (.var k)
  | _, .app0 o => .app0 o
  | _, .app1 o x => F.rw (F.fold1 o (F.nfM x))
  | _, .app2 o x y => F.rw (F.fold2 o (F.nfM x) (F.nfM y))
  | _, .app3 o x y z => F.rw (F.fold3 o (F.nfM x) (F.nfM y) (F.nfM z))
  | _, .index it q i => .index it (F.nfM q) (F.nfM i)
  | _, .obsW q => F.rw (.obsW (F.nfM q))
  | _, .obsL q => F.rw (.obsL (F.nfM q))
  | _, .obsH q => F.rw (F.hasRange (hasN (.obsH (F.nfM q))))
  | _, .seq d a => F.seqN (F.nfM d) (F.nfM a)
  | _, .orElse a b => F.orElseN (F.nfM a) (F.nfM b)
  | _, .kite a b t e => F.kiteN (F.nfM a) (F.nfM b) (F.nfM t) (F.nfM e)
  | _, .err => .err

/-- **A term's normal form under the facts**, bottom-up: symbols folded,
guards that return dropped, keys compared, what a premise rewrites
rewritten.  By the recursor. -/
@[implemented_by Facts.nfM]
def Facts.nf (F : Facts C) {s : Srt} (t : LTm C s) : LTm C s :=
  @LTm.rec C (fun s _ => LTm C s)
    (@fun _ k => F.rw (.var k))
    (@fun _ o => .app0 o)
    (@fun _ _ o _ ihx => F.rw (F.fold1 o ihx))
    (@fun _ _ _ o _ _ ihx ihy => F.rw (F.fold2 o ihx ihy))
    (@fun _ _ _ _ o _ _ _ ihx ihy ihz => F.rw (F.fold3 o ihx ihy ihz))
    (@fun _ _ _ it _ _ ihq ihi => .index it ihq ihi)
    (@fun _ _ ih => F.rw (.obsW ih))
    (@fun _ _ ih => F.rw (.obsL ih))
    (@fun _ _ ih => F.rw (F.hasRange (hasN (.obsH ih))))
    (@fun _ _ _ _ ihd iha => F.seqN ihd iha)
    (@fun _ _ _ iha ihb => F.orElseN iha ihb)
    (@fun _ _ _ _ _ _ iha ihb iht ihe => F.kiteN iha ihb iht ihe)
    (@fun _ => .err) s t

theorem Facts.nf_eq_nfM (F : Facts C) {s : Srt} (t : LTm C s) : F.nf t = F.nfM t := by
  induction t with
  | var | app0 | err => rfl
  | app1 o x ih => simp only [Facts.nfM, ← ih]; rfl
  | app2 o x y ihx ihy => simp only [Facts.nfM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => simp only [Facts.nfM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => simp only [Facts.nfM, ← ihq, ← ihi]; rfl
  | obsW q ih | obsL q ih | obsH q ih => simp only [Facts.nfM, ← ih]; rfl
  | seq d a ihd iha => simp only [Facts.nfM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => simp only [Facts.nfM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe => simp only [Facts.nfM, ← iha, ← ihb, ← iht, ← ihe]; rfl

/-- **The normal form reads what the term reads.** -/
theorem Facts.nf_eval {F : Facts C} (hF : F.Ok g ν) {s : Srt} (t : LTm C s) :
    (F.nf t).eval g ν = t.eval g ν := by
  induction t with
  | var k => exact F.rw_eval hF _
  | app0 o => rfl
  | err => rfl
  | app1 o x ih =>
    show (F.rw (F.fold1 o (F.nf x))).eval g ν = _
    rw [F.rw_eval hF, F.fold1_eval hF, LTm.eval_app1, LTm.eval_app1, ih]
  | app2 o x y ihx ihy =>
    show (F.rw (F.fold2 o (F.nf x) (F.nf y))).eval g ν = _
    rw [F.rw_eval hF, F.fold2_eval hF, LTm.eval_app2, LTm.eval_app2, ihx, ihy]
  | app3 o x y z ihx ihy ihz =>
    show (F.rw (F.fold3 o (F.nf x) (F.nf y) (F.nf z))).eval g ν = _
    rw [F.rw_eval hF, F.fold3_eval hF, LTm.eval_app3, LTm.eval_app3, ihx, ihy, ihz]
  | index it q i ihq ihi =>
    show (LTm.index it (F.nf q) (F.nf i)).eval g ν = _
    rw [LTm.eval_index, LTm.eval_index, ihq, ihi]
  | obsW q ih =>
    show (F.rw (.obsW (F.nf q))).eval g ν = _
    rw [F.rw_eval hF, LTm.eval_obsW, LTm.eval_obsW, ih]
  | obsL q ih =>
    show (F.rw (.obsL (F.nf q))).eval g ν = _
    rw [F.rw_eval hF, LTm.eval_obsL, LTm.eval_obsL, ih]
  | obsH q ih =>
    show (F.rw (F.hasRange (hasN (.obsH (F.nf q))))).eval g ν = _
    rw [F.rw_eval hF, F.hasRange_eval hF, hasN_eval, LTm.eval_obsH, LTm.eval_obsH, ih]
  | seq d a ihd iha =>
    show (F.seqN (F.nf d) (F.nf a)).eval g ν = _
    rw [F.seqN_eval hF, LTm.eval_seq, LTm.eval_seq, ihd, iha]
  | orElse a b iha ihb =>
    show (F.orElseN (F.nf a) (F.nf b)).eval g ν = _
    rw [F.orElseN_eval hF, LTm.eval_orElse, LTm.eval_orElse, iha, ihb]
  | kite a b t e iha ihb iht ihe =>
    show (F.kiteN (F.nf a) (F.nf b) (F.nf t) (F.nf e)).eval g ν = _
    rw [F.kiteN_eval hF, LTm.eval_kite, LTm.eval_kite, iha, ihb, iht, ihe]

end Normal

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

/-- The rewrite `a ≐ b` gives, their normal forms oriented (`orient`). -/
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

/-- The premise `a ≐ b` alone: both normal forms return, with their strict
subterms, and the one rewrites to the other. -/
def Facts.addEq1 (F : Facts C) {p : PrimTy} (a b : LTm C (.val p)) : Facts C :=
  ((F.addRets (F.nf a)).addRets (F.nf b)).addEqR a b

theorem Facts.addEq1_ok {F : Facts C} {ν : AEnv} (hF : F.Ok g ν) {p : PrimTy}
    {a b : LTm C (.val p)} (h : (LFml.eq a b).holds g ν) : (F.addEq1 a b).Ok g ν := by
  obtain ⟨x, ha, hb⟩ := (LFml.holds_eq_iff g ν a b).1 h
  rw [← F.nf_eval hF] at ha hb
  exact Facts.addEqR_ok (Facts.addRets_ok (Facts.addRets_ok hF (by rw [ha]; rfl))
    (by rw [hb]; rfl)) h

/-- The premise `¬ a ≐ b` alone: where both normal forms return, they are
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

`c ≐ true` with `c` an equation, a conjunction, a negation is taken apart
(KeY's `equal_literals`, `andLeft`, `notLeft` on the formula a boolean term
reads); `assert(c)` returning is `c ≐ true`. -/

theorem evalT_eqB {p : PrimTy} (u w : p.Denote) :
    BinOp.evalT .eqB u w = some (decide (u = w)) := by
  cases p
  · rfl
  · show some (decide (u.1 = w.1)) = _
    simp only [Option.some.injEq, decide_eq_decide]
    exact Subtype.ext_iff.symm
  · show some (decide (u.1 = w.1)) = _
    simp only [Option.some.injEq, decide_eq_decide]
    exact Subtype.ext_iff.symm

theorem evalT_neB {p : PrimTy} (u w : p.Denote) :
    BinOp.evalT .neB u w = some (!decide (u = w)) := by
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
    cases strict <;> simp_all
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

/-- The facts a binary symbol on two values gives, read as `v`. -/
def Facts.boolStep (ih : Facts C → LTm C (.val .bool) → Bool → Facts C) (F : Facts C)
    {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) (v : Bool) : Facts C :=
  match o, x, y with
  | .binop .eqB _, x, y => if v then F.addEq1 x y else F.addNe1 x y
  | .binop .neB _, x, y => if v then F.addNe1 x y else F.addEq1 x y
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
    (h : binopT .eqB u y = some v) : ∃ w, y = some w ∧ v = decide (u = w) := by
  unfold binopT at h
  cases p <;> simp only [BinOp.shortT] at h <;>
  · cases y with
    | none => cases h
    | some w =>
      rw [Option.bind_some, evalT_eqB, Option.some.injEq] at h
      exact ⟨w, rfl, h.symm⟩

theorem binopT_neB {p : PrimTy} {u : p.Denote} {y : Option p.Denote} {v : Bool}
    (h : binopT .neB u y = some v) : ∃ w, y = some w ∧ v = !decide (u = w) := by
  unfold binopT at h
  cases p <;> simp only [BinOp.shortT] at h <;>
  · cases y with
    | none => cases h
    | some w =>
      rw [Option.bind_some, evalT_neB, Option.some.injEq] at h
      exact ⟨w, rfl, h.symm⟩

theorem binopT_and {u : Bool} {y : Option Bool} (h : binopT (p := .bool) .and u y = some true) :
    u = true ∧ y = some true := by
  unfold binopT at h
  cases u
  · cases h
  · cases y with
    | none => cases h
    | some w => cases w <;> first | exact ⟨rfl, rfl⟩ | cases h

theorem binopT_or {u : Bool} {y : Option Bool} (h : binopT (p := .bool) .or u y = some false) :
    u = false ∧ y = some false := by
  unfold binopT at h
  cases u
  · cases y with
    | none => cases h
    | some w => cases w <;> first | exact ⟨rfl, rfl⟩ | cases h
  · cases h

/-- The premise `x ≐ y` where `x == y` reads `v`. -/
theorem Facts.eqB_ok {ν : AEnv} {F : Facts C} (hF : F.Ok g ν) {p : PrimTy}
    {x y : LTm C (.val p)} {u w : p.Denote} (hx : (x.eval g ν : Option p.Denote) = some u)
    (hy : (y.eval g ν : Option p.Denote) = some w) (v : Bool) (hv : v = decide (u = w)) :
    (if v then F.addEq1 x y else F.addNe1 x y).Ok g ν := by
  split
  · rename_i hvt
    rw [hvt, eq_comm, decide_eq_true_iff] at hv
    exact Facts.addEq1_ok hF ((LFml.holds_eq_iff g ν x y).2 ⟨u, hx, hv ▸ hy⟩)
  · rename_i hvt
    refine Facts.addNe1_ok hF fun hh => hvt ?_
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
        cases v <;> simpa using this
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

/-- **The premise `c ≐ v`**, `c` boolean: the rewrite, and what `c` says
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

/-- `assert(c)` (`ite(c, true, err)`), its condition. -/
def assertArg? {s : Srt} (t : LTm C s) : Option (LTm C (.val .bool)) :=
  match t with
  | .app3 o x y z => Op3.assertArg o x y z
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

/-- Every fact read again under the others: each rewrite and each pair
apart normalized under the ones newer than it, each term that returns
under all (KeY's `applyEq` on the antecedent). -/
def Facts.rebuild (F : Facts C) : Facts C :=
  let G1 := F.eqs.foldl (fun G e => G.addEqR e.l e.r) { F with eqs := [], nes := [] }
  let G2 := F.nes.foldl (fun G e => G.addNe1 e.l e.r) G1
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
  have h0 : ({ F with eqs := [], nes := [] } : Facts C).Ok g ν :=
    ⟨fun _ h => (nomatch h), fun _ h => (nomatch h), hF.rets, hF.bnds⟩
  have h2 := Facts.foldl_addNe1_ok F.nes (Facts.foldl_addEqR_ok F.eqs h0 hF.eqs) hF.nes
  refine ⟨h2.eqs, h2.nes, fun u hu => ?_, fun b hb v hv => ?_⟩
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
    show ((Facts.nf _ w.2).eval g ν).isSome = true
    rw [Facts.nf_eval h2]
    exact h2.rets w hw
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hb
    have hv' : (w.t.eval g ν : Option w.p.Denote) = some v := by
      rw [← Facts.nf_eval h2]; exact hv
    exact h2.bnds w hw v hv'

/-- `p ≐ v` at `bool`, a side a literal: the other side and `v`. -/
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

/-- **The premise `a ≐ b`**: `addEq1`, the `assert`s among its terms, a
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

theorem _root_.Solidity.PrimTy.ival_inj : {p : PrimTy} → {u w : p.Denote} →
    PrimTy.ival u = PrimTy.ival w → u = w
  | .bool, u, w, h => by
    cases hu : (show Bool from u) <;> cases hw : (show Bool from w) <;>
      simp only [PrimTy.ival, hu, hw] at h <;> first | rfl | cases h |
      (exact (show (u : Bool) = w from hu.trans hw.symm))
  | .uint, _, _, h => Subtype.ext h
  | .int, _, _, h => Subtype.ext h

/-- The premise `¬ a ≐ v`, `v` a literal at an edge of `a`'s range: the
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

/-- The premise `¬ a ≐ b` with a side a literal: the other's range narrowed. -/
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

/-- **The premise `¬ a ≐ b`**: `addNe1`, a boolean side read apart, and the
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

/-- A `bool` atom to split on: `x ≐ true` or not. -/
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

/-- `a ≐ b` by the normal forms: one term, which returns. -/
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

/-- `a ≐ b` by the normal forms, splitting on a key comparison at most
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

/-- `a ≐ b` is false by the normal forms: two literals that differ, a
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

/-! ## A bound on the work -/

section Fits

/-- One node, its subterms counted after it: `none` out of fuel. -/
def fitsNode (n : Nat) (k : Nat → Option Nat) : Option Nat :=
  match n with
  | 0 => none
  | n + 1 => k n

/-- `LTm.fits`' compiled twin. -/
def LTm.fitsM : {s : Srt} → LTm C s → Nat → Option Nat
  | _, .var _, n | _, .app0 _, n | _, .err, n => fitsNode n some
  | _, .app1 _ x, n | _, .obsW x, n | _, .obsL x, n | _, .obsH x, n => fitsNode n x.fitsM
  | _, .app2 _ x y, n | _, .index _ x y, n | _, .seq x y, n | _, .orElse x y, n =>
    fitsNode n fun m => (x.fitsM m).bind y.fitsM
  | _, .app3 _ x y z, n => fitsNode n fun m => ((x.fitsM m).bind y.fitsM).bind z.fitsM
  | _, .kite a b t e, n =>
    fitsNode n fun m => (((a.fitsM m).bind b.fitsM).bind t.fitsM).bind e.fitsM

/-- **`t` has at most `n` nodes**, counted as a tree: the fuel left.  By
the recursor. -/
@[implemented_by LTm.fitsM]
def LTm.fits {s : Srt} (t : LTm C s) : Nat → Option Nat :=
  @LTm.rec C (fun _ _ => Nat → Option Nat)
    (@fun _ _ n => fitsNode n some) (@fun _ _ n => fitsNode n some)
    (@fun _ _ _ _ ihx n => fitsNode n ihx)
    (@fun _ _ _ _ _ _ ihx ihy n => fitsNode n fun m => (ihx m).bind ihy)
    (@fun _ _ _ _ _ _ _ _ ihx ihy ihz n => fitsNode n fun m => ((ihx m).bind ihy).bind ihz)
    (@fun _ _ _ _ _ _ ihq ihi n => fitsNode n fun m => (ihq m).bind ihi)
    (@fun _ _ ih n => fitsNode n ih) (@fun _ _ ih n => fitsNode n ih)
    (@fun _ _ ih n => fitsNode n ih)
    (@fun _ _ _ _ ihd iha n => fitsNode n fun m => (ihd m).bind iha)
    (@fun _ _ _ iha ihb n => fitsNode n fun m => (iha m).bind ihb)
    (@fun _ _ _ _ _ _ iha ihb iht ihe n =>
      fitsNode n fun m => (((iha m).bind ihb).bind iht).bind ihe)
    (@fun _ n => fitsNode n some) s t

theorem LTm.fits_eq_fitsM {s : Srt} (t : LTm C s) : t.fits = t.fitsM := by
  induction t with
  | var | app0 | err => funext n; rfl
  | app1 o x ih => funext n; simp only [LTm.fitsM, ← ih]; rfl
  | app2 o x y ihx ihy => funext n; simp only [LTm.fitsM, ← ihx, ← ihy]; rfl
  | app3 o x y z ihx ihy ihz => funext n; simp only [LTm.fitsM, ← ihx, ← ihy, ← ihz]; rfl
  | index it q i ihq ihi => funext n; simp only [LTm.fitsM, ← ihq, ← ihi]; rfl
  | obsW q ih | obsL q ih | obsH q ih => funext n; simp only [LTm.fitsM, ← ih]; rfl
  | seq d a ihd iha => funext n; simp only [LTm.fitsM, ← ihd, ← iha]; rfl
  | orElse a b iha ihb => funext n; simp only [LTm.fitsM, ← iha, ← ihb]; rfl
  | kite a b t e iha ihb iht ihe =>
    funext n; simp only [LTm.fitsM, ← iha, ← ihb, ← iht, ← ihe]; rfl

/-- `LFml.fits`' compiled twin. -/
def LFml.fitsM : LFml C → Nat → Option Nat
  | .tt, n => fitsNode n some
  | .eq a b, n => fitsNode n fun m => (a.fits m).bind b.fits
  | .not φ, n | .all _ _ φ, n => fitsNode n φ.fitsM
  | .and φ ψ, n | .imp φ ψ, n => fitsNode n fun m => (φ.fitsM m).bind ψ.fitsM

/-- **`φ` has at most `n` nodes**, counted as a tree: its terms share
subterms, a storage written from a read of the one before it twice, so the
tree doubles with each such write.  By the recursor. -/
@[implemented_by LFml.fitsM]
def LFml.fits (φ : LFml C) : Nat → Option Nat :=
  @LFml.rec C (fun _ => Nat → Option Nat)
    (fun n => fitsNode n some)
    (@fun _ a b n => fitsNode n fun m => (a.fits m).bind b.fits)
    (fun _ ih n => fitsNode n ih)
    (fun _ _ ihφ ihψ n => fitsNode n fun m => (ihφ m).bind ihψ)
    (fun _ _ ihφ ihψ n => fitsNode n fun m => (ihφ m).bind ihψ)
    (fun _ _ _ ih n => fitsNode n ih) φ

theorem LFml.fits_eq_fitsM (φ : LFml C) : φ.fits = φ.fitsM := by
  induction φ with
  | tt | eq => funext n; rfl
  | not φ ih | all k p φ ih => funext n; simp only [LFml.fitsM, ← ih]; rfl
  | and φ ψ ihφ ihψ | imp φ ψ ihφ ihψ => funext n; simp only [LFml.fitsM, ← ihφ, ← ihψ]; rfl

end Fits

end Decide

end Solidity
