import Solidity.Calculus.DecideLang
import Solidity.Calculus.ReadBounds
import Solidity.Calculus.TermEq
import Solidity.Calculus.Decide

/-!
# The closer: a reduction closed by its terms

`sol_prove`'s leaves, reduced (`Fml.reduceS`), are typed first-order
formulas over the starting state (`LFml`, `Calculus/DecideLang.lean`).
KeY closes them with its simplification taclets, each a proof step; here
they are clauses of one function, `LFml.close`, proved sound once
(`LFml.close_valid`), so that the kernel checks a leaf by evaluation.

What it knows at a point of a leaf is a `Facts`: terms that return, pairs
of terms equal (a rewrite, left to right: KeY's `applyEq`) or apart.  A
premise adds to it (`LFml.yesM`: an equation, its `assert`s and guards
read `true`, its `bool` sides taken apart); a term is read in its normal
form under the facts (`Facts.nf`): every symbol on literals evaluated
(KeY's literal and `intSimplification` taclets), a guard that returns
dropped, a key compared with itself or with one it is apart from read as
its branch (`select(store(h, k, v), j)` under `k = j` or `k ≠ j`), a
comparison of two terms apart folded, `(a - b) + b` and `(a + b) - b`
cancelled, `2 * a` read as `a + a`, `a < a + c` read `true` (Lean only),
and a subterm (a constant included) the premises know rewritten.  A conclusion `a = b` holds where the two normal
forms are one term that returns; where a key comparison is left open, the
closer splits on it (`LTm.pick`, KeY's `cut` on `k = j`).

Since W10.4 the terms are typed: a value is in range by its type, the
storage has the shape its contract declares, so no layout premise and no
kind test is left to the closer.

The functions the kernel evaluates are written with their recursors, each
with a `match` twin for compiled code (Gate G0).
-/

namespace Solidity

namespace Decide

variable {C : Contract}


/-! ## What the symbols read -/

section Symbols

variable (g : State C [])

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
    show binopT op _ x none = none
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
  | .cleanTail => false
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
  case cleanTail => simp only [Op1.total, Bool.false_eq_true] at h
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
  | .zbin _ _ | .zcmp _ _ | .mat _ | .copy _ | .copySt _ | .keccak => true
  | _ => false

theorem _root_.Solidity.Op2.total_isSome {a b s : Srt} (o : Op2 C a b s) (h : o.total = true)
    (x : a.Den C g.H) (y : b.Den C g.H) : (o.eval g (some x) (some y)).isSome = true := by
  cases o
  case binop op p hp =>
    simp only [Op2.total] at h
    show (binopT op _ x (some y)).isSome = true
    unfold binopT
    cases op <;> simp only [BinOp.totalB, Bool.false_eq_true] at h <;>
      cases p <;> first | exact absurd hp (by decide) | skip <;>
      first | rfl | (cases (x : Bool) <;> rfl)
  case zbin | zcmp | mat | copy | copySt | keccak => rfl
  all_goals simp only [Op2.total, Bool.false_eq_true] at h

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
  -- Lean only: a `uint`'s remainder by a positive literal is below it
  | @Op2.binop _ .mod .uint _, _, y =>
    match y.litV? with
    | some c => if 0 < PrimTy.ival c then some (0, PrimTy.ival c - 1) else none
    | none => none
  | _, _, _ => none

theorem ofInt?_ival {p : PrimTy} {n : Int} {v : p.Denote} (h : p.ofInt? n = some v) :
    PrimTy.ival v = n := by
  cases p with
  | bool => simp only [PrimTy.ofInt?, reduceCtorEq] at h
  | uint =>
    simp only [PrimTy.ofInt?] at h
    split at h
    · cases h; rfl
    · cases h
  | int =>
    simp only [PrimTy.ofInt?] at h
    split at h
    · cases h; rfl
    · cases h

theorem ofInt?_isSome {p : PrimTy} (hp : p.isNumeric = true) {n : Int} (h1 : p.lo ≤ n)
    (h2 : n ≤ p.hi) : (p.ofInt? n).isSome = true := by
  cases p with
  | bool => cases hp
  | uint =>
    simp only [PrimTy.lo, PrimTy.hi] at h1 h2
    simp only [PrimTy.ofInt?]
    rw [dif_pos (by simp only [PrimTy.inRange, decide_eq_true_eq]; omega)]; rfl
  | int =>
    simp only [PrimTy.lo, PrimTy.hi] at h1 h2
    simp only [PrimTy.ofInt?]
    rw [dif_pos (by simp only [PrimTy.inRange, decide_eq_true_eq]; omega)]; rfl

theorem evalT_add {p : PrimTy} {hp : BinOp.add.accepts p = true} {u w v : p.Denote}
    (h : BinOp.evalT .add hp u w = some v) :
    PrimTy.ival v = PrimTy.ival u + PrimTy.ival w := by
  cases p with
  | bool => exact absurd hp (by decide)
  | uint | int =>
    simp only [BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Option.bind_some] at h
    exact ofInt?_ival h

theorem evalT_mul {p : PrimTy} {hp : BinOp.mul.accepts p = true} {u w v : p.Denote}
    (h : BinOp.evalT .mul hp u w = some v) :
    PrimTy.ival v = PrimTy.ival u * PrimTy.ival w := by
  cases p with
  | bool => exact absurd hp (by decide)
  | uint | int =>
    simp only [BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Option.bind_some] at h
    exact ofInt?_ival h

theorem evalT_sub {p : PrimTy} {hp : BinOp.sub.accepts p = true} {u w v : p.Denote}
    (h : BinOp.evalT .sub hp u w = some v) :
    PrimTy.ival v = PrimTy.ival u - PrimTy.ival w := by
  cases p with
  | bool => exact absurd hp (by decide)
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
        have h' : binopT _ _ u (y.eval g ν) = some v := h
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
    case mod =>
      cases q <;> simp only [Facts.rangeOp, reduceCtorEq] at hr
      cases hs
      split at hr
      · rename_i c hc
        split at hr
        · rename_i hc0
          simp only [Option.some.injEq] at hr
          subst hr
          obtain rfl := LTm.eq_of_litV? hc
          cases hx : (x.eval g ν : Option PrimTy.uint.Denote) with
          | none => rw [hx] at h; cases h
          | some u =>
            rw [hx] at h
            have h' : binopT .mod hop u (some c) = some v := h
            unfold binopT at h'
            simp only [BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum,
              BinOp.arithInt] at h'
            have hu := PrimTy.ival_mem u
            simp only [PrimTy.ival, PrimTy.lo] at hu hc0
            rw [if_neg (by omega), Option.bind_some] at h'
            have hv := ofInt?_ival h'
            simp only [PrimTy.ival] at hv
            show InR (0, c.val - 1) (v : PrimTy.uint.Denote).1
            rw [hv, Int.tmod_eq_emod_of_nonneg hu.1]
            unfold InR
            exact ⟨Int.emod_nonneg _ (by omega), by have := Int.emod_lt_of_pos u.1 hc0; omega⟩
        · cases hr
      · cases hr
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
  -- Lean only: a product of `uint`s whose ranges keep it in range, a `uint`
  -- shifted right, or its remainder by a positive literal
  | @Op2.binop _ .mul .uint _, x, y =>
    decide (0 ≤ (F.range x).1) && decide (0 ≤ (F.range y).1) &&
      decide ((F.range x).2 * (F.range y).2 ≤ PrimTy.uint.hi)
  | @Op2.binop _ .shr .uint _, _, _ => true
  | @Op2.binop _ .mod .uint _, _, y =>
    match y.litV? with
    | some c => decide (0 < PrimTy.ival c)
    | none => false
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
      show (binopT _ _ u (some w)).isSome = true
      unfold binopT
      cases q
      · cases hq
      all_goals
        simp only [BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum, BinOp.arithInt]
        exact ofInt?_isSome rfl (by simp only [PrimTy.ival] at ru rw'; omega)
          (by simp only [PrimTy.ival] at ru rw'; omega)
    case mul =>
      cases q <;> simp only [Facts.arithOk, Bool.false_eq_true] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have ru := F.range_sound hF x hx
      have rw' := F.range_sound hF y hy
      unfold InR at ru rw'
      show (binopT .mul hop u (some w)).isSome = true
      unfold binopT
      simp only [BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum, BinOp.arithInt]
      simp only [PrimTy.ival] at ru rw'
      have hm : (u : PrimTy.uint.Denote).1 * (w : PrimTy.uint.Denote).1 ≤ (F.range x).2 * (F.range y).2 :=
        Int.mul_le_mul ru.2 rw'.2 (by omega) (by omega)
      exact ofInt?_isSome rfl (by simp only [PrimTy.lo]; exact Int.mul_nonneg (by omega) (by omega))
        (by omega)
    case shr =>
      cases q <;> simp only [Facts.arithOk, Bool.false_eq_true] at h
      show (binopT .shr hop u (some w)).isSome = true
      unfold binopT
      simp only [BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum, BinOp.arithInt]
      have hu := (PrimTy.ival_mem u)
      simp only [PrimTy.ival, PrimTy.lo, PrimTy.hi] at hu
      split
      · have h2 : (0 : Int) < 2 ^ (w : PrimTy.uint.Denote).1.toNat := Int.pow_pos (by decide)
        exact ofInt?_isSome rfl (by simp only [PrimTy.lo]; exact Int.ediv_nonneg hu.1 (Int.le_of_lt h2))
          (by have := Int.ediv_le_self (2 ^ (w : PrimTy.uint.Denote).1.toNat) hu.1
              simp only [PrimTy.hi]; omega)
      · rw [if_neg (by omega)]
        exact ofInt?_isSome rfl (by simp only [PrimTy.lo]; omega) (by simp only [PrimTy.hi]; omega)
    case mod =>
      cases q <;> simp only [Facts.arithOk, Bool.false_eq_true] at h
      split at h
      · rename_i c hc
        simp only [decide_eq_true_eq] at h
        obtain rfl := LTm.eq_of_litV? hc
        have hw : w = c := (Option.some.inj hy).symm
        subst hw
        show (binopT .mod hop u (some w)).isSome = true
        unfold binopT
        simp only [BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum, BinOp.arithInt]
        have hu := (PrimTy.ival_mem u)
        have hwr := (PrimTy.ival_mem w)
        simp only [PrimTy.ival, PrimTy.lo, PrimTy.hi] at hu hwr h
        rw [if_neg (by omega), Option.bind_some, Int.tmod_eq_emod_of_nonneg hu.1]
        exact ofInt?_isSome rfl (by simp only [PrimTy.lo]; exact Int.emod_nonneg _ (by omega))
          (by have := Int.emod_lt_of_pos (u : PrimTy.uint.Denote).1 h
              simp only [PrimTy.hi]; omega)
      · cases h
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

/-- `has` at an entry: a mapping's where its base has one, its key
returning. -/
def hasIdx {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V) (q : LTm C (.path (.ref R)))
    (i : LTm C (.val k)) : LTm C (.val .bool) :=
  @IndexTy.casesOn (fun R k V _ => LTm C (.path (.ref R)) → LTm C (.val k) → LTm C (.val .bool))
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

theorem findM_at_isSome {E : Ty} (v : SVal (.ref (.array E))) {i : PrimTy.uint.Denote} (h0 : 0 ≤ i.1)
    (hi : i.1 < ((SVal.view v : ArrView E).n : Int)) : (v.findM (.at i .nil)).isSome = true := by
  cases v with
  | array e sh hn =>
    simp only [SVal.view] at hi
    simp only [SVal.findM, if_pos h0]
    have hl : i.1.toNat < e.toList.length := by rw [SVec.length_toList]; omega
    rw [List.getElem?_append_left hl, List.getElem?_eq_getElem hl]
    simp only [SVal.findM_nil', Option.isSome_some]

theorem has_below (st : Storage C) {E : Ty} (r : SRef C (.ref (.array E))) {i : PrimTy.uint.Denote}
    (h0 : 0 ≤ i.1) (hi : i.1 < (st.obs.len (.ref r) : Int)) :
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

theorem findM_atF_isSome {E : Ty} {n : Nat} (v : SVal (.ref (.fixed E n))) {i : PrimTy.uint.Denote} (h0 : 0 ≤ i.1)
    (hi : i.1 < (n : Int)) : (v.findM (.atF i .nil)).isSome = true := by
  cases v with
  | fixed e =>
    simp only [SVal.findM, if_pos h0]
    have hl : i.1.toNat < e.toList.length := by rw [SVec.length_toList]; omega
    rw [List.getElem?_eq_getElem hl]
    simp only [SVal.findM_nil', Option.isSome_some]

/-- `has` at a dynamic array's index the ranges put below its length. -/
def Facts.hasIdxDyn (F : Facts C) {R : RefTy} {k : PrimTy} {V : Ty} (it : IndexTy R k V)
    (q : LTm C (.path (.ref R))) (i : LTm C (.val k)) : LTm C (.val .bool) :=
  @IndexTy.casesOn
    (fun R k V _ => LTm C (.path (.ref R)) → LTm C (.val k) → LTm C (.val .bool))
    R k V it (fun {_} {_} q i => .obsH (.index .map q i))
    (fun a => @ArrTy.casesOn
      (fun R E a => LTm C (.path (.ref R)) → LTm C (.val PrimTy.uint) → LTm C (.val .bool))
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
    {q : LTm C (.path (.ref (.array E)))} {i : LTm C (.val PrimTy.uint)}
    (hlt : (F.range i).2 < (F.range (.obsL q)).1) :
    ((i.eval g ν : Option PrimTy.uint.Denote).bind fun _ =>
      ((LTm.obsL q).eval g ν : Option PrimTy.uint.Denote).bind fun _ =>
        (LTm.tt.eval g ν : Option Bool)) =
    (((q.eval g ν : Option (SRef C (.ref (.array E)))).bind fun r =>
      (i.eval g ν : Option PrimTy.uint.Denote).bind fun j =>
        some (r.index (IndexTy.arr ArrTy.dyn) j)).bind fun r =>
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
      rw [ival_uintOfNat (obs_len_lt _ _)] at rl
      have hk : 0 ≤ PrimTy.ival k := (PrimTy.ival_mem k).1
      have hkey : k.val = PrimTy.ival k := rfl
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
                  have hkey : k.val = PrimTy.ival k := rfl
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

/-- `a = true ? true : false` at `bool`, as `a`. -/
def kiteBool? {p : PrimTy} {s : Srt} (a b : LTm C (.val p)) (t e : LTm C s) : Option (LTm C s) :=
  match p, s, a, b, t, e with
  | .bool, .val .bool, a, b, t, e => if b.isTT && t.isTT && e.isFF then some a else none
  | _, _, _, _, _, _ => none

theorem kiteBool?_eval {p : PrimTy} {s : Srt} {a b : LTm C (.val p)} {t e : LTm C s}
    {r : LTm C s} (h : kiteBool? a b t e = some r) :
    r.eval g ν = (LTm.kite a b t e).eval g ν := by
  unfold kiteBool? at h
  split at h
  · rename_i a b t e
    split at h
    · rename_i hb
      cases h
      simp only [Bool.and_eq_true] at hb
      obtain ⟨⟨hb, ht⟩, he⟩ := hb
      rw [LTm.eval_kite, LTm.isTT_eval hb, LTm.isTT_eval ht, LTm.isFF_eval he]
      cases ha : (a.eval g ν : Option Bool) with
      | none => rfl
      | some x => cases x <;> rfl
    · cases h
  · cases h

/-- A conditional on keys, its keys compared. -/
def Facts.kiteN (F : Facts C) {p : PrimTy} {s : Srt} (a b : LTm C (.val p)) (t e : LTm C s) :
    LTm C s :=
  match F.keyCmp a b with
  | some true => t
  | some false => e
  | none =>
    if t.beqR e && F.returns a && F.returns b then t
    else match kiteBool? a b t e with
      | some r => r
      | none => .kite a b t e

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
    · split
      · rename_i r hr
        exact kiteBool?_eval hr
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

/-- A difference's operands. -/
def Op2.subArgs {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) : Option (EqF C) :=
  match o, x, y with
  | @Op2.binop _ .sub p _, x, y => some ⟨p, x, y⟩
  | _, _, _ => none

/-- The operands of a subtraction. -/
def LTm.subArgs? {s : Srt} (t : LTm C s) : Option (EqF C) :=
  match t with
  | .app2 o x y => Op2.subArgs o x y
  | _ => none

theorem LTm.subArgs?_eq {s : Srt} {t : LTm C s} {e : EqF C} (h : t.subArgs? = some e) :
    ∃ hp : BinOp.sub.accepts e.p = true,
      (⟨s, t⟩ : (s : Srt) × LTm C s) = ⟨.val e.p, .app2 (.binop .sub hp) e.l e.r⟩ := by
  cases t with
  | app2 o x y =>
    cases o with
    | @binop op p hp =>
      cases op <;> simp only [LTm.subArgs?, Op2.subArgs, reduceCtorEq, Option.some.injEq] at h
      subst h
      exact ⟨hp, rfl⟩
    | _ => simp only [LTm.subArgs?, Op2.subArgs, reduceCtorEq] at h
  | _ => simp only [LTm.subArgs?, reduceCtorEq] at h

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

/-- The operands of a product. -/
def Op2.mulArgs {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) : Option (EqF C) :=
  match o, x, y with
  | @Op2.binop _ .mul p _, x, y => some ⟨p, x, y⟩
  | _, _, _ => none

/-- The operands of a product. -/
def LTm.mulArgs? {s : Srt} (t : LTm C s) : Option (EqF C) :=
  match t with
  | .app2 o x y => Op2.mulArgs o x y
  | _ => none

theorem LTm.mulArgs?_eq {s : Srt} {t : LTm C s} {e : EqF C} (h : t.mulArgs? = some e) :
    ∃ hp : BinOp.mul.accepts e.p = true,
      (⟨s, t⟩ : (s : Srt) × LTm C s) = ⟨.val e.p, .app2 (.binop .mul hp) e.l e.r⟩ := by
  cases t with
  | app2 o x y =>
    cases o with
    | @binop op p hp =>
      cases op <;> simp only [LTm.mulArgs?, Op2.mulArgs, reduceCtorEq, Option.some.injEq] at h
      subst h
      exact ⟨hp, rfl⟩
    | _ => simp only [LTm.mulArgs?, Op2.mulArgs, reduceCtorEq] at h
  | _ => simp only [LTm.mulArgs?, reduceCtorEq] at h

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
    simp only [PrimTy.ofInt?, PrimTy.ival]
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
        have h1 : binopT .add _ va (r.eval g ν) = some vx := hvx
        unfold binopT at h1
        simp only [BinOp.shortT] at h1
        cases hr : (r.eval g ν : Option q.Denote) with
        | none => rw [hr] at h1; cases h1
        | some vb =>
          rw [hr, Option.bind_some] at h1
          have hsum := evalT_add h1
          rw [LTm.eval_app2, LTm.eval_app2, hl, hr]
          show some va = (binopT .add _ va (some vb)).bind fun z => binopT .sub _ z (some vb)
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

/-- `(a - b) + b`, cancelled to `a` where the difference returns. -/
def Facts.cancelAdd (F : Facts C) {p : PrimTy} (x y : LTm C (.val p)) : Option (LTm C (.val p)) :=
  match x.subArgs? with
  | some e => if e.r.beqR y && F.returns x then e.l.castTo? else none
  | none => none

theorem Facts.cancelAdd_eval {F : Facts C} (hF : F.Ok g ν) {p : PrimTy}
    (hs : BinOp.add.accepts p = true) {x y a : LTm C (.val p)} (h : F.cancelAdd x y = some a) :
    (a.eval g ν : Option p.Denote) = (LTm.app2 (.binop .add hs) x y).eval g ν := by
  unfold Facts.cancelAdd at h
  split at h
  · rename_i e he
    split at h
    · rename_i hb
      simp only [Bool.and_eq_true] at hb
      obtain ⟨hp, hx⟩ := LTm.subArgs?_eq he
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
        have h1 : binopT .sub _ va (r.eval g ν) = some vx := hvx
        unfold binopT at h1
        simp only [BinOp.shortT] at h1
        cases hr : (r.eval g ν : Option q.Denote) with
        | none => rw [hr] at h1; cases h1
        | some vb =>
          rw [hr, Option.bind_some] at h1
          have hdiff := evalT_sub h1
          rw [LTm.eval_app2, LTm.eval_app2, hl, hr]
          show some va = (binopT .sub _ va (some vb)).bind fun z => binopT .add _ z (some vb)
          unfold binopT
          simp only [BinOp.shortT, Option.bind_some]
          rw [h1, Option.bind_some]
          have hd : PrimTy.ival vx + PrimTy.ival vb = PrimTy.ival va := by omega
          cases q with
          | bool => cases hnum
          | uint =>
            show some va = PrimTy.uint.ofInt? (PrimTy.ival vx + PrimTy.ival vb)
            rw [hd]; exact (ofInt?_ival_self rfl va).symm
          | int =>
            show some va = PrimTy.int.ofInt? (PrimTy.ival vx + PrimTy.ival vb)
            rw [hd]; exact (ofInt?_ival_self rfl va).symm
    · cases h
  · cases h

/-- `(a * k + c) / k`, cancelled to `a` at `uint` where the sum returns,
`k` and `c` literals with `c < k` (Lean only): an external function value,
packed as `address * 2^32 + selector`, read back to its address
(`docs/semantic-gaps.md`, "Function types"). -/
def Facts.cancelDiv (F : Facts C) {p : PrimTy} (x y : LTm C (.val p)) : Option (LTm C (.val p)) :=
  match x.addArgs?, y.litV? with
  | some e, some k =>
    match e.l.mulArgs?, e.r.litV? with
    | some m, some c =>
      match m.r.litV? with
      | some k' =>
        if p == .uint && PrimTy.ival k' == PrimTy.ival k && decide (0 ≤ PrimTy.ival c) &&
            decide (PrimTy.ival c < PrimTy.ival k) && F.returns x then m.l.castTo? else none
      | none => none
    | _, _ => none
  | _, _ => none

theorem Facts.cancelDiv_eval {F : Facts C} (hF : F.Ok g ν) {p : PrimTy}
    (hs : BinOp.div.accepts p = true) {x y a : LTm C (.val p)} (h : F.cancelDiv x y = some a) :
    (a.eval g ν : Option p.Denote) = (LTm.app2 (.binop .div hs) x y).eval g ν := by
  unfold Facts.cancelDiv at h
  split at h
  · rename_i e k he hk
    split at h
    · rename_i m c hm hc
      split at h
      · rename_i k' hk'
        split at h
        · rename_i hb
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
          obtain ⟨⟨⟨⟨hpu, hkk⟩, hc0⟩, hck⟩, hret⟩ := hb
          subst hpu
          obtain ⟨hp, hx⟩ := LTm.addArgs?_eq he
          obtain ⟨q, l, r⟩ := e
          cases hx
          obtain ⟨hpm, hl⟩ := LTm.mulArgs?_eq hm
          obtain ⟨q2, ml, mr⟩ := m
          cases hl
          cases LTm.castTo?_eq h
          obtain rfl := LTm.eq_of_litV? hk
          dsimp only at hk' hc hret ⊢
          have hr := LTm.eq_of_litV? hc
          have hmr := LTm.eq_of_litV? hk'
          rw [hr, hmr] at hret ⊢
          obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF _ hret)
          cases hl : (ml.eval g ν : Option PrimTy.uint.Denote) with
          | none =>
            rw [LTm.eval_app2, LTm.eval_app2, hl, Op2.eval_none_left, Op2.eval_none_left] at hvx
            cases hvx
          | some va =>
            have e1 : (LTm.app2 (Op2.binop BinOp.mul hpm) ml (LTm.lit k')).eval g ν =
                BinOp.evalT .mul hpm va k' := by
              rw [LTm.eval_app2, hl, Op2.eval_eq_evalM]; rfl
            cases hm' : (BinOp.evalT .mul hpm va k' : Option PrimTy.uint.Denote) with
            | none =>
              rw [LTm.eval_app2, e1.trans hm', Op2.eval_none_left] at hvx; cases hvx
            | some vm =>
              have e2 : (LTm.app2 (Op2.binop BinOp.add hp)
                  (LTm.app2 (Op2.binop BinOp.mul hpm) ml (LTm.lit k')) (LTm.lit c)).eval g ν =
                  BinOp.evalT .add hp vm c := by
                rw [LTm.eval_app2, e1, hm', Op2.eval_eq_evalM]; rfl
              rw [e2] at hvx
              have hmul := evalT_mul hm'
              have hadd := evalT_add hvx
              rw [LTm.eval_app2, e2, hvx, Op2.eval_eq_evalM]
              show some va = BinOp.evalT .div hs vx k
              have hva : 0 ≤ PrimTy.ival va := by
                have h2 := va.2
                simp only [PrimTy.inRange, decide_eq_true_eq] at h2
                exact h2.1
              have hk0 : PrimTy.ival k ≠ 0 := by omega
              have hq : Int.tdiv (PrimTy.ival vx) (PrimTy.ival k) = PrimTy.ival va := by
                rw [hadd, hmul, hkk, Int.tdiv_eq_ediv_of_nonneg (by
                  have : 0 ≤ PrimTy.ival va * PrimTy.ival k := Int.mul_nonneg hva (by omega)
                  omega), Int.add_comm, Int.add_mul_ediv_right _ _ hk0,
                  Int.ediv_eq_zero_of_lt hc0 hck, Int.zero_add]
              simp only [BinOp.evalT, BinOp.evalNum, BinOp.arithInt]
              show some va = (if PrimTy.ival k = 0 then none
                else some (Int.tdiv (PrimTy.ival vx) (PrimTy.ival k))).bind PrimTy.uint.ofInt?
              rw [if_neg hk0, hq, Option.bind_some]
              exact (ofInt?_ival_self rfl va).symm
        · cases h
      · cases h
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

/-- `x < x + c`, `c` a positive literal, where the sum returns. -/
def Facts.ltSucc (F : Facts C) {p : PrimTy} (x y : LTm C (.val p)) : Bool :=
  match y.addArgs? with
  | some e => e.l.beqR x && ((e.r.litV?).map fun v => decide (0 < PrimTy.ival v)).getD false &&
      F.returns y
  | none => false

theorem Facts.ltSucc_sound {F : Facts C} (hF : F.Ok g ν) {p : PrimTy} {x y : LTm C (.val p)}
    (h : F.ltSucc x y = true) : ∃ u w, (x.eval g ν : Option p.Denote) = some u ∧
      (y.eval g ν : Option p.Denote) = some w ∧ PrimTy.ival u < PrimTy.ival w := by
  unfold Facts.ltSucc at h
  split at h
  · rename_i e he
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hl, hc⟩, hr⟩ := h
    obtain ⟨vy, hvy⟩ := Option.isSome_iff_exists.1 (F.returns_sound hF _ hr)
    obtain ⟨hp, hy⟩ := LTm.addArgs?_eq he
    obtain ⟨q, l, r⟩ := e
    cases hy
    cases LTm.sigma_eq_of_beqR hl
    cases hlv : r.litV? with
    | none => rw [hlv] at hc; cases hc
    | some c =>
      rw [hlv] at hc
      simp only [Option.map_some, Option.getD_some, decide_eq_true_eq] at hc
      obtain rfl := LTm.eq_of_litV? hlv
      rw [LTm.eval_app2] at hvy
      cases hxv : (l.eval g ν : Option q.Denote) with
      | none => rw [hxv] at hvy; cases hvy
      | some vx =>
        rw [hxv] at hvy
        have h1 : binopT .add _ vx (some c) = some vy := hvy
        unfold binopT at h1
        simp only [BinOp.shortT, Option.bind_some] at h1
        have hs := evalT_add h1
        refine ⟨vx, vy, rfl, ?_, by omega⟩
        rw [LTm.eval_app2, hxv]
        exact hvy
  · cases h

/-- A comparison folded by its operands' ranges, where both return. -/
def Facts.cmpFold (F : Facts C) {p : PrimTy} (dec : Int × Int → Int × Int → Option Bool)
    (x y : LTm C (.val p)) : Option Bool :=
  if F.returns x && F.returns y then dec (F.range x) (F.range y) else none

/-- The literal `2`. -/
def isTwo {p : PrimTy} (x : LTm C (.val p)) : Bool :=
  match x.litV? with
  | some v => PrimTy.ival v == 2
  | none => false

/-- `2 * y` is `y + y`: both check the one integer `2·y` against the
range. -/
theorem evalT_two_mul {p : PrimTy} {x : LTm C (.val p)} (hx : isTwo x = true)
    (hm : BinOp.mul.accepts p = true) (y : LTm C (.val p)) :
    (LTm.app2 (.binop .add hm) y y).eval g ν = (LTm.app2 (.binop .mul hm) x y).eval g ν := by
  unfold isTwo at hx
  split at hx
  · rename_i v hv
    obtain rfl := LTm.eq_of_litV? hv
    rw [LTm.eval_app2, LTm.eval_app2]
    have hl : ((LTm.lit v : LTm C (.val p)).eval g ν : Option p.Denote) = some v := rfl
    rw [hl, Op2.eval_eq_evalM, Op2.eval_eq_evalM]
    simp only [Op2.evalM, Option.bind_some]
    cases hy : (y.eval g ν : Option p.Denote) with
    | none =>
      unfold binopT
      cases p <;> simp only [BinOp.shortT, Option.bind_none] <;> rfl
    | some w =>
      simp only [Option.bind_some]
      unfold binopT
      cases p with
      | bool => cases hm
      | uint | int =>
        have h2 : v.1 = 2 := by simpa only [PrimTy.ival, beq_iff_eq] using hx
        simp only [BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, h2]
        rw [show w.1 + w.1 = 2 * w.1 by omega]
  · cases hx

/-! ### Bytes reassembled (Lean only)

An ABI encoding writes a word byte by byte, `(x >> 8k) % 256`; reading
the bytes back by Horner's rule, `r * 256 + b`, reassembles the word:
`hornerU?` reads `((q >> k) % 2^w) * 2^k + q % 2^k` as `q % 2^(w+k)`,
`shrZeroU?` reads `x >> 0` as `x`, and `modModU?` reads `(t % m) % n` as
`t % n` where `n` divides `m` (a `uint8(…)` of a byte).  No solkey taclet
reads bytes (KeY has no byte layout). -/

theorem Int.emod_mul_split (x a b : Int) (ha : 0 < a) :
    x % (a * b) = x % a + a * (x / a % b) := by
  have h1 := Int.mul_ediv_add_emod x a
  have h2 := Int.mul_ediv_add_emod (x / a) b
  have h3 : x / (a * b) = x / a / b := (Int.ediv_ediv (by omega)).symm
  have h4 := Int.mul_ediv_add_emod x (a * b)
  rw [h3] at h4
  grind

theorem emod_pow_ediv (a : Int) (m k w : Nat) (hm : k + w ≤ m) :
    a % 2 ^ m / 2 ^ k % 2 ^ w = a / 2 ^ k % 2 ^ w := by
  have h2k : (2 : Int) ^ k ≠ 0 := Int.ne_of_gt (Int.pow_pos (by decide))
  have hsplit : (2 : Int) ^ m = 2 ^ k * (2 ^ w * 2 ^ (m - k - w)) := by
    rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
  have ha := Int.emod_add_mul_ediv a (2 ^ m)
  conv => rhs; rw [← ha]
  rw [hsplit, Int.mul_assoc, Int.add_mul_ediv_left _ _ h2k, Int.mul_assoc, Int.add_mul_emod_self_left]

/-- The operands of `op` at `uint`. -/
def Op2.uArgs (op : BinOp) {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    Option (LTm C (.val .uint) × LTm C (.val .uint)) :=
  match o, x, y with
  | @Op2.binop _ op' p _, x, y =>
    if op' == op then
      match p with
      | .uint => some (x, y)
      | _ => none
    else none
  | _, _, _ => none

/-- The operands of `t`, an `op` at `uint`. -/
def LTm.uArgs? (op : BinOp) {s : Srt} (t : LTm C s) :
    Option (LTm C (.val .uint) × LTm C (.val .uint)) :=
  match t with
  | .app2 o x y => Op2.uArgs op o x y
  | _ => none

theorem LTm.uArgs?_eq {op : BinOp} {s : Srt} {t : LTm C s} {l r : LTm C (.val .uint)}
    (h : t.uArgs? op = some (l, r)) :
    ∃ hp : op.accepts .uint = true,
      (⟨s, t⟩ : (s : Srt) × LTm C s) = ⟨.val (op.ret .uint), .app2 (.binop op hp) l r⟩ := by
  cases t with
  | app2 o x y =>
    cases o with
    | @binop op' p hp =>
      simp only [LTm.uArgs?, Op2.uArgs] at h
      split at h
      · rename_i he
        have := eq_of_beq he
        subst this
        cases p <;> simp only [reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hp, rfl⟩
      · cases h
    | _ => simp only [LTm.uArgs?, Op2.uArgs, reduceCtorEq] at h
  | _ => simp only [LTm.uArgs?, reduceCtorEq] at h

/-- A `uint` literal's integer. -/
def LTm.uLit? (t : LTm C (.val .uint)) : Option Int := t.litV?.map (·.1)

theorem LTm.eq_of_uLit? {t : LTm C (.val .uint)} {n : Int} (h : t.uLit? = some n) :
    ∃ v : PrimTy.uint.Denote, v.1 = n ∧ t = .lit v := by
  unfold LTm.uLit? at h
  cases hv : t.litV? with
  | none => rw [hv] at h; cases h
  | some v =>
    rw [hv] at h
    cases h
    exact ⟨v, rfl, LTm.eq_of_litV? hv⟩

/-- The exponent `k` of `n = pw * 2 ^ j` with `k = i + j`, searched from
`i` with `pw = 2 ^ i`, within `f` doublings (structural, for the kernel). -/
def log2Go (n : Int) : Nat → Nat → Int → Option Nat
  | 0, _, _ => none
  | f + 1, i, pw => if n = pw then some i else if n < pw then none else log2Go n f (i + 1) (pw * 2)

theorem log2Go_eq {n : Int} : ∀ {f i : Nat} {pw : Int} {k : Nat}, pw = 2 ^ i →
    log2Go n f i pw = some k → n = 2 ^ k
  | 0, _, _, _, _, h => by cases h
  | f + 1, i, pw, k, hpw, h => by
    unfold log2Go at h
    split at h
    · rename_i he; cases h; rw [he, hpw]
    · split at h
      · cases h
      · exact log2Go_eq (f := f) (i := i + 1) (by rw [hpw, Int.pow_succ]) h

/-- The exponent `k` with `2 ^ k = n`, for a power of two below `2 ^ 256`. -/
def log2Exact (n : Int) : Option Nat :=
  match log2Go n 257 0 1 with
  | some k => if k ≤ 256 then some k else none
  | none => none

theorem log2Exact_eq {n : Int} {k : Nat} (h : log2Exact n = some k) : n = 2 ^ k ∧ k ≤ 256 := by
  unfold log2Exact at h
  split at h
  · rename_i k' hk
    split at h
    · cases h; exact ⟨log2Go_eq (by rfl) hk, by assumption⟩
    · cases h
  · cases h

theorem eval_uop (op : BinOp) (hp : op.accepts .uint = true) (hs : ∀ a : PrimTy.uint.Denote, op.shortT a = none)
    (x y : LTm C (.val .uint)) :
    (LTm.app2 (.binop op hp) x y).eval g ν =
      (x.eval g ν).bind fun a => (y.eval g ν).bind fun b => BinOp.evalT op hp a b := by
  rw [LTm.eval_app2, Op2.eval_eq_evalM]
  cases x.eval g ν with
  | none => rfl
  | some a =>
    simp only [Op2.evalM, Option.bind_some]
    unfold binopT
    rw [hs a]

theorem uint_ofInt?_ival (v : PrimTy.uint.Denote) : PrimTy.uint.ofInt? v.1 = some v :=
  ofInt?_ival_self rfl v

theorem uint_nonneg (v : PrimTy.uint.Denote) : 0 ≤ v.1 := by
  have h := v.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  exact h.1

theorem uint_lt (v : PrimTy.uint.Denote) : v.1 < 2 ^ 256 := by
  have h := v.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  exact_mod_cast h.2

/-- `x >> 0` is `x`. -/
theorem eval_shr_zero (hp : BinOp.shr.accepts .uint = true) (x : LTm C (.val .uint))
    (c : PrimTy.uint.Denote) (hc : c.1 = 0) :
    ((LTm.app2 (.binop .shr hp) x (.lit c)).eval g ν : Option PrimTy.uint.Denote) = x.eval g ν := by
  rw [eval_uop .shr hp (fun _ => rfl)]
  cases x.eval g ν with
  | none => rfl
  | some a =>
    show (BinOp.arithInt .shr a.1 c.1).bind PrimTy.uint.ofInt? = some a
    simp only [BinOp.arithInt, hc, Int.toNat_zero, Int.pow_zero, Int.ediv_one]
    simp only [show (0 : Int) < 256 from by decide, if_true, Option.bind_some]
    exact uint_ofInt?_ival a

/-- `(t % m) % n` is `t % n` where `n` divides `m`. -/
theorem eval_mod_mod (hp : BinOp.mod.accepts .uint = true) (hp' : BinOp.mod.accepts .uint = true)
    (t : LTm C (.val .uint)) (m n : PrimTy.uint.Denote) (hn : 0 < n.1) (hm : 0 < m.1)
    (hd : m.1 % n.1 = 0) :
    ((LTm.app2 (.binop .mod hp') (LTm.app2 (.binop .mod hp) t (.lit m)) (.lit n)).eval g ν :
      Option PrimTy.uint.Denote) = (LTm.app2 (.binop .mod hp) t (.lit n)).eval g ν := by
  rw [eval_uop .mod hp' (fun _ => rfl), eval_uop .mod hp (fun _ => rfl),
    eval_uop .mod hp (fun _ => rfl)]
  cases ht : t.eval g ν with
  | none => rfl
  | some a =>
    have ha := uint_nonneg a
    show ((BinOp.arithInt .mod a.1 m.1).bind PrimTy.uint.ofInt?).bind
        (fun b => (BinOp.arithInt .mod b.1 n.1).bind PrimTy.uint.ofInt?) =
      (BinOp.arithInt .mod a.1 n.1).bind PrimTy.uint.ofInt?
    simp only [BinOp.arithInt, if_neg (Int.ne_of_gt hm), if_neg (Int.ne_of_gt hn), Option.bind_some]
    cases hw : PrimTy.uint.ofInt? (Int.tmod a.1 m.1) with
    | none =>
      exfalso
      rw [Int.tmod_eq_emod_of_nonneg ha] at hw
      have h1 := Int.emod_nonneg a.1 (Int.ne_of_gt hm)
      have h2 := Int.emod_lt_of_pos a.1 hm
      have h3 := uint_lt m
      simp only [PrimTy.ofInt?, PrimTy.inRange] at hw
      split at hw
      · cases hw
      · rename_i hh; apply hh; simp only [decide_eq_true_eq]; constructor <;> omega
    | some w =>
      simp only [Option.bind_some]
      have hw1 := ofInt?_ival hw
      simp only [PrimTy.ival] at hw1
      congr 1
      rw [hw1, Int.tmod_eq_emod_of_nonneg ha, Int.tmod_eq_emod_of_nonneg (Int.emod_nonneg _ (Int.ne_of_gt hm)),
        Int.tmod_eq_emod_of_nonneg ha]
      exact Int.emod_emod_of_dvd _ (Int.dvd_of_emod_eq_zero hd)

theorem uint_ofInt?_some {n : Int} (h0 : 0 ≤ n) (h1 : n < 2 ^ 256) :
    ∃ v : PrimTy.uint.Denote, PrimTy.uint.ofInt? n = some v ∧ v.1 = n := by
  have hr : PrimTy.uint.inRange n = true := by
    simp only [PrimTy.inRange, decide_eq_true_eq]; exact ⟨h0, by exact_mod_cast h1⟩
  refine ⟨⟨n, hr⟩, ?_, rfl⟩
  simp only [PrimTy.ofInt?, dif_pos hr]

/-- **Horner's step on bytes**: `((q >> k) % 2^w) * 2^k + q % 2^k` is
`q % 2^(w+k)`, `S` a term reading `q >> k` modulo `2^w` (`hS`). -/
theorem eval_horner (hm : BinOp.mod.accepts .uint = true) (hm' : BinOp.mod.accepts .uint = true)
    (hmul : BinOp.mul.accepts .uint = true) (ha : BinOp.add.accepts .uint = true)
    (S s : LTm C (.val .uint)) (W K K' L : PrimTy.uint.Denote) (w k : Nat)
    (hW : W.1 = 2 ^ w) (hK : K.1 = 2 ^ k) (hK' : K'.1 = 2 ^ k) (hL : L.1 = 2 ^ (w + k))
    (hwk : w + k < 256)
    (hS : (S.eval g ν).map (fun v => v.1 % 2 ^ w) = (s.eval g ν).map (fun q => q.1 / 2 ^ k % 2 ^ w)) :
    ((LTm.app2 (.binop .add ha) (LTm.app2 (.binop .mul hmul) (LTm.app2 (.binop .mod hm) S (.lit W))
        (.lit K)) (LTm.app2 (.binop .mod hm') s (.lit K'))).eval g ν : Option PrimTy.uint.Denote) =
      (LTm.app2 (.binop .mod hm') s (.lit L)).eval g ν := by
  rw [eval_uop .add ha (fun _ => rfl), eval_uop .mul hmul (fun _ => rfl),
    eval_uop .mod hm (fun _ => rfl), eval_uop .mod hm' (fun _ => rfl),
    eval_uop .mod hm' (fun _ => rfl)]
  have h2k : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  have h2w : (0 : Int) < 2 ^ w := Int.pow_pos (by decide)
  have hwk' : (2 : Int) ^ (w + k) = 2 ^ k * 2 ^ w := by rw [Int.pow_add, Int.mul_comm]
  have hbig : (2 : Int) ^ k * 2 ^ w < 2 ^ 256 := by
    rw [← hwk']
    have : (2 : Nat) ^ (w + k) < 2 ^ 256 := Nat.pow_lt_pow_right (by decide) hwk
    exact_mod_cast this
  have hw1 : (1 : Int) ≤ 2 ^ w := h2w
  have e7 : (2 : Int) ^ k ≤ 2 ^ k * 2 ^ w := by
    have := Int.mul_le_mul_of_nonneg_left hw1 (Int.le_of_lt h2k)
    rwa [Int.mul_one] at this
  have e8 : (2 : Int) ^ w ≤ 2 ^ k * 2 ^ w := by
    have := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ 2 ^ k from h2k) (Int.le_of_lt h2w)
    rwa [Int.one_mul] at this
  cases hs : s.eval g ν with
  | none =>
    rw [hs, Option.map_none] at hS
    cases hS' : S.eval g ν with
    | none => rfl
    | some v => rw [hS', Option.map_some] at hS; cases hS
  | some q =>
    rw [hs, Option.map_some] at hS
    cases hS' : S.eval g ν with
    | none => rw [hS', Option.map_none] at hS; cases hS
    | some v =>
      rw [hS', Option.map_some, Option.some.injEq] at hS
      have hq := uint_nonneg q
      have hv := uint_nonneg v
      simp only [Option.bind_some]
      show (((BinOp.arithInt .mod v.1 W.1).bind PrimTy.uint.ofInt?).bind fun a =>
          (BinOp.arithInt .mul a.1 K.1).bind PrimTy.uint.ofInt?).bind (fun a =>
          ((BinOp.arithInt .mod q.1 K'.1).bind PrimTy.uint.ofInt?).bind fun b =>
            (BinOp.arithInt .add a.1 b.1).bind PrimTy.uint.ofInt?) =
        (BinOp.arithInt .mod q.1 L.1).bind PrimTy.uint.ofInt?
      simp only [BinOp.arithInt, hW, hK, hK', hL, if_neg (Int.ne_of_gt h2w), if_neg (Int.ne_of_gt h2k),
        if_neg (Int.ne_of_gt (Int.pow_pos (by decide) : (0 : Int) < 2 ^ (w + k))), Option.bind_some]
      rw [Int.tmod_eq_emod_of_nonneg hv, Int.tmod_eq_emod_of_nonneg hq, Int.tmod_eq_emod_of_nonneg hq]
      have e1 := Int.emod_nonneg v.1 (Int.ne_of_gt h2w)
      have e2 := Int.emod_lt_of_pos v.1 h2w
      obtain ⟨a1, ha1, ha1v⟩ := uint_ofInt?_some (n := v.1 % 2 ^ w) e1 (by omega)
      rw [ha1, Option.bind_some, ha1v]
      have e3 : v.1 % 2 ^ w * 2 ^ k < 2 ^ k * 2 ^ w := by
        rw [Int.mul_comm]; exact Int.mul_lt_mul_of_pos_left e2 h2k
      have e4 : 0 ≤ v.1 % 2 ^ w * 2 ^ k := Int.mul_nonneg e1 (Int.le_of_lt h2k)
      obtain ⟨a2, ha2, ha2v⟩ := uint_ofInt?_some (n := v.1 % 2 ^ w * 2 ^ k) e4 (by omega)
      rw [ha2, Option.bind_some]
      have e5 := Int.emod_nonneg q.1 (Int.ne_of_gt h2k)
      have e6 := Int.emod_lt_of_pos q.1 h2k
      obtain ⟨a3, ha3, ha3v⟩ := uint_ofInt?_some (n := q.1 % 2 ^ k) e5 (by omega)
      rw [ha3, Option.bind_some, ha2v, ha3v]
      congr 1
      rw [hwk', Int.emod_mul_split q.1 _ _ h2k, ← hS]
      rw [Int.mul_comm (v.1 % 2 ^ w), Int.add_comm]

/-- `x >> c` at `uint`, `c` a literal below 256: `x` divided by `2^c`. -/
theorem eval_shr_lit (hp : BinOp.shr.accepts .uint = true) (x : LTm C (.val .uint))
    (c : PrimTy.uint.Denote) (hc : c.1 < 256) :
    ((LTm.app2 (.binop .shr hp) x (.lit c)).eval g ν : Option PrimTy.uint.Denote).map (·.1) =
      (x.eval g ν).map (fun a => a.1 / 2 ^ c.1.toNat) := by
  rw [eval_uop .shr hp (fun _ => rfl)]
  cases x.eval g ν with
  | none => rfl
  | some a =>
    show ((BinOp.arithInt .shr a.1 c.1).bind PrimTy.uint.ofInt?).map (·.1) = some (a.1 / 2 ^ c.1.toNat)
    simp only [BinOp.arithInt, if_pos hc, Option.bind_some]
    have ha := uint_nonneg a
    have h2 : (0 : Int) < 2 ^ c.1.toNat := Int.pow_pos (by decide)
    have h1 : a.1 / 2 ^ c.1.toNat ≤ a.1 := Int.ediv_le_self _ ha
    obtain ⟨v, hv, hvv⟩ := uint_ofInt?_some (n := a.1 / 2 ^ c.1.toNat)
      (Int.ediv_nonneg ha (Int.le_of_lt h2)) (by have := uint_lt a; omega)
    rw [hv, Option.map_some, hvv]

/-- `S` reads `s >> k`: `S` is `s >> k`, or `t >> (j + k)` where `s` is `t >> j`. -/
def shrMatchAB (S s : LTm C (.val .uint)) (k : Nat) : Bool :=
  match S.uArgs? .shr with
  | some (u, jl) =>
    match jl.uLit? with
    | some J =>
      (u.beqR s && J == (k : Int)) ||
      (match s.uArgs? .shr with
        | some (t, jl') =>
          match jl'.uLit? with
          | some j => u.beqR t && J == j + k && decide (0 ≤ j) && decide (J < 256)
          | none => false
        | none => false)
    | none => false
  | none => false

theorem shrMatchAB_sound {S s : LTm C (.val .uint)} {k : Nat} (h : shrMatchAB S s k = true)
    (hk : k < 256) :
    (S.eval g ν).map (·.1) = (s.eval g ν).map (fun q => q.1 / 2 ^ k) := by
  unfold shrMatchAB at h
  split at h
  · rename_i u jl hS
    obtain ⟨hp, hSe⟩ := LTm.uArgs?_eq hS
    cases hSe
    split at h
    · rename_i J hJ
      obtain ⟨Jv, hJv, rfl⟩ := LTm.eq_of_uLit? hJ
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨hu, hk'⟩ | h
      · cases LTm.eq_of_beqR hu
        refine (eval_shr_lit hp _ Jv (by omega)).trans ?_
        simp only [hJv, hk', Int.toNat_natCast]
      · split at h
        · rename_i t jl' hs
          obtain ⟨hp', hse⟩ := LTm.uArgs?_eq hs
          cases hse
          split at h
          · rename_i j hj
            obtain ⟨jv, hjv, rfl⟩ := LTm.eq_of_uLit? hj
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
            obtain ⟨⟨⟨hu, hJ'⟩, hj0⟩, hJ256⟩ := h
            cases LTm.eq_of_beqR hu
            refine (eval_shr_lit hp _ Jv (by omega)).trans ?_
            rw [hJv]
            have hjl : jv.1 < 256 := by omega
            have e := eval_shr_lit (g := g) (ν := ν) hp' u jv hjl
            cases ht : u.eval g ν with
            | none =>
              rw [ht, Option.map_none] at e
              cases hs' : (LTm.app2 (.binop .shr hp') u (.lit jv)).eval g ν with
              | none => rfl
              | some _ => rw [hs', Option.map_some] at e; cases e
            | some a =>
              rw [ht, Option.map_some] at e
              cases hs' : ((LTm.app2 (.binop .shr hp') u (.lit jv)).eval g ν : Option PrimTy.uint.Denote) with
              | none => rw [hs', Option.map_none] at e; cases e
              | some b =>
                rw [hs', Option.map_some, Option.some.injEq] at e
                simp only [Option.map_some, e, hJ']
                have h2j : (0 : Int) ≤ 2 ^ jv.1.toNat := Int.le_of_lt (Int.pow_pos (by decide))
                rw [Int.ediv_ediv h2j, ← Int.pow_add]
                congr 3
                omega
          · cases h
        · cases h
    · cases h
  · cases h

/-- `x % c` at `uint`, `c` a positive literal. -/
theorem eval_mod_lit (hp : BinOp.mod.accepts .uint = true) (x : LTm C (.val .uint))
    (c : PrimTy.uint.Denote) (hc : 0 < c.1) :
    ((LTm.app2 (.binop .mod hp) x (.lit c)).eval g ν : Option PrimTy.uint.Denote).map (·.1) =
      (x.eval g ν).map (fun a => a.1 % c.1) := by
  rw [eval_uop .mod hp (fun _ => rfl)]
  cases x.eval g ν with
  | none => rfl
  | some a =>
    show ((BinOp.arithInt .mod a.1 c.1).bind PrimTy.uint.ofInt?).map (·.1) = some (a.1 % c.1)
    have ha := uint_nonneg a
    simp only [BinOp.arithInt, if_neg (Int.ne_of_gt hc), Option.bind_some,
      Int.tmod_eq_emod_of_nonneg ha]
    obtain ⟨v, hv, hvv⟩ := uint_ofInt?_some (n := a.1 % c.1) (Int.emod_nonneg _ (Int.ne_of_gt hc))
      (by have := Int.emod_lt_of_pos a.1 hc; have := uint_lt c; omega)
    rw [hv, Option.map_some, hvv]

/-- `S` reads `s >> k` modulo `2^w`: by `shrMatchAB`, or `S` is
`(s % 2^m) >> k` with `k + w <= m` (a narrowed word). -/
def shrMatch (S s : LTm C (.val .uint)) (k w : Nat) : Bool :=
  shrMatchAB S s k ||
  (match S.uArgs? .shr with
    | some (u, jl) =>
      match jl.uLit?, u.uArgs? .mod with
      | some J, some (s', ml) =>
        match ml.uLit? with
        | some M =>
          match log2Exact M with
          | some m => s'.beqR s && J == (k : Int) && decide (k + w ≤ m)
          | none => false
        | none => false
      | _, _ => false
    | none => false)

theorem shrMatch_sound {S s : LTm C (.val .uint)} {k w : Nat} (h : shrMatch S s k w = true)
    (hk : k < 256) :
    (S.eval g ν).map (fun v => v.1 % 2 ^ w) = (s.eval g ν).map (fun q => q.1 / 2 ^ k % 2 ^ w) := by
  unfold shrMatch at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · have e := congrArg (Option.map (· % (2 : Int) ^ w)) (shrMatchAB_sound (g := g) (ν := ν) h hk)
    simp only [Option.map_map] at e
    exact e
  · split at h
    · rename_i u jl hS
      obtain ⟨hp, hSe⟩ := LTm.uArgs?_eq hS
      cases hSe
      split at h
      · rename_i J s' ml hJ hu
        obtain ⟨Jv, hJv, rfl⟩ := LTm.eq_of_uLit? hJ
        obtain ⟨hm, hue⟩ := LTm.uArgs?_eq hu
        cases hue
        split at h
        · rename_i M hM
          obtain ⟨Mv, hMv, rfl⟩ := LTm.eq_of_uLit? hM
          split at h
          · rename_i m hm'
            obtain ⟨hm1, -⟩ := log2Exact_eq hm'
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
            obtain ⟨⟨hb, hJk⟩, hkw⟩ := h
            cases LTm.eq_of_beqR hb
            have e1 := eval_shr_lit (g := g) (ν := ν) hp (LTm.app2 (.binop .mod hm) s (.lit Mv)) Jv
              (by omega)
            have hM0 : 0 < Mv.1 := by rw [hMv, hm1]; exact Int.pow_pos (by decide)
            have e2 := eval_mod_lit (g := g) (ν := ν) hm s Mv hM0
            have e1' := congrArg (Option.map (· % (2 : Int) ^ w)) e1
            simp only [Option.map_map] at e1'
            refine e1'.trans ?_
            cases hs : s.eval g ν with
            | none =>
              rw [hs, Option.map_none] at e2
              cases hu' : ((LTm.app2 (.binop .mod hm) s (.lit Mv)).eval g ν : Option PrimTy.uint.Denote) with
              | none => rfl
              | some _ => rw [hu', Option.map_some] at e2; cases e2
            | some a =>
              rw [hs, Option.map_some] at e2
              cases hu' : ((LTm.app2 (.binop .mod hm) s (.lit Mv)).eval g ν : Option PrimTy.uint.Denote) with
              | none => rw [hu', Option.map_none] at e2; cases e2
              | some b =>
                rw [hu', Option.map_some, Option.some.injEq] at e2
                simp only [Option.map_some, Function.comp, e2, hJv, hJk, Int.toNat_natCast, hMv, hm1]
                exact congrArg some (emod_pow_ediv a.1 m k w hkw)
          · cases h
        · cases h
      · cases h
    · cases h

/-- `x >> 0` read as `x`, at `uint` (Lean only). -/
def shrZeroU? (x y : LTm C (.val .uint)) : Option (LTm C (.val .uint)) :=
  match y.uLit? with
  | some n => if n == 0 then some x else none
  | none => none

theorem shrZeroU?_eval (hp : BinOp.shr.accepts .uint = true) {x y a : LTm C (.val .uint)}
    (h : shrZeroU? x y = some a) :
    (a.eval g ν : Option PrimTy.uint.Denote) = (LTm.app2 (.binop .shr hp) x y).eval g ν := by
  unfold shrZeroU? at h
  split at h
  · rename_i n hn
    obtain ⟨v, hv, rfl⟩ := LTm.eq_of_uLit? hn
    split at h
    · rename_i h0
      cases h
      exact (eval_shr_zero hp x v (hv.trans (eq_of_beq h0))).symm
    · cases h
  · cases h

/-- `(t % m) % n` read as `t % n` where `n` divides `m`, at `uint` (Lean only). -/
def modModU? (x y : LTm C (.val .uint)) : Option (LTm C (.val .uint)) :=
  match x.uArgs? .mod, y.uLit? with
  | some (t, ml), some n =>
    match ml.uLit? with
    | some m => if decide (0 < n) && decide (0 < m) && m % n == 0 then
        some (.app2 (.binop .mod rfl) t y) else none
    | none => none
  | _, _ => none

theorem modModU?_eval (hp : BinOp.mod.accepts .uint = true) {x y a : LTm C (.val .uint)}
    (h : modModU? x y = some a) :
    (a.eval g ν : Option PrimTy.uint.Denote) = (LTm.app2 (.binop .mod hp) x y).eval g ν := by
  unfold modModU? at h
  split at h
  · rename_i t ml n hx hn
    obtain ⟨hp', hxe⟩ := LTm.uArgs?_eq hx
    cases hxe
    obtain ⟨nv, hnv, rfl⟩ := LTm.eq_of_uLit? hn
    split at h
    · rename_i m hm
      obtain ⟨mv, hmv, rfl⟩ := LTm.eq_of_uLit? hm
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
        obtain ⟨⟨hn0, hm0⟩, hd⟩ := hc
        exact (eval_mod_mod hp' hp t mv nv (by omega) (by omega) (by rw [hmv, hnv]; exact hd)).symm
      · cases h
    · cases h
  · cases h

/-- **Horner's step on bytes** (Lean only): `((q >> k) % 2^w) * 2^k + q % 2^k`
read as `q % 2^(w+k)`, at `uint`, `w + k < 256`. -/
def hornerU? (x y : LTm C (.val .uint)) : Option (LTm C (.val .uint)) :=
  match x.uArgs? .mul, y.uArgs? .mod with
  | some (xm, kl), some (s, kl') =>
    match xm.uArgs? .mod with
    | some (S, wl) =>
      match kl.uLit?, kl'.uLit?, wl.uLit? with
      | some K, some K', some W =>
        match log2Exact K, log2Exact W with
        | some k, some w =>
          if K' == K && decide (w + k < 256) && shrMatch S s k w then
            match PrimTy.uint.ofInt? (W * K) with
            | some L =>
              match modModU? s (.lit L) with
              | some t => some t
              | none => some (.app2 (.binop .mod rfl) s (.lit L))
            | none => none
          else none
        | _, _ => none
      | _, _, _ => none
    | none => none
  | _, _ => none

theorem hornerU?_eval (ha : BinOp.add.accepts .uint = true) {x y a : LTm C (.val .uint)}
    (h : hornerU? x y = some a) :
    (a.eval g ν : Option PrimTy.uint.Denote) = (LTm.app2 (.binop .add ha) x y).eval g ν := by
  unfold hornerU? at h
  split at h
  · rename_i xm kl s kl' hx hy
    obtain ⟨hmul, hxe⟩ := LTm.uArgs?_eq hx
    cases hxe
    obtain ⟨hm', hye⟩ := LTm.uArgs?_eq hy
    cases hye
    split at h
    · rename_i S wl hxm
      obtain ⟨hm, hxme⟩ := LTm.uArgs?_eq hxm
      cases hxme
      split at h
      · rename_i K K' W hK hK' hW
        obtain ⟨Kv, hKv, rfl⟩ := LTm.eq_of_uLit? hK
        obtain ⟨K'v, hK'v, rfl⟩ := LTm.eq_of_uLit? hK'
        obtain ⟨Wv, hWv, rfl⟩ := LTm.eq_of_uLit? hW
        split at h
        · rename_i k w hk hw
          obtain ⟨hk1, -⟩ := log2Exact_eq hk
          obtain ⟨hw1, -⟩ := log2Exact_eq hw
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
            obtain ⟨⟨hKK, hwk⟩, hsm⟩ := hc
            split at h
            · rename_i L hL
              have hLv := ofInt?_ival hL
              simp only [PrimTy.ival] at hLv
              have e := (eval_horner (g := g) (ν := ν) hm hm' hmul ha S s Wv Kv K'v L w k
                (by rw [hWv, hw1]) (by rw [hKv, hk1]) (by rw [hK'v, hKK, hk1])
                (by rw [hLv, hw1, hk1, Int.pow_add]) hwk (shrMatch_sound hsm (by omega))).symm
              split at h
              · rename_i t ht
                cases h
                exact (modModU?_eval hm' ht).trans e
              · cases h
                exact e
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem uint_opt_ext {a b : Option PrimTy.uint.Denote}
    (h : a.map (·.1) = b.map (·.1)) : a = b := by
  cases a <;> cases b <;> simp only [Option.map_none, Option.map_some, reduceCtorEq,
    Option.some.injEq] at h ⊢
  exact Subtype.ext h

/-- `((t % 2^m) >> j) % 2^w` read as `(t >> j) % 2^w` where `j + w <= m`, at
`uint` (Lean only): a byte of a narrowed word. -/
def modShrModU? (x y : LTm C (.val .uint)) : Option (LTm C (.val .uint)) :=
  match x.uArgs? .shr, y.uLit? with
  | some (u, jl), some W =>
    match u.uArgs? .mod, jl.uLit? with
    | some (t, ml), some j =>
      match ml.uLit? with
      | some M =>
        match log2Exact M, log2Exact W with
        | some m, some w =>
          if decide (0 ≤ j) && decide (j < 256) && decide (j + w ≤ m) then
            some (.app2 (.binop .mod rfl) (.app2 (.binop .shr rfl) t jl) y)
          else none
        | _, _ => none
      | none => none
    | _, _ => none
  | _, _ => none

theorem modShrModU?_eval (hp : BinOp.mod.accepts .uint = true) {x y a : LTm C (.val .uint)}
    (h : modShrModU? x y = some a) :
    (a.eval g ν : Option PrimTy.uint.Denote) = (LTm.app2 (.binop .mod hp) x y).eval g ν := by
  unfold modShrModU? at h
  split at h
  · rename_i u jl W hx hW
    obtain ⟨hs, hxe⟩ := LTm.uArgs?_eq hx
    cases hxe
    obtain ⟨Wv, hWv, rfl⟩ := LTm.eq_of_uLit? hW
    split at h
    · rename_i t ml j hu hj
      obtain ⟨hm, hue⟩ := LTm.uArgs?_eq hu
      cases hue
      obtain ⟨jv, hjv, rfl⟩ := LTm.eq_of_uLit? hj
      split at h
      · rename_i M hM
        obtain ⟨Mv, hMv, rfl⟩ := LTm.eq_of_uLit? hM
        split at h
        · rename_i m w hm' hw'
          obtain ⟨hm1, -⟩ := log2Exact_eq hm'
          obtain ⟨hw1, -⟩ := log2Exact_eq hw'
          split at h
          · rename_i hc
            cases h
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            obtain ⟨⟨hj0, hj256'⟩, hjw⟩ := hc
            have hW0 : 0 < Wv.1 := by rw [hWv, hw1]; exact Int.pow_pos (by decide)
            have hM0 : 0 < Mv.1 := by rw [hMv, hm1]; exact Int.pow_pos (by decide)
            have hj256 : jv.1 < 256 := by omega
            apply uint_opt_ext
            refine (eval_mod_lit rfl _ Wv hW0).trans (Eq.trans ?_ (eval_mod_lit hp _ Wv hW0).symm)
            have e1 := eval_shr_lit (g := g) (ν := ν) (rfl : BinOp.shr.accepts .uint = true) t jv hj256
            have e2 := eval_shr_lit (g := g) (ν := ν) hs (LTm.app2 (.binop .mod hm) t (.lit Mv)) jv hj256
            have e3 := eval_mod_lit (g := g) (ν := ν) hm t Mv hM0
            have f1 := congrArg (Option.map (· % Wv.1)) e1
            have f2 := congrArg (Option.map (· % Wv.1)) e2
            simp only [Option.map_map] at f1 f2
            refine f1.trans (Eq.trans ?_ f2.symm)
            cases ht : t.eval g ν with
            | none =>
              rw [ht, Option.map_none] at e3
              cases hu' : ((LTm.app2 (.binop .mod hm) t (.lit Mv)).eval g ν : Option PrimTy.uint.Denote) with
              | none => rfl
              | some _ => rw [hu', Option.map_some] at e3; cases e3
            | some a =>
              rw [ht, Option.map_some] at e3
              cases hu' : ((LTm.app2 (.binop .mod hm) t (.lit Mv)).eval g ν : Option PrimTy.uint.Denote) with
              | none => rw [hu', Option.map_none] at e3; cases e3
              | some b =>
                rw [hu', Option.map_some, Option.some.injEq] at e3
                simp only [Option.map_some, Function.comp, e3, hMv, hm1, hWv, hw1]
                have hjn : (jv.1.toNat : Int) = jv.1 := Int.toNat_of_nonneg (by omega)
                exact congrArg some (emod_pow_ediv a.1 m jv.1.toNat w (by omega)).symm
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- `x % c` read as `x` at `uint` where `x`'s range lies below the
positive literal `c` (Lean only): a word reassembled from its bytes, of a
type narrower than its modulus. -/
def Facts.modSmall (F : Facts C) {p : PrimTy} (x y : LTm C (.val p)) : Option (LTm C (.val p)) :=
  match y.litV? with
  | some c =>
    if p == .uint && decide (0 < PrimTy.ival c) && decide (0 ≤ (F.range x).1) &&
        decide ((F.range x).2 < PrimTy.ival c) then some x else none
  | none => none

theorem Facts.modSmall_eval {F : Facts C} (hF : F.Ok g ν) {p : PrimTy}
    (hs : BinOp.mod.accepts p = true) {x y a : LTm C (.val p)} (h : F.modSmall x y = some a) :
    (a.eval g ν : Option p.Denote) = (LTm.app2 (.binop .mod hs) x y).eval g ν := by
  unfold Facts.modSmall at h
  split at h
  · rename_i c hc
    split at h
    · rename_i hb
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
      obtain ⟨⟨⟨hpu, hc0⟩, hlo⟩, hhi⟩ := hb
      subst hpu
      obtain rfl := LTm.eq_of_litV? hc
      rw [eval_uop .mod hs (fun _ => rfl)]
      cases hx : (x.eval g ν : Option PrimTy.uint.Denote) with
      | none => rfl
      | some u =>
        have hr := F.range_sound hF x hx
        unfold InR at hr
        simp only [PrimTy.ival] at hr hc0 hhi
        show some u = (BinOp.arithInt .mod u.1 c.1).bind PrimTy.uint.ofInt?
        simp only [BinOp.arithInt, if_neg (Int.ne_of_gt hc0), Option.bind_some,
          Int.tmod_eq_emod_of_nonneg (by omega : 0 ≤ u.1)]
        rw [Int.emod_eq_of_lt (by omega : 0 ≤ u.1) (by omega : u.1 < c.1)]
        exact (uint_ofInt?_ival u).symm
    · cases h
  · cases h

/-- A remainder `a % c` read again by `Facts.modSmall`. -/
def Facts.reMod (F : Facts C) (t : LTm C (.val .uint)) : LTm C (.val .uint) :=
  match t.uArgs? .mod with
  | some (a, b) =>
    match F.modSmall a b with
    | some r => r
    | none => t
  | none => t

theorem Facts.reMod_eval {F : Facts C} (hF : F.Ok g ν) (t : LTm C (.val .uint)) :
    ((F.reMod t).eval g ν : Option PrimTy.uint.Denote) = t.eval g ν := by
  unfold Facts.reMod
  split
  · rename_i a b ht
    obtain ⟨hp, hte⟩ := LTm.uArgs?_eq ht
    cases hte
    split
    · rename_i r hr
      exact Facts.modSmall_eval hF hp hr
    · rfl
  · rfl

/-- The bit clauses at a numeric type: only `uint` is read. -/
def bitsAdd {p : PrimTy} (x y : LTm C (.val p)) : Option (LTm C (.val p)) :=
  match p, x, y with
  | .uint, x, y => hornerU? x y
  | _, _, _ => none

def bitsMod {p : PrimTy} (x y : LTm C (.val p)) : Option (LTm C (.val p)) :=
  match p, x, y with
  | .uint, x, y =>
    match modModU? x y with
    | some t => some t
    | none => modShrModU? x y
  | _, _, _ => none

def bitsShr {p : PrimTy} (x y : LTm C (.val p)) : Option (LTm C (.val p)) :=
  match p, x, y with
  | .uint, x, y => shrZeroU? x y
  | _, _, _ => none

theorem bitsAdd_eval {p : PrimTy} (h : BinOp.add.accepts p = true) {x y a : LTm C (.val p)}
    (ha : bitsAdd x y = some a) :
    (a.eval g ν : Option p.Denote) = (LTm.app2 (.binop .add h) x y).eval g ν := by
  cases p with
  | uint => exact hornerU?_eval h ha
  | _ => cases ha

theorem bitsMod_eval {p : PrimTy} (h : BinOp.mod.accepts p = true) {x y a : LTm C (.val p)}
    (ha : bitsMod x y = some a) :
    (a.eval g ν : Option p.Denote) = (LTm.app2 (.binop .mod h) x y).eval g ν := by
  cases p with
  | uint =>
    simp only [bitsMod] at ha
    split at ha
    · rename_i t ht; cases ha; exact modModU?_eval h ht
    · exact modShrModU?_eval h ha
  | _ => cases ha

theorem bitsShr_eval {p : PrimTy} (h : BinOp.shr.accepts p = true) {x y a : LTm C (.val p)}
    (ha : bitsShr x y = some a) :
    (a.eval g ν : Option p.Denote) = (LTm.app2 (.binop .shr h) x y).eval g ν := by
  cases p with
  | uint => exact shrZeroU?_eval h ha
  | _ => cases ha

/-- `Facts.reMod` at a numeric type: only `uint` is read. -/
def Facts.reModP (F : Facts C) {p : PrimTy} (t : LTm C (.val p)) : LTm C (.val p) :=
  match p, t with
  | .uint, t => F.reMod t
  | _, t => t

theorem Facts.reModP_eval {F : Facts C} (hF : F.Ok g ν) {p : PrimTy} (t : LTm C (.val p)) :
    ((F.reModP t).eval g ν : Option p.Denote) = t.eval g ν := by
  cases p with
  | uint => exact Facts.reMod_eval hF t
  | _ => rfl

/-- A binary symbol folded: on literals, `a == a`, `a != a` on a term that
returns, `a == b`/`a != b` on terms apart (`Facts.apart`), `x == true`/
`x == false` as `x`/`!x` (`eqBoolLit`), `x < x + c` (`Facts.ltSucc`), a
comparison of terms whose ranges decide it, `(a + b) - b` and
`(a - b) + b` (`Facts.cancel`, `Facts.cancelAdd`), `(a * k + c) / k`
(`Facts.cancelDiv`), `2 * y` as `y + y` (`isTwo`), and bytes reassembled
(`bitsAdd`, `bitsMod`, `bitsShr`). -/
def Facts.fold2 (F : Facts C) {a b s : Srt} (o : Op2 C a b s) (x : LTm C a) (y : LTm C b) :
    LTm C s :=
  match o, x, y with
  | .binop .eqB h, x, y =>
    if x.beqR y && F.returns x then .lit (p := .bool) true
    else if F.apart x y then .lit (p := .bool) false
    else
      match eqBoolLit x y with
      | some t => t
      | none => Decide.fold2 (.binop .eqB h) x y
  | .binop .neB h, x, y =>
    if x.beqR y && F.returns x then .lit (p := .bool) false
    else if F.apart x y then .lit (p := .bool) true
    else Decide.fold2 (.binop .neB h) x y
  | .binop .lt h, x, y =>
    if F.ltSucc x y then .lit (p := .bool) true else
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
  | .binop .add h, x, y =>
    match F.cancelAdd x y with
    | some t => t
    | none =>
      match bitsAdd x y with
      | some t => F.reModP t
      | none => Decide.fold2 (.binop .add h) x y
  | .binop .mul h, x, y =>
    if isTwo x then Decide.fold2 (.binop .add h) y y else Decide.fold2 (.binop .mul h) x y
  | .binop .div h, x, y =>
    match F.cancelDiv x y with
    | some t => t
    | none => Decide.fold2 (.binop .div h) x y
  | .binop .mod h, x, y =>
    match bitsMod x y with
    | some t => t
    | none =>
      match F.modSmall x y with
      | some t => t
      | none => Decide.fold2 (.binop .mod h) x y
  | .binop .shr h, x, y =>
    match bitsShr x y with
    | some t => t
    | none => Decide.fold2 (.binop .shr h) x y
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
        show _ = binopT _ _ v (some v)
        cases p <;> simp only [binopT, BinOp.shortT, Option.bind_some, BinOp.evalT,
          BinOp.evalNum, BinOp.evalBool, decide_true, Bool.not_true]
      split
      · rename_i hb
        obtain ⟨u, v, hu, hv, hne⟩ := F.apart_sound hF hb
        rw [LTm.eval_app2, hu, hv]
        refine Eq.trans (b := some _) rfl ?_
        show _ = binopT _ _ u (some v)
        cases p with
        | bool =>
          simp only [binopT, BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalBool,
            decide_eq_false hne, Bool.not_false]
        | uint | int =>
          have hne' : ¬ u.1 = v.1 := fun e => hne (Subtype.ext e)
          simp only [binopT, BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum,
            decide_eq_false hne', Bool.not_false]
      · first
          | (split
             · rename_i t ht
               exact eqBoolLit_eval ht h
             · exact Decide.fold2_eval g ν _ x y)
          | exact Decide.fold2_eval g ν _ x y
    case lt =>
      have hnum : p.isNumeric = true := by
        cases p <;> first | rfl | cases h
      simp only [Facts.fold2]
      split
      · rename_i hs
        obtain ⟨u, w, hu, hw, hlt⟩ := F.ltSucc_sound hF hs
        simp only [LTm.eval_app2, hu, hw]
        rw [Op2.eval_eq_evalM]
        simp only [Op2.evalM, Option.bind_some]
        unfold binopT
        cases p with
        | bool => cases hnum
        | uint | int =>
          simp only [BinOp.shortT, Option.bind_some, BinOp.evalT, BinOp.evalNum]
          exact congrArg some (decide_eq_true hlt).symm
      · split
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
    case gt | le | ge =>
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
    case add =>
      simp only [Facts.fold2]
      split
      · rename_i t ht
        exact Facts.cancelAdd_eval hF h ht
      · split
        · rename_i t ht
          exact (Facts.reModP_eval hF t).trans (bitsAdd_eval h ht)
        · exact Decide.fold2_eval g ν _ x y
    case mul =>
      simp only [Facts.fold2]
      split
      · rename_i hx
        rw [Decide.fold2_eval]
        exact evalT_two_mul hx h y
      · exact Decide.fold2_eval g ν _ x y
    case div =>
      simp only [Facts.fold2]
      split
      · rename_i t ht
        exact Facts.cancelDiv_eval hF h ht
      · exact Decide.fold2_eval g ν _ x y
    case mod =>
      simp only [Facts.fold2]
      split
      · rename_i t ht
        exact bitsMod_eval h ht
      · split
        · rename_i t ht
          exact Facts.modSmall_eval hF h ht
        · exact Decide.fold2_eval g ν _ x y
    case shr =>
      simp only [Facts.fold2]
      split
      · rename_i t ht
        exact bitsShr_eval h ht
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
  | _, .app0 o => F.rw (.app0 o)
  | _, .app1 o x => F.rw (F.fold1 o (F.nfM x))
  | _, .app2 o x y => F.rw (F.fold2 o (F.nfM x) (F.nfM y))
  | _, .app3 o x y z => F.rw (F.fold3 o (F.nfM x) (F.nfM y) (F.nfM z))
  | _, .index it q i => .index it (F.nfM q) (F.nfM i)
  | _, .obsW q => F.rw (.obsW (F.nfM q))
  | _, .obsL q => F.rw (.obsL (F.nfM q))
  | _, .obsH q => F.rw (F.hasRange (hasN (.obsH (F.nfM q))))
  | _, .seq d a => F.seqN (F.nfM d) (F.nfM a)
  | _, .orElse a b => F.orElseN (F.nfM a) (F.nfM b)
  | _, .kite a b t e => F.rw (F.kiteN (F.nfM a) (F.nfM b) (F.nfM t) (F.nfM e))
  | _, .err => .err

/-- **A term's normal form under the facts**, bottom-up: symbols folded,
guards that return dropped, keys compared, what a premise rewrites
rewritten.  By the recursor. -/
@[implemented_by Facts.nfM]
def Facts.nf (F : Facts C) {s : Srt} (t : LTm C s) : LTm C s :=
  @LTm.rec C (fun s _ => LTm C s)
    (@fun _ k => F.rw (.var k))
    (@fun _ o => F.rw (.app0 o))
    (@fun _ _ o _ ihx => F.rw (F.fold1 o ihx))
    (@fun _ _ _ o _ _ ihx ihy => F.rw (F.fold2 o ihx ihy))
    (@fun _ _ _ _ o _ _ _ ihx ihy ihz => F.rw (F.fold3 o ihx ihy ihz))
    (@fun _ _ _ it _ _ ihq ihi => .index it ihq ihi)
    (@fun _ _ ih => F.rw (.obsW ih))
    (@fun _ _ ih => F.rw (.obsL ih))
    (@fun _ _ ih => F.rw (F.hasRange (hasN (.obsH ih))))
    (@fun _ _ _ _ ihd iha => F.seqN ihd iha)
    (@fun _ _ _ iha ihb => F.orElseN iha ihb)
    (@fun _ _ _ _ _ _ iha ihb iht ihe => F.rw (F.kiteN iha ihb iht ihe))
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
  | app0 o => exact F.rw_eval hF _
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
    show (F.rw (F.kiteN (F.nf a) (F.nf b) (F.nf t) (F.nf e))).eval g ν = _
    rw [F.rw_eval hF, F.kiteN_eval hF, LTm.eval_kite, LTm.eval_kite, iha, ihb, iht, ihe]

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
