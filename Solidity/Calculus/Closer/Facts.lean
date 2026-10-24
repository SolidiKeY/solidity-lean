import Solidity.Calculus.DecideLang
import Solidity.Calculus.ReadBounds
import Solidity.Calculus.TermEq
import Solidity.Calculus.Decide

/-!
# The closer's symbols, facts and bounds

What the symbols read, the facts, ranges, what returns, where a typed
storage has a location, and an index below the length.

A piece of `Calculus/Closer.lean`, whose docstring describes the whole.
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
  | .zbin _ _ | .zcmp _ _ | .mat _ | .copy _ | .copySt _ | .hash _ => true
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
  case zbin | zcmp | mat | copy | copySt | hash => rfl
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

end Decide

end Solidity
