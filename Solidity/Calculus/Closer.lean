import Solidity.Calculus.DecideSyn
import Solidity.Typing.CanonTest

/-!
# The closer: KeY's first-order and arithmetic taclets as one `Bool`

`sol_prove`'s leaves are first-order formulas over the initial state
(`Fml.reduce`).  KeY closes them with a few hundred simplification taclets,
each a proof step; here they are clauses of one function, `LFml.close`,
proved sound once (`LFml.close_holds`), so that the kernel checks a leaf by
evaluation.  `docs/lean-key-rule-map.md` maps each taclet family to its
clause.

What it knows at a point of a leaf is a `Facts`: terms that return, pairs
of terms equal or apart (from `LFml.syn`), terms known by others (`Eqs`),
the layout `wt(storage)` gives, and the quantified locals with their types.
A premise adds to it (`Facts.prem`): an equation decomposed through `&&`,
`||`, `==`, `!=`, `!` and guards (`Facts.decomp`), a side with a literal or
local normal form rewriting the other (KeY's `applyEq`).

* **Normal forms** (`Facts.nf`): guards dropped, `(x - a) + a` cancelled,
  then bottom-up (`LTerm.simpE`) every node on literals evaluated
  (`foldBin`, `foldUn`, …, checked arithmetic and comparisons, KeY's
  `intSimplification` and literal taclets), `a == a` read as `true`, a
  subterm the premises know rewritten, a default of a known kind read as
  `0` or `false`, a key compared with itself read as its first branch
  (`foldKite`), and an `orElse` whose left side halts or returns resolved.
  Each step keeps what a term returns (`Keeps`); none is trusted.
* **What returns** (`Facts.rets`): an operation whose operands return and
  that accepts them (comparisons on integers, `&&` on `bool`s, literal
  arithmetic that stays in range, or an operation a premise shows returns),
  and a read of the initial storage at a path the layout types
  (`LPath.ty`, `LPath.ty_find`): under `wt(storage)` every root is there,
  canonical at its declared type, so a member, a mapping entry or a
  fixed-size array's element in range is there too.
* **What halts** (`Facts.halts`): a test for a shape the layout says is
  not there (a `delete`'s guards), so `orElse` takes its other side.
* **Intervals** (`Facts.range`, `Facts.bnds`): a `uint` or `int` local
  lies in its type's range, a premise `x <= 100` (`x > 0`, …) narrows it,
  and `+`, `-` add the intervals; a checked `+` or `-` whose interval fits
  its type returns (`Facts.fitsArith`), and a comparison the intervals
  decide folds (`foldCmp`).  KeY's `inEqSimp` on bounds by constants, not
  on differences of terms.  A bound below alone (`Facts.lo`) decides what
  needs no bound above: an array's length is at least `0`, so after a
  `push` it is at least `1` (`values.length > 0`); the length is counted
  unchecked (`bool` arithmetic), which returns on any integers.
* **Formulas** (`Facts.prove`, `Facts.refute`): an equation by normal
  forms, a premise refuted (literals apart, a side that halts), a case
  split on a `bool` local or condition (KeY's `cut` on a formula,
  `Facts.split`).

`LFml.fits` bounds the work: a leaf's tree doubles with each storage write
that reads the storage before it, and `Derive.synClose` skips a leaf past
its bound rather than let the reduction run away.
-/

namespace Solidity

namespace Decide

open Semantics SemanticsProperties

/-! ## Ground evaluation and known values -/

/-- `b` returns what `a` returns, wherever `a` returns. -/
def Keeps (σ : State) (a b : LTerm) : Prop := ∀ v, a.eval σ = .ok v → b.eval σ = .ok v

theorem Keeps.refl (σ : State) (a : LTerm) : Keeps σ a a := fun _ h => h

theorem Keeps.trans {σ : State} {a b c : LTerm} (h₁ : Keeps σ a b) (h₂ : Keeps σ b c) :
    Keeps σ a c := fun v h => h₂ v (h₁ v h)

/-- `a ⊕ b` on two literals, evaluated; `false && b` and `true || b` too. -/
def foldBin (op : BinOp) (p : PrimTy) (a b : LTerm) : LTerm :=
  match a with
  | .lit x =>
    if op = .and ∧ x = .bool false then .lit (.bool false)
    else if op = .or ∧ x = .bool true then .lit (.bool true)
    else match b with
      | .lit y =>
        match evalBinop op p x (.ok y) with
        | .ok v => .lit v
        | .error _ => .binop op p a b
      | _ => .binop op p a b
  | _ => .binop op p a b

theorem foldBin_keeps (σ : State) (op : BinOp) (p : PrimTy) (a b : LTerm) :
    Keeps σ (.binop op p a b) (foldBin op p a b) := by
  intro v h
  unfold foldBin
  split
  · rename_i x
    simp only [LTerm.eval, Res.ok_bind] at h
    split
    · rename_i hx
      obtain ⟨rfl, rfl⟩ := hx
      simp only [evalBinop, pure, Except.pure] at h
      cases h; rfl
    · split
      · rename_i _ hx
        obtain ⟨rfl, rfl⟩ := hx
        simp only [evalBinop, pure, Except.pure] at h
        cases h; rfl
      · split
        · rename_i y
          split
          · rename_i w hw
            simp only [LTerm.eval] at h
            rw [hw] at h
            exact h
          · simp only [LTerm.eval, Res.ok_bind]; exact h
        · simp only [LTerm.eval, Res.ok_bind]; exact h
  · exact h

/-- `−a` or `!a` of a literal, evaluated. -/
def foldUn (op : UnOp) (p : PrimTy) (a : LTerm) : LTerm :=
  match a with
  | .lit x =>
    match applyUnOp op x >>= unopCheck op p with
    | .ok v => .lit v
    | .error _ => .unop op p a
  | _ => .unop op p a

theorem foldUn_keeps (σ : State) (op : UnOp) (p : PrimTy) (a : LTerm) :
    Keeps σ (.unop op p a) (foldUn op p a) := by
  intro v h
  unfold foldUn
  split
  · split
    · rename_i w hw
      simp only [LTerm.eval, Res.ok_bind] at h
      rw [hw] at h
      exact h
    · exact h
  · exact h

/-- A conditional on a literal: its branch. -/
def foldIte (c a b : LTerm) : LTerm :=
  match c with
  | .lit (.bool true) => a
  | .lit (.bool false) => b
  | _ => .ite c a b

theorem foldIte_keeps (σ : State) (c a b : LTerm) : Keeps σ (.ite c a b) (foldIte c a b) := by
  intro v h
  unfold foldIte
  split
  · simp only [LTerm.eval, Res.ok_bind, pickBranch] at h; exact h
  · simp only [LTerm.eval, Res.ok_bind, pickBranch] at h; exact h
  · exact h

/-- A key comparison on two integer literals, or of a key with itself
(`values[values.length + 1 - 1]` after a push): its branch. -/
def foldKite (a b t e : LTerm) : LTerm :=
  if a == b then t else
  match a, b with
  | .lit (.int i), .lit (.int j) => if i = j then t else e
  | _, _ => .kite a b t e

theorem foldKite_keeps (σ : State) (a b t e : LTerm) :
    Keeps σ (.kite a b t e) (foldKite a b t e) := by
  intro v h
  unfold foldKite
  split
  · rename_i hab
    simp only [beq_iff_eq] at hab
    subst hab
    simp only [LTerm.eval] at h
    obtain ⟨i, hi, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨j, hj, h⟩ := Res.bind_eq_ok.1 h
    rw [hi] at hj; cases hj
    simpa only [if_true] using h
  split
  · rename_i i j
    simp only [LTerm.eval, Res.ok_bind, Value.asInt] at h
    rw [apply_ite (LTerm.eval σ)]
    exact h
  · exact h

/-- Terms known by others: `(t, u)` says `u` returns what `t` returns,
where `t` returns (`EqOk`).  A premise `x ≐ 5` gives `(x, 5)`, a premise
`v ≐ alice.age` gives `(alice.age, v)`: KeY's `applyEq`. -/
abbrev Eqs := List (LTerm × LTerm)

/-- What the facts of `E` say holds in `σ`. -/
def EqOk (σ : State) (E : Eqs) : Prop := ∀ p ∈ E, Keeps σ p.1 p.2

/-- `t`, or the term `E` knows it by. -/
def substE (E : Eqs) (t : LTerm) : LTerm :=
  match E.find? (·.1 == t) with
  | some p => p.2
  | none => t

theorem substE_keeps {σ : State} {E : Eqs} (hE : EqOk σ E) (t : LTerm) :
    Keeps σ t (substE E t) := by
  intro v h
  unfold substE
  split
  · rename_i q hq
    have hm := List.mem_of_find?_eq_some hq
    have he : q.1 = t := by simpa only [beq_iff_eq] using List.find?_some hq
    rw [← he] at h
    exact hE q hm v h
  · exact h

/-- Where `t` returns: an integer (`some true`), a `bool` (`some false`). -/
def KindOk (σ : State) (K : LTerm → Option Bool) : Prop :=
  ∀ t v, t.eval σ = .ok v → (K t = some true → ∃ i, v = .int i) ∧ (K t = some false → ∃ b,
      v = .bool b)

/-- What the simplifier may ask of a term: its kind, that it halts, that it
returns. -/
structure Orc where
  kind : LTerm → Option Bool := fun _ => none
  halts : LTerm → Bool := fun _ => false
  rets : LTerm → Bool := fun _ => false
  range : LTerm → Option (Int × Int) := fun _ => none
  lo : LTerm → Option Int := fun _ => none

/-- An interval holds of a term: where `t` returns an integer, it lies in
it. -/
def RangeOk (σ : State) (R : LTerm → Option (Int × Int)) : Prop :=
  ∀ t l h i, R t = some (l, h) → t.eval σ = .ok (.int i) → l ≤ i ∧ i ≤ h

/-- A lower bound holds of a term: where `t` returns an integer, it is at
least that. -/
def LoOk (σ : State) (L : LTerm → Option Int) : Prop :=
  ∀ t l i, L t = some l → t.eval σ = .ok (.int i) → l ≤ i

/-- The oracle's answers hold in `σ`. -/
def Orc.Ok (σ : State) (O : Orc) : Prop :=
  KindOk σ O.kind ∧ (∀ t v, O.halts t = true → t.eval σ ≠ .ok v) ∧
    (∀ t, O.rets t = true → Returns σ t) ∧ RangeOk σ O.range ∧ LoOk σ O.lo

theorem Orc.ok_none (σ : State) : Orc.Ok σ {} :=
  ⟨fun _ _ _ => ⟨fun h => by simp only [reduceCtorEq] at h,
      fun h => by simp only [reduceCtorEq] at h⟩, fun _ _ h => by simp only [Bool.false_eq_true]
          at h,
    fun _ h => by simp only [Bool.false_eq_true] at h, fun _ _ _ _ h => by
      simp only [reduceCtorEq] at h, fun _ _ _ h => by simp only [reduceCtorEq] at h⟩

/-- The default of a term whose kind is known: `0` or `false`. -/
def foldZeroT (K : LTerm → Option Bool) (a : LTerm) : LTerm :=
  match a with
  | .lit v => .lit (zeroV v)
  | _ =>
    match K a with
    | some true => .lit (.int 0)
    | some false => .lit (.bool false)
    | none => .zero a

theorem foldZeroT_keeps {σ : State} {K : LTerm → Option Bool} (hK : KindOk σ K) (a : LTerm) :
    Keeps σ (.zero a) (foldZeroT K a) := by
  intro v h
  unfold foldZeroT
  split
  · simp only [LTerm.eval, Res.ok_bind] at h; exact h
  · simp only [LTerm.eval] at h
    obtain ⟨x, hx, h⟩ := Res.bind_eq_ok.1 h
    cases h
    split
    · rename_i hk; obtain ⟨i, rfl⟩ := (hK a x hx).1 hk; rfl
    · rename_i hk; obtain ⟨b, rfl⟩ := (hK a x hx).2 hk; rfl
    · simp only [LTerm.eval, hx, Res.ok_bind]

/-- A comparison of a term with itself: `a == a` is `true` wherever it
returns. -/
def foldSame (t : LTerm) : LTerm :=
  match t with
  | .binop op _ a b =>
    if a == b then
      match op with
      | .eqB | .le | .ge => .lit (.bool true)
      | .neB | .lt | .gt => .lit (.bool false)
      | _ => t
    else t
  | _ => t

theorem foldSame_keeps (σ : State) (t : LTerm) : Keeps σ t (foldSame t) := by
  intro v h
  unfold foldSame
  split
  · rename_i op p a b
    split
    · rename_i hab
      simp only [beq_iff_eq] at hab
      subst hab
      simp only [LTerm.eval] at h
      obtain ⟨x, hx, h⟩ := Res.bind_eq_ok.1 h
      rw [hx] at h
      split <;> first
        | (cases x <;> simp only [evalBinop, bind, Except.bind, applyBinOp, decide_true,
            checkArith, Except.ok.injEq, Value.asInt, Int.le_refl, reduceCtorEq, Bool.not_true,
            Int.lt_irrefl, decide_false] at h <;> subst h <;> rfl)
        | (simp only [LTerm.eval, hx, Res.ok_bind]; exact h)
    · exact h
  · exact h

/-- What a comparison returns on integers. -/
def cmpOp : BinOp → Int → Int → Bool
  | .lt, i, j => decide (i < j)
  | .le, i, j => decide (i ≤ j)
  | .gt, i, j => decide (j < i)
  | .ge, i, j => decide (j ≤ i)
  | _, _, _ => false

/-- A comparison its operands' intervals decide. -/
def cmpDecide (op : BinOp) (la ha lb hb : Int) : Option Bool :=
  match op with
  | .lt => if ha < lb then some true else if hb ≤ la then some false else none
  | .le => if ha ≤ lb then some true else if hb < la then some false else none
  | .gt => if hb < la then some true else if ha ≤ lb then some false else none
  | .ge => if hb ≤ la then some true else if ha < lb then some false else none
  | _ => none

theorem cmpDecide_sound {op : BinOp} {la ha lb hb i j : Int} {c : Bool}
    (h : cmpDecide op la ha lb hb = some c) (hi : la ≤ i ∧ i ≤ ha) (hj : lb ≤ j ∧ j ≤ hb) :
    cmpOp op i j = c := by
  cases op <;> simp only [cmpDecide, reduceCtorEq] at h
  all_goals
    split at h
    · cases h; simp only [cmpOp, decide_eq_true_eq]; omega
    · split at h
      · cases h; simp only [cmpOp, decide_eq_false_iff_not]; omega
      · cases h

theorem evalBinop_cmp {op : BinOp} (hop : op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge) {p : PrimTy}
    {x : Value} {rb : Res Value} {v : Value} (h : evalBinop op p x rb = .ok v) :
    ∃ i j, x = .int i ∧ rb = .ok (.int j) ∧ v = .bool (cmpOp op i j) := by
  rcases hop with rfl | rfl | rfl | rfl <;>
  (cases rb with
    | error e => cases x <;> simp only [evalBinop, bind, Except.bind, reduceCtorEq] at h
    | ok y =>
      cases x <;> cases y <;>
        simp only [evalBinop, applyBinOp, Value.asInt, bind, Except.bind, checkArith,
          Except.ok.injEq, reduceCtorEq] at h <;>
        exact ⟨_, _, rfl, rfl, by rw [← h]; rfl⟩)

/-- `x < y`, both bounds known. -/
def ltO : Option Int → Option Int → Bool
  | some x, some y => decide (x < y)
  | _, _ => false

/-- `x ≤ y`, both bounds known. -/
def leO : Option Int → Option Int → Bool
  | some x, some y => decide (x ≤ y)
  | _, _ => false

/-- A comparison its operands' bounds decide, a bound possibly missing: a
length is at least `0`, with no bound above. -/
def cmpDecideO (op : BinOp) (la ha lb hb : Option Int) : Option Bool :=
  match op with
  | .lt => if ltO ha lb then some true else if leO hb la then some false else none
  | .le => if leO ha lb then some true else if ltO hb la then some false else none
  | .gt => if ltO hb la then some true else if leO ha lb then some false else none
  | .ge => if leO hb la then some true else if ltO ha lb then some false else none
  | _ => none

/-- A bound below holds of `i`. -/
def LoHolds (l : Option Int) (i : Int) : Prop := ∀ x, l = some x → x ≤ i

/-- A bound above holds of `i`. -/
def HiHolds (h : Option Int) (i : Int) : Prop := ∀ x, h = some x → i ≤ x

theorem cmpDecideO_sound {op : BinOp} {la ha lb hb : Option Int} {i j : Int} {c : Bool}
    (h : cmpDecideO op la ha lb hb = some c) (hli : LoHolds la i) (hhi : HiHolds ha i)
    (hlj : LoHolds lb j) (hhj : HiHolds hb j) : cmpOp op i j = c := by
  have lt_ok : ∀ {x y : Option Int} {a b : Int}, ltO x y = true → HiHolds x a → LoHolds y b →
      a < b := by
    intro x y a b hxy hx hy
    match x, y, hxy with
    | some x, some y, hxy =>
      simp only [ltO, decide_eq_true_eq] at hxy
      have := hx x rfl; have := hy y rfl; omega
  have le_ok : ∀ {x y : Option Int} {a b : Int}, leO x y = true → HiHolds x a → LoHolds y b →
      a ≤ b := by
    intro x y a b hxy hx hy
    match x, y, hxy with
    | some x, some y, hxy =>
      simp only [leO, decide_eq_true_eq] at hxy
      have := hx x rfl; have := hy y rfl; omega
  cases op <;> simp only [cmpDecideO, reduceCtorEq] at h
  · by_cases h₁ : ltO ha lb = true
    · rw [if_pos h₁] at h; cases h
      simp only [cmpOp, decide_eq_true_eq]; exact lt_ok h₁ hhi hlj
    · rw [if_neg h₁] at h
      by_cases h₂ : leO hb la = true
      · rw [if_pos h₂] at h; cases h
        simp only [cmpOp, decide_eq_false_iff_not, Int.not_lt]; exact le_ok h₂ hhj hli
      · rw [if_neg h₂] at h; cases h
  · by_cases h₁ : ltO hb la = true
    · rw [if_pos h₁] at h; cases h
      simp only [cmpOp, decide_eq_true_eq]; exact lt_ok h₁ hhj hli
    · rw [if_neg h₁] at h
      by_cases h₂ : leO ha lb = true
      · rw [if_pos h₂] at h; cases h
        simp only [cmpOp, decide_eq_false_iff_not, Int.not_lt]; exact le_ok h₂ hhi hlj
      · rw [if_neg h₂] at h; cases h
  · by_cases h₁ : leO ha lb = true
    · rw [if_pos h₁] at h; cases h
      simp only [cmpOp, decide_eq_true_eq]; exact le_ok h₁ hhi hlj
    · rw [if_neg h₁] at h
      by_cases h₂ : ltO hb la = true
      · rw [if_pos h₂] at h; cases h
        simp only [cmpOp, decide_eq_false_iff_not, Int.not_le]; exact lt_ok h₂ hhj hli
      · rw [if_neg h₂] at h; cases h
  · by_cases h₁ : leO hb la = true
    · rw [if_pos h₁] at h; cases h
      simp only [cmpOp, decide_eq_true_eq]; exact le_ok h₁ hhj hli
    · rw [if_neg h₁] at h
      by_cases h₂ : ltO ha lb = true
      · rw [if_pos h₂] at h; cases h
        simp only [cmpOp, decide_eq_false_iff_not, Int.not_le]; exact lt_ok h₂ hhi hlj
      · rw [if_neg h₂] at h; cases h

/-- The bounds of a term: its interval's, or a bound below alone. -/
def bndsOf (R : LTerm → Option (Int × Int)) (L : LTerm → Option Int) (a : LTerm) :
    Option Int × Option Int :=
  match R a with
  | some (l, h) => (some l, some h)
  | none => (L a, none)

theorem bndsOf_holds {σ : State} {R : LTerm → Option (Int × Int)} {L : LTerm → Option Int}
    (hR : RangeOk σ R) (hL : LoOk σ L) {a : LTerm} {i : Int} (ha : a.eval σ = .ok (.int i)) :
    LoHolds (bndsOf R L a).1 i ∧ HiHolds (bndsOf R L a).2 i := by
  unfold bndsOf
  split
  · rename_i l h hr
    have := hR a l h i hr ha
    exact ⟨fun x hx => by cases hx; exact this.1, fun x hx => by cases hx; exact this.2⟩
  · exact ⟨fun x hx => hL a x i hx ha, fun x hx => by cases hx⟩

/-- A comparison its operands' bounds decide, as a literal. -/
def foldCmp (R : LTerm → Option (Int × Int)) (L : LTerm → Option Int) (t : LTerm) : LTerm :=
  match t with
  | .binop op _ a b =>
    match cmpDecideO op (bndsOf R L a).1 (bndsOf R L a).2 (bndsOf R L b).1 (bndsOf R L b).2 with
    | some c => .lit (.bool c)
    | none => t
  | _ => t

theorem foldCmp_keeps {σ : State} {R : LTerm → Option (Int × Int)} {L : LTerm → Option Int}
    (hR : RangeOk σ R) (hL : LoOk σ L) (t : LTerm) : Keeps σ t (foldCmp R L t) := by
  intro v h
  unfold foldCmp
  split
  · rename_i op p a b
    split
    · rename_i c hc
      have hop : op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge := by
        cases op <;> simp only [cmpDecideO, reduceCtorEq] at hc <;>
          simp only [reduceCtorEq, or_self, or_false, or_true]
      simp only [LTerm.eval] at h
      obtain ⟨x, hx, h⟩ := Res.bind_eq_ok.1 h
      obtain ⟨i, j, rfl, hj, rfl⟩ := evalBinop_cmp hop h
      have ha := bndsOf_holds hR hL hx
      have hb := bndsOf_holds hR hL hj
      rw [cmpDecideO_sound hc ha.1 ha.2 hb.1 hb.2]
      rfl
    · exact h
  · exact h

mutual

/-- The term simplified bottom-up: every node on literals evaluated
(`foldBin`, …), every subterm `E` knows replaced by its value.  Not the left
side of an `orElse`, whose halting picks the right. -/
def LTerm.simpE (O : Orc) (E : Eqs) : LTerm → LTerm
  | .lit v => .lit v
  | .var x => substE E (.var x)
  | .err => .err
  | .env k => .env k
  | .binop op p a b =>
    substE E (foldCmp O.range O.lo (foldSame (foldBin op p (a.simpE O E) (b.simpE O E))))
  | .unop op p a => substE E (foldUn op p (a.simpE O E))
  | .ite c a b => substE E (foldIte (c.simpE O E) (a.simpE O E) (b.simpE O E))
  | .zero a => substE E (foldZeroT O.kind (a.simpE O E))
  | .kite a b t e => substE E (foldKite (a.simpE O E) (b.simpE O E) (t.simpE O E) (e.simpE O E))
  | .seq _ a => a.simpE O E
  | .find s q => substE E (.find (s.simpE O E) (q.simpE O E))
  | .findP s q => substE E (.findP (s.simpE O E) (q.simpE O E))
  | .has s q => .has (s.simpE O E) (q.simpE O E)
  | .kmap sh s q => .kmap sh (s.simpE O E) (q.simpE O E)
  | .len s q => substE E (.len (s.simpE O E) (q.simpE O E))
  | .sok s => .sok (s.simpE O E)
  | .pok q => .pok (q.simpE O E)
  | .orElse a b =>
    if O.halts a then b.simpE O E
    else if O.rets a then a.simpE O E
    else substE E (.orElse a (b.simpE O E))

/-- The path with its keys simplified. -/
def LPath.simpE (O : Orc) (E : Eqs) : LPath → LPath
  | .root r => .root r
  | .field q f => .field (q.simpE O E) f
  | .at q k => .at (q.simpE O E) (k.simpE O E)

/-- The storage with its terms simplified. -/
def LStor.simpE (O : Orc) (E : Eqs) : LStor → LStor
  | .init => .init
  | .save s q w => .save (s.simpE O E) (q.simpE O E) (w.simpE O E)
  | .del s q => .del (s.simpE O E) (q.simpE O E)
  | .arr op s q w => .arr op (s.simpE O E) (q.simpE O E) (w.simpE O E)
  | .copy s q src sq => .copy (s.simpE O E) (q.simpE O E) (src.simpE O E) (sq.simpE O E)

end

mutual

/-- **Simplifying keeps what a term returns.** -/
theorem LTerm.simpE_eval {σ : State} {O : Orc} {E : Eqs} (hO : O.Ok σ) (hE : EqOk σ E) :
    (t : LTerm) → Keeps σ t (t.simpE O E)
  | .lit _, _, h | .err, _, h | .env _, _, h => h
  | .var x, v, h => substE_keeps hE _ v h
  | .binop op p a b, v, h => by
    refine substE_keeps hE _ v (foldCmp_keeps hO.2.2.2.1 hO.2.2.2.2 _ v
      (foldSame_keeps σ _ v (foldBin_keeps σ op p _ _ v ?_)))
    simp only [LTerm.eval] at h ⊢
    obtain ⟨x, ha, hb⟩ := Res.bind_eq_ok.1 h
    simp only [LTerm.simpE_eval hO hE a x ha, Res.ok_bind]
    exact evalBinop_congr hb (fun w hw => LTerm.simpE_eval hO hE b w hw)
  | .unop op p a, v, h => by
    refine substE_keeps hE _ v (foldUn_keeps σ op p _ v ?_)
    simp only [LTerm.eval] at h ⊢
    obtain ⟨x, ha, h⟩ := Res.bind_eq_ok.1 h
    simp only [LTerm.simpE_eval hO hE a x ha, Res.ok_bind]
    exact h
  | .ite c a b, v, h => by
    refine substE_keeps hE _ v (foldIte_keeps σ _ _ _ v ?_)
    simp only [LTerm.eval] at h ⊢
    obtain ⟨x, hc, h⟩ := Res.bind_eq_ok.1 h
    simp only [LTerm.simpE_eval hO hE c x hc, Res.ok_bind]
    unfold pickBranch at h ⊢
    split at h
    · exact LTerm.simpE_eval hO hE a v h
    · exact LTerm.simpE_eval hO hE b v h
    · exact h
  | .zero a, v, h => by
    refine substE_keeps hE _ v (foldZeroT_keeps hO.1 _ v ?_)
    simp only [LTerm.eval] at h ⊢
    obtain ⟨x, ha, h⟩ := Res.bind_eq_ok.1 h
    simp only [LTerm.simpE_eval hO hE a x ha, Res.ok_bind]
    exact h
  | .kite a b t e, v, h => by
    refine substE_keeps hE _ v (foldKite_keeps σ _ _ _ _ v ?_)
    simp only [LTerm.eval] at h ⊢
    obtain ⟨i, hi, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨x, ha, hi⟩ := Res.bind_eq_ok.1 hi
    obtain ⟨j, hj, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hb, hj⟩ := Res.bind_eq_ok.1 hj
    simp only [LTerm.simpE_eval hO hE a x ha, LTerm.simpE_eval hO hE b y hb, Res.ok_bind, hi, hj]
    by_cases hij : i = j
    · rw [if_pos hij] at h ⊢; exact LTerm.simpE_eval hO hE t v h
    · rw [if_neg hij] at h ⊢; exact LTerm.simpE_eval hO hE e v h
  | .seq d a, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨x, hd, ha⟩ := Res.bind_eq_ok.1 h
    exact LTerm.simpE_eval hO hE a v ha
  | .find s q, v, h | .findP s q, v, h | .len s q, v, h => by
    refine substE_keeps hE _ v ?_
    simp only [LTerm.eval] at h ⊢
    obtain ⟨x, hs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hq, h⟩ := Res.bind_eq_ok.1 h
    simp only [LStor.simpE_eval hO hE s hs, LPath.simpE_eval hO hE q hq, Res.ok_bind]
    exact h
  | .has s q, v, h | .kmap _ s q, v, h => by
    simp only [LTerm.eval] at h ⊢
    obtain ⟨x, hs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hq, h⟩ := Res.bind_eq_ok.1 h
    simp only [LTerm.simpE, LTerm.eval, LStor.simpE_eval hO hE s hs, LPath.simpE_eval hO hE q hq,
      Res.ok_bind]
    exact h
  | .sok s, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨x, hs, h⟩ := Res.bind_eq_ok.1 h
    simp only [LTerm.simpE, LTerm.eval, LStor.simpE_eval hO hE s hs, Res.ok_bind]
    exact h
  | .pok q, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨x, hq, h⟩ := Res.bind_eq_ok.1 h
    simp only [LTerm.simpE, LTerm.eval, LPath.simpE_eval hO hE q hq, Res.ok_bind]
    exact h
  | .orElse a b, v, h => by
    simp only [LTerm.eval] at h
    simp only [LTerm.simpE]
    cases ha : a.eval σ with
    | ok w =>
      rw [ha, orElseR_ok] at h
      cases h
      split
      · rename_i hh; exact absurd ha (hO.2.1 a v hh)
      · split
        · exact LTerm.simpE_eval hO hE a v ha
        · refine substE_keeps hE _ v ?_
          simp only [LTerm.eval, ha, orElseR_ok]
    | error e =>
      rw [ha, orElseR_error] at h
      split
      · exact LTerm.simpE_eval hO hE b v h
      · split
        · rename_i _ hr
          obtain ⟨w, hw⟩ := hO.2.2.1 a hr
          rw [ha] at hw; cases hw
        · refine substE_keeps hE _ v ?_
          simp only [LTerm.eval, ha, orElseR_error]
          exact LTerm.simpE_eval hO hE b v h

/-- Simplifying keeps the path a path evaluates to. -/
theorem LPath.simpE_eval {σ : State} {O : Orc} {E : Eqs} (hO : O.Ok σ) (hE : EqOk σ E) :
    (q : LPath) → ∀ {ps : List Seg}, q.eval σ = .ok ps → (q.simpE O E).eval σ = .ok ps
  | .root _, _, h => h
  | .field q f, ps, h => by
    simp only [LPath.eval] at h
    obtain ⟨x, hq, h⟩ := Res.bind_eq_ok.1 h
    simp only [LPath.simpE, LPath.eval, LPath.simpE_eval hO hE q hq, Res.ok_bind]
    exact h
  | .at q k, ps, h => by
    simp only [LPath.eval] at h
    obtain ⟨x, hq, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨i, hk, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hk, hi⟩ := Res.bind_eq_ok.1 hk
    simp only [LPath.simpE, LPath.eval, LPath.simpE_eval hO hE q hq, LTerm.simpE_eval hO hE k y hk,
      Res.ok_bind, hi]
    exact h

/-- Simplifying keeps the storage a storage evaluates to. -/
theorem LStor.simpE_eval {σ : State} {O : Orc} {E : Eqs} (hO : O.Ok σ) (hE : EqOk σ E) :
    (s : LStor) → ∀ {sv : SVal}, s.eval σ = .ok sv → (s.simpE O E).eval σ = .ok sv
  | .init, _, h => h
  | .save s q w, sv, h => by
    simp only [LStor.eval] at h
    obtain ⟨x, hw, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨z, hq, h⟩ := Res.bind_eq_ok.1 h
    simp only [LStor.simpE, LStor.eval, LTerm.simpE_eval hO hE w x hw, LStor.simpE_eval hO hE s hs,
      LPath.simpE_eval hO hE q hq, Res.ok_bind]
    exact h
  | .del s q, sv, h => by
    simp only [LStor.eval] at h
    obtain ⟨y, hs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨z, hq, h⟩ := Res.bind_eq_ok.1 h
    simp only [LStor.simpE, LStor.eval, LStor.simpE_eval hO hE s hs, LPath.simpE_eval hO hE q hq,
      Res.ok_bind]
    exact h
  | .arr _ s q w, sv, h => by
    simp only [LStor.eval] at h
    obtain ⟨x, hw, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨z, hq, h⟩ := Res.bind_eq_ok.1 h
    simp only [LStor.simpE, LStor.eval, LTerm.simpE_eval hO hE w x hw, LStor.simpE_eval hO hE s hs,
      LPath.simpE_eval hO hE q hq, Res.ok_bind]
    exact h
  | .copy s q src sq, sv, h => by
    simp only [LStor.eval] at h
    obtain ⟨a, ha, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨b, hb, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨n, hn, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hs, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨z, hq, h⟩ := Res.bind_eq_ok.1 h
    simp only [LStor.simpE, LStor.eval, LStor.simpE_eval hO hE src ha, LPath.simpE_eval hO hE sq hb,
      LStor.simpE_eval hO hE s hs, LPath.simpE_eval hO hE q hq, Res.ok_bind, hn]
    exact h

end


/-! ## What a well-formed storage holds

Under `wt(storage)` every root is there, canonical at its declared type
(`SVal.canonB`): a struct has exactly its members, a mapping every key (its
default), a fixed-size array its length.  So a read along a path whose type
the layout gives statically, a fixed-size array indexed in range, returns:
KeY's `wellFormed(heap)` with the typed `select` lemmas. -/

/-- The roots of `L` are in `σ`'s storage, each canonical at its type. -/
def LayoutOk (L : List (Name × Ty)) (σ : State) : Prop :=
  ∀ r T, lookupBy r L = some T → ∃ v, lookupBy r σ.storage = some v ∧ v.canonB T = true

/-- The type of a path in the layout `L`: through a struct's member, a
mapping's key, a fixed-size array's index `inB` puts in range; none
through a dynamic array, whose length the layout does not give. -/
def LPath.ty (L : List (Name × Ty)) (inB : LTerm → Nat → Bool) : LPath → Option Ty
  | .root r => lookupBy r L
  | .field q f =>
    match q.ty L inB with
    | some (.ref (.struct s)) => lookupBy f (structDef s)
    | _ => none
  | .at q k =>
    match q.ty L inB with
    | some (.ref (.mapping _ V)) => some V
    | some (.ref (.fixed E n)) => if inB k n then some E else none
    | _ => none

open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB) in
theorem canonFieldsB_lookup {s f : Name} {v : SVal} :
    ∀ {fields : List (Name × SVal)}, canonFieldsB s fields = true → lookupBy f fields = some v →
      ∃ T, lookupBy f (structDef s) = some T ∧ v.canonB T = true
  | [], _, h => by simp only [lookupBy, reduceCtorEq] at h
  | (n, w) :: rest, hc, h => by
    simp only [canonFieldsB, Bool.and_eq_true] at hc
    simp only [lookupBy] at h
    split at h
    · rename_i hn
      subst hn
      cases h
      revert hc
      split
      · rename_i T hT
        exact fun hc => ⟨T, hT, hc.1⟩
      · exact fun hc => absurd hc.1 Bool.false_ne_true
    · exact canonFieldsB_lookup hc.2 h

theorem lookupBy_isSome_iff {κ α : Type} [DecidableEq κ] {k : κ} :
    ∀ {l : List (κ × α)}, (lookupBy k l).isSome = true ↔ k ∈ l.map (·.1)
  | [] => by simp only [lookupBy, Option.isSome_none, Bool.false_eq_true, List.map_nil,
      List.not_mem_nil]
  | (k', v) :: l => by
    simp only [lookupBy, List.map_cons, List.mem_cons]
    split
    · rename_i h; simp only [Option.isSome_some, h, List.mem_map, Prod.exists, exists_and_right,
        exists_eq_right, true_or]
    · rename_i h; simp only [h, false_or]; exact lookupBy_isSome_iff

open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB) in
theorem canonEntriesB_lookup {V : Ty} {i : Int} {v : SVal} :
    ∀ {es : List (Int × SVal)}, canonEntriesB V es = true → lookupBy i es = some v →
      v.canonB V = true
  | [], _, h => by simp only [lookupBy, reduceCtorEq] at h
  | (n, w) :: rest, hc, h => by
    simp only [canonEntriesB, Bool.and_eq_true] at hc
    simp only [lookupBy] at h
    split at h
    · cases h; exact hc.1
    · exact canonEntriesB_lookup hc.2 h

open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB) in
theorem canonElemsB_get {E : Ty} :
    ∀ {es : List SVal} {i : Nat} (h : i < es.length), canonElemsB E es = true →
      (es.get ⟨i, h⟩).canonB E = true
  | [], _, h, _ => absurd h (Nat.not_lt_zero _)
  | w :: rest, 0, _, hc => by
    simp only [canonElemsB, Bool.and_eq_true] at hc; exact hc.1
  | w :: rest, i + 1, h, hc => by
    simp only [canonElemsB, Bool.and_eq_true] at hc
    exact canonElemsB_get (Nat.lt_of_succ_lt_succ h) hc.2

open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB) in
/-- One step down a canonical value, at a member its type declares. -/
theorem canon_field {v : SVal} {s f : Name} {T : Ty} (hv : v.canonB (.ref (.struct s)) = true)
    (hT : lookupBy f (structDef s) = some T) :
    ∃ w, v.findLive [.field f] = .ok w ∧ w.canonB T = true := by
  match v, hv with
  | .struct fields, hv =>
    simp only [SVal.canonB, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨hn, hc⟩ := hv
    have hs : (lookupBy f fields).isSome = true := by
      rw [lookupBy_isSome_iff, hn, ← lookupBy_isSome_iff, hT]; rfl
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨T', hT', hc'⟩ := canonFieldsB_lookup hc hw
    rw [hT] at hT'
    cases hT'
    exact ⟨w, by simp only [SVal.findLive, hw, SVal.findLive_nil], hc'⟩

open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB) in
/-- One step down a canonical mapping, at any key. -/
theorem canon_key {v : SVal} {K V : Ty} (hv : v.canonB (.ref (.mapping K V)) = true) (i : Int) :
    ∃ w, v.findLive [.at i] = .ok w ∧ w.canonB V = true := by
  match v, hv with
  | .map es d, hv =>
    simp only [SVal.canonB, Bool.and_eq_true] at hv
    obtain ⟨⟨⟨-, hc⟩, -⟩, hd⟩ := hv
    simp only [SVal.findLive]
    split
    · rename_i w hw
      exact ⟨w, rfl, canonEntriesB_lookup hc hw⟩
    · exact ⟨d, rfl, hd⟩

open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB) in
/-- One step down a canonical fixed-size array, at an index in range. -/
theorem canon_index {v : SVal} {E : Ty} {n : Nat} (hv : v.canonB (.ref (.fixed E n)) = true)
    {i : Int} (h0 : 0 ≤ i) (hn : i < n) :
    ∃ w, v.findLive [.at i] = .ok w ∧ w.canonB E = true := by
  match v, hv with
  | .array es sh fx, hv =>
    simp only [SVal.canonB, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨⟨-, hl⟩, hc⟩, -⟩ := hv
    have hi : i.toNat < es.length := by omega
    refine ⟨es.get ⟨i.toNat, hi⟩, ?_, canonElemsB_get hi hc⟩
    simp only [SVal.findLive, h0, hi, and_self, dif_pos, SVal.findLive_nil]

/-- **A path the layout types is there** in a storage that holds the
layout, canonical at its type. -/
theorem LPath.ty_find {σ : State} {L : List (Name × Ty)} {inB : LTerm → Nat → Bool}
    (hL : LayoutOk L σ)
    (hB : ∀ k n, inB k n = true → ∀ i, (k.eval σ >>= Value.asInt) = .ok i → 0 ≤ i ∧ i < n) :
    (q : LPath) → ∀ {T : Ty} {qs : List Seg}, q.ty L inB = some T → q.eval σ = .ok qs →
      ∃ v, (SVal.struct σ.storage).findLive qs = .ok v ∧ v.canonB T = true
  | .root r, T, qs, ht, hq => by
    simp only [LPath.eval] at hq
    cases hq
    obtain ⟨v, hv, hc⟩ := hL r T ht
    exact ⟨v, by simp only [SVal.findLive, hv, SVal.findLive_nil], hc⟩
  | .field q f, T, qs, ht, hq => by
    simp only [LPath.eval] at hq
    obtain ⟨qs₀, hq₀, hq⟩ := Res.bind_eq_ok.1 hq
    cases hq
    simp only [LPath.ty] at ht
    split at ht
    · rename_i s hs
      obtain ⟨v, hv, hc⟩ := LPath.ty_find hL hB q hs hq₀
      obtain ⟨w, hw, hc'⟩ := canon_field hc ht
      exact ⟨w, by rw [SVal.findLive_append, hv, Res.ok_bind, hw], hc'⟩
    · cases ht
  | .at q k, T, qs, ht, hq => by
    simp only [LPath.eval] at hq
    obtain ⟨qs₀, hq₀, hq⟩ := Res.bind_eq_ok.1 hq
    obtain ⟨i, hi, hq⟩ := Res.bind_eq_ok.1 hq
    cases hq
    simp only [LPath.ty] at ht
    split at ht
    · rename_i K V hs
      cases ht
      obtain ⟨v, hv, hc⟩ := LPath.ty_find hL hB q hs hq₀
      obtain ⟨w, hw, hc'⟩ := canon_key hc i
      exact ⟨w, by rw [SVal.findLive_append, hv, Res.ok_bind, hw], hc'⟩
    · rename_i E n hs
      split at ht
      · rename_i hk
        cases ht
        obtain ⟨v, hv, hc⟩ := LPath.ty_find hL hB q hs hq₀
        obtain ⟨h0, hn⟩ := hB k n hk i hi
        obtain ⟨w, hw, hc'⟩ := canon_index hc h0 hn
        exact ⟨w, by rw [SVal.findLive_append, hv, Res.ok_bind, hw], hc'⟩
      · cases ht
    · cases ht

/-! ## The facts a leaf's premises give -/

/-- What the closer knows at a point of a leaf: terms that return
(`known`), pairs of terms equal or apart (`ne`), terms' values (`eqs`), the
layout a well-formed storage holds (`lay`), and the quantified locals with
their types (`vars`). -/
structure Facts where
  known : List LTerm := []
  ne : Keys := []
  eqs : Eqs := []
  lay : List (Name × Ty) := []
  vars : List (Var × PrimTy) := []
  /-- Intervals the premises give: `(t, l, h)`, where `t` returns an integer
  it lies in `[l, h]`. -/
  bnds : List (LTerm × Int × Int) := []

/-- The intervals of `B` hold in `σ`. -/
def BndOk (σ : State) (B : List (LTerm × Int × Int)) : Prop :=
  ∀ b ∈ B, ∀ i, b.1.eval σ = .ok (.int i) → b.2.1 ≤ i ∧ i ≤ b.2.2

/-- What the facts say holds in `σ`. -/
def Facts.Ok (σ : State) (F : Facts) : Prop :=
  (∀ u ∈ F.known, Returns σ u) ∧ Apart σ F.ne ∧ EqOk σ F.eqs ∧ LayoutOk F.lay σ ∧
    (∀ xp ∈ F.vars, ∃ v, (LTerm.var xp.1).eval σ = .ok v ∧ xp.2.admits v) ∧ BndOk σ F.bnds

/-- The normal form a path's key is compared by: its guards dropped (`LTerm.core`),
`(x - a) + a` cancelled (`LTerm.arith`), and simplified (`LTerm.simpE`). -/
def Facts.nf0 (F : Facts) (t : LTerm) : LTerm := ((t.core F.ne).arith).simpE {} F.eqs

theorem Facts.nf0_keeps {σ : State} {F : Facts} (hF : F.Ok σ) (t : LTerm) : Keeps σ t (F.nf0 t) :=
  fun v h => LTerm.simpE_eval (Orc.ok_none σ) hF.2.2.1 _ v
    (LTerm.arith_eval _ (LTerm.core_eval hF.2.1 t h))

/-- A term whose normal form is a literal returns that literal, if anything. -/
theorem Facts.nf0_lit {σ : State} {F : Facts} (hF : F.Ok σ) {t : LTerm} {w v : Value}
    (hn : F.nf0 t = .lit w) (hv : t.eval σ = .ok v) : v = w := by
  have h := F.nf0_keeps hF t v hv
  rw [hn] at h
  simp only [LTerm.eval, Except.ok.injEq] at h
  exact h.symm

/-- The key `k` is an integer in `[0, n)` wherever it is one. -/
def Facts.inB (F : Facts) (k : LTerm) (n : Nat) : Bool :=
  match F.nf0 k with
  | .lit (.int i) => decide (0 ≤ i ∧ i < n)
  | _ => false

theorem Facts.inB_sound {σ : State} {F : Facts} (hF : F.Ok σ) {k : LTerm} {n : Nat}
    (h : F.inB k n = true) (i : Int) (hi : (k.eval σ >>= Value.asInt) = .ok i) :
    0 ≤ i ∧ i < n := by
  unfold Facts.inB at h
  split at h
  · rename_i j hj
    obtain ⟨x, hx, hxi⟩ := Res.bind_eq_ok.1 hi
    cases F.nf0_lit hF hj hx
    simp only [Value.asInt, Except.ok.injEq] at hxi
    subst hxi
    simpa only [Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] using h
  · cases h

/-- The type of a path in the layout. -/
def Facts.pty (F : Facts) (q : LPath) : Option Ty := q.ty F.lay F.inB

theorem Facts.pty_find {σ : State} {F : Facts} (hF : F.Ok σ) {q : LPath} {T : Ty}
    {qs : List Seg} (ht : F.pty q = some T) (hq : q.eval σ = .ok qs) :
    ∃ v, (SVal.struct σ.storage).findLive qs = .ok v ∧ v.canonB T = true :=
  LPath.ty_find hF.2.2.2.1 (fun _ _ h i hi => F.inB_sound hF h i hi) q ht hq

/-! ## The slot a `push()` of the initial storage takes

A `push()` of a struct or an array onto an array of the initial storage
takes the first slot past its end: an element popped before, or the type's
default.  Under `wt(storage)` both are canonical at the element type (the
storage's shadow is checked as its elements are, `SVal.canonB`; a default is
canonical where the type's structs are, `defaultForTy_canonB`), so a read
below the slot, or below an element at an index up to the old length, is
typed as a read of the initial storage is (`Facts.slotTy`): its shape and
kind follow the type, and it returns where the index is in range
(`Facts.slotIn`). -/

deriving instance DecidableEq for SSeg

/-- The segments of `q` after its prefix `p`. -/
def segsAfter : List SSeg → List SSeg → Option (List SSeg)
  | [], q => some q
  | a :: p, b :: q => if a = b then segsAfter p q else none
  | _ :: _, [] => none

theorem segsAfter_spec : ∀ {p q r : List SSeg}, segsAfter p q = some r → q = p ++ r
  | [], q, r, h => by simp only [segsAfter, Option.some.injEq] at h; subst h; rfl
  | a :: p, b :: q, r, h => by
    simp only [segsAfter] at h
    split at h
    · rename_i hab; subst hab; rw [segsAfter_spec h]; rfl
    · cases h
  | _ :: _, [], _, h => by simp [segsAfter] at h

/-- `Q` as `P[k]` and the segments below: the index and the rest. -/
def LPath.splitAt (P Q : LPath) : Option (LTerm × List SSeg) :=
  match segsAfter P.segs Q.segs with
  | some (.key k :: rest) => some (k, rest)
  | _ => none

theorem LPath.splitAt_spec {P Q : LPath} {k : LTerm} {rest : List SSeg}
    (h : P.splitAt Q = some (k, rest)) : Q.segs = P.segs ++ .key k :: rest := by
  unfold LPath.splitAt at h
  split at h
  · rename_i k' rest' hs
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact segsAfter_spec hs
  · cases h

theorem segsEval_append_inv (σ : State) : ∀ {xs ys : List SSeg} {zs : List Seg},
    segsEval σ (xs ++ ys) = .ok zs →
      ∃ a b, segsEval σ xs = .ok a ∧ segsEval σ ys = .ok b ∧ zs = a ++ b
  | [], ys, zs, h => ⟨[], zs, rfl, h, rfl⟩
  | .field f :: xs, ys, zs, h => by
    obtain ⟨zs', h', he⟩ := Res.bind_eq_ok.1 h
    cases he
    obtain ⟨a, b, ha, hb, rfl⟩ := segsEval_append_inv σ h'
    exact ⟨.field f :: a, b, by simp only [segsEval, ha, Res.ok_bind], hb, rfl⟩
  | .key k :: xs, ys, zs, h => by
    obtain ⟨i, hi, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨zs', h', he⟩ := Res.bind_eq_ok.1 h
    cases he
    obtain ⟨a, b, ha, hb, rfl⟩ := segsEval_append_inv σ h'
    exact ⟨.at i :: a, b, by simp only [segsEval, hi, ha, Res.ok_bind], hb, rfl⟩

/-- The type below a value of type `T`, along members, mapping keys and
array indices: what a read there returns, where it returns. -/
def tyFrom : Ty → List SSeg → Option Ty
  | T, [] => some T
  | .ref (.struct s), .field f :: r => (lookupBy f (structDef s)).bind fun T => tyFrom T r
  | .ref (.mapping _ V), .key _ :: r => tyFrom V r
  | .ref (.fixed E _), .key _ :: r => tyFrom E r
  | .ref (.array E), .key _ :: r => tyFrom E r
  | _, _ :: _ => none

/-- A read below a value of type `T` returns: through members, mapping keys
and fixed-size indices `inB` puts in range, no dynamic array's index. -/
def exFrom (inB : LTerm → Nat → Bool) : Ty → List SSeg → Bool
  | _, [] => true
  | .ref (.struct s), .field f :: r =>
    match lookupBy f (structDef s) with
    | some T => exFrom inB T r
    | none => false
  | .ref (.mapping _ V), .key _ :: r => exFrom inB V r
  | .ref (.fixed E n), .key k :: r => inB k n && exFrom inB E r
  | _, _ :: _ => false

theorem findLive_cons (v : SVal) (s : Seg) (r : List Seg) :
    v.findLive (s :: r) = v.findLive [s] >>= fun w => w.findLive r := by
  rw [← SVal.findLive_append]; rfl

open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB) in
/-- An index of a canonical array read: a canonical element. -/
theorem canon_elem_find {v : SVal} {E : Ty}
    (hv : ∃ es sh fx, v = .array es sh fx ∧ canonElemsB E es = true) {i : Int} {r : List Seg}
    {w : SVal} (h : v.findLive (.at i :: r) = .ok w) :
    ∃ e : SVal, e.canonB E = true ∧ e.findLive r = .ok w := by
  obtain ⟨es, sh, fx, rfl, hes⟩ := hv
  simp only [SVal.findLive] at h
  split at h
  · rename_i hr
    exact ⟨_, canonElemsB_get hr.2 hes, h⟩
  · cases h

open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB) in
/-- **A typed read below a canonical value** returns a canonical value of its
type, where it returns. -/
theorem tyFrom_canon {σ : State} :
    ∀ (rest : List SSeg) {v : SVal} {T T' : Ty} {r : List Seg}, v.canonB T = true →
      tyFrom T rest = some T' → segsEval σ rest = .ok r →
        ∀ w, v.findLive r = .ok w → w.canonB T' = true
  | [], v, T, T', r, hv, ht, hr, w, hw => by
    simp only [tyFrom, Option.some.injEq] at ht; subst ht
    cases hr
    have : w = v := by cases v <;> simp_all [SVal.findLive]
    subst this; exact hv
  | .field f :: rest, v, T, T', r, hv, ht, hr, w, hw => by
    obtain ⟨r', hr', he⟩ := Res.bind_eq_ok.1 hr
    cases he
    match T, ht with
    | .ref (.struct s), ht =>
      simp only [tyFrom] at ht
      obtain ⟨T₀, hT₀, ht⟩ := Option.bind_eq_some_iff.1 ht
      obtain ⟨w₀, hw₀, hc⟩ := canon_field hv hT₀
      rw [findLive_cons, hw₀, Res.ok_bind] at hw
      exact tyFrom_canon rest hc ht hr' w hw
  | .key k :: rest, v, T, T', r, hv, ht, hr, w, hw => by
    obtain ⟨i, hi, hr⟩ := Res.bind_eq_ok.1 hr
    obtain ⟨r', hr', he⟩ := Res.bind_eq_ok.1 hr
    cases he
    match T, ht with
    | .ref (.mapping K V), ht =>
      simp only [tyFrom] at ht
      obtain ⟨w₀, hw₀, hc⟩ := canon_key hv i
      rw [findLive_cons, hw₀, Res.ok_bind] at hw
      exact tyFrom_canon rest hc ht hr' w hw
    | .ref (.fixed E n), ht =>
      simp only [tyFrom] at ht
      match v, hv with
      | .array es sh fx, hv =>
        simp only [SVal.canonB, Bool.and_eq_true] at hv
        obtain ⟨e, hc, he⟩ := canon_elem_find ⟨es, sh, fx, rfl, hv.1.2⟩ hw
        exact tyFrom_canon rest hc ht hr' w he
    | .ref (.array E), ht =>
      simp only [tyFrom] at ht
      match v, hv with
      | .array es sh fx, hv =>
        simp only [SVal.canonB, Bool.and_eq_true] at hv
        obtain ⟨e, hc, he⟩ := canon_elem_find ⟨es, sh, fx, rfl, hv.1.2⟩ hw
        exact tyFrom_canon rest hc ht hr' w he

open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB) in
/-- **A typed read below a canonical value returns** where its indices are
in range, and it reads no dynamic array's element. -/
theorem tyFrom_exists {σ : State} {inB : LTerm → Nat → Bool}
    (hB : ∀ k n, inB k n = true → ∀ i, (k.eval σ >>= Value.asInt) = .ok i → 0 ≤ i ∧ i < n) :
    ∀ (rest : List SSeg) {v : SVal} {T : Ty} {r : List Seg}, v.canonB T = true →
      exFrom inB T rest = true → segsEval σ rest = .ok r → ∃ w, v.findLive r = .ok w
  | [], v, T, r, _, _, hr => by cases hr; exact ⟨v, by cases v <;> rfl⟩
  | .field f :: rest, v, T, r, hv, he, hr => by
    obtain ⟨r', hr', hh⟩ := Res.bind_eq_ok.1 hr
    cases hh
    match T, he with
    | .ref (.struct s), he =>
      simp only [exFrom] at he
      split at he
      · rename_i T₀ hT₀
        obtain ⟨w₀, hw₀, hc⟩ := canon_field hv hT₀
        obtain ⟨w, hw⟩ := tyFrom_exists hB rest hc he hr'
        exact ⟨w, by rw [findLive_cons, hw₀, Res.ok_bind, hw]⟩
      · cases he
  | .key k :: rest, v, T, r, hv, he, hr => by
    obtain ⟨i, hi, hr⟩ := Res.bind_eq_ok.1 hr
    obtain ⟨r', hr', hh⟩ := Res.bind_eq_ok.1 hr
    cases hh
    match T, he with
    | .ref (.mapping K V), he =>
      simp only [exFrom] at he
      obtain ⟨w₀, hw₀, hc⟩ := canon_key hv i
      obtain ⟨w, hw⟩ := tyFrom_exists hB rest hc he hr'
      exact ⟨w, by rw [findLive_cons, hw₀, Res.ok_bind, hw]⟩
    | .ref (.fixed E n), he =>
      simp only [exFrom, Bool.and_eq_true] at he
      obtain ⟨h0, hn⟩ := hB k n he.1 i hi
      obtain ⟨w₀, hw₀, hc⟩ := canon_index hv h0 hn
      obtain ⟨w, hw⟩ := tyFrom_exists hB rest hc he.2 hr'
      exact ⟨w, by rw [findLive_cons, hw₀, Res.ok_bind, hw]⟩

/-- The storages a `push()` of a struct or an array takes its slot from, as
far as the slot facts read them: the initial one, and the initial one with
the array at `P` deleted (`delete values; values.push();`). -/
def baseOk : LStor → LPath → Bool
  | .init, _ => true
  | .del .init P', P => P' == P
  | _, _ => false

/-- The length of the array at `P` in such a storage: the initial one's, or
`0` after its `delete`. -/
def baseLen : LStor → LPath → LTerm
  | .init, P => .len .init P
  | _, _ => .lit (.int 0)

/-- The type of a read below the slot a `push()` takes (or an element
before it), the array at `P` of such a storage: the layout's element type,
then down the rest. -/
def Facts.slotTy (F : Facts) : LStor → LPath → Option Ty
  | .arr (.slot E) base P (.lit _), Q =>
    if P.noLen && baseOk base P then
      match F.pty P, P.splitAt Q with
      | some (.ref (.array E')), some (_, rest) =>
        if E = E' ∧ E.okDeep = true then tyFrom E rest else none
      | _, _ => none
    else none
  | _, _ => none

/-- The index of such a read is at most the old length, by the normal forms
`N` gives: an element, or the slot; `0` always is. -/
def Facts.slotIn (F : Facts) (N : LTerm → LTerm) : LStor → LPath → Bool
  | .arr (.slot E) base P _, Q =>
    match P.splitAt Q with
    | some (k, rest) =>
      exFrom F.inB E rest && (N k == .lit (.int 0) ||
        match N k, N (baseLen base P) with
        | .lit (.int i), .lit (.int n) => decide (0 ≤ i ∧ i ≤ n)
        | a, b => a == b)
    | none => false
  | _, _ => false

open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB) in
theorem canonElemsB_append {E : Ty} : ∀ {es fs : List SVal}, canonElemsB E es = true →
    canonElemsB E fs = true → canonElemsB E (es ++ fs) = true
  | [], _, _, h => h
  | _ :: es, fs, h, h' => by
    simp only [canonElemsB, Bool.and_eq_true, List.cons_append] at h ⊢
    exact ⟨h.1, canonElemsB_append h.2 h'⟩

open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB) in
theorem canonElemsB_defaultOf {E : Ty} : ∀ {es : List SVal}, canonElemsB E es = true →
    canonElemsB E (SVal.defaultOf.defaultOfElems es) = true
  | [], _ => by simp [SVal.defaultOf.defaultOfElems, canonElemsB]
  | e :: es, h => by
    simp only [canonElemsB, Bool.and_eq_true] at h
    simp only [SVal.defaultOf.defaultOfElems, canonElemsB, Bool.and_eq_true]
    exact ⟨SVal.canonB_iff.2 (SVal.defaultOf_canon (SVal.canonB_iff.1 h.1)),
      canonElemsB_defaultOf h.2⟩

open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB) in
/-- **The array a slot is taken from**: in the initial storage or after its
`delete`, an array whose elements and slots past the end are canonical, of
the length `baseLen` reads. -/
theorem Facts.slot_base {σ : State} {F : Facts} (hF : F.Ok σ) {base : LStor} {P : LPath}
    {E : Ty} (hb : baseOk base P = true) (hn : P.noLen = true)
    (hpty : F.pty P = some (.ref (.array E))) {ps : List Seg} (hp : P.eval σ = .ok ps) :
    ∃ v0 es sh fx, base.eval σ = .ok v0 ∧ v0.findLive ps = .ok (.array es sh fx) ∧
      canonElemsB E es = true ∧ canonElemsB E sh = true ∧
      (baseLen base P).eval σ = .ok (.int es.length) := by
  obtain ⟨c0, hc0, hcan⟩ := F.pty_find hF hpty hp
  match c0, hcan with
  | .array es0 sh0 fx0, hcan =>
    simp only [SVal.canonB, Bool.and_eq_true] at hcan
    obtain ⟨⟨hfx, hes⟩, hsh⟩ := hcan
    match base, hb with
    | .init, _ =>
      exact ⟨_, es0, sh0, fx0, rfl, hc0, hes, hsh, by
        simp only [baseLen, LTerm.eval, LStor.eval, hp, hc0, Res.ok_bind, Close.arrLen]⟩
    | .del .init P', hb =>
      simp only [baseOk, beq_iff_eq] at hb
      subst hb
      simp only [Bool.not_eq_true'] at hfx
      subst hfx
      obtain ⟨u, hu⟩ := (save_ok_iff_find_ok (new := (SVal.array es0 sh0 false).defaultOf)
        (LPath.noLen_eval σ hn hp)).2 ⟨_, hc0⟩
      refine ⟨u, [], SVal.defaultOf.defaultOfElems es0 ++ sh0, false, ?_, ?_, rfl, ?_, rfl⟩
      · simp only [LStor.eval, Res.ok_bind, hp, hc0, hu]
      · rw [findLive_saveLive_same hu]; rfl
      · exact canonElemsB_append (canonElemsB_defaultOf hes) hsh

open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB) in
/-- The slot a `push()` takes, canonical at the element type: an element
popped before, or the default. -/
theorem pushSlot_canonB {E : Ty} {sh : List SVal} (hE : E.okDeep = true)
    (hsh : canonElemsB E sh = true) : (pushSlot E sh).1.canonB E = true := by
  cases sh with
  | nil => exact defaultForTy_canonB hE
  | cons c t =>
    simp only [pushSlot]
    split
    · exact defaultForTy_canonB hE
    · simp only [canonElemsB, Bool.and_eq_true] at hsh; exact hsh.1

open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB) in
/-- **Below the slot or an element up to the old length** is a canonical
element: where a read below the index returns, it reads one; where the
index is in range, it does. -/
theorem slotElem {E : Ty} {es sh : List SVal} {fx : Bool} (hE : E.okDeep = true)
    (hes : canonElemsB E es = true) (hsh : canonElemsB E sh = true) (i : Int) (r : List Seg) :
    (∀ w, (SVal.array (es ++ [(pushSlot E sh).1]) (pushSlot E sh).2 fx).findLive (.at i :: r) =
        .ok w → ∃ e : SVal, e.canonB E = true ∧ e.findLive r = .ok w) ∧
    (0 ≤ i ∧ i ≤ es.length → ∃ e : SVal, e.canonB E = true ∧
      (SVal.array (es ++ [(pushSlot E sh).1]) (pushSlot E sh).2 fx).findLive (.at i :: r) =
        e.findLive r) := by
  rw [findLive_grow es sh _ fx _ i r]
  by_cases hi : i = es.length
  · rw [if_pos hi]
    exact ⟨fun w h => ⟨_, pushSlot_canonB hE hsh, h⟩, fun _ => ⟨_, pushSlot_canonB hE hsh, rfl⟩⟩
  · rw [if_neg hi]
    by_cases hr : 0 ≤ i ∧ i.toNat < es.length
    · have hc := canonElemsB_get hr.2 hes
      have hf : (SVal.array es sh fx).findLive (.at i :: r) = (es.get ⟨i.toNat, hr.2⟩).findLive r := by
        simp only [SVal.findLive, dif_pos hr]
      rw [hf]
      exact ⟨fun w h => ⟨_, hc, h⟩, fun _ => ⟨_, hc, rfl⟩⟩
    · have hf : (SVal.array es sh fx).findLive (.at i :: r) = .error .revert := by
        simp only [SVal.findLive, dif_neg hr]
      rw [hf]
      refine ⟨fun w h => (by cases h), fun h => ?_⟩
      exfalso; apply hr; exact ⟨h.1, by omega⟩

/-- **What the slot facts say holds**: a read the slot type types returns a
canonical value of its type where it returns, and returns where its index
is in range. -/
theorem Facts.slot_find {σ : State} {F : Facts} (hF : F.Ok σ) {S : LStor} {Q : LPath} {T : Ty}
    (ht : F.slotTy S Q = some T) {v : SVal} {qs : List Seg} (hS : S.eval σ = .ok v)
    (hq : Q.eval σ = .ok qs) :
    (∀ w, v.findLive qs = .ok w → w.canonB T = true) ∧
    (∀ N : LTerm → LTerm, (∀ t, Keeps σ t (N t)) → F.slotIn N S Q = true →
      ∃ w, v.findLive qs = .ok w) := by
  match S, ht with
  | .arr (.slot E) base P (.lit c), ht =>
    simp only [Facts.slotTy] at ht
    split at ht
    · rename_i hnb
      simp only [Bool.and_eq_true] at hnb
      split at ht
      · rename_i E' k rest hpty hsp
        split at ht
        · rename_i hEE
          obtain ⟨rfl, hok⟩ := hEE
          obtain ⟨wv, v0', ps, c, c', -, hv0', hp, hc, hap, hu⟩ := arr_eval_ok hS
          obtain ⟨v0, es, sh, fx, hv0, hnode, hes, hsh, hlen⟩ :=
            F.slot_base hF hnb.2 hnb.1 hpty hp
          rw [hv0] at hv0'; cases hv0'
          rw [hnode] at hc; cases hc
          simp only [AOp.apply] at hap; cases hap
          have hQs := LPath.segs_eval σ hq
          rw [LPath.splitAt_spec hsp] at hQs
          obtain ⟨a, b, ha, hb, rfl⟩ := segsEval_append_inv σ hQs
          rw [LPath.segs_eval σ hp] at ha; cases ha
          obtain ⟨i, hi, hb⟩ := Res.bind_eq_ok.1 hb
          obtain ⟨r, hr, he⟩ := Res.bind_eq_ok.1 hb
          cases he
          have hread : v.findLive (ps ++ .at i :: r) =
              (SVal.array (es ++ [(pushSlot E sh).1]) (pushSlot E sh).2 fx).findLive
                (.at i :: r) := by
            rw [SVal.findLive_append, findLive_saveLive_same hu, Res.ok_bind]
          have hel := slotElem (fx := fx) hok hes hsh i r
          have hB := fun k n h i hi => F.inB_sound hF (k := k) (n := n) h i hi
          refine ⟨fun w hw => ?_, fun N hN hin => ?_⟩
          · rw [hread] at hw
            obtain ⟨e, hce, hew⟩ := hel.1 w hw
            exact tyFrom_canon rest hce ht hr w hew
          · simp only [Facts.slotIn, hsp, Bool.and_eq_true, Bool.or_eq_true] at hin
            obtain ⟨hex, hin⟩ := hin
            have hrange : 0 ≤ i ∧ i ≤ es.length := by
              have hk := hN k
              obtain ⟨x, hx, hxi⟩ := Res.bind_eq_ok.1 hi
              have hxk := hk x hx
              rcases hin with hin | hin
              · simp only [beq_iff_eq] at hin
                rw [hin] at hxk
                simp only [LTerm.eval, Except.ok.injEq] at hxk
                subst hxk
                simp only [Value.asInt, Except.ok.injEq] at hxi
                subst hxi
                omega
              · have hLn := hN (baseLen base P) _ hlen
                split at hin
                · rename_i i' n' hi' hn'
                  rw [hi'] at hxk; rw [hn'] at hLn
                  simp only [LTerm.eval, Except.ok.injEq] at hxk hLn
                  subst hxk; cases hLn
                  simp only [Value.asInt, Except.ok.injEq] at hxi
                  subst hxi
                  simpa only [decide_eq_true_eq] using hin
                · simp only [beq_iff_eq] at hin
                  rw [hin] at hxk
                  rw [hxk] at hLn; cases hLn
                  simp only [Value.asInt, Except.ok.injEq] at hxi
                  subst hxi
                  omega
            obtain ⟨e, hce, hew⟩ := hel.2 hrange
            obtain ⟨w', hw'⟩ := tyFrom_exists hB rest hce hex hr
            exact ⟨w', by rw [hread, hew, hw']⟩
        · cases ht
      · cases ht
    · cases ht

/-- A path whose segments evaluate evaluates to them. -/
theorem LPath.eval_of_segs (σ : State) : ∀ {q : LPath} {qs : List Seg},
    segsEval σ q.segs = .ok qs → q.eval σ = .ok qs
  | .root r, qs, h => by cases h; rfl
  | .field q f, qs, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := segsEval_append_inv σ h
    cases hb
    simp only [LPath.eval, LPath.eval_of_segs σ ha, Res.ok_bind]
  | .at q k, qs, h => by
    obtain ⟨a, b, ha, hb, rfl⟩ := segsEval_append_inv σ h
    obtain ⟨i, hi, hb⟩ := Res.bind_eq_ok.1 hb
    obtain ⟨_, he, hb⟩ := Res.bind_eq_ok.1 hb
    cases he; cases hb
    simp only [LPath.eval, LPath.eval_of_segs σ ha, Res.ok_bind, hi]

/-- The storage the slot facts read returns where the read's path does. -/
theorem Facts.slot_ret {σ : State} {F : Facts} (hF : F.Ok σ) {S : LStor} {Q : LPath} {T : Ty}
    (ht : F.slotTy S Q = some T) {qs : List Seg} (hq : Q.eval σ = .ok qs) :
    ∃ v, S.eval σ = .ok v := by
  match S, ht with
  | .arr (.slot E) base P (.lit c), ht =>
    simp only [Facts.slotTy] at ht
    split at ht
    · rename_i hnb
      simp only [Bool.and_eq_true] at hnb
      split at ht
      · rename_i E' k rest hpty hsp
        have hQs := LPath.segs_eval σ hq
        rw [LPath.splitAt_spec hsp] at hQs
        obtain ⟨ps, b, ha, -, -⟩ := segsEval_append_inv σ hQs
        have hp := LPath.eval_of_segs σ ha
        obtain ⟨v0, es, sh, fx, hv0, hnode, -, -, -⟩ := F.slot_base hF hnb.2 hnb.1 hpty hp
        obtain ⟨u, hu⟩ := (save_ok_iff_find_ok
          (new := .array (es ++ [(pushSlot E sh).1]) (pushSlot E sh).2 fx)
          (LPath.noLen_eval σ hnb.1 hp)).2 ⟨_, hnode⟩
        exact ⟨u, by simp only [LStor.eval, LTerm.eval, Res.ok_bind, hv0, hp, hnode, AOp.apply, hu]⟩
      · cases ht
    · cases ht

/-- **A read the slot facts type**, where it returns, reads a canonical
value of its type. -/
theorem Facts.slot_read {σ : State} {F : Facts} (hF : F.Ok σ) {S : LStor} {Q : LPath} {T : Ty}
    (ht : F.slotTy S Q = some T) {α : Type} {G : SVal → Res α} {x : α}
    (h : (S.eval σ >>= fun v => Q.eval σ >>= fun qs => v.findLive qs >>= G) = .ok x) :
    ∃ w, w.canonB T = true ∧ G w = .ok x := by
  obtain ⟨v, hv, h⟩ := Res.bind_eq_ok.1 h
  obtain ⟨qs, hq, h⟩ := Res.bind_eq_ok.1 h
  obtain ⟨w, hw, h⟩ := Res.bind_eq_ok.1 h
  exact ⟨w, (F.slot_find hF ht hv hq).1 w hw, h⟩

open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB) in
/-- A slot of a canonical array read past its end too (`SVal.find`): a
canonical element, live or not. -/
theorem canon_slot_find {E : Ty} {es sh : List SVal} {fx : Bool}
    (hes : canonElemsB E (es ++ sh) = true) {i : Int} {r : List Seg} {w : SVal}
    (h : (SVal.array es sh fx).find (.at i :: r) = .ok w) :
    ∃ e : SVal, e.canonB E = true ∧ e.find r = .ok w := by
  simp only [SVal.find] at h
  split at h
  · rename_i hr
    exact ⟨_, canonElemsB_get hr.2 hes, h⟩
  · cases h

open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB) in
/-- **A typed read below a canonical value, past the live ends too**,
returns a canonical value of its type where it returns. -/
theorem tyFrom_canonP {σ : State} :
    ∀ (rest : List SSeg) {v : SVal} {T T' : Ty} {r : List Seg}, v.canonB T = true →
      tyFrom T rest = some T' → segsEval σ rest = .ok r →
        ∀ w, v.find r = .ok w → w.canonB T' = true
  | [], v, T, T', r, hv, ht, hr, w, hw => by
    simp only [tyFrom, Option.some.injEq] at ht; subst ht
    cases hr
    have : w = v := by cases v <;> simp_all [SVal.find]
    subst this; exact hv
  | .field f :: rest, v, T, T', r, hv, ht, hr, w, hw => by
    obtain ⟨r', hr', he⟩ := Res.bind_eq_ok.1 hr
    cases he
    match T, ht with
    | .ref (.struct s), ht =>
      simp only [tyFrom] at ht
      obtain ⟨T₀, hT₀, ht⟩ := Option.bind_eq_some_iff.1 ht
      obtain ⟨w₀, hw₀, hc⟩ := canon_field hv hT₀
      rw [show Seg.field f :: r' = [Seg.field f] ++ r' from rfl, SVal.find_append,
        SVal.find_of_findLive hw₀, Res.ok_bind] at hw
      exact tyFrom_canonP rest hc ht hr' w hw
  | .key k :: rest, v, T, T', r, hv, ht, hr, w, hw => by
    obtain ⟨i, hi, hr⟩ := Res.bind_eq_ok.1 hr
    obtain ⟨r', hr', he⟩ := Res.bind_eq_ok.1 hr
    cases he
    match T, ht with
    | .ref (.mapping K V), ht =>
      simp only [tyFrom] at ht
      obtain ⟨w₀, hw₀, hc⟩ := canon_key hv i
      rw [show Seg.at i :: r' = [Seg.at i] ++ r' from rfl, SVal.find_append,
        SVal.find_of_findLive hw₀, Res.ok_bind] at hw
      exact tyFrom_canonP rest hc ht hr' w hw
    | .ref (.fixed E n), ht =>
      simp only [tyFrom] at ht
      match v, hv with
      | .array es sh fx, hv =>
        simp only [SVal.canonB, Bool.and_eq_true] at hv
        obtain ⟨e, hc, he⟩ := canon_slot_find (canonElemsB_append hv.1.2 hv.2) hw
        exact tyFrom_canonP rest hc ht hr' w he
    | .ref (.array E), ht =>
      simp only [tyFrom] at ht
      match v, hv with
      | .array es sh fx, hv =>
        simp only [SVal.canonB, Bool.and_eq_true] at hv
        obtain ⟨e, hc, he⟩ := canon_slot_find (canonElemsB_append hv.1.2 hv.2) hw
        exact tyFrom_canonP rest hc ht hr' w he

open Semantics.SVal.canonB (canonFieldsB canonElemsB canonEntriesB) in
/-- **A snapshot read the slot facts type** reads a canonical value of its
type where it returns: past the live ends, the slots are canonical too. -/
theorem Facts.slot_readP {σ : State} {F : Facts} (hF : F.Ok σ) {S : LStor} {Q : LPath} {T : Ty}
    (ht : F.slotTy S Q = some T) {α : Type} {G : SVal → Res α} {x : α}
    (h : (S.eval σ >>= fun v => Q.eval σ >>= fun qs => v.find qs >>= G) = .ok x) :
    ∃ w, w.canonB T = true ∧ G w = .ok x := by
  obtain ⟨v, hS, h⟩ := Res.bind_eq_ok.1 h
  obtain ⟨qs, hq, h⟩ := Res.bind_eq_ok.1 h
  obtain ⟨w, hw, h⟩ := Res.bind_eq_ok.1 h
  refine ⟨w, ?_, h⟩
  match S, ht with
  | .arr (.slot E) base P (.lit c), ht =>
    simp only [Facts.slotTy] at ht
    split at ht
    · rename_i hnb
      simp only [Bool.and_eq_true] at hnb
      split at ht
      · rename_i E' k rest hpty hsp
        split at ht
        · rename_i hEE
          obtain ⟨rfl, hok⟩ := hEE
          obtain ⟨wv, v0', ps, c, c', -, hv0', hp, hc, hap, hu⟩ := arr_eval_ok hS
          obtain ⟨v0, es, sh, fx, hv0, hnode, hes, hsh, -⟩ := F.slot_base hF hnb.2 hnb.1 hpty hp
          rw [hv0] at hv0'; cases hv0'
          rw [hnode] at hc; cases hc
          simp only [AOp.apply] at hap; cases hap
          have hQs := LPath.segs_eval σ hq
          rw [LPath.splitAt_spec hsp] at hQs
          obtain ⟨a, b, ha, hb, rfl⟩ := segsEval_append_inv σ hQs
          rw [LPath.segs_eval σ hp] at ha; cases ha
          obtain ⟨i, hi, hb⟩ := Res.bind_eq_ok.1 hb
          obtain ⟨r, hr, he⟩ := Res.bind_eq_ok.1 hb
          cases he
          rw [SVal.find_append, SVal.find_of_findLive (findLive_saveLive_same hu),
            Res.ok_bind] at hw
          have hall : canonElemsB E ((es ++ [(pushSlot E sh).1]) ++ (pushSlot E sh).2) = true := by
            refine canonElemsB_append (canonElemsB_append hes ?_) ?_
            · simp only [canonElemsB, pushSlot_canonB hok hsh, Bool.and_self]
            · cases sh with
              | nil => rfl
              | cons c t =>
                simp only [canonElemsB, Bool.and_eq_true] at hsh
                exact hsh.2
          obtain ⟨e, hce, hew⟩ := canon_slot_find hall hw
          exact tyFrom_canonP rest hce ht hr w hew
        · cases ht
      · cases ht
    · cases ht

/-- **A read the slot facts type, at an index in range**, returns a
canonical value of its type. -/
theorem Facts.slot_resolve {σ : State} {F : Facts} (hF : F.Ok σ) {N : LTerm → LTerm}
    (hN : ∀ t, Keeps σ t (N t)) {S : LStor} {Q : LPath} {T : Ty} (ht : F.slotTy S Q = some T)
    (hin : F.slotIn N S Q = true) (hk : ∃ qs, Q.eval σ = .ok qs) :
    ∃ v qs w, S.eval σ = .ok v ∧ Q.eval σ = .ok qs ∧ v.findLive qs = .ok w ∧
      w.canonB T = true := by
  obtain ⟨qs, hq⟩ := hk
  obtain ⟨v, hv⟩ := F.slot_ret hF ht hq
  have hs := F.slot_find hF ht hv hq
  obtain ⟨w, hw⟩ := hs.2 N hN hin
  exact ⟨v, qs, w, hv, hq, hw, hs.1 w hw⟩


/-- The type is a `uint` or an `int`. -/
def tyInt : Option Ty → Bool
  | some (.prim .uint) | some (.prim .int) => true
  | _ => false

/-- The type is a `bool`. -/
def tyBool : Option Ty → Bool
  | some (.prim .bool) => true
  | _ => false

/-- The type is a word. -/
def tyPrim : Option Ty → Bool
  | some (.prim _) => true
  | _ => false

/-- The type has the shape `sh`. -/
def tyShape : KShape → Option Ty → Bool
  | .map, some (.ref (.mapping _ _)) | .fixed, some (.ref (.fixed _ _)) => true
  | _, _ => false

/-- The type does not have the shape `sh`. -/
def tyShapeNot : KShape → Option Ty → Bool
  | .map, some (.ref (.mapping _ _)) | .fixed, some (.ref (.fixed _ _)) => false
  | _, some _ => true
  | _, none => false

/-- Where `t` returns, it returns an integer. -/
def Facts.isInt (F : Facts) : LTerm → Bool
  | .lit (.int _) | .env _ | .len _ _ => true
  | .binop op _ _ _ => op.isArith
  | .unop op _ _ => op != .not
  | .var x => F.vars.any fun xp => xp.1 == x && xp.2 != .bool
  | .find .init q | .findP .init q =>
    match F.pty q with
    | some (.prim .uint) | some (.prim .int) => true
    | _ => false
  | .find (.arr op s P w) q | .findP (.arr op s P w) q => tyInt (F.slotTy (.arr op s P w) q)
  | .seq _ a | .zero a => F.isInt a
  | .ite _ a b | .orElse a b | .kite _ _ a b => F.isInt a && F.isInt b
  | _ => false

/-- Where `t` returns, it returns a `bool`. -/
def Facts.isBool (F : Facts) : LTerm → Bool
  | .lit (.bool _) | .has _ _ | .kmap _ _ _ | .sok _ | .pok _ => true
  | .binop op _ _ _ => !op.isArith
  | .unop op _ _ => op == .not
  | .var x => F.vars.any fun xp => xp.1 == x && xp.2 == .bool
  | .find .init q | .findP .init q => F.pty q == some (.prim .bool)
  | .find (.arr op s P w) q | .findP (.arr op s P w) q => tyBool (F.slotTy (.arr op s P w) q)
  | .seq _ a | .zero a => F.isBool a
  | .ite _ a b | .orElse a b | .kite _ _ a b => F.isBool a && F.isBool b
  | _ => false

theorem evalBinop_arith_int {op : BinOp} {p : PrimTy} {x : Value} {rb : Res Value} {v : Value}
    (hop : op.isArith = true) (h : evalBinop op p x rb = .ok v) : ∃ i, v = .int i := by
  unfold evalBinop at h
  split at h
  · simp only [BinOp.isArith, Bool.false_eq_true] at hop
  · simp only [BinOp.isArith, Bool.false_eq_true] at hop
  · obtain ⟨y, -, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨r, hr, h⟩ := Res.bind_eq_ok.1 h
    rw [checkArith_ok_eq h]
    cases op <;> simp only [BinOp.isArith, Bool.false_eq_true] at hop <;>
      simp only [applyBinOp, bind, Except.bind] at hr <;> (try split at hr) <;>
      (try split at hr) <;> (try split at hr) <;> (try split at hr) <;>
      first | (cases hr; exact ⟨_, rfl⟩) | cases hr

theorem evalBinop_notArith_bool {op : BinOp} {p : PrimTy} {x : Value} {rb : Res Value}
    {v : Value} (hop : op.isArith = false) (h : evalBinop op p x rb = .ok v) :
    ∃ b, v = .bool b := by
  unfold evalBinop at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · cases h; exact ⟨_, rfl⟩
  · obtain ⟨y, -, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨r, hr, h⟩ := Res.bind_eq_ok.1 h
    rw [checkArith_ok_eq h]
    cases op <;> simp only [BinOp.isArith, reduceCtorEq] at hop <;>
      simp only [applyBinOp, bind, Except.bind] at hr <;> (try split at hr) <;>
      (try split at hr) <;> (try split at hr) <;> (try split at hr) <;>
      first | (cases hr; exact ⟨_, rfl⟩) | cases hr

theorem canonB_uint {v : SVal} (h : v.canonB (.prim .uint) = true) : ∃ i, v = SVal.int i := by
  match v, h with
  | SVal.int i, _ => exact ⟨i, rfl⟩

theorem canonB_int {v : SVal} (h : v.canonB (.prim .int) = true) : ∃ i, v = SVal.int i := by
  match v, h with
  | SVal.int i, _ => exact ⟨i, rfl⟩

theorem canonB_bool {v : SVal} (h : v.canonB (.prim .bool) = true) : ∃ b, v = SVal.bool b := by
  match v, h with
  | SVal.bool b, _ => exact ⟨b, rfl⟩

theorem canonB_prim {v : SVal} {p : PrimTy} (h : v.canonB (.prim p) = true) :
    ∃ w, v.asValue = .ok w := by
  cases p with
  | uint => obtain ⟨i, rfl⟩ := canonB_uint h; exact ⟨_, rfl⟩
  | int => obtain ⟨i, rfl⟩ := canonB_int h; exact ⟨_, rfl⟩
  | bool => obtain ⟨b, rfl⟩ := canonB_bool h; exact ⟨_, rfl⟩

/-- The read of a typed path in the initial storage: what it finds. -/
theorem Facts.read_init {σ : State} {F : Facts} (hF : F.Ok σ) {q : LPath} {T : Ty}
    (ht : F.pty q = some T) {v : Value} (hv : (LTerm.find .init q).eval σ = .ok v ∨
      (LTerm.findP .init q).eval σ = .ok v) :
    ∃ w : SVal, w.canonB T = true ∧ w.asValue = .ok v := by
  rcases hv with hv | hv
  · simp only [LTerm.eval, LStor.eval, Res.ok_bind] at hv
    obtain ⟨qs, hq, hv⟩ := Res.bind_eq_ok.1 hv
    obtain ⟨w, hw, hv⟩ := Res.bind_eq_ok.1 hv
    obtain ⟨w', hw', hc⟩ := F.pty_find hF ht hq
    rw [hw'] at hw; cases hw
    exact ⟨w, hc, hv⟩
  · simp only [LTerm.eval, LStor.eval, Res.ok_bind] at hv
    obtain ⟨qs, hq, hv⟩ := Res.bind_eq_ok.1 hv
    obtain ⟨w, hw, hv⟩ := Res.bind_eq_ok.1 hv
    obtain ⟨w', hw', hc⟩ := F.pty_find hF ht hq
    rw [SVal.find_of_findLive hw'] at hw; cases hw
    exact ⟨w, hc, hv⟩

theorem Facts.isInt_sound {σ : State} {F : Facts} (hF : F.Ok σ) :
    (t : LTerm) → F.isInt t = true → ∀ {v : Value}, t.eval σ = .ok v → ∃ i, v = .int i
  | .lit (.int _), _, _, h => by cases h; exact ⟨_, rfl⟩
  | .env _, _, _, h => by cases h; exact ⟨_, rfl⟩
  | .len s q, _, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨_, -, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨_, -, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨w, -, h⟩ := Res.bind_eq_ok.1 h
    cases w <;> simp only [Close.arrLen, reduceCtorEq] at h
    cases h; exact ⟨_, rfl⟩
  | .binop op p a b, hi, v, h => by
    simp only [Facts.isInt] at hi
    simp only [LTerm.eval] at h
    obtain ⟨x, -, h⟩ := Res.bind_eq_ok.1 h
    exact evalBinop_arith_int hi h
  | .unop op p a, hi, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨x, -, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hy, h⟩ := Res.bind_eq_ok.1 h
    cases op with
    | not => simp only [isInt, bne_self_eq_false, Bool.false_eq_true] at hi
    | neg =>
      simp only [applyUnOp, bind, Except.bind] at hy
      split at hy
      · cases hy
      · cases hy
        unfold unopCheck at h
        split at h
        · exact ⟨_, (checkArith_ok_eq h)⟩
        · cases h; exact ⟨_, rfl⟩
    | bnot =>
      simp only [applyUnOp, bind, Except.bind] at hy
      split at hy
      · cases hy
      · cases hy
        simp only [unopCheck, pure, Except.pure] at h
        cases h; exact ⟨_, rfl⟩
  | .var x, hi, v, h => by
    simp only [Facts.isInt, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
      ne_eq] at hi
    obtain ⟨⟨y, p⟩, hm, rfl, hp⟩ := hi
    obtain ⟨w, hw, ha⟩ := hF.2.2.2.2.1 _ hm
    rw [hw] at h; cases h
    cases p <;> cases v <;> simp_all only [not_true_eq_false, reduceCtorEq, not_false_eq_true,
        PrimTy.admits, PrimVal.int.injEq, exists_eq']
  | .find .init q, hi, v, h | .findP .init q, hi, v, h => by
    simp only [Facts.isInt] at hi
    have hv : (LTerm.find .init q).eval σ = .ok v ∨ (LTerm.findP .init q).eval σ = .ok v := by
      first | exact .inl h | exact .inr h
    split at hi
    · rename_i ht
      obtain ⟨w, hc, hw⟩ := F.read_init hF ht hv
      obtain ⟨i, rfl⟩ := canonB_uint hc; cases hw; exact ⟨i, rfl⟩
    · rename_i ht
      obtain ⟨w, hc, hw⟩ := F.read_init hF ht hv
      obtain ⟨i, rfl⟩ := canonB_int hc; cases hw; exact ⟨i, rfl⟩
    · cases hi
  | .find (.save ..) _, hi, _, _ | .find (.del ..) _, hi, _, _
  | .findP (.save ..) _, hi, _, _ | .findP (.del ..) _, hi, _, _ => by simp only [isInt,
      Bool.false_eq_true] at hi
  | .find (.arr op s P w) q, hi, v, h => by
    simp only [Facts.isInt] at hi
    cases ht : F.slotTy (.arr op s P w) q with
    | none => simp only [ht, tyInt, Bool.false_eq_true] at hi
    | some T =>
      simp only [LTerm.eval] at h
      obtain ⟨w', hc, hw⟩ := F.slot_read hF ht h
      rw [ht] at hi
      match T, hi with
      | .prim .uint, _ => obtain ⟨i, rfl⟩ := canonB_uint hc; cases hw; exact ⟨i, rfl⟩
      | .prim .int, _ => obtain ⟨i, rfl⟩ := canonB_int hc; cases hw; exact ⟨i, rfl⟩
  | .findP (.arr op s P w) q, hi, v, h => by
    simp only [Facts.isInt] at hi
    cases ht : F.slotTy (.arr op s P w) q with
    | none => simp only [ht, tyInt, Bool.false_eq_true] at hi
    | some T =>
      simp only [LTerm.eval] at h
      obtain ⟨w', hc, hw⟩ := F.slot_readP hF ht h
      rw [ht] at hi
      match T, hi with
      | .prim .uint, _ => obtain ⟨i, rfl⟩ := canonB_uint hc; cases hw; exact ⟨i, rfl⟩
      | .prim .int, _ => obtain ⟨i, rfl⟩ := canonB_int hc; cases hw; exact ⟨i, rfl⟩
  | .seq d a, hi, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨_, -, h⟩ := Res.bind_eq_ok.1 h
    exact Facts.isInt_sound hF a hi h
  | .zero a, hi, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨x, hx, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨i, rfl⟩ := Facts.isInt_sound hF a hi hx
    cases h; exact ⟨0, rfl⟩
  | .ite c a b, hi, v, h => by
    simp only [Facts.isInt, Bool.and_eq_true] at hi
    simp only [LTerm.eval] at h
    obtain ⟨x, -, h⟩ := Res.bind_eq_ok.1 h
    unfold pickBranch at h
    split at h
    · exact Facts.isInt_sound hF a hi.1 h
    · exact Facts.isInt_sound hF b hi.2 h
    · cases h
  | .orElse a b, hi, v, h => by
    simp only [Facts.isInt, Bool.and_eq_true] at hi
    simp only [LTerm.eval] at h
    unfold orElseR at h
    split at h
    · rename_i heq; cases h; exact Facts.isInt_sound hF a hi.1 heq
    · exact Facts.isInt_sound hF b hi.2 h
  | .kite a b x y, hi, v, h => by
    simp only [Facts.isInt, Bool.and_eq_true] at hi
    simp only [LTerm.eval] at h
    obtain ⟨_, -, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨_, -, h⟩ := Res.bind_eq_ok.1 h
    split at h
    · exact Facts.isInt_sound hF x hi.1 h
    · exact Facts.isInt_sound hF y hi.2 h
  | .lit (.bool _), hi, _, _ | .err, hi, _, _ | .has .., hi, _, _ | .kmap .., hi, _, _
  | .sok _, hi, _, _ | .pok _, hi, _, _ => by simp only [isInt, Bool.false_eq_true] at hi

theorem Facts.isBool_sound {σ : State} {F : Facts} (hF : F.Ok σ) :
    (t : LTerm) → F.isBool t = true → ∀ {v : Value}, t.eval σ = .ok v → ∃ b, v = .bool b
  | .lit (.bool _), _, _, h => by cases h; exact ⟨_, rfl⟩
  | .has s q, _, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨_, -, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨_, -, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨w, -, h⟩ := Res.bind_eq_ok.1 h
    cases h; exact ⟨_, rfl⟩
  | .kmap sh s q, _, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨_, -, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨_, -, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨w, -, h⟩ := Res.bind_eq_ok.1 h
    cases sh <;> simp only [KShape.test, kmapF] at h <;> split at h <;>
      first | (cases h; exact ⟨_, rfl⟩) | cases h
  | .sok s, _, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨_, -, h⟩ := Res.bind_eq_ok.1 h
    cases h; exact ⟨_, rfl⟩
  | .pok q, _, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨_, -, h⟩ := Res.bind_eq_ok.1 h
    cases h; exact ⟨_, rfl⟩
  | .binop op p a b, hi, v, h => by
    simp only [Facts.isBool, Bool.not_eq_true'] at hi
    simp only [LTerm.eval] at h
    obtain ⟨x, -, h⟩ := Res.bind_eq_ok.1 h
    exact evalBinop_notArith_bool hi h
  | .unop op p a, hi, v, h => by
    simp only [Facts.isBool, beq_iff_eq] at hi
    subst hi
    simp only [LTerm.eval] at h
    obtain ⟨x, -, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨y, hy, h⟩ := Res.bind_eq_ok.1 h
    simp only [applyUnOp, bind, Except.bind] at hy
    split at hy
    · cases hy
    · cases hy
      simp only [unopCheck, pure, Except.pure] at h
      cases h; exact ⟨_, rfl⟩
  | .var x, hi, v, h => by
    simp only [Facts.isBool, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hi
    obtain ⟨⟨y, p⟩, hm, rfl, rfl⟩ := hi
    obtain ⟨w, hw, ha⟩ := hF.2.2.2.2.1 _ hm
    rw [hw] at h; cases h
    cases v <;> simp_all only [PrimTy.admits, PrimVal.bool.injEq, exists_eq']
  | .find .init q, hi, v, h | .findP .init q, hi, v, h => by
    simp only [Facts.isBool, beq_iff_eq] at hi
    have hv : (LTerm.find .init q).eval σ = .ok v ∨ (LTerm.findP .init q).eval σ = .ok v := by
      first | exact .inl h | exact .inr h
    obtain ⟨w, hc, hw⟩ := F.read_init hF hi hv
    obtain ⟨b, rfl⟩ := canonB_bool hc; cases hw; exact ⟨b, rfl⟩
  | .find (.save ..) _, hi, _, _ | .find (.del ..) _, hi, _, _
  | .findP (.save ..) _, hi, _, _ | .findP (.del ..) _, hi, _, _ => by simp only [isBool,
      Bool.false_eq_true] at hi
  | .find (.arr op s P w) q, hi, v, h => by
    simp only [Facts.isBool] at hi
    cases ht : F.slotTy (.arr op s P w) q with
    | none => simp only [ht, tyBool, Bool.false_eq_true] at hi
    | some T =>
      simp only [LTerm.eval] at h
      obtain ⟨w', hc, hw⟩ := F.slot_read hF ht h
      rw [ht] at hi
      match T, hi with
      | .prim .bool, _ => obtain ⟨b, rfl⟩ := canonB_bool hc; cases hw; exact ⟨b, rfl⟩
  | .findP (.arr op s P w) q, hi, v, h => by
    simp only [Facts.isBool] at hi
    cases ht : F.slotTy (.arr op s P w) q with
    | none => simp only [ht, tyBool, Bool.false_eq_true] at hi
    | some T =>
      simp only [LTerm.eval] at h
      obtain ⟨w', hc, hw⟩ := F.slot_readP hF ht h
      rw [ht] at hi
      match T, hi with
      | .prim .bool, _ => obtain ⟨b, rfl⟩ := canonB_bool hc; cases hw; exact ⟨b, rfl⟩
  | .seq d a, hi, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨_, -, h⟩ := Res.bind_eq_ok.1 h
    exact Facts.isBool_sound hF a hi h
  | .zero a, hi, v, h => by
    simp only [LTerm.eval] at h
    obtain ⟨x, hx, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨b, rfl⟩ := Facts.isBool_sound hF a hi hx
    cases h; exact ⟨false, rfl⟩
  | .ite c a b, hi, v, h => by
    simp only [Facts.isBool, Bool.and_eq_true] at hi
    simp only [LTerm.eval] at h
    obtain ⟨x, -, h⟩ := Res.bind_eq_ok.1 h
    unfold pickBranch at h
    split at h
    · exact Facts.isBool_sound hF a hi.1 h
    · exact Facts.isBool_sound hF b hi.2 h
    · cases h
  | .orElse a b, hi, v, h => by
    simp only [Facts.isBool, Bool.and_eq_true] at hi
    simp only [LTerm.eval] at h
    unfold orElseR at h
    split at h
    · rename_i heq; cases h; exact Facts.isBool_sound hF a hi.1 heq
    · exact Facts.isBool_sound hF b hi.2 h
  | .kite a b x y, hi, v, h => by
    simp only [Facts.isBool, Bool.and_eq_true] at hi
    simp only [LTerm.eval] at h
    obtain ⟨_, -, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨_, -, h⟩ := Res.bind_eq_ok.1 h
    split at h
    · exact Facts.isBool_sound hF x hi.1 h
    · exact Facts.isBool_sound hF y hi.2 h
  | .lit (.int _), hi, _, _ | .err, hi, _, _ | .env _, hi, _, _ | .len .., hi, _, _ => by
    simp only [isBool, Bool.false_eq_true] at hi

/-! ## Intervals -/

/-- The interval of a local's type. -/
def _root_.Solidity.PrimTy.range? : PrimTy → Option (Int × Int)
  | .uint => some (0, uintBound - 1)
  | .int => some (-intBound, intBound - 1)
  | .bool => none

/-- The interval of `a ⊕ b` from its operands': `+` and `-`. -/
def rangeOp : BinOp → Option (Int × Int) → Option (Int × Int) → Option (Int × Int)
  | .add, some (la, ha), some (lb, hb) => some (la + lb, ha + hb)
  | .sub, some (la, ha), some (lb, hb) => some (la - hb, ha - lb)
  | _, _, _ => none

/-- The interval the premises give `t`. -/
def Facts.bndOf (F : Facts) (t : LTerm) : Option (Int × Int) :=
  (F.bnds.find? (·.1 == t)).map (·.2)

/-- An interval `t` lies in where it returns an integer: a literal's, one
the premises give, a local's type's, a sum's or a difference's. -/
def Facts.range (F : Facts) : LTerm → Option (Int × Int)
  | .lit (.int i) => some (i, i)
  | t@(.var x) =>
    match F.bndOf t with
    | some r => some r
    | none => (F.vars.find? (·.1 == x)).bind (·.2.range?)
  | t@(.seq _ a) =>
    match F.bndOf t with
    | some r => some r
    | none => F.range a
  | t@(.binop op _ a b) =>
    match F.bndOf t with
    | some r => some r
    | none => rangeOp op (F.range a) (F.range b)
  | t => F.bndOf t

theorem Facts.bndOf_sound {σ : State} {F : Facts} (hF : F.Ok σ) {t : LTerm} {l h : Int}
    (hb : F.bndOf t = some (l, h)) {i : Int} (hi : t.eval σ = .ok (.int i)) : l ≤ i ∧ i ≤ h := by
  simp only [Facts.bndOf, Option.map_eq_some_iff] at hb
  obtain ⟨b, hf, hbe⟩ := hb
  have hm := List.mem_of_find?_eq_some hf
  have he : b.1 = t := by simpa only [beq_iff_eq] using List.find?_some hf
  have := hF.2.2.2.2.2 b hm i (he ▸ hi)
  rw [hbe] at this
  exact this

theorem Facts.range_sound {σ : State} {F : Facts} (hF : F.Ok σ) :
    (t : LTerm) → ∀ {l h i : Int}, F.range t = some (l, h) → t.eval σ = .ok (.int i) →
      l ≤ i ∧ i ≤ h
  | .lit (.int n), l, h, i, hr, hi => by
    simp only [Facts.range, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    cases hi; exact ⟨Int.le_refl _, Int.le_refl _⟩
  | .var x, l, h, i, hr, hi => by
    simp only [Facts.range] at hr
    split at hr
    · rename_i hb; rw [hr] at hb; exact F.bndOf_sound hF hb hi
    · simp only [Option.bind_eq_some_iff] at hr
      obtain ⟨xp, hf, hr⟩ := hr
      have he : xp.1 = x := by simpa only [beq_iff_eq] using List.find?_some hf
      obtain ⟨w, hw, ha⟩ := hF.2.2.2.2.1 xp (List.mem_of_find?_eq_some hf)
      rw [he, hi] at hw
      cases hw
      revert ha hr
      cases xp.2 <;> simp only [PrimTy.range?, PrimTy.admits, Option.some.injEq,
        Prod.mk.injEq, reduceCtorEq, false_imp_iff] <;> intro ha hr <;> omega
  | .seq d a, l, h, i, hr, hi => by
    simp only [Facts.range] at hr
    split at hr
    · rename_i hb; rw [hr] at hb; exact F.bndOf_sound hF hb hi
    · simp only [LTerm.eval] at hi
      obtain ⟨_, -, ha⟩ := Res.bind_eq_ok.1 hi
      exact Facts.range_sound hF a hr ha
  | .binop op p a b, l, h, i, hr, hi => by
    simp only [Facts.range] at hr
    split at hr
    · rename_i hb; rw [hr] at hb; exact F.bndOf_sound hF hb hi
    · simp only [LTerm.eval] at hi
      obtain ⟨x, hx, hv⟩ := Res.bind_eq_ok.1 hi
      cases hra : F.range a with
      | none => cases op <;> simp only [hra, rangeOp, reduceCtorEq] at hr
      | some ra =>
        cases hrb : F.range b with
        | none => cases op <;> simp only [hra, hrb, rangeOp, reduceCtorEq] at hr
        | some rb =>
          obtain ⟨la, ha'⟩ := ra
          obtain ⟨lb, hb'⟩ := rb
          have hop : op = .add ∨ op = .sub := by
            cases op <;> simp only [hra, hrb, rangeOp, reduceCtorEq] at hr <;>
              simp only [reduceCtorEq, or_false, or_true]
          obtain ⟨y, hy⟩ := evalBinop_right hv (by
            rcases hop with rfl | rfl <;> simp only [reduceCtorEq, or_self, not_false_eq_true])
          rw [hy] at hv
          obtain ⟨i', j', hxi, hyj, hvi⟩ := evalBinop_addsub hop hv
          subst hxi hyj
          have h1 := Facts.range_sound hF a hra hx
          have h2 := Facts.range_sound hF b hrb hy
          rcases hop with rfl | rfl <;>
            simp only [hra, hrb, rangeOp, Option.some.injEq, Prod.mk.injEq, ↓reduceIte,
              reduceCtorEq, PrimVal.int.injEq] at hr hvi <;> omega
  | .lit (.bool _), _, _, _, hr, hi | .err, _, _, _, hr, hi | .env _, _, _, _, hr, hi
  | .unop .., _, _, _, hr, hi | .ite .., _, _, _, hr, hi | .find .., _, _, _, hr, hi
  | .has .., _, _, _, hr, hi | .kmap .., _, _, _, hr, hi | .len .., _, _, _, hr, hi
  | .sok _, _, _, _, hr, hi | .pok _, _, _, _, hr, hi | .orElse .., _, _, _, hr, hi
  | .kite .., _, _, _, hr, hi | .zero _, _, _, _, hr, hi | .findP .., _, _, _, hr, hi =>
    F.bndOf_sound hF hr hi

/-! ## What returns -/

/-- A bound below where no interval is known: a length is at least `0`, a
sum at least the sum of its operands' bounds (`values.length + 1 > 0`). -/
def Facts.lo (F : Facts) : LTerm → Option Int
  | .len _ _ => some 0
  | t@(.binop .add _ a b) =>
    match F.range t with
    | some (l, _) => some l
    | none => (F.lo a).bind fun x => (F.lo b).map (x + ·)
  | t@(.seq _ a) =>
    match F.range t with
    | some (l, _) => some l
    | none => F.lo a
  | t => (F.range t).map (·.1)

theorem evalBinop_add_int {p : PrimTy} {x : Value} {rb : Res Value} {i : Int}
    (h : evalBinop .add p x rb = .ok (.int i)) :
    ∃ a b, x = .int a ∧ rb = .ok (.int b) ∧ i = a + b := by
  cases rb with
  | error e => cases x <;> simp only [evalBinop, bind, Except.bind, reduceCtorEq] at h
  | ok y =>
    cases x <;> cases y <;>
      simp only [evalBinop, applyBinOp, Value.asInt, bind, Except.bind, reduceCtorEq] at h
    rename_i a b
    refine ⟨a, b, rfl, rfl, ?_⟩
    generalize BinOp.add.retTy (Ty.prim p) = ty at h
    cases ty with
    | prim q =>
      cases q <;> simp only [checkArith] at h
      · cases h; rfl
      · split at h
        · cases h; rfl
        · cases h
      · split at h
        · cases h; rfl
        · cases h
    | ref _ => simp only [checkArith] at h; cases h; rfl

theorem Facts.lo_sound {σ : State} {F : Facts} (hF : F.Ok σ) :
    (t : LTerm) → ∀ {l i : Int}, F.lo t = some l → t.eval σ = .ok (.int i) → l ≤ i
  | .len s q, l, i, hl, hi => by
    simp only [Facts.lo, Option.some.injEq] at hl
    subst hl
    simp only [LTerm.eval] at hi
    obtain ⟨_, -, hi⟩ := Res.bind_eq_ok.1 hi
    obtain ⟨_, -, hi⟩ := Res.bind_eq_ok.1 hi
    obtain ⟨c, -, hi⟩ := Res.bind_eq_ok.1 hi
    obtain ⟨es, _, _, -, he⟩ := Close.arrLen_eq_ok.1 hi
    cases he
    omega
  | .binop op p a b, l, i, hl, hi => by
    cases op
    case add =>
      simp only [Facts.lo] at hl
      split at hl
      · rename_i l' h' hr
        cases hl
        exact (F.range_sound hF _ hr hi).1
      · obtain ⟨x, hx, hl⟩ := Option.bind_eq_some_iff.1 hl
        obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hl
        simp only [LTerm.eval] at hi
        obtain ⟨va, ha, hi⟩ := Res.bind_eq_ok.1 hi
        obtain ⟨ia, ib, rfl, hb, rfl⟩ := evalBinop_add_int hi
        have := Facts.lo_sound hF a hx ha
        have := Facts.lo_sound hF b hy hb
        omega
    all_goals
      simp only [Facts.lo] at hl
      obtain ⟨⟨l', h'⟩, hr, rfl⟩ := Option.map_eq_some_iff.1 hl
      exact (F.range_sound hF _ hr hi).1
  | .seq d a, l, i, hl, hi => by
    simp only [Facts.lo] at hl
    split at hl
    · rename_i l' h' hr
      cases hl
      exact (F.range_sound hF _ hr hi).1
    · simp only [LTerm.eval] at hi
      obtain ⟨_, -, hi⟩ := Res.bind_eq_ok.1 hi
      exact Facts.lo_sound hF a hl hi
  | .lit _, l, i, hl, hi | .var _, l, i, hl, hi | .err, l, i, hl, hi | .env _, l, i, hl, hi
  | .unop .., l, i, hl, hi | .ite .., l, i, hl, hi | .find .., l, i, hl, hi
  | .has .., l, i, hl, hi | .kmap .., l, i, hl, hi | .sok _, l, i, hl, hi
  | .pok _, l, i, hl, hi | .orElse .., l, i, hl, hi | .kite .., l, i, hl, hi
  | .zero _, l, i, hl, hi | .findP .., l, i, hl, hi => by
    simp only [Facts.lo] at hl
    obtain ⟨⟨l', h'⟩, hr, rfl⟩ := Option.map_eq_some_iff.1 hl
    exact (F.range_sound hF _ hr hi).1

/-- A literal a term keeps is what it returns. -/
theorem lit_of_keeps {σ : State} {t u : LTerm} {w v : Value} (hk : Keeps σ t u)
    (hn : u = .lit w) (hv : t.eval σ = .ok v) : v = w := by
  have h := hk v hv
  rw [hn] at h
  simp only [LTerm.eval, Except.ok.injEq] at h
  exact h.symm

/-- The run returned. -/
def resOk : Res Value → Bool
  | .ok _ => true
  | .error _ => false

theorem resOk_iff {r : Res Value} : resOk r = true ↔ ∃ v, r = .ok v := by
  cases r <;> simp only [resOk, Bool.false_eq_true, reduceCtorEq, exists_false, Except.ok.injEq,
      exists_eq']

/-- The storage is the initial one. -/
def LStor.isInit : LStor → Bool
  | .init => true
  | _ => false

/-- A premise shows `a' ⊕ b'` returns, its operands with the normal forms of
`a` and `b`: `{ r := x + 1 }` under the box, against `x + 1` later. -/
def Facts.knownOp (F : Facts) (N : LTerm → LTerm) (op : BinOp) (p : PrimTy) (a b : LTerm) : Bool :=
  F.known.any fun
    | .binop op' p' a' b' => op' == op && p' == p && N a' == N a && N b' == N b
    | _ => false

theorem Facts.knownOp_sound {σ : State} {F : Facts} (hF : F.Ok σ) {N : LTerm → LTerm}
    (hN : ∀ t, Keeps σ t (N t)) {op : BinOp} {p : PrimTy} {a b : LTerm}
    (h : F.knownOp N op p a b = true) {x y : Value} (ha : a.eval σ = .ok x)
    (hb : b.eval σ = .ok y) : ∃ v, evalBinop op p x (.ok y) = .ok v := by
  simp only [Facts.knownOp, List.any_eq_true] at h
  obtain ⟨k, hk, hc⟩ := h
  split at hc
  · rename_i op' p' a' b'
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨rfl, rfl⟩, hna⟩, hnb⟩ := hc
    obtain ⟨r, hr⟩ := hF.1 _ hk
    simp only [LTerm.eval] at hr
    obtain ⟨x', hx', hr⟩ := Res.bind_eq_ok.1 hr
    have h1 := hN a' x' hx'
    have h2 := hN a x ha
    rw [hna, h2] at h1
    cases h1
    exact ⟨r, evalBinop_congr hr fun w hw => by
      have h3 := hN b' w hw
      have h4 := hN b y hb
      rw [hnb, h4] at h3
      cases h3; rfl⟩
  · cases hc

/-- `n` is in the range of the type `p`; any integer at `bool`, which
`checkArith` lets through. -/
def inTy (p : PrimTy) (n : Int) : Bool :=
  match p with
  | .uint => decide (0 ≤ n ∧ n < uintBound)
  | .int => decide (-intBound ≤ n ∧ n < intBound)
  | .bool => true

/-- `a ⊕ b` stays in its type's range, by the operands' intervals: KeY's
`inEqSimp` bounds on a checked `+` or `-`. -/
def Facts.fitsArith (F : Facts) (op : BinOp) (p : PrimTy) (a b : LTerm) : Bool :=
  F.isInt a && F.isInt b &&
    ((p == .bool && (op == .add || op == .sub)) ||
    match rangeOp op (F.range a) (F.range b) with
    | some (l, h) => inTy p l && inTy p h
    | none => false)

theorem Facts.fitsArith_sound {σ : State} {F : Facts} (hF : F.Ok σ) {op : BinOp} {p : PrimTy}
    {a b : LTerm} (h : F.fitsArith op p a b = true) {x y : Value} (ha : a.eval σ = .ok x)
    (hb : b.eval σ = .ok y) : ∃ v, evalBinop op p x (.ok y) = .ok v := by
  simp only [Facts.fitsArith, Bool.and_eq_true] at h
  obtain ⟨⟨hia, hib⟩, h⟩ := h
  obtain ⟨i, rfl⟩ := F.isInt_sound hF a hia ha
  obtain ⟨j, rfl⟩ := F.isInt_sound hF b hib hb
  -- the unchecked `+` and `-` a length is counted with (`lenSucc`)
  by_cases hu : (p == .bool && (op == .add || op == .sub)) = true
  · simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hu
    obtain ⟨rfl, rfl | rfl⟩ := hu <;> exact ⟨_, rfl⟩
  rw [Bool.eq_false_iff.2 hu, Bool.false_or] at h
  split at h
  · rename_i l u hr
    simp only [Bool.and_eq_true] at h
    cases hra : F.range a with
    | none => rw [hra] at hr; cases op <;> simp only [rangeOp, reduceCtorEq] at hr
    | some ra =>
      cases hrb : F.range b with
      | none => rw [hra, hrb] at hr; cases op <;> simp only [rangeOp, reduceCtorEq] at hr
      | some rb =>
        obtain ⟨la, ua⟩ := ra
        obtain ⟨lb, ub⟩ := rb
        have h1 := F.range_sound hF a hra ha
        have h2 := F.range_sound hF b hrb hb
        rw [hra, hrb] at hr
        cases op <;> simp only [rangeOp, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hr <;>
          obtain ⟨rfl, rfl⟩ := hr <;>
          cases p <;> simp only [inTy, decide_eq_true_eq] at h <;>
          simp only [evalBinop, applyBinOp, Value.asInt, bind, Except.bind, checkArith,
            BinOp.retTy, BinOp.isArith, ↓reduceIte] <;>
          first
            | exact ⟨_, rfl⟩
            | (rw [if_pos (by omega)]; exact ⟨_, rfl⟩)
  · cases h

/-- What `a ⊕ b` needs to return, once `a` returns (`rb`: `b` returns):
operands of the kinds the operator takes, or literal operands it accepts. -/
def Facts.binRets (F : Facts) (N : LTerm → LTerm) (op : BinOp) (p : PrimTy) (a b : LTerm) (rb :
    Bool) : Bool :=
  match op with
  | .and => N a == .lit (.bool false) || (F.isBool a && rb && F.isBool b)
  | .or => N a == .lit (.bool true) || (F.isBool a && rb && F.isBool b)
  | .eqB | .neB => rb
  | .lt | .gt | .le | .ge => F.isInt a && rb && F.isInt b
  | _ => rb &&
    ((match N a, N b with
      | .lit x, .lit y => resOk (evalBinop op p x (.ok y))
      | _, _ => false) || F.knownOp N op p a b || F.fitsArith op p a b)

/-- What `⊖ a` needs to return, once `a` returns. -/
def Facts.unRets (F : Facts) (N : LTerm → LTerm) (op : UnOp) (p : PrimTy) (a : LTerm) : Bool :=
  match op with
  | .not => F.isBool a
  | .bnot => F.isInt a
  | .neg => (p != .int && F.isInt a) ||
    match N a with
    | .lit x => resOk (applyUnOp .neg x >>= unopCheck .neg p)
    | _ => false

/-- The layout types the path as a word. -/
def Facts.isPrimPath (F : Facts) (q : LPath) : Bool :=
  match F.pty q with
  | some (.prim _) => true
  | _ => false

/-- The layout types the path as a mapping (a fixed-size array). -/
def Facts.shapeIs (F : Facts) (sh : KShape) (q : LPath) : Bool :=
  match sh, F.pty q with
  | .map, some (.ref (.mapping _ _)) => true
  | .fixed, some (.ref (.fixed _ _)) => true
  | _, _ => false

/-- The layout types the path as an array. -/
def Facts.isArrPath (F : Facts) (q : LPath) : Bool :=
  match F.pty q with
  | some (.ref (.array _)) | some (.ref (.fixed _ _)) => true
  | _ => false

mutual

/-- `t` returns wherever the facts hold: what `LTerm.rets` shows from the
premises, or a literal, a guarded term whose guard and value do, an
operation on operands that do and that it accepts (`binRets`), a
conditional on a condition that does, a read of the initial storage at a
path the layout types. -/
def Facts.retsW (F : Facts) (N : LTerm → LTerm) : LTerm → Bool
  | .lit _ => true
  | .env _ => true
  | .err => false
  | t@(.var x) => t.known F.known F.ne || F.vars.any (·.1 == x)
  | t@(.seq d a) => t.known F.known F.ne || (F.retsW N d && F.retsW N a)
  | t@(.zero a) => t.known F.known F.ne || F.retsW N a
  | t@(.orElse a b) => t.known F.known F.ne || F.retsW N a || F.retsW N b
  | t@(.binop op p a b) => t.rets F.known F.ne || (F.retsW N a && F.binRets N op p a b (F.retsW N
      b))
  | t@(.unop op p a) => t.known F.known F.ne || (F.retsW N a && F.unRets N op p a)
  | t@(.ite c a b) => t.known F.known F.ne || (F.retsW N c &&
      match N c with
      | .lit (.bool true) => F.retsW N a
      | .lit (.bool false) => F.retsW N b
      | _ => F.isBool c && F.retsW N a && F.retsW N b)
  | t@(.kite a b x y) => t.rets F.known F.ne ||
      (F.retsW N a && F.isInt a && F.retsW N b && F.isInt b &&
        match N a, N b with
        | .lit (.int i), .lit (.int j) => if i = j then F.retsW N x else F.retsW N y
        | _, _ => F.retsW N x && F.retsW N y)
  | t@(.find s q) => t.known F.known F.ne || (s.isInit && F.keysRetW N q && F.isPrimPath q) ||
      (F.slotIn N s q && F.keysRetW N q && tyPrim (F.slotTy s q))
  | t@(.findP s q) => t.rets F.known F.ne || (s.isInit && F.keysRetW N q && F.isPrimPath q)
  | t@(.has s q) => t.known F.known F.ne || (s.isInit && F.keysRetW N q && (F.pty q).isSome) ||
      (F.slotIn N s q && F.keysRetW N q && (F.slotTy s q).isSome)
  | t@(.kmap sh s q) => t.known F.known F.ne || (s.isInit && F.keysRetW N q && F.shapeIs sh q) ||
      (F.slotIn N s q && F.keysRetW N q && tyShape sh (F.slotTy s q))
  | t@(.len s q) => t.known F.known F.ne || (s.isInit && F.keysRetW N q && F.isArrPath q)
  | t@(.sok _) => t.known F.known F.ne
  | t@(.pok q) => t.known F.known F.ne || F.keysRetW N q

/-- Every key of the path returns an integer. -/
def Facts.keysRetW (F : Facts) (N : LTerm → LTerm) : LPath → Bool
  | .root _ => true
  | .field q _ => F.keysRetW N q
  | .at q k => F.keysRetW N q && F.retsW N k && F.isInt k

end

theorem evalBinop_and_bool (p : PrimTy) (a b : Bool) :
    ∃ v, evalBinop .and p (.bool a) (.ok (.bool b)) = .ok v := by
  cases a <;> cases b <;> exact ⟨_, rfl⟩

theorem evalBinop_or_bool (p : PrimTy) (a b : Bool) :
    ∃ v, evalBinop .or p (.bool a) (.ok (.bool b)) = .ok v := by
  cases a <;> cases b <;> exact ⟨_, rfl⟩

theorem Facts.binRets_sound {σ : State} {F : Facts} (hF : F.Ok σ) {N : LTerm → LTerm}
    (hN : ∀ t, Keeps σ t (N t)) {op : BinOp} {p : PrimTy}
    {a b : LTerm} {rb : Bool} (h : F.binRets N op p a b rb = true) {x : Value}
    (ha : a.eval σ = .ok x) (hb : rb = true → Returns σ b) :
    ∃ v, evalBinop op p x (b.eval σ) = .ok v := by
  unfold Facts.binRets at h
  split at h
  · simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
    rcases h with h | ⟨⟨hba, hr⟩, hbb⟩
    · cases lit_of_keeps (hN _) h ha; exact ⟨_, rfl⟩
    · obtain ⟨xb, rfl⟩ := F.isBool_sound hF a hba ha
      obtain ⟨y, hy⟩ := hb hr
      obtain ⟨yb, rfl⟩ := F.isBool_sound hF b hbb hy
      rw [hy]; exact evalBinop_and_bool p xb yb
  · simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
    rcases h with h | ⟨⟨hba, hr⟩, hbb⟩
    · cases lit_of_keeps (hN _) h ha; exact ⟨_, rfl⟩
    · obtain ⟨xb, rfl⟩ := F.isBool_sound hF a hba ha
      obtain ⟨y, hy⟩ := hb hr
      obtain ⟨yb, rfl⟩ := F.isBool_sound hF b hbb hy
      rw [hy]; exact evalBinop_or_bool p xb yb
  all_goals first
    | (obtain ⟨y, hy⟩ := hb h; rw [hy]; cases x <;> exact ⟨_, rfl⟩)
    | (simp only [Bool.and_eq_true] at h
       obtain ⟨⟨hia, hr⟩, hib⟩ := h
       obtain ⟨i, rfl⟩ := F.isInt_sound hF a hia ha
       obtain ⟨y, hy⟩ := hb hr
       obtain ⟨j, rfl⟩ := F.isInt_sound hF b hib hy
       rw [hy]; exact ⟨_, rfl⟩)
    | (simp only [Bool.and_eq_true] at h
       obtain ⟨hr, h⟩ := h
       obtain ⟨y, hy⟩ := hb hr
       rw [hy]
       simp only [Bool.or_eq_true] at h
       rcases h with (h | h) | h
       · split at h
         · rename_i x' y' hx' hy'
           cases lit_of_keeps (hN _) hx' ha
           cases lit_of_keeps (hN _) hy' hy
           exact resOk_iff.1 h
         · cases h
       · exact F.knownOp_sound hF hN h ha hy
       · exact F.fitsArith_sound hF h ha hy)

theorem Facts.unRets_sound {σ : State} {F : Facts} (hF : F.Ok σ) {N : LTerm → LTerm}
    (hN : ∀ t, Keeps σ t (N t)) {op : UnOp} {p : PrimTy}
    {a : LTerm} (h : F.unRets N op p a = true) {x : Value} (ha : a.eval σ = .ok x) :
    ∃ v, (applyUnOp op x >>= unopCheck op p) = .ok v := by
  unfold Facts.unRets at h
  split at h
  · obtain ⟨b, rfl⟩ := F.isBool_sound hF a h ha
    exact ⟨_, rfl⟩
  · obtain ⟨i, rfl⟩ := F.isInt_sound hF a h ha
    exact ⟨_, rfl⟩
  · simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rcases h with ⟨hp, hi⟩ | h
    · obtain ⟨i, rfl⟩ := F.isInt_sound hF a hi ha
      cases p with
      | int => exact absurd rfl hp
      | uint | bool => exact ⟨_, rfl⟩
    · split at h
      · rename_i x' hx'
        cases lit_of_keeps (hN _) hx' ha
        exact resOk_iff.1 h
      · cases h

/-- A path the layout types and whose keys return resolves in the initial
storage, to a value canonical at its type. -/
theorem Facts.resolve {σ : State} {F : Facts} (hF : F.Ok σ) {q : LPath} {T : Ty}
    (hk : ∃ qs, q.eval σ = .ok qs) (ht : F.pty q = some T) :
    ∃ qs w, q.eval σ = .ok qs ∧ (SVal.struct σ.storage).findLive qs = .ok w ∧
      w.canonB T = true := by
  obtain ⟨qs, hq⟩ := hk
  obtain ⟨w, hw, hc⟩ := F.pty_find hF ht hq
  exact ⟨qs, w, hq, hw, hc⟩

mutual

/-- **What `Facts.rets` accepts returns.** -/
theorem Facts.retsW_sound {σ : State} {F : Facts} (hF : F.Ok σ) {N : LTerm → LTerm}
    (hN : ∀ t, Keeps σ t (N t)) :
    (t : LTerm) → F.retsW N t = true → Returns σ t
  | .lit _, _ => ⟨_, rfl⟩
  | .env _, _ => ⟨_, rfl⟩
  | .err, h => by simp only [retsW, Bool.false_eq_true] at h
  | .var x, h => by
    simp only [Facts.retsW, Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at h
    rcases h with h | ⟨xp, hm, rfl⟩
    · exact LTerm.known_returns hF.1 hF.2.1 _ h
    · obtain ⟨v, hv, -⟩ := hF.2.2.2.2.1 xp hm
      exact ⟨v, hv⟩
  | .seq d a, h => by
    simp only [Facts.retsW, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨hd, ha⟩
    · exact LTerm.known_returns hF.1 hF.2.1 _ h
    · obtain ⟨_, hd⟩ := Facts.retsW_sound hF hN d hd
      obtain ⟨v, ha⟩ := Facts.retsW_sound hF hN a ha
      exact ⟨v, by simp only [LTerm.eval, hd, Res.ok_bind, ha]⟩
  | .zero a, h => by
    simp only [Facts.retsW, Bool.or_eq_true] at h
    rcases h with h | ha
    · exact LTerm.known_returns hF.1 hF.2.1 _ h
    · obtain ⟨v, ha⟩ := Facts.retsW_sound hF hN a ha
      exact ⟨_, by simp only [LTerm.eval, ha, Res.ok_bind] <;> rfl⟩
  | .orElse a b, h => by
    simp only [Facts.retsW, Bool.or_eq_true] at h
    rcases h with (h | ha) | hb
    · exact LTerm.known_returns hF.1 hF.2.1 _ h
    · obtain ⟨v, ha⟩ := Facts.retsW_sound hF hN a ha
      exact ⟨v, by simp only [LTerm.eval, ha, orElseR]⟩
    · obtain ⟨v, hb⟩ := Facts.retsW_sound hF hN b hb
      simp only [Returns, LTerm.eval, orElseR]
      split
      · exact ⟨_, rfl⟩
      · exact ⟨v, hb⟩
  | .binop op p a b, h => by
    simp only [Facts.retsW, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨ha, hb⟩
    · exact LTerm.rets_returns hF.1 hF.2.1 _ h
    · obtain ⟨x, hx⟩ := Facts.retsW_sound hF hN a ha
      obtain ⟨v, hv⟩ := F.binRets_sound hF hN hb hx (fun hr => Facts.retsW_sound hF hN b hr)
      exact ⟨v, by simp only [LTerm.eval, hx, Res.ok_bind, hv]⟩
  | .unop op p a, h => by
    simp only [Facts.retsW, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨ha, hu⟩
    · exact LTerm.known_returns hF.1 hF.2.1 _ h
    · obtain ⟨x, hx⟩ := Facts.retsW_sound hF hN a ha
      obtain ⟨v, hv⟩ := F.unRets_sound hF hN hu hx
      exact ⟨v, by simp only [LTerm.eval, hx, Res.ok_bind, hv]⟩
  | .ite c a b, h => by
    simp only [Facts.retsW, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨hc, h⟩
    · exact LTerm.known_returns hF.1 hF.2.1 _ h
    · obtain ⟨cv, hcv⟩ := Facts.retsW_sound hF hN c hc
      simp only [Returns, LTerm.eval, hcv, Res.ok_bind]
      split at h
      · rename_i hn
        cases lit_of_keeps (hN _) hn hcv
        exact Facts.retsW_sound hF hN a h
      · rename_i hn
        cases lit_of_keeps (hN _) hn hcv
        exact Facts.retsW_sound hF hN b h
      · simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hb, ha⟩, hb'⟩ := h
        obtain ⟨bv, rfl⟩ := F.isBool_sound hF c hb hcv
        cases bv
        · exact Facts.retsW_sound hF hN _ hb'
        · exact Facts.retsW_sound hF hN _ ha
  | .kite a b x y, h => by
    simp only [Facts.retsW, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨⟨⟨⟨ha, hia⟩, hb⟩, hib⟩, h⟩
    · exact LTerm.rets_returns hF.1 hF.2.1 _ h
    · obtain ⟨av, hav⟩ := Facts.retsW_sound hF hN a ha
      obtain ⟨bv, hbv⟩ := Facts.retsW_sound hF hN b hb
      obtain ⟨i, rfl⟩ := F.isInt_sound hF a hia hav
      obtain ⟨j, rfl⟩ := F.isInt_sound hF b hib hbv
      simp only [Returns, LTerm.eval, hav, hbv, Res.ok_bind, Value.asInt]
      split at h
      · rename_i i' j' hi' hj'
        cases lit_of_keeps (hN _) hi' hav
        cases lit_of_keeps (hN _) hj' hbv
        split
        · rw [if_pos ‹_›] at h; exact Facts.retsW_sound hF hN x h
        · rw [if_neg ‹_›] at h; exact Facts.retsW_sound hF hN y h
      · simp only [Bool.and_eq_true] at h
        split
        · exact Facts.retsW_sound hF hN x h.1
        · exact Facts.retsW_sound hF hN y h.2
  | .find s q, h => by
    simp only [Facts.retsW, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (h | ⟨⟨hs, hk⟩, ht⟩) | ⟨⟨hin, hk⟩, ht⟩
    · exact LTerm.known_returns hF.1 hF.2.1 _ h
    rotate_left
    · cases hT : F.slotTy s q with
      | none => simp only [hT, tyPrim, Bool.false_eq_true] at ht
      | some T =>
        obtain ⟨v, qs, w, hv, hq, hw, hc⟩ :=
          F.slot_resolve hF hN hT hin (Facts.keysRetW_sound hF hN q hk)
        rw [hT] at ht
        match T, ht with
        | .prim _, _ =>
          obtain ⟨x, hx⟩ := canonB_prim hc
          exact ⟨x, by simp only [LTerm.eval, hv, hq, hw, Res.ok_bind, hx]⟩
    · cases s <;> simp only [LStor.isInit, Bool.false_eq_true] at hs
      unfold Facts.isPrimPath at ht
      split at ht
      · rename_i pt hpt
        obtain ⟨qs, w, hq, hw, hc⟩ := F.resolve hF (Facts.keysRetW_sound hF hN q hk) hpt
        obtain ⟨v, hv⟩ := canonB_prim hc
        exact ⟨v, by simp only [LTerm.eval, LStor.eval, hq, hw, Res.ok_bind, hv]⟩
      · cases ht
  | .findP s q, h => by
    simp only [Facts.retsW, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨⟨hs, hk⟩, ht⟩
    · exact LTerm.rets_returns hF.1 hF.2.1 _ h
    · cases s <;> simp only [LStor.isInit, Bool.false_eq_true] at hs
      unfold Facts.isPrimPath at ht
      split at ht
      · rename_i pt hpt
        obtain ⟨qs, w, hq, hw, hc⟩ := F.resolve hF (Facts.keysRetW_sound hF hN q hk) hpt
        obtain ⟨v, hv⟩ := canonB_prim hc
        exact ⟨v, by simp only [LTerm.eval, LStor.eval, hq, SVal.find_of_findLive hw,
          Res.ok_bind, hv]⟩
      · cases ht
  | .has s q, h => by
    simp only [Facts.retsW, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (h | ⟨⟨hs, hk⟩, ht⟩) | ⟨⟨hin, hk⟩, ht⟩
    · exact LTerm.known_returns hF.1 hF.2.1 _ h
    rotate_left
    · obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 ht
      obtain ⟨v, qs, w, hv, hq, hw, -⟩ :=
        F.slot_resolve hF hN hT hin (Facts.keysRetW_sound hF hN q hk)
      exact ⟨_, by simp only [LTerm.eval, hv, hq, hw, Res.ok_bind] <;> rfl⟩
    · cases s <;> simp only [LStor.isInit, Bool.false_eq_true] at hs
      obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 ht
      obtain ⟨qs, w, hq, hw, -⟩ := F.resolve hF (Facts.keysRetW_sound hF hN q hk) hT
      exact ⟨_, by simp only [LTerm.eval, LStor.eval, hq, hw, Res.ok_bind] <;> rfl⟩
  | .kmap sh s q, h => by
    simp only [Facts.retsW, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with (h | ⟨⟨hs, hk⟩, ht⟩) | ⟨⟨hin, hk⟩, ht⟩
    · exact LTerm.known_returns hF.1 hF.2.1 _ h
    rotate_left
    · cases hT : F.slotTy s q with
      | none => cases sh <;> simp only [hT, tyShape, Bool.false_eq_true] at ht
      | some T =>
        obtain ⟨v, qs, w, hv, hq, hw, hc⟩ :=
          F.slot_resolve hF hN hT hin (Facts.keysRetW_sound hF hN q hk)
        rw [hT] at ht
        match sh, T, ht with
        | .map, .ref (.mapping K V), _ =>
          match w, hc with
          | .map _ _, _ =>
            exact ⟨_, by simp only [LTerm.eval, hv, hq, hw, Res.ok_bind, KShape.test,
              kmapF, isMapV, if_true] <;> rfl⟩
        | .fixed, .ref (.fixed E n), _ =>
          match w, hc with
          | .array _ _ fx, hc =>
            simp only [SVal.canonB, Bool.and_eq_true] at hc
            obtain ⟨⟨⟨hfx, -⟩, -⟩, -⟩ := hc
            exact ⟨_, by simp only [LTerm.eval, hv, hq, hw, Res.ok_bind, KShape.test,
              isFixV, hfx, if_true] <;> rfl⟩
    · cases s <;> simp only [LStor.isInit, Bool.false_eq_true] at hs
      unfold Facts.shapeIs at ht
      split at ht
      · rename_i K V hT
        obtain ⟨qs, w, hq, hw, hc⟩ := F.resolve hF (Facts.keysRetW_sound hF hN q hk) hT
        match w, hc with
        | .map _ _, _ =>
          exact ⟨_, by simp only [LTerm.eval, LStor.eval, hq, hw, Res.ok_bind, KShape.test,
            kmapF, isMapV, if_true] <;> rfl⟩
      · rename_i E n hT
        obtain ⟨qs, w, hq, hw, hc⟩ := F.resolve hF (Facts.keysRetW_sound hF hN q hk) hT
        match w, hc with
        | .array _ _ fx, hc =>
          simp only [SVal.canonB, Bool.and_eq_true] at hc
          obtain ⟨⟨⟨hfx, -⟩, -⟩, -⟩ := hc
          exact ⟨_, by simp only [LTerm.eval, LStor.eval, hq, hw, Res.ok_bind, KShape.test,
            isFixV, hfx, if_true] <;> rfl⟩
      · cases ht
  | .len s q, h => by
    simp only [Facts.retsW, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨⟨hs, hk⟩, ht⟩
    · exact LTerm.known_returns hF.1 hF.2.1 _ h
    · cases s <;> simp only [LStor.isInit, Bool.false_eq_true] at hs
      unfold Facts.isArrPath at ht
      split at ht
      · rename_i E hT
        obtain ⟨qs, w, hq, hw, hc⟩ := F.resolve hF (Facts.keysRetW_sound hF hN q hk) hT
        match w, hc with
        | .array _ _ _, _ =>
          exact ⟨_, by simp only [LTerm.eval, LStor.eval, hq, hw, Res.ok_bind,
              Close.arrLen] <;> rfl⟩
      · rename_i E n hT
        obtain ⟨qs, w, hq, hw, hc⟩ := F.resolve hF (Facts.keysRetW_sound hF hN q hk) hT
        match w, hc with
        | .array _ _ _, _ =>
          exact ⟨_, by simp only [LTerm.eval, LStor.eval, hq, hw, Res.ok_bind,
              Close.arrLen] <;> rfl⟩
      · cases ht
  | .sok s, h => by
    simp only [Facts.retsW] at h
    exact LTerm.known_returns hF.1 hF.2.1 _ h
  | .pok q, h => by
    simp only [Facts.retsW, Bool.or_eq_true] at h
    rcases h with h | hk
    · exact LTerm.known_returns hF.1 hF.2.1 _ h
    · obtain ⟨qs, hq⟩ := Facts.keysRetW_sound hF hN q hk
      exact ⟨_, by simp only [LTerm.eval, hq, Res.ok_bind] <;> rfl⟩

/-- A path whose keys return integers evaluates. -/
theorem Facts.keysRetW_sound {σ : State} {F : Facts} (hF : F.Ok σ) {N : LTerm → LTerm}
    (hN : ∀ t, Keeps σ t (N t)) :
    (q : LPath) → F.keysRetW N q = true → ∃ qs, q.eval σ = .ok qs
  | .root _, _ => ⟨_, rfl⟩
  | .field q _, h => by
    simp only [Facts.keysRetW] at h
    obtain ⟨qs, hq⟩ := Facts.keysRetW_sound hF hN q h
    exact ⟨_, by simp only [LPath.eval, hq, Res.ok_bind] <;> rfl⟩
  | .at q k, h => by
    simp only [Facts.keysRetW, Bool.and_eq_true] at h
    obtain ⟨⟨hq, hk⟩, hi⟩ := h
    obtain ⟨qs, hq⟩ := Facts.keysRetW_sound hF hN q hq
    obtain ⟨v, hv⟩ := Facts.retsW_sound hF hN k hk
    obtain ⟨i, rfl⟩ := F.isInt_sound hF k hi hv
    exact ⟨_, by simp only [LPath.eval, hq, hv, Res.ok_bind, Value.asInt] <;> rfl⟩

end

/-- What the facts tell of a term's kind. -/
def Facts.kind (F : Facts) (t : LTerm) : Option Bool :=
  if F.isInt t then some true else if F.isBool t then some false else none

theorem Facts.kind_ok {σ : State} {F : Facts} (hF : F.Ok σ) : KindOk σ F.kind := by
  intro t v hv
  unfold Facts.kind
  refine ⟨fun h => ?_, fun h => ?_⟩
  · split at h
    · rename_i hi; exact F.isInt_sound hF t hi hv
    · split at h <;> cases h
  · split at h
    · cases h
    · split at h
      · rename_i hb; exact F.isBool_sound hF t hb hv
      · cases h

/-- The layout says the location at `q` is not of the shape `sh`. -/
def Facts.shapeNot (F : Facts) (sh : KShape) (q : LPath) : Bool :=
  match sh, F.pty q with
  | .map, some (.ref (.mapping _ _)) => false
  | .fixed, some (.ref (.fixed _ _)) => false
  | _, some _ => true
  | _, none => false

/-- Where the facts hold, `t` halts: a test of a shape the layout says is
not there (the guard of a read below a `delete`, `LStor.mapU`). -/
def Facts.halts (F : Facts) : LTerm → Bool
  | .err => true
  | .seq d a => F.halts d || F.halts a
  | .orElse a b => F.halts a && F.halts b
  | .kmap sh s q => (s.isInit && F.shapeNot sh q) || tyShapeNot sh (F.slotTy s q)
  | .zero a => F.halts a
  | _ => false

theorem canonB_map_ty {es : List (Int × SVal)} {d : SVal} {T : Ty}
    (h : (SVal.map es d).canonB T = true) : ∃ K V, T = .ref (.mapping K V) := by
  match T, h with
  | .ref (.mapping K V), _ => exact ⟨K, V, rfl⟩

theorem canonB_fixed_ty {es sh : List SVal} {T : Ty}
    (h : (SVal.array es sh true).canonB T = true) : ∃ E n, T = .ref (.fixed E n) := by
  match T, h with
  | .ref (.fixed E n), _ => exact ⟨E, n, rfl⟩
  | .ref (.array E), h => simp only [SVal.canonB, Bool.not_true, Bool.false_and,
      Bool.false_eq_true] at h

theorem Facts.halts_sound {σ : State} {F : Facts} (hF : F.Ok σ) :
    (t : LTerm) → F.halts t = true → ∀ v, t.eval σ ≠ .ok v
  | .err, _, _, h => nomatch h
  | .seq d a, hh, v, h => by
    simp only [Facts.halts, Bool.or_eq_true] at hh
    simp only [LTerm.eval] at h
    obtain ⟨x, hd, ha⟩ := Res.bind_eq_ok.1 h
    rcases hh with hh | hh
    · exact Facts.halts_sound hF d hh x hd
    · exact Facts.halts_sound hF a hh v ha
  | .orElse a b, hh, v, h => by
    simp only [Facts.halts, Bool.and_eq_true] at hh
    simp only [LTerm.eval] at h
    unfold orElseR at h
    split at h
    · rename_i w hw; exact Facts.halts_sound hF a hh.1 w hw
    · exact Facts.halts_sound hF b hh.2 v h
  | .zero a, hh, v, h => by
    simp only [Facts.halts] at hh
    simp only [LTerm.eval] at h
    obtain ⟨x, ha, -⟩ := Res.bind_eq_ok.1 h
    exact Facts.halts_sound hF a hh x ha
  | .kmap sh s q, hh, v, h => by
    simp only [Facts.halts, Bool.or_eq_true, Bool.and_eq_true] at hh
    rcases hh with ⟨hs, hn⟩ | hn
    rotate_left
    · cases hT : F.slotTy s q with
      | none => cases sh <;> simp only [hT, tyShapeNot, Bool.false_eq_true] at hn
      | some T =>
        simp only [LTerm.eval] at h
        obtain ⟨w, hc, hw⟩ := F.slot_read hF hT h
        rw [hT] at hn
        cases sh with
        | map =>
          simp only [KShape.test, kmapF] at hw
          split at hw
          · rename_i hm
            match w, hm, hc with
            | .map _ _, _, hc =>
              obtain ⟨K, V, rfl⟩ := canonB_map_ty hc
              simp only [tyShapeNot, Bool.false_eq_true] at hn
          · cases hw
        | fixed =>
          simp only [KShape.test] at hw
          split at hw
          · rename_i hm
            match w, hm, hc with
            | .array _ _ true, _, hc =>
              obtain ⟨E, n, rfl⟩ := canonB_fixed_ty hc
              simp only [tyShapeNot, Bool.false_eq_true] at hn
          · cases hw
    cases s <;> simp only [LStor.isInit, Bool.false_eq_true] at hs
    simp only [LTerm.eval, LStor.eval, Res.ok_bind] at h
    obtain ⟨qs, hq, h⟩ := Res.bind_eq_ok.1 h
    obtain ⟨w, hw, h⟩ := Res.bind_eq_ok.1 h
    cases hp : F.pty q with
    | none => cases sh <;> simp only [shapeNot, hp, Bool.false_eq_true] at hn
    | some T =>
      obtain ⟨w', hw', hc⟩ := F.pty_find hF hp hq
      rw [hw'] at hw; cases hw
      cases sh with
      | map =>
        simp only [KShape.test, kmapF] at h
        split at h
        · rename_i hm
          match w, hm, hc with
          | .map _ _, _, hc =>
            obtain ⟨K, V, rfl⟩ := canonB_map_ty hc
            simp only [shapeNot, hp, Bool.false_eq_true] at hn
        · cases h
      | fixed =>
        simp only [KShape.test] at h
        split at h
        · rename_i hm
          match w, hm, hc with
          | .array _ _ true, _, hc =>
            obtain ⟨E, n, rfl⟩ := canonB_fixed_ty hc
            simp only [shapeNot, hp, Bool.false_eq_true] at hn
        · cases h
  | .lit _, hh, _, _ | .var _, hh, _, _ | .binop .., hh, _, _ | .unop .., hh, _, _
  | .ite .., hh, _, _ | .find .., hh, _, _ | .has .., hh, _, _ | .len .., hh, _, _
  | .sok _, hh, _, _ | .pok _, hh, _, _ | .kite .., hh, _, _ | .env _, hh, _, _
  | .findP .., hh, _, _ => by simp only [halts, Bool.false_eq_true] at hh

/-- What the facts tell the simplifier: kinds, halting, and returning by
`retsW` over the untyped normal form. -/
def Facts.orc (F : Facts) : Orc :=
  { kind := F.kind, halts := F.halts, rets := F.retsW F.nf0, range := F.range, lo := F.lo }

theorem Facts.orc_ok {σ : State} {F : Facts} (hF : F.Ok σ) : F.orc.Ok σ :=
  ⟨F.kind_ok hF, fun t v h => F.halts_sound hF t h v,
    fun t h => F.retsW_sound hF (F.nf0_keeps hF) t h,
    fun t _ _ _ hr hi => F.range_sound hF t hr hi, fun t _ _ hl hi => F.lo_sound hF t hl hi⟩

/-- The normal form a term is compared by: its guards dropped (`LTerm.core`),
`(x - a) + a` cancelled (`LTerm.arith`), and simplified (`LTerm.simpE`),
a default of a known kind read as `0` or `false`. -/
def Facts.nf (F : Facts) (t : LTerm) : LTerm := ((t.core F.ne).arith).simpE F.orc F.eqs

theorem Facts.nf_keeps {σ : State} {F : Facts} (hF : F.Ok σ) (t : LTerm) : Keeps σ t (F.nf t) :=
  fun v h => LTerm.simpE_eval (F.orc_ok hF) hF.2.2.1 _ v
    (LTerm.arith_eval _ (LTerm.core_eval hF.2.1 t h))

/-- A term whose normal form is a literal returns that literal, if anything. -/
theorem Facts.nf_lit {σ : State} {F : Facts} (hF : F.Ok σ) {t : LTerm} {w v : Value}
    (hn : F.nf t = .lit w) (hv : t.eval σ = .ok v) : v = w := by
  have h := F.nf_keeps hF t v hv
  rw [hn] at h
  simp only [LTerm.eval, Except.ok.injEq] at h
  exact h.symm

/-- What returns, by the typed normal form. -/
def Facts.rets (F : Facts) : LTerm → Bool := F.retsW F.nf

/-- Every key returns an integer, by the typed normal form. -/
def Facts.keysRet (F : Facts) : LPath → Bool := F.keysRetW F.nf

theorem Facts.rets_sound {σ : State} {F : Facts} (hF : F.Ok σ) (t : LTerm)
    (h : F.rets t = true) : Returns σ t :=
  F.retsW_sound hF (F.nf_keeps hF) t h

/-! ## What a premise tells -/

theorem evalBinop_and_true {p : PrimTy} {x : Value} {rb : Res Value}
    (h : evalBinop .and p x rb = .ok (.bool true)) : x = .bool true ∧ rb = .ok (.bool true) := by
  cases x with
  | int i =>
    simp only [evalBinop, bind, Except.bind, applyBinOp, Value.asBool] at h
    cases rb <;> simp only [reduceCtorEq] at h
  | bool a =>
    cases a
    · simp only [evalBinop, pure, Except.pure, Except.ok.injEq, PrimVal.bool.injEq,
        Bool.false_eq_true] at h
    · refine ⟨rfl, ?_⟩
      cases rb with
      | error e => simp only [evalBinop, bind, Except.bind, reduceCtorEq] at h
      | ok y =>
        cases y with
        | int j => simp only [evalBinop, bind, Except.bind, applyBinOp, Value.asBool,
            reduceCtorEq] at h
        | bool c =>
          cases c
          · simp only [evalBinop, bind, Except.bind, applyBinOp, Value.asBool, Bool.and_false,
              checkArith, Except.ok.injEq, PrimVal.bool.injEq, Bool.false_eq_true] at h
          · rfl

theorem evalBinop_or_false {p : PrimTy} {x : Value} {rb : Res Value}
    (h : evalBinop .or p x rb = .ok (.bool false)) : x = .bool false ∧ rb = .ok (.bool false) := by
  cases x with
  | int i =>
    simp only [evalBinop, bind, Except.bind, applyBinOp, Value.asBool] at h
    cases rb <;> simp only [reduceCtorEq] at h
  | bool a =>
    cases a
    · refine ⟨rfl, ?_⟩
      cases rb with
      | error e => simp only [evalBinop, bind, Except.bind, reduceCtorEq] at h
      | ok y =>
        cases y with
        | int j => simp only [evalBinop, bind, Except.bind, applyBinOp, Value.asBool,
            reduceCtorEq] at h
        | bool c =>
          cases c
          · rfl
          · simp only [evalBinop, bind, Except.bind, applyBinOp, Value.asBool, Bool.or_true,
              checkArith, Except.ok.injEq, PrimVal.bool.injEq, Bool.true_eq_false] at h
    · simp only [evalBinop, pure, Except.pure, Except.ok.injEq, PrimVal.bool.injEq,
        Bool.true_eq_false] at h

/-- `a == b` returned `c`: `b` returned, equal to `a` exactly when `c`. -/
theorem evalBinop_eqB_c {p : PrimTy} {x : Value} {rb : Res Value} {c : Bool}
    (h : evalBinop .eqB p x rb = .ok (.bool c)) : ∃ y, rb = .ok y ∧ decide (x = y) = c := by
  cases rb with
  | error e => cases x <;> simp only [evalBinop, bind, Except.bind, reduceCtorEq] at h
  | ok y =>
    refine ⟨y, rfl, ?_⟩
    cases x <;> simp only [evalBinop, applyBinOp, bind, Except.bind, checkArith,
      Except.ok.injEq, PrimVal.bool.injEq] at h <;> exact h

/-- `a != b` returned `c`: `b` returned, equal to `a` exactly when not `c`. -/
theorem evalBinop_neB_c {p : PrimTy} {x : Value} {rb : Res Value} {c : Bool}
    (h : evalBinop .neB p x rb = .ok (.bool c)) : ∃ y, rb = .ok y ∧ decide (x = y) = !c := by
  cases rb with
  | error e => cases x <;> simp only [evalBinop, bind, Except.bind, reduceCtorEq] at h
  | ok y =>
    refine ⟨y, rfl, ?_⟩
    cases x <;> simp only [evalBinop, applyBinOp, bind, Except.bind, checkArith,
      Except.ok.injEq, PrimVal.bool.injEq] at h <;> rw [← h, Bool.not_not]

/-- `!a` returned `b`: `a` returned `!b`. -/
theorem unop_not {p : PrimTy} {x : Value} {b : Bool}
    (h : (applyUnOp .not x >>= unopCheck .not p) = .ok (.bool b)) : x = .bool (!b) := by
  cases x with
  | int i => simp only [bind, Except.bind, applyUnOp, Value.asBool, reduceCtorEq] at h
  | bool a =>
    simp only [bind, Except.bind, applyUnOp, Value.asBool, unopCheck, pure, Except.pure,
        Except.ok.injEq, PrimVal.bool.injEq, Bool.not_eq_eq_eq_not] at h
    subst h; simp only

/-- Record that `t` returns `v`: its normal form's value. -/
def Facts.addEq (F : Facts) (t : LTerm) (v : Value) : Facts :=
  { F with known := t :: F.known, eqs := (F.nf t, .lit v) :: F.eqs }

theorem Facts.addEq_ok {σ : State} {F : Facts} (hF : F.Ok σ) {t : LTerm} {v : Value}
    (ht : t.eval σ = .ok v) : (F.addEq t v).Ok σ := by
  obtain ⟨hk, hn, he, hl, hv⟩ := hF
  refine ⟨?_, hn, ?_, hl, hv⟩
  · intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact ⟨v, ht⟩
    · exact hk u hu
  · intro q hq x hx
    rcases List.mem_cons.1 hq with rfl | hq
    · have h := Facts.nf_keeps ⟨hk, hn, he, hl, hv⟩ t v ht
      rw [hx] at h
      cases h; rfl
    · exact he q hq x hx

/-- A local or a value of the transaction: what a term is rewritten to. -/
def LTerm.isAtomT : LTerm → Bool
  | .var _ | .env _ => true
  | _ => false

/-- Record that `a` returns what `b` returns: `a`'s normal form rewritten to
`b`'s. -/
def Facts.addSubst (F : Facts) (a b : LTerm) : Facts := { F with eqs := (F.nf a, F.nf b) :: F.eqs }

theorem Facts.addSubst_ok {σ : State} {F : Facts} (hF : F.Ok σ) {a b : LTerm} {x : Value}
    (ha : a.eval σ = .ok x) (hb : b.eval σ = .ok x) : (F.addSubst a b).Ok σ := by
  obtain ⟨hk, hn, he, hl, hv⟩ := hF
  refine ⟨hk, hn, ?_, hl, hv⟩
  intro q hq y hy
  rcases List.mem_cons.1 hq with rfl | hq
  · have h := Facts.nf_keeps ⟨hk, hn, he, hl, hv⟩ a x ha
    rw [hy] at h
    cases h
    exact Facts.nf_keeps ⟨hk, hn, he, hl, hv⟩ b x hb
  · exact he q hq y hy

/-- `a` and `b` return, equal (`c`) or not. -/
def Facts.withNe (F : Facts) (c : Bool) (a b : LTerm) : Facts :=
  { F with known := a.strict ++ b.strict ++ F.known, ne := (c, a, b) :: F.ne }

theorem Facts.withNe_ok {σ : State} {F : Facts} (hF : F.Ok σ) {c : Bool} {a b : LTerm}
    {x y : Value} (ha : a.eval σ = .ok x) (hb : b.eval σ = .ok y) (hxy : x = y ↔ c = true) :
    (F.withNe c a b).Ok σ := by
  obtain ⟨hk, hn, he, hl, hv⟩ := hF
  refine ⟨?_, ?_, he, hl, hv⟩
  · intro u hu
    simp only [Facts.withNe, List.mem_append] at hu
    rcases hu with (hu | hu) | hu
    · exact LTerm.strict_returns a ⟨x, ha⟩ u hu
    · exact LTerm.strict_returns b ⟨y, hb⟩ u hu
    · exact hk u hu
  · intro q hq x' y' hx' hy'
    rcases List.mem_cons.1 hq with rfl | hq
    · simp only at hx' hy'
      rw [ha] at hx'; rw [hb] at hy'
      cases hx'; cases hy'
      exact hxy
    · exact hn q hq x' y' hx' hy'

/-- Two terms return one value: both return, `ne` keeps them equal, and
where one has a literal normal form the other is decomposed at it by `ka`
(`kb`). -/
def Facts.eqnK (F : Facts) (a b : LTerm) (ka kb : Facts → Value → Facts) : Facts :=
  match (F.withNe true a b).nf b with
  | .lit w => ka (F.withNe true a b) w
  | _ =>
    match (F.withNe true a b).nf a with
    | .lit w => kb (F.withNe true a b) w
    | _ =>
      if ((F.withNe true a b).nf b).isAtomT then (F.withNe true a b).addSubst a b
      else if ((F.withNe true a b).nf a).isAtomT then (F.withNe true a b).addSubst b a
      else F.withNe true a b

theorem Facts.eqnK_ok {σ : State} {F : Facts} (hF : F.Ok σ) {a b : LTerm}
    {ka kb : Facts → Value → Facts} {x : Value} (ha : a.eval σ = .ok x) (hb : b.eval σ = .ok x)
    (hka : ∀ G w, G.Ok σ → a.eval σ = .ok w → (ka G w).Ok σ)
    (hkb : ∀ G w, G.Ok σ → b.eval σ = .ok w → (kb G w).Ok σ) :
    (F.eqnK a b ka kb).Ok σ := by
  have hG := F.withNe_ok hF ha hb (c := true) (by simp only)
  unfold Facts.eqnK
  split
  · rename_i w hw
    exact hka _ w hG (by rw [ha, ← Facts.nf_lit hG hw hb])
  · split
    · rename_i _ w hw
      exact hkb _ w hG (by rw [hb, ← Facts.nf_lit hG hw ha])
    · split
      · exact Facts.addSubst_ok hG ha hb
      · split
        · exact Facts.addSubst_ok hG hb ha
        · exact hG

/-- The bounds `a op k = c` puts on `a`: a lower one and an upper one. -/
def cmpBoundL : BinOp → Bool → Int → Option Int × Option Int
  | .lt, true, k => (none, some (k - 1))
  | .lt, false, k => (some k, none)
  | .le, true, k => (none, some k)
  | .le, false, k => (some (k + 1), none)
  | .gt, true, k => (some (k + 1), none)
  | .gt, false, k => (none, some k)
  | .ge, true, k => (some k, none)
  | .ge, false, k => (none, some (k - 1))
  | _, _, _ => (none, none)

/-- The bounds `k op b = c` puts on `b`. -/
def cmpBoundR : BinOp → Bool → Int → Option Int × Option Int
  | .lt, true, k => (some (k + 1), none)
  | .lt, false, k => (none, some k)
  | .le, true, k => (some k, none)
  | .le, false, k => (none, some (k - 1))
  | .gt, true, k => (none, some (k - 1))
  | .gt, false, k => (some k, none)
  | .ge, true, k => (none, some k)
  | .ge, false, k => (some (k + 1), none)
  | _, _, _ => (none, none)

theorem cmpBoundL_sound {op : BinOp} {i k : Int} {c : Bool} (hc : cmpOp op i k = c) :
    (∀ l, (cmpBoundL op c k).1 = some l → l ≤ i) ∧
      (∀ h, (cmpBoundL op c k).2 = some h → i ≤ h) := by
  subst hc
  cases op <;> simp only [cmpOp] <;>
    (try (by_cases hik : i < k <;> simp only [hik, decide_true, decide_false, cmpBoundL,
      Option.some.injEq, reduceCtorEq, false_imp_iff, implies_true, true_and,
      and_true] <;> omega)) <;>
    (try (by_cases hik : i ≤ k <;> simp only [hik, decide_true, decide_false, cmpBoundL,
      Option.some.injEq, reduceCtorEq, false_imp_iff, implies_true, true_and,
      and_true] <;> omega)) <;>
    (try (by_cases hik : k < i <;> simp only [hik, decide_true, decide_false, cmpBoundL,
      Option.some.injEq, reduceCtorEq, false_imp_iff, implies_true, true_and,
      and_true] <;> omega)) <;>
    (try (by_cases hik : k ≤ i <;> simp only [hik, decide_true, decide_false, cmpBoundL,
      Option.some.injEq, reduceCtorEq, false_imp_iff, implies_true, true_and,
      and_true] <;> omega)) <;>
    simp only [cmpBoundL, reduceCtorEq, false_imp_iff, implies_true, and_self]

theorem cmpBoundR_sound {op : BinOp} {k j : Int} {c : Bool} (hc : cmpOp op k j = c) :
    (∀ l, (cmpBoundR op c k).1 = some l → l ≤ j) ∧
      (∀ h, (cmpBoundR op c k).2 = some h → j ≤ h) := by
  subst hc
  cases op <;> simp only [cmpOp] <;>
    (try (by_cases hik : k < j <;> simp only [hik, decide_true, decide_false, cmpBoundR,
      Option.some.injEq, reduceCtorEq, false_imp_iff, implies_true, true_and,
      and_true] <;> omega)) <;>
    (try (by_cases hik : k ≤ j <;> simp only [hik, decide_true, decide_false, cmpBoundR,
      Option.some.injEq, reduceCtorEq, false_imp_iff, implies_true, true_and,
      and_true] <;> omega)) <;>
    (try (by_cases hik : j < k <;> simp only [hik, decide_true, decide_false, cmpBoundR,
      Option.some.injEq, reduceCtorEq, false_imp_iff, implies_true, true_and,
      and_true] <;> omega)) <;>
    (try (by_cases hik : j ≤ k <;> simp only [hik, decide_true, decide_false, cmpBoundR,
      Option.some.injEq, reduceCtorEq, false_imp_iff, implies_true, true_and,
      and_true] <;> omega)) <;>
    simp only [cmpBoundR, reduceCtorEq, false_imp_iff, implies_true, and_self]

/-- Narrow the interval of `t` to the bounds given, where it has one. -/
def Facts.narrow (F : Facts) (t : LTerm) (lo hi : Option Int) : Facts :=
  match F.range t with
  | some (l, h) => { F with bnds := (t, max l (lo.getD l), min h (hi.getD h)) :: F.bnds }
  | none => F

theorem Facts.narrow_ok {σ : State} {F : Facts} (hF : F.Ok σ) {t : LTerm} {i : Int}
    (ht : t.eval σ = .ok (.int i)) {lo hi : Option Int} (hlo : ∀ l, lo = some l → l ≤ i)
    (hhi : ∀ h, hi = some h → i ≤ h) : (F.narrow t lo hi).Ok σ := by
  unfold Facts.narrow
  split
  · rename_i l h hr
    have hlh := F.range_sound hF t hr ht
    obtain ⟨hk, hn, he, hl, hv, hb⟩ := hF
    refine ⟨hk, hn, he, hl, hv, ?_⟩
    intro b hm i' hi'
    rcases List.mem_cons.1 hm with rfl | hm
    · rw [ht] at hi'
      cases hi'
      have h1 : lo.getD l ≤ i := by
        cases lo with
        | none => exact hlh.1
        | some l' => exact hlo l' rfl
      have h2 : i ≤ hi.getD h := by
        cases hi with
        | none => exact hlh.2
        | some h' => exact hhi h' rfl
      exact ⟨Int.max_le.2 ⟨hlh.1, h1⟩, Int.le_min.2 ⟨hlh.2, h2⟩⟩
    · exact hb b hm i' hi'
  · exact hF

/-- What `a op b = c` tells, one side a literal: an interval for the
other. -/
def Facts.addCmp (F : Facts) (op : BinOp) (a b : LTerm) (c : Bool) : Facts :=
  match b with
  | .lit (.int k) => F.narrow a (cmpBoundL op c k).1 (cmpBoundL op c k).2
  | _ =>
    match a with
    | .lit (.int k) => F.narrow b (cmpBoundR op c k).1 (cmpBoundR op c k).2
    | _ => F

theorem Facts.addCmp_ok {σ : State} {F : Facts} (hF : F.Ok σ) {op : BinOp} {a b : LTerm}
    {i j : Int} (ha : a.eval σ = .ok (.int i)) (hb : b.eval σ = .ok (.int j)) {c : Bool}
    (hc : cmpOp op i j = c) : (F.addCmp op a b c).Ok σ := by
  unfold Facts.addCmp
  split
  · rename_i k
    cases hb
    exact F.narrow_ok hF ha (cmpBoundL_sound hc).1 (cmpBoundL_sound hc).2
  · split
    · rename_i k _
      cases ha
      exact F.narrow_ok hF hb (cmpBoundR_sound hc).1 (cmpBoundR_sound hc).2
    · exact hF

/-- What `t` returning `v` tells: its value (`addEq`), and through `&&`,
`||`, `==`, `!=`, `!` and guards, what its operands return. -/
def Facts.decomp (F : Facts) : LTerm → Value → Facts
  | t@(.seq _ a), v => ((F.addEq t v).decomp a v)
  | t@(.binop op _ a b), v =>
    let G := F.addEq t v
    match op, v with
    | .and, .bool true => (G.decomp a (.bool true)).decomp b (.bool true)
    | .or, .bool false => (G.decomp a (.bool false)).decomp b (.bool false)
    | .eqB, .bool true => G.eqnK a b (fun G w => G.decomp a w) (fun G w => G.decomp b w)
    | .neB, .bool false => G.eqnK a b (fun G w => G.decomp a w) (fun G w => G.decomp b w)
    | .eqB, .bool false => G.withNe false a b
    | .neB, .bool true => G.withNe false a b
    | .lt, .bool c => G.addCmp .lt a b c
    | .le, .bool c => G.addCmp .le a b c
    | .gt, .bool c => G.addCmp .gt a b c
    | .ge, .bool c => G.addCmp .ge a b c
    | _, _ => G
  | t@(.unop .not _ a), .bool c => ((F.addEq t (.bool c)).decomp a (.bool !c))
  | t, v => F.addEq t v

theorem Facts.decomp_ok {σ : State} :
    (t : LTerm) → ∀ {F : Facts} {v : Value}, F.Ok σ → t.eval σ = .ok v → (F.decomp t v).Ok σ
  | .seq d a, F, v, hF, ht => by
    simp only [Facts.decomp]
    have ha : a.eval σ = .ok v := by
      simp only [LTerm.eval] at ht
      obtain ⟨_, -, ha⟩ := Res.bind_eq_ok.1 ht
      exact ha
    exact Facts.decomp_ok a (F.addEq_ok hF ht) ha
  | .binop op p a b, F, v, hF, ht => by
    have hG := F.addEq_ok hF ht
    simp only [LTerm.eval] at ht
    obtain ⟨x, hx, ht'⟩ := Res.bind_eq_ok.1 ht
    simp only [Facts.decomp]
    split
    · obtain ⟨rfl, hb⟩ := evalBinop_and_true ht'
      exact Facts.decomp_ok b (Facts.decomp_ok a hG hx) hb
    · obtain ⟨rfl, hb⟩ := evalBinop_or_false ht'
      exact Facts.decomp_ok b (Facts.decomp_ok a hG hx) hb
    · obtain ⟨y, hy, hxy⟩ := evalBinop_eqB_c ht'
      have he : x = y := by simpa only [decide_eq_true_eq] using hxy
      subst he
      exact Facts.eqnK_ok hG hx hy
        (fun G w hG h => Facts.decomp_ok a hG h) (fun G w hG h => Facts.decomp_ok b hG h)
    · obtain ⟨y, hy, hxy⟩ := evalBinop_neB_c ht'
      have he : x = y := by simpa only [Bool.not_false, decide_eq_true_eq] using hxy
      subst he
      exact Facts.eqnK_ok hG hx hy
        (fun G w hG h => Facts.decomp_ok a hG h) (fun G w hG h => Facts.decomp_ok b hG h)
    · obtain ⟨y, hy, hxy⟩ := evalBinop_eqB_c ht'
      exact Facts.withNe_ok hG hx hy (by simpa only [Bool.false_eq_true, iff_false,
          decide_eq_false_iff_not] using hxy)
    · obtain ⟨y, hy, hxy⟩ := evalBinop_neB_c ht'
      exact Facts.withNe_ok hG hx hy (by simpa only [Bool.false_eq_true, iff_false, Bool.not_true,
          decide_eq_false_iff_not] using hxy)
    all_goals first
      | exact hG
      | (obtain ⟨i, j, rfl, hy, hv⟩ := evalBinop_cmp (by simp only [reduceCtorEq, or_self, or_false,
          or_true]) ht'
         cases hv
         exact Facts.addCmp_ok hG hx hy rfl)
  | .unop op p a, F, v, hF, ht => by
    have hG := F.addEq_ok hF ht
    cases op with
    | not =>
      cases v with
      | int => simp only [Facts.decomp]; exact hG
      | bool c =>
        simp only [Facts.decomp]
        simp only [LTerm.eval] at ht
        obtain ⟨x, hx, ht'⟩ := Res.bind_eq_ok.1 ht
        rw [unop_not ht'] at hx
        exact Facts.decomp_ok a hG hx
    | neg | bnot => simp only [Facts.decomp]; exact hG
  | .lit _, F, v, hF, ht | .var _, F, v, hF, ht | .ite .., F, v, hF, ht | .find .., F, v, hF, ht
  | .has .., F, v, hF, ht | .kmap .., F, v, hF, ht | .len .., F, v, hF, ht | .sok _, F, v, hF, ht
  | .pok _, F, v, hF, ht | .orElse .., F, v, hF, ht | .kite .., F, v, hF, ht
  | .zero _, F, v, hF, ht | .err, F, v, hF, ht | .env _, F, v, hF, ht
  | .findP .., F, v, hF, ht => by
    simp only [Facts.decomp]; exact F.addEq_ok hF ht

/-- `a` and `b` never return one value. -/
def Facts.apartNe (F : Facts) (a b : LTerm) : Facts := { F with ne := (false, a, b) :: F.ne }

theorem Facts.apartNe_ok {σ : State} {F : Facts} (hF : F.Ok σ) {a b : LTerm}
    (h : ∀ x y, a.eval σ = .ok x → b.eval σ = .ok y → x ≠ y) : (F.apartNe a b).Ok σ := by
  obtain ⟨hk, hn, he, hl, hv⟩ := hF
  refine ⟨hk, ?_, he, hl, hv⟩
  intro q hq x y hx hy
  rcases List.mem_cons.1 hq with rfl | hq
  · simp only [Bool.false_eq_true, iff_false]
    exact h x y hx hy
  · exact hn q hq x y hx hy

/-- What a premise tells: an equation (`eqnK`, decomposed where a side has a
literal normal form), a disequation, a conjunction both. -/
def Facts.prem (F : Facts) : LFml → Facts
  | .eq a b => F.eqnK a b (fun G w => G.decomp a w) (fun G w => G.decomp b w)
  | .not φ =>
    match φ with
    | .eq a b => F.apartNe a b
    | .and (.eq a a') (.and (.eq b b') (.eq c d)) =>
      -- `¬(c = d)` of a program comparison: `¬(defined c ∧ defined d ∧ c ≐ d)`
      if a = c ∧ a' = c ∧ b = d ∧ b' = d then F.apartNe c d else F
    | _ => F
  | .and φ ψ => (F.prem φ).prem ψ
  | _ => F

theorem Facts.prem_ok {σ : State} : (φ : LFml) → ∀ {F : Facts}, F.Ok σ → φ.holds σ →
    (F.prem φ).Ok σ
  | .eq a b, F, hF, h => by
    obtain ⟨x, ha, hb⟩ := (LFml.holds_eq_iff σ a b).1 h
    exact Facts.eqnK_ok hF ha hb (fun G w hG h => Facts.decomp_ok a hG h)
      (fun G w hG h => Facts.decomp_ok b hG h)
  | .not φ, F, hF, h => by
    simp only [Facts.prem]
    split
    · rename_i a b
      refine F.apartNe_ok hF fun x y hx hy hxy => h ?_
      subst hxy
      exact (LFml.holds_eq_iff σ a b).2 ⟨x, hx, hy⟩
    · rename_i a a' b b' c d
      split
      · rename_i he
        refine F.apartNe_ok hF fun x y hx hy hxy => h ?_
        subst hxy
        rw [he.1, he.2.1, he.2.2.1, he.2.2.2]
        exact ⟨(LFml.holds_eq_iff σ c c).2 ⟨x, hx, hx⟩, (LFml.holds_eq_iff σ d d).2 ⟨x, hy, hy⟩,
          (LFml.holds_eq_iff σ c d).2 ⟨x, hx, hy⟩⟩
      · exact hF
    · exact hF
  | .and φ ψ, F, hF, h => Facts.prem_ok ψ (Facts.prem_ok φ hF h.1) h.2
  | .tt, _, hF, _ | .imp .., _, hF, _ | .all .., _, hF, _ => hF

/-! ## Closing a leaf -/

/-- Two normal forms that are different literals, or a normal form that
halts. -/
def litNe : LTerm → LTerm → Bool
  | .lit x, .lit y => x != y
  | _, _ => false

/-- `a ≐ b` cannot hold: one side halts, both are literals apart, or a
premise keeps them apart. -/
def Facts.apart (F : Facts) (a b : LTerm) : Bool :=
  F.halts a || F.halts b || F.nf a == .err || F.nf b == .err || litNe (F.nf a) (F.nf b) ||
    F.ne.any fun (c, p, q) => !c && ((p == a && q == b) || (p == b && q == a))

theorem Facts.apart_sound {σ : State} {F : Facts} (hF : F.Ok σ) {a b : LTerm}
    (h : F.apart a b = true) : ¬ (LFml.eq a b).holds σ := by
  intro hab
  obtain ⟨x, ha, hb⟩ := (LFml.holds_eq_iff σ a b).1 hab
  have hna := F.nf_keeps hF a x ha
  have hnb := F.nf_keeps hF b x hb
  simp only [Facts.apart, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  rcases h with ((((h | h) | h) | h) | h) | ⟨⟨c, p, q⟩, hm, hc, hpq⟩
  · exact F.halts_sound hF a h x ha
  · exact F.halts_sound hF b h x hb
  · rw [h] at hna; cases hna
  · rw [h] at hnb; cases hnb
  · unfold litNe at h
    split at h
    · rename_i u w hu hw
      rw [hu] at hna; rw [hw] at hnb
      simp only [LTerm.eval, Except.ok.injEq] at hna hnb
      subst hna hnb
      simp only [bne_self_eq_false, Bool.false_eq_true] at h
    · cases h
  · simp only at hc
    subst hc
    have := hF.2.1 _ hm
    rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · subst hp hq
      simpa only [Bool.false_eq_true, iff_false, not_true_eq_false] using (this x x ha hb)
    · subst hp hq
      simpa only [Bool.false_eq_true, iff_false, not_true_eq_false] using (this x x hb ha)

/-- The terms an equation compares with a `bool` literal: what a case split
on a condition takes. -/
def LFml.boolAtoms : LFml → List LTerm
  | .eq a (.lit (.bool _)) => [a]
  | .not φ => φ.boolAtoms
  | .and φ ψ | .imp φ ψ => φ.boolAtoms ++ ψ.boolAtoms
  | _ => []

/-- No fact mentions `x`. -/
def Facts.fresh (F : Facts) (x : Var) : Bool :=
  F.known.all (fun t => !t.vars.contains x) &&
    F.ne.all (fun q => !q.2.1.vars.contains x && !q.2.2.vars.contains x) &&
    F.eqs.all (fun e => !e.1.vars.contains x && !e.2.vars.contains x) &&
    F.bnds.all (fun b => !b.1.vars.contains x)

/-- `x` holds a value of type `p`. -/
def Facts.bind (F : Facts) (x : Var) (p : PrimTy) : Facts :=
  { F with vars := (x, p) :: F.vars.filter (·.1 != x) }

theorem Facts.bind_ok {σ : State} {F : Facts} (hF : F.Ok σ) {x : Var} (hx : F.fresh x = true)
    {p : PrimTy} {v : Value} (hv : p.admits v) : (F.bind x p).Ok (σ.setEnv x (.val v)) := by
  obtain ⟨hk, hn, he, hl, hvs, hb⟩ := hF
  simp only [Facts.fresh, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not] at hx
  obtain ⟨⟨⟨hkx, hnx⟩, hex⟩, hbx⟩ := hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨w, hw⟩ := hk u hu
    exact ⟨w, by rw [LTerm.eval_setEnv _ (hkx u hu)]; exact hw⟩
  · intro q hq x' y' hx' hy'
    rw [LTerm.eval_setEnv _ (hnx q hq).1] at hx'
    rw [LTerm.eval_setEnv _ (hnx q hq).2] at hy'
    exact hn q hq x' y' hx' hy'
  · intro e he' x' hx'
    rw [LTerm.eval_setEnv _ (hex e he').1] at hx'
    rw [LTerm.eval_setEnv _ (hex e he').2]
    exact he e he' x' hx'
  · exact hl
  · intro xp hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨v, by simp only [LTerm.eval, State.getEnv_setEnv_self, Res.ok_bind]; rfl, hv⟩
    · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hm
      obtain ⟨hm, hne⟩ := hm
      obtain ⟨w, hw, ha⟩ := hvs xp hm
      exact ⟨w, by simp only [LTerm.eval, State.getEnv_setEnv_ne hne] at hw ⊢; exact hw, ha⟩
  · intro b hm i hi
    rw [LTerm.eval_setEnv _ (hbx b hm)] at hi
    exact hb b hm i hi

/-- The locals of type `bool`: what a case split takes first. -/
def Facts.boolVars (F : Facts) : List LTerm :=
  F.vars.filterMap fun xp => if xp.2 == .bool then some (.var xp.1) else none

/-- `k` holds of the facts, or of the facts with `c` `true` and with `c`
`false` for one `bool` term `c` of `cs` that returns: KeY's case split on a
formula. -/
def Facts.split (F : Facts) (k : Facts → Bool) (cs : List LTerm) : Bool :=
  k F || cs.any fun c => F.rets c && F.isBool c &&
    k (F.addEq c (.bool true)) && k (F.addEq c (.bool false))

theorem Facts.split_sound {σ : State} {F : Facts} (hF : F.Ok σ) {k : Facts → Bool}
    {cs : List LTerm} {P : Prop} (hk : ∀ G : Facts, G.Ok σ → k G = true → P)
    (h : F.split k cs = true) : P := by
  simp only [Facts.split, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨c, -, ⟨⟨hc, hb⟩, ht⟩, hf⟩
  · exact hk F hF h
  · obtain ⟨v, hv⟩ := F.rets_sound hF c hc
    obtain ⟨b, rfl⟩ := F.isBool_sound hF c hb hv
    cases b
    · exact hk _ (F.addEq_ok hF hv) hf
    · exact hk _ (F.addEq_ok hF hv) ht

/-- `a ≐ b` holds wherever the facts do: both sides return, with one normal
form, or as the two sides of an equation the premises give. -/
def Facts.eqHolds (F : Facts) (a b : LTerm) : Bool :=
  F.rets a && F.rets b &&
    (F.nf a == F.nf b || F.ne.any fun (c, p, q) => c && F.rets p && F.rets q &&
      ((F.nf a == F.nf p && F.nf b == F.nf q) || (F.nf a == F.nf q && F.nf b == F.nf p)))

theorem Facts.eqHolds_sound {σ : State} {F : Facts} (hF : F.Ok σ) {a b : LTerm}
    (h : F.eqHolds a b = true) : (LFml.eq a b).holds σ := by
  simp only [Facts.eqHolds, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true] at h
  obtain ⟨⟨ha, hb⟩, hc⟩ := h
  obtain ⟨x, hx⟩ := F.rets_sound hF a ha
  obtain ⟨y, hy⟩ := F.rets_sound hF b hb
  refine (LFml.holds_eq_iff σ a b).2 ⟨x, hx, ?_⟩
  have hnx := F.nf_keeps hF a x hx
  have hny := F.nf_keeps hF b y hy
  rcases hc with hc | ⟨⟨c, p, q⟩, hm, hc⟩
  · rw [hc, hny] at hnx; cases hnx; exact hy
  · obtain ⟨⟨⟨rfl, hp⟩, hq⟩, hs⟩ := hc
    obtain ⟨xp, hxp⟩ := F.rets_sound hF p hp
    obtain ⟨yq, hyq⟩ := F.rets_sound hF q hq
    have hpq : xp = yq := (hF.2.1 _ hm xp yq hxp hyq).2 rfl
    have hnp := F.nf_keeps hF p xp hxp
    have hnq := F.nf_keeps hF q yq hyq
    rcases hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [h₁, hnp] at hnx; rw [h₂, hnq] at hny
      cases hnx; cases hny; rw [hpq]; exact hy
    · rw [h₁, hnq] at hnx; rw [h₂, hnp] at hny
      cases hnx; cases hny; rw [← hpq]; exact hy

mutual

/-- `φ` holds wherever the facts do. -/
def Facts.prove (F : Facts) : LFml → Bool
  | .tt => true
  | .imp φ ψ => F.refute φ || (F.prem φ).prove ψ
  | .and φ ψ => F.prove φ && F.prove ψ
  | .eq a b => F.split (·.eqHolds a b) F.boolVars
  | .not φ => F.split (·.refute φ) (F.boolVars ++ φ.boolAtoms)
  | .all x p φ => F.fresh x && (F.bind x p).prove φ

/-- `φ` fails wherever the facts hold. -/
def Facts.refute (F : Facts) : LFml → Bool
  | .tt => false
  | .eq a b => F.apart a b
  | .not φ => F.prove φ
  | .and φ ψ => F.refute φ || (F.prem φ).refute ψ
  | .imp φ ψ => F.prove φ && (F.prem φ).refute ψ
  | .all .. => false

end

mutual

theorem Facts.prove_sound : (φ : LFml) → ∀ {σ : State} {F : Facts}, F.Ok σ →
    F.prove φ = true → φ.holds σ
  | .tt, _, _, _, _ => trivial
  | .imp φ ψ, σ, F, hF, h => fun hφ => by
    simp only [Facts.prove, Bool.or_eq_true] at h
    rcases h with h | h
    · exact absurd hφ (Facts.refute_sound φ hF h)
    · exact Facts.prove_sound ψ (Facts.prem_ok φ hF hφ) h
  | .and φ ψ, σ, F, hF, h => by
    simp only [Facts.prove, Bool.and_eq_true] at h
    exact ⟨Facts.prove_sound φ hF h.1, Facts.prove_sound ψ hF h.2⟩
  | .eq a b, σ, F, hF, h =>
    F.split_sound hF (fun _ hG hk => Facts.eqHolds_sound hG hk) h
  | .not φ, σ, F, hF, h =>
    F.split_sound hF (fun _ hG hk => Facts.refute_sound φ hG hk) h
  | .all x p φ, σ, F, hF, h => by
    simp only [Facts.prove, Bool.and_eq_true] at h
    intro v hv
    exact Facts.prove_sound φ (F.bind_ok hF h.1 hv) h.2

theorem Facts.refute_sound : (φ : LFml) → ∀ {σ : State} {F : Facts}, F.Ok σ →
    F.refute φ = true → ¬ φ.holds σ
  | .tt, _, _, _, h => by simp only [refute, Bool.false_eq_true] at h
  | .all .., _, _, _, h => by simp only [refute, Bool.false_eq_true] at h
  | .eq a b, σ, F, hF, h => F.apart_sound hF h
  | .not φ, σ, F, hF, h => fun hn => hn (Facts.prove_sound φ hF h)
  | .and φ ψ, σ, F, hF, h => fun ⟨hφ, hψ⟩ => by
    simp only [Facts.refute, Bool.or_eq_true] at h
    rcases h with h | h
    · exact Facts.refute_sound φ hF h hφ
    · exact Facts.refute_sound ψ (Facts.prem_ok φ hF hφ) h hψ
  | .imp φ ψ, σ, F, hF, h => fun hi => by
    simp only [Facts.refute, Bool.and_eq_true] at h
    have hφ := Facts.prove_sound φ hF h.1
    exact Facts.refute_sound ψ (Facts.prem_ok φ hF hφ) h.2 (hi hφ)

end

/-- **The closer**: `φ` holds in every state whose storage holds the
layout `L` (none asked when `L` is empty). -/
def LFml.close (L : List (Name × Ty)) (φ : LFml) : Bool := Facts.prove { lay := L } φ

theorem LFml.close_holds {L : List (Name × Ty)} {φ : LFml} {σ : State} (hL : LayoutOk L σ)
    (h : LFml.close L φ = true) : φ.holds σ :=
  Facts.prove_sound φ (F := { lay := L })
    ⟨fun _ hu => (nomatch hu), fun _ hp => (nomatch hp), fun _ hp => (nomatch hp), hL,
      fun _ hp => (nomatch hp), fun _ hp => (nomatch hp)⟩ h

/-! ## A bound on the work -/

mutual

/-- `t` has at most `n` nodes, counted as a tree; the fuel left. -/
def LTerm.fits : Nat → LTerm → Option Nat
  | 0, _ => none
  | n + 1, .binop _ _ a b | n + 1, .seq a b | n + 1, .orElse a b =>
    (a.fits n).bind fun m => b.fits m
  | n + 1, .unop _ _ a | n + 1, .zero a => a.fits n
  | n + 1, .ite c a b =>
    (c.fits n).bind fun m => (a.fits m).bind fun k => b.fits k
  | n + 1, .kite a b t e =>
    (a.fits n).bind fun m => (b.fits m).bind fun k => (t.fits k).bind fun j => e.fits j
  | n + 1, .find s q | n + 1, .has s q | n + 1, .kmap _ s q | n + 1, .len s q
  | n + 1, .findP s q => (s.fits n).bind fun m => q.fits m
  | n + 1, .sok s => s.fits n
  | n + 1, .pok q => q.fits n
  | n + 1, .lit _ | n + 1, .var _ | n + 1, .err | n + 1, .env _ => some n

/-- `q` has at most `n` nodes. -/
def LPath.fits : Nat → LPath → Option Nat
  | 0, _ => none
  | n + 1, .root _ => some n
  | n + 1, .field q _ => q.fits n
  | n + 1, .at q k => (q.fits n).bind fun m => k.fits m

/-- `s` has at most `n` nodes. -/
def LStor.fits : Nat → LStor → Option Nat
  | 0, _ => none
  | n + 1, .init => some n
  | n + 1, .save s q w => (s.fits n).bind fun m => (q.fits m).bind fun k => w.fits k
  | n + 1, .del s q => (s.fits n).bind fun m => q.fits m
  | n + 1, .arr _ s q w => (s.fits n).bind fun m => (q.fits m).bind fun k => w.fits k
  | n + 1, .copy s q src sq =>
    (s.fits n).bind fun m => (q.fits m).bind fun k => (src.fits k).bind fun j => sq.fits j

end

/-- `φ` has at most `n` nodes, counted as a tree: its terms share
subterms, a storage written from a read of the one before it twice, so the
tree doubles with each such write. -/
def LFml.fits : Nat → LFml → Option Nat
  | 0, _ => none
  | n + 1, .tt => some n
  | n + 1, .eq a b => (a.fits n).bind fun m => b.fits m
  | n + 1, .not φ => φ.fits n
  | n + 1, .and φ ψ | n + 1, .imp φ ψ => (φ.fits n).bind fun m => ψ.fits m
  | n + 1, .all _ _ φ => φ.fits n

end Decide

end Solidity
