import Solidity.Calculus.KIntBinder
import Solidity.Calculus.MemHoist

/-!
# Binders of KeY's `int` read over two words (M7, feature 27)

A binder of KeY's unbounded `int` (`Fml.bind _ _ .kint`) has no position in
the leaf language (`LFml` binds a `PrimTy`'s values only), and feature 26
reads only positive ones, as ledger entries, in leaves reading no ledger.
A binder whose body reads it *linearly against bounded terms* needs neither
an unbounded position nor the ledger: every comparison `zcmp` of the body
whose two sides read it with different coefficients compares `c·z + ρ`
with `0`, the remainder `ρ` a sum of words, literals and their products by
literals, so `|ρ| ≤ R` for a bound `R` read off the body (`Tm.zl`).  Past
`R` on either side the comparison has the sign of `c·z`, so the body holds
at `z` exactly where it holds at `z` clamped to `[-R-1, R+1]`
(`Fml.zl_holds`, two values `ZSim` alike).  That interval is the range of
`c·toInt(a) - toInt(b) - (R+1)` over two words `a`, `b` (`zEncT`, `c`
the least multiplier whose range covers it), so

  `∀ int z. φ`  reads as  `∀ uint a. ∀ uint b. φ[z := c·toInt(a) - toInt(b) - (R+1)]`

at every state and in either polarity (`Fml.holds_kencAt`): an `∃` over
`ℤ` (a negative binder, `gapKIntNeg`) becomes one over two words, which
the quantified pipeline (`quantReduction?`) takes, and a positive binder
in a leaf that reads the ledger elsewhere becomes two parameters.  The
rewriting is an equivalence at every state (`Fml.holds_kenc`), so a proof
of the rewritten leaf proves the leaf and a state refuting it refutes the
leaf, as it is.

The substitution (`Sb`, `Tm.sb`, `Fml.sb?`) is a renaming that may send a
local of KeY's `int` to a term (`SbT.tm`), read in the state whose locals
are pulled back along it (`State.sbPull`, `Tm.eval_sb`, `Fml.holds_sb`),
as `Calculus/MemHoist.lean`'s renamings are.

Outside: a binder one of whose comparisons reads it beside an unbounded
term with another coefficient (a ledger entry, another local of KeY's
`int`, a product of two symbolic terms), and a remainder past `2^511`
(`c` would exceed a word).
-/

namespace Solidity

open Decide (Ren)

variable {C : Contract}

/-! ## Linear in a local of KeY's `int` -/

/-- **An unbounded term a comparison may cancel**: a local of KeY's `int`,
a ledger entry at a `uint` local or at a literal (locals by position from
the innermost, in the context the term is read in). -/
inductive AKey where
  | loc (n : Nat)
  | netL (n : Nat)
  | netC (v : PrimTy.uint.Denote)
  deriving DecidableEq

/-- `k·κ` added to a sum of keys, merged with `κ`'s coefficient (dropped
at `0`). -/
def uIns (κ : AKey) (k : Int) : List (AKey × Int) → List (AKey × Int)
  | [] => if k = 0 then [] else [(κ, k)]
  | (κ', k') :: u => if κ' = κ then (if k' + k = 0 then u else (κ, k' + k) :: u)
    else (κ', k') :: uIns κ k u

/-- Two sums of keys added. -/
def uAdd (a b : List (AKey × Int)) : List (AKey × Int) := a.foldr (fun e acc => uIns e.1 e.2 acc) b

/-- A sum of keys scaled. -/
def uScale (m : Int) (u : List (AKey × Int)) : List (AKey × Int) :=
  if m = 0 then [] else u.map fun e => (e.1, m * e.2)

/-- `a - b`. -/
def uSub (a b : List (AKey × Int)) : List (AKey × Int) := uAdd a (uScale (-1) b)

/-- A sum of keys at their values `ν`. -/
def uval (ν : AKey → Int) : List (AKey × Int) → Int
  | [] => 0
  | e :: u => e.2 * ν e.1 + uval ν u

theorem uval_uIns (ν : AKey → Int) (κ : AKey) (k : Int) :
    (u : List (AKey × Int)) → uval ν (uIns κ k u) = k * ν κ + uval ν u
  | [] => by
    unfold uIns
    split
    · next h => subst h; simp only [uval, Int.zero_mul, Int.add_zero]
    · rfl
  | (κ', k') :: u => by
    unfold uIns
    split
    · next h =>
      subst h
      split
      · next h => simp only [uval, Int.add_mul] at h ⊢; rw [← Int.add_assoc]
                  have : k' * ν κ' + k * ν κ' = 0 := by rw [← Int.add_mul, h, Int.zero_mul]
                  omega
      · simp only [uval, Int.add_mul]; omega
    · simp only [uval, uval_uIns ν κ k u]; omega

theorem uval_uAdd (ν : AKey → Int) (a b : List (AKey × Int)) :
    uval ν (uAdd a b) = uval ν a + uval ν b := by
  induction a with
  | nil => simp only [uAdd, List.foldr, uval, Int.zero_add]
  | cons e a ih =>
    show uval ν (uIns e.1 e.2 (uAdd a b)) = _
    rw [uval_uIns, ih]
    simp only [uval]; omega

theorem uval_uScale (ν : AKey → Int) (m : Int) (u : List (AKey × Int)) :
    uval ν (uScale m u) = m * uval ν u := by
  unfold uScale
  split
  · next h => subst h; simp only [uval, Int.zero_mul]
  · induction u with
    | nil => simp only [List.map, uval, Int.mul_zero]
    | cons e u ih => simp only [List.map, uval] at ih ⊢; rw [ih, Int.mul_add, Int.mul_assoc]

theorem uval_uSub (ν : AKey → Int) (a b : List (AKey × Int)) :
    uval ν (uSub a b) = uval ν a - uval ν b := by
  rw [uSub, uval_uAdd, uval_uScale]; omega

/-- **What a term reads of the local `z`**: its coefficient `c` (a term of
KeY's `int` reads `c·z + U + ρ`, `U` a sum of keys `u`), a bound on the
remainder `|ρ|` (`none`: unbounded), the largest bound a comparison in it
needs (`n`), and its value where it is a literal (`k`). -/
structure ZL where
  c : Int
  b : Option Nat
  n : Nat
  k : Option Int
  u : List (AKey × Int)

/-- A term not of KeY's `int`, its comparisons needing `n`. -/
def ZL.flat (n : Nat) : ZL := ⟨0, none, n, none, []⟩

/-- The sum of two bounds. -/
def optAdd (x y : Option Nat) : Option Nat := x.bind fun p => y.map (p + ·)

/-- A binary symbol read over its operands': linear `+`, `-`, a product
with a literal (or of two terms not reading `z`), and a comparison whose
sides read `z` alike, or are bounded once their keys cancel. -/
def Op2.zl {a b s : Srt} : Op2 C a b s → ZL → ZL → Option ZL
  | .zbin .add _, x, y => some ⟨x.c + y.c, optAdd x.b y.b, max x.n y.n, none, uAdd x.u y.u⟩
  | .zbin .sub _, x, y => some ⟨x.c - y.c, optAdd x.b y.b, max x.n y.n, none, uSub x.u y.u⟩
  | .zbin .mul _, x, y => match x.k, y.k with
    | some m, _ => some ⟨m * y.c, y.b.map (m.natAbs * ·), max x.n y.n, none, uScale m y.u⟩
    | none, some m => some ⟨x.c * m, x.b.map (· * m.natAbs), max x.n y.n, none, uScale m x.u⟩
    | none, none =>
      if x.c = 0 ∧ y.c = 0 then
        some ⟨0, (if x.u = [] ∧ y.u = [] then x.b.bind fun p => y.b.map (p * ·) else none),
          max x.n y.n, none, []⟩
      else none
  | .zbin _ _, _, _ => none
  | .zcmp _ _, x, y =>
    if x.c = y.c then some (ZL.flat (max x.n y.n))
    else match x.b, y.b with
      | some p, some q =>
        if uSub x.u y.u = [] then some (ZL.flat (max (max x.n y.n) (p + q))) else none
      | _, _ => none
  | _, x, y => some (ZL.flat (max x.n y.n))

/-- A unary symbol's result's bound: a `uint` widened is below `2^256`. -/
def Op1.zlB {a s : Srt} : Op1 C a s → Option Nat
  | .toInt => some (2 ^ 256 - 1)
  | _ => none

/-- A `uint` term naming a ledger entry's address as a key: a local or a
literal. -/
def Tm.netKey? {Γ : Ctx} : Tm C Γ (.val .uint) → Option AKey
  | .pvV i => some (.netL i.toNat)
  | .app0 (.lit v) => some (.netC v)
  | _ => none

/-- A unary symbol's result as a key: a ledger entry at a key's address. -/
def Op1.zlK {Γ : Ctx} {a s : Srt} : Op1 C a s → Tm C Γ a → Option AKey
  | .net, x => x.netKey?
  | _, _ => none

/-- **A term linear in the local `zi`** (`none` outside). -/
def Tm.zl {Γ : Ctx} (zi : Idx Γ .kint) : {s : Srt} → Tm C Γ s → Option ZL
  | _, .pvV _ | _, .pvP _ | _, .pvS _ | _, .pvI _ => some (ZL.flat 0)
  | _, .netOf _ a => (a.zl zi).map fun r => ZL.flat r.n
  | _, .pvZ i => some (if i.toNat = zi.toNat then ⟨1, some 0, 0, none, []⟩
    else ⟨0, some 0, 0, none, [(.loc i.toNat, 1)]⟩)
  | _, .app0 o => some (match o with
    | .zlit m => ⟨0, some m.natAbs, 0, some m, []⟩
    | _ => ZL.flat 0)
  | _, .app1 o x => (x.zl zi).map fun r => match o.zlK x with
    | some κ => ⟨0, some 0, r.n, none, [(κ, 1)]⟩
    | none => ⟨0, o.zlB, r.n, none, []⟩
  | _, .app2 o x y => (x.zl zi).bind fun rx => (y.zl zi).bind fun ry => o.zl rx ry
  | _, .app3 _ x y z => (x.zl zi).bind fun rx => (y.zl zi).bind fun ry =>
    (z.zl zi).map fun rz => ZL.flat (max rx.n (max ry.n rz.n))

/-! ## Two values the comparisons do not tell apart -/

/-- Equal, or both past `R` on one side. -/
def ZSim (R : Nat) (v v' : Int) : Prop :=
  v = v' ∨ ((R : Int) < v ∧ (R : Int) < v') ∨ (v < -(R : Int) ∧ v' < -(R : Int))

/-- Two readings of a term of KeY's `int` at `z = v` and `z = v'`, its
keys at `ν`: equal past `c·z`, the remainder past the keys within the
bound, a literal itself. -/
def ZRelK (ν : AKey → Int) (r : ZL) (v v' : Int) (x y : Option Int) : Prop :=
  x.map (· - r.c * v) = y.map (· - r.c * v') ∧
    (∀ B w, r.b = some B → x = some w →
      -(B : Int) ≤ w - r.c * v - uval ν r.u ∧ w - r.c * v - uval ν r.u ≤ B) ∧
    (∀ m, r.k = some m → x = some m ∧ y = some m)

/-- Two readings of a term: `ZRelK` at KeY's `int`, equal otherwise. -/
def ZRel {H : HTy} (ν : AKey → Int) (r : ZL) (v v' : Int) :
    (s : Srt) → Option (s.Den C H) → Option (s.Den C H) → Prop
  | .kint, x, y => ZRelK ν r v v' x y
  | _, x, y => x = y

/-- Two denotations of a term: `ZRelK` at KeY's `int`, equal otherwise. -/
def ZRelD (ν : AKey → Int) (r : ZL) (v v' : Int) : (s : Srt) → s.TDen C → s.TDen C → Prop
  | .kint, x, y => ZRelK ν r v v' x y
  | _, x, y => x = y

theorem ZRel.iff_eq {H : HTy} {ν : AKey → Int} {r : ZL} {v v' : Int} {s : Srt} (hs : s ≠ .kint)
    {x y : Option (s.Den C H)} : ZRel ν r v v' s x y ↔ x = y := by
  cases s <;> first | exact absurd rfl hs | exact Iff.rfl

theorem ZRelD.iff_eq {ν : AKey → Int} {r : ZL} {v v' : Int} {s : Srt} (hs : s ≠ .kint)
    {x y : s.TDen C} : ZRelD (C := C) ν r v v' s x y ↔ x = y := by
  cases s <;> first | exact absurd rfl hs | exact Iff.rfl

/-! ### The arithmetic of the relation -/

section Arith

variable {ν : AKey → Int} {v v' : Int}

/-- Both readings halt, or both return, alike past `c·z`. -/
theorem ZRelK.cases {r : ZL} {X X' : Option Int} (h : ZRelK ν r v v' X X') :
    (X = none ∧ X' = none) ∨ ∃ a a', X = some a ∧ X' = some a' ∧ a - r.c * v = a' - r.c * v' := by
  obtain ⟨h, -, -⟩ := h
  cases X <;> cases X' <;> simp_all

/-- Equal readings of a term with no coefficient. -/
theorem ZRelK.of_eq {X : Option Int} {b : Option Nat} {n : Nat} {u : List (AKey × Int)}
    (hb : ∀ B w, b = some B → X = some w → -(B : Int) ≤ w - uval ν u ∧ w - uval ν u ≤ B) :
    ZRelK ν ⟨0, b, n, none, u⟩ v v' X X :=
  ⟨by simp only [Int.zero_mul, Int.sub_zero, Option.map_id_fun', id_eq],
    fun B w hB hw => by simpa only [Int.zero_mul, Int.sub_zero] using hb B w hB hw,
    fun _ h => nomatch h⟩

/-- A coefficient-free relation is equality. -/
theorem ZRelK.eq_of_c {r : ZL} {X X' : Option Int} (h : ZRelK ν r v v' X X') (hc : r.c = 0) :
    X = X' := by
  have h1 := h.1
  rw [hc] at h1
  simpa only [Int.zero_mul, Int.sub_zero, Option.map_id_fun', id_eq] using h1

theorem ZRelK.add {rx ry : ZL} {n : Nat} {X X' Y Y' : Option Int} (hx : ZRelK ν rx v v' X X')
    (hy : ZRelK ν ry v v' Y Y') :
    ZRelK ν ⟨rx.c + ry.c, optAdd rx.b ry.b, n, none, uAdd rx.u ry.u⟩ v v'
      (do some (BinOp.evalZ .add (← X) (← Y))) (do some (BinOp.evalZ .add (← X') (← Y'))) := by
  refine ⟨?_, ?_, fun _ h => nomatch h⟩
  · rcases hx.cases with ⟨rfl, rfl⟩ | ⟨a, a', rfl, rfl, ha⟩
    · rfl
    rcases hy.cases with ⟨rfl, rfl⟩ | ⟨b, b', rfl, rfl, hb⟩
    · rfl
    show some (a + b - (rx.c + ry.c) * v) = some (a' + b' - (rx.c + ry.c) * v')
    rw [Int.add_mul, Int.add_mul]; congr 1; omega
  · intro B w hB hw
    simp only [optAdd, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hB
    obtain ⟨p, hp, q, hq, rfl⟩ := hB
    rcases hx.cases with ⟨rfl, rfl⟩ | ⟨a, a', rfl, rfl, -⟩
    · cases hw
    rcases hy.cases with ⟨rfl, rfl⟩ | ⟨b, b', rfl, rfl, -⟩
    · cases hw
    cases hw
    have h1 := hx.2.1 p a hp rfl
    have h2 := hy.2.1 q b hq rfl
    show -((p + q : Nat) : Int) ≤ a + b - (rx.c + ry.c) * v - uval ν (uAdd rx.u ry.u) ∧
      a + b - (rx.c + ry.c) * v - uval ν (uAdd rx.u ry.u) ≤ (p + q : Nat)
    rw [Int.add_mul, uval_uAdd]; omega

theorem ZRelK.sub {rx ry : ZL} {n : Nat} {X X' Y Y' : Option Int} (hx : ZRelK ν rx v v' X X')
    (hy : ZRelK ν ry v v' Y Y') :
    ZRelK ν ⟨rx.c - ry.c, optAdd rx.b ry.b, n, none, uSub rx.u ry.u⟩ v v'
      (do some (BinOp.evalZ .sub (← X) (← Y))) (do some (BinOp.evalZ .sub (← X') (← Y'))) := by
  refine ⟨?_, ?_, fun _ h => nomatch h⟩
  · rcases hx.cases with ⟨rfl, rfl⟩ | ⟨a, a', rfl, rfl, ha⟩
    · rfl
    rcases hy.cases with ⟨rfl, rfl⟩ | ⟨b, b', rfl, rfl, hb⟩
    · rfl
    show some (a - b - (rx.c - ry.c) * v) = some (a' - b' - (rx.c - ry.c) * v')
    rw [Int.sub_mul, Int.sub_mul]; congr 1; omega
  · intro B w hB hw
    simp only [optAdd, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hB
    obtain ⟨p, hp, q, hq, rfl⟩ := hB
    rcases hx.cases with ⟨rfl, rfl⟩ | ⟨a, a', rfl, rfl, -⟩
    · cases hw
    rcases hy.cases with ⟨rfl, rfl⟩ | ⟨b, b', rfl, rfl, -⟩
    · cases hw
    cases hw
    have h1 := hx.2.1 p a hp rfl
    have h2 := hy.2.1 q b hq rfl
    show -((p + q : Nat) : Int) ≤ a - b - (rx.c - ry.c) * v - uval ν (uSub rx.u ry.u) ∧
      a - b - (rx.c - ry.c) * v - uval ν (uSub rx.u ry.u) ≤ (p + q : Nat)
    rw [Int.sub_mul, uval_uSub]; omega

/-- `|m·ρ| ≤ |m|·B` where `|ρ| ≤ B`. -/
theorem int_mul_bound (m ρ : Int) (B : Nat) (h1 : -(B : Int) ≤ ρ) (h2 : ρ ≤ B) :
    -((m.natAbs * B : Nat) : Int) ≤ m * ρ ∧ m * ρ ≤ ((m.natAbs * B : Nat) : Int) := by
  have h : (m * ρ).natAbs ≤ m.natAbs * B := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul_left _ (by omega)
  omega

theorem ZRelK.mulL {rx ry : ZL} {m : Int} {n : Nat} {X X' Y Y' : Option Int}
    (hx : ZRelK ν rx v v' X X') (hm : rx.k = some m) (hy : ZRelK ν ry v v' Y Y') :
    ZRelK ν ⟨m * ry.c, ry.b.map (m.natAbs * ·), n, none, uScale m ry.u⟩ v v'
      (do some (BinOp.evalZ .mul (← X) (← Y))) (do some (BinOp.evalZ .mul (← X') (← Y'))) := by
  obtain ⟨rfl, rfl⟩ := hx.2.2 m hm
  refine ⟨?_, ?_, fun _ h => nomatch h⟩
  · rcases hy.cases with ⟨rfl, rfl⟩ | ⟨b, b', rfl, rfl, hb⟩
    · rfl
    show some (m * b - m * ry.c * v) = some (m * b' - m * ry.c * v')
    rw [Int.mul_assoc, Int.mul_assoc, ← Int.mul_sub, ← Int.mul_sub, hb]
  · intro B w hB hw
    simp only [Option.map_eq_some_iff] at hB
    obtain ⟨q, hq, rfl⟩ := hB
    rcases hy.cases with ⟨rfl, rfl⟩ | ⟨b, b', rfl, rfl, -⟩
    · cases hw
    cases hw
    have h := hy.2.1 q b hq rfl
    show -((m.natAbs * q : Nat) : Int) ≤ m * b - m * ry.c * v - uval ν (uScale m ry.u) ∧
      m * b - m * ry.c * v - uval ν (uScale m ry.u) ≤ ((m.natAbs * q : Nat) : Int)
    rw [uval_uScale, Int.mul_assoc, ← Int.mul_sub, ← Int.mul_sub]
    exact int_mul_bound m _ q h.1 h.2

theorem ZRelK.mulR {rx ry : ZL} {m : Int} {n : Nat} {X X' Y Y' : Option Int}
    (hx : ZRelK ν rx v v' X X') (hy : ZRelK ν ry v v' Y Y') (hm : ry.k = some m) :
    ZRelK ν ⟨rx.c * m, rx.b.map (· * m.natAbs), n, none, uScale m rx.u⟩ v v'
      (do some (BinOp.evalZ .mul (← X) (← Y))) (do some (BinOp.evalZ .mul (← X') (← Y'))) := by
  obtain ⟨rfl, rfl⟩ := hy.2.2 m hm
  refine ⟨?_, ?_, fun _ h => nomatch h⟩
  · rcases hx.cases with ⟨rfl, rfl⟩ | ⟨a, a', rfl, rfl, ha⟩
    · rfl
    show some (a * m - rx.c * m * v) = some (a' * m - rx.c * m * v')
    rw [Int.mul_comm rx.c m, Int.mul_assoc, Int.mul_assoc, Int.mul_comm a m, Int.mul_comm a' m,
      ← Int.mul_sub, ← Int.mul_sub, ha]
  · intro B w hB hw
    simp only [Option.map_eq_some_iff] at hB
    obtain ⟨p, hp, rfl⟩ := hB
    rcases hx.cases with ⟨rfl, rfl⟩ | ⟨a, a', rfl, rfl, -⟩
    · cases hw
    cases hw
    have h := hx.2.1 p a hp rfl
    show -((p * m.natAbs : Nat) : Int) ≤ a * m - rx.c * m * v - uval ν (uScale m rx.u) ∧
      a * m - rx.c * m * v - uval ν (uScale m rx.u) ≤ ((p * m.natAbs : Nat) : Int)
    rw [uval_uScale, Int.mul_comm rx.c m, Int.mul_assoc, Int.mul_comm a m, ← Int.mul_sub,
      ← Int.mul_sub, Nat.mul_comm]
    exact int_mul_bound m _ p h.1 h.2

theorem ZRelK.mul0 {rx ry : ZL} {n : Nat} {X X' Y Y' : Option Int} (hx : ZRelK ν rx v v' X X')
    (hy : ZRelK ν ry v v' Y Y') (hcx : rx.c = 0) (hcy : ry.c = 0) :
    ZRelK ν ⟨0, (if rx.u = [] ∧ ry.u = [] then rx.b.bind fun p => ry.b.map (p * ·) else none),
        n, none, []⟩ v v'
      (do some (BinOp.evalZ .mul (← X) (← Y))) (do some (BinOp.evalZ .mul (← X') (← Y'))) := by
  rw [← hx.eq_of_c hcx, ← hy.eq_of_c hcy]
  refine ZRelK.of_eq fun B w hB hw => ?_
  split at hB
  · next hu =>
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hB
    obtain ⟨p, hp, q, hq, rfl⟩ := hB
    have hx' := hx.2.1
    have hy' := hy.2.1
    rw [hcx, hu.1] at hx'
    rw [hcy, hu.2] at hy'
    rcases hx.cases with ⟨rfl, -⟩ | ⟨a, a', rfl, -, -⟩
    · cases hw
    rcases hy.cases with ⟨rfl, -⟩ | ⟨b, b', rfl, -, -⟩
    · cases hw
    cases hw
    have h1 := hx' p a hp rfl
    have h2 := hy' q b hq rfl
    simp only [Int.zero_mul, Int.sub_zero, uval] at h1 h2
    have h : (a * b).natAbs ≤ p * q := by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul (by omega) (by omega)
    show -((p * q : Nat) : Int) ≤ a * b - 0 ∧ a * b - 0 ≤ ((p * q : Nat) : Int)
    omega
  · cases hB

/-- A comparison reads its sides' difference. -/
theorem BinOp.cmpZ_sub (op : BinOp) (a b : Int) : op.cmpZ a b = op.cmpZ (a - b) 0 := by
  cases op <;> simp only [BinOp.cmpZ] <;>
    first | rfl | (apply decide_eq_decide.2; omega) | (congr 1; apply decide_eq_decide.2; omega)

/-- **Past `R` the sign is the coefficient's**: two values `ZSim` alike
give `c·z + ρ` one sign, `|ρ| ≤ R`. -/
theorem zsign {R : Nat} {c ρ : Int} (hv : ZSim R v v') (h1 : -(R : Int) ≤ ρ) (h2 : ρ ≤ R) :
    (0 < c * v + ρ ↔ 0 < c * v' + ρ) ∧ (c * v + ρ < 0 ↔ c * v' + ρ < 0) := by
  rcases hv with rfl | ⟨hv, hv'⟩ | ⟨hv, hv'⟩
  · exact ⟨Iff.rfl, Iff.rfl⟩
  · rcases Int.lt_trichotomy c 0 with hc | rfl | hc
    · have e1 : c * v ≤ (-1) * v := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      have e2 : c * v' ≤ (-1) * v' := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      omega
    · simp only [Int.zero_mul, Int.zero_add, iff_self, and_self]
    · have e1 : 1 * v ≤ c * v := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      have e2 : 1 * v' ≤ c * v' := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      omega
  · rcases Int.lt_trichotomy c 0 with hc | rfl | hc
    · have e1 : (-1) * v ≤ c * v := Int.mul_le_mul_of_nonpos_right (by omega) (by omega)
      have e2 : (-1) * v' ≤ c * v' := Int.mul_le_mul_of_nonpos_right (by omega) (by omega)
      omega
    · simp only [Int.zero_mul, Int.zero_add, iff_self, and_self]
    · have e1 : c * v ≤ 1 * v := Int.mul_le_mul_of_nonpos_right (by omega) (by omega)
      have e2 : c * v' ≤ 1 * v' := Int.mul_le_mul_of_nonpos_right (by omega) (by omega)
      omega

theorem ZRelK.cmp {R : Nat} {rx ry : ZL} (hv : ZSim R v v') (op : BinOp) {X X' Y Y' : Option Int}
    (hx : ZRelK ν rx v v' X X') (hy : ZRelK ν ry v v' Y Y')
    (hb : rx.c = ry.c ∨ ∃ p q, rx.b = some p ∧ ry.b = some q ∧ uSub rx.u ry.u = [] ∧ p + q ≤ R) :
    (do some (op.cmpZ (← X) (← Y))) = (do some (op.cmpZ (← X') (← Y')) : Option Bool) := by
  rcases hx.cases with ⟨hX, hX'⟩ | ⟨a, a', hX, hX', ha⟩
  · rw [hX, hX']; rfl
  rcases hy.cases with ⟨hY, hY'⟩ | ⟨b, b', hY, hY', hb'⟩
  · rw [hX, hX', hY, hY']; rfl
  rw [hX, hX', hY, hY']
  show some (op.cmpZ a b) = some (op.cmpZ a' b')
  rw [op.cmpZ_sub a b, op.cmpZ_sub a' b']
  congr 1
  rcases hb with hc | ⟨p, q, hp, hq, hu, hpq⟩
  · rw [hc] at ha
    have : a - b = a' - b' := by omega
    rw [this]
  · have h1 := hx.2.1 p a hp hX
    have h2 := hy.2.1 q b hq hY
    have hu' : uval ν rx.u - uval ν ry.u = 0 := by rw [← uval_uSub, hu]; rfl
    have hs := zsign (c := rx.c - ry.c) (ρ := (a - rx.c * v) - (b - ry.c * v)) hv (by omega)
      (by omega)
    have e1 : a - b = (rx.c - ry.c) * v + ((a - rx.c * v) - (b - ry.c * v)) := by
      rw [Int.sub_mul]; omega
    have e2 : a' - b' = (rx.c - ry.c) * v' + ((a - rx.c * v) - (b - ry.c * v)) := by
      rw [Int.sub_mul]; omega
    rw [← e1, ← e2] at hs
    cases op <;> simp only [BinOp.cmpZ] <;>
      first | rfl | (apply decide_eq_decide.2; omega) | (congr 1; apply decide_eq_decide.2; omega)

end Arith

/-! ### Symbols -/

section Symbols

variable {ν : AKey → Int} {v v' : Int}

theorem ZRelK.toInt {n : Nat} {X : Option PrimTy.uint.Denote} :
    ZRelK ν ⟨0, some (2 ^ 256 - 1), n, none, []⟩ v v' (X.map fun n => n.1) (X.map fun n => n.1) := by
  refine ZRelK.of_eq fun B w hB hw => ?_
  cases hB
  obtain ⟨u, -, rfl⟩ := Option.map_eq_some_iff.1 hw
  have h := u.2
  simp only [PrimTy.inRange, decide_eq_true_eq] at h
  have : ((2 ^ 256 - 1 : Nat) : Int) = ((2 ^ 256 : Nat) : Int) - 1 := by omega
  simp only [uval, Int.sub_zero]
  rw [this]; omega

/-- **A unary symbol keeps the relation**: no unary symbol reads KeY's
`int`, so its operand's readings are equal. -/
theorem Op1.zl_rel (g : State C []) {a s : Srt} (o : Op1 C a s) {rx : ZL}
    {X X' : Option (a.Den C g.H)} {D D' : a.TDen C}
    (hX : ZRel ν rx v v' a X X') (hD : ZRelD ν rx v v' a D D') :
    ZRel ν (⟨0, o.zlB, rx.n, none, []⟩ : ZL) v v' s (o.eval g X) (o.eval g X') ∧
      ZRelD ν (⟨0, o.zlB, rx.n, none, []⟩ : ZL) v v' s (o.denote g D) (o.denote g D') := by
  cases o
  all_goals
    have hX := (ZRel.iff_eq (by simp)).1 hX
    have hD := (ZRelD.iff_eq (by simp)).1 hD
    subst hX hD
  case net =>
    exact ⟨ZRelK.of_eq (fun _ _ hB => by cases hB), ZRelK.of_eq (fun _ _ hB => by cases hB)⟩
  case toInt => exact ⟨ZRelK.toInt, ZRelK.toInt⟩
  all_goals exact ⟨(ZRel.iff_eq (by simp)).2 rfl, (ZRelD.iff_eq (by simp)).2 rfl⟩

theorem Op2.zl_n {a b s : Srt} {o : Op2 C a b s} {x y r : ZL} (h : o.zl x y = some r) :
    max x.n y.n ≤ r.n := by
  unfold Op2.zl at h
  split at h
  all_goals (repeat' split at h)
  all_goals first
    | (cases h; simp only [ZL.flat]; omega)
    | (cases h)

/-- **A binary symbol keeps the relation**: `+`, `-` and the products
`Op2.zl` takes shift the coefficient, a comparison reads its sides alike
(`ZRelK.cmp`), and every other symbol reads equal operands. -/
theorem Op2.zl_rel {R : Nat} (hv : ZSim R v v') (g : State C []) {a b s : Srt} (o : Op2 C a b s)
    {rx ry r : ZL} (ho : o.zl rx ry = some r) (hn : r.n ≤ R)
    {X X' : Option (a.Den C g.H)} {Y Y' : Option (b.Den C g.H)} {DX DX' : a.TDen C}
    {DY DY' : b.TDen C}
    (hX : ZRel ν rx v v' a X X') (hDX : ZRelD ν rx v v' a DX DX')
    (hY : ZRel ν ry v v' b Y Y') (hDY : ZRelD ν ry v v' b DY DY') :
    ZRel ν r v v' s (o.eval g X Y) (o.eval g X' Y') ∧
      ZRelD ν r v v' s (o.denote g X Y DX DY) (o.denote g X' Y' DX' DY') := by
  cases o
  case zbin op hop =>
    cases op <;> simp only [Op2.zl] at ho
    case add => cases ho; exact ⟨ZRelK.add hX hY, ZRelK.add hDX hDY⟩
    case sub => cases ho; exact ⟨ZRelK.sub hX hY, ZRelK.sub hDX hDY⟩
    case mul =>
      split at ho
      next m _ hm => cases ho; exact ⟨ZRelK.mulL hX hm hY, ZRelK.mulL hDX hm hDY⟩
      next m _ hm => cases ho; exact ⟨ZRelK.mulR hX hY hm, ZRelK.mulR hDX hDY hm⟩
      next =>
        split at ho
        next hc => cases ho; exact ⟨ZRelK.mul0 hX hY hc.1 hc.2, ZRelK.mul0 hDX hDY hc.1 hc.2⟩
        next => cases ho
    all_goals cases ho
  case zcmp op hop =>
    have hb : rx.c = ry.c ∨
        ∃ p q, rx.b = some p ∧ ry.b = some q ∧ uSub rx.u ry.u = [] ∧ p + q ≤ R := by
      simp only [Op2.zl] at ho
      split at ho
      next hc => exact .inl hc
      next =>
        split at ho
        next p q hp hq =>
          split at ho
          next hu =>
            cases ho
            simp only [ZL.flat] at hn
            exact .inr ⟨p, q, hp, hq, hu, by omega⟩
          next => cases ho
        next => cases ho
    exact ⟨(ZRel.iff_eq (by simp)).2 (ZRelK.cmp hv op hX hY hb),
      (ZRelD.iff_eq (by simp)).2 (ZRelK.cmp hv op hDX hDY hb)⟩
  all_goals
    simp only [Op2.zl] at ho
    cases ho
    have hX := (ZRel.iff_eq (by simp)).1 hX
    have hDX := (ZRelD.iff_eq (by simp)).1 hDX
    have hY := (ZRel.iff_eq (by simp)).1 hY
    have hDY := (ZRelD.iff_eq (by simp)).1 hDY
    subst hX hDX hY hDY
    exact ⟨(ZRel.iff_eq (by simp)).2 rfl, (ZRelD.iff_eq (by simp)).2 rfl⟩

/-- No ternary symbol reads or returns KeY's `int`. -/
theorem Op3.zl_rel (g : State C []) {a b c s : Srt} (o : Op3 C a b c s) {rx ry rz : ZL} {n : Nat}
    {X X' : Option (a.Den C g.H)} {Y Y' : Option (b.Den C g.H)} {Z Z' : Option (c.Den C g.H)}
    {DX DX' : a.TDen C} {DY DY' : b.TDen C} {DZ DZ' : c.TDen C}
    (hX : ZRel ν rx v v' a X X') (hDX : ZRelD ν rx v v' a DX DX')
    (hY : ZRel ν ry v v' b Y Y') (hDY : ZRelD ν ry v v' b DY DY')
    (hZ : ZRel ν rz v v' c Z Z') (hDZ : ZRelD ν rz v v' c DZ DZ') :
    ZRel ν (ZL.flat n) v v' s (o.eval g X Y Z) (o.eval g X' Y' Z') ∧
      ZRelD ν (ZL.flat n) v v' s (o.denote DX DY DZ) (o.denote DX' DY' DZ') := by
  cases o
  all_goals
    have hX := (ZRel.iff_eq (by simp)).1 hX
    have hDX := (ZRelD.iff_eq (by simp)).1 hDX
    have hY := (ZRel.iff_eq (by simp)).1 hY
    have hDY := (ZRelD.iff_eq (by simp)).1 hDY
    have hZ := (ZRel.iff_eq (by simp)).1 hZ
    have hDZ := (ZRelD.iff_eq (by simp)).1 hDZ
    subst hX hDX hY hDY hZ hDZ
    exact ⟨(ZRel.iff_eq (by simp)).2 rfl, (ZRelD.iff_eq (by simp)).2 rfl⟩

end Symbols

/-! ### Terms -/

/-- Two positions of one type at one depth are one. -/
theorem Idx.eq_of_toNat_eq {t : LTy} : {Γ : Ctx} → (i j : Idx Γ t) → i.toNat = j.toNat → i = j
  | _, .here, .here, _ => rfl
  | _, .here, .there j, h => absurd h (by simp only [Idx.toNat]; omega)
  | _, .there i, .here, h => absurd h (by simp only [Idx.toNat]; omega)
  | _, .there i, .there j, h => by
    rw [Idx.eq_of_toNat_eq i j (by simpa only [Idx.toNat, Nat.add_right_cancel_iff] using h)]

/-- A local of another type than `zi`'s is not set by setting `zi`. -/
theorem TEnv.get_setLocal_ne {H : HTy} {Γ : Ctx} {t : LTy} (zi : Idx Γ .kint) (i : Idx Γ t)
    (ht : t ≠ .kint) (w : Int) (e : TEnv C H Γ) : TEnv.get i (TEnv.set zi w e) = TEnv.get i e :=
  TEnv.get_set_ne zi i w e fun h => ht (Idx.ty_eq_of_toNat h).symm

/-- The local of KeY's `int` at a position. -/
def TEnv.kAt {H : HTy} : {Γ : Ctx} → TEnv C H Γ → Nat → Option Int
  | [], _, _ => none
  | t :: _, e, 0 => match t, e with
    | .kint, e => some e.1
    | _, _ => none
  | _ :: _, e, n + 1 => TEnv.kAt e.2 n

/-- The `uint` local at a position. -/
def TEnv.uAt {H : HTy} : {Γ : Ctx} → TEnv C H Γ → Nat → Option PrimTy.uint.Denote
  | [], _, _ => none
  | t :: _, e, 0 => match t, e with
    | .val .uint, e => some e.1
    | _, _ => none
  | _ :: _, e, n + 1 => TEnv.uAt e.2 n

theorem TEnv.kAt_get {H : HTy} : {Γ : Ctx} → (i : Idx Γ .kint) → (e : TEnv C H Γ) →
    TEnv.kAt e i.toNat = some (TEnv.get i e)
  | _, .here, _ => rfl
  | _ :: _, .there i, e => TEnv.kAt_get i e.2

theorem TEnv.uAt_get {H : HTy} : {Γ : Ctx} → (i : Idx Γ (.val .uint)) → (e : TEnv C H Γ) →
    TEnv.uAt e i.toNat = some (TEnv.get i e)
  | _, .here, _ => rfl
  | _ :: _, .there i, e => TEnv.uAt_get i e.2

/-- **The keys' values in a state.** -/
def State.zν {Γ : Ctx} (σ : State C Γ) : AKey → Int
  | .loc n => (TEnv.kAt σ.env n).getD 0
  | .netL n => ((TEnv.uAt σ.env n).map fun a => (Semantics.lookupBy a σ.net).getD 0).getD 0
  | .netC v => (Semantics.lookupBy v σ.net).getD 0

/-- A ledger entry at a key's address reads the key's value, whatever `zi` holds. -/
theorem Tm.netKey?_rel {Γ : Ctx} (zi : Idx Γ .kint) (σ : State C Γ) (w : Int)
    (x : Tm C Γ (.val .uint)) {κ : AKey} (h : x.netKey? = some κ) :
    (Tm.app1 .net x).eval (σ.setLocal zi w) = some (σ.zν κ) ∧
      (Tm.app1 .net x).denote (σ.setLocal zi w) = some (σ.zν κ) := by
  match x, h with
  | .pvV i, h =>
    cases h
    have e := TEnv.get_setLocal_ne (C := C) zi i (by simp) w σ.env (H := σ.H)
    have hu := TEnv.uAt_get i σ.env
    refine ⟨?_, ?_⟩
    · show some ((Semantics.lookupBy (TEnv.get i (TEnv.set zi w σ.env)) σ.net).getD 0) = _
      rw [e]; simp only [State.zν, hu, Option.map_some, Option.getD_some]
    · show some ((Semantics.lookupBy (TEnv.get i (TEnv.set zi w σ.env)) σ.net).getD 0) = _
      rw [e]; simp only [State.zν, hu, Option.map_some, Option.getD_some]
  | .app0 (.lit v), h =>
    cases h
    exact ⟨rfl, rfl⟩
  | .app0 (.env _), h | .app1 _ _, h | .app2 _ _ _, h | .app3 _ _ _ _, h =>
    exact absurd h (by simp only [Tm.netKey?, reduceCtorEq, not_false_eq_true])

/-- **A term linear in `zi` reads alike at two values the comparisons do
not tell apart**: equal past `c·zi` where it is of KeY's `int`, its keys at
their values in `σ`, equal otherwise. -/
theorem Tm.zl_rel {Γ : Ctx} (zi : Idx Γ .kint) {R : Nat} (σ : State C Γ) {v v' : Int}
    (hv : ZSim R v v') : {s : Srt} → (t : Tm C Γ s) → {r : ZL} → t.zl zi = some r → r.n ≤ R →
      ZRel σ.zν r v v' s (t.eval (σ.setLocal zi v)) (t.eval (σ.setLocal zi v')) ∧
        ZRelD σ.zν r v v' s (t.denote (σ.setLocal zi v)) (t.denote (σ.setLocal zi v'))
  | _, .pvV i, r, h, _ => by
    simp only [Tm.zl, Option.some.injEq] at h; subst h
    have e := TEnv.get_setLocal_ne (C := C) zi i (by simp) (H := σ.H)
    refine ⟨(ZRel.iff_eq (by simp)).2 ?_, (ZRelD.iff_eq (by simp)).2 ?_⟩
    · show some (TEnv.get i (TEnv.set zi v σ.env)) = some (TEnv.get i (TEnv.set zi v' σ.env))
      rw [e, e]
    · show some (TEnv.get i (TEnv.set zi v σ.env)) = some (TEnv.get i (TEnv.set zi v' σ.env))
      rw [e, e]
  | _, .pvP i, r, h, _ => by
    simp only [Tm.zl, Option.some.injEq] at h; subst h
    have e := TEnv.get_setLocal_ne (C := C) zi i (by simp) (H := σ.H)
    refine ⟨(ZRel.iff_eq (by simp)).2 ?_, (ZRelD.iff_eq (by simp)).2 ?_⟩
    · show TEnv.get i (TEnv.set zi v σ.env) = TEnv.get i (TEnv.set zi v' σ.env)
      rw [e, e]
    · rw [Tm.denote_pvP, Tm.denote_pvP]
      show ((LTy.VDen.ofT _ (TEnv.get i (TEnv.set zi v σ.env))).map SLoc.ref).getD _ =
        ((LTy.VDen.ofT _ (TEnv.get i (TEnv.set zi v' σ.env))).map SLoc.ref).getD _
      rw [e, e]
  | _, .pvS i, r, h, _ => by
    simp only [Tm.zl, Option.some.injEq] at h; subst h
    have e := TEnv.get_setLocal_ne (C := C) zi i (by simp) (H := σ.H)
    refine ⟨(ZRel.iff_eq (by simp)).2 ?_, (ZRelD.iff_eq (by simp)).2 ?_⟩
    · show some (TEnv.get i (TEnv.set zi v σ.env)) = some (TEnv.get i (TEnv.set zi v' σ.env))
      rw [e, e]
    · simp only [Tm.denote, State.setLocal, e]
  | _, .pvI i, r, h, _ => by
    simp only [Tm.zl, Option.some.injEq] at h; subst h
    have e := TEnv.get_setLocal_ne (C := C) zi i (by simp) (H := σ.H)
    refine ⟨(ZRel.iff_eq (by simp)).2 ?_, (ZRelD.iff_eq (by simp)).2 rfl⟩
    show (TEnv.get i (TEnv.set zi v σ.env)).map (·.id) = (TEnv.get i (TEnv.set zi v' σ.env)).map (·.id)
    rw [e, e]
  | _, .netOf i a, r, h, hn => by
    simp only [Tm.zl, Option.map_eq_some_iff] at h
    obtain ⟨ra, ha, rfl⟩ := h
    have ih := Tm.zl_rel zi σ hv a ha (by simpa only [ZL.flat] using hn)
    have hE := (ZRel.iff_eq (by simp)).1 ih.1
    have hD := (ZRelD.iff_eq (by simp)).1 ih.2
    have e := TEnv.get_setLocal_ne (C := C) zi i (by simp) (H := σ.H)
    refine ⟨?_, ?_⟩
    · show ZRelK _ _ v v' ((a.eval (σ.setLocal zi v)).bind (Tm.netOfT (TEnv.get i (TEnv.set zi v σ.env))))
        ((a.eval (σ.setLocal zi v')).bind (Tm.netOfT (TEnv.get i (TEnv.set zi v' σ.env))))
      rw [e, e, hE]
      exact ZRelK.of_eq fun _ _ hB => by cases hB
    · show ZRelK _ _ v v' ((a.denote (σ.setLocal zi v)).map fun n =>
          (Semantics.lookupBy n (TEnv.get i (TEnv.set zi v σ.env) : Ledger)).getD 0)
        ((a.denote (σ.setLocal zi v')).map fun n =>
          (Semantics.lookupBy n (TEnv.get i (TEnv.set zi v' σ.env) : Ledger)).getD 0)
      rw [e, e, hD]
      exact ZRelK.of_eq fun _ _ hB => by cases hB
  | _, .pvZ i, r, h, _ => by
    simp only [Tm.zl, Option.some.injEq] at h; subst h
    split
    · rename_i hi
      cases Idx.eq_of_toNat_eq i zi hi
      have e : ∀ w : Int, TEnv.get zi (TEnv.set zi w σ.env) = w := fun w => TEnv.get_set zi w σ.env
      have key : ZRelK σ.zν ⟨1, some 0, 0, none, []⟩ v v' (some (TEnv.get zi (TEnv.set zi v σ.env)))
          (some (TEnv.get zi (TEnv.set zi v' σ.env))) := by
        rw [e, e]
        refine ⟨?_, ?_, fun _ h => nomatch h⟩
        · simp only [Option.map_some, Int.one_mul, Int.sub_self]
        · intro B w hB hw
          cases hB; cases hw
          simp only [Int.one_mul, Int.sub_self, uval]; omega
      exact ⟨key, key⟩
    · rename_i hi
      have e : ∀ w : Int, TEnv.get i (TEnv.set zi w σ.env) = TEnv.get i σ.env := fun w =>
        TEnv.get_set_ne zi i w σ.env (Ne.symm hi)
      have hk := TEnv.kAt_get i σ.env
      have key : ZRelK σ.zν ⟨0, some 0, 0, none, [(.loc i.toNat, 1)]⟩ v v'
          (some (TEnv.get i (TEnv.set zi v σ.env))) (some (TEnv.get i (TEnv.set zi v' σ.env))) := by
        rw [e, e]
        refine ZRelK.of_eq fun B w hB hw => ?_
        cases hB; cases hw
        simp only [uval, State.zν, hk, Option.getD_some, Int.one_mul, Int.add_zero, Int.sub_self]
        omega
      exact ⟨key, key⟩
  | _, .app0 o, r, h, hn => by
    simp only [Tm.zl, Option.some.injEq] at h; subst h
    cases o
    case zlit m =>
      have key : ZRelK σ.zν ⟨0, some m.natAbs, 0, some m, []⟩ v v' (some m) (some m) :=
        ⟨by simp only [Option.map_some, Int.zero_mul, Int.sub_zero],
          fun B w hB hw => by
            cases hB; cases hw; simp only [Int.zero_mul, Int.sub_zero, uval]; omega,
          fun _ h => by cases h; exact ⟨rfl, rfl⟩⟩
      exact ⟨key, key⟩
    all_goals exact ⟨(ZRel.iff_eq (by simp)).2 rfl, (ZRelD.iff_eq (by simp)).2 rfl⟩
  | _, .app1 o x, r, h, hn => by
    simp only [Tm.zl, Option.map_eq_some_iff] at h
    obtain ⟨rx, hx, rfl⟩ := h
    have hn' : rx.n ≤ R := by split at hn <;> exact hn
    have ih := Tm.zl_rel zi σ hv x hx hn'
    split
    · next κ hκ =>
      cases o
      case net =>
        have hk := Tm.netKey?_rel zi σ v x hκ
        have hk' := Tm.netKey?_rel zi σ v' x hκ
        have key : ZRelK σ.zν ⟨0, some 0, rx.n, none, [(κ, 1)]⟩ v v' (some (σ.zν κ)) (some (σ.zν κ)) :=
          ZRelK.of_eq fun B w hB hw => by
            cases hB; cases hw; simp only [uval, Int.one_mul, Int.add_zero, Int.sub_self]; omega
        refine ⟨?_, ?_⟩
        · show ZRelK _ _ v v' ((Tm.app1 .net x).eval _) ((Tm.app1 .net x).eval _)
          rw [hk.1, hk'.1]; exact key
        · show ZRelK _ _ v v' ((Tm.app1 .net x).denote _) ((Tm.app1 .net x).denote _)
          rw [hk.2, hk'.2]; exact key
      all_goals exact absurd hκ (by simp only [Op1.zlK, reduceCtorEq, not_false_eq_true])
    · exact Op1.zl_rel σ.glob o ih.1 ih.2
  | _, .app2 o x y, r, h, hn => by
    simp only [Tm.zl, Option.bind_eq_some_iff] at h
    obtain ⟨rx, hx, ry, hy, ho⟩ := h
    have hm := Op2.zl_n ho
    have ihx := Tm.zl_rel zi σ hv x hx (by omega)
    have ihy := Tm.zl_rel zi σ hv y hy (by omega)
    exact Op2.zl_rel hv σ.glob o ho hn ihx.1 ihx.2 ihy.1 ihy.2
  | _, .app3 o x y z, r, h, hn => by
    simp only [Tm.zl, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨rx, hx, ry, hy, rz, hz, rfl⟩ := h
    simp only [ZL.flat] at hn
    have ihx := Tm.zl_rel zi σ hv x hx (by omega)
    have ihy := Tm.zl_rel zi σ hv y hy (by omega)
    have ihz := Tm.zl_rel zi σ hv z hz (by omega)
    exact Op3.zl_rel σ.glob o ihx.1 ihx.2 ihy.1 ihy.2 ihz.1 ihz.2

/-! ### Formulas -/

/-- **A formula linear in `zi`**: its terms are (`Tm.zl`), under value and
local binders; the largest bound its comparisons need. -/
def Fml.zl : {Γ : Ctx} → Idx Γ .kint → Fml C Γ → Option Nat
  | _, _, .tt => some 0
  | _, zi, .eq a b => (a.zl zi).bind fun ra => (b.zl zi).map fun rb => max ra.n rb.n
  | _, zi, .wellFormed s => (s.zl zi).map (·.n)
  | _, zi, .not φ => φ.zl zi
  | _, zi, .and φ ψ | _, zi, .imp φ ψ => (φ.zl zi).bind fun n => (ψ.zl zi).map (max n)
  | _, zi, .all _ _ φ => φ.zl zi.there
  | _, zi, .bind _ _ _ φ => φ.zl zi.there
  | _, _, _ => none

/-- **A formula linear in `zi` holds alike at two values its comparisons
do not tell apart.** -/
theorem Fml.zl_holds {R : Nat} {Γ : Ctx} (φ : Fml C Γ) : (zi : Idx Γ .kint) → {n : Nat} →
    φ.zl zi = some n → n ≤ R → (σ : State C Γ) → {v v' : Int} → ZSim R v v' →
      (holds (σ.setLocal zi v) φ ↔ holds (σ.setLocal zi v') φ) := by
  induction φ with
  | tt => intro _ _ _ _ _ _ _ _; exact Iff.rfl
  | eq a b =>
    intro zi n h hn σ v v' hv
    simp only [Fml.zl, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ra, ha, rb, hb, rfl⟩ := h
    have ia := (ZRelD.iff_eq (by simp)).1 (Tm.zl_rel zi σ hv a ha (by omega)).2
    have ib := (ZRelD.iff_eq (by simp)).1 (Tm.zl_rel zi σ hv b hb (by omega)).2
    rw [holds_eq, holds_eq, ia, ib]
  | wellFormed s =>
    intro zi n h hn σ v v' hv
    simp only [Fml.zl, Option.map_eq_some_iff] at h
    obtain ⟨rs, hs, rfl⟩ := h
    have is := (ZRel.iff_eq (by simp)).1 (Tm.zl_rel zi σ hv s hs hn).1
    rw [holds_wellFormed, holds_wellFormed, is]
  | not φ ih =>
    intro zi n h hn σ v v' hv
    exact not_congr (ih zi h hn σ hv)
  | and φ ψ ihφ ihψ =>
    intro zi n h hn σ v v' hv
    simp only [Fml.zl, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨n₁, h₁, n₂, h₂, rfl⟩ := h
    exact and_congr (ihφ zi h₁ (by omega) σ hv) (ihψ zi h₂ (by omega) σ hv)
  | imp φ ψ ihφ ihψ =>
    intro zi n h hn σ v v' hv
    simp only [Fml.zl, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨n₁, h₁, n₂, h₂, rfl⟩ := h
    exact imp_congr (ihφ zi h₁ (by omega) σ hv) (ihψ zi h₂ (by omega) σ hv)
  | all x p φ ih =>
    intro zi n h hn σ v v' hv
    exact forall_congr' fun u => ih zi.there h hn (σ.push (t := .val p) u) hv
  | bind m x t φ ih =>
    intro zi n h hn σ v v' hv
    exact forall_congr' fun u => ih zi.there h hn (σ.push (t := t) u) hv
  | upd | modal | havoc | anon | allocAll | grow => intro _ _ h; cases h

/-- A value clamped to `[-(n+1), n+1]`. -/
def zclamp (n : Nat) (v : Int) : Int := max (-((n : Int) + 1)) (min ((n : Int) + 1) v)

theorem zsim_clamp (n : Nat) (v : Int) : ZSim n v (zclamp n v) := by
  unfold ZSim zclamp
  by_cases h1 : (n : Int) < v
  · exact .inr (.inl ⟨h1, by omega⟩)
  · by_cases h2 : v < -(n : Int)
    · exact .inr (.inr ⟨h2, by omega⟩)
    · exact .inl (by omega)

/-- **The binder's body holds at `z` exactly where it holds at `z`
clamped.** -/
theorem Fml.zl_clamp {Γ : Ctx} {A : Fml C (.kint :: Γ)} {n : Nat} (h : A.zl .here = some n)
    (σ : State C Γ) (v : Int) :
    holds (σ.push (t := .kint) v) A ↔ holds (σ.push (t := .kint) (zclamp n v)) A :=
  Fml.zl_holds A .here h (Nat.le_refl n) (σ.push (t := .kint) 0) (zsim_clamp n v)

/-! ## Substitution -/

/-- Where a local is sent: a local, or, for one of KeY's `int`, a term. -/
inductive SbT (C : Contract) (Δ : Ctx) : LTy → Type where
  | idx {t : LTy} (i : Idx Δ t) : SbT C Δ t
  | tm (e : Tm C Δ .kint) : SbT C Δ .kint

/-- **A substitution**: each local of `Γ` sent to a local of `Δ` at its
type, or, for one of KeY's `int`, to a term. -/
structure Sb (C : Contract) (Γ Δ : Ctx) where
  f : {t : LTy} → Idx Γ t → SbT C Δ t

/-- One binder further out. -/
def SbT.up {Δ : Ctx} {t : LTy} (u : LTy) : SbT C Δ t → SbT C (u :: Δ) t
  | .idx i => .idx (.there i)
  | .tm e => .tm (e.ren (Ren.up u))

/-- Under one more binder. -/
def Sb.lift {Γ Δ : Ctx} (r : Sb C Γ Δ) (u : LTy) : Sb C (u :: Γ) (u :: Δ) where
  f := fun {_} i => match i with
    | .here => .idx .here
    | .there j => (r.f j).up u

/-- Past the innermost local. -/
def Sb.tail {Γ Δ : Ctx} {u : LTy} (r : Sb C (u :: Γ) Δ) : Sb C Γ Δ := ⟨fun j => r.f (.there j)⟩

/-- **A term, its locals substituted.** -/
def Tm.sb {Γ Δ : Ctx} (r : Sb C Γ Δ) : {s : Srt} → Tm C Γ s → Tm C Δ s
  | _, .pvV i => match r.f i with | .idx j => .pvV j
  | _, .pvP i => match r.f i with | .idx j => .pvP j
  | _, .pvS i => match r.f i with | .idx j => .pvS j
  | _, .pvI i => match r.f i with | .idx j => .pvI j
  | _, .netOf i a => match r.f i with | .idx j => .netOf j (a.sb r)
  | _, .app0 o => .app0 o
  | _, .app1 o a => .app1 o (a.sb r)
  | _, .app2 o a b => .app2 o (a.sb r) (b.sb r)
  | _, .app3 o a b c => .app3 o (a.sb r) (b.sb r) (c.sb r)
  | _, .pvZ i => match r.f i with
    | .idx j => .pvZ j
    | .tm e => e

/-- What a local is sent to, read in `σ`. -/
def SbT.val {Δ : Ctx} (σ : State C Δ) {t : LTy} : SbT C Δ t → t.TDenote C σ.H
  | .idx j => TEnv.get j σ.env
  | .tm e => ((e.eval σ).getD 0 : Int)

/-- The locals pulled back along a substitution. -/
def TEnv.sbPull {Δ : Ctx} (σ : State C Δ) : {Γ : Ctx} → Sb C Γ Δ → TEnv C σ.H Γ
  | [], _ => ()
  | _ :: _, r => ((r.f .here).val σ, TEnv.sbPull σ r.tail)

theorem TEnv.get_sbPull {Δ : Ctx} (σ : State C Δ) : {Γ : Ctx} → (r : Sb C Γ Δ) → {t : LTy} →
    (i : Idx Γ t) → TEnv.get i (TEnv.sbPull σ r) = (r.f i).val σ
  | _ :: _, _, _, .here => rfl
  | _ :: _, r, _, .there i => TEnv.get_sbPull σ r.tail i

/-- **A state read along a substitution**: its locals pulled back. -/
def State.sbPull {Γ Δ : Ctx} (σ : State C Δ) (r : Sb C Γ Δ) : State C Γ :=
  σ.withEnv (TEnv.sbPull σ r)

/-- Every term the substitution sends a local to returns, alike in the
Theory. -/
def Sb.Rets {Γ Δ : Ctx} (r : Sb C Γ Δ) (σ : State C Δ) : Prop :=
  ∀ (i : Idx Γ .kint) (e : Tm C Δ .kint), r.f i = .tm e →
    ∃ w, e.eval σ = some w ∧ e.denote σ = some w

theorem Tm.eval_sb {Γ Δ : Ctx} (r : Sb C Γ Δ) (σ : State C Δ) (hr : r.Rets σ) :
    {s : Srt} → (t : Tm C Γ s) → (t.sb r).eval σ = t.eval (σ.sbPull r)
  | _, .pvV i => by
    show _ = some (TEnv.get i (TEnv.sbPull σ r))
    rw [TEnv.get_sbPull]
    simp only [Tm.sb]
    split
    next j hj => rw [hj]; rfl
  | _, .pvP i => by
    show _ = TEnv.get i (TEnv.sbPull σ r)
    rw [TEnv.get_sbPull]
    simp only [Tm.sb]
    split
    next j hj => rw [hj]; rfl
  | _, .pvS i => by
    show _ = some (TEnv.get i (TEnv.sbPull σ r))
    rw [TEnv.get_sbPull]
    simp only [Tm.sb]
    split
    next j hj => rw [hj]; rfl
  | _, .pvI i => by
    show _ = (TEnv.get i (TEnv.sbPull σ r)).map (·.id)
    rw [TEnv.get_sbPull]
    simp only [Tm.sb]
    split
    next j hj => rw [hj]; rfl
  | _, .netOf i a => by
    show _ = (a.eval (σ.sbPull r)).bind (Tm.netOfT (TEnv.get i (TEnv.sbPull σ r)))
    rw [TEnv.get_sbPull, ← Tm.eval_sb r σ hr a]
    simp only [Tm.sb]
    split
    next j hj => rw [hj]; rfl
  | _, .app0 o => rfl
  | _, .app1 o a => by
    rw [Tm.sb, Tm.eval_app1, Tm.eval_app1, Tm.eval_sb r σ hr a]; rfl
  | _, .app2 o a b => by
    rw [Tm.sb, Tm.eval_app2, Tm.eval_app2, Tm.eval_sb r σ hr a, Tm.eval_sb r σ hr b]; rfl
  | _, .app3 o a b c => by
    rw [Tm.sb, Tm.eval_app3, Tm.eval_app3, Tm.eval_sb r σ hr a, Tm.eval_sb r σ hr b,
      Tm.eval_sb r σ hr c]; rfl
  | _, .pvZ i => by
    show _ = some (TEnv.get i (TEnv.sbPull σ r))
    rw [TEnv.get_sbPull]
    simp only [Tm.sb]
    split
    next j hj => rw [hj]; rfl
    next e he =>
      obtain ⟨w, hw, -⟩ := hr i e he
      rw [he]
      show e.eval σ = some ((e.eval σ).getD 0)
      rw [hw]; rfl

theorem Tm.denote_sb {Γ Δ : Ctx} (r : Sb C Γ Δ) (σ : State C Δ) (hr : r.Rets σ) :
    {s : Srt} → (t : Tm C Γ s) → (t.sb r).denote σ = t.denote (σ.sbPull r)
  | _, .pvV i => by
    show _ = some (TEnv.get i (TEnv.sbPull σ r))
    rw [TEnv.get_sbPull]
    simp only [Tm.sb]
    split
    next j hj => rw [hj]; rfl
  | _, .pvP i => by
    rw [Tm.denote_pvP]
    show _ = ((LTy.VDen.ofT _ (TEnv.get i (TEnv.sbPull σ r))).map SLoc.ref).getD _
    rw [TEnv.get_sbPull]
    simp only [Tm.sb]
    split
    next j hj => rw [hj, Tm.denote_pvP]; rfl
  | _, .pvS i => by
    show _ = Storage.obs (TEnv.get i (TEnv.sbPull σ r) : Storage C)
    rw [TEnv.get_sbPull]
    simp only [Tm.sb]
    split
    next j hj => rw [hj]; rfl
  | _, .pvI i => by
    simp only [Tm.sb]
  | _, .netOf i a => by
    show _ = (a.denote (σ.sbPull r)).map fun n =>
      (Semantics.lookupBy n (TEnv.get i (TEnv.sbPull σ r) : Ledger)).getD 0
    rw [TEnv.get_sbPull, ← Tm.denote_sb r σ hr a]
    simp only [Tm.sb]
    split
    next j hj => rw [hj]; rfl
  | _, .app0 o => rfl
  | _, .app1 o a => by
    show o.denote σ.glob ((a.sb r).denote σ) = o.denote σ.glob (a.denote (σ.sbPull r))
    rw [Tm.denote_sb r σ hr a]
  | _, .app2 o a b => by
    show o.denote σ.glob ((a.sb r).eval σ) ((b.sb r).eval σ) ((a.sb r).denote σ) ((b.sb r).denote σ) =
      o.denote σ.glob (a.eval (σ.sbPull r)) (b.eval (σ.sbPull r)) (a.denote (σ.sbPull r))
        (b.denote (σ.sbPull r))
    rw [Tm.denote_sb r σ hr a, Tm.denote_sb r σ hr b, Tm.eval_sb r σ hr a, Tm.eval_sb r σ hr b]
  | _, .app3 o a b c => by
    show o.denote ((a.sb r).denote σ) ((b.sb r).denote σ) ((c.sb r).denote σ) =
      o.denote (a.denote (σ.sbPull r)) (b.denote (σ.sbPull r)) (c.denote (σ.sbPull r))
    rw [Tm.denote_sb r σ hr a, Tm.denote_sb r σ hr b, Tm.denote_sb r σ hr c]
  | _, .pvZ i => by
    show _ = some (TEnv.get i (TEnv.sbPull σ r))
    rw [TEnv.get_sbPull]
    simp only [Tm.sb]
    split
    next j hj => rw [hj]; rfl
    next e he =>
      obtain ⟨w, hw, hd⟩ := hr i e he
      rw [he]
      show e.denote σ = some ((e.eval σ).getD 0)
      rw [hw, hd]; rfl

/-- **A formula, its locals substituted** (`none` outside the first-order
fragment with binders). -/
def Fml.sb? : {Γ Δ : Ctx} → Sb C Γ Δ → Fml C Γ → Option (Fml C Δ)
  | _, _, _, .tt => some .tt
  | _, _, r, .eq a b => some (.eq (a.sb r) (b.sb r))
  | _, _, r, .wellFormed s => some (.wellFormed (s.sb r))
  | _, _, r, .not φ => (Fml.sb? r φ).map .not
  | _, _, r, .and φ ψ => (Fml.sb? r φ).bind fun φ' => (Fml.sb? r ψ).map fun ψ' => .and φ' ψ'
  | _, _, r, .imp φ ψ => (Fml.sb? r φ).bind fun φ' => (Fml.sb? r ψ).map fun ψ' => .imp φ' ψ'
  | _, _, r, .all x p φ => (Fml.sb? (r.lift _) φ).map (.all x p)
  | _, _, r, .bind m x t φ => (Fml.sb? (r.lift _) φ).map (.bind m x t)
  | _, _, _, _ => none

/-- A pushed state read one binder out is the state. -/
theorem State.pull_up {Δ : Ctx} (σ : State C Δ) {u : LTy} (w : u.TDenote C σ.H) :
    (σ.push w).pull (Ren.up u) = σ := by
  show σ.withEnv (Decide.TEnv.pull (Δ := u :: Δ) ⟨fun j => .there ((Ren.id Δ).f j)⟩ (w, σ.env)) = σ
  rw [Decide.TEnv.pull_there, Decide.TEnv.pull_id]
  rfl

theorem SbT.val_up {Δ : Ctx} (σ : State C Δ) {u : LTy} (w : u.TDenote C σ.H) {t : LTy}
    (x : SbT C Δ t) : (x.up u).val (σ.push w) = x.val σ := by
  cases x with
  | idx i => rfl
  | tm e =>
    show (((e.ren (Ren.up u)).eval (σ.push w)).getD 0 : Int) = (e.eval σ).getD 0
    rw [Tm.eval_ren, State.pull_up]

theorem TEnv.sbPull_up {Δ : Ctx} (σ : State C Δ) {u : LTy} (w : u.TDenote C σ.H) :
    {Γ : Ctx} → (r : Sb C Γ Δ) →
      TEnv.sbPull (σ.push w) (Γ := Γ) ⟨fun j => (r.f j).up u⟩ = TEnv.sbPull σ r
  | [], _ => rfl
  | _ :: _, r => by
    show ((r.f .here).up u |>.val (σ.push w), TEnv.sbPull (σ.push w) ⟨fun j => (r.tail.f j).up u⟩) = _
    rw [SbT.val_up, TEnv.sbPull_up σ w r.tail]
    rfl

theorem State.sbPull_lift {Γ Δ : Ctx} (σ : State C Δ) (r : Sb C Γ Δ) {u : LTy}
    (w : u.TDenote C σ.H) : (σ.push w).sbPull (r.lift u) = (σ.sbPull r).push (t := u) w := by
  show (σ.push w).withEnv (Δ := u :: Γ) (w, TEnv.sbPull (σ.push w) ⟨fun j => (r.f j).up u⟩) = _
  rw [TEnv.sbPull_up]
  rfl

theorem Sb.Rets.lift {Γ Δ : Ctx} {r : Sb C Γ Δ} {σ : State C Δ} (hr : r.Rets σ) {u : LTy}
    (w : u.TDenote C σ.H) : (r.lift u).Rets (σ.push w) := by
  intro i e he
  cases i with
  | here => cases he
  | there j =>
    change (r.f j).up u = .tm e at he
    revert he
    generalize hx : r.f j = x
    cases x with
    | idx _ => intro he; cases he
    | tm e₀ =>
      intro he
      cases he
      obtain ⟨v, hv, hd⟩ := hr j e₀ hx
      refine ⟨v, ?_, ?_⟩
      · rw [Tm.eval_ren, State.pull_up, hv]
      · rw [Tm.denote_ren, State.pull_up, hd]

/-- **A substituted formula holds where the formula does in the pulled-back
state.** -/
theorem Fml.holds_sb {Γ : Ctx} (φ : Fml C Γ) : {Δ : Ctx} → (r : Sb C Γ Δ) → {ψ : Fml C Δ} →
    φ.sb? r = some ψ → ∀ σ : State C Δ, r.Rets σ → (holds σ ψ ↔ holds (σ.sbPull r) φ) := by
  induction φ with
  | tt => intro _ _ _ e _ _; cases e; exact Iff.rfl
  | eq a b =>
    intro _ r _ e σ hr
    cases e
    show (a.sb r).denote σ = (b.sb r).denote σ ↔ a.denote (σ.sbPull r) = b.denote (σ.sbPull r)
    rw [Tm.denote_sb r σ hr, Tm.denote_sb r σ hr]
  | wellFormed s =>
    intro _ r _ e σ hr
    cases e
    rw [holds_wellFormed, holds_wellFormed, Tm.eval_sb r σ hr]
  | not φ ih =>
    intro _ r _ e σ hr
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact not_congr (ih r hφ σ hr)
  | and φ ψ ihφ ihψ =>
    intro _ r _ e σ hr
    obtain ⟨φ', hφ, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact and_congr (ihφ r hφ σ hr) (ihψ r hψ σ hr)
  | imp φ ψ ihφ ihψ =>
    intro _ r _ e σ hr
    obtain ⟨φ', hφ, e⟩ := Option.bind_eq_some_iff.1 e
    obtain ⟨ψ', hψ, rfl⟩ := Option.map_eq_some_iff.1 e
    exact imp_congr (ihφ r hφ σ hr) (ihψ r hψ σ hr)
  | all x p φ ih =>
    intro _ r _ e σ hr
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    show (∀ w : p.Denote, holds (σ.push (t := .val p) w) φ') ↔
      ∀ w : p.Denote, holds ((σ.sbPull r).push (t := .val p) w) φ
    exact forall_congr' fun w =>
      (ih (r.lift _) hφ _ (hr.lift (u := .val p) w)).trans (by rw [State.sbPull_lift])
  | bind m x t φ ih =>
    intro _ r _ e σ hr
    obtain ⟨φ', hφ, rfl⟩ := Option.map_eq_some_iff.1 e
    show (∀ w : t.TDenote C σ.H, holds (σ.push w) φ') ↔
      ∀ w : t.TDenote C σ.H, holds ((σ.sbPull r).push (t := t) w) φ
    exact forall_congr' fun w => (ih (r.lift _) hφ _ (hr.lift w)).trans (by rw [State.sbPull_lift])
  | upd | modal | havoc | anon | allocAll | grow => intro _ _ _ e; cases e


/-! ## The encoding -/

/-- `c·toInt(a) - toInt(b) - off`, `a` the outer of two words. -/
def zEncT {Γ : Ctx} (c off : Nat) : Tm C (.val .uint :: .val .uint :: Γ) .kint :=
  .app2 (.zbin .sub rfl)
    (.app2 (.zbin .sub rfl)
      (.app2 (.zbin .mul rfl) (.app0 (.zlit c)) (.app1 .toInt (.pvV (.there .here))))
      (.app1 .toInt (.pvV .here)))
    (.app0 (.zlit off))

/-- The binder sent to its encoding over two words, the other locals two
binders further out. -/
def encSb {Γ : Ctx} (c off : Nat) : Sb C (.kint :: Γ) (.val .uint :: .val .uint :: Γ) where
  f := fun {_} i => match i with
    | .here => .tm (zEncT c off)
    | .there j => .idx j.there.there

theorem zEncT_eval {Γ : Ctx} (c off : Nat) (σ : State C Γ) (a b : PrimTy.uint.Denote) :
    (zEncT c off).eval ((σ.push (t := .val .uint) a).push (t := .val .uint) b) =
        some ((c : Int) * a.1 - b.1 - off) ∧
      (zEncT c off).denote ((σ.push (t := .val .uint) a).push (t := .val .uint) b) =
        some ((c : Int) * a.1 - b.1 - off) :=
  ⟨rfl, rfl⟩

theorem encSb_rets {Γ : Ctx} (c off : Nat) (σ : State C Γ) (a b : PrimTy.uint.Denote) :
    (encSb (C := C) (Γ := Γ) c off).Rets ((σ.push (t := .val .uint) a).push (t := .val .uint) b) := by
  intro i e he
  cases i with
  | here =>
    cases he
    exact ⟨_, (zEncT_eval c off σ a b).1, (zEncT_eval c off σ a b).2⟩
  | there j => cases he

/-- A substitution sending every local to a local is a renaming. -/
theorem TEnv.sbPull_idx {Δ : Ctx} (σ : State C Δ) : {Γ : Ctx} → (ρ : Ren Γ Δ) →
    TEnv.sbPull σ (Γ := Γ) ⟨fun j => .idx (ρ.f j)⟩ = Decide.TEnv.pull ρ σ.env
  | [], _ => rfl
  | _ :: _, ρ => by
    show (TEnv.get (ρ.f .here) σ.env, TEnv.sbPull σ ⟨fun j => .idx (ρ.tail.f j)⟩) = _
    rw [TEnv.sbPull_idx σ ρ.tail]
    rfl

theorem State.sbPull_enc {Γ : Ctx} (σ : State C Γ) (c off : Nat) (a b : PrimTy.uint.Denote) :
    ((σ.push (t := .val .uint) a).push (t := .val .uint) b).sbPull (encSb c off) =
      σ.push (t := .kint) ((c : Int) * a.1 - b.1 - off) := by
  show State.withEnv (Δ := .kint :: Γ) _ (((zEncT c off).eval _).getD 0,
    TEnv.sbPull _ ⟨fun j => .idx (Idx.there (Idx.there j))⟩) = _
  rw [(zEncT_eval c off σ a b).1,
    TEnv.sbPull_idx _ (Γ := Γ) ⟨fun j => Idx.there (Idx.there j)⟩]
  show State.withEnv (Δ := .kint :: Γ) _ (_, Decide.TEnv.pull (Δ := .val .uint :: .val .uint :: Γ)
    ⟨fun j => .there ((⟨fun j => .there ((Ren.id Γ).f j)⟩ : Ren Γ (.val .uint :: Γ)).f j)⟩
      (b, (a, σ.env))) = _
  rw [Decide.TEnv.pull_there, Decide.TEnv.pull_there, Decide.TEnv.pull_id]
  rfl

/-- The least multiplier `c` with `c·(2^256 - 1) ≥ 2n + 2`. -/
def zMul (n : Nat) : Nat := (2 * n + 2 + (2 ^ 256 - 2)) / (2 ^ 256 - 1)

theorem zMul_spec (n : Nat) : 1 ≤ zMul n ∧ 2 * n + 2 ≤ (2 ^ 256 - 1) * zMul n := by
  have h1 := Nat.div_add_mod (2 * n + 2 + (2 ^ 256 - 2)) (2 ^ 256 - 1)
  have h2 := Nat.mod_lt (2 * n + 2 + (2 ^ 256 - 2)) (show 2 ^ 256 - 1 > 0 by decide)
  unfold zMul
  omega

/-- A word of the value `x`. -/
def uintOf (x : Nat) (h : x < 2 ^ 256) : PrimTy.uint.Denote :=
  ⟨x, by simp only [PrimTy.inRange, decide_eq_true_eq]; omega⟩

/-- **Every value of `[-(n+1), n+1]` is `c·a - b - (n+1)`** at two words,
`c = zMul n` a word. -/
theorem zEnc_onto (n : Nat) (hc : zMul n ≤ 2 ^ 256) (w : Int) (hw1 : -((n : Int) + 1) ≤ w)
    (hw2 : w ≤ (n : Int) + 1) :
    ∃ a b : PrimTy.uint.Denote, ((zMul n : Nat) : Int) * a.1 - b.1 - ((n + 1 : Nat) : Int) = w := by
  obtain ⟨hc1, hcM⟩ := zMul_spec n
  generalize zMul n = c at hc hc1 hcM
  obtain ⟨W, hW⟩ : ∃ W : Nat, (W : Int) = w + n + 1 := ⟨(w + n + 1).toNat, by omega⟩
  have hWle : W ≤ 2 * n + 2 := by omega
  have hdm := Nat.div_add_mod W c
  have hml := Nat.mod_lt W (show c > 0 by omega)
  generalize W / c = q at hdm
  generalize W % c = rr at hdm hml
  by_cases hr : rr = 0
  · subst hr
    have hq : q ≤ 2 ^ 256 - 1 := by
      apply Nat.le_of_mul_le_mul_left (c := c) _ (by omega)
      rw [Nat.mul_comm c (2 ^ 256 - 1)]; omega
    refine ⟨uintOf q (by omega), uintOf 0 (by decide), ?_⟩
    show (c : Int) * (q : Int) - ((0 : Nat) : Int) - ((n + 1 : Nat) : Int) = w
    have : ((c * q : Nat) : Int) = (c : Int) * (q : Int) := by push_cast; rfl
    omega
  · have hq : q < 2 ^ 256 - 1 := by
      apply Nat.lt_of_mul_lt_mul_left (a := c)
      rw [Nat.mul_comm c (2 ^ 256 - 1)]; omega
    refine ⟨uintOf (q + 1) (by omega), uintOf (c - rr) (by omega), ?_⟩
    show (c : Int) * ((q + 1 : Nat) : Int) - ((c - rr : Nat) : Int) - ((n + 1 : Nat) : Int) = w
    have : ((c * q : Nat) : Int) = (c : Int) * (q : Int) := by push_cast; rfl
    have e1 : ((q + 1 : Nat) : Int) = (q : Int) + 1 := by omega
    rw [e1, Int.mul_add]
    omega

/-- Names of the two words. -/
def Var.zA : Var → Var
  | .user s => .user (s ++ "₁")
  | .fresh b k => .fresh (b ++ "₁") k

def Var.zB : Var → Var
  | .user s => .user (s ++ "₂")
  | .fresh b k => .fresh (b ++ "₂") k

/-- **`∀ int z. A` over two words**, where `A` is linear in `z` and the
multiplier fits a word: `∀ uint a. ∀ uint b. A[z := c·a - b - (n+1)]`. -/
def Fml.kencAt? {Γ : Ctx} (x : Var) (A : Fml C (.kint :: Γ)) : Option (Fml C Γ) :=
  (A.zl .here).bind fun n =>
    if zMul n ≤ 2 ^ 256 then
      (A.sb? (encSb (zMul n) (n + 1))).map fun A' => .all x.zA .uint (.all x.zB .uint A')
    else none

/-- **The encoded binder reads as the binder**, at every state. -/
theorem Fml.holds_kencAt {Γ : Ctx} {x : Var} {A : Fml C (.kint :: Γ)} {ψ : Fml C Γ}
    (h : A.kencAt? x = some ψ) (m : Modality) (σ : State C Γ) :
    holds σ ψ ↔ holds σ (.bind m x .kint A) := by
  simp only [Fml.kencAt?, Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, h⟩ := h
  split at h
  next hc =>
    obtain ⟨A', hA', rfl⟩ := Option.map_eq_some_iff.1 h
    have key : ∀ a b : PrimTy.uint.Denote, holds ((σ.push (t := .val .uint) a).push (t := .val .uint) b) A' ↔
        holds (σ.push (t := .kint) (((zMul n : Nat) : Int) * a.1 - b.1 - ((n + 1 : Nat) : Int))) A :=
      fun a b => (Fml.holds_sb A _ hA' _ (encSb_rets _ _ σ a b)).trans (by rw [State.sbPull_enc])
    show (∀ a b : PrimTy.uint.Denote, holds ((σ.push (t := .val .uint) a).push (t := .val .uint) b) A') ↔
      ∀ v : Int, holds (σ.push (t := .kint) v) A
    constructor
    · intro hab v
      rw [Fml.zl_clamp hn σ v]
      obtain ⟨a, b, e⟩ := zEnc_onto n hc (zclamp n v) (by unfold zclamp; omega)
        (by unfold zclamp; omega)
      have := (key a b).1 (hab a b)
      rwa [e] at this
    · intro hv a b
      exact (key a b).2 (hv _)
  next => cases h

/-! ## Anchors

A binder compared with an unbounded term `U` at another coefficient
(`z == net(a)`, `y > z` for an outer `z`) has no bounded remainder; read
past `U` it may: `∀ int z. A` is `∀ int d. A[z := U + d]` at every state
(`Fml.holds_shift`, `d = z - U`), and in the shifted body the keys of `U`
cancel (`Tm.zl`'s sums of keys).  The anchor is a key of the binder's
context: a local of KeY's `int`, a ledger entry at a `uint` local, or at a
literal address the body reads; each returns in every state. -/

/-- The position `n` of `Γ`, where it has the type `t`. -/
def Idx.ofNat? : (Γ : Ctx) → (t : LTy) → Nat → Option (Idx Γ t)
  | [], _, _ => none
  | u :: _, t, 0 => if h : u = t then some (h ▸ .here) else none
  | _ :: Γ, t, n + 1 => (Idx.ofNat? Γ t n).map .there

/-- A key's term in the context `Γ` (`none` where it names no local of its type). -/
def AKey.tm? {Γ : Ctx} : AKey → Option (Tm C Γ .kint)
  | .loc n => (Idx.ofNat? Γ .kint n).map .pvZ
  | .netL n => (Idx.ofNat? Γ (.val .uint) n).map fun i => .app1 .net (.pvV i)
  | .netC v => some (.app1 .net (.app0 (.lit v)))

/-- **A key's term returns in every state**, alike in the Theory. -/
theorem AKey.tm?_rets {Γ : Ctx} {κ : AKey} {U : Tm C Γ .kint} (h : κ.tm? = some U)
    (σ : State C Γ) : ∃ w, U.eval σ = some w ∧ U.denote σ = some w := by
  cases κ with
  | loc n =>
    obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨_, rfl, rfl⟩
  | netL n =>
    obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨_, rfl, rfl⟩
  | netC v =>
    cases h
    exact ⟨_, rfl, rfl⟩

/-- The keys of a context: its locals of KeY's `int` and the ledger
entries at its `uint` locals, from the position `n`. -/
def ctxKeys : Ctx → Nat → List AKey
  | [], _ => []
  | t :: Γ, n => (match t with
    | .kint => [.loc n]
    | .val .uint => [.netL n]
    | _ => []) ++ ctxKeys Γ (n + 1)

/-- The literal addresses at which a term reads the ledger. -/
def Tm.netLits {Γ : Ctx} : {s : Srt} → Tm C Γ s → List PrimTy.uint.Denote
  | _, .netOf _ a => a.netLits
  | _, .app1 o x => (match o.zlK x with
    | some (.netC v) => [v]
    | _ => []) ++ x.netLits
  | _, .app2 _ x y => x.netLits ++ y.netLits
  | _, .app3 _ x y z => x.netLits ++ y.netLits ++ z.netLits
  | _, _ => []

/-- The literal addresses at which a formula reads the ledger. -/
def Fml.netLits : {Γ : Ctx} → Fml C Γ → List PrimTy.uint.Denote
  | _, .eq a b => a.netLits ++ b.netLits
  | _, .wellFormed s => s.netLits
  | _, .not φ => φ.netLits
  | _, .and φ ψ | _, .imp φ ψ => φ.netLits ++ ψ.netLits
  | _, .all _ _ φ | _, .bind _ _ _ φ => φ.netLits
  | _, _ => []

/-- The binder read past `U`: `z := U + d`. -/
def shiftSb {Γ : Ctx} (U : Tm C Γ .kint) : Sb C (.kint :: Γ) (.kint :: Γ) where
  f := fun {_} i => match i with
    | .here => .tm (.app2 (.zbin .add rfl) (U.ren (Ren.up .kint)) (.pvZ .here))
    | .there j => .idx j.there

/-- **The binder read past a term that returns reads as the binder.** -/
theorem Fml.holds_shift {Γ : Ctx} {U : Tm C Γ .kint}
    (hU : ∀ σ : State C Γ, ∃ w, U.eval σ = some w ∧ U.denote σ = some w)
    {A A' : Fml C (.kint :: Γ)} (h : A.sb? (shiftSb U) = some A') (m : Modality) (x : Var)
    (σ : State C Γ) : holds σ (.bind m x .kint A') ↔ holds σ (.bind m x .kint A) := by
  obtain ⟨u, hu, hud⟩ := hU σ
  have key : ∀ d : Int, holds (σ.push (t := .kint) d) A' ↔ holds (σ.push (t := .kint) (u + d)) A := by
    intro d
    have he : (Tm.app2 (.zbin .add rfl) (U.ren (Ren.up .kint)) (.pvZ .here) :
        Tm C (.kint :: Γ) .kint).eval (σ.push (t := .kint) d) = some (u + d) := by
      rw [Tm.eval_app2, Tm.eval_ren, State.pull_up, hu]; rfl
    have hd : (Tm.app2 (.zbin .add rfl) (U.ren (Ren.up .kint)) (.pvZ .here) :
        Tm C (.kint :: Γ) .kint).denote (σ.push (t := .kint) d) = some (u + d) := by
      simp only [Tm.denote, Tm.denote_ren, State.pull_up, hud]; rfl
    have hr : (shiftSb U).Rets (σ.push (t := .kint) d) := by
      intro i e hi
      cases i with
      | here => cases hi; exact ⟨_, he, hd⟩
      | there j => cases hi
    refine (Fml.holds_sb A _ h _ hr).trans ?_
    have hp : (σ.push (t := .kint) d).sbPull (shiftSb U) = σ.push (t := .kint) (u + d) := by
      show State.withEnv (Δ := .kint :: Γ) _ (((Tm.app2 (.zbin .add rfl) (U.ren (Ren.up .kint))
          (.pvZ .here) : Tm C (.kint :: Γ) .kint).eval (σ.push (t := .kint) d)).getD 0,
        TEnv.sbPull _ ⟨fun j => .idx (Idx.there j)⟩) = _
      rw [he, TEnv.sbPull_idx _ (Γ := Γ) ⟨fun j => Idx.there j⟩]
      show State.withEnv (Δ := .kint :: Γ) _ (_, Decide.TEnv.pull (Δ := .kint :: Γ)
        ⟨fun j => .there ((Ren.id Γ).f j)⟩ (d, σ.env)) = _
      rw [Decide.TEnv.pull_there, Decide.TEnv.pull_id]
      rfl
    rw [hp]
  show (∀ d : Int, holds (σ.push (t := .kint) d) A') ↔ ∀ z : Int, holds (σ.push (t := .kint) z) A
  refine ⟨fun h z => ?_, fun h d => (key d).2 (h _)⟩
  have := (key (z - u)).1 (h _)
  rwa [Int.add_comm, Int.sub_add_cancel] at this

/-- **`∀ int z. A` over two words**, directly (`Fml.kencAt?`) or past an
anchor of its context (`Fml.holds_shift`). -/
def Fml.kencAtA? {Γ : Ctx} (x : Var) (A : Fml C (.kint :: Γ)) : Option (Fml C Γ) :=
  match A.kencAt? x with
  | some ψ => some ψ
  | none => (ctxKeys Γ 0 ++ A.netLits.map AKey.netC).findSome? fun (κ : AKey) =>
    (κ.tm? (C := C) (Γ := Γ)).bind fun U => (A.sb? (shiftSb U)).bind fun A' => A'.kencAt? x

theorem Fml.holds_kencAtA {Γ : Ctx} {x : Var} {A : Fml C (.kint :: Γ)} {ψ : Fml C Γ}
    (h : A.kencAtA? x = some ψ) (m : Modality) (σ : State C Γ) :
    holds σ ψ ↔ holds σ (.bind m x .kint A) := by
  unfold Fml.kencAtA? at h
  split at h
  · next ψ' hψ => cases h; exact Fml.holds_kencAt hψ m σ
  · obtain ⟨κ, -, hκ⟩ := List.exists_of_findSome?_eq_some h
    obtain ⟨U, hU, hκ⟩ := Option.bind_eq_some_iff.1 hκ
    obtain ⟨A', hA', hκ⟩ := Option.bind_eq_some_iff.1 hκ
    exact (Fml.holds_kencAt hκ m σ).trans (Fml.holds_shift (AKey.tm?_rets hU) hA' m x σ)

/-! ## The leaf -/

/-- A binder: KeY's `int` encoded where it can be, any other kept. -/
def Fml.kencBind {Γ : Ctx} (m : Modality) (x : Var) : (t : LTy) → Fml C (t :: Γ) → Fml C Γ × Bool
  | .kint, A => match A.kencAtA? x with
    | some ψ => (ψ, true)
    | none => (.bind m x .kint A, false)
  | t, A => (.bind m x t A, false)

/-- **Every binder of KeY's `int` encoded where it can be** (`Fml.kencAt?`),
innermost first, with whether one was. -/
def Fml.kencB : {Γ : Ctx} → Fml C Γ → Fml C Γ × Bool
  | _, .not φ => let r := φ.kencB; (.not r.1, r.2)
  | _, .and φ ψ => let a := φ.kencB; let b := ψ.kencB; (.and a.1 b.1, a.2 || b.2)
  | _, .imp φ ψ => let a := φ.kencB; let b := ψ.kencB; (.imp a.1 b.1, a.2 || b.2)
  | _, .all x p φ => let r := φ.kencB; (.all x p r.1, r.2)
  | _, .bind m x t φ => let r := φ.kencB; let q := Fml.kencBind m x t r.1; (q.1, r.2 || q.2)
  | _, .upd m U φ => let r := φ.kencB; (.upd m U r.1, r.2)
  | _, .havoc φ => let r := φ.kencB; (.havoc r.1, r.2)
  | _, .anon xs φ => let r := φ.kencB; (.anon xs r.1, r.2)
  | _, .allocAll x R φ => let r := φ.kencB; (.allocAll x R r.1, r.2)
  | _, .grow φ => let r := φ.kencB; (.grow r.1, r.2)
  | _, φ => (φ, false)

theorem Fml.holds_kencBind {Γ : Ctx} (m : Modality) (x : Var) (t : LTy) (A : Fml C (t :: Γ))
    (σ : State C Γ) : holds σ (Fml.kencBind m x t A).1 ↔ holds σ (.bind m x t A) := by
  cases t
  case kint =>
    simp only [Fml.kencBind]
    split
    next ψ hψ => exact Fml.holds_kencAtA hψ m σ
    next => exact Iff.rfl
  all_goals exact Iff.rfl

theorem Upd.afterT_congr {Γ Δ : Ctx} {m : Modality} {σ : State C Γ} {U : Upd C Γ Δ}
    {p q : State C Δ → Prop} (h : ∀ σ', p σ' ↔ q σ') : U.afterT m σ p ↔ U.afterT m σ q :=
  ⟨fun hp => Upd.afterT_imp hp fun σ' => (h σ').1, fun hq => Upd.afterT_imp hq fun σ' => (h σ').2⟩

/-- **The encoded leaf reads as the leaf, at every state.** -/
theorem Fml.holds_kenc {Γ : Ctx} (φ : Fml C Γ) : ∀ σ : State C Γ, holds σ φ.kencB.1 ↔ holds σ φ := by
  induction φ with
  | tt | eq | wellFormed | modal => intro σ; exact Iff.rfl
  | not φ ih => intro σ; exact not_congr (ih σ)
  | and φ ψ ihφ ihψ => intro σ; exact and_congr (ihφ σ) (ihψ σ)
  | imp φ ψ ihφ ihψ => intro σ; exact imp_congr (ihφ σ) (ihψ σ)
  | all x p φ ih => intro σ; exact forall_congr' fun v => ih _
  | bind m x t φ ih =>
    intro σ
    exact (Fml.holds_kencBind m x t _ σ).trans (forall_congr' fun v => ih _)
  | upd m U φ ih => intro σ; exact Upd.afterT_congr ih
  | havoc φ ih => intro σ; exact forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => ih _
  | anon xs φ ih => intro σ; exact forall_congr' fun _ => ih _
  | allocAll x R φ ih => intro σ; exact forall_congr' fun _ => ih _
  | grow φ ih => intro σ; exact forall_congr' fun _ => imp_congr Iff.rfl (ih _)

/-- info: 'Solidity.Fml.holds_kenc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fml.holds_kenc

end Solidity
