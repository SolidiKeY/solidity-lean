import Solidity.Optimizer.Propagate
import Solidity.Optimizer.StmtFold

/-!
# O02 expression simplification

Algebraic identities from solc's simplification rule list
(`libevmasm/RuleList.h`, used by the legacy and Yul `ExpressionSimplifier`),
restricted to the ones that hold under *checked* Solidity arithmetic and keep
every halt. solc applies a rule that drops an operand only when that operand
is movable; here an operand may revert (a storage read through an unset alias,
a checked operation), so a rule that drops `X` requires `X` to be a simple
value (`Val.simple`), whose evaluation never fails.

| rule | types | solc rule |
|---|---|---|
| `X + 0 → X`, `0 + X → X` | `uint`, `int` | `ADD(X, 0)` |
| `X - 0 → X` | `uint`, `int` | `SUB(X, 0)` |
| `X * 1 → X`, `1 * X → X` | `uint`, `int` | `MUL(X, 1)` |
| `X / 1 → X` | `uint`, `int` | `DIV(X, 1)` |
| `X && true → X`, `true && X → X` | `bool` | `AND(X, 1)` on booleans |
| `X \|\| false → X`, `false \|\| X → X` | `bool` | `OR(X, 0)` on booleans |
| `X ** 1 → X` | `uint` | `EXP(X, 1)` |
| `X >> 0 → X` | `uint`, `int` | `SHR(0, X)` / `SAR(0, X)` |
| `s * 0 → 0` (s simple) | `uint`, `int` | `MUL(X, 0)` |
| `s - s → 0` (s simple) | `uint`, `int` | `SUB(X, X)` |
| `s == s → true`, `s != s → false` (s simple) | any | `EQ(X, X)` |
| `s < s`, `s > s → false`; `s <= s`, `s >= s → true` (s simple) | `uint`, `int` | `LT(X, X)` |

A rule that would hide a failure is absent: `X * 0 → 0` and `X - X → 0` for a
compound `X` (it may revert). Not implemented although valid: the bitwise and
`<<` identities, `X % 1`, `X ** 0`, `!!X`, and the identities of the wrapping
operators (`addW`, …), which hold exactly but are not yet proved here.
Preservation is `Val.simp_evalT`:
equal results (value or halt) in every typed state.
-/
namespace Solidity.Optimizer.ConstFold
open Solidity

variable {C : Contract} {Γ : Ctx}

/-! ## Recognisers -/

/-- The integer of an integer literal. -/
def litInt? {p : PrimTy} : Val C Γ p → Option Int
  | .simple (.lit n _) => some n
  | .simple (.bool _) | .simple (.local _) | .simple (.env ..) | .read _ | .binop .. | .unop ..
  | .ternary .. | .readMem _ | .len .. | .mlen .. | .modular .. | .hash .. => none

theorem litInt?_eq {p : PrimTy} {v : Val C Γ p} {n : Int} (h : litInt? v = some n) :
    ∃ hn, v = .simple (.lit n hn) := by
  cases v with
  | simple s =>
    cases s with
    | lit m hm =>
      simp only [litInt?, Option.some.injEq] at h
      subst h
      exact ⟨hm, rfl⟩
    | bool | «local» | env => simp only [litInt?, reduceCtorEq] at h
  | read | binop | unop | ternary | readMem | len | mlen | modular | hash =>
    simp only [litInt?, reduceCtorEq] at h

/-- The Boolean of a Boolean literal. -/
def litBool? {p : PrimTy} : Val C Γ p → Option Bool
  | .simple (.bool b) => some b
  | .simple (.lit ..) | .simple (.local _) | .simple (.env ..) | .read _ | .binop .. | .unop ..
  | .ternary .. | .readMem _ | .len .. | .mlen .. | .modular .. | .hash .. => none

theorem litBool?_eq {v : Val C Γ .bool} {b : Bool} (h : litBool? v = some b) :
    v = .simple (.bool b) := by
  cases v with
  | simple s =>
    cases s with
    | bool c =>
      simp only [litBool?, Option.some.injEq] at h
      subst h
      rfl
    | lit _ hn => simp only [PrimTy.inRange, Bool.false_eq_true] at hn
    | «local» | env => simp only [litBool?, reduceCtorEq] at h
  | read | binop | unop | ternary | readMem | len | mlen | hash =>
    simp only [litBool?, reduceCtorEq] at h

/-- Syntactic equality of simple values, decided without a classical oracle. -/
def Simple.beq : {p : PrimTy} → Simple C Γ p → Simple C Γ p → Bool
  | _, .lit n _, .lit m _ => n == m
  | _, .bool a, .bool b => a == b
  | _, .local i, .local j => i.toNat == j.toNat
  | _, .env k _, .env l _ => decide (k = l)
  | _, .lit .., .bool _ | _, .lit .., .local _ | _, .lit .., .env .. => false
  | _, .bool _, .lit .. | _, .bool _, .local _ | _, .bool _, .env .. => false
  | _, .local _, .lit .. | _, .local _, .bool _ | _, .local _, .env .. => false
  | _, .env .., .lit .. | _, .env .., .bool _ | _, .env .., .local _ => false

theorem Simple.beq_eq : {p : PrimTy} → (s t : Simple C Γ p) → Simple.beq s t = true → s = t
  | _, .lit n _, .lit m _, h => by
    simp only [Simple.beq, beq_iff_eq] at h
    subst h
    rfl
  | _, .bool a, .bool b, h => by
    simp only [Simple.beq, beq_iff_eq] at h
    subst h
    rfl
  | _, .local i, .local j, h => by
    simp only [Simple.beq, beq_iff_eq] at h
    obtain ⟨e, hj⟩ := Idx.eq_of_toNat j i h
    cases e
    subst hj
    rfl
  | _, .env k hk, .env l hl, h => by
    simp only [Simple.beq, decide_eq_true_eq] at h
    subst h
    rfl
  | _, .lit .., .bool _, h | _, .lit .., .local _, h | _, .lit .., .env .., h
  | _, .bool _, .lit .., h | _, .bool _, .local _, h | _, .bool _, .env .., h
  | _, .local _, .lit .., h | _, .local _, .bool _, h | _, .local _, .env .., h
  | _, .env .., .lit .., h | _, .env .., .bool _, h | _, .env .., .local _, h => by
    simp only [Simple.beq, Bool.false_eq_true] at h

/-- The simple value an expression is. -/
def simple? {p : PrimTy} : Val C Γ p → Option (Simple C Γ p)
  | .simple s => some s
  | .read _ | .binop .. | .unop .. | .ternary .. | .readMem _ | .len .. | .mlen .. | .modular ..
  | .hash .. => none

theorem simple?_eq {p : PrimTy} {v : Val C Γ p} {s : Simple C Γ p} (h : simple? v = some s) :
    v = .simple s := by
  cases v with
  | simple t => simp only [simple?, Option.some.injEq] at h; rw [h]
  | read | binop | unop | ternary | readMem | len | mlen | modular | hash =>
    simp only [simple?, reduceCtorEq] at h

/-- Both operands are the same simple value. -/
def sameSimple {p : PrimTy} (a b : Val C Γ p) : Bool :=
  match simple? a, simple? b with
  | some s, some t => Simple.beq s t
  | _, _ => false

theorem sameSimple_eq {p : PrimTy} {a b : Val C Γ p} (h : sameSimple a b = true) :
    ∃ s, a = .simple s ∧ b = .simple s := by
  unfold sameSimple at h
  cases ha : simple? a with
  | none => simp only [ha, Bool.false_eq_true] at h
  | some s =>
    cases hb : simple? b with
    | none => simp only [ha, hb, Bool.false_eq_true] at h
    | some t =>
      simp only [ha, hb] at h
      exact ⟨s, simple?_eq ha, by rw [simple?_eq hb, Simple.beq_eq s t h]⟩

/-! ## Arithmetic facts -/

theorem add_zero_r_uint (σ : State C Γ) (a : Val C Γ .uint) (h : BinOp.add.accepts .uint = true)
    (hq : BinOp.add.ret .uint = .uint) (hn : PrimTy.uint.inRange 0 = true) :
    (Val.binop .add h hq a (.simple (.lit 0 hn))).evalT σ = a.evalT σ := by
  cases ha : a.evalT σ with
  | error e => simp only [Val.evalT, ha, bind, Except.bind]
  | ok x =>
    obtain ⟨y, hy⟩ := x
    simp only [Val.evalT, bind, Except.bind, ha, BinOp.shortT, Simple.evalT, PrimTy.ofLit,
      TRes.ofOpt, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.add_zero, Option.bind_some,
      PrimTy.ofInt?, hy, ↓reduceDIte]

theorem add_zero_r_int (σ : State C Γ) (a : Val C Γ .int) (h : BinOp.add.accepts .int = true)
    (hq : BinOp.add.ret .int = .int) (hn : PrimTy.int.inRange 0 = true) :
    (Val.binop .add h hq a (.simple (.lit 0 hn))).evalT σ = a.evalT σ := by
  cases ha : a.evalT σ with
  | error e => simp only [Val.evalT, ha, bind, Except.bind]
  | ok x =>
    obtain ⟨y, hy⟩ := x
    simp only [Val.evalT, bind, Except.bind, ha, BinOp.shortT, Simple.evalT, PrimTy.ofLit,
      TRes.ofOpt, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.add_zero, Option.bind_some,
      PrimTy.ofInt?, hy, ↓reduceDIte]

theorem add_zero_l_uint (σ : State C Γ) (b : Val C Γ .uint) (h : BinOp.add.accepts .uint = true)
    (hq : BinOp.add.ret .uint = .uint) (hn : PrimTy.uint.inRange 0 = true) :
    (Val.binop .add h hq (.simple (.lit 0 hn)) b).evalT σ = b.evalT σ := by
  cases hb : b.evalT σ with
  | error e => simp only [Val.evalT, hb, bind, Except.bind, Simple.evalT, BinOp.shortT]
  | ok x =>
    obtain ⟨y, hy⟩ := x
    simp only [Val.evalT, bind, Except.bind, Simple.evalT, PrimTy.ofLit, BinOp.shortT, hb,
      TRes.ofOpt, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.zero_add, Option.bind_some,
      PrimTy.ofInt?, hy, ↓reduceDIte]

theorem add_zero_l_int (σ : State C Γ) (b : Val C Γ .int) (h : BinOp.add.accepts .int = true)
    (hq : BinOp.add.ret .int = .int) (hn : PrimTy.int.inRange 0 = true) :
    (Val.binop .add h hq (.simple (.lit 0 hn)) b).evalT σ = b.evalT σ := by
  cases hb : b.evalT σ with
  | error e => simp only [Val.evalT, hb, bind, Except.bind, Simple.evalT, BinOp.shortT]
  | ok x =>
    obtain ⟨y, hy⟩ := x
    simp only [Val.evalT, bind, Except.bind, Simple.evalT, PrimTy.ofLit, BinOp.shortT, hb,
      TRes.ofOpt, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.zero_add, Option.bind_some,
      PrimTy.ofInt?, hy, ↓reduceDIte]

theorem sub_zero_r_uint (σ : State C Γ) (a : Val C Γ .uint) (h : BinOp.sub.accepts .uint = true)
    (hq : BinOp.sub.ret .uint = .uint) (hn : PrimTy.uint.inRange 0 = true) :
    (Val.binop .sub h hq a (.simple (.lit 0 hn))).evalT σ = a.evalT σ := by
  cases ha : a.evalT σ with
  | error e => simp only [Val.evalT, ha, bind, Except.bind]
  | ok x =>
    obtain ⟨y, hy⟩ := x
    simp only [Val.evalT, bind, Except.bind, ha, BinOp.shortT, Simple.evalT, PrimTy.ofLit,
      TRes.ofOpt, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.sub_zero, Option.bind_some,
      PrimTy.ofInt?, hy, ↓reduceDIte]

theorem sub_zero_r_int (σ : State C Γ) (a : Val C Γ .int) (h : BinOp.sub.accepts .int = true)
    (hq : BinOp.sub.ret .int = .int) (hn : PrimTy.int.inRange 0 = true) :
    (Val.binop .sub h hq a (.simple (.lit 0 hn))).evalT σ = a.evalT σ := by
  cases ha : a.evalT σ with
  | error e => simp only [Val.evalT, ha, bind, Except.bind]
  | ok x =>
    obtain ⟨y, hy⟩ := x
    simp only [Val.evalT, bind, Except.bind, ha, BinOp.shortT, Simple.evalT, PrimTy.ofLit,
      TRes.ofOpt, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.sub_zero, Option.bind_some,
      PrimTy.ofInt?, hy, ↓reduceDIte]

theorem mul_one_r_uint (σ : State C Γ) (a : Val C Γ .uint) (h : BinOp.mul.accepts .uint = true)
    (hq : BinOp.mul.ret .uint = .uint) (hn : PrimTy.uint.inRange 1 = true) :
    (Val.binop .mul h hq a (.simple (.lit 1 hn))).evalT σ = a.evalT σ := by
  cases ha : a.evalT σ with
  | error e => simp only [Val.evalT, ha, bind, Except.bind]
  | ok x =>
    obtain ⟨y, hy⟩ := x
    simp only [Val.evalT, bind, Except.bind, ha, BinOp.shortT, Simple.evalT, PrimTy.ofLit,
      TRes.ofOpt, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.mul_one, Option.bind_some,
      PrimTy.ofInt?, hy, ↓reduceDIte]

theorem mul_one_r_int (σ : State C Γ) (a : Val C Γ .int) (h : BinOp.mul.accepts .int = true)
    (hq : BinOp.mul.ret .int = .int) (hn : PrimTy.int.inRange 1 = true) :
    (Val.binop .mul h hq a (.simple (.lit 1 hn))).evalT σ = a.evalT σ := by
  cases ha : a.evalT σ with
  | error e => simp only [Val.evalT, ha, bind, Except.bind]
  | ok x =>
    obtain ⟨y, hy⟩ := x
    simp only [Val.evalT, bind, Except.bind, ha, BinOp.shortT, Simple.evalT, PrimTy.ofLit,
      TRes.ofOpt, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.mul_one, Option.bind_some,
      PrimTy.ofInt?, hy, ↓reduceDIte]

theorem mul_one_l_uint (σ : State C Γ) (b : Val C Γ .uint) (h : BinOp.mul.accepts .uint = true)
    (hq : BinOp.mul.ret .uint = .uint) (hn : PrimTy.uint.inRange 1 = true) :
    (Val.binop .mul h hq (.simple (.lit 1 hn)) b).evalT σ = b.evalT σ := by
  cases hb : b.evalT σ with
  | error e => simp only [Val.evalT, hb, bind, Except.bind, Simple.evalT, BinOp.shortT]
  | ok x =>
    obtain ⟨y, hy⟩ := x
    simp only [Val.evalT, bind, Except.bind, Simple.evalT, PrimTy.ofLit, BinOp.shortT, hb,
      TRes.ofOpt, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.one_mul, Option.bind_some,
      PrimTy.ofInt?, hy, ↓reduceDIte]

theorem mul_one_l_int (σ : State C Γ) (b : Val C Γ .int) (h : BinOp.mul.accepts .int = true)
    (hq : BinOp.mul.ret .int = .int) (hn : PrimTy.int.inRange 1 = true) :
    (Val.binop .mul h hq (.simple (.lit 1 hn)) b).evalT σ = b.evalT σ := by
  cases hb : b.evalT σ with
  | error e => simp only [Val.evalT, hb, bind, Except.bind, Simple.evalT, BinOp.shortT]
  | ok x =>
    obtain ⟨y, hy⟩ := x
    simp only [Val.evalT, bind, Except.bind, Simple.evalT, PrimTy.ofLit, BinOp.shortT, hb,
      TRes.ofOpt, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.one_mul, Option.bind_some,
      PrimTy.ofInt?, hy, ↓reduceDIte]

theorem div_one_r_uint (σ : State C Γ) (a : Val C Γ .uint) (h : BinOp.div.accepts .uint = true)
    (hq : BinOp.div.ret .uint = .uint) (hn : PrimTy.uint.inRange 1 = true) :
    (Val.binop .div h hq a (.simple (.lit 1 hn))).evalT σ = a.evalT σ := by
  cases ha : a.evalT σ with
  | error e => simp only [Val.evalT, ha, bind, Except.bind]
  | ok x =>
    obtain ⟨y, hy⟩ := x
    simp only [Val.evalT, bind, Except.bind, ha, BinOp.shortT, Simple.evalT, PrimTy.ofLit,
      TRes.ofOpt, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.reduceEq, ↓reduceIte,
      Int.tdiv_one, Option.bind_some, PrimTy.ofInt?, hy, ↓reduceDIte]

theorem div_one_r_int (σ : State C Γ) (a : Val C Γ .int) (h : BinOp.div.accepts .int = true)
    (hq : BinOp.div.ret .int = .int) (hn : PrimTy.int.inRange 1 = true) :
    (Val.binop .div h hq a (.simple (.lit 1 hn))).evalT σ = a.evalT σ := by
  cases ha : a.evalT σ with
  | error e => simp only [Val.evalT, ha, bind, Except.bind]
  | ok x =>
    obtain ⟨y, hy⟩ := x
    simp only [Val.evalT, bind, Except.bind, ha, BinOp.shortT, Simple.evalT, PrimTy.ofLit,
      TRes.ofOpt, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.reduceEq, ↓reduceIte,
      Int.tdiv_one, Option.bind_some, PrimTy.ofInt?, hy, ↓reduceDIte]

theorem and_true_r (σ : State C Γ) (a : Val C Γ .bool) (h : BinOp.and.accepts .bool = true)
    (hq : BinOp.and.ret .bool = .bool) :
    (Val.binop .and h hq a (.simple (.bool true))).evalT σ = a.evalT σ := by
  cases ha : a.evalT σ with
  | error e => simp only [Val.evalT, ha, bind, Except.bind]
  | ok x =>
    cases x <;> simp only [Val.evalT, bind, Except.bind, ha, BinOp.shortT, boolT,
      Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Simple.evalT, TRes.ofOpt, BinOp.evalT,
      BinOp.evalBool, Bool.and_self]

theorem and_true_l (σ : State C Γ) (b : Val C Γ .bool) (h : BinOp.and.accepts .bool = true)
    (hq : BinOp.and.ret .bool = .bool) :
    (Val.binop .and h hq (.simple (.bool true)) b).evalT σ = b.evalT σ := by
  cases hb : b.evalT σ with
  | error e => simp only [Val.evalT, bind, Except.bind, Simple.evalT, BinOp.shortT, boolT,
    ↓reduceIte, hb]
  | ok x =>
    cases x <;> simp only [Val.evalT, bind, Except.bind, Simple.evalT, BinOp.shortT, boolT,
      ↓reduceIte, hb, TRes.ofOpt, BinOp.evalT, BinOp.evalBool, Bool.and_false, Bool.and_self]

theorem or_false_r (σ : State C Γ) (a : Val C Γ .bool) (h : BinOp.or.accepts .bool = true)
    (hq : BinOp.or.ret .bool = .bool) :
    (Val.binop .or h hq a (.simple (.bool false))).evalT σ = a.evalT σ := by
  cases ha : a.evalT σ with
  | error e => simp only [Val.evalT, ha, bind, Except.bind]
  | ok x =>
    cases x <;> simp only [Val.evalT, bind, Except.bind, ha, BinOp.shortT, boolT,
      Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Simple.evalT, TRes.ofOpt, BinOp.evalT,
      BinOp.evalBool, Bool.or_self]

theorem or_false_l (σ : State C Γ) (b : Val C Γ .bool) (h : BinOp.or.accepts .bool = true)
    (hq : BinOp.or.ret .bool = .bool) :
    (Val.binop .or h hq (.simple (.bool false)) b).evalT σ = b.evalT σ := by
  cases hb : b.evalT σ with
  | error e => simp only [Val.evalT, bind, Except.bind, Simple.evalT, BinOp.shortT, boolT,
    Bool.false_eq_true, ↓reduceIte, hb]
  | ok x =>
    cases x <;> simp only [Val.evalT, bind, Except.bind, Simple.evalT, BinOp.shortT, boolT,
      Bool.false_eq_true, ↓reduceIte, hb, TRes.ofOpt, BinOp.evalT, BinOp.evalBool, Bool.or_self,
      Bool.or_true]

theorem sub_self_uint (σ : State C Γ) (s : Simple C Γ .uint) (h : BinOp.sub.accepts .uint = true)
    (hq : BinOp.sub.ret .uint = .uint) (hn : PrimTy.uint.inRange 0 = true) :
    (Val.binop .sub h hq (.simple s) (.simple s)).evalT σ =
      (Val.simple (.lit 0 hn) : Val C Γ .uint).evalT σ := by
  obtain ⟨y, hy⟩ := s.evalT σ
  simp only [Val.evalT, bind, Except.bind, Simple.evalT, PrimTy.ofLit, BinOp.shortT, TRes.ofOpt,
    BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.sub_self, Option.bind_some, PrimTy.ofInt?, hn,
    ↓reduceDIte]

theorem sub_self_int (σ : State C Γ) (s : Simple C Γ .int) (h : BinOp.sub.accepts .int = true)
    (hq : BinOp.sub.ret .int = .int) (hn : PrimTy.int.inRange 0 = true) :
    (Val.binop .sub h hq (.simple s) (.simple s)).evalT σ =
      (Val.simple (.lit 0 hn) : Val C Γ .int).evalT σ := by
  obtain ⟨y, hy⟩ := s.evalT σ
  simp only [Val.evalT, bind, Except.bind, Simple.evalT, PrimTy.ofLit, BinOp.shortT, TRes.ofOpt,
    BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.sub_self, Option.bind_some, PrimTy.ofInt?, hn,
    ↓reduceDIte]

theorem eq_self (σ : State C Γ) {p : PrimTy} (s : Simple C Γ p) (h : BinOp.eqB.accepts p = true)
    (hq : BinOp.eqB.ret p = .bool) :
    (Val.binop .eqB h hq (.simple s) (.simple s)).evalT σ =
      (Val.simple (.bool true) : Val C Γ .bool).evalT σ := by
  cases p <;> simp only [Val.evalT, bind, Except.bind, Simple.evalT, PrimTy.ofLit, BinOp.shortT,
    TRes.ofOpt, BinOp.evalT, BinOp.evalBool, BinOp.evalNum, decide_true]

theorem ne_self (σ : State C Γ) {p : PrimTy} (s : Simple C Γ p) (h : BinOp.neB.accepts p = true)
    (hq : BinOp.neB.ret p = .bool) :
    (Val.binop .neB h hq (.simple s) (.simple s)).evalT σ =
      (Val.simple (.bool false) : Val C Γ .bool).evalT σ := by
  cases p <;> simp only [Val.evalT, bind, Except.bind, Simple.evalT, PrimTy.ofLit, BinOp.shortT,
    TRes.ofOpt, BinOp.evalT, BinOp.evalBool, BinOp.evalNum, decide_true, Bool.not_true]

theorem pow_one_r (σ : State C Γ) (a : Val C Γ .uint) (h : BinOp.pow.accepts .uint = true)
    (hq : BinOp.pow.ret .uint = .uint) (hn : PrimTy.uint.inRange 1 = true) :
    (Val.binop .pow h hq a (.simple (.lit 1 hn))).evalT σ = a.evalT σ := by
  cases ha : a.evalT σ with
  | error e => simp only [Val.evalT, ha, bind, Except.bind]
  | ok x =>
    obtain ⟨y, hy⟩ := x
    simp only [Val.evalT, bind, Except.bind, ha, BinOp.shortT, Simple.evalT, PrimTy.ofLit,
      TRes.ofOpt, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.reduceLT, ↓reduceIte,
      Int.toNat_one, Lean.Grind.Int.pow_one, Option.bind_some, PrimTy.ofInt?, hy, ↓reduceDIte]

theorem shr_zero_r_uint (σ : State C Γ) (a : Val C Γ .uint) (h : BinOp.shr.accepts .uint = true)
    (hq : BinOp.shr.ret .uint = .uint) (hn : PrimTy.uint.inRange 0 = true) :
    (Val.binop .shr h hq a (.simple (.lit 0 hn))).evalT σ = a.evalT σ := by
  cases ha : a.evalT σ with
  | error e => simp only [Val.evalT, ha, bind, Except.bind]
  | ok x =>
    obtain ⟨y, hy⟩ := x
    simp only [Val.evalT, bind, Except.bind, ha, BinOp.shortT, Simple.evalT, PrimTy.ofLit,
      TRes.ofOpt, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.reduceLT, ↓reduceIte,
      Int.toNat_zero, Int.pow_zero, Int.ediv_one, Option.bind_some, PrimTy.ofInt?, hy,
      ↓reduceDIte]

theorem shr_zero_r_int (σ : State C Γ) (a : Val C Γ .int) (h : BinOp.shr.accepts .int = true)
    (hq : BinOp.shr.ret .int = .int) (hn : PrimTy.int.inRange 0 = true) :
    (Val.binop .shr h hq a (.simple (.lit 0 hn))).evalT σ = a.evalT σ := by
  cases ha : a.evalT σ with
  | error e => simp only [Val.evalT, ha, bind, Except.bind]
  | ok x =>
    obtain ⟨y, hy⟩ := x
    simp only [Val.evalT, bind, Except.bind, ha, BinOp.shortT, Simple.evalT, PrimTy.ofLit,
      TRes.ofOpt, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.reduceLT, ↓reduceIte,
      Int.toNat_zero, Int.pow_zero, Int.ediv_one, Option.bind_some, PrimTy.ofInt?, hy,
      ↓reduceDIte]

theorem mul_zero_r_uint (σ : State C Γ) (s : Simple C Γ .uint) (h : BinOp.mul.accepts .uint = true)
    (hq : BinOp.mul.ret .uint = .uint) (hn : PrimTy.uint.inRange 0 = true) :
    (Val.binop .mul h hq (.simple s) (.simple (.lit 0 hn))).evalT σ =
      (Val.simple (.lit 0 hn) : Val C Γ .uint).evalT σ := by
  simp only [Val.evalT, bind, Except.bind, Simple.evalT, PrimTy.ofLit, BinOp.shortT,
    TRes.ofOpt, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.mul_zero, Option.bind_some,
    PrimTy.ofInt?, hn, ↓reduceDIte]

theorem mul_zero_r_int (σ : State C Γ) (s : Simple C Γ .int) (h : BinOp.mul.accepts .int = true)
    (hq : BinOp.mul.ret .int = .int) (hn : PrimTy.int.inRange 0 = true) :
    (Val.binop .mul h hq (.simple s) (.simple (.lit 0 hn))).evalT σ =
      (Val.simple (.lit 0 hn) : Val C Γ .int).evalT σ := by
  simp only [Val.evalT, bind, Except.bind, Simple.evalT, PrimTy.ofLit, BinOp.shortT,
    TRes.ofOpt, BinOp.evalT, BinOp.evalNum, BinOp.arithInt, Int.mul_zero, Option.bind_some,
    PrimTy.ofInt?, hn, ↓reduceDIte]

theorem lt_self (σ : State C Γ) {p : PrimTy} (s : Simple C Γ p) (h : BinOp.lt.accepts p = true)
    (hq : BinOp.lt.ret p = .bool) :
    (Val.binop .lt h hq (.simple s) (.simple s)).evalT σ =
      (Val.simple (.bool false) : Val C Γ .bool).evalT σ := by
  cases p <;> first
    | exact absurd h (by decide)
    | simp only [Val.evalT, bind, Except.bind, Simple.evalT, BinOp.shortT, TRes.ofOpt,
        BinOp.evalT, BinOp.evalNum, Int.lt_irrefl, decide_false]

theorem le_self (σ : State C Γ) {p : PrimTy} (s : Simple C Γ p) (h : BinOp.le.accepts p = true)
    (hq : BinOp.le.ret p = .bool) :
    (Val.binop .le h hq (.simple s) (.simple s)).evalT σ =
      (Val.simple (.bool true) : Val C Γ .bool).evalT σ := by
  cases p <;> first
    | exact absurd h (by decide)
    | simp only [Val.evalT, bind, Except.bind, Simple.evalT, BinOp.shortT, TRes.ofOpt,
        BinOp.evalT, BinOp.evalNum, Int.le_refl, decide_true]

theorem gt_self (σ : State C Γ) {p : PrimTy} (s : Simple C Γ p) (h : BinOp.gt.accepts p = true)
    (hq : BinOp.gt.ret p = .bool) :
    (Val.binop .gt h hq (.simple s) (.simple s)).evalT σ =
      (Val.simple (.bool false) : Val C Γ .bool).evalT σ := by
  cases p <;> first
    | exact absurd h (by decide)
    | simp only [Val.evalT, bind, Except.bind, Simple.evalT, BinOp.shortT, TRes.ofOpt,
        BinOp.evalT, BinOp.evalNum, Int.lt_irrefl, decide_false]

theorem ge_self (σ : State C Γ) {p : PrimTy} (s : Simple C Γ p) (h : BinOp.ge.accepts p = true)
    (hq : BinOp.ge.ret p = .bool) :
    (Val.binop .ge h hq (.simple s) (.simple s)).evalT σ =
      (Val.simple (.bool true) : Val C Γ .bool).evalT σ := by
  cases p <;> first
    | exact absurd h (by decide)
    | simp only [Val.evalT, bind, Except.bind, Simple.evalT, BinOp.shortT, TRes.ofOpt,
        BinOp.evalT, BinOp.evalNum, Int.le_refl, decide_true]

/-! ## The rewriter -/

/-- Retype along an equation of primitive types. -/
def castV {r q : PrimTy} (h : r = q) (v : Val C Γ r) : Val C Γ q := h ▸ v

def isLitI {p : PrimTy} (n : Int) (v : Val C Γ p) : Bool := litInt? v == some n
def isLitB {p : PrimTy} (b : Bool) (v : Val C Γ p) : Bool := litBool? v == some b

theorem isLitI_true {p : PrimTy} {n : Int} {v : Val C Γ p} (h : isLitI n v = true) :
    ∃ hn, v = .simple (.lit n hn) :=
  litInt?_eq (by simpa only [isLitI, beq_iff_eq] using h)

theorem isLitB_true {b : Bool} {v : Val C Γ .bool} (h : isLitB b v = true) :
    v = .simple (.bool b) :=
  litBool?_eq (by simpa only [isLitB, beq_iff_eq] using h)

def isSimp {p : PrimTy} (v : Val C Γ p) : Bool := (simple? v).isSome

theorem isSimp_true {p : PrimTy} {v : Val C Γ p} (h : isSimp v = true) : ∃ s, v = .simple s := by
  unfold isSimp at h
  cases hv : simple? v with
  | none => simp only [hv, Option.isSome_none, Bool.false_eq_true] at h
  | some s => exact ⟨s, simple?_eq hv⟩

/-- One binary node, operands already simplified. -/
def simpBin : (op : BinOp) → (p : PrimTy) → {q : PrimTy} → op.accepts p = true →
    op.ret p = q → Val C Γ p → Val C Γ p → Val C Γ q
  | .add, .uint, _, h, hq, a, b =>
    if isLitI 0 b then castV hq a else if isLitI 0 a then castV hq b else .binop .add h hq a b
  | .add, .int, _, h, hq, a, b =>
    if isLitI 0 b then castV hq a else if isLitI 0 a then castV hq b else .binop .add h hq a b
  | .sub, .uint, _, h, hq, a, b =>
    if isLitI 0 b then castV hq a
    else if sameSimple a b then castV hq (.simple (.lit 0 (by decide)))
    else .binop .sub h hq a b
  | .sub, .int, _, h, hq, a, b =>
    if isLitI 0 b then castV hq a
    else if sameSimple a b then castV hq (.simple (.lit 0 (by decide)))
    else .binop .sub h hq a b
  | .mul, .uint, _, h, hq, a, b =>
    if isLitI 1 b then castV hq a else if isLitI 1 a then castV hq b
    else if isLitI 0 b then
      (if isSimp a then castV hq (.simple (.lit 0 (by decide))) else .binop .mul h hq a b)
    else .binop .mul h hq a b
  | .mul, .int, _, h, hq, a, b =>
    if isLitI 1 b then castV hq a else if isLitI 1 a then castV hq b
    else if isLitI 0 b then
      (if isSimp a then castV hq (.simple (.lit 0 (by decide))) else .binop .mul h hq a b)
    else .binop .mul h hq a b
  | .div, .uint, _, h, hq, a, b => if isLitI 1 b then castV hq a else .binop .div h hq a b
  | .div, .int, _, h, hq, a, b => if isLitI 1 b then castV hq a else .binop .div h hq a b
  | .pow, .uint, _, h, hq, a, b => if isLitI 1 b then castV hq a else .binop .pow h hq a b
  | .shr, .uint, _, h, hq, a, b => if isLitI 0 b then castV hq a else .binop .shr h hq a b
  | .shr, .int, _, h, hq, a, b => if isLitI 0 b then castV hq a else .binop .shr h hq a b
  | .lt, _, _, h, hq, a, b =>
    if sameSimple a b then castV hq (.simple (.bool false)) else .binop .lt h hq a b
  | .gt, _, _, h, hq, a, b =>
    if sameSimple a b then castV hq (.simple (.bool false)) else .binop .gt h hq a b
  | .le, _, _, h, hq, a, b =>
    if sameSimple a b then castV hq (.simple (.bool true)) else .binop .le h hq a b
  | .ge, _, _, h, hq, a, b =>
    if sameSimple a b then castV hq (.simple (.bool true)) else .binop .ge h hq a b
  | .and, .bool, _, h, hq, a, b =>
    if isLitB true b then castV hq a else if isLitB true a then castV hq b
    else .binop .and h hq a b
  | .or, .bool, _, h, hq, a, b =>
    if isLitB false b then castV hq a else if isLitB false a then castV hq b
    else .binop .or h hq a b
  | .eqB, _, _, h, hq, a, b =>
    if sameSimple a b then castV hq (.simple (.bool true)) else .binop .eqB h hq a b
  | .neB, _, _, h, hq, a, b =>
    if sameSimple a b then castV hq (.simple (.bool false)) else .binop .neB h hq a b
  | op, _, _, h, hq, a, b => .binop op h hq a b

theorem simpBin_evalT (σ : State C Γ) (op : BinOp) (p : PrimTy) {q : PrimTy}
    (h : op.accepts p = true) (hq : op.ret p = q) (a b : Val C Γ p) :
    (simpBin op p h hq a b).evalT σ = (Val.binop op h hq a b).evalT σ := by
  subst hq
  cases op <;> cases p <;> simp only [simpBin] <;> (repeat' split) <;>
    first
      | rfl
      | (obtain ⟨hn, rfl⟩ := isLitI_true ‹isLitI _ _ = true›
         first
          | exact (add_zero_r_uint σ _ _ _ _).symm
          | exact (add_zero_r_int σ _ _ _ _).symm
          | exact (add_zero_l_uint σ _ _ _ _).symm
          | exact (add_zero_l_int σ _ _ _ _).symm
          | exact (sub_zero_r_uint σ _ _ _ _).symm
          | exact (sub_zero_r_int σ _ _ _ _).symm
          | exact (mul_one_r_uint σ _ _ _ _).symm
          | exact (mul_one_r_int σ _ _ _ _).symm
          | exact (mul_one_l_uint σ _ _ _ _).symm
          | exact (mul_one_l_int σ _ _ _ _).symm
          | exact (div_one_r_uint σ _ _ _ _).symm
          | exact (div_one_r_int σ _ _ _ _).symm
          | exact (and_true_r σ _ _ _).symm
          | exact (and_true_l σ _ _ _).symm
          | exact (or_false_r σ _ _ _).symm
          | exact (or_false_l σ _ _ _).symm
          | exact (pow_one_r σ _ _ _ _).symm
          | exact (shr_zero_r_uint σ _ _ _ _).symm
          | exact (shr_zero_r_int σ _ _ _ _).symm)
      | (obtain ⟨hn, rfl⟩ := isLitI_true ‹isLitI _ _ = true›
         obtain ⟨s, rfl⟩ := isSimp_true ‹isSimp _ = true›
         first
          | exact (mul_zero_r_uint σ s _ _ _).symm
          | exact (mul_zero_r_int σ s _ _ _).symm)
      | (have hb := isLitB_true ‹isLitB _ _ = true›
         subst hb
         first
          | exact (and_true_r σ _ _ _).symm
          | exact (and_true_l σ _ _ _).symm
          | exact (or_false_r σ _ _ _).symm
          | exact (or_false_l σ _ _ _).symm)
      | (obtain ⟨s, rfl, rfl⟩ := sameSimple_eq ‹sameSimple _ _ = true›
         first
          | exact (sub_self_uint σ s _ _ _).symm
          | exact (sub_self_int σ s _ _ _).symm
          | exact (eq_self σ s _ _).symm
          | exact (ne_self σ s _ _).symm
          | exact (lt_self σ s _ _).symm
          | exact (gt_self σ s _ _).symm
          | exact (le_self σ s _ _).symm
          | exact (ge_self σ s _ _).symm)

/-- Bottom-up simplification. -/
def _root_.Solidity.Val.simp : {p : PrimTy} → Val C Γ p → Val C Γ p
  | _, .binop op h hq a b => simpBin op _ h hq a.simp b.simp
  | _, .unop op h hq a => .unop op h hq a.simp
  | _, .ternary c a b => .ternary c.simp a.simp b.simp
  | _, .modular op a b k => .modular op a.simp b.simp k.simp
  | _, .simple s => .simple s
  | _, .read l => .read l
  | _, .readMem l => .readMem l
  | _, .len b hp => .len b hp
  | _, .mlen b hp => .mlen b hp
  | _, .hash k b hp => .hash k b hp

/-- **Simplification preserves every result**, value or halt. -/
theorem _root_.Solidity.Val.simp_evalT (σ : State C Γ) : {p : PrimTy} → (v : Val C Γ p) →
    v.simp.evalT σ = v.evalT σ
  | _, .binop op h hq a b => by
    rw [Val.simp, simpBin_evalT]
    simp only [Val.evalT, Val.simp_evalT σ a, Val.simp_evalT σ b]
  | _, .unop op h hq a => by
    simp only [Val.simp, Val.evalT, Val.simp_evalT σ a]
  | _, .ternary c a b => by
    simp only [Val.simp, Val.evalT, Val.simp_evalT σ c, Val.simp_evalT σ a, Val.simp_evalT σ b]
  | _, .modular op a b k => by
    simp only [Val.simp, Val.evalT, Val.simp_evalT σ a, Val.simp_evalT σ b, Val.simp_evalT σ k]
  | _, .simple _ => rfl
  | _, .read _ => rfl
  | _, .readMem _ => rfl
  | _, .len _ _ => rfl
  | _, .mlen _ _ => rfl
  | _, .hash _ _ _ => rfl

/-- Simplify, then fold. -/
def simpFoldPass : ValPass C :=
  ⟨fun v => (Val.simp v).cfold, fun σ v => by rw [Val.cfold_evalT, Val.simp_evalT]⟩

/-- Simplification, folding and dead-code elimination over a program. -/
abbrev _root_.Solidity.Prog.simplify {Γ Γ' : Ctx} (P : Prog C Γ Γ') : Prog C Γ Γ' :=
  Prog.vopt simpFoldPass P

theorem _root_.Solidity.Prog.simplify_runC {Γ Γ' : Ctx} (P : Prog C Γ Γ') :
    Prog.runC (Prog.simplify P) = Prog.runC P :=
  Prog.vopt_runC simpFoldPass P

end Solidity.Optimizer.ConstFold
