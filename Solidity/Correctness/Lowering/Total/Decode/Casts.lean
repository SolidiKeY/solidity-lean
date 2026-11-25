import Solidity.Correctness.Lowering.Total.Decode.WithExpr
import Solidity.Source.Eval

/-!
# Casts written as calls

The model writes a conversion as a raw call of the type's name: `uintN(e)`,
`intN(e)`, `bytesN(e)`, `address(e)` (also its `payable(e)`; `address(this)`
is `address` of the own-address read). `Casts.expr` is `Calls.expr` with one
more case: an unclaimed one-argument call of a cast name (`target`) is the
Source explicit conversion `T(e)`; Source typing (`STy.explicit`) decides
whether it is allowed.

* `expr_cast`: the equation at a cast; `conservative`: cast-free expressions
  are spelled as before; `typed`: the spelling has the target type wherever
  Source allows the conversion; `Casts.decode`: the request decoder over it,
  with the unchanged guard.
* `unsigned_value`, `signed_value`: integer targets, as arithmetic. Source
  converts by wrapping (`convExplicitVal`); the wrapped number equals the
  number denoted by the formulas `lowBits` and `signedAt` write. The formulas
  are transcribed: the lemmas mention neither function nor their evaluation,
  and do not cover a literal argument (checked by `fitCheck` instead).

Not shown: that the model's elaborated cast (`castCapture`) runs to that
number (simulation obligation). Gaps: a cast the model accepts and Source
refuses (the model reduces `address(uint256)` modulo `2^160`), and a cast
among the raw arguments of a registered call. This decoder has no state
relation, initial matching or boundary of its own. No goal is stated.
-/
namespace Solidity.Correctness.Lowering.Total.Decode.Casts

open Source (Syn)
open CallSpellExt

/-- The Source explicit conversion `T(a)` to an elementary type. -/
def conversion (el : Source.Elem) (h : el ≠ .addressPayable) (a : Syn .expr) : Syn .expr :=
  .call (.elemType el h) (.positional (.cons a .nil))

/-- The integer type of a cast name read by `castTy?`. -/
def intTarget : PrimTy × Nat → Option (Syn .expr → Syn .expr)
  | (p, n) =>
    if h : n % 8 = 0 ∧ 8 ≤ n ∧ n ≤ 256 then
      match p with
      | .uint => some (conversion (.int false n h) (by simp))
      | .int => some (conversion (.int true n h) (by simp))
      | .bool => none
    else none

/-- The conversion a raw callee name stands for, if it is a cast name:
`address`, `bytesN`, `uintN`/`intN` and `uint`/`int`. -/
def target (f : String) : Option (Syn .expr → Syn .expr) :=
  if f = "address" then some (conversion .address (by decide))
  else match bytesTy? f with
    | some n =>
      if h : 1 ≤ n ∧ n ≤ 32 then some (conversion (.fixedBytes n h) (by simp)) else none
    | none => (castTy? f).bind intTarget

/-- The one argument of a one-argument list. -/
def single : Syn (.list .expr) → Option (Syn .expr)
  | .cons a .nil => some a
  | _ => none

/-- An unclaimed call: a conversion for a one-argument cast name, else a call. -/
def call (f : String) (args : List RawExpr) (spelled : Option (Syn (.list .expr))) :
    Option (Syn .expr) :=
  match target f, args with
  | some conv, [_] => (spelled.bind single).map conv
  | _, _ => spelled.map fun args => .call (.ident f) (.positional args)

variable (T : Tables) (R : Registry)

mutual
/-- Expressions: as `Calls.expr`, and an unclaimed one-argument call of a cast
name is the explicit conversion of its decoded argument. -/
def expr : RawExpr → Option (Syn .expr)
  | .num n => some (num n)
  | .name x => some (.ident x)
  | .bool b => some (.lit (.bool b))
  | .field e f => (expr e).map (.member · f)
  | .index e k => do pure (.index (← expr e) (.some (← expr k)))
  | .binop op a b => do pure ((← binop op) (← expr a) (← expr b))
  | .unop .neg a => (expr a).map (.unaryPrefix .neg)
  | .unop .not a => (expr a).map (.unaryPrefix .not)
  | .unop .bnot a => (expr a).map (.unaryPrefix .bitNot)
  | .unop .toInt a => (expr a).map fun a =>
      .call (.elemType intElem (by decide)) (.positional (.cons a .nil))
  | .unop .toUint a => (expr a).map fun a =>
      .call (.elemType uintElem (by decide)) (.positional (.cons a .nil))
  | .ternary c a b => do pure (.cond (← expr c) (← expr a) (← expr b))
  | .incDec .preInc e => (expr e).map (.unaryPrefix .inc)
  | .incDec .preDec e => (expr e).map (.unaryPrefix .dec)
  | .incDec .postInc e => (expr e).map (.unarySuffix .inc)
  | .incDec .postDec e => (expr e).map (.unarySuffix .dec)
  | .call f args =>
      match R.lookup f with
      | some c => c.spell args
      | none => call f args (exprs args)
  | .modular op a b k => do
      pure (.call (.ident op.toStr)
        (.positional (.cons (← expr a) (.cons (← expr b) (.cons (← expr k) .nil)))))
  | .env k => T.env k
  | .tuple (a :: b :: rest) => do
      pure (.tuple (.some (← expr a)) (.cons (.some (← expr b)) (← components rest)))
  | .assign l r => do pure (.assign .assign (← expr l) (← expr r))
  | .opAssign op l r => do pure (.assign (← assignOp op) (← expr l) (← expr r))
  | _ => none
/-- Argument lists, in order. -/
def exprs : List RawExpr → Option (Syn (.list .expr))
  | [] => some .nil
  | e :: es => do pure (.cons (← expr e) (← exprs es))
/-- Tuple components. -/
def components : List RawExpr → Option (Syn (.list (.opt .expr)))
  | [] => some .nil
  | e :: es => do pure (.cons (.some (← expr e)) (← components es))
end

variable {T : Tables} {R : Registry}

/-- **The equation at a cast**: an unclaimed call of a cast name with one
argument is the conversion of the decoded argument, and a gap exactly where
the argument is. -/
theorem expr_cast {f : String} {conv : Syn .expr → Syn .expr} (a : RawExpr)
    (unclaimed : R.lookup f = none) (cast : target f = some conv) :
    expr T R (.call f [a]) = (expr T R a).map conv := by
  simp only [expr, unclaimed, call, cast, exprs]
  cases expr T R a <;> rfl

/-- Whether the node is a one-argument call of a cast name. -/
def isCast : RawExpr → Bool
  | .call f [_] => (target f).isSome
  | _ => false

/-- No one-argument call of a cast name anywhere in the expression. -/
def CastFree (e : RawExpr) : Prop := e.any isCast = false

mutual
/-- **Conservative**: an expression with no cast is spelled as by the
registered-call decoder. The premise is the compatibility domain, not an
admission restriction. -/
theorem conservative : (e : RawExpr) → CastFree e → expr T R e = Calls.expr T R e
  | .num _, _ | .name _, _ | .bool _, _ | .env _, _ | .newArr .., _
  | .named .., _ | .tuple [], _ | .tuple [_], _ => rfl
  | .field e f, h => by
      simp only [CastFree, RawExpr.any, isCast, Bool.false_or] at h
      simp [expr, Calls.expr, conservative e h]
  | .index a b, h | .binop _ a b, h | .assign a b, h | .opAssign _ a b, h => by
      simp only [CastFree, RawExpr.any, isCast, Bool.false_or, Bool.or_eq_false_iff] at h
      simp [expr, Calls.expr, conservative a h.1, conservative b h.2]
  | .unop op a, h | .incDec op a, h => by
      simp only [CastFree, RawExpr.any, isCast, Bool.false_or] at h
      cases op <;> simp [expr, Calls.expr, conservative a h]
  | .ternary a b c, h | .modular _ a b c, h => by
      simp only [CastFree, RawExpr.any, isCast, Bool.false_or, Bool.or_eq_false_iff] at h
      simp [expr, Calls.expr, conservative a h.1.1, conservative b h.1.2, conservative c h.2]
  | .call f args, h => by
      simp only [CastFree, RawExpr.any, Bool.or_eq_false_iff] at h
      have children : ∀ e ∈ args, CastFree e := by
        intro e he
        simpa only [CastFree, Bool.not_eq_true] using
          (List.any_eq_false.mp h.2) ⟨e, he⟩ (List.mem_attach _ _)
      have same := conservative_args args children
      cases found : R.lookup f with
      | some c => simp [expr, Calls.expr, found]
      | none =>
        cases cast : target f with
        | none => simp [expr, Calls.expr, found, call, cast, same]
        | some conv =>
          rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
          · simp [expr, Calls.expr, found, call, cast, same]
          · simp [isCast, cast] at h
          · simp [expr, Calls.expr, found, call, cast, same]
  | .tuple (a :: b :: rest), h => by
      simp only [CastFree, RawExpr.any, isCast, Bool.false_or] at h
      have children : ∀ e ∈ a :: b :: rest, CastFree e := by
        intro e he
        simpa only [CastFree, Bool.not_eq_true] using
          (List.any_eq_false.mp h) ⟨e, he⟩ (List.mem_attach _ _)
      simp [expr, Calls.expr, conservative a (children a (by simp)),
        conservative b (children b (by simp)),
        conservative_components rest (fun e he => children e (by simp [he]))]
theorem conservative_args : (es : List RawExpr) → (∀ e ∈ es, CastFree e) →
    exprs T R es = Calls.exprs T R es
  | [], _ => rfl
  | e :: es, h => by
      simp [exprs, Calls.exprs, conservative e (h e (by simp)),
        conservative_args es (fun a ha => h a (by simp [ha]))]
theorem conservative_components : (es : List RawExpr) → (∀ e ∈ es, CastFree e) →
    components T R es = Calls.components T R es
  | [], _ => rfl
  | e :: es, h => by
      simp [components, Calls.components, conservative e (h e (by simp)),
        conservative_components es (fun a ha => h a (by simp [ha]))]
end

/-! ## Typing and value faithfulness -/

/-- The conversion has the target type wherever Source allows it. -/
def typed {Γ : Source.Ctx} {a : Syn .expr} {σ : Source.STy} (el : Source.Elem)
    (h : el ≠ .addressPayable) (argument : Source.Typed Γ a σ)
    (allowed : σ.explicit Γ.isBase Γ.mapFree (el.ty σ.convLoc) = true) :
    Source.Typed Γ (conversion el h a) (el.ty σ.convLoc) :=
  .convElem argument rfl allowed

/-- **Unsigned targets** wrap to the word modulo `2^N` (the `lowBits` formula). -/
theorem unsigned_value {n : Nat} (width : n ≤ 256) (x : Int) :
    Source.wrapBits false n x = (x % ((2 ^ 256 : Nat) : Int)) % ((2 ^ n : Nat) : Int) := by
  have divides : ((2 ^ n : Nat) : Int) ∣ ((2 ^ 256 : Nat) : Int) :=
    Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 width)
  simp only [Source.wrapBits, Bool.false_eq_true, false_and, if_false]
  exact (Int.emod_emod_of_dvd x divides).symm

/-- **Signed targets**: the wrapped number is the argument moved by
`2^(N-1)`, cut to `N` bits and moved back, the formula `signedAt` writes. -/
theorem signed_value {n : Nat} (width : 1 ≤ n) (x : Int) :
    Source.wrapBits true n x =
      (x + ((2 ^ (n - 1) : Nat) : Int)) % ((2 ^ n : Nat) : Int) - ((2 ^ (n - 1) : Nat) : Int) := by
  have double : ((2 ^ n : Nat) : Int) = 2 * ((2 ^ (n - 1) : Nat) : Int) := by
    rw [Source.two_pow_succ_pred width]; simp
  have positive : (0 : Int) < ((2 ^ (n - 1) : Nat) : Int) :=
    Int.natCast_pos.mpr (Nat.pow_pos (by decide))
  have top : Source.bitsHi true n = ((2 ^ (n - 1) : Nat) : Int) - 1 := by
    have one : 1 ≤ 2 ^ (n - 1) := Nat.pow_pos (by decide)
    simp only [Source.bitsHi, if_true]
    omega
  simp only [Source.wrapBits, true_and, top]
  rw [double]
  generalize ((2 ^ (n - 1) : Nat) : Int) = half at positive
  rw [← Int.emod_add_emod x (2 * half) half]
  have low := Int.emod_nonneg x (show (2 * half : Int) ≠ 0 by omega)
  have high := Int.emod_lt_of_pos x (show (0 : Int) < 2 * half by omega)
  generalize x % (2 * half) = r at low high
  split
  · have step := Int.add_mul_emod_self_right (a := r + half - 2 * half) (b := 1) (c := 2 * half)
    rw [show r + half - 2 * half + 1 * (2 * half) = r + half by omega] at step
    rw [step, Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega

/-- **The request decoder with casts**: `WithExpr.decode` over `Casts.expr`. -/
def decode (T : Tables) (R : Registry) : Request → Option SourceProgram :=
  WithExpr.decode T (expr T R)

/-- Reading casts cannot bypass the request guard. -/
theorem decode_guard {r : Request} {s : SourceProgram} (h : decode T R r = some s) :
    plain r = true :=
  WithExpr.decode_guard T _ h

end Solidity.Correctness.Lowering.Total.Decode.Casts
