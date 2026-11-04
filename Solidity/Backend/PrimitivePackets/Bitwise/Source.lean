import Solidity.Source.Eval

/-! Unsigned byte-width bitwise value transport. Operands are arbitrary runtime
naturals in the declared Source range; no literal-evaluation premise is used. -/
namespace Solidity.Backend.PrimitivePackets.Bitwise

open Solidity.Source

/-- Precisely the three Source constructors owned by this packet. -/
def Supported (op : Source.BinOp) : Prop :=
  op = .bitAnd ∨ op = .bitOr ∨ op = .bitXor

/-- Legal unsigned Source type, keeping its original dependent validity proof. -/
def unsigned (w : Fin 32) : IntTy :=
  ⟨false, 8 * (w.val + 1), by omega⟩

/-- The actual natural reading of these existing bitwise constructors. -/
def value (op : Source.BinOp) (x y : Nat) : Nat :=
  match op with
  | .bitAnd => x &&& y
  | .bitOr => x ||| y
  | .bitXor => x ^^^ y
  | _ => 0

theorem value_lt (op : Source.BinOp) (hop : Supported op) (n x y : Nat)
    (hx : x < 2 ^ n) (hy : y < 2 ^ n) : value op x y < 2 ^ n := by
  rcases hop with rfl | rfl | rfl
  · exact Nat.and_lt_two_pow _ hy
  · exact Nat.or_lt_two_pow hx hy
  · exact Nat.xor_lt_two_pow hx hy

/-- The incoming Source value is clean because it is an actual unsigned value,
not because arbitrary dirty EVM words are silently normalized. -/
def operand {D : Layout} (w : Fin 32) (x : Nat)
    (hx : x < 2 ^ (unsigned w).bits) : Source.Val D (.int (unsigned w)) :=
  .int (x : Int) (by
    simp only [IntTy.lo, IntTy.hi, unsigned, Bool.false_eq_true, if_false]
    constructor
    · omega
    · exact_mod_cast Nat.le_sub_one_of_lt hx)

/-- Exact Source binVal result at every byte-multiple unsigned width. Checked
and unchecked mode agree here; integer wrapping remains the existing operation. -/
theorem binVal_operand {D : Layout} (checked : Bool) (w : Fin 32)
    (op : Source.BinOp) (hop : Supported op) (x y : Nat)
    (hx : x < 2 ^ (unsigned w).bits) (hy : y < 2 ^ (unsigned w).bits) :
    Source.binVal checked op (operand (D := D) w x hx) (operand w y hy) =
      .ok (operand w (value op x y) (value_lt op hop _ _ _ hx hy)) := by
  have hb : (0 : Int) ≤ (value op x y : Int) := Int.natCast_nonneg _
  have ht : (value op x y : Int) < ((2 ^ (unsigned w).bits : Nat) : Int) :=
    Int.ofNat_lt.mpr (value_lt op hop _ _ _ hx hy)
  rcases hop with rfl | rfl | rfl
  · change Except.ok (Source.Val.int (((x &&& y : Nat) : Int) % ((2 ^ (unsigned w).bits : Nat) : Int)) _) = _
    simp only [value] at hb ht
    congr 2
    exact Int.emod_eq_of_lt hb ht
  · change Except.ok (Source.Val.int (((x ||| y : Nat) : Int) % ((2 ^ (unsigned w).bits : Nat) : Int)) _) = _
    simp only [value] at hb ht
    congr 2
    exact Int.emod_eq_of_lt hb ht
  · change Except.ok (Source.Val.int (((x ^^^ y : Nat) : Int) % ((2 ^ (unsigned w).bits : Nat) : Int)) _) = _
    simp only [value] at hb ht
    congr 2
    exact Int.emod_eq_of_lt hb ht

/-- The actual resolved Source local expression, for both evaluation orders. -/
def sourceExpr (E : Source.Env) (w : Fin 32) (op : Source.BinOp) :
    Source.RExpr E [.int (unsigned w), .int (unsigned w)] (.int (unsigned w)) :=
  .binary op (.local .here) (.local (.there .here))

/-- Both pipelines evaluate these runtime-local leaves without changing locals,
state or horizon policy. Three units are needed by binary/pair/local recursion. -/
theorem evalE_operand {E : Source.Env} (G : Source.Glob E) (F : Source.Fr)
    (n : Nat) (w : Fin 32) (op : Source.BinOp) (hop : Supported op)
    (x y : Nat) (hx : x < 2 ^ (unsigned w).bits) (hy : y < 2 ^ (unsigned w).bits)
    (s : Source.St E) :
    let ls := Source.Locals.cons (operand (D := E.layout) w x hx)
      (.cons (operand w y hy) .nil)
    (Source.evalE G F (n + 3) (sourceExpr E w op)).run (ls, s) =
      (.ok (.val (operand w (value op x y) (value_lt op hop _ _ _ hx hy))), (ls, s)) := by
  rcases hop with rfl | rfl | rfl <;>
    cases hp : G.pipeline <;>
    simp only [sourceExpr, Source.evalE, Source.evalPair, hp, reduceCtorEq, decide_false, Bool.false_or, Bool.false_eq_true, if_false] <;>
    simp only [Source.EM.locals, Source.getV, Source.EM.lift, Source.RVal.get,
      Source.Locals.get, ExceptT.run, ExceptT.bind, ExceptT.pure,
      StateT.bind, StateT.pure, Bind.bind, Pure.pure, MonadStateOf.get,
      MonadLift.monadLift, ExceptT.lift, StateT.get, ExceptT.bindCont,
      Functor.map, StateT.map, Except.pure, ExceptT.mk, get, getThe, liftM, MonadLiftT.monadLift]

  all_goals rw [binVal_operand F.checked w _ (by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)) x y hx hy] <;> rfl


/-- Below the binary/pair/local horizon there is an actual timeout, not a
successful evaluation inferred from the mathematical bitwise denotation. -/
theorem evalE_two {E : Source.Env} (G : Source.Glob E) (F : Source.Fr)
    (w : Fin 32) (op : Source.BinOp) (hop : Supported op)
    (ls : Source.Locals E.layout [.int (unsigned w), .int (unsigned w)])
    (s : Source.St E) :
    (Source.evalE G F 2 (sourceExpr E w op)).run (ls, s) =
      (.error .timeout, (ls, s)) := by
  rcases hop with rfl | rfl | rfl <;>
    cases hp : G.pipeline <;>
    simp only [sourceExpr, Source.evalE, Source.evalPair, hp,
      reduceCtorEq, decide_false, Bool.false_or, Bool.false_eq_true, if_false] <;> rfl


end Solidity.Backend.PrimitivePackets.Bitwise
