import Solidity.Correctness.Lowering.Total.ArithmeticInference


/-! Arithmetic argument inference: nested local/literal arithmetic, constant
folding, bitwise, shift, power, negation, comparisons, ordered arguments and a
call over them, each checked against the actual inferencer by `#guard`; and
the wrong-type, zero-divisor, unfolded, unsupported-spelling and
insufficient-fuel boundaries. -/
namespace Solidity.Examples.Lowering.Total.ArithmeticInference

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.Decode
open Solidity.Correctness.Lowering.Total.ArithmeticInference
open Solidity.Correctness.Lowering.Total.CalleeInference (argExprs)
open Solidity.Source (STy Syn Typed Q)

/-- `uint256`. -/
def u256 : STy := .int Source.IntTy.u256
/-- `int256`. -/
def i256 : STy := .int ⟨true, 256, by decide⟩
/-- Locals `uint x`, `uint y`, `int i`, `bool b` over any unit. -/
def ctx (u : Syn .unit) : Source.Ctx :=
  { env := u.env, scope := some "C",
    locals := [("x", u256), ("y", u256), ("i", i256), ("b", .bool)] }

variable {u : Syn .unit}

/-- The local `uint x` with its resolution and slot type. -/
theorem x : Infers (ctx u) (.name "x") u256 := .local (i := 0) (resolve_local rfl) rfl
/-- The local `uint y` with its resolution and slot type. -/
theorem y : Infers (ctx u) (.name "y") u256 := .local (i := 1) (resolve_local rfl) rfl
/-- The local `int i` with its resolution and slot type. -/
theorem i : Infers (ctx u) (.name "i") i256 := .local (i := 2) (resolve_local rfl) rfl
/-- The local `bool b` with its resolution and slot type. -/
theorem b : Infers (ctx u) (.name "b") .bool := .local (i := 3) (resolve_local rfl) rfl

/-- The type the actual `Typed.infer` gives the `tables1` spelling in the empty unit. -/
def inferTy (e : RawExpr) : Option (Option STy) :=
  (tables1.expr e).map fun s => (Typed.infer (ctx (.unit .nil)) s).map (·.1)
/-- The same at fuel `n`. -/
def inferTyN (n : Nat) (e : RawExpr) : Option (Option STy) :=
  (tables1.expr e).map fun s => (Typed.inferN n (ctx (.unit .nil)) s).map (·.1)

/-! ## Nested local/literal arithmetic -/

/-- `(x + 1) * y`. -/
def e1 : RawExpr := .binop .mul (.binop .add (.name "x") (.num 1)) (.name "y")

/-- In the family: `e1_infers`. -/
theorem e1_infers : Infers (ctx u) e1 u256 :=
  .arith rfl (.arith rfl x (.const rfl) rfl rfl rfl) y rfl rfl rfl

#guard depth e1 = 3
#guard inferTy e1 = some (some u256)
#guard inferTyN 3 e1 = some (some u256)
#guard inferTyN 2 e1 = some none


/-- At the actual `Typed.inferN`: `uint256` from fuel 3 on, nothing below. -/
example {s} (hs : tables1.expr e1 = some s) :
    ∃ d, Typed.inferN 3 (ctx u) s = some ⟨u256, d⟩ ∧ Typed.inferN 2 (ctx u) s = none :=
  let ⟨d, hd⟩ := e1_infers.inferN hs
  ⟨d, by rw [hd]; rfl, e1_infers.inferN_short hs (by decide)⟩

/-- A folded operand inside a non-constant sum: `x + 2 * 3`. -/
def e2 : RawExpr := .binop .add (.name "x") (.binop .mul (.num 2) (.num 3))

/-- In the family: `e2_infers`. -/
theorem e2_infers : Infers (ctx u) e2 u256 := .arith rfl x (.const rfl) rfl rfl rfl

#guard depth e2 = 2
#guard inferTy e2 = some (some u256)

/-! ## Constant folding wins before recursion -/

/-- `(2 + 3) * 4` is the constant `20` at fuel 1, whatever its nesting. -/
def c1 : RawExpr := .binop .mul (.binop .add (.num 2) (.num 3)) (.num 4)

#guard fold c1 = some (Q.ofInt 20)
#guard depth c1 = 1
#guard inferTyN 1 c1 = some (some (.rational (Q.ofInt 20)))

/-- In the family: `c1_infers`. -/
theorem c1_infers : Infers (ctx u) c1 (.rational (Q.ofInt 20)) := .const (by decide)

/-- `-(1 - 3)` and `~5` fold: `2` and `-6`. -/
example : fold (.unop .neg (.binop .sub (.num 1) (.num 3))) = some (Q.ofInt 2) := by decide
example : fold (.unop .bnot (.num 5)) = some (Q.ofInt (-6)) := by decide
/-- `1 << 3`, `17 >> 2`, `2 ** 10`, `6 & 3` fold. -/
example : fold (.binop .shl (.num 1) (.num 3)) = some (Q.ofInt 8) := by decide
example : fold (.binop .shr (.num 17) (.num 2)) = some (Q.ofInt 4) := by decide
example : fold (.binop .pow (.num 2) (.num 10)) = some (Q.ofInt 1024) := by decide
example : fold (.binop .band (.num 6) (.num 3)) = some (Q.ofInt 2) := by decide

/-! ## Bitwise, shift, exponentiation, negation, complement -/

/-- In the family: `and_infers`. -/
theorem and_infers : Infers (ctx u) (.binop .band (.name "x") (.name "y")) u256 :=
  .bit rfl x y rfl rfl
/-- Model `>>` is spelled `sar`: `x >> 2` at `x`'s type. -/
theorem shr_infers : Infers (ctx u) (.binop .shr (.name "x") (.num 2)) u256 :=
  .shift rfl x (.const rfl) rfl rfl rfl
/-- A constant shifted by a local is typed at `uint256`: `1 << x`. -/
theorem shl_infers : Infers (ctx u) (.binop .shl (.num 1) (.name "x")) u256 :=
  show Infers _ _ (STy.rational (Source.NumLit.dec 1 0 0).value).shiftTy from
    .shift rfl (.const rfl) x (by decide) rfl rfl
/-- In the family: `pow_infers`. -/
theorem pow_infers : Infers (ctx u) (.binop .pow (.name "x") (.num 2)) u256 :=
  .exp rfl x (.const rfl) rfl rfl rfl
/-- In the family: `neg_infers`. -/
theorem neg_infers : Infers (ctx u) (.unop .neg (.name "i")) i256 := .negInt i rfl
/-- In the family: `bnot_infers`. -/
theorem bnot_infers : Infers (ctx u) (.unop .bnot (.binop .bxor (.name "x") (.name "y"))) u256 :=
  .bitNot' (.bit rfl x y rfl rfl) rfl

example : Decode.binop .shr = some (.shift .sar) := rfl

#guard inferTy (.binop .band (.name "x") (.name "y")) = some (some u256)
#guard inferTy (.binop .shr (.name "x") (.num 2)) = some (some u256)
#guard inferTy (.binop .shl (.num 1) (.name "x")) = some (some u256)
#guard inferTy (.binop .pow (.name "x") (.num 2)) = some (some u256)
#guard inferTy (.unop .neg (.name "i")) = some (some i256)
#guard inferTy (.unop .bnot (.binop .bxor (.name "x") (.name "y"))) = some (some u256)

/-! ## Comparisons -/

/-- `x + 1 < y`. -/
def lt1 : RawExpr := .binop .lt (.binop .add (.name "x") (.num 1)) (.name "y")

/-- In the family: `lt1_infers`. -/
theorem lt1_infers : Infers (ctx u) lt1 .bool :=
  .order rfl (.arith rfl x (.const rfl) rfl rfl rfl) y rfl rfl
/-- In the family: `eq_infers`. -/
theorem eq_infers : Infers (ctx u) (.binop .neB (.name "x") (.num 0)) .bool :=
  .eq rfl x (.const rfl) rfl rfl
/-- Two constants compare at fuel 1, without operand inference: `1 < 2`. -/
theorem ltc_infers : Infers (ctx u) (.binop .lt (.num 1) (.num 2)) .bool :=
  .cmpConst (k := .order) rfl rfl rfl rfl

#guard inferTy lt1 = some (some .bool)
#guard inferTy (.binop .neB (.name "x") (.num 0)) = some (some .bool)
#guard depth (.binop .lt (.num 1) (.num 2)) = 1
#guard inferTyN 1 (.binop .lt (.num 1) (.num 2)) = some (some .bool)
/-- `1 == 2` likewise. -/
theorem eqc_infers : Infers (ctx u) (.binop .eqB (.num 1) (.num 2)) .bool :=
  .cmpConst (k := .eq) rfl rfl rfl rfl
#guard inferTyN 1 (.binop .eqB (.num 1) (.num 2)) = some (some .bool)

/-! ## Ordered arguments at their position-dependent fuels -/

/-- `(x + 1) * y`, `x + 1 < y`, `(2 + 3) * 4`. -/
def es : List RawExpr := [e1, lt1, c1]
/-- In the family: `σs`. -/
def σs : List STy := [u256, .bool, .rational (Q.ofInt 20)]

/-- In the family: `es_infers`. -/
theorem es_infers : ∀ (j : Nat) e σ, es[j]? = some e → σs[j]? = some σ → Infers (ctx u) e σ
  | 0, _, _, he, hσ => by cases he; cases hσ; exact e1_infers
  | 1, _, _, he, hσ => by cases he; cases hσ; exact lt1_infers
  | 2, _, _, he, hσ => by cases he; cases hσ; exact c1_infers
  | _ + 3, _, _, he, _ => by cases he

/-- The premises of `alias_infer` for any spelling of the list: position `j`
at fuel `args.nodes.length + 2 - j`. -/
example {T : Tables} {args} (hs : T.exprs es = some args) :
    σs.length = (argExprs args).length ∧
      ∀ (j : Nat) a σ, (argExprs args)[j]? = some a → σs[j]? = some σ →
        ∃ d, Typed.inferN (args.nodes.length + 2 - j) (ctx u) a = some ⟨σ, d⟩ :=
  args_infer hs rfl es_infers

/-- The premises of `alias_inferN` at fuel 5: budgets `4, 3, 2` against depths `3, 3, 1`. -/
example {T : Tables} {args} (hs : T.exprs es = some args) :
    σs.length = (argExprs args).length ∧
      ∀ (j : Nat) a σ, (argExprs args)[j]? = some a → σs[j]? = some σ →
        ∃ d, Typed.inferN (5 - 1 - j) (ctx u) a = some ⟨σ, d⟩ :=
  args_inferN hs rfl es_infers fun j e he => by
    rcases j with _ | _ | _ | j <;> cases he <;> decide

/-- The list infers through the actual `TypedArgs.inferN` at fuel 5 and not at
fuel 4 (position 1 would get fuel 2 for depth 3). -/
def argsTyN (n : Nat) : Option (Option (List STy)) :=
  (tables1.exprs es).map fun args =>
    (Source.TypedArgs.inferN n (ctx (.unit .nil)) args).map (·.1)
#guard argsTyN 5 = some (some σs)
#guard argsTyN 4 = some none

/-! ## A call over ordered arithmetic arguments -/

section call
open Solidity.Correctness.Lowering.Total.Decode.Callee
open Solidity.Correctness.Lowering.Total.CalleeSelection

/-- `function h(uint p, bool q) internal returns (uint r) {}`. -/
def fs : List (Name × FunDecl) :=
  [("h_0", { sourceDecl := some { name := "h", callable := .local .internalFn },
             params := [("p", .prim .uint), ("q", .prim .bool)], rets := [("r", .prim .uint)],
             body := [] })]

/-- In the family: `paramSlots`. -/
theorem paramSlots : Slots [] [("p", Ty.prim .uint), ("q", Ty.prim .bool)] [u256, .bool] :=
  .cons ⟨.uint, .int false 256 (by decide), rfl, rfl, rfl, .uint _ rfl⟩
    (.cons ⟨.bool, .bool, rfl, rfl, rfl, .bool⟩ .nil)
/-- In the family: `retSlots`. -/
theorem retSlots : Slots [] [("r", Ty.prim .uint)] [u256] :=
  .cons ⟨.uint, .int false 256 (by decide), rfl, rfl, rfl, .uint _ rfl⟩ .nil

/-- `h((x + 1) * y, x + 1 < y)` infers to `uint256` at `Typed.infer`'s fuel:
both argument premises of `alias_infer` come from the family. -/
example {u'} (hu : Callee.withFunctions tablesS [] "C" .nil fs = some u') {args}
    (hs : tablesS.exprs [e1, lt1] = some args) :
    ∃ d, Typed.infer (ctx u') (.call (.ident "h") (.positional args)) = some ⟨u256, d⟩ := by
  obtain ⟨_, rs, _, hrs, _, _, _, h⟩ :=
    alias_infer_arith (Γ := ctx u') (a := "h_0") (index := 0) (σs := [u256, .bool])
      (source := { name := "h", callable := .local .internalFn }) hu rfl rfl rfl rfl rfl
      (by decide) rfl rfl paramSlots rfl
      (fun j e s hj hne hs hn => by
        rcases j with _ | j
        · exact absurd rfl hne
        · simp [fs] at hj)
      (fun p hp => by cases hp) hs rfl
      (fun j e σ he hσ => by
        rcases j with _ | _ | j
        · cases he; cases hσ; exact e1_infers
        · cases he; cases hσ; exact lt1_infers
        · cases he)
  cases slots_unique hrs retSlots
  exact ⟨_, h⟩

end call

/-! ## Boundaries -/

/-- Wrong type: `x + b` has no common type. -/
theorem wrong_type : Rejects (ctx u) (.binop .add (.name "x") (.name "b")) .incompatible :=
  .noCommon rfl (by decide) x b rfl rfl rfl
/-- Wrong signedness: `-x` on `uint256`. -/
theorem wrong_sign : Rejects (ctx u) (.unop .neg (.name "x")) .incompatible := .negUnsigned x rfl
/-- Wrong amount: `x << i` by a signed amount. -/
theorem wrong_amount : Rejects (ctx u) (.binop .shl (.name "x") (.name "i")) .incompatible :=
  .badAmount rfl (.inl rfl) x i rfl rfl
/-- `~b` on a boolean. -/
theorem wrong_bits : Rejects (ctx u) (.unop .bnot (.name "b")) .incompatible := .bitNot b rfl rfl
/-- Constant zero divisor: `x / 0`, `x % (1 - 1)`, and the constant `1 / 0`. -/
theorem zero_div : Rejects (ctx u) (.binop .div (.name "x") (.num 0)) .zeroDivisor :=
  .zeroDivisor rfl x (.const rfl) rfl
/-- In the family: `zero_mod`. -/
theorem zero_mod :
    Rejects (ctx u) (.binop .mod (.name "x") (.binop .sub (.num 1) (.num 1))) .zeroDivisor :=
  .zeroDivisor rfl x (.const (q := Q.ofInt 0) (by decide)) rfl
/-- In the family: `zero_const`. -/
theorem zero_const : Rejects (ctx u) (.binop .div (.num 1) (.num 0)) .zeroDivisor :=
  .zeroDivisor rfl (.const rfl) (.const rfl) rfl
/-- Two constants that do not fold: `1 << 5000` is past solc's bound. -/
theorem unfolded : Rejects (ctx u) (.binop .shl (.num 1) (.num 5000)) .unfolded :=
  .bin (k := .shift) rfl (.const rfl) (.const rfl) (by decide) rfl rfl
/-- A rejected operand rejects the nest: `(x / 0) + y < x`. -/
theorem nested_rejected :
    Rejects (ctx u) (.binop .lt (.binop .add (.binop .div (.name "x") (.num 0)) (.name "y"))
      (.name "x")) .zeroDivisor :=
  .left (k := .order) rfl (.left (k := .arith) rfl zero_div)

/-- Two constants that do not fold: `2 ** 5000`. -/
theorem unfolded_pow : Rejects (ctx u) (.binop .pow (.num 2) (.num 5000)) .unfolded :=
  .bin (k := .exp) rfl (.const rfl) (.const rfl) (by decide) rfl rfl
/-- A rejected right operand under `~` and `-`: `-(y & ~(x / 0))`. -/
theorem nested_right :
    Rejects (ctx u) (.unop .neg (.binop .band (.name "y")
      (.unop .bnot (.binop .div (.name "x") (.num 0))))) .zeroDivisor :=
  .negArg (.right (k := .bit) rfl (.bitNotArg zero_div))

/-- No fuel infers a rejected form. -/
example {T : Tables} {s n} (hs : T.expr (.binop .div (.name "x") (.num 0)) = some s) :
    Typed.inferN n (ctx u) s = none := (zero_div.sound hs).2 n

#guard inferTy (.binop .add (.name "x") (.name "b")) = some none
#guard inferTy (.unop .neg (.name "x")) = some none
#guard inferTy (.binop .shl (.name "x") (.name "i")) = some none
#guard inferTy (.unop .bnot (.name "b")) = some none
#guard inferTy (.binop .div (.name "x") (.num 0)) = some none
#guard inferTy (.binop .mod (.name "x") (.binop .sub (.num 1) (.num 1))) = some none
#guard inferTy (.binop .div (.num 1) (.num 0)) = some none
#guard inferTy (.binop .shl (.num 1) (.num 5000)) = some none
#guard inferTy (.binop .pow (.num 2) (.num 5000)) = some none
-- Division by a nonzero constant is admitted.
#guard inferTy (.binop .div (.name "x") (.num 2)) = some (some u256)

/-- Unsupported spelling: the wrapping operators are not decoded, nor is a nest over one. -/
example {T : Tables} {a b} : T.expr (.binop .addW a b) = none := expr_unspelled rfl
example {T : Tables} {a b c} : T.expr (.binop .add (.binop .mulW a b) c) = none :=
  expr_binop_none (.inl (expr_unspelled rfl))
#guard inferTy (.binop .addW (.name "x") (.name "y")) = none

/-- A rejected argument fails a call at every fuel: `f(y, x / 0)`. -/
example {T : Tables} {args n} {f : String}
    (hs : T.exprs [.name "y", .binop .div (.name "x") (.num 0)] = some args) :
    Typed.inferN n (ctx u) (.call (.ident f) (.positional args)) = none :=
  call_rejected hs (i := 1) rfl zero_div

/-! ## Axioms -/

/--
info: 'Solidity.Correctness.Lowering.Total.ArithmeticInference.Infers.sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Infers.sound

/--
info: 'Solidity.Correctness.Lowering.Total.ArithmeticInference.Rejects.sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Rejects.sound

/--
info: 'Solidity.Correctness.Lowering.Total.ArithmeticInference.alias_infer_arith' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms alias_infer_arith

/--
info: 'Solidity.Correctness.Lowering.Total.ArithmeticInference.alias_inferN_arith' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms alias_inferN_arith

/--
info: 'Solidity.Correctness.Lowering.Total.ArithmeticInference.args_infer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms args_infer

end Solidity.Examples.Lowering.Total.ArithmeticInference
