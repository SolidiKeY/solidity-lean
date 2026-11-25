import Solidity.Correctness.Lowering.Total.ArgumentInference

/-! Scalar argument inference: nested Boolean arguments, scalar locals, number
literals and mixed lists, by the family theorems and by `#guard` on the actual
inference; the boundaries (missing local, wrong type, too little fuel) fail; and
the call theorem `alias_infer_scalar` on `h(x && !y, n)` over an assembled unit. -/
namespace Solidity.Examples.Lowering.Total.ArgumentInference

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.Decode
open Solidity.Correctness.Lowering.Total.Decode.Callee
open Solidity.Correctness.Lowering.Total.CalleeSelection
open Solidity.Correctness.Lowering.Total.CalleeInference
open Solidity.Correctness.Lowering.Total.ArgumentInference
open Solidity.Source (STy Syn)

/-- `uint256`. -/
def u256 : STy := .int Source.IntTy.u256
/-- Locals `bool x; bool y; uint256 n;`, innermost first. -/
def locs : List (String × STy) := [("x", .bool), ("y", .bool), ("n", u256)]
/-- A context over any unit with those locals. -/
def ctx (u : Syn .unit) : Source.Ctx := { env := u.env, scope := some "C", locals := locs }
/-- The empty unit's context. -/
def Γ0 : Source.Ctx := ctx (Syn.unit .nil)

/-- The positional argument list of `es`, in order. -/
def args : List (Syn .expr) → Syn (.list .expr)
  | [] => .nil
  | e :: es => .cons e (args es)

theorem argExprs_args : ∀ l : List (Syn .expr), argExprs (args l) = l
  | [] => by simp [args, argExprs]
  | e :: l => by simp [args, argExprs, argExprs_args l]

def x : Syn .expr := .ident "x"
def y : Syn .expr := .ident "y"
def n : Syn .expr := .ident "n"
def tru : Syn .expr := .lit (.bool true)
/-- `7`. -/
def seven : Syn .expr := .lit (.num (.dec 7 0 0))
/-- `!(x && (y || true)) == (x ? y : !y)`. -/
def nested : Syn .expr :=
  .equality .eq (.unaryPrefix .not (.and x (.or y tru))) (.cond x y (.unaryPrefix .not y))
/-- `x != !(true && y)`. -/
def neq : Syn .expr := .equality .ne x (.unaryPrefix .not (.and tru y))

/-! ## The actual inference -/

#guard (Source.Typed.infer Γ0 nested).map (·.1) = some .bool
#guard (Source.Typed.infer Γ0 neq).map (·.1) = some .bool
#guard (Source.Typed.infer Γ0 n).map (·.1) = some u256
#guard (Source.Typed.infer Γ0 seven).map (·.1) = some (.rational (Source.Q.ofInt 7))
#guard (Source.TypedArgs.infer Γ0 (args [nested, n, seven, x])).map (·.1) =
  some [.bool, u256, .rational (Source.Q.ofInt 7), .bool]
-- Boundaries: a missing local, a wrong operand type, too little fuel.
#guard (Source.Typed.infer Γ0 (.and x (.ident "z"))).map (·.1) = none
#guard (Source.Typed.infer Γ0 (.unaryPrefix .not n)).map (·.1) = none
#guard (Source.Typed.infer Γ0 (.and x n)).map (·.1) = none
#guard (Source.Typed.inferN 2 Γ0 (.unaryPrefix .not (.unaryPrefix .not x))).map (·.1) = none

/-! ## The family theorems -/

/-- `x` and `y` read local slots 0 and 1, of type `bool`, in any unit. -/
theorem bx (u : Syn .unit) : BoolArg (ctx u) x := .loc (i := 0) rfl rfl
theorem bY (u : Syn .unit) : BoolArg (ctx u) y := .loc (i := 1) rfl rfl

/-- `!(x && (y || true)) == (x ? y : !y)` is a Boolean argument in any unit. -/
theorem nested_bool (u : Syn .unit) : BoolArg (ctx u) nested :=
  .eq .eq (.not (.and (bx u) (.or (bY u) (.lit true)))) (.cond (bx u) (bY u) (.not (bY u)))

/-- It infers to `bool` at `Typed.infer`'s fuel, in any unit. -/
example (u : Syn .unit) : ∃ d, Source.Typed.infer (ctx u) nested = some ⟨.bool, d⟩ :=
  (ScalarArg.bool (nested_bool u)).infer

/-- `x != !(true && y)`: inequality, at any fuel above its node count. -/
example (u : Syn .unit) :
    ∃ d, ∀ m, neq.nodes.length < m → Source.Typed.inferN m (ctx u) neq = some ⟨.bool, d⟩ :=
  BoolArg.inferN (.eq .ne (bx u) (.not (.and (.lit true) (bY u))))

/-- The mixed list `(nested, n, 7, x)`: Boolean, `uint256` local, literal, Boolean local. -/
theorem mixed (u : Syn .unit) :
    ScalarArgs (ctx u) (argExprs (args [nested, n, seven, x]))
      [.bool, u256, .rational (Source.NumLit.dec 7 0 0).value, .bool] := by
  rw [argExprs_args]
  exact .cons (.bool (nested_bool u)) (.cons (.loc (x := "n") (i := 2) rfl rfl) (.cons (.num 7 0 0)
    (.cons (.bool (bx u)) .nil)))

/-- The list infers in order at `TypedArgs.infer`'s fuel. -/
example (u : Syn .unit) : ∃ da, Source.TypedArgs.infer (ctx u) (args [nested, n, seven, x]) =
    some ⟨[.bool, u256, .rational (Source.NumLit.dec 7 0 0).value, .bool], da⟩ :=
  scalarArgs_argsInfer (mixed u)

/-- Position 3 at the budget `args.nodes.length + 2 - 3` of `alias_infer`. -/
example (u : Syn .unit) : ∃ d, Source.Typed.inferN
    ((args [nested, n, seven, x]).nodes.length + 2 - 3) (ctx u) x = some ⟨.bool, d⟩ :=
  scalarArgs_each_infer (mixed u) 3 x .bool (by simp [argExprs_args]) rfl

/-! ## Boundaries -/

/-- Missing local: `z` is not declared in the empty unit. -/
example : Source.Typed.inferN 5 Γ0 (.ident "z") = none := inferN_ident_none rfl

/-- Wrong type: `!n` with `n : uint256`. -/
example : Source.Typed.inferN 3 Γ0 (.unaryPrefix .not n) = none :=
  inferN_not_none (inferN_loc (k := 1) (i := 2) rfl rfl) (by decide)

/-- Too little fuel: three arguments need more than three units. -/
example : Source.TypedArgs.inferN 3 Γ0 (args [x, y, n]) = none :=
  argsN_short (by simp [args, argExprs])

/-! ## The call theorem -/

/-- `function h(bool p, uint q) internal returns (bool r) {}`. -/
def hDecl : FunDecl :=
  { sourceDecl := some { name := "h", callable := .local .internalFn },
    params := [("p", .prim .bool), ("q", .prim .uint)], rets := [("r", .prim .bool)], body := [] }
/-- The one entry `h_0`. -/
def fs : List (Name × FunDecl) := [("h_0", hDecl)]

/-- The retained parameter slots `bool p, uint q`. -/
theorem paramSlots : Slots [] [("p", Ty.prim .bool), ("q", Ty.prim .uint)] [.bool, u256] :=
  .cons ⟨.bool, .bool, rfl, rfl, rfl, .bool⟩ (.cons ⟨.uint, .int false 256 (by decide), rfl, rfl,
    rfl, .uint _ rfl⟩ .nil)

/-- `h(x && !y, n)` infers to `h`'s return type at `Typed.infer`'s fuel: every
argument premise comes from `ScalarArgs`. -/
example {u} (hu : Callee.withFunctions tablesS [] "C" .nil fs = some u) :
    ∃ rs, ∃ d, Source.Typed.infer (ctx u)
      (.call (.ident "h") (.positional (args [.and x (.unaryPrefix .not y), n]))) =
        some ⟨STy.ret rs, d⟩ := by
  obtain ⟨_, rs, _, _, _, _, _, h⟩ :=
    alias_infer_scalar (Γ := ctx u) (a := "h_0") (index := 0) (σs := [.bool, u256])
      (source := { name := "h", callable := .local .internalFn }) hu rfl rfl rfl rfl rfl
      (by decide) rfl rfl paramSlots rfl
      (fun j e s hj hne hs hn => by
        rcases j with _ | j
        · exact absurd rfl hne
        · simp [fs] at hj)
      (fun p hp => by cases hp)
      (by rw [argExprs_args]
          exact .cons (.bool (.and (bx u) (.not (bY u)))) (.cons (.loc (x := "n") (i := 2) rfl rfl) .nil))
  exact ⟨rs, _, h⟩

/-! ## Axiom guards: only the standard axioms -/

/-- info: 'Solidity.Correctness.Lowering.Total.ArgumentInference.BoolArg.inferN' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Correctness.Lowering.Total.ArgumentInference.BoolArg.inferN

/-- info: 'Solidity.Correctness.Lowering.Total.ArgumentInference.ScalarArg.inferN' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Correctness.Lowering.Total.ArgumentInference.ScalarArg.inferN

/-- info: 'Solidity.Correctness.Lowering.Total.ArgumentInference.scalarArgs_argsN' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Correctness.Lowering.Total.ArgumentInference.scalarArgs_argsN

/-- info: 'Solidity.Correctness.Lowering.Total.ArgumentInference.alias_inferN_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Correctness.Lowering.Total.ArgumentInference.alias_inferN_scalar

/-- info: 'Solidity.Correctness.Lowering.Total.ArgumentInference.alias_infer_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Correctness.Lowering.Total.ArgumentInference.alias_infer_scalar

end Solidity.Examples.Lowering.Total.ArgumentInference
