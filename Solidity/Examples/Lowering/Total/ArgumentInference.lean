import Solidity.Correctness.Lowering.Total.ArgumentInference

/-! Scalar argument inference: nested Boolean arguments, scalar locals, number
literals and mixed lists, by the family theorems and by `#guard` on the actual
inference; the boundaries (missing local, wrong type, too little fuel) fail; and
the call theorem on the decoder's raw spelling, `alias_infer_raw`, for
`h(x && !y, n)` in any unit the assembly returns. -/
namespace Solidity.Examples.Lowering.Total.ArgumentInference

open Solidity.Correctness.Lowering.Total
open Decode Decode.Callee CalleeSelection CalleeInference ArgumentInference
open Solidity.Source (STy Syn)

def u256 : STy := .int Source.IntTy.u256
/-- Locals `bool x; bool y; uint256 n;`, innermost first, over any unit. -/
def ctx (u : Syn .unit) : Source.Ctx :=
  { env := u.env, scope := some "C", locals := [("x", .bool), ("y", .bool), ("n", u256)] }
def Γ0 : Source.Ctx := ctx (Syn.unit .nil)

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
def seven : Syn .expr := .lit (.num (.dec 7 0 0))
/-- `!(x && (y || true)) == (x ? y : !y)`. -/
def nested : Syn .expr :=
  .equality .eq (.unaryPrefix .not (.and x (.or y tru))) (.cond x y (.unaryPrefix .not y))
/-- `x != !(true && y)`. -/
def neq : Syn .expr := .equality .ne x (.unaryPrefix .not (.and tru y))

#guard (Source.Typed.infer Γ0 nested).map (·.1) = some .bool
#guard (Source.Typed.infer Γ0 neq).map (·.1) = some .bool
#guard (Source.TypedArgs.infer Γ0 (args [nested, n, seven, x])).map (·.1) =
  some [.bool, u256, .rational (Source.Q.ofInt 7), .bool]
#guard (Source.Typed.infer Γ0 (.and x n)).map (·.1) = none  -- wrong type

/-- `x` and `y` read local slots 0 and 1, of type `bool`, in any unit. -/
theorem bx (u : Syn .unit) : BoolArg (ctx u) x := .loc (i := 0) rfl rfl
theorem bY (u : Syn .unit) : BoolArg (ctx u) y := .loc (i := 1) rfl rfl

/-- `!(x && (y || true)) == (x ? y : !y)` is a Boolean argument in any unit. -/
theorem nested_bool (u : Syn .unit) : BoolArg (ctx u) nested :=
  .eq .eq (.not (.and (bx u) (.or (bY u) (.lit true)))) (.cond (bx u) (bY u) (.not (bY u)))

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
  scalarArgs_argsN (mixed u) (Nat.lt_succ_self _)

/-- Position 3 at the budget `args.nodes.length + 2 - 3` of `alias_infer`. -/
example (u : Syn .unit) : ∃ d, Source.Typed.inferN
    ((args [nested, n, seven, x]).nodes.length + 2 - 3) (ctx u) x = some ⟨.bool, d⟩ :=
  scalarArgs_each_infer (mixed u) 3 x .bool (by simp [argExprs_args]) rfl

/-- Missing local: `z` is not declared in the empty unit. -/
example : Source.Typed.inferN 5 Γ0 (.ident "z") = none := inferN_ident_none rfl

/-- Wrong type: `!n` with `n : uint256`. -/
example : Source.Typed.inferN 3 Γ0 (.unaryPrefix .not n) = none :=
  inferN_not_none (inferN_loc (k := 1) (i := 2) rfl rfl) (by decide)

/-- Too little fuel: three arguments need more than three units. -/
example : Source.TypedArgs.inferN 3 Γ0 (args [x, y, n]) = none :=
  argsN_short (by simp [args, argExprs])

/-! ## The call theorem -/

/-- The one entry `h_0`: `function h(bool p, uint q) internal returns (bool r) {}`. -/
def fs : List (Name × FunDecl) :=
  [("h_0", { sourceDecl := some { name := "h", callable := .local .internalFn },
             params := [("p", .prim .bool), ("q", .prim .uint)], rets := [("r", .prim .bool)],
             body := [] })]

/-- The retained parameter slots `bool p, uint q`. -/
theorem paramSlots : Slots [] [("p", Ty.prim .bool), ("q", Ty.prim .uint)] [.bool, u256] :=
  .cons ⟨.bool, .bool, rfl, rfl, rfl, .bool⟩ (.cons ⟨.uint, .int false 256 (by decide), rfl, rfl,
    rfl, .uint _ rfl⟩ .nil)

/-- On the decoder's spelling: the raw call `h(x && !y, n)` is spelled by any
decoder version and infers to `h`'s return type, every argument premise derived
from the raw arguments and the context. -/
example (Te : Tables) {u} (hu : Callee.withFunctions tablesS [] "C" .nil fs = some u) :
    ∃ e, Te.expr (.call "h" [.binop .and (.name "x") (.unop .not (.name "y")), .name "n"]) =
      some e ∧ ∃ rs d, Source.Typed.infer (ctx u) e = some ⟨STy.ret rs, d⟩ := by
  obtain ⟨_, _, he, _, rs, _, _, _, _, _, h⟩ :=
    alias_infer_raw (Γ := ctx u) (a := "h_0") (index := 0) (σs := [.bool, u256]) Te
      (source := { name := "h", callable := .local .internalFn }) hu rfl rfl rfl rfl rfl
      (by decide) rfl rfl paramSlots rfl
      (fun j e s hj hne hs hn => by
        rcases j with _ | j
        · exact absurd rfl hne
        · simp [fs] at hj)
      (fun p hp => by cases hp)
      (.cons (.bool (.and (.name (x := "x") (i := 0) rfl rfl) (.not (.name (x := "y") (i := 1) rfl rfl))))
        (.cons (.name (x := "n") (i := 2) rfl rfl) .nil))
  exact ⟨_, he, rs, _, h⟩

-- Axiom guard: only the standard axioms.
/-- info: 'Solidity.Correctness.Lowering.Total.ArgumentInference.alias_infer_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms Solidity.Correctness.Lowering.Total.ArgumentInference.alias_infer_raw

end Solidity.Examples.Lowering.Total.ArgumentInference
