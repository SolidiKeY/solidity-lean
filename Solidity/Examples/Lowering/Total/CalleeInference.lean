import Solidity.Correctness.Lowering.Total.CalleeInference

/-! Actual call inference over assembled units: successful internal dispatch
with empty, single and two-argument lists (argument and return-slot order
kept), argument failure, duplicate entries, local shadowing, and the
competing conversion, struct and builtin branches, each with and without an
entry retaining the callee name. Execution is not checked. -/
namespace Solidity.Examples.Lowering.Total.CalleeInference

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.Decode
open Solidity.Correctness.Lowering.Total.Decode.Callee
open Solidity.Correctness.Lowering.Total.CalleeSelection
open Solidity.Correctness.Lowering.Total.CalleeInference
open Solidity.Source (STy Syn)

def internal : SourceCallable := .local .internalFn
/-- `function NAME(params) internal returns (rets) {}` with retained source identity. -/
def fn (name : String) (params : List (Name × Ty)) (rets : List (Name × Ty) := []) : FunDecl :=
  { sourceDecl := some { name, callable := internal }, params, rets, body := [] }
/-- The context of the generated contract `C` over the assembled unit. -/
def ctx (u : Syn .unit) (locals : List (String × STy)) : Source.Ctx :=
  { env := u.env, scope := some "C", locals }
def args : List (Syn .expr) → Syn (.list .expr)
  | [] => .nil
  | e :: es => .cons e (args es)
/-- `f(es…)`. -/
def call (f : String) (es : List (Syn .expr)) : Syn .expr := .call (.ident f) (.positional (args es))
def tru : Syn .expr := .lit (.bool true)
def one : Syn .expr := .lit (.num (.dec 1 0 0))
def u256 : STy := .int Source.IntTy.u256

/-- The type `Typed.infer` gives `e` in the assembled contract, if it assembles. -/
def inferTy (pre : Syn (.list (.part false))) (fs : List (Name × FunDecl))
    (locals : List (String × STy)) (e : Syn .expr) : Option (Option STy) :=
  (Callee.withFunctions tablesS [] "C" pre fs).map fun u =>
    (Source.Typed.infer (ctx u locals) e).map (·.1)

/-- `f(bool) returns (uint)`, `g()`, `h(bool, uint) returns (bool, uint)`. -/
def fs1 : List (Name × FunDecl) :=
  [("f_0", fn "f" [("p", .prim .bool)] [("r", .prim .uint)]),
   ("g_0", fn "g" []),
   ("h_0", fn "h" [("p", .prim .bool), ("q", .prim .uint)] [("r", .prim .bool), ("s", .prim .uint)])]
/-- Prefix `struct S { bool b; }`. -/
def structS : Syn (.list (.part false)) :=
  .cons (.struct "S" (.structMember (.elem .bool) "b") .nil) .nil

/-! ## Internal dispatch, argument order and return slots -/

#guard inferTy .nil fs1 [] (call "f" [tru]) = some (some u256)
#guard inferTy .nil fs1 [] (call "g" []) = some (some (.tuple []))
#guard inferTy .nil fs1 [] (call "h" [tru, one]) = some (some (.tuple [.bool, u256]))
#guard inferTy .nil fs1 [] (call "h" [one, tru]) = some none
-- Argument failure: an unresolved argument fails the call.
#guard inferTy .nil fs1 [] (call "f" [.ident "nope"]) = some none
-- Duplicate entries `f(bool)`: no singleton overload.
#guard inferTy .nil (("f_1", fn "f" [("p", .prim .bool)]) :: fs1) [] (call "f" [tru]) = some none

/-! ## Competing branches -/

-- Builtin `require(true)`; an entry named `require` makes the name a
-- declaration set, so the internal call wins.
#guard inferTy .nil fs1 [] (call "require" [tru]) = some (some (.tuple []))
#guard inferTy .nil (("require_0", fn "require" [("p", .prim .bool)] [("r", .prim .uint)]) :: fs1) []
  (call "require" [tru]) = some (some u256)
-- Conversion `C(a)` to the contract; an entry named `C` excludes it, and
-- its `uint` parameter rejects the address.
#guard inferTy .nil fs1 [("a", .address false)] (call "C" [.ident "a"]) =
  some (some (.contract ⟨none, "C"⟩))
#guard inferTy .nil (("C_0", fn "C" [("p", .prim .uint)]) :: fs1) [("a", .address false)]
  (call "C" [.ident "a"]) = some none
-- Struct construction `S(true)`; an entry named `S` excludes it and is selected.
#guard inferTy structS fs1 [] (call "S" [tru]) = some (some (.struct .memory ⟨some "C", "S"⟩))
#guard inferTy structS (("S_0", fn "S" [("p", .prim .bool)]) :: fs1) [] (call "S" [tru]) =
  some (some (.tuple []))

/-! ## Theorems at the actual fuels -/

theorem boolSlots : Slots [] [("p", Ty.prim .bool)] [.bool] :=
  .cons ⟨.bool, .bool, rfl, rfl, rfl, .bool⟩ .nil
theorem uintSlots : Slots [] [("r", Ty.prim .uint)] [u256] :=
  .cons ⟨.uint, .int false 256 (by decide), rfl, rfl, rfl, .uint _ rfl⟩ .nil

/-- `f(true)` infers to `uint`, the one retained return slot, at `Typed.infer`'s
fuel; the residual argument obligation is `true` at its actual fuel. -/
example {u} (hu : Callee.withFunctions tablesS [] "C" .nil fs1 = some u) :
    ∃ d, Source.Typed.infer (ctx u []) (call "f" [tru]) = some ⟨u256, d⟩ := by
  obtain ⟨_, rs, _, hrs, _, _, _, h⟩ :=
    alias_infer (Γ := ctx u []) (a := "f_0") (index := 0) (σs := [.bool]) (args := args [tru])
      (source := { name := "f", callable := internal }) hu rfl rfl rfl rfl rfl (by decide) rfl
      rfl boolSlots rfl
      (fun j e s hj hne hs hn => by
        rcases j with _ | _ | _ | j
        · exact absurd rfl hne
        all_goals simp [fs1, fn] at hj <;> subst hj <;> simp at hs <;> subst hs <;> simp_all)
      (fun p hp => by cases hp) (by simp [args, argExprs])
      (fun i a σ hi hσ => by
        rcases i with _ | i
        · simp [args, argExprs] at hi hσ; subst hi hσ; exact ⟨_, rfl⟩
        · simp [args, argExprs] at hi)
  cases slots_unique hrs uintSlots
  exact ⟨_, h⟩

/-- Empty argument list: `g()` infers to the empty tuple; no argument obligation. -/
example {u} (hu : Callee.withFunctions tablesS [] "C" .nil fs1 = some u) :
    ∃ d, Source.Typed.infer (ctx u []) (call "g" []) = some ⟨.tuple [], d⟩ := by
  obtain ⟨_, rs, _, hrs, _, _, _, h⟩ :=
    alias_infer (Γ := ctx u []) (a := "g_0") (index := 1) (σs := []) (args := args [])
      (source := { name := "g", callable := internal }) hu rfl rfl rfl rfl rfl (by decide) rfl
      rfl .nil rfl
      (fun j e s hj hne hs hn => by
        rcases j with _ | _ | _ | j
        · simp [fs1, fn] at hj; subst hj; simp at hs; subst hs; simp at hn
        · exact absurd rfl hne
        all_goals simp [fs1, fn] at hj <;> subst hj <;> simp at hs <;> subst hs <;> simp_all)
      (fun p hp => by cases hp) (by simp [args, argExprs]) (fun i a σ hi _ => by simp [args, argExprs] at hi)
  cases hrs
  exact ⟨_, h⟩

/-- Two arguments in order: the list infers position 0 at fuel `n - 1` and
position 1 at fuel `n - 2`, giving `[bool, rational 1]`. -/
example (Γ : Source.Ctx) :
    ∃ da, Source.TypedArgs.inferN 3 Γ (args [tru, one]) =
      some ⟨[.bool, .rational (Source.Q.ofInt 1)], da⟩ :=
  argsN_of_each (by simp [args, argExprs]) (by simp [args, argExprs]) fun i a σ hi hσ => by
    rcases i with _ | _ | i
    · simp [args, argExprs] at hi hσ; subst hi hσ; exact ⟨_, rfl⟩
    · simp [args, argExprs] at hi hσ; subst hi hσ; exact ⟨_, rfl⟩
    · simp [args, argExprs] at hi

/-- Too little fuel for two arguments fails the list. -/
example (Γ : Source.Ctx) : Source.TypedArgs.inferN 2 Γ (args [tru, one]) = none :=
  argsN_short (by simp [args, argExprs])

/-- Duplicate accepting entries: inference of `f(true)` fails. -/
example {u} (hu : Callee.withFunctions tablesS [] "C" .nil
      [("f_0", fn "f" [("p", .prim .bool)]), ("f_1", fn "f" [("p", .prim .bool)])] = some u) :
    Source.Typed.inferN 5 (ctx u []) (call "f" [tru]) = none :=
  ambiguous_inferN (i := 0) (j := 1) (s := { name := "f", callable := internal })
    (s' := { name := "f", callable := internal }) (da := .cons (.bool true) .nil)
    hu rfl rfl (by decide) rfl (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    ⟨[.bool], boolSlots, rfl⟩ ⟨[.bool], boolSlots, rfl⟩ rfl

/-- Local shadowing over any unit: a local `f` leaves no internal call. -/
example (u : Syn .unit) :
    Source.Typed.inferN 5 (ctx u [("f", .bool)]) (call "f" [tru]) = none :=
  local_inferN (da := .cons (.bool true) .nil) (i := 0) rfl rfl

end Solidity.Examples.Lowering.Total.CalleeInference
