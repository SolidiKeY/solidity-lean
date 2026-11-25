import Solidity.Correctness.Lowering.Total.StructUnitInference
import Solidity.Examples.Lowering.Total.StructUnit

/-! Callee lookup, selection and call inference in assembled mixed units: structs
`Pair` and `Tag`, roots `n` and `Pair p`, the explicit and the implicit constructor,
then eight function entries kept in order: a unique callable overload `f(bool)` beside
`f(uint)` and an external `f(bool)`, a function `Pair` colliding with the struct, a
function `n` colliding with the root, ambiguous `g(bool)` twice, and a repeated alias
`f_0`. Local shadowing; execution is not checked. -/
namespace Solidity.Examples.Lowering.Total.StructUnitInference

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.Decode
open Solidity.Correctness.Lowering.Total.Decode.Callee
open Solidity.Correctness.Lowering.Total.CalleeSelection
open Solidity.Correctness.Lowering.Total.CalleeInference (argExprs NotOther local_inferN)
open Solidity.Correctness.Lowering.Total.CalleeAliases (firstIndex)
open Solidity.Correctness.Lowering.Total.StructUnitInference
open Solidity.Examples.Lowering.Total.StructUnit (full implicit)
open Solidity.Source (STy Syn)

/-- `function NAME(params) ROLE returns (rets) {}` with retained source identity. -/
def fn (name : String) (callable : SourceCallable) (params : List (Name × Ty))
    (rets : List (Name × Ty) := []) : FunDecl :=
  { sourceDecl := some { name, callable }, params, rets, body := [] }
def internal : SourceCallable := .local .internalFn
def external : SourceCallable := .abi .externalFn .selected none
def pb : List (Name × Ty) := [("p", .prim .bool)]
def ru : List (Name × Ty) := [("r", .prim .uint)]

/-- `f(bool) returns (uint)`, `f(uint)`, external `f(bool)`, `Pair(bool)`,
`n(bool) returns (uint)`, `g(bool)` twice, and `h()` under the repeated alias `f_0`. -/
def fsM : List (Name × FunDecl) :=
  [("f_0", fn "f" internal pb ru), ("f_1", fn "f" internal [("p", .prim .uint)]),
   ("f_2", fn "f" external pb), ("Pair_0", fn "Pair" internal pb),
   ("n_0", fn "n" internal pb ru), ("g_0", fn "g" internal pb), ("g_1", fn "g" internal pb),
   ("f_0", fn "h" internal [])]

/-- The context of the generated contract `C` over the unit. -/
def ctx (u : Syn .unit) (locals : List (String × STy)) : Source.Ctx :=
  { env := u.env, scope := some "C", locals }
def args : List (Syn .expr) → Syn (.list .expr)
  | [] => .nil
  | e :: es => .cons e (args es)
/-- `x(es…)`. -/
def call (x : String) (es : List (Syn .expr)) : Syn .expr := .call (.ident x) (.positional (args es))
def tru : Syn .expr := .lit (.bool true)
def u256 : STy := .int Source.IntTy.u256

def unitOf (C : Contract) : Option (Syn .unit) := (StructUnit.build tablesS [] C "C" fsM).toOption
def table (C : Contract) :=
  (unitOf C).map fun u => u.decls.map fun d => (d.kind, d.name)
/-- The type `Typed.infer` gives `e` in the built unit, if it builds. -/
def inferTy (C : Contract) (locals : List (String × STy)) (e : Syn .expr) : Option (Option STy) :=
  (unitOf C).map fun u => (Source.Typed.infer (ctx u locals) e).map (·.1)
/-- The number of callable functions of `x` in the built unit. -/
def callables (C : Contract) (x : String) : Option Nat :=
  (unitOf C).map fun u => ((ctx u []).functions x).length

/-! ## The mixed units, evaluated -/

-- Every declaration kept, in order: structs, constructor, roots, all eight functions.
#guard table full == some [(.contract, "C"), (.struct, "Pair"), (.struct, "Tag"),
  (.constructor, ""), (.stateVar, "n"), (.stateVar, "p"), (.function, "f"), (.function, "f"),
  (.function, "f"), (.function, "Pair"), (.function, "n"), (.function, "g"), (.function, "g"),
  (.function, "h")]
#guard table implicit == (table full).map (·.erase (.constructor, ""))
-- Callable functions: the two internal `f`, not the external one; the colliding struct
-- and root are candidates but not functions.
#guard [full, implicit].all fun C =>
  [callables C "f", callables C "Pair", callables C "n", callables C "g", callables C "Tag"] ==
    [some 2, some 1, some 1, some 2, some 0]
-- Unique overload `f(true)`; the function `Pair` and `n` win over the struct and the root.
#guard [full, implicit].all fun C =>
  [inferTy C [] (call "f" [tru]), inferTy C [] (call "Pair" [tru]), inferTy C [] (call "n" [tru]),
    inferTy C [] (call "h" [])] == [some (some u256), some (some (.tuple [])), some (some u256),
    some (some (.tuple []))]
-- Ambiguous `g(true)`, local shadowing of `f`, and `Tag(…)` still the struct branch.
#guard [full, implicit].all fun C =>
  [inferTy C [] (call "g" [tru]), inferTy C [("f", .bool)] (call "f" [tru])] == [some none, some none]
#guard (inferTy full [] (call "Tag" [.ident "msg"])).isSome

/-! ## The exported facts on the built unit -/

theorem boolSlots : Slots [] pb [.bool] := .cons ⟨.bool, .bool, rfl, rfl, rfl, .bool⟩ .nil
theorem uintSlots : Slots [] ru [u256] :=
  .cons ⟨.uint, .int false 256 (by decide), rfl, rfl, rfl, .uint _ rfl⟩ .nil

theorem uint_rejects {isBase mapFree} :
    ¬ Accepts isBase mapFree [.bool] (fn "f" internal [("p", .prim .uint)]) := by
  rintro ⟨ps, hps, hfit⟩
  cases slots_unique hps
    (.cons ⟨.uint, .int false 256 (by decide), rfl, rfl, rfl, .uint _ rfl⟩ .nil)
  exact Bool.false_ne_true hfit

/-- The leading prefix rejects every call: derived, not assumed. -/
example {u} (h : StructUnit.build tablesS [] full "C" fsM = .ok u) (Γ : Source.Ctx) :=
  build_prefixRejects (Γ := Γ) (σs := [.bool]) (x := "Pair") h

/-- Lookup of `n`: the root `n` and the function `n`, the root no function. -/
example {u} (h : StructUnit.build tablesS [] full "C" fsM = .ok u) := build_lookup (x := "n") h

/-- The callable functions of `f` are exactly its callable entries. -/
example {u} (h : StructUnit.build tablesS [] implicit "C" fsM = .ok u) :
    (ctx u []).functions "f" = callableEntries tablesS [] "C" fsM "f" :=
  build_functions h rfl rfl (by decide) rfl

/-- The external `f(bool)` is never callable. -/
example {u : Syn .unit} {o} (hm : fromMetadata tablesS [] "C" (fn "f" external pb) = some o) :
    o ∉ (ctx u []).functions "f" :=
  entry_unreachable hm (callable_external rfl rfl) rfl

/-- First-alias lookup: `f_0` selects position 0, not the later `h()` under `f_0`. -/
example {u} (h : StructUnit.build tablesS [] full "C" fsM = .ok u) :
    ∃ out, firstIndex "f_0" fsM = some 0 ∧ fromMetadata tablesS [] "C" (fn "f" internal pb ru) = some out ∧
      out ∈ u.env.lookup (some "C") "f" ∧ out ∈ (ctx u []).functions "f" := by
  obtain ⟨index, out, source, hf, -, hm, hs, -, -, hk⟩ :=
    build_alias_lookup (Γ := ctx u []) (a := "f_0") (fd := fn "f" internal pb ru) h rfl rfl rfl
  cases hf.symm.trans (rfl : firstIndex "f_0" fsM = some 0)
  cases hs
  obtain ⟨hl, hc⟩ := hk (by decide)
  exact ⟨out, rfl, hm, hl, hc rfl rfl⟩

/-- A name no entry retains (here the struct `Tag`) has no callable function. -/
example {u} (h : StructUnit.build tablesS [] full "C" fsM = .ok u) :
    (ctx u []).functions "Tag" = [] := by
  rw [build_functions h rfl rfl (by decide) rfl]; rfl

/-- An empty function list: no callable function under any nonempty name. -/
example {u} {x : String} (h : StructUnit.build tablesS [] implicit "C" [] = .ok u) (hx : x ≠ "")
    (hloc : ([] : List String).idxOf? x = none) : (ctx u []).functions x = [] :=
  build_functions h rfl rfl hx hloc

/-- **Unique overload**: `f(true)` infers to `uint` at `Typed.infer`'s fuel; `f(uint)`
rejects the argument and the external `f(bool)` is not callable. -/
example {u} (h : StructUnit.build tablesS [] full "C" fsM = .ok u) :
    ∃ d, Source.Typed.infer (ctx u []) (call "f" [tru]) = some ⟨u256, d⟩ := by
  obtain ⟨_, rs, _, hrs, _, _, _, hinf⟩ :=
    build_alias_infer (Γ := ctx u []) (a := "f_0") (index := 0) (σs := [.bool])
      (args := args [tru]) (source := { name := "f", callable := internal })
      h rfl rfl rfl rfl rfl (by decide) rfl rfl boolSlots rfl
      (fun j e s hj hne hs hn => by
        rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
        · exact absurd rfl hne
        · cases hj; exact .inr uint_rejects
        · cases hj; exact .inl (callable_external rfl rfl)
        all_goals simp [fsM, fn] at hj <;> subst hj <;> simp at hs <;> subst hs <;> simp_all)
      (by simp [args, argExprs])
      (fun i a σ hi hσ => by
        rcases i with _ | i
        · simp [args, argExprs] at hi hσ; subst hi hσ; exact ⟨_, rfl⟩
        · simp [args, argExprs] at hi)
  cases slots_unique hrs uintSlots
  exact ⟨_, hinf⟩

/-- **Colliding struct name**: the function `Pair` excludes the struct branch, so
`Pair(true)` dispatches to `inferCall`. -/
example {u} (h : StructUnit.build tablesS [] full "C" fsM = .ok u) :
    NotOther (ctx u []) "Pair" ∧
      Source.Typed.inferN 5 (ctx u []) (call "Pair" [tru]) =
        Source.inferCall (ctx u []) "Pair" (args [tru]) [.bool] (.cons (.bool true) .nil) :=
  ⟨build_entry_notOther (Γ := ctx u []) (index := 3)
    (source := { name := "Pair", callable := internal }) h rfl rfl rfl rfl (by decide) rfl,
   build_entry_dispatch (index := 3) (source := { name := "Pair", callable := internal })
    h rfl rfl rfl rfl (by decide) rfl rfl⟩

/-- **Colliding root name**: `n(true)` selects the function `n` alone. -/
example {u} (h : StructUnit.build tablesS [] implicit "C" fsM = .ok u) :
    ∃ out rs, ((ctx u []).functions "n").filter (fits (ctx u []) [.bool]) = [out] ∧
      out.fnSig u.env = some ([.bool], rs) := by
  obtain ⟨out, rs, -, -, hsel, hsig⟩ :=
    build_entry_selected (Γ := ctx u []) (index := 4) (σs := [.bool])
      (source := { name := "n", callable := internal }) h rfl rfl rfl rfl (by decide) rfl rfl
      boolSlots rfl
      (fun j e s hj hne hs hn => by
        rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
        · cases hj; cases hs; exact absurd hn (by decide)
        · cases hj; cases hs; exact absurd hn (by decide)
        · cases hj; cases hs; exact absurd hn (by decide)
        · cases hj; cases hs; exact absurd hn (by decide)
        · exact absurd rfl hne
        all_goals simp [fsM, fn] at hj <;> subst hj <;> simp at hs <;> subst hs <;> simp_all)
  exact ⟨out, rs, hsel, hsig⟩

/-- **Ambiguous overloads**: `g(true)` with two accepting `g(bool)` fails. -/
example {u} (h : StructUnit.build tablesS [] full "C" fsM = .ok u) :
    Source.Typed.inferN 5 (ctx u []) (call "g" [tru]) = none :=
  build_ambiguous_inferN (i := 5) (j := 6) (s := { name := "g", callable := internal })
    (s' := { name := "g", callable := internal }) (da := .cons (.bool true) .nil)
    h rfl rfl (by decide) rfl (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    ⟨[.bool], boolSlots, rfl⟩ ⟨[.bool], boolSlots, rfl⟩ rfl

/-- **Local shadowing**: a local `f` leaves no callable `f` and no internal call. -/
example {u} (_ : StructUnit.build tablesS [] full "C" fsM = .ok u) :
    (ctx u [("f", .bool)]).functions "f" = [] ∧
      Source.Typed.inferN 5 (ctx u [("f", .bool)]) (call "f" [tru]) = none :=
  ⟨functions_local (i := 0) rfl, local_inferN (da := .cons (.bool true) .nil) (i := 0) rfl rfl⟩


end Solidity.Examples.Lowering.Total.StructUnitInference
