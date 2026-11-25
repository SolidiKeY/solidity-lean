import Solidity.Correctness.Lowering.Total.CalleeSelection

/-! Typed callee selection over assembled units: a uniquely compatible
overload among same-name declarations, ambiguous compatible overloads, an
external-only candidate, local shadowing and a matching prefix competitor.
Execution is not checked. -/
namespace Solidity.Examples.Lowering.Total.CalleeSelection

open Solidity.Correctness.Lowering.Total Solidity.Correctness.Lowering.Total.Decode
open Solidity.Correctness.Lowering.Total.Decode.Callee
open Solidity.Correctness.Lowering.Total.CalleeSelection
open Solidity.Source (STy)

/-- `function NAME(T p) ROLE {}` with retained source identity. -/
def fn (name : String) (callable : SourceCallable) (t : PrimTy) : FunDecl :=
  { sourceDecl := some { name, callable }, params := [("p", .prim t)], body := [] }

def internal : SourceCallable := .local .internalFn
def external : SourceCallable := .abi .externalFn .selected none
/-- `f(uint)` and `f(bool)`: one name, distinct parameter types. -/
def overload : List (Name × FunDecl) :=
  [("f_0", fn "f" internal .uint), ("f_1", fn "f" internal .bool)]
/-- Two positions retaining `f(bool)` with equal declarations. -/
def twice : List (Name × FunDecl) :=
  [("f_0", fn "f" internal .bool), ("f_1", fn "f" internal .bool)]
/-- An external-only `f(bool)` beside an internal `f(bool)`. -/
def withExternal : List (Name × FunDecl) :=
  [("f_0", fn "f" external .bool), ("f_1", fn "f" (.local .privateFn) .bool)]
def single : List (Name × FunDecl) := [("f_0", fn "f" internal .bool)]
/-- Prefix `function f(bool p) internal {}`: a matching competitor. -/
def prefixF : Source.Syn (.list (.part false)) :=
  .cons (.function (.ident "f") (.cons (.param (.elem .bool) none (some "p")) .nil)
    (some .internal) none .nil false none .nil (.some (.block .nil))) .nil
/-- Prefix `error f();`: named `f`, not a function. -/
def errorF : Source.Syn (.list (.part false)) := .cons (.error "f" .nil) .nil
/-- The context of the generated contract `C` over the assembled unit. -/
def ctx (u : Source.Syn .unit) (locals : List (String × STy)) : Source.Ctx :=
  { env := u.env, scope := some "C", locals }
def trueArg : Source.Syn (.list .expr) := .cons (.lit (.bool true)) .nil
def trueTyped (Γ : Source.Ctx) : Source.TypedArgs Γ trueArg [.bool] := .cons (.bool true) .nil

/-- Size of the actual overload filter for `f(true)`, and whether `inferCall` succeeds. -/
def selectOf (pre : Source.Syn (.list (.part false))) (fs : List (Name × FunDecl))
    (locals : List (String × STy)) : Option (Nat × Bool) :=
  (Callee.withFunctions tablesS [] "C" pre fs).map fun u =>
    (((ctx u locals).functions "f").filter (fits (ctx u locals) [.bool]) |>.length,
      (Source.inferCall (ctx u locals) "f" trueArg [.bool] (trueTyped _)).isSome)

#guard selectOf .nil overload [] == some (1, true)
#guard selectOf .nil twice [] == some (2, false)
#guard selectOf .nil withExternal [] == some (1, true)
#guard selectOf .nil [("f_0", fn "f" external .bool)] [] == some (0, false)
#guard selectOf .nil single [("f", .bool)] == some (0, false)
#guard selectOf prefixF single [] == some (2, false)
#guard selectOf errorF single [] == some (1, true)

theorem boolSlots : Slots [] [("p", Ty.prim .bool)] [.bool] :=
  .cons ⟨.bool, .bool, rfl, rfl, rfl, .bool⟩ .nil

theorem uint_rejects {isBase mapFree} : ¬ Accepts isBase mapFree [.bool] (fn "f" internal .uint) := by
  rintro ⟨ps, hps, hfit⟩
  cases slots_unique hps (.cons ⟨.uint, .int false 256 (by decide), rfl, rfl, rfl, .uint _ rfl⟩ .nil)
  exact Bool.false_ne_true hfit

/-- Every callable entry declaration of `f` carries that name. -/
example {o} (h : o ∈ callableEntries tablesS [] "C" overload "f") : o.name = "f" :=
  (callableEntries_entry h).elim fun _ h => h.2.2.1

/-- Unique overload: alias `f_1` selects `f(bool)`; `f(uint)` rejects a `bool`. -/
example {u} (hu : Callee.withFunctions tablesS [] "C" .nil overload = some u) :
    ∃ out rs hsel hsig, Slots [] [] rs ∧
      Source.inferCall (ctx u []) "f" trueArg [.bool] (trueTyped _) =
        some ⟨STy.ret rs, typedCall (d := out) (ps := [.bool]) (trueTyped _) hsel hsig⟩ := by
  obtain ⟨out, rs, _, hrs, hsel, hsig, hinf⟩ :=
    alias_inferCall (Γ := ctx u []) (a := "f_1") (index := 1) (σs := [.bool])
      (fd := fn "f" internal .bool) (source := { name := "f", callable := internal })
      hu rfl rfl rfl rfl rfl (by decide) rfl rfl boolSlots rfl
      (fun j e s hj hne _ _ => by
        rcases j with _ | _ | j
        · cases hj; exact .inr uint_rejects
        · exact absurd rfl hne
        · cases hj)
      (fun p hp => by cases hp) (trueTyped _)
  exact ⟨out, rs, hsel, hsig, hrs, hinf⟩

/-- Ambiguity: two accepting positions with equal declarations; inference fails. -/
example {u} (hu : Callee.withFunctions tablesS [] "C" .nil twice = some u) :
    Source.inferCall (ctx u []) "f" trueArg [.bool] (trueTyped _) = none :=
  inferCall_none _ <| entries_ambiguous (i := 0) (j := 1)
    (e := ("f_0", fn "f" internal .bool)) (e' := ("f_1", fn "f" internal .bool))
    (s := { name := "f", callable := internal }) (s' := { name := "f", callable := internal })
    hu rfl rfl (by decide) rfl (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    ⟨[.bool], boolSlots, rfl⟩
    ⟨[.bool], boolSlots, rfl⟩

/-- External-only `f` is never callable; the private `f(bool)` at position 1 is selected. -/
example {u} (hu : Callee.withFunctions tablesS [] "C" .nil withExternal = some u) :
    (∀ o, fromMetadata tablesS [] "C" (fn "f" external .bool) = some o →
        o ∉ (ctx u []).functions "f") ∧
      ∃ out, fromMetadata tablesS [] "C" (fn "f" (.local .privateFn) .bool) = some out ∧
        (((ctx u []).functions "f").filter (fits (ctx u []) [.bool])) = [out] := by
  obtain ⟨out, _, hm, _, hsel, _⟩ :=
    entry_selected (Γ := ctx u []) (index := 1) (σs := [.bool])
      (e := ("f_1", fn "f" (.local .privateFn) .bool))
      (source := { name := "f", callable := .local .privateFn }) hu rfl rfl rfl rfl (by decide)
      rfl (callable_local rfl rfl (by decide)) boolSlots rfl
      (fun j e s hj hne _ _ => by
        rcases j with _ | _ | j
        · cases hj; exact .inl (callable_external rfl rfl)
        · exact absurd rfl hne
        · cases hj)
      (fun p hp => by cases hp)
  exact ⟨fun o ho => entry_unreachable ho (callable_external rfl rfl) rfl, out, hm, hsel⟩

/-- Local shadowing over any unit (assembled included): no callable `f`; inference fails. -/
example (u : Source.Syn .unit) :
    Source.inferCall (ctx u [("f", .bool)]) "f" trueArg [.bool] (trueTyped _) = none :=
  inferCall_none _ fun o h => by
    rw [functions_local (i := 0) rfl] at h; cases h

/-- Matching prefix competitor: the prefix `f(bool)` is callable and accepts
in any context, so the prefix obligation fails (the `#guard` above shows the
resulting two-candidate filter on the assembled unit). -/
example (Γ : Source.Ctx) : ¬ PrefixRejects Γ [.bool] "C" prefixF "f" := fun h => by
  rcases h ⟨.function, "f", some "C", false, .function (.ident "f")
      (.cons (.param (.elem .bool) none (some "p")) .nil) (some .internal) none .nil false none
      .nil (.some (.block .nil))⟩ (by simp [CalleeResolution.prefixNamed, prefixF,
        Source.Syn.collect, Source.FnName.text]) with hk | hk | hk
  · exact hk rfl
  · cases hk
  · cases hk

end Solidity.Examples.Lowering.Total.CalleeSelection
