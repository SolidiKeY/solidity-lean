import Solidity.Yul.FunctionScope

/-! Exact binder positions combined with no-shadow controls. -/
namespace Solidity.Yul.Checks.Scope

def older : List (String × Fin 2) := [("x", 0), ("y", 1)]

theorem fresh_group : fresh ["x", "y"] ["a", "b"] = true := by decide +kernel

theorem first_new_slot :
    resolve (extendLocals ["a", "b"] older) "a" = some 0 := by decide +kernel

theorem second_new_slot :
    resolve (extendLocals ["a", "b"] older) "b" = some 1 := by decide +kernel

theorem shifted_old_slot :
    resolve (extendLocals ["a", "b"] older) "y" = some 3 := by decide +kernel

theorem shadow_refused : fresh ["x", "y"] ["a", "x"] = false := by decide +kernel

theorem duplicate_group_refused : fresh ["x", "y"] ["a", "a"] = false := by decide +kernel

/-- Why no-shadow checking is required before using the extension operation. -/
theorem unchecked_extension_can_shadow :
    resolve (extendLocals ["y"] older) "y" = some 0 := by decide +kernel

def headers : List (String × Sig) := [("even", ⟨1, 1⟩), ("odd", ⟨1, 1⟩)]

def olderFunctions : FunctionNames [⟨0, 0⟩] := [("stopper", ⟨⟨0, 0⟩, .here⟩)]

theorem later_function_visible :
    resolve (hoistNames headers olderFunctions) "odd" = some ⟨⟨1, 1⟩, .there .here⟩ := rfl

theorem older_function_shifted :
    resolve (hoistNames headers olderFunctions) "stopper" = some ⟨⟨0, 0⟩, .there (.there .here)⟩ := rfl

theorem distinct_arity_does_not_allow_duplicate_name :
    fresh [] ([ ("f", (⟨0, 0⟩ : Sig)), ("f", ⟨1, 1⟩) ].map Prod.fst) = false := by
  decide +kernel

end Solidity.Yul.Checks.Scope
