import Solidity.Yul.GlobalExternal
import Solidity.Yul.Checks.External

/-! Function-boundary resolution controls: preserve declaration occurrence and
resolve original lexical visibility before testing capture eligibility. -/
namespace Solidity.Yul.Checks.GlobalExternal
open Solidity.Yul.Checks.External

theorem state_slot_reindexed :
    (checkGlobalExternal decls "g" ["slot"] false).map (fun r => r.1) =
      some ⟨.here, .slot, .slotRead⟩ := rfl

theorem constant_reindexed :
    (checkGlobalExternal decls "c" [] false).map (fun r => r.1) =
      some ⟨.there .here, .plain, .constantRead⟩ := rfl

theorem source_value_capture_refused :
    (checkGlobalExternal decls "x" [] false).isSome = false := by decide +kernel

theorem storage_pointer_capture_refused :
    (checkGlobalExternal decls "s" ["slot"] false).isSome = false := by decide +kernel

theorem calldata_capture_refused :
    (checkGlobalExternal decls "a" ["length"] false).isSome = false := by decide +kernel

theorem external_function_capture_refused :
    (checkGlobalExternal decls "f" ["selector"] false).isSome = false := by decide +kernel

abbrev PlainShadow : List ExternalType := [.value (.unsigned 0), .constant (word 7)]

def plainShadowed : ExternalNames PlainShadow := [
  ("x", ⟨_, .here⟩), ("x", ⟨_, .there .here⟩)]

def plainGlobal : ExternalNames PlainShadow := [("x", ⟨_, .there .here⟩)]

/-- The older constant really would be readable if it were the visible binding. -/
theorem older_plain_binding_is_legal :
    (checkGlobalExternal plainGlobal "x" [] false).isSome = true := by decide +kernel

/-- The local is found first and rejected for capture; no global retry. -/
theorem shadowing_plain_does_not_expose_global :
    (checkGlobalExternal plainShadowed "x" [] false).isSome = false := by decide +kernel

/-- The local's illegal suffix is not a reason to retry the older global. -/
theorem shadowing_slot_does_not_expose_global :
    (checkGlobalExternal shadowed "x" ["slot"] false).isSome = false := by decide +kernel

abbrev Repeated : List ExternalType := [.storage false false, .value (.signed 0), .storage false false]

def repeated : ExternalNames Repeated := [
  ("first", ⟨_, .here⟩), ("second", ⟨_, .there (.there .here)⟩)]

/-- Equal descriptor types do not collapse two distinct declaration positions. -/
theorem second_occurrence_preserved :
    (checkGlobalExternal repeated "second" ["slot"] false).map (fun r => r.1) =
      some ⟨.there .here, .slot, .slotRead⟩ := rfl

theorem global_attribute_write_refused :
    (checkGlobalExternal decls "g" ["slot"] true).isSome = false := by decide +kernel

end Solidity.Yul.Checks.GlobalExternal
