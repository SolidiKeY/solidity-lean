import Solidity.Yul.ExternalCheck

/-! Static external-reference controls. No physical execution or whole-block
provenance/capture guarantee follows from a supplied declaration table. -/
namespace Solidity.Yul.Checks.External

abbrev X : List ExternalType := [.value (.unsigned 0), .storage false false,
  .storage true false, .calldataDynamic, .externalFunction, .constant (word 7)]

def decls : ExternalNames X := [
  ("x", ⟨_, .here⟩),
  ("g", ⟨_, .there .here⟩),
  ("s", ⟨_, .there (.there .here)⟩),
  ("a", ⟨_, .there (.there (.there .here))⟩),
  ("f", ⟨_, .there (.there (.there (.there .here)))⟩),
  ("c", ⟨_, .there (.there (.there (.there (.there .here))))⟩)
]

theorem value_plain : (checkExternal decls "x" [] false).isSome = true := by decide +kernel

theorem value_slot_refused : (checkExternal decls "x" ["slot"] false).isSome = false := by decide +kernel

theorem global_slot_read :
    (checkExternal decls "g" ["slot"] false).map (fun r => r.1) =
      some ⟨.there .here, .slot, .slotRead⟩ := rfl

theorem global_slot_write_refused : (checkExternal decls "g" ["slot"] true).isSome = false := by decide +kernel

theorem local_slot_write :
    (checkExternal decls "s" ["slot"] true).map (fun r => r.1.attr) = some .slot := by decide +kernel

theorem local_offset_write_refused : (checkExternal decls "s" ["offset"] true).isSome = false := by decide +kernel

theorem dynamic_offset_write : (checkExternal decls "a" ["offset"] true).isSome = true := by decide +kernel

theorem dynamic_length_write : (checkExternal decls "a" ["length"] true).isSome = true := by decide +kernel

theorem dynamic_plain_refused : (checkExternal decls "a" [] false).isSome = false := by decide +kernel

theorem external_selector_write :
    (checkExternal decls "f" ["selector"] true).map (fun r => r.1.attr) = some .selector := by decide +kernel

theorem external_address_read :
    (checkExternal decls "f" ["address"] false).map (fun r => r.1.attr) = some .address := by decide +kernel

theorem constant_write_refused : (checkExternal decls "c" [] true).isSome = false := by decide +kernel

theorem unknown_name_refused : (checkExternal decls "unknown" [] false).isSome = false := by decide +kernel

theorem unknown_suffix_refused : (checkExternal decls "x" ["balance"] false).isSome = false := by decide +kernel

theorem multiple_suffixes_refused : (checkExternal decls "f" ["address", "selector"] false).isSome = false := by decide +kernel

def shadowed : ExternalNames X := ("x", ⟨_, .here⟩) :: ("x", ⟨_, .there .here⟩) :: []

/-- Attribute failure at the visible binding never falls back to a shadowed one. -/
theorem no_attribute_fallback : (checkExternal shadowed "x" ["slot"] false).isSome = false := by decide +kernel

def internal : ExternalNames [.internalFunction] := [("p", ⟨_, .here⟩)]

theorem internal_pointer_statically_represented : (checkExternal internal "p" [] false).isSome = true := by decide +kernel

theorem internal_selector_refused : (checkExternal internal "p" ["selector"] false).isSome = false := by decide +kernel

theorem internal_pointer_not_admitted :
    admitExternal .A .internalFunction = .error (.compilerDependent "internal function address") := rfl

end Solidity.Yul.Checks.External
