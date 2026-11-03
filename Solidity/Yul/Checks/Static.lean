import Solidity.Yul.Static

set_option Elab.async false

/-! Inhabited syntax and boundary refusals. These are kernel controls for the
foundation, not end-to-end import or execution claims. -/
namespace Solidity.Yul.Checks.Static

/-- A whole-block function reference used in the statement before its definition:
`function mulDiv(a,b,d) -> q { q := div(mul(a,b),d) }`. -/
def mulDivBody : Stmt [⟨3, 1⟩] [] ⟨true, false⟩ 4 :=
  .assign (fun _ => .«local» 3)
    (.builtin (.pure .«div») (fun i => if i.val = 0 then
      .builtin (.pure .«mul») (fun j => if j.val = 0 then .«local» 0 else .«local» 1)
      else .«local» 2))

def mulDiv : Stmt [] [] ⟨false, false⟩ 1 :=
  .functions [⟨3, 1⟩] (.cons mulDivBody .nil)
    (.assign (fun _ => .«local» 0)
      (.call .here (fun i => .literal (word (if i.val = 0 then 21 else if i.val = 1 then 10 else 3)))))

/-- A loop with both continue and break, at intrinsically legal positions. -/
def loop : Stmt [] [] ⟨false, false⟩ 1 :=
  .for_ .skip (.literal (word 1))
    (.assign (fun _ => .«local» 0)
      (.builtin (.pure .«add») (fun i => if i.val = 0 then .«local» 0 else .literal (word 1))))
    (.seq (.if_ (.«local» 0) .break_) .continue_)

/-- A global state variable's slot remains available inside a Yul function. -/
def globalSlot : Stmt [] [.storage false false] ⟨false, false⟩ 0 :=
  .functions [⟨0, 1⟩]
    (.cons (.assign (fun _ => .«local» 0)
      (.external ⟨.here, .slot, .slotRead⟩)) .nil)
    .skip

theorem no_value_capture : globals [.value (.unsigned 0)] = [] := rfl
theorem no_memory_capture : globals [.memory] = [] := rfl
theorem keep_globals : globals [.memory, .storage false false, .constant (word 9), .library] =
    [.storage false false, .constant (word 9), .library] := rfl

theorem unknown_name : resolve [("x", 3)] "y" = (none : Option Nat) := by decide +kernel
theorem no_shadow : fresh ["x", "f"] ["x"] = false := by decide +kernel
theorem no_duplicate_declarations : fresh [] ["x", "x"] = false := by decide +kernel
theorem fresh_names : fresh ["outer"] ["x", "f"] = true := by decide +kernel
theorem function_global_slot : (checkAccess (.storage false false) .slot false).isSome = true := rfl
theorem state_slot_readonly : (checkAccess (.storage false false) .slot true).isSome = false := rfl
theorem pointer_slot_writable : (checkAccess (.storage true false) .slot true).isSome = true := rfl
theorem storage_offset_readonly : (checkAccess (.storage true false) .offset true).isSome = false := rfl
theorem storage_plain_refused : (checkAccess (.storage true false) .plain false).isSome = false := rfl
theorem calldata_length_writable : (checkAccess .calldataDynamic .length true).isSome = true := rfl
theorem calldata_static_plain : (checkAccess .calldataStatic .plain true).isSome = true := rfl
theorem calldata_static_length_refused : (checkAccess .calldataStatic .length false).isSome = false := rfl
theorem function_selector_writable : (checkAccess .externalFunction .selector true).isSome = true := rfl
theorem internal_selector_refused : (checkAccess .internalFunction .selector false).isSome = false := rfl
theorem compiler_dependent_pointer : admitExternal .C .internalFunction =
    .error (.compilerDependent "internal function address") := rfl
theorem external_function_tier_A : admitExternal .A .externalFunction = .ok () := rfl

theorem value_slot_refused : (checkAccess (.value .boolean) .slot false).isSome = false := rfl
theorem constant_readonly : (checkAccess (.constant (word 3)) .plain true).isSome = false := rfl
theorem too_large_literal : checkLiteral (2 ^ 256) = none := by decide +kernel
theorem max_literal : (checkLiteral (2 ^ 256 - 1)).isSome = true := by decide +kernel

theorem no_duplicate_builtin_names : (builtins.map (fun e => e.2.2.name)).Nodup := by decide +kernel
theorem pure_at_A : Builtin.admit .A (.pure .«mulmod») = .ok () := rfl
theorem physical_needs_B : Builtin.admit .A .mload = .error (.needsTier .B) := rfl
theorem effects_need_C : Builtin.admit .B .call = .error (.needsTier .C) := rfl
theorem gas_refused : Builtin.admit .C .gas = .error (.compilerDependent "gas") := rfl
theorem msize_refused : Builtin.admit .C .msize = .error (.compilerDependent "msize") := rfl
theorem pc_refused : Builtin.admit .C .pc = .error (.compilerDependent "pc") := rfl
theorem codesize_refused : Builtin.admit .C .codesize = .error (.compilerDependent "codesize") := rfl
theorem codecopy_refused : Builtin.admit .C .codecopy = .error (.compilerDependent "codecopy") := rfl
theorem callcode_refused : Builtin.admit .C .callcode = .error .unsupportedCallcode := rfl
theorem unsafe_refused : admitSafety false = .error .nonMemorySafe := rfl

end Solidity.Yul.Checks.Static
