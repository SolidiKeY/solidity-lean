module

import all Init.Data.String.Basic
import Init.Data.String.Lemmas

public section

/-! Isolated case controls for the external Raw String-API blocker. These use
only official standard strings. KeySort is checked as a separate prerequisite. They neither
replace Raw's parser nor prove its general correctness. Check each unchanged
statement independently on the two official toolchains. No raised budget. -/
namespace H62.MigrateSolkey.StringApiControls

theorem hashKeccakDrop : (toString ("#keccak256".drop 1)) = "keccak256" := by
  first
  | decide +kernel
  | apply String.toList_injective
    rw [String.Slice.toStringToString_eq]
    change ("#keccak256".drop 1).copy.toList = "keccak256".toList
    rw [String.toList_copy_drop]
    decide +kernel

theorem hashShaDrop : (toString ("#sha256".drop 1)) = "sha256" := by
  first
  | decide +kernel
  | apply String.toList_injective
    rw [String.Slice.toStringToString_eq]
    change ("#sha256".drop 1).copy.toList = "sha256".toList
    rw [String.toList_copy_drop]
    decide +kernel

theorem unicodeDrop : (toString ("κλx".drop 1)) = "λx" := by
  first
  | decide +kernel
  | apply String.toList_injective
    rw [String.Slice.toStringToString_eq]
    change ("κλx".drop 1).copy.toList = "λx".toList
    rw [String.toList_copy_drop]
    decide +kernel

theorem functionPrefixDrop :
    (toString ("function(uint256,address)".drop 9)).toList = "uint256,address)".toList := by
  first
  | decide +kernel
  | rw [String.Slice.toStringToString_eq]
    change ("function(uint256,address)".drop 9).copy.toList = "uint256,address)".toList
    rw [String.toList_copy_drop]
    decide +kernel

theorem returnsPrefixAndSuffix :
    (toString ("returns(uint256)".drop 8)).toList.dropLast = "uint256".toList := by
  first
  | decide +kernel
  | rw [String.Slice.toStringToString_eq]
    change ("returns(uint256)".drop 8).copy.toList.dropLast = "uint256".toList
    rw [String.toList_copy_drop]
    decide +kernel

theorem locationSuffixEta :
    ["[]memory", "[]storage"].find? (fun suffix : String => "uint256[]memory".endsWith suffix)
      = some "[]memory" := by
  first
  | decide +kernel
  | have h : "uint256[]memory".endsWith "[]memory" = true := by
      unfold String.endsWith Substring.hasBeq Substring.beq String.substrEq
      change String.substrEq.loop "uint256[]memory" "[]memory" ⟨7⟩ ⟨0⟩ ⟨15⟩ = true
      have step0 : String.substrEq.loop "uint256[]memory" "[]memory" ⟨7⟩ ⟨0⟩ ⟨15⟩ = String.substrEq.loop "uint256[]memory" "[]memory" ⟨8⟩ ⟨1⟩ ⟨15⟩ := by
        conv => lhs; rw [String.substrEq.loop]
        rfl
      have step1 : String.substrEq.loop "uint256[]memory" "[]memory" ⟨8⟩ ⟨1⟩ ⟨15⟩ = String.substrEq.loop "uint256[]memory" "[]memory" ⟨9⟩ ⟨2⟩ ⟨15⟩ := by
        conv => lhs; rw [String.substrEq.loop]
        rfl
      have step2 : String.substrEq.loop "uint256[]memory" "[]memory" ⟨9⟩ ⟨2⟩ ⟨15⟩ = String.substrEq.loop "uint256[]memory" "[]memory" ⟨10⟩ ⟨3⟩ ⟨15⟩ := by
        conv => lhs; rw [String.substrEq.loop]
        rfl
      have step3 : String.substrEq.loop "uint256[]memory" "[]memory" ⟨10⟩ ⟨3⟩ ⟨15⟩ = String.substrEq.loop "uint256[]memory" "[]memory" ⟨11⟩ ⟨4⟩ ⟨15⟩ := by
        conv => lhs; rw [String.substrEq.loop]
        rfl
      have step4 : String.substrEq.loop "uint256[]memory" "[]memory" ⟨11⟩ ⟨4⟩ ⟨15⟩ = String.substrEq.loop "uint256[]memory" "[]memory" ⟨12⟩ ⟨5⟩ ⟨15⟩ := by
        conv => lhs; rw [String.substrEq.loop]
        rfl
      have step5 : String.substrEq.loop "uint256[]memory" "[]memory" ⟨12⟩ ⟨5⟩ ⟨15⟩ = String.substrEq.loop "uint256[]memory" "[]memory" ⟨13⟩ ⟨6⟩ ⟨15⟩ := by
        conv => lhs; rw [String.substrEq.loop]
        rfl
      have step6 : String.substrEq.loop "uint256[]memory" "[]memory" ⟨13⟩ ⟨6⟩ ⟨15⟩ = String.substrEq.loop "uint256[]memory" "[]memory" ⟨14⟩ ⟨7⟩ ⟨15⟩ := by
        conv => lhs; rw [String.substrEq.loop]
        rfl
      have step7 : String.substrEq.loop "uint256[]memory" "[]memory" ⟨14⟩ ⟨7⟩ ⟨15⟩ = String.substrEq.loop "uint256[]memory" "[]memory" ⟨15⟩ ⟨8⟩ ⟨15⟩ := by
        conv => lhs; rw [String.substrEq.loop]
        rfl
      have lastStep : String.substrEq.loop "uint256[]memory" "[]memory" ⟨15⟩ ⟨8⟩ ⟨15⟩ = true := by
        rw [String.substrEq.loop]
        rfl
      calc
        String.substrEq.loop "uint256[]memory" "[]memory" ⟨7⟩ ⟨0⟩ ⟨15⟩ = String.substrEq.loop "uint256[]memory" "[]memory" ⟨8⟩ ⟨1⟩ ⟨15⟩ := step0
        _ = String.substrEq.loop "uint256[]memory" "[]memory" ⟨9⟩ ⟨2⟩ ⟨15⟩ := step1
        _ = String.substrEq.loop "uint256[]memory" "[]memory" ⟨10⟩ ⟨3⟩ ⟨15⟩ := step2
        _ = String.substrEq.loop "uint256[]memory" "[]memory" ⟨11⟩ ⟨4⟩ ⟨15⟩ := step3
        _ = String.substrEq.loop "uint256[]memory" "[]memory" ⟨12⟩ ⟨5⟩ ⟨15⟩ := step4
        _ = String.substrEq.loop "uint256[]memory" "[]memory" ⟨13⟩ ⟨6⟩ ⟨15⟩ := step5
        _ = String.substrEq.loop "uint256[]memory" "[]memory" ⟨14⟩ ⟨7⟩ ⟨15⟩ := step6
        _ = String.substrEq.loop "uint256[]memory" "[]memory" ⟨15⟩ ⟨8⟩ ⟨15⟩ := step7
        _ = true := lastStep
    simp only [List.find?_cons, h]
  | have h : "uint256[]memory".endsWith "[]memory" = true := by
      rw [String.endsWith_eq_endsWith_toSlice]
      apply String.Slice.endsWith_string_iff.mpr
      rw [String.copy_toSlice]
      exact ⟨"uint256".toList, by decide +kernel⟩
    simp only [List.find?_cons, h]

theorem absentLocationSuffix :
    ["[]memory", "[]storage"].find? (fun suffix : String => "uint256".endsWith suffix)
      = none := by
  first
  | decide +kernel
  | have memory : "uint256".endsWith "[]memory" = false := by
      rw [String.endsWith_eq_endsWith_toSlice, String.Slice.endsWith_string_eq_false_iff,
        String.copy_toSlice]
      decide +kernel
    have storage : "uint256".endsWith "[]storage" = false := by
      rw [String.endsWith_eq_endsWith_toSlice, String.Slice.endsWith_string_eq_false_iff,
        String.copy_toSlice]
      decide +kernel
    simp only [List.find?_cons, List.find?_nil, memory, storage]

theorem locationSuffixCharacterBoundary :
    "uint256[]memory".toList.take ("uint256[]memory".length - "[]memory".length)
      = "uint256".toList := by
  decide +kernel


end H62.MigrateSolkey.StringApiControls
