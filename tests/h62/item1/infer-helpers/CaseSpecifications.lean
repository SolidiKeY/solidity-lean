import Solidity.Source.Infer
import Solidity.Frontend.Static.Infer

/-!
Candidate case specifications for the copied inference helpers. This file is
an additive test, not a replacement for either inferencer. The constructor
inventory is explicit so that a new `STy` constructor requires review.
The file requires a successful Lean check before its theorems are evidence.
-/

namespace Solidity.H62.InferHelpers

open Solidity.Source

/-- Expected mapping, payable-argument and conversion-location results. -/
def expected : STy → Bool × Bool × DataLoc
  | .int _ => (false, false, .memory)
  | .bool => (false, false, .memory)
  | .address _ => (false, true, .memory)
  | .fixedBytes _ _ => (false, false, .memory)
  | .fixed _ => (false, false, .memory)
  | .enum _ => (false, false, .memory)
  | .udvt _ => (false, false, .memory)
  | .contract _ => (false, true, .memory)
  | .bytes loc => (false, false, loc)
  | .string loc => (false, false, loc)
  | .array _ _ _ => (false, false, .memory)
  | .struct _ _ => (false, false, .memory)
  | .mapping _ _ => (true, false, .memory)
  | .fn _ _ _ _ => (false, false, .memory)
  | .rational _ => (false, false, .memory)
  | .hexConst _ _ => (false, false, .memory)
  | .stringLit _ => (false, false, .memory)
  | .tuple _ => (false, false, .memory)

/-- All source helper results agree with the constructor specification. -/
theorem source_cases (τ : STy) :
    expected τ = (τ.isMapping, τ.isPayableArg, τ.convLoc) := by
  cases τ <;> rfl

/-- All static helper results agree with the same constructor specification. -/
theorem static_cases (τ : STy) :
    expected τ = (Solidity.Frontend.Static.isMappingTy τ,
      Solidity.Frontend.Static.payableArg τ, Solidity.Frontend.Static.convLoc τ) := by
  cases τ <;> rfl


/-- The two mapping tests return the same Boolean on every source type. -/
theorem mapping_agreement (τ : STy) :
    τ.isMapping = Solidity.Frontend.Static.isMappingTy τ := by
  cases τ <;> rfl

/-- The two payable-argument tests return the same Boolean on every source type. -/
theorem payable_agreement (τ : STy) :
    τ.isPayableArg = Solidity.Frontend.Static.payableArg τ := by
  cases τ <;> rfl

/-- The two conversion-location functions agree on every source type. -/
theorem location_agreement (τ : STy) :
    τ.convLoc = Solidity.Frontend.Static.convLoc τ := by
  cases τ <;> rfl

/-- Mappings are accepted by the mapping test for arbitrary key and value types. -/
theorem mapping_positive (key value : STy) :
    (STy.mapping key value).isMapping = true ∧
    Solidity.Frontend.Static.isMappingTy (.mapping key value) = true := by
  exact ⟨rfl, rfl⟩

/-- This test is shallow: an array containing a mapping is not itself a mapping. -/
theorem mapping_array_negative (loc : DataLoc) (key value : STy) :
    (STy.array loc (.mapping key value) none).isMapping = false ∧
    Solidity.Frontend.Static.isMappingTy (.array loc (.mapping key value) none) = false := by
  exact ⟨rfl, rfl⟩

/-- Both payable flags on an address are accepted as payable arguments. -/
theorem payable_address (payable : Bool) :
    (STy.address payable).isPayableArg = true ∧
    Solidity.Frontend.Static.payableArg (.address payable) = true := by
  exact ⟨rfl, rfl⟩

/-- Contract arguments are accepted independently of the declaration name. -/
theorem payable_contract (name : DeclName) :
    (STy.contract name).isPayableArg = true ∧
    Solidity.Frontend.Static.payableArg (.contract name) = true := by
  exact ⟨rfl, rfl⟩

/-- Boolean arguments witness a payable refusal. -/
theorem payable_bool_negative :
    STy.bool.isPayableArg = false ∧
    Solidity.Frontend.Static.payableArg .bool = false := by
  exact ⟨rfl, rfl⟩

/-- Dynamic bytes retain every possible source location. -/
theorem location_bytes (loc : DataLoc) :
    (STy.bytes loc).convLoc = loc ∧
    Solidity.Frontend.Static.convLoc (.bytes loc) = loc := by
  exact ⟨rfl, rfl⟩

/-- Strings retain every possible source location. -/
theorem location_string (loc : DataLoc) :
    (STy.string loc).convLoc = loc ∧
    Solidity.Frontend.Static.convLoc (.string loc) = loc := by
  exact ⟨rfl, rfl⟩

/-- Arrays use the default location even when their own location is different. -/
theorem location_array_default (loc : DataLoc) (elem : STy) (len : Option Nat) :
    (STy.array loc elem len).convLoc = .memory ∧
    Solidity.Frontend.Static.convLoc (.array loc elem len) = .memory := by
  exact ⟨rfl, rfl⟩

end Solidity.H62.InferHelpers
