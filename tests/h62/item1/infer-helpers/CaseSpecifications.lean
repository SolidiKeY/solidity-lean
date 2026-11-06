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


/-! ## Candidate compatibility with the existing typed constructors

These terms retain the original relation, constructor shapes and premises.
Their acceptance still requires a successful bounded Lean check.
-/

/-- The source mapping helper exposes the premise used by `Typed.delete`. -/
theorem source_mapping_premise (τ : STy) :
    (τ.isMapping = false) ↔ ((τ matches .mapping _ _) = false) := Iff.rfl

/-- The static mapping helper exposes the same inline premise. -/
theorem static_mapping_premise (τ : STy) :
    (Solidity.Frontend.Static.isMappingTy τ = false) ↔
      ((τ matches .mapping _ _) = false) := Iff.rfl

/-- Preserve the delete refusal premise while using the source helper. -/
def source_delete {Γ : Ctx} {e : Syn .expr} {τ : STy}
    (d : LVal Γ e τ) (hm : τ.isMapping = false) (hp : Γ.deleteRefused τ e = false) :
    Typed Γ (.unaryPrefix .delete e) (.tuple []) :=
  .delete d hm hp

/-- Preserve the delete refusal premise while using the static helper. -/
def static_delete {Γ : Ctx} {e : Syn .expr} {τ : STy}
    (d : LVal Γ e τ) (hm : Solidity.Frontend.Static.isMappingTy τ = false)
    (hp : Γ.deleteRefused τ e = false) : Typed Γ (.unaryPrefix .delete e) (.tuple []) :=
  .delete d hm hp

/-- Preserve the source payable premise when constructing its derivation. -/
def source_payable {Γ : Ctx} {x : Syn .expr} {σ : STy}
    (d : Typed Γ x σ) (hp : σ.isPayableArg = true) :
    Typed Γ (.payableConv (.positional (.cons x .nil))) (.address true) :=
  .payable d hp

/-- Preserve the static payable premise when constructing its derivation. -/
def static_payable {Γ : Ctx} {x : Syn .expr} {σ : STy}
    (d : Typed Γ x σ) (hp : Solidity.Frontend.Static.payableArg σ = true) :
    Typed Γ (.payableConv (.positional (.cons x .nil))) (.address true) :=
  .payable d hp

/-- Preserve the conversion check and result type with the source location helper. -/
def source_conv_elem {Γ : Ctx} {x : Syn .expr} {σ : STy}
    (el : Elem) (h : el ≠ .addressPayable) (d : Typed Γ x σ)
    (he : σ.explicit Γ.isBase Γ.mapFree (el.ty σ.convLoc) = true) :
    Typed Γ (.call (.elemType el h) (.positional (.cons x .nil))) (el.ty σ.convLoc) :=
  .convElem d rfl he

/-- Preserve the conversion check and result type with the static location helper. -/
def static_conv_elem {Γ : Ctx} {x : Syn .expr} {σ : STy}
    (el : Elem) (h : el ≠ .addressPayable) (d : Typed Γ x σ)
    (he : σ.explicit Γ.isBase Γ.mapFree (el.ty (Solidity.Frontend.Static.convLoc σ)) = true) :
    Typed Γ (.call (.elemType el h) (.positional (.cons x .nil)))
      (el.ty (Solidity.Frontend.Static.convLoc σ)) :=
  .convElem d rfl he

end Solidity.H62.InferHelpers
