import Solidity.Source.Inheritance
import Solidity.Lowering.V08.PayableMetadata

/-!
# Inherited callable payment observations

The published override checker supplies mutOK, not a body-lowering certificate.
Its actual accepted cases preserve payment tags, including stricter nonpayable
view/pure overrides. The target clauses compare header guards on the same
supplied world/storage/context; they do not identify or compile source bodies.
-/
namespace Solidity.Lowering.V08.InheritedMetadata
open Solidity
open ContractWorld

theorem mutOK_payable (base derived : Option Source.Mutability)
    (accepted : Source.mutOK base derived = true) :
    (base == some .payable) = (derived == some .payable) := by
  cases base with
  | none =>
    cases derived with
    | none => rfl
    | some derived => cases derived <;> first | rfl | cases accepted
  | some base =>
    cases base <;> cases derived with
    | none => first | rfl | cases accepted
    | some derived => cases derived <;> first | rfl | cases accepted

/-- Consume the actual static check and an actual member of its base list. -/
theorem override_payable (environment : Source.Env) (scope : String)
    (base derived : Source.Decl) (checked : Source.FnOverrideOK environment scope derived)
    (member : base ∈ environment.baseFns scope derived) :
    (base.mutability == some .payable) = (derived.mutability == some .payable) :=
  mutOK_payable _ _ (checked.mutab base member)

/-- Only the payment argument of the existing entry guard is transported. -/
theorem override_enter {K : Type} {contracts : K → Contract}
    (environment : Source.Env) (scope : String) (base derived : Source.Decl)
    (checked : Source.FnOverrideOK environment scope derived)
    (member : base ∈ environment.baseFns scope derived)
    (world : World contracts) {key : K} (self : Address) (context : Context)
    (storage : Storage (contracts key)) :
    world.enter self context storage (base.mutability == some .payable) =
      world.enter self context storage (derived.mutability == some .payable) := by
  rw [override_payable environment scope base derived checked member]

/-- An accepted override cannot make a nonpayable ordinary entry accept funds.
This is not a restriction on internal ambient msg.value. -/
theorem override_nonzero_rejected {K : Type} {contracts : K → Contract}
    (environment : Source.Env) (scope : String) (base derived : Source.Decl)
    (checked : Source.FnOverrideOK environment scope derived)
    (member : base ∈ environment.baseFns scope derived)
    (nonpayable : (base.mutability == some .payable) = false)
    (world : World contracts) {key : K} (self : Address) (context : Context)
    (storage : Storage (contracts key)) (nonzero : context.value.1 ≠ 0) :
    world.enter self context storage (derived.mutability == some .payable) = .error .revert := by
  rw [← override_payable environment scope base derived checked member, nonpayable]
  exact PayableMetadata.nonpayable_enter world self context storage nonzero
end Solidity.Lowering.V08.InheritedMetadata

#print axioms Solidity.Lowering.V08.InheritedMetadata.mutOK_payable
#print axioms Solidity.Lowering.V08.InheritedMetadata.override_payable
#print axioms Solidity.Lowering.V08.InheritedMetadata.override_enter
#print axioms Solidity.Lowering.V08.InheritedMetadata.override_nonzero_rejected
