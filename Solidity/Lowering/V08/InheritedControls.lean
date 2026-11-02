import Solidity.Lowering.V08.InheritedMetadata
import Solidity.Lowering.V08.Controls

/-! A real nonempty source inheritance chain and checked override metadata.
No source admission, dispatch/body certificate or execution theorem is asserted. -/
namespace Solidity.Lowering.V08.InheritedControls
open Solidity
open Source
open InheritedMetadata

def base : Decl :=
  { kind := .function, name := "paid", scope := some "A", top := false,
    node := .function (.ident "paid") .nil (some .external) (some .payable)
      .nil true none .nil .none }
def derived : Decl :=
  { kind := .function, name := "paid", scope := some "B", top := false,
    node := .function (.ident "paid") .nil (some .pub) (some .payable)
      .nil false (some []) .nil .none }
def sourceUnit : Syn .unit := .unit (.cons (.contract true "A" .none .nil
  (.cons base.node .nil)) (.cons (.contract true "B" .none
    (.cons (.inherit ⟨"A", []⟩ .none) .nil) (.cons derived.node .nil)) .nil))
def environment : Env := sourceUnit.env

theorem base_member : base ∈ sourceUnit.decls := by
  exact List.mem_cons_of_mem _ (List.mem_cons_self)
theorem derived_member : derived ∈ sourceUnit.decls := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_self)))
theorem base_functions : environment.baseFns "B" derived = [base] := rfl

theorem checked_override : FnOverrideOK environment "B" derived := by
  constructor
  · intro _ _; rfl
  · intro absent
    rw [base_functions] at absent
    cases absent
  · intro f member
    rw [base_functions] at member
    have same : f = base := List.mem_singleton.mp member
    subst f
    rfl
  · intro enough
    rw [base_functions] at enough
    contradiction
  · intro paths equal name member
    have empty : paths = [] := Option.some.inj equal.symm
    subst paths
    cases member
  · intro f member
    rw [base_functions] at member
    have same : f = base := List.mem_singleton.mp member
    subst f
    rfl
  · intro f member
    rw [base_functions] at member
    have same : f = base := List.mem_singleton.mp member
    subst f
    rfl
  · intro f member
    rw [base_functions] at member
    have same : f = base := List.mem_singleton.mp member
    subst f
    rfl
  · intro paths equal
    have empty : paths = [] := Option.some.inj equal.symm
    subst paths
    exact List.nodup_nil
  · intro f member body
    rw [base_functions] at member
    have same : f = base := List.mem_singleton.mp member
    subst f
    cases body

theorem inherited_payment :
    (base.mutability == some .payable) = (derived.mutability == some .payable) :=
  override_payable environment "B" base derived checked_override (by rw [base_functions]; exact List.mem_singleton_self _)

def paid (payable : Bool) : TRes
    (Option (Int × Int × Int × Int) × List UInt8) := do
  let world ← Controls.setup
  let (next, bytes) ← world.call (⟨Controls.self⟩ : ContractWorld.Handle ())
    { Controls.entry with payable } Controls.paidCtx
  pure (Controls.observe next, bytes)

theorem funded_header : (paid (derived.mutability == some .payable)).toOption =
    some (some (93, 7, 3, 9), [0xab, 0xcd]) := by decide +kernel

theorem wrong_header : paid false = .error .revert := rfl

theorem stricter_nonpayable : Source.mutOK none (some .view) = true ∧
    Source.mutOK (some .view) (some .pure) = true := ⟨rfl, rfl⟩
theorem wrong_payability : Source.mutOK (some .payable) none = false ∧
    Source.mutOK none (some .payable) = false := ⟨rfl, rfl⟩
end Solidity.Lowering.V08.InheritedControls

#print axioms Solidity.Lowering.V08.InheritedControls.base_member
#print axioms Solidity.Lowering.V08.InheritedControls.derived_member
#print axioms Solidity.Lowering.V08.InheritedControls.base_functions
#print axioms Solidity.Lowering.V08.InheritedControls.checked_override
#print axioms Solidity.Lowering.V08.InheritedControls.inherited_payment
#print axioms Solidity.Lowering.V08.InheritedControls.funded_header
#print axioms Solidity.Lowering.V08.InheritedControls.wrong_header
#print axioms Solidity.Lowering.V08.InheritedControls.stricter_nonpayable
#print axioms Solidity.Lowering.V08.InheritedControls.wrong_payability
