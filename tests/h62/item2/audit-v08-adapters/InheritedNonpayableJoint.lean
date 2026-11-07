import Solidity.Lowering.V08.InheritedControls

/-! Regression: a payable checked-override fixture cannot witness the joint
nonpayable rejection premises. This separate abstract inheritance unit supplies
all FnOverrideOK fields, an actual base member and a nonpayable tag together.
Only the existing target entry guard is transported; no Source execution,
admission, body correspondence or compiler/H68 adequacy is asserted. -/
namespace H62.AuditV08Adapters.InheritedNonpayableJoint
open Solidity Source
open Solidity.Lowering.V08

def base : Decl :=
  { kind := .function, name := "paid", scope := some "A", top := false,
    node := .function (.ident "paid") .nil (some .external) none
      .nil true none .nil .none }
def derived : Decl :=
  { kind := .function, name := "paid", scope := some "B", top := false,
    node := .function (.ident "paid") .nil (some .pub) (some .view)
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


/-- All metadata premises refer to this one actual inheritance environment. -/
theorem joint : FnOverrideOK environment "B" derived ∧
    base ∈ environment.baseFns "B" derived ∧
    (base.mutability == some .payable) = false :=
  ⟨checked_override, by rw [base_functions]; exact List.mem_singleton_self _, rfl⟩

/-- Full original guard result, for arbitrary supplied world/storage and
nonzero context; no successful target run is assumed. -/
theorem actual_rejection {K : Type} {contracts : K → Contract}
    (world : ContractWorld.World contracts) {key : K} (self : ContractWorld.Address)
    (context : ContractWorld.Context) (storage : Storage (contracts key))
    (nonzero : context.value.1 ≠ 0) :
    world.enter self context storage (derived.mutability == some .payable) = .error .revert :=
  InheritedMetadata.override_nonzero_rejected environment "B" base derived
    joint.1 joint.2.1 joint.2.2 world self context storage nonzero

/-- The context premise is inhabited by the existing genuinely paid context. -/
theorem paid_context : FnOverrideOK environment "B" derived ∧
    base ∈ environment.baseFns "B" derived ∧
    (base.mutability == some .payable) = false ∧ Controls.paidCtx.value.1 ≠ 0 :=
  ⟨joint.1, joint.2.1, joint.2.2, by decide +kernel⟩

/-- The old payable base genuinely fails this model's nonpayable premise. -/
theorem old_payable_refused :
    ¬ ((InheritedControls.base.mutability == some .payable) = false) := by
  decide +kernel

#print axioms checked_override
#print axioms joint
#print axioms actual_rejection
#print axioms paid_context
#print axioms old_payable_refused
end H62.AuditV08Adapters.InheritedNonpayableJoint
