import Solidity.Backend.StructuredFlow.MappedCondition

/-! Additive proposal: one intrinsic mapped Boolean-copy execution law and two
structurally different typed fixtures. No source outcome is reclassified here.
Checked on the live pinned Lean 4.24.0 import closure via cache-aware lake lean.
This protects distinct-donor versus same-slot copy execution without dropping
untouched machine fields. It does not establish migrated 4.35 compatibility,
original-control correspondence, refusal coverage or comparative timings. -/
namespace Solidity.Backend.StructuredFlow.GenericMapped
open Solidity.Evm Solidity.Lowering.V07 Solidity.Lowering.G19

/-- A donor and destination inhabit the actual Source context. Their images in
    the target context must both be Boolean slots, with exact witnesses. -/
structure Fixture (srcΓ : Source.RCtx) (Γ : Ctx) where
  mapping : ContextMap srcΓ Γ
  destination : Source.Idx srcΓ .bool
  donor : Source.Idx srcΓ .bool
  destinationBool : (mapping.slot destination).1 = .val .bool
  donorBool : (mapping.slot donor).1 = .val .bool

/-- One intrinsic program, rather than an untyped vector of instructions. -/
def program {srcΓ : Source.RCtx} {Γ : Ctx} (C : Contract) (f : Fixture srcΓ Γ) :
    Prog C Γ (.val .bool :: Γ) :=
  AssignmentReturnFlag.code f.mapping f.destination f.donor f.destinationBool f.donorBool

/-- Semantic execution for arbitrary contexts, typed slot choices, base and
    full machine. The existing compiler/code correspondence supplies the bridge;
    the proof uses the actual run theorem, never a finite decision table. -/
theorem compiled_execution {srcΓ : Source.RCtx} {Γ : Ctx} (C : Contract)
    (f : Fixture srcΓ Γ) (base : Nat) (machine : Machine) :
    run (compileProg base (program C f)) machine =
      .ok (MappedCondition.after base f.mapping f.destination f.donor
        f.destinationBool f.donorBool machine) 0 := by
  rw [show compileProg base (program C f) =
    MappedCondition.emit base f.mapping f.destination f.donor f.destinationBool f.donorBool from
      (MappedCondition.code_exact (C := C) base f.mapping f.destination f.donor
        f.destinationBool f.donorBool).symm]
  exact MappedCondition.run_exact base f.mapping f.destination f.donor
    f.destinationBool f.donorBool machine

abbrev BooleanFixture := Fixture [.bool,.bool] [.val .bool,.val .bool]

def booleanMap : ContextMap [.bool,.bool] [.val .bool,.val .bool] :=
  (ContextMap.empty.cons .bool (.val .bool)).cons .bool (.val .bool)

/-- The distinct donor and same-slot alias cases from the original controls. -/
def copyFixture : BooleanFixture := ⟨booleanMap,.here,.there .here,rfl,rfl⟩
def selfFixture : BooleanFixture := ⟨booleanMap,.here,.here,rfl,rfl⟩
def fixtures : List BooleanFixture := [copyFixture,selfFixture]

/-- Every table row inherits the same universal execution theorem, including
    all untouched machine fields. The table contains data, not proof results. -/
theorem fixtures_execute (C : Contract) (base : Nat) (machine : Machine) :
    ∀ f ∈ fixtures, run (compileProg base (program C f)) machine =
      .ok (MappedCondition.after base f.mapping f.destination f.donor
        f.destinationBool f.donorBool machine) 0 := by
  intro f _
  exact compiled_execution C f base machine

#print axioms compiled_execution
#print axioms fixtures_execute
end Solidity.Backend.StructuredFlow.GenericMapped
