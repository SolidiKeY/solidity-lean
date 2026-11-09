import Solidity.Lowering.P9.CatalogueRecognizerCompleteness
import Solidity.Lowering.P9.BoundRecognizerControls

/-! Inhabited controls for readiness and relative catalogue completeness.
Both pipeline instances are existing elaborated fixtures, not supplied runs. -/
namespace Solidity.Source.Calls.Recognize.CompletenessControls
open Solidity.Source.Progress

def referenceItems (E : Env) : RItems E [] false .body [.bytes .memory] [.bytes .memory] :=
  .unchecked (.stmt (.expr (.local .here)) .nil) .nil

theorem reference_ready (E : Env) :
    ReadyItems (fun d => d ∈ ([] : List Decl)) [] false (referenceItems E) :=
  .unchecked (.stmt (.expr (.local _)) .nil) .nil

theorem reference_accepted (E : Env) : itemsB [] (referenceItems E) = true :=
  itemsB_complete (reference_ready E)

theorem reference_bound (E : Env) : boundB [] (referenceItems E) = true :=
  boundB_complete (.ready (reference_ready E))

namespace Parent
open BoundCatalogueParentControls

theorem body_accepted : boundB [] body.items = true := boundB_complete admitted_body

theorem from_certificate (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ∃ fuel, catalogueB (globals p fixed) "C" [] fuel [d] = true :=
  catalogueB_complete (globals p fixed) "C" [] [d] (catalogue p fixed)

theorem checked_calls_from_certificate (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ReadyProgramCalls resolution (globals p fixed) "C" := by
  obtain ⟨fuel,accepted⟩ := from_certificate p fixed
  exact checked_program_calls resolution actual_elaboration (globals p fixed) rfl "C" [] [d] fuel
    (checked p fixed) accepted (by decide +kernel)

theorem equivalence (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    BoundMemoryCatalogue (fun d => d ∈ ([] : List Decl)) (globals p fixed) "C" [d] ↔
      ∃ fuel, catalogueB (globals p fixed) "C" [] fuel [d] = true :=
  catalogueB_iff_from_elaborate resolution actual_elaboration (globals p fixed) rfl "C" [] [d]
    (checked p fixed)

theorem low_fuel_refused (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    catalogueB (globals p fixed) "C" [] 0 [d] = false := by
  simp only [catalogueB,entryB,List.all_cons,List.all_nil,Bool.and_true]
  rw [BoundCatalogueParentControls.dispatch p fixed,BoundCatalogueParentControls.signature,RecognizerControls.Parent.lookup p fixed]
  decide +kernel

theorem low_fuel_not_refutation (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    BoundMemoryCatalogue (fun d => d ∈ ([] : List Decl)) (globals p fixed) "C" [d] ∧
      catalogueB (globals p fixed) "C" [] 0 [d] = false ∧
      ∃ fuel, catalogueB (globals p fixed) "C" [] fuel [d] = true :=
  ⟨catalogue p fixed,low_fuel_refused p fixed,from_certificate p fixed⟩
end Parent

theorem stray_not_admitted :
    ¬ BoundParentItems (fun d => d ∈ ([] : List Decl)) [BoundParentControls.Aty] false
      RecognizerControls.Local.strayItems := by
  intro admitted
  have accepted := boundB_complete admitted
  rw [RecognizerControls.Local.stray_refused] at accepted
  cases accepted

theorem undeclared_refused_every_fuel (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) (fuel : Nat) :
    catalogueB (BoundParentControls.globals p fixed) "C" [] fuel
      [RecognizerControls.Local.undeclared] = false := by
  simp only [catalogueB,entryB,List.all_cons,List.all_nil,Bool.and_true]
  rw [show decide (RecognizerControls.Local.undeclared ∈ BoundParentControls.E.decls) = false
      by decide +kernel,Bool.false_and]

/-- info: 'Solidity.Source.Calls.Recognize.CompletenessControls.reference_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reference_ready
/-- info: 'Solidity.Source.Calls.Recognize.CompletenessControls.reference_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reference_accepted
/-- info: 'Solidity.Source.Calls.Recognize.CompletenessControls.reference_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reference_bound
/-- info: 'Solidity.Source.Calls.Recognize.CompletenessControls.Parent.body_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Parent.body_accepted
/-- info: 'Solidity.Source.Calls.Recognize.CompletenessControls.Parent.from_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Parent.from_certificate
/-- info: 'Solidity.Source.Calls.Recognize.CompletenessControls.Parent.checked_calls_from_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Parent.checked_calls_from_certificate
/-- info: 'Solidity.Source.Calls.Recognize.CompletenessControls.Parent.equivalence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Parent.equivalence
/-- info: 'Solidity.Source.Calls.Recognize.CompletenessControls.Parent.low_fuel_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Parent.low_fuel_refused
/-- info: 'Solidity.Source.Calls.Recognize.CompletenessControls.Parent.low_fuel_not_refutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Parent.low_fuel_not_refutation
/-- info: 'Solidity.Source.Calls.Recognize.CompletenessControls.stray_not_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stray_not_admitted
/-- info: 'Solidity.Source.Calls.Recognize.CompletenessControls.undeclared_refused_every_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms undeclared_refused_every_fuel
end Solidity.Source.Calls.Recognize.CompletenessControls
