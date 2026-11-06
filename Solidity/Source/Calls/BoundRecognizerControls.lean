import Solidity.Source.Calls.BoundRecognizer
import Solidity.Source.Progress.BoundParentControls
import Solidity.Source.Progress.BoundCatalogueParentControls

/-! The bound-body catalogue checker on two actually elaborated units. Each
catalogue is derived by one Boolean evaluation; the body, its return types and
its admission are read from the actual dispatch target. To reduce the check the
controls rewrite with the fixtures' proved evaluations of dispatch and body
lookup (`dispatch`, `source_body`), which do not reduce by `rfl`. Refusals:
insufficient default fuel, the declaration-membership guard, and body admission
of a string-literal statement. -/
namespace Solidity.Source.Calls.RecognizerControls
open EM Solidity.Lowering.P9 Solidity.Source.Progress Recognize

namespace Local
open BoundParentControls

theorem lookup (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (globals p fixed).prog.body d = some body := source_body

theorem accepted (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    catalogueB (globals p fixed) "C" [] 1 [d] = true := by
  simp only [catalogueB, entryB, List.all_cons, List.all_nil, Bool.and_true]
  rw [BoundParentControls.dispatch p fixed, BoundParentControls.signature, lookup p fixed]
  decide +kernel

theorem catalogue (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    BoundMemoryCatalogue (fun d=>d ∈ ([] : List Decl)) (globals p fixed) "C" [d] :=
  catalogueB_from_elaborate resolution actual_elaboration (globals p fixed) rfl "C" [] [d] 1
    (checked p fixed) (accepted p fixed)

theorem whole (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ReadyProgramCalls resolution (globals p fixed) "C" :=
  checked_program_calls resolution actual_elaboration (globals p fixed) rfl "C" [] [d] 1
    (checked p fixed) (accepted p fixed) (by decide +kernel)

/-- The fixed `bool[2]` return default needs one fuel step. -/
theorem no_fuel_refused (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    catalogueB (globals p fixed) "C" [] 0 [d] = false := by
  simp only [catalogueB, entryB, List.all_cons, List.all_nil, Bool.and_true]
  rw [BoundParentControls.dispatch p fixed, BoundParentControls.signature, lookup p fixed]
  decide +kernel

def undeclared : Decl := {d with name := "missing"}

theorem undeclared_refused (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    catalogueB (globals p fixed) "C" [] 1 [undeclared] = false := by
  simp only [catalogueB, entryB, List.all_cons, List.all_nil, Bool.and_true]
  rw [show decide (undeclared ∈ E.decls) = false by decide +kernel, Bool.false_and]

/-- Body admission refuses an item outside the bound-parent fragment: a string
literal expression statement is neither `ValFragC` nor a ready shape. -/
def strayItems : RItems E [Aty] false .body [] [] := .stmt (.expr (.str [1])) .nil

theorem stray_refused : boundB [] strayItems = false := by decide

end Local

namespace Parent
open BoundCatalogueParentControls

theorem lookup (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (globals p fixed).prog.body d = some body := source_body

theorem accepted (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    catalogueB (globals p fixed) "C" [] 1 [d] = true := by
  simp only [catalogueB, entryB, List.all_cons, List.all_nil, Bool.and_true]
  rw [BoundCatalogueParentControls.dispatch p fixed, BoundCatalogueParentControls.signature, lookup p fixed]
  decide +kernel

theorem catalogue (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    BoundMemoryCatalogue (fun d=>d ∈ ([] : List Decl)) (globals p fixed) "C" [d] :=
  catalogueB_from_elaborate resolution actual_elaboration (globals p fixed) rfl "C" [] [d] 1
    (checked p fixed) (accepted p fixed)

theorem whole (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    ReadyProgramCalls resolution (globals p fixed) "C" :=
  checked_program_calls resolution actual_elaboration (globals p fixed) rfl "C" [] [d] 1
    (checked p fixed) (accepted p fixed) (by decide +kernel)

end Parent

#print axioms Local.accepted
#print axioms Local.catalogue
#print axioms Local.whole
#print axioms Local.no_fuel_refused
#print axioms Local.undeclared_refused
#print axioms Parent.accepted
#print axioms Parent.catalogue
#print axioms Parent.whole
#print axioms Local.stray_refused
end Solidity.Source.Calls.RecognizerControls
