import Solidity.Source.Calls.BoundRecognizer
import Solidity.Source.Progress.BoundParentControls
import Solidity.Source.Progress.BoundCatalogueParentControls

/-! The bound-body catalogue checker on two actually elaborated units. The
hand-built `BoundMemoryCatalogue` proofs of the existing controls are replaced
by one Boolean evaluation; the body, its return types and its admission are
read from the actual dispatch target. The only supplied equations are the
existing evaluations of elaboration and dispatch (`source_body`, `dispatch`),
which do not reduce by `rfl`. Refusals: insufficient default fuel and an
undeclared function. -/
namespace Solidity.Source.Calls.RecognizerControls
open EM Solidity.Lowering.P9 Solidity.Source.Progress Recognize

namespace Local
open BoundParentControls

theorem lookup (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (globals p fixed).prog.body d = some body := source_body

theorem accepted (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    catalogueB (globals p fixed) "C" [] 1 [d] = true := by
  simp only [catalogueB, entryB, List.all_cons, List.all_nil, Bool.and_true, dispatch, signature,
    lookup]
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
  simp only [catalogueB, entryB, List.all_cons, List.all_nil, Bool.and_true, dispatch, signature,
    lookup]
  decide +kernel

def undeclared : Decl := {d with name := "missing"}

theorem undeclared_refused (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    catalogueB (globals p fixed) "C" [] 1 [undeclared] = false := by
  simp only [catalogueB, entryB, List.all_cons, List.all_nil, Bool.and_true]
  rw [show decide (undeclared ∈ E.decls) = false by decide +kernel, Bool.false_and]

end Local

namespace Parent
open BoundCatalogueParentControls

theorem lookup (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    (globals p fixed).prog.body d = some body := source_body

theorem accepted (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    catalogueB (globals p fixed) "C" [] 1 [d] = true := by
  simp only [catalogueB, entryB, List.all_cons, List.all_nil, Bool.and_true, dispatch, signature,
    lookup]
  decide +kernel

theorem catalogue (p : Roadmap.Pipeline) (fixed : Roadmap.Fixed) :
    BoundMemoryCatalogue (fun d=>d ∈ ([] : List Decl)) (globals p fixed) "C" [d] :=
  catalogueB_from_elaborate resolution actual_elaboration (globals p fixed) rfl "C" [] [d] 1
    (checked p fixed) (accepted p fixed)

end Parent

#print axioms Local.accepted
#print axioms Local.catalogue
#print axioms Local.whole
#print axioms Local.no_fuel_refused
#print axioms Local.undeclared_refused
#print axioms Parent.accepted
#print axioms Parent.catalogue
end Solidity.Source.Calls.RecognizerControls
