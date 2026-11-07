import Solidity.Lowering.P8.SourceAstTypes

/-! Ordered compiler parameter containers in existing intrinsic Source syntax.
Regression purpose: keep parameter/result order, storage qualifiers and string
returns when preparing Source.elaborate input. This incomplete conversion
component supplies neither function declarations nor resolution/admission. -/
namespace Solidity.Lowering.P8.SourceAstParameters
open Lean Solidity.Source

/-- Reuse the indexed Source list constructors without a parallel AST. -/
def syntaxList {c : Cat} : List (Syn c) → Syn (.list c)
  | [] => .nil
  | head :: tail => .cons head (syntaxList tail)

/-- Proof-only eliminator motive: generalize the syntax index to avoid
equality casts. It is not part of the executable conversion path. -/
def ElementsAt : Cat → Type
  | .list c => List (Syn c)
  | _ => Unit

noncomputable def elementsAt {c : Cat} (value : Syn c) : ElementsAt c := by
  induction value with
  | nil => exact []
  | cons head tail _ tailElements => exact head :: tailElements
  | _ => exact ()

noncomputable def elements {c : Cat} (value : Syn (.list c)) : List (Syn c) := elementsAt value

theorem elements_syntaxList {c : Cat} (values : List (Syn c)) :
    elements (syntaxList values) = values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    change head :: elements (syntaxList tail) = head :: tail
    rw [ih]

/-- Every child is converted by the existing leaf reader, in source order;
errors propagate rather than dropping unsupported parameters. -/
def parameters (nodes : List Json) : Except String (Syn (.list .param)) := do
  return syntaxList (← nodes.mapM SourceAstTypes.parameter)

/-- Exact order and exact conversion errors are retained, not just lengths. -/
theorem parameters_elements (nodes : List Json) :
    (parameters nodes).map elements = nodes.mapM SourceAstTypes.parameter := by
  unfold parameters
  cases h : nodes.mapM SourceAstTypes.parameter with
  | error message => rfl
  | ok values =>
    change Except.ok (elements (syntaxList values)) = Except.ok values
    rw [elements_syntaxList]

def parameterList (node : Json) : Except String (Syn (.list .param)) := do
  unless (← node.getObjValAs? String "nodeType") == "ParameterList" do
    throw "parameter list required"
  let nodes ← node.getObjValAs? (Array Json) "parameters"
  parameters nodes.toList

/-- info: 'Solidity.Lowering.P8.SourceAstParameters.elements_syntaxList' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms elements_syntaxList
/-- info: 'Solidity.Lowering.P8.SourceAstParameters.parameters_elements' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms parameters_elements
/-- info: 'Solidity.Lowering.P8.SourceAstParameters.parameterList' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms parameterList
end Solidity.Lowering.P8.SourceAstParameters
