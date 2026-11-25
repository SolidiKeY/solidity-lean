import Solidity.Tools.ExecutableGoalBinding

/-! Constructor and request data for executable metadata examples.
The nondefault raw contract is quotation data, not admitted Solidity source. -/
open Lean Solidity Solidity.Tools
namespace ExecutableBindingControls

/- Deliberately nondefault raw data exercises quotation, not source admission.
Some location/return flags here are not an admitted Solidity signature. -/
def quotationFunction : FunDecl := {
  sourceDecl := some { declaration := some 29, name := "declared", signature := some "declared(uint256)", mutability := .viewFn, callable := .abi .publicFn .selected (some ⟨17, by decide⟩) }
  params := [("a", .prim .uint)]
  paramLocs := [("a", .memory)]
  rets := [("r", .prim .uint)]
  retMem := true
  retStorage := true
  body := [.assign (.name "x") (.num 7), .whileLoop
    { inv := [.bool true], dec := some (.num 4), unwind := some 2, brk := true,
      qinv := [.all .bool "b" (.expr (.name "b"))] } (.bool false) []]
  mods := [{ name := "m", params := [("p", .prim .bool)], args := [.bool true], body := [.hole], widths := [("p", 1)], locs := [("p", .calldata)] }]
  spec := { requires := [.bool true], ensures := [.bool false], assignable := some [.root "x"], skip := true }
  payable := true
  widths := [("a", 8)] }

def quotationContract : Contract := {
  vars := [("x", .prim .uint)]
  transientRoots := ["x"]
  funs := [("model", quotationFunction)]
  enums := [("E", ["A", "B"])]
  inv := [.bool true]
  widths := [("x", 8)]
  ctor := some quotationFunction
  inits := [("x", .num 9)]
  structs := [("S", "encoded")]
  errors := [("Oops", quotationFunction)]
  evalOrder := .viaIR }

def invocationFixture : Except String Json := Json.parse r#"{"contract":{"nodeType":"ContractDefinition","contractKind":"contract","nodes":[{"nodeType":"FunctionDefinition","id":1,"name":"first","kind":"function","visibility":"public","stateMutability":"pure","modifiers":[],"parameters":{"parameters":[]},"returnParameters":{"parameters":[]},"body":{"nodeType":"Block","statements":[]},"documentation":""},{"nodeType":"FunctionDefinition","id":2,"name":"second","kind":"function","visibility":"public","stateMutability":"pure","modifiers":[],"parameters":{"parameters":[]},"returnParameters":{"parameters":[]},"body":{"nodeType":"Block","statements":[]},"documentation":""}]},"listing":true}"#

end ExecutableBindingControls
