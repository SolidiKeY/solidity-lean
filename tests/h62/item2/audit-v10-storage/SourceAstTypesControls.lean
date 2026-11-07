import Solidity.Lowering.P8.SourceAstParameters
import Solidity.Source.Ctor

/-! Runtime conversion checks over the unchanged LibraryTry compiler fixtures.
These are not Source program/admission/semantics proofs. Regression purpose:
retain storage formals and string-memory returns without cloning source cases. -/
namespace H62.StorageAudit.SourceAstTypesControls
open Lean Solidity.Source Solidity.Lowering.P8.SourceAstTypes

def get (j : Json) (key : String) : Except String Json := j.getObjVal? key
def array (j : Json) (key : String) : Except String (Array Json) := j.getObjValAs? (Array Json) key
def text (j : Json) (key : String) : Except String String := j.getObjValAs? String key

def storageFormal (p : Syn .param) : Bool :=
  match p with
  | .param (.userType ⟨"S", []⟩) (some .storage) (some "t") => true
  | _ => false

def stringReturn (p : Syn .param) : Bool :=
  match p with
  | .param (.elem .string) (some .memory) none => true
  | _ => false

def inspect (doc : Json) : Except String Nat := do
  let ast ← get doc "ast"
  let mut count := 0
  let mut storageSeen := false
  let mut stringSeen := false
  for top in ← array ast "nodes" do
    if (← text top "nodeType") == "ContractDefinition" then
      for node in ← array top "nodes" do
        if (← text node "nodeType") == "FunctionDefinition" then
          let inputNode ← get node "parameters"
          let returnNode ← get node "returnParameters"
          let args ← array inputNode "parameters"
          let returns ← array returnNode "parameters"
          let inputSyntax ← Solidity.Lowering.P8.SourceAstParameters.parameterList inputNode
          let returnSyntax ← Solidity.Lowering.P8.SourceAstParameters.parameterList returnNode
          unless (inputSyntax.nodes.filter (fun n => n.ctor == .param)).length == args.size &&
              (returnSyntax.nodes.filter (fun n => n.ctor == .param)).length == returns.size do
            throw "parameter length lost"
          for arg in args ++ returns do
            let _ ← parameter arg
            count := count + 1
          if (← text top "name") == "L" && (← text node "name") == "stru" then
            let some first := args[0]? | throw "missing storage formal"
            unless storageFormal (← parameter first) do throw "storage formal changed"
            storageSeen := true
          if (← text top "name") == "C" && (← text node "name") == "g" then
            let some second := returns[1]? | throw "missing string result"
            unless stringReturn (← parameter second) do throw "string result changed"
            stringSeen := true
  unless storageSeen && stringSeen && count == 12 do throw "incomplete fixture conversion"
  return count

#eval do
  for file in ["tests/solc/LibraryTry.ast.json", "tests/solc/LibraryTryIR.ast.json"] do
    let contents ← IO.FS.readFile file
    let result := do inspect (← Json.parse contents)
    match result with
    | .ok count => IO.println s!"{file}: {count} actual parameters/results converted"
    | .error why => throw (IO.userError why)

/-- Kernel reduction controls for malformed lexical inputs. They neither
modify the accepted Source profile nor establish a compiler parser contract. -/
theorem invalid_integer : (elementary "uint7").isOk = false := by decide
theorem noncanonical_integer : (elementary "uint08").isOk = false := by decide
theorem invalid_bytes : (elementary "bytes33").isOk = false := by decide
theorem invalid_location : (location "stack").isOk = false := rfl

/-- info: 'H62.StorageAudit.SourceAstTypesControls.invalid_integer' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms invalid_integer
/-- info: 'H62.StorageAudit.SourceAstTypesControls.noncanonical_integer' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms noncanonical_integer
/-- info: 'H62.StorageAudit.SourceAstTypesControls.invalid_bytes' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms invalid_bytes
/-- info: 'H62.StorageAudit.SourceAstTypesControls.invalid_location' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms invalid_location
end H62.StorageAudit.SourceAstTypesControls
