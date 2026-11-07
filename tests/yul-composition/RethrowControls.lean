import Solidity.Frontend.SolcJson.Body

/-!
Concrete controls of the pre-existing declaration-sensitive rethrow recognizer.
Seven runtime guards traverse existing opaque JSON numeric parsing; three
negative shape/name equalities reduce in the kernel and have axiom reports.
These finite JSON boundary tests do not prove general Yul admission or semantics.
No source AST/state/term representation is introduced.
-/
namespace Solidity.Yul.Composition.RethrowControls
open Lean Solidity.Frontend

def ident (name : String) : Json := Json.mkObj [
  ("nodeType", toJson "YulIdentifier"), ("name", toJson name)]

def call (name : String) (args : List Json) : Json := Json.mkObj [
  ("nodeType", toJson "YulFunctionCall"), ("functionName", ident name),
  ("arguments", toJson args)]

def declaration (id : Nat) (name location typeName : String) : Json := Json.mkObj [
  ("nodeType", toJson "VariableDeclaration"), ("id", toJson id),
  ("name", toJson name), ("storageLocation", toJson location),
  ("typeDescriptions", Json.mkObj [("typeString", toJson typeName)])]

def dataDecl : Json := declaration 7 "data" "memory" "bytes"

def ref (id : Nat) (slot : Bool := false) : Json := Json.mkObj [
  ("declaration", toJson id), ("isOffset", toJson false),
  ("isSlot", toJson slot), ("valueSize", toJson (1 : Nat))]

def stmt (offset : Nat) (same : String := "data") : Json := Json.mkObj [
  ("nodeType", toJson "YulExpressionStatement"),
  ("expression", call "revert" [call "add" [ident "data", Json.mkObj [
    ("nodeType", toJson "YulLiteral"), ("kind", toJson "number"),
    ("value", toJson (toString offset))]], call "mload" [ident same]])]

def block (statements refs : List Json) : Json := Json.mkObj [
  ("nodeType", toJson "InlineAssembly"),
  ("AST", Json.mkObj [("nodeType", toJson "YulBlock"), ("statements", toJson statements)]),
  ("externalReferences", toJson refs)]

def canonical : Json := block [stmt 32] [ref 7, ref 7]

/- The documented non-memory-safe legacy exception is inhabited. -/
#guard (memoryRethrow? [dataDecl] canonical) == (some dataDecl)

/- A missing source declaration cannot be imported as a canonical rethrow. -/
#guard (memoryRethrow? [] canonical) == (none)

/- An incorrect data offset is refused rather than erased. -/
#guard (memoryRethrow? [dataDecl] (block [stmt 31] [ref 7, ref 7])) == (none)

/- Both occurrences must refer to the same declaration. -/
#guard (memoryRethrow? [dataDecl] (block [stmt 32] [ref 7, ref 8])) == (none)

/- A storage value cannot masquerade as a memory bytes buffer. -/
#guard (memoryRethrow? [declaration 7 "data" "storage" "bytes"] canonical) == (none)

/- An unrelated memory type cannot be rethrown as a byte buffer. -/
#guard (memoryRethrow? [declaration 7 "data" "memory" "uint256[]"] canonical) == (none)

/-- The rethrow recognizer never drops an extra assembly statement. -/
theorem extra_statement :
    memoryRethrow? [dataDecl] (block [stmt 32, stmt 32] [ref 7, ref 7]) = none := by rfl

/- Raw slot references are outside the canonical whole-buffer exception. -/
#guard (memoryRethrow? [dataDecl] (block [stmt 32] [ref 7 true, ref 7 true])) == (none)

/-- Distinct pointer and length names cannot masquerade as one byte buffer. -/
theorem different_names :
    memoryRethrow? [dataDecl] (block [stmt 32 "other"] [ref 7, ref 7]) = none := by rfl

/-- Malformed JSON is refused at the boundary. -/
theorem malformed : memoryRethrow? [dataDecl] (Json.mkObj []) = none := by rfl

#print axioms extra_statement
#print axioms different_names
#print axioms malformed
end Solidity.Yul.Composition.RethrowControls
