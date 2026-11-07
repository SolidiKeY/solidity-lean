import Lean.Data.Json
import Solidity.Source.Syntax

/-! Compiler-AST leaf types and parameters in the existing intrinsic Source
syntax. Regression purpose: preserve qualified struct spelling, storage aliases
and string types while preparing input for Source.elaborate. This incomplete
conversion component makes no Source admission/profile decision; unsupported
nodes are conversion gaps, not new Source exclusions. No program, origin or
semantic adequacy is provided here. -/
namespace Solidity.Lowering.P8.SourceAstTypes
open Lean Solidity.Source

def path (name : String) : Except String IdPath :=
  match name.splitOn "." with
  | [] => .error "empty type path"
  | head :: tail =>
    if head.isEmpty || tail.any String.isEmpty then .error "empty type path component"
    else .ok ⟨head, tail⟩

def location (name : String) : Except String (Option DataLoc) :=
  match name with
  | "default" => .ok none
  | "storage" => .ok (some .storage)
  | "memory" => .ok (some .memory)
  | "calldata" => .ok (some .calldata)
  | _ => .error "unrecognized data location"

/-- Decimal width reading over the finite character list, so lexical controls
can reduce in the kernel without a native string-parser proof. -/
def decimalWidth (digits : List Char) : Option Nat :=
  if digits.isEmpty then none else
    digits.foldlM (fun n c =>
      if '0' ≤ c ∧ c ≤ '9' then some (n * 10 + (c.toNat - '0'.toNat))
      else none) 0

def elementary (name : String) : Except String Elem := do
  match name with
  | "bool" => return .bool
  | "string" => return .string
  | "bytes" => return .bytes
  | "address" => return .address
  | "uint" => return .int false 256 (by decide)
  | "int" => return .int true 256 (by decide)
  | _ =>
    if ['u','i','n','t'].isPrefixOf name.data || ['i','n','t'].isPrefixOf name.data then
      let signed := ['i','n','t'].isPrefixOf name.data
      let width := if signed then name.data.drop 3 else name.data.drop 4
      let some bits := decimalWidth width | throw "invalid integer width"
      if width.head? == some '0' then throw "noncanonical integer width"
      if h : bits % 8 = 0 ∧ 8 ≤ bits ∧ bits ≤ 256 then
        return .int signed bits h
      else throw "invalid integer width"
    else if ['b','y','t','e','s'].isPrefixOf name.data then
      let width := name.data.drop 5
      let some size := decimalWidth width | throw "invalid bytes width"
      if width.head? == some '0' then throw "noncanonical bytes width"
      if h : 1 ≤ size ∧ size ≤ 32 then return .fixedBytes size h
      else throw "invalid bytes width"
    else throw "unimplemented elementary type conversion"

/-- Nonrecursive leaf conversion only. SourceAstCompoundTypes extends this
reader for arrays/mappings/functions; failures here are conversion gaps,
not accepted-program refusals. -/
def typeNameLeaf (node : Json) : Except String (Syn .typeName) := do
  let kind ← node.getObjValAs? String "nodeType"
  match kind with
  | "ElementaryTypeName" =>
    let name ← node.getObjValAs? String "name"
    if name == "address" then
      match node.getObjVal? "stateMutability" with
      | .ok (.str "payable") => return .elem .addressPayable
      | .ok (.str "nonpayable") | .error _ => return .elem .address
      | _ => throw "unrecognized address mutability"
    else return .elem (← elementary name)
  | "UserDefinedTypeName" =>
    let written ← match node.getObjVal? "pathNode" with
      | .ok p => p.getObjValAs? String "name"
      | .error _ => node.getObjValAs? String "namePath"
    return .userType (← path written)
  | _ => throw "unimplemented non-leaf type conversion"

/-- Parameters preserve the written location and optional name. This leaf
adapter does not resolve declaration IDs or certify a function signature. -/
def parameter (node : Json) : Except String (Syn .param) := do
  unless (← node.getObjValAs? String "nodeType") == "VariableDeclaration" do
    throw "parameter declaration required"
  let ty ← typeNameLeaf (← node.getObjVal? "typeName")
  let loc ← location (← node.getObjValAs? String "storageLocation")
  let name ← node.getObjValAs? String "name"
  return .param ty loc (if name.isEmpty then none else some name)

/-- info: 'Solidity.Lowering.P8.SourceAstTypes.elementary' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms elementary
/-- info: 'Solidity.Lowering.P8.SourceAstTypes.typeNameLeaf' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms typeNameLeaf
/-- info: 'Solidity.Lowering.P8.SourceAstTypes.parameter' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms parameter

end Solidity.Lowering.P8.SourceAstTypes
