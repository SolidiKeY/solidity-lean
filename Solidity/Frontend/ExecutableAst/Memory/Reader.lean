import Solidity.Frontend.ExecutableAst.Shared.Translate

/-! Location-aware executable array locals and allocation. All results use the
existing Raw syntax; the intrinsic elaborator owns type equality, alias/copy
selection, map-free evidence and index semantics. Child reader errors are final.
No environment, kernel, or alternative evaluator is used by these readers. -/
namespace Solidity.Frontend.ExecutableAst.Memory
open Lean Solidity
open Shared

/-- Exact compiler spelling for the deliberately admitted primitive/array types.
Mappings, structs, narrow widths, bytes and calldata remain unsupported here. -/
private def spelling : Ty → Except String String
  | .prim .int => pure "int256"
  | .prim .uint => pure "uint256"
  | .prim .bool => pure "bool"
  | .ref (.array e) => return (← spelling e) ++ "[]"
  | .ref (.fixed e n) => return (← spelling e) ++ s!"[{n}]"
  | _ => throw "memory reader: unsupported reference element type"

private def description (j : Json) : Except String String := do
  str (← field j "typeDescriptions") "typeString"

private def identifier (loc : String) : Ty → Except String String
  | .prim .int => pure "t_int256"
  | .prim .uint => pure "t_uint256"
  | .prim .bool => pure "t_bool"
  | .ref (.array e) => return "t_array$_" ++ (← identifier (if loc == "storage_ptr" then "storage" else loc) e) ++ "_$dyn_" ++ loc
  | .ref (.fixed e n) => return "t_array$_" ++ (← identifier (if loc == "storage_ptr" then "storage" else loc) e) ++ s!"_${n}_" ++ loc
  | _ => throw "memory reader: unsupported type identifier"

private def memorySpelling : Ty → Except String String
  | .prim p => spelling (.prim p)
  | .ref (.array e) => return (← memorySpelling e) ++ "[] memory"
  | .ref (.fixed e n) => return (← memorySpelling e) ++ s!"[{n}] memory"
  | _ => throw "memory reader: unsupported memory type"

private def checkIdentifier (j : Json) (t : Ty) (loc : String) : Except String Unit := do
  unless (← str (← field j "typeDescriptions") "typeIdentifier") == (← identifier loc t) do
    throw "memory reader: inconsistent type identifier/location"

/-- Check the recursive type syntax and its compiler metadata together. -/
partial def typeName (j : Json) : Except String (Ty × RawTy) := do
  let result ← Shared.typeNameStep typeName j
  unless (← description j) == (← spelling result.1) do
    throw "memory reader: inconsistent type metadata"
  if let .ref (.fixed _ n) := result.1 then
    unless 0 < n ∧ n < 2 ^ 256 do throw "memory reader: invalid fixed array length"
  checkIdentifier j result.1 "storage_ptr"
  return result

/-- The allocation arm is selected by node kind, never by catching a failure. -/
def expressionStep (read : Json → Except String RawExpr)
    (readType : Json → Except String (Ty × RawTy)) (j : Json) : Except String RawExpr := do
  if (← node j) != "FunctionCall" then return ← Shared.expressionStep read j
  let fn ← field j "expression"
  unless (← node fn) == "NewExpression" do
    throw "memory reader: unsupported expression call"
  unless (← str j "kind") == "functionCall" do throw "memory reader: allocation call kind"
  unless (← j.getObjValAs? Bool "tryCall") == false do throw "memory reader: try allocation"
  unless (← arr j "names").isEmpty do throw "memory reader: named allocation arguments"
  let args ← arr j "arguments"
  unless args.size == 1 do throw "memory reader: allocation needs one length"
  let (t, raw) ← readType (← field fn "typeName")
  let .ref r := t | throw "memory reader: new of primitive"
  unless r.newArrOk do throw "memory reader: unsupported allocation type"
  let name ← memorySpelling t
  checkIdentifier j t "memory_ptr"
  unless (← description j) == name do
    throw "memory reader: inconsistent allocation result type/location"
  unless (← description fn) == s!"function (uint256) pure returns ({name})" do
    throw "memory reader: inconsistent allocation constructor type"
  unless (← str (← field fn "typeDescriptions") "typeIdentifier") ==
      "t_function_objectcreation_pure$_t_uint256_$returns$_" ++ (← identifier "memory_ptr" t) ++ "_$" do
    throw "memory reader: inconsistent allocation constructor identifier"
  return .newArr raw (← read args[0]!)

partial def expression (j : Json) : Except String RawExpr :=
  expressionStep expression typeName j

/-- Only explicit memory/storage locations admit reference locals. Primitive
locals require default location. Intrinsic elaboration subsequently checks the
initializer against the declared type and selects identity versus deep copy. -/
def statementsStep (readExpr : Json → Except String RawExpr)
    (readStmts : Json → Except String (List RawStmt))
    (readType : Json → Except String (Ty × RawTy)) (j : Json) : Except String (List RawStmt) := do
  if (← node j) != "VariableDeclarationStatement" then
    return ← Shared.statementsStep readExpr readStmts readType j
  let ds ← arr j "declarations"
  unless ds.size == 1 do throw "memory reader: tuple declaration"
  let d := ds[0]!
  unless (← node d) == "VariableDeclaration" do throw "memory reader: declaration node kind"
  unless (← d.getObjValAs? Bool "stateVariable") == false do throw "memory reader: state local"
  unless (← d.getObjValAs? Bool "constant") == false do throw "memory reader: constant local"
  unless (← str d "mutability") == "mutable" do throw "memory reader: immutable local"
  let (t, raw) ← readType (← field d "typeName")
  unless (← description d) == (← spelling t) do
    throw "memory reader: inconsistent declaration type"
  let loc ← str d "storageLocation"
  let name ← str d "name"
  if name.isEmpty then throw "memory reader: unnamed local"
  let init ← (optional j "initialValue").mapM readExpr
  match t with
  | .prim _ =>
    unless loc == "default" do throw "memory reader: location on primitive local"
    checkIdentifier d t "storage_ptr"
    return [.decl raw name init]
  | .ref _ =>
    match loc with
    | "memory" =>
      checkIdentifier d t "memory_ptr"
      return [.declMemory raw name init]
    | "storage" =>
      checkIdentifier d t "storage_ptr"
      unless init.isSome do throw "memory reader: unset storage local"
      if let some (.newArr ..) := init then throw "memory reader: storage local from new"
      return [.declStorage raw name init]
    | _ => throw "memory reader: unsupported reference location"

partial def statements (j : Json) : Except String (List RawStmt) :=
  statementsStep expression statements typeName j

/-- A/D integration: pass this reader to Shared.function/contract. Control/tuple
extensions should compose the public one-step functions, routing all recursive
children through the combined reader, without retry on error. -/
-- State-root parsing retains Shared support, including mappings. Combined
-- local/allocation handlers must use Memory.typeName, not this root callback.
def reader : Shared.Reader :=
  { Shared.reader with expression, statements }

end Solidity.Frontend.ExecutableAst.Memory
