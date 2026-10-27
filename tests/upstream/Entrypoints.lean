import Solidity.Tools.Upstream

/-! Source controls for exact ABI entry selection and generated getter execution.
These are observational replays, not source-lowering equivalence theorems. -/
open Solidity Solidity.Frontend Solidity.Tools.Upstream Lean

solc_import "Entrypoints.ast.json" hash 0xce96ed60b7a47884 as Controls.Entrypoints testing entrypoints
solc_import "Entrypoints.ast.json" hash 0xce96ed60b7a47884 as Controls.EntrypointRefusal testing entrypoints

solc_import "EntrypointsIR.ast.json" hash 0x2a108acc20b8a243 as IRControls.Entrypoints testing entrypoints

private def check (text status : String) : IO Unit := do
  let .ok data := Json.parse text | throw (IO.userError "bad test JSON")
  for (C, rows) in [(Controls.Entrypoints, Controls.Entrypoints.report),
      (IRControls.Entrypoints, IRControls.Entrypoints.report)] do
    let actual := replay C rows data
    unless (actual.getObjValAs? String "status").toOption == some status do
      throw (IO.userError actual.pretty)

-- Scalar, mapping/bool keys, nested mapping/fixed/dynamic array, signed result,
-- inherited body, selected override, overload and unerased nominal ABI identity.
#eval check "{\"vectors\":[
  {\"signature\":\"scalar()\",\"args\":[],\"failure\":false,\"expected\":[\"7\"]},
  {\"signature\":\"nested(uint256,uint256,uint256)\",\"args\":[\"2\",\"1\",\"0\"],\"failure\":false,\"expected\":[\"115792089237316195423570985008687907853269984665640564039457584007913129639927\"]},
  {\"signature\":\"nested(uint256,uint256,uint256)\",\"args\":[\"2\",\"2\",\"0\"],\"failure\":true,\"expected\":[]},
  {\"signature\":\"nested(uint256,uint256,uint256)\",\"args\":[\"2\",\"1\",\"1\"],\"failure\":true,\"expected\":[]},
  {\"signature\":\"flags(uint256,bool)\",\"args\":[\"4\",\"true\"],\"failure\":false,\"expected\":[\"12\"]},
  {\"signature\":\"inherited()\",\"args\":[],\"failure\":false,\"expected\":[\"41\"]},
  {\"signature\":\"choose(uint8)\",\"args\":[\"5\"],\"failure\":false,\"expected\":[\"2\"]},
  {\"signature\":\"choose(uint256)\",\"args\":[\"5\"],\"failure\":false,\"expected\":[\"3\"]},
  {\"signature\":\"kind(uint8)\",\"args\":[\"2\"],\"failure\":false,\"expected\":[\"2\"]},
  {\"signature\":\"kind(uint8)\",\"args\":[\"3\"],\"failure\":true,\"expected\":[]},
  {\"signature\":\"kind(uint8)\",\"args\":[\"167\"],\"failure\":true,\"expected\":[]},
  {\"signature\":\"nominal(int256)\",\"args\":[\"-1\"],\"failure\":false,\"expected\":[\"115792089237316195423570985008687907853269984665640564039457584007913129639935\"]}
]}" "working"

#eval check "{\"vectors\":[{\"signature\":\"scalar()\",\"args\":[],\"failure\":false,\"expected\":[\"99\"]}]}" "broken"
#eval check "{\"vectors\":[{\"signature\":\"choose(uint16)\",\"args\":[\"5\"],\"failure\":false,\"expected\":[\"2\"]}]}" "broken"
#eval check "{\"vectors\":[{\"signature\":\"hidden()\",\"args\":[],\"failure\":false,\"expected\":[\"99\"]}]}" "broken"
#eval check "{\"vectors\":[{\"signature\":\"constructor()\",\"args\":[],\"failure\":false,\"expected\":[]}]}" "broken"

-- Invalid enum ABI input must fail before the mutating body runs.
#eval check "{\"vectors\":[
  {\"signature\":\"mutate(uint8)\",\"args\":[\"3\"],\"failure\":true,\"expected\":[]},
  {\"signature\":\"scalar()\",\"args\":[],\"failure\":false,\"expected\":[\"7\"]}
]}" "working"

solc_import "Entrypoints.ast.json" hash 0xce96ed60b7a47884 as Controls.EntrypointConstructor testing entrypoints

#eval (do
  for (arg, failure) in [("2", false), ("3", true), ("167", true)] do
    let vector := Json.mkObj [("signature", toJson "constructor"), ("args", toJson [arg]),
      ("failure", toJson failure), ("expected", toJson ([] : List String))]
    let actual := replay Controls.EntrypointConstructor Controls.EntrypointConstructor.report
      (Json.mkObj [("vectors", toJson [vector])])
    unless (actual.getObjValAs? String "status").toOption == some "working" do
      throw (IO.userError actual.pretty) : IO Unit)

-- Reference-valued getters remain explicit gaps; no observation is discarded.
#eval (do
  unless Controls.EntrypointRefusal.report.any (fun row =>
      row.status == .unsupported && (row.reason.splitOn "reference").length > 1) do
    throw (IO.userError "reference getter was silently omitted") : IO Unit)

-- Duplicate ABI identities and a missing compiler declaration ID fail closed.
#eval (do
  let C := Controls.Entrypoints
  let .ok name := resolveEntry C Controls.Entrypoints.report "scalar()"
    | throw (IO.userError "scalar entry missing")
  let some f := Semantics.lookupBy name C.funs | throw (IO.userError "entry body missing")
  unless (resolveEntry { C with funs := (name, f) :: C.funs } [] "scalar()").toOption.isNone do
    throw (IO.userError "ambiguous ABI entry accepted")
  let missing := { f with sourceDecl := f.sourceDecl.map fun d => { d with declaration := none } }
  unless (resolveEntry { C with funs := [(name, missing)] } [] "scalar()").toOption.isNone do
    throw (IO.userError "missing declaration identity accepted") : IO Unit)

-- Index arity, source declaration identity and narrow signed/result widths survive.
#eval check "{\"vectors\":[{\"signature\":\"nested(uint256,uint256)\",\"args\":[\"2\",\"1\"],\"failure\":false,\"expected\":[\"0\"]}]}" "broken"
#eval (do
  for (signature, id, width, result) in
      [("scalar()", (44 : Int), (8 : Nat), Ty.prim .uint),
       ("nested(uint256,uint256,uint256)", 74, 16, Ty.prim .int)] do
    let .ok name := resolveEntry Controls.Entrypoints Controls.Entrypoints.report signature
      | throw (IO.userError "getter missing")
    let some f := Semantics.lookupBy name Controls.Entrypoints.funs
      | throw (IO.userError "getter body missing")
    unless f.sourceDecl.any (fun d => d.declaration == some id) &&
        f.widths.any (fun (_, n) => n == width) && f.rets.map (·.2) == [result] do
      throw (IO.userError "getter source identity/type/width changed") : IO Unit)

-- Nominal primitives retain their widths; enum getter inputs retain membership.
#eval check "{\"vectors\":[
  {\"signature\":\"typed()\",\"args\":[],\"failure\":false,\"expected\":[\"17\"]},
  {\"signature\":\"unwrapped()\",\"args\":[],\"failure\":false,\"expected\":[\"17\"]},
  {\"signature\":\"nominalMap(int256)\",\"args\":[\"-2\"],\"failure\":false,\"expected\":[\"115792089237316195423570985008687907853269984665640564039457584007913129639927\"]},
  {\"signature\":\"enumerated(uint8)\",\"args\":[\"2\"],\"failure\":false,\"expected\":[\"13\"]},
  {\"signature\":\"enumerated(uint8)\",\"args\":[\"3\"],\"failure\":true,\"expected\":[]},
  {\"signature\":\"enumerated(uint8)\",\"args\":[\"167\"],\"failure\":true,\"expected\":[]}
]}" "working"
#eval check "{\"vectors\":[{\"signature\":\"enumerated(uint8)\",\"args\":[\"3\"],\"failure\":false,\"expected\":[\"0\"]}]}" "broken"

#eval check "{\"vectors\":[{\"signature\":\"negative()\",\"args\":[],\"failure\":false,\"expected\":[\"115792089237316195423570985008687907853269984665640564039457584007913129639919\"]}]}" "working"

solc_import "Entrypoints.ast.json" hash 0xce96ed60b7a47884 as Controls.EntrypointEnumRefusal testing entrypoints
#eval (do
  unless Controls.EntrypointEnumRefusal.report.any (·.status == .unsupported) do
    throw (IO.userError "enum result getter was silently admitted") : IO Unit)

-- Type metadata cannot redirect an elementary key to a nominal declaration.
-- Missing nominal identities and declarations also fail closed.
#eval (do
  let enumDecl := Json.mkObj [("nodeType", toJson "EnumDefinition"), ("id", toJson (2 : Nat)),
    ("members", toJson [Json.null, Json.null])]
  for text in [
      "{\"id\":1,\"typeName\":{\"nodeType\":\"UserDefinedTypeName\"}}",
      "{\"id\":1,\"typeName\":{\"nodeType\":\"UserDefinedTypeName\",\"referencedDeclaration\":999}}",
      "{\"id\":1,\"typeName\":{\"nodeType\":\"Mapping\",\"keyType\":{\"nodeType\":\"ElementaryTypeName\",\"name\":\"uint256\",\"referencedDeclaration\":2},\"valueType\":{\"nodeType\":\"ElementaryTypeName\",\"name\":\"bool\"}}}"] do
    let .ok node := Json.parse text | throw (IO.userError "bad malformed-type control")
    unless (publicGetterPlan [] [enumDecl] [] node "root").toOption.isNone do
      throw (IO.userError "malformed nominal getter type was accepted") : IO Unit)

-- Pin the nominal/enum extension's parameter and result types independently
-- of word encoding (a negative signed word alone could hide signedness loss).
#eval (do
  let C := Controls.Entrypoints
  for (signature, type, inputWidth, outputWidth) in
      [("nominalMap(int256)", PrimTy.int, (none : Option Nat), (16 : Nat)),
       ("enumerated(uint8)", .uint, some 8, 8)] do
    let .ok name := resolveEntry C Controls.Entrypoints.report signature
      | throw (IO.userError "nominal/enum getter missing")
    let some f := Semantics.lookupBy name C.funs | throw (IO.userError "getter body missing")
    unless f.params.all (fun (x, t) => t == Ty.prim type &&
        (Semantics.lookupBy x f.widths) == inputWidth) &&
        f.rets.all (fun (x, t) => t == Ty.prim type &&
          (Semantics.lookupBy x f.widths) == some outputWidth) do
      throw (IO.userError "nominal/enum getter type or width changed")
  let .ok name := resolveEntry C Controls.Entrypoints.report "typed()"
    | throw (IO.userError "narrow constant getter missing")
  let some f := Semantics.lookupBy name C.funs | throw (IO.userError "constant getter body missing")
  unless f.rets.all (fun (x, t) => t == Ty.prim .int &&
      (Semantics.lookupBy x f.widths) == some 224) do
    throw (IO.userError "narrow constant result type or width changed") : IO Unit)

solc_import "EntrypointsIR.ast.json" hash 0x2a108acc20b8a243 as IRControls.EntrypointConstructor testing entrypoints

-- A successful explicit enum constructor must initialize the same runtime
-- contract whose getter is selected, without a second default deployment.
#eval (do
  let .ok data := Json.parse "{\"vectors\":[
    {\"signature\":\"constructor\",\"args\":[\"2\"],\"failure\":false,\"expected\":[]},
    {\"signature\":\"result()\",\"args\":[],\"failure\":false,\"expected\":[\"2\"]}
  ]}" | throw (IO.userError "bad constructor/runtime control")
  for (C, rows) in [(Controls.EntrypointConstructor, Controls.EntrypointConstructor.report),
      (IRControls.EntrypointConstructor, IRControls.EntrypointConstructor.report)] do
    let actual := replay C rows data
    unless (actual.getObjValAs? String "status").toOption == some "working" do
      throw (IO.userError actual.pretty) : IO Unit)
