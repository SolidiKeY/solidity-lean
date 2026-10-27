import Solidity.Tools.Upstream

/-! Canonical ABI identity must preserve type-like text inside function names. -/
solc_import "../operators-0.8.38/AbiIdentity.ast.json" hash 0x49bdcd231818bdbe
  as Imported.AbiIdentity testing
solc_import "../operators-0.8.38/AbiIdentityIR.ast.json" hash 0x5596782269ddbf6b
  as Imported.IR.AbiIdentity testing

namespace Solidity.Upstream.AbiIdentity
open Solidity Lean Solidity.Frontend Solidity.Tools.Upstream

private def positive := "{\"vectors\":[
  {\"signature\":\"route_uint()\",\"args\":[],\"failure\":false,\"expected\":[\"11\"]},
  {\"signature\":\"route_uint256()\",\"args\":[],\"failure\":false,\"expected\":[\"22\"]},
  {\"signature\":\"route_int()\",\"args\":[],\"failure\":false,\"expected\":[\"33\"]},
  {\"signature\":\"route_int256()\",\"args\":[],\"failure\":false,\"expected\":[\"44\"]}
]}"

private def wrong := "{\"vectors\":[
  {\"signature\":\"route_uint256()\",\"args\":[],\"failure\":false,\"expected\":[\"11\"]}
]}"

private def check (C : Contract) (rows : List ImportRow) (text expected : String) : IO Unit := do
  let data ← IO.ofExcept (Json.parse text)
  let result := replay C rows data
  unless (result.getObjValAs? String "status").toOption == some expected do
    throw (IO.userError result.pretty)

#eval check Imported.AbiIdentity Imported.AbiIdentity.report positive "working"
#eval check Imported.IR.AbiIdentity Imported.IR.AbiIdentity.report positive "working"
#eval check Imported.AbiIdentity Imported.AbiIdentity.report wrong "broken"
#eval check Imported.IR.AbiIdentity Imported.IR.AbiIdentity.report wrong "broken"

private def Native : Contract := contract!{
  function route_uint() returns (uint) { return 11; }
  function route_uint256() returns (uint) { return 22; }
  function route_int() returns (int) { return 33; }
  function route_int256() returns (int) { return 44; }
}

private def nativeRows : List ImportRow :=
  ["route_uint", "route_uint256", "route_int", "route_int256"].map fun name =>
    { name, sourceSignature := name ++ "()", tag := .diamond,
      params := [], status := .elaborated, reason := "" }

#eval check Native nativeRows positive "working"
#eval check Native nativeRows wrong "broken"
end Solidity.Upstream.AbiIdentity
