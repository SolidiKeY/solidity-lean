import Solidity.Tools.Upstream

/-! Regressions for sequencing, deployment, rollback and inconclusive halts. -/
open Solidity Solidity.Frontend Solidity.Tools.Upstream Lean

private def Counter : Contract := contract!{
  uint x = 5;
  function bump() returns (uint) { x++; return x; }
  function set(uint v) returns (uint) { x = v; return x; }
  function fail() { x = 99; revert(); }
  function spin() { while (true) { } }
  function panics() { assert(false); }
}

private def rows : List ImportRow :=
  ["bump", "set", "fail", "spin", "panics"].map fun name =>
    { name, sourceSignature := if name == "set" then "set(uint)" else name ++ "()",
      tag := .diamond, params := [], status := .elaborated, reason := "" }

private def check (text status : String) : IO Unit := do
  let .ok data := Json.parse text | throw (IO.userError "bad test JSON")
  let actual := replay Counter rows data
  unless (actual.getObjValAs? String "status").toOption == some status do
    throw (IO.userError actual.pretty)

#eval check "{\"vectors\":[
  {\"signature\":\"bump()\",\"args\":[],\"failure\":false,\"expected\":[\"6\"]},
  {\"signature\":\"set(uint256)\",\"args\":[\"10\"],\"failure\":false,\"expected\":[\"10\"]},
  {\"signature\":\"fail()\",\"args\":[],\"failure\":true,\"expected\":[]},
  {\"signature\":\"bump()\",\"args\":[],\"failure\":false,\"expected\":[\"11\"]}
]}" "working"

#eval check "{\"vectors\":[
  {\"signature\":\"bump()\",\"args\":[],\"failure\":false,\"expected\":[\"999\"]}
]}" "broken"

#eval check "{\"vectors\":[
  {\"signature\":\"spin()\",\"args\":[],\"failure\":true,\"expected\":[]}
]}" "blocked"

#eval check "{\"vectors\":[
  {\"signature\":\"panics()\",\"args\":[],\"failure\":true,\"expected\":[]}
]}" "blocked"

private def FailedDeployment : Contract := contract!{
  constructor() { revert(); }
  function f() returns (uint) { return 9; }
}

#eval (do
  let text := "{\"vectors\":[
    {\"signature\":\"constructor\",\"args\":[],\"failure\":true,\"expected\":[]},
    {\"signature\":\"f()\",\"args\":[],\"failure\":false,\"expected\":[\"9\"]}
  ]}"
  let .ok data := Json.parse text | throw (IO.userError "bad test JSON")
  let report := replay FailedDeployment [] data
  unless (report.getObjValAs? String "status").toOption == some "blocked" do
    throw (IO.userError report.pretty) : IO Unit)


/- Nominal contract/address overloads can share an ABI spelling, but only
   the selected public declaration is an external transaction. -/
private def NominalOverloads : Contract :=
  let C := contract!{
    function internalF(address x) returns (uint) { return 1; }
    function publicF(address x) returns (uint) { return 2; }
  }
  { C with funs := C.funs.map fun (name, declaration) =>
      (name, { declaration with sourceDecl := some {
        name := "f", signature := some "f(address)",
        callable := if name == "internalF" then .local .internalFn
          else .abi .publicFn .selected none } }) }

#eval (do
  let rows : List ImportRow := [
    { name := "internalF", sourceSignature := "f(contract A)", tag := .internal,
      params := [], status := .elaborated, reason := "" },
    { name := "publicF", sourceSignature := "f(address)", tag := .diamond,
      params := [], status := .elaborated, reason := "" }]
  let .ok data := Json.parse "{\"vectors\":[{\"signature\":\"f(address)\",\"args\":[\"0\"],\"failure\":false,\"expected\":[\"2\"]}]}"
    | throw (IO.userError "bad nominal overload test JSON")
  let actual := replay NominalOverloads rows data
  unless (actual.getObjValAs? String "status").toOption == some "working" do
    throw (IO.userError actual.pretty) : IO Unit)

/- Width admission for a reference tuple must match the destination, even
   though all reference elements share the same intrinsic primitive sort. -/
private def TupleWidths : Contract := contract!{}

/-- error: Solidity elaboration failed: wide has narrow positions none where ·[] 8 bits wide are expected: solc converts no reference type to one of another element type -/
#guard_msgs in #check sol[TupleWidths]{
  uint8[] memory small = new uint8[](1);
  uint[] memory wide = new uint[](1);
  (small, ) = (wide, 0);
}

/-- error: Solidity elaboration failed: small has narrow positions ·[] 8 bits wide where none are expected: solc converts no reference type to one of another element type -/
#guard_msgs in #check sol[TupleWidths]{
  uint8[] memory small = new uint8[](1);
  uint[] memory wide = new uint[](1);
  (wide, ) = (small, 0);
}

/- Nominal ABI matching must not let an out-of-range address input become
   an admitted uint256 transaction merely because its parameter is unused. -/
#eval (do
  let rows : List ImportRow := [
    { name := "publicF", sourceSignature := "f(contract A)", tag := .diamond,
      params := [], status := .elaborated, reason := "" }]
  let data := Json.mkObj [("vectors", toJson ([Json.mkObj [
    ("signature", toJson "f(address)"), ("args", toJson [toString (2^160 : Nat)]),
    ("failure", toJson false), ("expected", toJson ["2"])]] : List Json))]
  let actual := replay NominalOverloads rows data
  unless (actual.getObjValAs? String "status").toOption == some "blocked" &&
      (actual.getObjValAs? String "reason").toOption == some "noncanonical address ABI argument" do
    throw (IO.userError actual.pretty) : IO Unit)
