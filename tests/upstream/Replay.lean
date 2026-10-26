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

private def GetterIdentityBase : Contract := contract!{
  function one() returns (uint) { return 1; }
  function two() returns (uint) { return 2; }
}

/-- Getter identity must retain names containing ABI type spellings. -/
private def GetterIdentity : Contract :=
  { GetterIdentityBase with funs := GetterIdentityBase.funs.map fun (name, d) =>
      let sourceName := if name == "one" then "amountuint256" else "amountuint"
      (name, { d with sourceDecl := some {
        name := sourceName
        signature := some (sourceName ++ "()")
        callable := .getter ⟨0, by decide⟩ } }) }

#eval (do
  let .ok data := Json.parse "{\"vectors\":[
    {\"signature\":\"amountuint256()\",\"args\":[],\"failure\":false,\"expected\":[\"1\"]},
    {\"signature\":\"amountuint()\",\"args\":[],\"failure\":false,\"expected\":[\"2\"]}
  ]}" | throw (IO.userError "bad getter test")
  let report := replay GetterIdentity [] data
  unless (report.getObjValAs? String "status").toOption == some "working" do
    throw (IO.userError report.pretty) : IO Unit)

#eval (do
  let .ok data := Json.parse "{\"vectors\":[
    {\"signature\":\"one()\",\"args\":[],\"failure\":false,\"expected\":[\"1\"]}
  ]}" | throw (IO.userError "bad getter test")
  let report := replay GetterIdentity [] data
  unless (report.getObjValAs? String "status").toOption == some "broken" do
    throw (IO.userError report.pretty) : IO Unit)
