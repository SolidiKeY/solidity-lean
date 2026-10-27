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


/-! Ordinary source transient cells: constructor sharing, entry reset,
persistent retention and rollback are exercised by the actual replay path. -/
private def TransactionCounter : Contract := contract!{
  uint transient scratch;
  uint saved;
  constructor() { scratch = 7; saved = scratch; }
  function tick() returns (uint) { scratch += saved; saved++; return scratch; }
  function inspect() returns (uint, uint) { return (scratch, saved); }
  function fail() { scratch = 99; saved = 99; revert(); }
}

private def transactionRows : List ImportRow :=
  ["tick", "inspect", "fail"].map fun name =>
    { name, sourceSignature := name ++ "()", tag := .diamond,
      params := [], status := .elaborated, reason := "" }

private def transactionCheck (expected status : String) : IO Unit := do
  let .ok data := Json.parse expected | throw (IO.userError "bad test JSON")
  let report := replay TransactionCounter transactionRows data
  unless (report.getObjValAs? String "status").toOption == some status do
    throw (IO.userError report.pretty)

#eval transactionCheck "{\"vectors\":[
  {\"signature\":\"inspect()\",\"args\":[],\"failure\":false,\"expected\":[\"0\",\"7\"]},
  {\"signature\":\"tick()\",\"args\":[],\"failure\":false,\"expected\":[\"7\"]},
  {\"signature\":\"tick()\",\"args\":[],\"failure\":false,\"expected\":[\"8\"]},
  {\"signature\":\"fail()\",\"args\":[],\"failure\":true,\"expected\":[]},
  {\"signature\":\"tick()\",\"args\":[],\"failure\":false,\"expected\":[\"9\"]}
]}" "working"

-- This control would match if cells accidentally persisted between calls.
#eval transactionCheck "{\"vectors\":[
  {\"signature\":\"tick()\",\"args\":[],\"failure\":false,\"expected\":[\"7\"]},
  {\"signature\":\"tick()\",\"args\":[],\"failure\":false,\"expected\":[\"15\"]}
]}" "broken"
