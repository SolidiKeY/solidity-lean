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

-- An inconclusive later call retains the completed prefix and its exact cause.
#eval (do
  for (name, reason) in [("spin", "execution exhausted loop fuel/resources"),
      ("panics", "generic model panic does not retain the ABI panic code")] do
    let text := "{\"vectors\":[" ++
      "{\"signature\":\"bump()\",\"args\":[],\"failure\":false,\"expected\":[\"6\"]}," ++
      "{\"signature\":\"" ++ name ++ "()\",\"args\":[],\"failure\":true,\"expected\":[]}]}"
    let data ← IO.ofExcept (Json.parse text)
    let report := replay Counter rows data
    unless (report.getObjValAs? String "status").toOption == some "blocked" &&
        (report.getObjValAs? String "reason").toOption == some reason do
      throw (IO.userError report.pretty)
    let observed ← IO.ofExcept (report.getObjValAs? (Array Json) "observed")
    unless observed.size == 1 &&
        (observed[0]!.getObjValAs? (List String) "values").toOption == some ["6"] do
      throw (IO.userError "completed prefix observations were lost")
    let blocked ← IO.ofExcept (report.getObjVal? "blockedVector")
    unless (blocked.getObjValAs? String "signature").toOption == some (name ++ "()") do
      throw (IO.userError "blocked vector was lost") : IO Unit)
