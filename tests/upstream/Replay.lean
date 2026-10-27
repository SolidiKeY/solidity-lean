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
  function excluded() { assume(false); }
}

private def rows : List ImportRow :=
  ["bump", "set", "fail", "spin", "panics", "excluded"].map fun name =>
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
  for (name, reason) in [("spin", "execution exhausted loop fuel"),
      ("excluded", "execution reached a model resource bound (including recursive unrolling); not an EVM failure"),
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

-- Getter lookup uses source ABI identity, not a report row or model name.
private def GetterCounter (callable : SourceCallable) : Contract :=
  { Counter with funs := Counter.funs.map fun (name, d) =>
      (name, if name == "set" then { d with sourceDecl := some {
        declaration := some 0, name := "sourceGetter", signature := some "sourceGetter(uint256)", callable } } else d) }

#eval (do
  let .ok data := Json.parse "{\"vectors\":[{\"signature\":\"sourceGetter(uint256)\",\"args\":[\"12\"],\"failure\":false,\"expected\":[\"12\"]}]}"
    | throw (IO.userError "bad test JSON")
  for (role, status) in [(SourceCallable.getter ⟨0, by decide⟩, "working"),
      (.implementation, "broken"), (.local .internalFn, "broken")] do
    let report := replay (GetterCounter role) [] data
    unless (report.getObjValAs? String "status").toOption == some status do
      throw (IO.userError report.pretty) : IO Unit)

-- Resource limits caught inside import rows are still inconclusive.
#eval (do
  let row : ImportRow := {
      name := "set", sourceSignature := "set(uint)",
      tag := .diamond, params := [], status := .unsupported,
      reason := "callee left out: maximum recursion depth has been reached" }
  let report := replay Counter [row] Json.null
  unless (report.getObjValAs? String "status").toOption == some "blocked" do
    throw (IO.userError report.pretty) : IO Unit)

-- Type canonicalization must never rewrite the source declaration name.
private def NameCollision : Contract :=
  { Counter with funs := Counter.funs.map fun (name, d) =>
      (name, { d with sourceDecl := some {
        declaration := some 0, name := name, signature := (if name == "bump" then some "uint256value()" else if name == "fail" then some "uintvalue()" else none),
        callable := .getter ⟨0, by decide⟩ } }) }

#eval (do
  let .ok data := Json.parse "{\"vectors\":[{\"signature\":\"uintvalue()\",\"args\":[],\"failure\":true,\"expected\":[]}]}"
    | throw (IO.userError "bad test JSON")
  let report := replay NameCollision [] data
  unless (report.getObjValAs? String "status").toOption == some "working" do
    throw (IO.userError report.pretty) : IO Unit)

#eval (do
  for messages in [["ordinary warning", "maximum recursion depth"],
      ["heartbeats exhausted", "ordinary warning"]] do
    let report := diagnosticFailure messages
    unless (report.getObjValAs? String "status").toOption == some "blocked" &&
        (report.getObjValAs? String "reason").toOption == some ("\n".intercalate messages) do
      throw (IO.userError report.pretty)
  unless ((diagnosticFailure ["ordinary error"]).getObjValAs? String "status").toOption == some "broken" do
    throw (IO.userError "ordinary diagnostics were hidden") : IO Unit)


/- Nominal contract/address overloads can share an ABI spelling, but only
   the selected public declaration is an external transaction. -/
private def NominalOverloads : Contract :=
  let C := contract!{
    function internalF(address x) returns (uint) { return 1; }
    function publicF(address x) returns (uint) { return 2; }
  }
  { C with funs := C.funs.map fun (name, declaration) =>
      (name, { declaration with sourceDecl := some {
        declaration := some 1, name := "f", signature := some "f(address)",
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

private def GetterIdentityBase : Contract := contract!{
  function one() returns (uint) { return 1; }
  function two() returns (uint) { return 2; }
}

/-- Getter identity must retain names containing ABI type spellings. -/
private def GetterIdentity : Contract :=
  { GetterIdentityBase with funs := GetterIdentityBase.funs.map fun (name, d) =>
      let sourceName := if name == "one" then "amountuint256" else "amountuint"
      (name, { d with sourceDecl := some {
        declaration := some 2
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
