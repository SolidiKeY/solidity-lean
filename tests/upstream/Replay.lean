import Solidity.Tools.Upstream

/-! Regressions for sequencing, deployment, rollback and inconclusive halts. -/
open Solidity Solidity.Frontend Solidity.Tools Solidity.Tools.Upstream Lean

private def Counter : Contract := contract!{
  uint x = 5;
  function bump() returns (uint) { x++; return x; }
  function set(uint v) returns (uint) { x = v; return x; }
  function fail() { x = 99; revert(); }
  function spin() { while (true) { } }
  function raw() {
    x = 99;
    bytes memory data = hex"010200";
    assembly { revert(add(data, 32), mload(data)) }
  }
  function panicBytes() {
    bytes memory data = hex"4e487b710000000000000000000000000000000000000000000000000000000000000012";
    assembly { revert(add(data, 32), mload(data)) }
  }
  function panics() { assert(false); }
}

private def rows : List ImportRow :=
  ["bump", "set", "fail", "spin", "panics", "raw", "panicBytes"].map fun name =>
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
]}" "broken"

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


-- Complete raw data, trailing zeros and rollback are observed in call order.
#eval check "{\"vectors\":[
  {\"signature\":\"raw()\",\"args\":[],\"failure\":true,\"expected\":[],\"revertBytes\":[1,2,0]},
  {\"signature\":\"bump()\",\"args\":[],\"failure\":false,\"expected\":[\"6\"]}
]}" "working"

#eval check "{\"vectors\":[
  {\"signature\":\"raw()\",\"args\":[],\"failure\":true,\"expected\":[],\"revertBytes\":[1,2]}
]}" "broken"

#eval check "{\"vectors\":[
  {\"signature\":\"raw()\",\"args\":[],\"failure\":true,\"expected\":[]}
]}" "broken"

-- Concrete guards and retained buffers certify only their actual code.
#eval (do
  let vector code name := Json.mkObj [
    ("signature", toJson name), ("args", toJson ([] : List String)),
    ("failure", toJson true), ("expected", toJson ([] : List String)),
    ("revertBytes", toJson ((Semantics.panicSelector ++ Semantics.wordBytes code).map UInt8.toNat))]
  for (code, name, status) in [(18, "panicBytes()", "working"), (17, "panicBytes()", "broken"),
      (18, "panics()", "broken"), (1, "panics()", "working")] do
    let report := replay Counter rows (Json.mkObj [("vectors", toJson [vector code name])])
    unless (report.getObjValAs? String "status").toOption == some status do
      throw (IO.userError report.pretty) : IO Unit)

-- A later unresolved call cannot erase an earlier successful observation.
#eval (do
  let .ok data := Json.parse "{\"vectors\":[
    {\"signature\":\"bump()\",\"args\":[],\"failure\":false,\"expected\":[\"6\"]},
    {\"signature\":\"missing()\",\"args\":[],\"failure\":false,\"expected\":[]}
  ]}" | throw (IO.userError "bad JSON")
  let report := replay Counter rows data
  unless (report.getObjValAs? String "status").toOption == some "broken" &&
      ((report.getObjValAs? (Array Json) "observed").toOption.map Array.size) == some 1 do
    throw (IO.userError report.pretty) : IO Unit)

-- A failed deployment's observation survives the blocked subsequent host call.
#eval (do
  let .ok data := Json.parse "{\"vectors\":[
    {\"signature\":\"constructor\",\"args\":[],\"failure\":true,\"expected\":[]},
    {\"signature\":\"f()\",\"args\":[],\"failure\":false,\"expected\":[\"9\"]}
  ]}" | throw (IO.userError "bad JSON")
  let report := replay FailedDeployment [] data
  unless (report.getObjValAs? String "status").toOption == some "blocked" &&
      ((report.getObjValAs? (Array Json) "observed").toOption.map Array.size) == some 1 do
    throw (IO.userError report.pretty) : IO Unit)

private def DataDeployment : Contract := contract!{
  constructor() {
    bytes memory data = hex"00ab";
    assembly { revert(add(data, 32), mload(data)) }
  }
}

-- Constructor failure bytes are compared exactly, including a leading zero.
#eval (do
  for (bytes, status) in [([0, 171], "working"), ([], "broken")] do
    let vector := Json.mkObj [("signature", toJson "constructor"),
      ("args", toJson ([] : List String)), ("failure", toJson true),
      ("expected", toJson ([] : List String)), ("revertBytes", toJson (bytes : List Nat))]
    let report := replay DataDeployment [] (Json.mkObj [("vectors", toJson [vector])])
    unless (report.getObjValAs? String "status").toOption == some status do
      throw (IO.userError report.pretty) : IO Unit)


private def AbiVectors : Contract := contract!{
  uint counter = 5;
  function decode(bytes memory data) returns (uint[] memory) {
    counter++;
    return abi.decode(data, (uint[]));
  }
  function unused(uint8[] calldata xs) returns (uint) { return 7; }
  function narrow(uint8 x) returns (uint) { counter++; return x; }
  function signed(int8 x) returns (int8) { return x; }
  function fixedBytes(bytes4 x) returns (bytes4) { return x; }
  function bump() returns (uint) { counter++; return counter; }
}
private def abiRows : List ImportRow :=
  [("decode", "decode(bytes)"), ("unused", "unused(uint8[])"), ("narrow", "narrow(uint8)"),
    ("signed", "signed(int8)"), ("fixedBytes", "fixedBytes(bytes4)"), ("bump", "bump()")].map fun (name,sig) =>
    { name, sourceSignature := sig, tag := .diamond, params := [], status := .elaborated, reason := "" }
private def abiWords (xs : List Nat) := (xs.flatMap Semantics.wordBytes).map UInt8.toNat
private def abiVector (sig : String) (inputs outputs : List String)
    (data expected : List Nat) (failure := false) : Json := Json.mkObj [
  ("signature", toJson sig), ("inputTypes", toJson inputs), ("outputTypes", toJson outputs),
  ("calldata", toJson data), ("expectedBytes", toJson expected), ("failure", toJson failure)]
private def abiCheck (vectors : List Json) (status : String) (count : Nat) : IO Unit := do
  let report := replay AbiVectors abiRows (Json.mkObj [("vectors", toJson vectors)])
  unless (report.getObjValAs? String "status").toOption == some status &&
      ((report.getObjValAs? (Array Json) "observed").toOption.map Array.size) == some count do
    throw (IO.userError report.pretty)

-- Bytes -> dynamic array output, actual body once, initialized state retained.
#eval abiCheck [
  abiVector "decode(bytes)" ["bytes"] ["uint256[]"]
    (abiWords [32,192,32,4,3,4,5,6]) (abiWords [32,4,3,4,5,6]),
  abiVector "bump()" [] ["uint256"] [] (abiWords [7])] "working" 2
-- Output mismatches cannot guide admission or become passes.
#eval abiCheck [abiVector "decode(bytes)" ["bytes"] ["uint256[]"]
  (abiWords [32,192,32,4,3,4,5,6]) (abiWords [32,4,3,4,5,99])] "broken" 1
-- Malformed aggregate data must stay blocked even when failure is expected:
-- the external calldata decoder can defer checks until individual accesses.
#eval (do
  for bytes in [abiWords [32,1,256], abiWords [32,10], abiWords [999,0]] do
    abiCheck [abiVector "unused(uint8[])" ["uint8[]"] ["uint256"] bytes [] true] "blocked" 0 : IO Unit)
#eval abiCheck [abiVector "unused(uint8[])" ["uint8[]"] ["uint256"]
  (abiWords [32,2,1,255]) (abiWords [7])] "working" 1
-- Primitive v2 entry checks are eager: invalid width and short calldata revert
-- before the body; its attempted counter write must never become visible.
#eval abiCheck [
  abiVector "narrow(uint8)" ["uint8"] ["uint256"] (abiWords [256]) [] true,
  abiVector "narrow(uint8)" ["uint8"] ["uint256"] [] [] true,
  abiVector "narrow(uint8)" ["uint8"] ["uint256"] (abiWords [255]) (abiWords [255]),
  abiVector "bump()" [] ["uint256"] [] (abiWords [7])] "working" 4
#eval abiCheck [abiVector "signed(int8)" ["int8"] ["int8"]
  (abiWords [255]) [] true] "working" 1
#eval abiCheck [abiVector "signed(int8)" ["int8"] ["int8"]
  (abiWords [2^256-1]) (abiWords [2^256-1])] "working" 1
#eval abiCheck [abiVector "fixedBytes(bytes4)" ["bytes4"] ["bytes4"]
  (abiWords [0x61626364 * 2^224]) (abiWords [0x61626364 * 2^224])] "working" 1
#eval abiCheck [abiVector "fixedBytes(bytes4)" ["bytes4"] ["bytes4"]
  (abiWords [0x61626364 * 2^224 + 1]) [] true] "working" 1
-- Schema mismatch is a block before execution, not an ABI reinterpretation.
#eval abiCheck [abiVector "narrow(uint8)" ["uint256"] ["uint256"]
  (abiWords [7]) (abiWords [7])] "blocked" 0

private def AbiDeployment : Contract := contract!{
  uint value = 5;
  constructor(uint[] memory xs) { value += xs[0]; }
  function get() returns (uint) { return value; }
}
#eval (do
  let rows : List ImportRow :=
    [{ name := "get", sourceSignature := "get()", tag := .diamond,
       params := [], status := .elaborated, reason := "" }]
  let vectors := [abiVector "constructor" ["uint256[]"] [] (abiWords [32,1,7]) [],
    abiVector "get()" [] ["uint256"] [] (abiWords [12])]
  let report := replay AbiDeployment rows (Json.mkObj [("vectors", toJson vectors)])
  unless (report.getObjValAs? String "status").toOption == some "working" do
    throw (IO.userError report.pretty) : IO Unit)

private def FunctionAbiVectors : Contract := contract!{
  function selectorPart(function() external f) returns (uint) { return uint32(f.selector); }
  function addressPart(function() external f) returns (uint) { return uint160(f.address); }
  function identity(function() external f) returns (function() external) { return f; }
}
private def functionRows : List ImportRow :=
  ["selectorPart", "addressPart", "identity"].map fun name =>
    { name, sourceSignature := name ++ "(function)", tag := .diamond,
      params := [], status := .elaborated, reason := "" }
#eval (do
  let address := 0x1234567890123456789012345678901234567890
  let input := (address * 2^32 + 0x12345678) * 2^64
  let check (v : Json) (status : String) (count : Nat) := do
    let report := replay FunctionAbiVectors functionRows (Json.mkObj [("vectors", toJson [v])])
    unless (report.getObjValAs? String "status").toOption == some status &&
        ((report.getObjValAs? (Array Json) "observed").toOption.map Array.size) == some count do
      throw (IO.userError report.pretty)
  check (abiVector "selectorPart(function)" ["function"] ["uint256"]
    (abiWords [input]) (abiWords [0x12345678])) "working" 1
  check (abiVector "addressPart(function)" ["function"] ["uint256"]
    (abiWords [input]) (abiWords [address])) "working" 1
  check (abiVector "selectorPart(function)" ["function"] ["uint256"]
    (abiWords [input]) (abiWords [0x12345679])) "broken" 1
  check (abiVector "selectorPart(function)" ["function"] ["uint256"]
    (abiWords [input+1]) [] true) "blocked" 0
  -- Existing call-return admission refuses this width/metadata transport.
  check (abiVector "identity(function)" ["function"] ["function"]
    (abiWords [input]) (abiWords [input])) "blocked" 0 : IO Unit)

-- Decoder rejection must match both the failure flag and the exact empty data.
#eval abiCheck [abiVector "narrow(uint8)" ["uint8"] ["uint256"]
  (abiWords [256]) [] false] "broken" 1
#eval abiCheck [abiVector "narrow(uint8)" ["uint8"] ["uint256"]
  (abiWords [256]) (abiWords [17]) true] "broken" 1

private def EntryControls : Contract := contract!{
  uint n = 5;
  error E(uint value);
  function context() returns (uint) { return uint160(msg.sender) + msg.value; }
  function internalFail(uint16 x) { n = 99; uint16 y = x + 1; }
  function outer(uint16 x) { internalFail(x); }
  function reason() { n = 99; require(false, "reason"); }
  function custom() { n = 99; revert E(17); }
  function get() returns (uint) { return n; }
}

-- External observation keeps the real caller/value, including inlining.
-- It does not set selfFrame, whose rewriting would make this return zero.
#eval (do
  let tx : TTx := { msgSender := ⟨37, rfl⟩, msgValue := ⟨5, rfl⟩ }
  for exact in [false, true] do
    let ss := [← IO.ofExcept (runStmt EntryControls "context" [])]
    let ⟨_,Q⟩ ← IO.ofExcept (if exact then entryProg EntryControls ss else elabProgS EntryControls ss)
    let .ok out := Q.runF 1000 (State.deploy EntryControls tx)
      | throw (IO.userError "context failed")
    let values := localVals (Q.outNames []) out.st.env
    unless Semantics.lookupBy (Var.ofName retLocal) values == some (.uint (PrimTy.ofIntD .uint 42)) do
      throw (IO.userError "entry changed caller/value") : IO Unit)

-- The same source has its ordinary abstract reading and its exact entry
-- reading. Neither a wrong code nor trailing/missing bytes can agree.
#eval (do
  let rs : List ImportRow := ["outer", "reason", "custom", "get"].map fun name =>
    { name, sourceSignature := name ++ (if name == "outer" then "(uint16)" else "()"),
      tag := .diamond, params := [], status := .elaborated, reason := "" }
  let failure sig args bytes := Json.mkObj [("signature", toJson sig),
    ("args", toJson (args : List String)), ("failure", toJson true),
    ("expected", toJson ([] : List String)), ("revertBytes", toJson (bytes : List Nat))]
  let get := Json.mkObj [("signature", toJson "get()"), ("args", toJson ([] : List String)),
    ("failure", toJson false), ("expected", toJson ["5"])]
  let panic := (Semantics.encodePanic 17).map UInt8.toNat
  let reason := (Semantics.encodeError "reason".toUTF8.toList).map UInt8.toNat
  let custom := ((Semantics.wordBytes (Keccak.selector "E(uint256)")).drop 28 |>.map UInt8.toNat) ++ abiWords [17]
  for (v,status) in [(failure "outer(uint16)" ["65535"] panic,"working"),
      (failure "outer(uint16)" ["65535"] (abiWords [17]),"broken"),
      (failure "reason()" [] reason,"working"), (failure "reason()" [] [],"broken"),
      (failure "custom()" [] custom,"working"), (failure "custom()" [] (custom ++ [0]),"broken")] do
    let report := replay EntryControls rs (Json.mkObj [("vectors", toJson [v,get])])
    unless (report.getObjValAs? String "status").toOption == some status do
      throw (IO.userError report.pretty) : IO Unit)

-- Only known fresh results break calldata alias provenance. Direct aliases,
-- casts and nested writes remain guarded; declarations cannot shadow builtins.
#guard (calldataCheck [] 4 ["data"] ["result"]
  [.ret (some (.call "abi.encode" [.name "data"]))]).isOk
#guard !(calldataCheck [] 4 ["data"] ["result"] [.ret (some (.name "data"))]).isOk
#guard !(calldataCheck [] 4 ["data"] ["result"]
  [.ret (some (.call "bytes" [.name "data"]))]).isOk
#guard !(calldataCheck [] 4 ["data"] ["result"]
  [.ret (some (.call "abi.encode" [.assign (.index (.name "data") (.num 0)) (.num 1)]))]).isOk
#guard !(calldataCheck [("abi.encode", {params := [], body := []})] 4 ["data"] ["result"]
  [.ret (some (.call "abi.encode" [.name "data"]))]).isOk
#guard (abiTyExpr? (.call "#abiArrayType" [.index (.name "uint") (.num 2)])).map RawTy.toStr ==
  some "uint[2][]"
#guard (abiTyExpr? (.call "#abiArrayType" [.index (.name "uint[]") (.num 2)])).map RawTy.toStr ==
  some "uint[][2][]"

private def FreshControls : Contract := contract!{
  function decoded(bytes calldata data) returns (uint[] memory) { return abi.decode(data, (uint[])); }
  function nested(uint[2][] memory x) returns (uint) { return x[1][0]; }
}
#eval (do
  let rows : List ImportRow := [("decoded", "decoded(bytes)"), ("nested", "nested(uint256[2][])")].map fun (name,sig) =>
    { name, sourceSignature := sig, tag := .diamond, params := [], status := .elaborated, reason := "" }
  let vectors := [abiVector "decoded(bytes)" ["bytes"] ["uint256[]"]
      (abiWords [32,96,32,1,7]) (abiWords [32,1,7]),
    abiVector "nested(uint256[2][])" ["uint256[2][]"] ["uint256"]
      (abiWords [32,2,1,2,3,4]) (abiWords [3])]
  let report := replay FreshControls rows (Json.mkObj [("vectors", toJson vectors)])
  unless (report.getObjValAs? String "status").toOption == some "working" do
    throw (IO.userError report.pretty) : IO Unit)

-- ABI v1 raw admission has a stricter boundary: only canonical input, even
-- for primitive arguments. No v2 decoder failure can certify a v1 failure.
#eval (do
  for (n,status) in [(255,"working"),(256,"blocked")] do
    let vector := Json.mkObj [("signature",toJson "narrow(uint8)"),
      ("calldata",toJson (abiWords [n])), ("inputTypes",toJson ["uint8"]),
      ("outputTypes",toJson ["uint256"]), ("canonicalOnly",toJson true),
      ("failure",toJson false), ("expectedBytes",toJson (abiWords [n]))]
    abiCheck [vector] status (if n == 255 then 1 else 0) : IO Unit)

-- Trailing bytes lie outside declared objects. They are retained in the input
-- but cannot become extra elements, alter the result or certify a failure.
#eval abiCheck [abiVector "unused(uint8[])" ["uint8[]"] ["uint256"]
  (abiWords [32,2,1,255,999]) (abiWords [7])] "working" 1
#eval abiCheck [abiVector "unused(uint8[])" ["uint8[]"] ["uint256"]
  (abiWords [32,2,1,255,999]) [] true] "broken" 1
#eval abiCheck [abiVector "unused(uint8[])" ["uint8[]"] ["uint256"]
  (abiWords [32,3,1,255,999]) [] true] "blocked" 0

#eval (do
  let data := abiWords [32,2,1,255] ++ [170,187,255]
  let v := abiVector "unused(uint8[])" ["uint8[]"] ["uint256"] data (abiWords [7])
  let report := replay AbiVectors abiRows (Json.mkObj [("vectors",toJson [v])])
  let .ok observations := report.getObjValAs? (Array Json) "observed"
    | throw (IO.userError report.pretty)
  let actual := observations[0]?.bind fun j => (j.getObjValAs? (List Nat) "calldataBytes").toOption
  unless actual == some data do throw (IO.userError "trailing calldata was lost") : IO Unit)
