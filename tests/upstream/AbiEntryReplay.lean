import Solidity.Tools.Upstream

/-! Lane CF1 replay controls: typed ABI entry decoding of noncanonical and
lazy layouts (`Semantics/AbiEntry.lean`, `Tools/UpstreamEntry.lean`). Each
vector's expected outcome is pinned solc 0.8.38's
(`tests/abi-0.8.38/LazyEntry.vectors.json`): positive controls run the body
once on the decoded value (a read-only calldata parameter on its lazy value),
entry failures are empty reverts before the body with state rolled back, and
the remaining lazy-only cases stay blocked by name. Run by
`scripts/test-solidity.test.mjs`. -/
open Solidity Solidity.Frontend Solidity.Tools Solidity.Tools.Upstream Lean

namespace AbiEntryReplay

private def C : Contract := contract!{
  uint counter = 5;
  function outer(uint[][] calldata x) returns (uint) { counter++; return x.length; }
  function inner(uint[][] calldata x, uint i) returns (uint) { counter++; return x[i].length; }
  function mem(uint[][] memory x) returns (uint) { counter++; return x.length + x[0].length; }
  function cat(bytes memory a, bytes memory b) returns (uint) { counter++; return a.length + b.length; }
  function narrow(uint8[] calldata xs) returns (uint) { counter++; return xs.length; }
  function copy(uint[][] calldata x) returns (uint) { uint[][] memory m = x; return m.length; }
  function narrowAt(uint8[] calldata xs, uint i) returns (uint) { counter++; return xs[i]; }
  function element(uint[][] calldata x, uint i, uint j) returns (uint) { counter++; return x[i][j]; }
  function enc(uint[][] calldata x) returns (uint) { counter++; return abi.encode(x).length; }
  function encIf(uint[][] calldata x, uint i) returns (uint) {
    counter++;
    if (i == 0) { return 7; }
    return abi.encode(x).length;
  }
  function reencode(uint[][3] calldata a) { counter++; abi.encode(a); }
  function order(uint8[] calldata x, uint k) returns (uint) { return x[0] + 1 / k; }
  function add16(uint16 a, uint16 b) returns (uint16) { return a + b; }
  function sx(int8 a, bool c) returns (int) { if (c) { return a; } return 0; }
  function v1arr(uint[] memory xs) returns (uint) { return xs.length; }
  function sliceK(uint[] calldata xs, uint k) returns (uint) { uint[] calldata t = xs[0:]; return t[k] + (k = 5); }
  function shadow(uint8[] calldata x) returns (uint) { { uint[] memory x = new uint[](1); return x[0]; } }
  function bump() returns (uint) { counter++; return counter; }
}

private def D : Contract := contract!{
  struct S { uint a; uint[] b; }
  uint counter = 5;
  function sc(S calldata s) returns (uint) { counter++; return s.a + s.b.length; }
  function sm(S memory s) returns (uint) { counter++; return s.a + s.b.length; }
  function bump() returns (uint) { counter++; return counter; }
}

private def rows : List ImportRow :=
  [("outer", "outer(uint256[][])"), ("inner", "inner(uint256[][],uint256)"),
   ("mem", "mem(uint256[][])"), ("cat", "cat(bytes,bytes)"), ("narrow", "narrow(uint8[])"),
   ("copy", "copy(uint256[][])"), ("narrowAt", "narrowAt(uint8[],uint256)"),
   ("element", "element(uint256[][],uint256,uint256)"), ("enc", "enc(uint256[][])"),
   ("encIf", "encIf(uint256[][],uint256)"), ("reencode", "reencode(uint256[][3])"),
   ("order", "order(uint8[],uint256)"), ("shadow", "shadow(uint8[])"), ("sliceK", "sliceK(uint256[],uint256)"),
   ("add16", "add16(uint16,uint16)"), ("sx", "sx(int8,bool)"), ("v1arr", "v1arr(uint256[])"),
   ("bump", "bump()")].map fun (name, sig) =>
    { name, sourceSignature := sig, tag := .diamond, params := [], status := .elaborated, reason := "" }

private def words (xs : List Nat) : List Nat := (xs.flatMap Semantics.wordBytes).map UInt8.toNat
private def neg (n : Nat) : Nat := 2 ^ 256 - n

private def vector (sig : String) (inputs : List String) (data expected : List Nat)
    (failure := false) : Json := Json.mkObj [
  ("signature", toJson sig), ("inputTypes", toJson inputs), ("outputTypes", toJson ["uint256"]),
  ("calldata", toJson data), ("expectedBytes", toJson expected), ("failure", toJson failure)]

private def check (vectors : List Json) (status : String) (count : Nat) (reason : Option String := none) :
    IO Unit := do
  let report := replay C rows (Json.mkObj [("vectors", toJson vectors)])
  unless (report.getObjValAs? String "status").toOption == some status &&
      ((report.getObjValAs? (Array Json) "observed").toOption.map Array.size) == some count &&
      (reason.all fun r => (report.getObjValAs? String "reason").toOption == some r) do
    throw (IO.userError report.pretty)

private def arr := ["uint256[][]"]

-- Overlapping inner arrays (calldata), out-of-order tails (memory), trailing
-- data and overlapping `bytes`: each body runs once on the decoded value.
#eval check [
  vector "outer(uint256[][])" arr (words [0x20, 2, 0x40, 0x40, 1, 23]) (words [2]),
  vector "inner(uint256[][],uint256)" (arr ++ ["uint256"]) (words [0x40, 1, 2, 0x40, 0x40, 1, 23]) (words [1]),
  vector "mem(uint256[][])" arr (words [0x20, 2, 0x80, 0x40, 1, 23, 0]) (words [2]),
  vector "outer(uint256[][])" arr (words [0x20, 0, 7, 7]) (words [0]),
  vector "cat(bytes,bytes)" ["bytes", "bytes"] (words [0x40, 0x40, 2, 0x6162 * 2 ^ 240]) (words [4]),
  vector "bump()" [] [] (words [11])] "working" 6

-- A negative relative offset (solc: `x[0]` is the outer length word): a body
-- that only reads `x[i].length` sees the lazy value, as solc returns 1.
#eval check [
  vector "inner(uint256[][],uint256)" (arr ++ ["uint256"]) (words [0x40, 0, 1, neg 32]) (words [1]),
  vector "bump()" [] [] (words [7])] "working" 2

-- Entry failures: empty reverts before the body, the counter write rolled back.
#eval check [
  vector "outer(uint256[][])" arr (words [2 ^ 64, 0]) [] true,
  vector "outer(uint256[][])" arr (words [0x40, 0]) [] true,
  vector "outer(uint256[][])" arr (words [0x20, 2, 0x40]) [] true,
  vector "mem(uint256[][])" arr (words [0x20, 1, 0x1000]) [] true,
  vector "mem(uint256[][])" arr (words [0x20, 1, neg 32]) [] true,
  vector "narrow(uint8[])" ["uint8[]"] (words [0x20, 2]) [] true,
  vector "bump()" [] [] (words [6])] "working" 7

-- A wrong expectation stays broken: certified reverts cannot become passes.
#eval check [vector "outer(uint256[][])" arr (words [0x40, 0]) (words [0])] "broken" 1

-- Access-time calldata (lane FU2-C, `Semantics/AbiAccess.lean`): an element
-- that fails only when read. Not read: the body runs (solc returns 1, the
-- `LazyEntry` probes "not accessed"). Read, indexed or encoded: an empty revert
-- at that read with the counter write rolled back; the other elements read
-- (`AccessEntry` probes `encAt`, `encIf`, `enc8`; `LazyEntry` "narrowAt").
#eval check [
  vector "outer(uint256[][])" arr (words [0x20, 1, 0x1000]) (words [1]),
  vector "narrow(uint8[])" ["uint8[]"] (words [0x20, 1, 0x100]) (words [1]),
  vector "inner(uint256[][],uint256)" (arr ++ ["uint256"]) (words [0x40, 0, 1, 0x1000]) [] true,
  vector "narrowAt(uint8[],uint256)" ["uint8[]", "uint256"] (words [0x40, 1, 2, 0x100, 7]) (words [7]),
  vector "narrowAt(uint8[],uint256)" ["uint8[]", "uint256"] (words [0x40, 0, 2, 0x100, 7]) [] true,
  vector "element(uint256[][],uint256,uint256)" (arr ++ ["uint256", "uint256"])
    (words [0x60, 0, 0, 2, 0x40, 0x1000, 1, 9]) (words [9]),
  vector "element(uint256[][],uint256,uint256)" (arr ++ ["uint256", "uint256"])
    (words [0x60, 1, 0, 2, 0x40, 0x1000, 1, 9]) [] true,
  vector "enc(uint256[][])" arr (words [0x20, 1, 0x1000]) [] true,
  vector "enc(uint256[][])" arr (words [0x20, 1, 0x20, 2 ^ 64]) [] true,
  vector "enc(uint256[][])" arr (words [0x20, 1, neg 32]) (words [0xa0]),
  vector "encIf(uint256[][],uint256)" (arr ++ ["uint256"]) (words [0x40, 0, 1, 0x1000]) (words [7]),
  vector "encIf(uint256[][],uint256)" (arr ++ ["uint256"]) (words [0x40, 1, 1, 0x1000]) [] true,
  vector "bump()" [] [] (words [12])] "working" 13
-- `calldata_nested_array_static_reencode_v2.sol`'s `f(uint256[][3])`: the
-- statement `abi.encode(a);` reads every inner array; the two short vectors
-- revert there (counter rolled back), the complete one runs.
private def vec0 (sig : String) (inputs : List String) (data : List Nat) (failure : Bool) : Json :=
  Json.mkObj [("signature", toJson sig), ("inputTypes", toJson inputs),
    ("outputTypes", toJson ([] : List String)), ("calldata", toJson data),
    ("expectedBytes", toJson ([] : List Nat)), ("failure", toJson failure)]
#eval check [
  vec0 "reencode(uint256[][3])" ["uint256[][3]"] (words [0x20, 0x60, 0x60, 0x60, 3, 1]) true,
  vec0 "reencode(uint256[][3])" ["uint256[][3]"] (words [0x20, 0x60, 0x60, 0x60, 3, 1, 2]) true,
  vec0 "reencode(uint256[][3])" ["uint256[][3]"] (words [0x20, 0x60, 0x60, 0x60, 3, 1, 2, 3]) false,
  vector "bump()" [] [] (words [7])] "working" 4

-- The guard sits where solc reads: `x[0] + 1 / k` with `k = 0` and a dirty
-- `x[0]` is `Panic(0x12)` in legacy (right operand first) and an empty revert
-- under via-IR (left first), as pinned solc (`AccessEntry` probe `order`).
private def panic12 : List Nat := (Semantics.encodePanic 0x12).map UInt8.toNat
#eval check [vector "order(uint8[],uint256)" ["uint8[]", "uint256"] (words [0x40, 0, 1, 0x100]) panic12 true,
  vector "order(uint8[],uint256)" ["uint8[]", "uint256"] (words [0x40, 1, 1, 0x100]) [] true] "working" 2
#eval (do
  let report := replay { C with evalOrder := EvalOrder.viaIR } rows (Json.mkObj [("vectors", toJson [
    vector "order(uint8[],uint256)" ["uint8[]", "uint256"] (words [0x40, 0, 1, 0x100]) [] true])])
  unless (report.getObjValAs? String "status").toOption == some "working" do
    throw (IO.userError report.pretty) : IO Unit)

-- A slice read whose index another operand reassigns (round-2 skeptic,
-- pinned solc): `t[k] + (k = 5)` with `t = [100, 200, 300]`, `k = 1` reads
-- `t[5]` (`Panic(0x32)`) in legacy (right operand first) and returns
-- `200 + 5` under via-IR; the view's check and read see the same `k`.
private def panic32 : List Nat := (Semantics.encodePanic 0x32).map UInt8.toNat
#eval check [vector "sliceK(uint256[],uint256)" ["uint256[]", "uint256"]
  (words [0x40, 1, 3, 100, 200, 300]) panic32 true] "working" 1
#eval (do
  let report := replay { C with evalOrder := EvalOrder.viaIR } rows (Json.mkObj [("vectors", toJson [
    vector "sliceK(uint256[],uint256)" ["uint256[]", "uint256"] (words [0x40, 1, 3, 100, 200, 300]) (words [205])])])
  unless (report.getObjValAs? String "status").toOption == some "working" do
    throw (IO.userError report.pretty) : IO Unit)

-- A local shadowing the parameter (legal in solc, a warning) is not
-- guarded by name: the body is not admitted for access-time reads.
#eval check [vector "shadow(uint8[])" ["uint8[]"] (words [0x20, 1, 0x100]) (words [0])] "blocked" 0
  (some "calldata element fails only on access: needs access-time calldata semantics")

-- ABI coder v1 (`canonicalOnly`) cleans value words (`UpstreamEntry.v1Plan`;
-- `checked_add_v1.sol` and the `V1Entry` probes): 65536 reads as 0, an
-- `int8` word `0x1ff` as -1, a `bool` word 2 as true; short calldata
-- reverts; a reference parameter keeps the byte-identical gate.
private def v1 (sig : String) (inputs outputs : List String) (data expected : List Nat)
    (failure := false) : Json := Json.mkObj [
  ("signature", toJson sig), ("inputTypes", toJson inputs), ("outputTypes", toJson outputs),
  ("calldata", toJson data), ("expectedBytes", toJson expected), ("failure", toJson failure),
  ("canonicalOnly", toJson true)]
#eval check [
  v1 "add16(uint16,uint16)" ["uint16", "uint16"] ["uint16"] (words [65536, 0]) (words [0]),
  v1 "add16(uint16,uint16)" ["uint16", "uint16"] ["uint16"] (words [65534, 0]) (words [65534]),
  v1 "add16(uint16,uint16)" ["uint16", "uint16"] ["uint16"] (words [65535, 1])
    ((Semantics.encodePanic 0x11).map UInt8.toNat) true,
  v1 "add16(uint16,uint16)" ["uint16", "uint16"] ["uint16"] ((words [1, 2]).take 63) [] true,
  v1 "sx(int8,bool)" ["int8", "bool"] ["int256"] (words [0x1ff, 2]) (words [neg 1]),
  v1 "sx(int8,bool)" ["int8", "bool"] ["int256"] (words [0x7f, 0, 9]) (words [0])] "working" 6
#eval check [v1 "v1arr(uint256[])" ["uint256[]"] ["uint256"] (words [0x40, 0, 0]) (words [0])] "blocked" 0
  (some "noncanonical calldata requires lazy ABI decoder replay")

-- The replay checks the guarded outcome: a wrong expectation is broken.
#eval check [vector "enc(uint256[][])" arr (words [0x20, 1, 0x1000]) (words [0x60])] "broken" 1

-- Copies keep the lazy-only refusal (solc copies with the eager rules).
#eval check [vector "copy(uint256[][])" arr (words [0x20, 1, neg 32]) (words [1])]
  "blocked" 0
  (some "calldata layout accepted by lazy access but rejected by an eager copy needs calldata references in the source semantics")
#eval check [vector "mem(uint256[][])" arr (words [0x20, 2 ^ 64]) [] true] "blocked" 0
  (some "possible Panic(0x41) allocation failure in memory decoding")

private def drows : List ImportRow :=
  [("sc", "sc((uint256,uint256[]))"), ("sm", "sm((uint256,uint256[]))"), ("bump", "bump()")].map
    fun (name, sig) =>
    { name, sourceSignature := sig, tag := .diamond, params := [], status := .elaborated, reason := "" }

private def dcheck (vectors : List Json) (status : String) (count : Nat) : IO Unit := do
  let report := replay D drows (Json.mkObj [("vectors", toJson vectors)])
  unless (report.getObjValAs? String "status").toOption == some status &&
      ((report.getObjValAs? (Array Json) "observed").toOption.map Array.size) == some count do
    throw (IO.userError report.pretty)

private def st := ["(uint256,uint256[])"]

-- Nested struct with a dynamic member: an out-of-order member tail and a member
-- array overlapping the struct head are accepted (calldata and memory); a member
-- offset past the data reverts at entry in memory and stays a named lazy
-- refusal in calldata (solc: accepted until `s.b` is read).
#eval dcheck [
  vector "sc((uint256,uint256[]))" st (words [0x20, 5, 0x60, 9, 2, 3, 4]) (words [7]),
  vector "sm((uint256,uint256[]))" st (words [0x20, 5, 0x60, 9, 2, 3, 4]) (words [7]),
  vector "sc((uint256,uint256[]))" st (words [0x20, 1, 0]) (words [2]),
  vector "sm((uint256,uint256[]))" st (words [0x20, 5, 0x1000]) [] true,
  vector "sc((uint256,uint256[]))" st (words [0x20, 5]) [] true,
  vector "bump()" [] [] (words [9])] "working" 6
#eval dcheck [vector "sc((uint256,uint256[]))" st (words [0x20, 5, 0x1000]) (words [5])] "blocked" 0

end AbiEntryReplay
