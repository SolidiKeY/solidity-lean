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
  function bump() returns (uint) { counter++; return counter; }
}

private def rows : List ImportRow :=
  [("outer", "outer(uint256[][])"), ("inner", "inner(uint256[][],uint256)"),
   ("mem", "mem(uint256[][])"), ("cat", "cat(bytes,bytes)"), ("narrow", "narrow(uint8[])"),
   ("copy", "copy(uint256[][])"),
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

-- Lazy-only layouts stay blocked by name, before any observation.
#eval check [vector "outer(uint256[][])" arr (words [0x20, 1, 0x1000]) (words [1])] "blocked" 0
  (some "calldata element fails only on access: needs access-time calldata semantics")
#eval check [vector "narrow(uint8[])" ["uint8[]"] (words [0x20, 1, 0x100]) (words [1])] "blocked" 0
  (some "calldata element fails only on access: needs access-time calldata semantics")
#eval check [vector "copy(uint256[][])" arr (words [0x20, 1, neg 32]) (words [1])]
  "blocked" 0
  (some "calldata layout accepted by lazy access but rejected by an eager copy needs calldata references in the source semantics")
#eval check [vector "mem(uint256[][])" arr (words [0x20, 2 ^ 64]) [] true] "blocked" 0
  (some "possible Panic(0x41) allocation failure in memory decoding")

end AbiEntryReplay
