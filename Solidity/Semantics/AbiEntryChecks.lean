import Solidity.Semantics.AbiEntry

/-!
# ABI entry decoding: controls against pinned solc

Each control replays one vector of `tests/abi-0.8.38/LazyEntry.vectors.json`
or of a retained Group 10 fixture, whose outcome pinned solc 0.8.38 produced
identically in legacy and via-IR, optimizer off and on
(`scripts/abi-entry-probe.mjs --probes`). The kernel evaluates the verdict
(`decide`): positive controls run the body on the expected value (its
canonical bytes), negative controls are certified empty reverts, and the
refusals keep their names.
-/

namespace Solidity.AbiEntry.Checks
open Solidity.AbiEntry

/-- Calldata: a selector (its bytes are not read here) and argument words. -/
def cd (ws : List Nat) (tail : List UInt8 := []) : Input :=
  { data := [0, 0, 0, 0] ++ ws.flatMap (fun w => wordBytes (w % W)) ++ tail, free := 2 ^ 32 }

def u256 : Shape := .word (.uint 256)
def u8 : Shape := .word (.uint 8)
def neg (n : Nat) : Nat := W - n

/-- The verdict, observed: `"revert"`, `"run"` with the canonical argument
bytes, or the refusal. -/
def observe (I : Input) (ps : List Param) : String × List UInt8 :=
  match verdict I 64 ps with
  | .revert => ("revert", [])
  | .run vs => ("run", encodeArgs vs)
  | .blocked r => (r, [])

def arr2 (loc : Loc) : List Param := [{ shape := .array (.array u256), loc }]
def lazyFail := "calldata element fails only on access: needs access-time calldata semantics"
def lazyOnly := "calldata layout accepted by lazy access but rejected by an eager copy needs calldata references in the source semantics"
def panic41 := "possible Panic(0x41) allocation failure in memory decoding"

/-! Calldata parameters (`CalldataNested`). -/

-- canonical: runs on its own bytes
example : observe (cd [0x20, 1, 0x20, 1, 23]) (arr2 .calldata) =
    ("run", ((cd [0x20, 1, 0x20, 1, 23]).data.drop 4)) := by decide +kernel
-- inner offset out of range: solc accepts unless accessed; refused by name
example : (observe (cd [0x20, 1, 0x1000]) (arr2 .calldata)).1 = lazyFail := by decide
-- negative relative offset: lazy access accepts, an eager copy reverts
example : (observe (cd [0x20, 1, neg 32]) (arr2 .calldata)).1 = lazyOnly := by decide
-- entry checks: outer offset 2^64, beyond data, length 2^64, region beyond data, short head
example : (observe (cd [2 ^ 64, 0]) (arr2 .calldata)).1 = "revert" := by decide
example : (observe (cd [0x40, 0]) (arr2 .calldata)).1 = "revert" := by decide
example : (observe (cd [0x20, 2 ^ 64]) (arr2 .calldata)).1 = "revert" := by decide
example : (observe (cd [0x20, 2, 0x40]) (arr2 .calldata)).1 = "revert" := by decide
example : (observe { data := [0, 0, 0, 0] ++ (wordBytes 0x20).take 31, free := 2 ^ 32 }
    (arr2 .calldata)).1 = "revert" := by decide
-- trailing data is not observed: the body runs on the canonical prefix
example : observe (cd [0x20, 0, 7, 7]) (arr2 .calldata) =
    ("run", (cd [0x20, 0]).data.drop 4) := by decide +kernel
-- overlapping inner arrays: accepted, the body sees both elements
example : observe (cd [0x20, 2, 0x40, 0x40, 1, 23]) (arr2 .calldata) =
    ("run", (cd [0x20, 2, 0x40, 0x80, 1, 23, 1, 23]).data.drop 4) := by decide +kernel
-- a dirty narrow element is validated on access only
example : (observe (cd [0x20, 1, 0x100]) [{ shape := .array u8, loc := .calldata }]).1 =
    lazyFail := by decide
-- unpadded bytes tail: accepted
example : observe (cd [0x20, 3] [0xab, 0xcd, 0xef]) [{ shape := .bytes, loc := .calldata }] =
    ("run", (cd [0x20, 3] ([0xab, 0xcd, 0xef] ++ List.replicate 29 0)).data.drop 4) := by decide
example : (observe (cd [0x20, 33, 1]) [{ shape := .bytes, loc := .calldata }]).1 = "revert" := by
  decide

/-! Memory parameters (`MemoryNested`): validated at entry. -/

example : (observe (cd [0x20, 1, 0x1000]) (arr2 .memory)).1 = "revert" := by decide
example : (observe (cd [0x20, 1, 0x20, 5]) (arr2 .memory)).1 = "revert" := by decide +kernel
example : (observe (cd [0x20, 1, neg 32]) (arr2 .memory)).1 = "revert" := by decide
example : (observe (cd [0x20, 1, 2 ^ 64]) (arr2 .memory)).1 = "revert" := by decide
example : (observe (cd [0x20, 2, 0x80, 0x40, 1, 23, 0]) (arr2 .memory)) =
    ("run", (cd [0x20, 2, 0x40, 0x60, 0, 1, 23]).data.drop 4) := by decide +kernel
example : (observe (cd [0x20, 1, 0x100]) [{ shape := .array u8, loc := .memory }]).1 =
    "revert" := by decide
-- dirty bytes padding is not checked
example : (observe (cd [0x20, 3, 0xabcdef * 2 ^ 232 + 0xff]) [{ shape := .bytes, loc := .memory }]).1 =
    "run" := by decide
example : (observe (cd [0x20, 33, 1]) [{ shape := .bytes, loc := .memory }]).1 = "revert" := by
  decide
-- solc: Panic(0x41) for 2^64 - 1 and 2^64; an empty revert for 2^32 (refused only where unsure)
example : (observe (cd [0x20, 2 ^ 64 - 1]) [{ shape := .bytes, loc := .memory }]).1 = panic41 := by
  decide
example : (observe (cd [0x20, 2 ^ 64]) [{ shape := .bytes, loc := .memory }]).1 = panic41 := by
  decide
example : (observe (cd [0x20, 2 ^ 32]) [{ shape := .bytes, loc := .memory }]).1 = "revert" := by
  decide
example : (observe (cd [0x20, 2 ^ 64]) (arr2 .memory)).1 = panic41 := by decide
-- the first failing parameter decides, whatever follows
example : (observe (cd [0x40, 0x100, 0]) [{ shape := .bytes, loc := .memory },
    { shape := u8, loc := .value }]).1 = "revert" := by decide
example : (observe (cd [0x1000, 1]) [{ shape := .bytes, loc := .memory },
    { shape := u8, loc := .value }]).1 = "revert" := by decide

/-! Calldata structs and static arrays (`CalldataStruct`, `CalldataStatic`). -/

def S : Shape := .tuple [u256, .array u256]
example : (observe (cd [0x20, 5, 0x40, 0]) [{ shape := S, loc := .calldata }]).1 = "run" := by
  decide +kernel
example : (observe (cd [0x20, 5, 0x1000]) [{ shape := S, loc := .calldata }]).1 = lazyFail := by
  decide
example : (observe (cd [0x20, 5]) [{ shape := S, loc := .calldata }]).1 = "revert" := by decide
example : (observe (cd [2 ^ 64]) [{ shape := S, loc := .calldata }]).1 = "revert" := by decide
example : (observe (cd [0x20, 5, 0x1000]) [{ shape := S, loc := .memory }]).1 = "revert" := by
  decide
example : (observe (cd [1, 2, 3]) [{ shape := .fixed (.fixed u256 2) 2, loc := .calldata }]).1 =
    "revert" := by decide
example : (observe (cd [0x100, 0]) [{ shape := .fixed u8 2, loc := .calldata }]).1 = lazyFail := by
  decide

/-! Retained Group 10 vectors. -/

-- calldata_array_length_v2: `f(uint256[][]): 0x20, 1, -32 -> 1, 1, 0` is lazy-only
example : (observe (cd [0x20, 1, neg 32]) (arr2 .calldata)).1 = lazyOnly := by decide
example : (observe (cd [0x20, 2, 0xA0, 0x40, 2, 23, 42, 0]) (arr2 .calldata)).1 = "run" := by
  decide +kernel
-- array_exceeds_calldatasize_no_revert_string: `f(uint256[]): 0x20, 1 -> FAILURE`
example : (observe (cd [0x20, 1]) [{ shape := .array u256, loc := .calldata }]).1 = "revert" := by
  decide
-- bytes_concat_nested: three overlapping `bytes memory`
example : (observe (cd [0x60, 0x60, 0x60, 2] ([0x61, 0x62] ++ List.replicate 30 0))
    [{ shape := .bytes, loc := .memory }, { shape := .bytes, loc := .memory },
     { shape := .bytes, loc := .memory }]).1 = "run" := by decide +kernel

end Solidity.AbiEntry.Checks
