import Solidity.Semantics.AbiAccess

/-!
# Access-time calldata: controls against pinned solc

Kernel-evaluated controls (`decide`) of the recording reader `cpart`, the
path access `cat` and `verdictA`, on vectors whose outcomes pinned solc
0.8.38 produced identically in legacy and via-IR, optimizer off and on
(`tests/abi-0.8.38/AccessEntry.sol`, `scripts/abi-entry-probe.mjs --access`,
and `calldata_nested_array_static_reencode_v2.sol`). Each control states
both outcomes: an access the recorded paths cover reverts, one they do not
cover is read.
-/

namespace Solidity.AbiEntry.AccessChecks
open Solidity.AbiEntry

/-- Calldata: a selector (not read here) and argument words. -/
def cd (ws : List Nat) : Input :=
  { data := [0, 0, 0, 0] ++ ws.flatMap (fun w => wordBytes (w % W)), free := 2 ^ 32 }

def u256 : Shape := .word (.uint 256)
def u8 : Shape := .word (.uint 8)
def neg (n : Nat) : Nat := W - n

/-- The recorded paths of the parameter whose reference `cref` enters at
head position 0 (`none`: the entry check fails or the reader errs). -/
def fails (I : Input) (s : Shape) : Option (List Path) :=
  match cref I s 4 0 with
  | .ok (addr, len) => match cpart I 64 s addr len with
    | .ok (_, ps) => some ps
    | .error _ => none
  | .error _ => none

/-- One access along `π` of that parameter: `"revert"`, `"ok"` or another
failure. -/
def access (I : Input) (s : Shape) (π : Path) : String :=
  match cref I s 4 0 with
  | .ok (addr, len) => match cat I 64 s addr len π with
    | .ok () => "ok"
    | .error .revert => "revert"
    | .error _ => "other"
  | .error _ => "entry"

/-- The verdict with every calldata parameter read at access time. -/
def observe (I : Input) (ps : List Param) : String × List (List Path) :=
  match verdictA I 64 (fun _ => true) ps with
  | .revert => ("revert", [])
  | .run _ fs => ("run", fs)
  | .blocked r => (r, [])

def arr2 : Shape := .array (.array u256)
def fix3 : Shape := .fixed (.array u256) 3

/-! `uint256[][]`: an inner offset out of range (`enc` probe: `abi.encode`
reverts; `encIf` with `i == 0`: not read, returns). -/

example : fails (cd [0x20, 1, 0x1000]) arr2 = some [[0]] := by decide +kernel
example : access (cd [0x20, 1, 0x1000]) arr2 [] = "ok" := by decide +kernel
example : access (cd [0x20, 1, 0x1000]) arr2 [0] = "revert" := by decide +kernel
example : access (cd [0x20, 1, 0x1000]) arr2 [0, 0] = "revert" := by decide +kernel
example : observe (cd [0x20, 1, 0x1000]) [{ shape := arr2, loc := .calldata }] =
    ("run", [[[0]]]) := by decide +kernel

/-! Two inner arrays, the second's offset out of range (`encAt`): `x[0]`
reads, `x[1]` reverts. -/

example : fails (cd [0x40, 1, 2, 0x40, 0x1000, 1, 9]) arr2 = some [[1]] := by decide +kernel
example : access (cd [0x40, 1, 2, 0x40, 0x1000, 1, 9]) arr2 [0, 0] = "ok" := by decide +kernel
example : access (cd [0x40, 1, 2, 0x40, 0x1000, 1, 9]) arr2 [1] = "revert" := by decide +kernel

/-! An inner length of `2^64` (`enc` probe: an empty revert, not a panic). -/

example : fails (cd [0x20, 1, 0x20, 2 ^ 64]) arr2 = some [[0]] := by decide +kernel

/-! A negative relative offset is read lazily (`enc` probe: `abi.encode`
succeeds): nothing is recorded. -/

example : fails (cd [0x20, 1, neg 32]) arr2 = some [] := by decide +kernel
example : observe (cd [0x20, 1, neg 32]) [{ shape := arr2, loc := .calldata }] =
    ("run", [[]]) := by decide +kernel

/-! A dirty `uint8` word (`enc8` probe): recorded at its element; the length
reads. -/

example : fails (cd [0x20, 2, 1, 0x100]) (.array u8) = some [[1]] := by decide +kernel
example : access (cd [0x20, 2, 1, 0x100]) (.array u8) [0] = "ok" := by decide +kernel
example : access (cd [0x20, 2, 1, 0x100]) (.array u8) [1] = "revert" := by decide +kernel
example : access (cd [0x20, 2, 1, 0x100]) (.array u8) [] = "ok" := by decide +kernel

/-! `calldata_nested_array_static_reencode_v2.sol`, `f(uint256[][3])`: the
inner arrays' elements past the calldata fail on access, so `abi.encode(a)`
reverts for the two short vectors and succeeds for the complete one. -/

example : fails (cd [0x20, 0x60, 0x60, 0x60, 3, 1]) fix3 = some [[0], [1], [2]] := by decide +kernel
example : fails (cd [0x20, 0x60, 0x60, 0x60, 3, 1, 2]) fix3 = some [[0], [1], [2]] := by decide +kernel
example : fails (cd [0x20, 0x60, 0x60, 0x60, 3, 1, 2, 3]) fix3 = some [] := by decide +kernel
example : observe (cd [0x20, 0x60, 0x60, 0x60, 3, 1]) [{ shape := fix3, loc := .calldata }] =
    ("run", [[[0], [1], [2]]]) := by decide +kernel

/-! Lazy-only layouts nested one level down (`enc8nL`, `encBL` probes): a
`-32` element offset of a `uint8[][]` reads the outer length's neighbour as
a `uint8` element, which is dirty, so encoding reverts; of a `bytes[]` it
reads bytes, never validated, so encoding succeeds. -/

example : fails (cd [0x20, 1, neg 32]) (.array (.array u8)) = some [[0, 0]] := by decide +kernel
example : fails (cd [0x20, 1, neg 32]) (.array .bytes) = some [] := by decide +kernel
-- `encPw`: the packed encoding of a whole dirty `uint8[]` reverts.
example : fails (cd [0x20, 2, 1, 0x100]) (.array u8) = some [[1]] := by decide +kernel
example : fails (cd [0x20, 2, 1, 0xff]) (.array u8) = some [] := by decide +kernel

/-! Without access-time reads the verdict is CF1's refusal (`verdictA_off`). -/

example : (match verdictA (cd [0x20, 1, 0x1000]) 64 (fun _ => false) [{ shape := arr2, loc := .calldata }] with
    | .blocked r => r | _ => "") =
    "calldata element fails only on access: needs access-time calldata semantics" := by
  decide +kernel

end Solidity.AbiEntry.AccessChecks
