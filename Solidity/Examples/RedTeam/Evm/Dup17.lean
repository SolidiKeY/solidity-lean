import Solidity.Evm.Examples

/-!
# Red team: the compiler emits `DUP17`, which is not an EVM opcode

Claim: `rows.push(one);` with `uint[16] one; uint[16][] rows;` is inside the
verified fragment (`inFragP`), and its compiled code contains `Instr.dup 17`.
The EVM has `DUP1`..`DUP16` only (Yellow Paper, Appendix H.2, `0x80`..`0x8f`;
`Backend.Op.DUP (n : Fin 16)` in `Backend/Opcode.lean`), so this instruction
list has no bytecode; solc compiles the same source with a copy loop. The
abstract machine nevertheless runs it to success, so `Evm/Correct.lean`'s
simulation theorems hold of a program no EVM can execute. No theorem is false:
this is a gap between the instruction model and the reference.

Culprit: `Solidity/Evm/Compile.lean:384` (`pushCode`, `.dup (leaves.length + 1)`),
admitted by `pushIn` (`Solidity/Evm/Compile.lean:168`, no bound on the leaves),
and `Solidity/Evm/Machine.lean:490`/`494` (`Instr.step` runs `.dup n`/`.swap n`
for every `n ≥ 1`).

Suggested fix: make `pushIn` require `(leaves (.ref R)).length < 16` (or index
`Instr.dup`/`Instr.swap` by `Fin 16`, as `Backend.Op` does), so a wider static
copy is refused instead of compiled.
-/

namespace Solidity.Examples.RedTeam.Evm.Dup17

open Solidity Solidity.Evm Solidity.Evm.Examples

/-- Sixteen words to copy into a new array element. -/
def Wide : Contract := contract!{ uint[16] one; uint[16][] rows; }

local instance : InContract := ⟨Wide⟩

def pushWide := (sol{ rows.push(one); } : Prog Wide [] _)

/-- A `DUPn` or `SWAPn` beyond the EVM's sixteen. -/
def beyond16 : Instr → Bool
  | .dup n | .swap n => decide (16 < n)
  | _ => false

/-- The program is in the fragment the compiler theorems cover. -/
theorem pushWide_frag : (inFragP (Frag.init []) pushWide).isSome = true := by
  decide +kernel

/-- Its code holds an instruction with no opcode: `DUP17`. -/
theorem pushWide_dup17 :
    ((compileProg 0 pushWide).filter beyond16).map toString = ["DUP17"] := by
  decide +kernel

/-- The model runs it: `rows.length` (slot `16`) is `1` afterwards. -/
theorem pushWide_runs :
    storeAt (run (compileProg 0 pushWide) fresh) (rootSlot Wide "rows") = some 1 := by
  decide +kernel

end Solidity.Examples.RedTeam.Evm.Dup17
