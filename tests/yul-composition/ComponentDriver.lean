import Solidity.Yul.Composition.Controls
import Solidity.Yul.Composition.TargetRepeat
import Solidity.Yul.Composition.ScopeTransport
import Solidity.Yul.Composition.WordBridge

/-! Executable projections of actual checked components. External comparisons
are finite differential evidence, not proofs of solc/source correspondence. -/
open Lean
open Solidity.Yul.Composition
open Solidity.Yul.Composition.Controls

def main : IO Unit := do
  let word := (Solidity.Backend.Scalar.run (literalSum 250 9).code [99]).map
    (fun xs => xs.map BitVec.toNat)
  let repeated :=  (Solidity.Backend.Scalar.run (repeatIncrement 3) [250,99]).map
    (fun xs => xs.map BitVec.toNat)
  let scope := (Solidity.Backend.Scalar.run
    (computedOuterWrite #v[42] (n := 2) ⟨1, by decide⟩ (by decide) 250 9) [7,8,99]).map
    (fun xs => xs.map BitVec.toNat)
  let code := Solidity.Backend.encode (literalSum 250 9).code |>.map UInt8.toNat
  let value := Lean.Json.mkObj [("schema", toJson (1 : Nat)), ("rawWord", toJson (worldWord (targetWord ⟨511, by decide⟩)).val),
    ("word", toJson word), ("scope", toJson scope), ("repeat", toJson repeated), ("code", toJson code),
    ("revert", toJson (summary revertedCopy)), ("success", toJson (summary successfulCopy))]
  IO.println value.compress
