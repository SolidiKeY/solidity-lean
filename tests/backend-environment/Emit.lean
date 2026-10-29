import Solidity.Backend.Environment.CryptoChecks
import Lean.Data.Json

open Solidity Solidity.Backend Solidity.Backend.Environment

-- Compiler-generated vector input, not a proof shortcut.
def vectorPrograms : List (String × List Instr) :=
  [("environment", [EnvKey.msgSender, .msgValue, .timestamp, .selfBalance, .selfAddress].map select),
   ("balance-high", [push256 ⟨2 ^ 160 + 7, by decide⟩, .op .BALANCE]),
   ("selector", [selectorCode ⟨0x12345678, by decide⟩]),
   ("selector-abi", [selectorAbiCode ⟨0x12345678, by decide⟩]),
   ("keccak", materialize 7 [0, 255, 0, 97] ++ keccakCode ⟨7, by decide⟩ ⟨4, by decide⟩),
   ("namespace", materialize 7 [0, 255, 0, 97] ++ namespaceCode ⟨7, by decide⟩ ⟨4, by decide⟩ ⟨64, by decide⟩),
   ("sha256", materialize 7 [97, 98, 99] ++ builtinCode .sha256 ⟨7, by decide⟩ ⟨3, by decide⟩ ⟨192, by decide⟩),
   ("ripemd160", materialize 7 [97, 98, 99] ++ builtinCode .ripemd160 ⟨7, by decide⟩ ⟨3, by decide⟩ ⟨192, by decide⟩),
   ("ecrecover", builtinCode .ecrecover ⟨0, by decide⟩ ⟨128, by decide⟩ ⟨192, by decide⟩),
   ("ecrecover-valid", materialize 0 (Precompiles.ofHex
     "c4179c5a26cda29e689fe027ee5f5e4e085b30ad136bcc4808cf982380607110000000000000000000000000000000000000000000000000000000000000001b60a33eea03a29c01e5bf251d76ed7bd817e46666faa8ea703d95b7648da367576136d40d487f83644b470554781141106cefbdf3324e63a49b1ef6c49e2368de") ++
     builtinCode .ecrecover ⟨0, by decide⟩ ⟨128, by decide⟩ ⟨192, by decide⟩),
   ("ecrecover-malformed", builtinCode .ecrecover ⟨0, by decide⟩ ⟨4, by decide⟩ ⟨192, by decide⟩),
   ("utf8-name", nameCode "Aλ" 5)]

#eval IO.println <| Lean.Json.compress <| Lean.toJson <|
  vectorPrograms.map fun (name, code) => (name, (Backend.encode code).map UInt8.toNat)
