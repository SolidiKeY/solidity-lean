import Lean.Data.Json
import Solidity.Backend.Creation.ExecutionChecks
import Solidity.Backend.Creation.PlacementChecks
import Solidity.Backend.Creation.LinkingChecks
import Solidity.Backend.Creation.ImmutableChecks
import Solidity.Backend.Creation.ConstructorChecks

open Solidity.Backend Solidity.Backend.Creation
private def hexDigit (n : Nat) : Char := Char.ofNat (if n < 10 then 48 + n else 87 + n)
private def hexBytes (bytes : List UInt8) : String :=
  "0x" ++ String.mk (bytes.flatMap (fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]))
private def emit (name : String) (code expected : List UInt8) (reverts : Bool := false) : IO Unit :=
  IO.println (Lean.Json.mkObj [("name", .str name), ("payload", .str (hexBytes code)),
    ("expected", .str (hexBytes expected)), ("reverts", .bool reverts)]).compress

#eval emit "sample-args" sample.payload sample.runtime
#eval emit "empty-args" emptyWithArgs.payload []
#eval emit "word31" (boundary ⟨31, by decide⟩).payload (boundary ⟨31, by decide⟩).runtime
#eval emit "word32" (boundary ⟨32, by decide⟩).payload (boundary ⟨32, by decide⟩).runtime
#eval emit "word33" (boundary ⟨33, by decide⟩).payload (boundary ⟨33, by decide⟩).runtime
#eval emit "length255" (boundary ⟨255, by decide⟩).payload (boundary ⟨255, by decide⟩).runtime
#eval emit "length256" (boundary ⟨256, by decide⟩).payload (boundary ⟨256, by decide⟩).runtime
#eval emit "offset255" (List.replicate 245 0x5b ++ encode (placedWrapper placement255.lengthWord placement255.offsetWord) ++ [0x60, 0x2a, 0] ++ [0xaa]) [0x60, 0x2a, 0]
#eval emit "offset257" (List.replicate 246 0x5b ++ encode (placedWrapper placement257.lengthWord placement257.offsetWord) ++ [0x60, 0x2a, 0] ++ [0xbb]) [0x60, 0x2a, 0]
#eval emit "linked" (linkedArtifact libraryArtifact libraryTable libraryAddress).payload (linkedArtifact libraryArtifact libraryTable libraryAddress).runtime
#eval emit "immutable" (patchedArtifact immutableArtifact immutableTable).payload (patchedArtifact immutableArtifact immutableTable).runtime
#eval emit "combined" (combinedArtifact mixedArtifact mixedLinks mixedTable (fun _ => Vector.replicate 20 0x55) (by decide)).payload (combinedArtifact mixedArtifact mixedLinks mixedTable (fun _ => Vector.replicate 20 0x55) (by decide)).runtime
#eval emit "constructor-return" (encode copyPrefix ++ encode (exitWrapper true ⟨3, by decide⟩ ⟨16, by decide⟩) ++ [0x60, 0x2a, 0] ++ [0xaa]) [0x60, 0x2a, 0]
#eval emit "constructor-revert" (encode copyPrefix ++ encode (exitWrapper false ⟨3, by decide⟩ ⟨16, by decide⟩) ++ [0xde, 0xad, 0xbe] ++ [0xaa]) [0xde, 0xad, 0xbe] true
#eval emit "wrong-source" wrongSource [0x2a, 0, 0xaa]
#eval emit "wrong-return-range" [0x60, 3, 0x60, 10, 0x5f, 0x39, 0x60, 2, 0x5f, 0xf3, 0x60, 0x2a, 0, 0xaa] [0x60, 0x2a]
