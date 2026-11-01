import Solidity.Yul.Composition.PhysicalControls
import Solidity.Yul.Composition.PhysicalMemory

/-! Executable actual producer/consumer projections, not a source interpreter
or a compiler correctness certificate. None remains null and fails validation. -/
open Lean
open Solidity.Yul.Views
open Solidity.Yul.Views.Controls
open Solidity.Yul.Composition
open Solidity.Yul.Composition.PhysicalControls

def logicalTruth (s : Solidity.Source.EMState originEnv []) : Option Bool :=
  match (s.2.ex.world.accounts account).storage.read (originPath "c") with
  | some (.bool b) => some b
  | _ => none

def main : IO Unit := do
  let innerEncoding := boolEncodingRollback ownedOriginRun.2.journal.length childRun.2
  let innerRaw := reencodePersistentSlot (representedBanks originRegistry false innerEncoding) revertedChild account 43
  let outerRaw := reencodePersistentSlot (representedBanks originRegistry false restoredEncoding) revertedOuter account 43
  let staleOwned := reencodePersistentSlot (representedBanks originRegistry false childRun.2) revertedChild account 43
  let stalePadding := reencodePersistentSlot (representedBanks originRegistry false ownedOriginRun.2)
    ⟨revertedChild.source,childRun.1.2⟩ account 43
  let staticRun := representedSourceStep originRegistry originTempRegistry childRequest ownedOriginRun.2
    {packedStepFrame with static := true} childPlan ownedOriginRun.1.1.2 ownedOriginRun.1.2
  let staticRaw := reencodePersistentSlot (representedBanks originRegistry false staticRun.2)
    ⟨staticRun.1.1.2.2.ex,staticRun.1.2⟩ account 43
  let staticTag := match staticRun.1.1.1 with
    | .error (.revert []) => "revert"
    | _ => "unexpected-source-result"
  let allocations := ([0,1,32,64] : List (Fin 65)).map fun gap =>
    let placement := placementShift gap
    let view := (PhysicalMemoryControls.image gap).encode (PhysicalMemoryControls.reservedView gap) (placement.address 0)
    Json.mkObj [("address",toJson (placement.address 0)),("free",toJson placement.free.val),
      ("payload",toJson ((readBytes view (placement.address 0+32) 1).map UInt8.toNat))]
  IO.println (Json.mkObj [("schema",toJson (1 : Nat)),("staticRaw",toJson (staticRaw.map Fin.val)),("staticTag",toJson staticTag),
    ("firstTruth",toJson (logicalTruth ownedOriginRun.1.1.2)),("childTruth",toJson (logicalTruth childRun.1.1.2)),
    ("firstRaw",toJson (firstRaw.map Fin.val)),("childRaw",toJson (childRaw.map Fin.val)),
    ("innerRaw",toJson (innerRaw.map Fin.val)),("outerRaw",toJson (outerRaw.map Fin.val)),
    ("staleOwnedRaw",toJson (staleOwned.map Fin.val)),("stalePaddingRaw",toJson (stalePadding.map Fin.val)),
    ("copied",toJson (copiedBytes.map (List.map UInt8.toNat))),
    ("allocations",toJson allocations)]).compress
