import Lean
import Solidity.Storage.HashedKeccak
import Solidity.Storage.HashedLayout
import Solidity.Storage.HashedLayoutEvm
import Solidity.Storage.HashedSeparation
import Solidity.Storage.Representation.ArrayControls
import Solidity.Storage.Representation.Arrays
import Solidity.Storage.Representation.Controls
import Solidity.Storage.Representation.Frames
import Solidity.Storage.Representation.GraphCompatibility
import Solidity.Storage.Representation.GraphControls
import Solidity.Storage.Representation.GraphFrames
import Solidity.Storage.Representation.GraphLayout
import Solidity.Storage.Representation.GraphRepresentation
import Solidity.Storage.Representation.Members
import Solidity.Storage.Representation.Model
import Solidity.Storage.Representation.Reads
import Solidity.Storage.Representation.Transport
import Solidity.Storage.Representation.TransportControls
import Solidity.Storage.Representation.UpdateControls
import Solidity.Storage.Representation.Updates
import Solidity.Storage.Representation.Words

/-! Export exact closed kernel type syntax after removing expression metadata.
Hashing/sorting is external deterministic tooling, not a new proof assertion.
All generated constants are included, so compiler-generated API drift is visible.
-/
open Lean in
private def stripMetadata : Expr → Expr
  | .app f a => .app (stripMetadata f) (stripMetadata a)
  | .lam n t b bi => .lam n (stripMetadata t) (stripMetadata b) bi
  | .forallE n t b bi => .forallE n (stripMetadata t) (stripMetadata b) bi
  | .letE n t v b nd => .letE n (stripMetadata t) (stripMetadata v) (stripMetadata b) nd
  | .mdata _ b => stripMetadata b
  | .proj n i b => .proj n i (stripMetadata b)
  | e => e

open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let roots := env.constants.fold (init := #[]) fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some i => if (modules[i.toNat]!).toString.startsWith "Solidity.Storage." then
        acc.push (modules[i.toNat]!, n, ci) else acc
    | none => acc
  for (modName, n, ci) in roots do
    let row := Json.mkObj [("module", toJson modName.toString),
      ("name", toJson n.toString), ("levels", toJson (repr ci.levelParams).pretty),
      ("type", toJson (repr (stripMetadata ci.type)).pretty)]
    Lean.Elab.Command.liftIO <| IO.println ("STORAGE_API\t" ++ row.compress)
