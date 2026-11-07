import SignatureEnvironment
import MetadataFingerprintV2
import Solidity.Scope

/-!
Guards metadata-refused types being erased or silently promoted to legacy signatures.
Enumerates visible constants and direct ranges for the freshly compiled,
unchanged Scope module. KeySort and AST are freshly compiled dependencies; their
constants are not enumerated by this probe. Unsupported types and absent ranges remain rows.
No parent-range fallback, ownership, body-equivalence or global coverage claim.
-/

open Lean Elab Command

#h62_environment

run_cmd do
  let env ← getEnv
  let target := (Name.mkSimple "Solidity").str "Scope"
  let mut signatures : Array Json := #[]
  let mut locations : Array Json := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[idx.toNat]! == target do continue
    let kind := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let legacy := match H62Signature.fingerprint info with
      | .ok signature => Json.mkObj [("status", toJson "serialized"), ("signature", signature)]
      | .error reason => Json.mkObj [("status", toJson "unsupported"), ("reason", toJson reason)]
    let observed := match H62MetadataV2.fingerprint info with
      | .ok signature => Json.mkObj [("status", toJson "serialized"), ("signature", signature)]
      | .error reason => Json.mkObj [("status", toJson "unsupported"), ("reason", toJson reason)]
    signatures := signatures.push (Json.mkObj [("declaration", H62Signature.encodeName name),
      ("kind", toJson kind), ("legacy", legacy), ("metadata_v2", observed)])
    let ranges ← findDeclarationRangesCore? name
    let selection := match ranges with
      | none => Json.null
      | some r => Json.mkObj [("start", toJson r.selectionRange.pos),
          ("end", toJson r.selectionRange.endPos), ("range_start", toJson r.range.pos),
          ("range_end", toJson r.range.endPos)]
    locations := locations.push (Json.mkObj [("declaration", H62Signature.encodeName name),
      ("selection", selection)])
  let sorted := signatures.qsort fun a b => a.compress < b.compress
  let census := Json.mkObj [("format", toJson (2 : Nat)),
    ("module", H62Signature.encodeName target), ("total", toJson signatures.size),
    ("rows", Json.arr sorted)]
  let positions := Json.mkObj [("format", toJson (1 : Nat)),
    ("module", H62Signature.encodeName target),
    ("rows", Json.arr (locations.qsort fun a b => a.compress < b.compress))]
  let result := Json.mkObj [("census", census), ("locations", positions)]
  logInfo m!"H62_METADATA_OBSERVATION {result.compress}"
