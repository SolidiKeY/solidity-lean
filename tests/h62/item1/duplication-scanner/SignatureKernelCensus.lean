import SignatureEnvironment

/-!
Guards omission of generated or same-spelling constants from a fixture census.
Enumerates the imported SignatureFingerprint module, including generated
constants. Unsupported serialized types are explicit rows, never dropped.
This is tooling evidence, not source-line mapping, ownership or a proof that
moving declarations is safe. Only constants visible in this import are counted; unloaded/private artifact
levels remain outside the result. The original five-record contract is unchanged.
-/

open Lean Elab Command

#h62_environment

run_cmd do
  let env ← getEnv
  let target := Name.mkSimple "SignatureFingerprint"
  let constants := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some idx => env.header.moduleNames[idx.toNat]! == target
    | none => false
  let mut rows : Array Json := #[]
  for (name, info) in constants do
    let kind := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let result := match H62Signature.fingerprint info with
      | .ok signature => [("status", toJson "serialized"), ("signature", signature)]
      | .error reason => [("status", toJson "unsupported"), ("reason", toJson reason)]
    rows := rows.push (Json.mkObj ([("declaration", H62Signature.encodeName name),
      ("kind", toJson kind)] ++ result))
  let sorted := rows.qsort fun a b => a.compress < b.compress
  let record := Json.mkObj [("format", toJson (1 : Nat)),
    ("module", H62Signature.encodeName target), ("total", toJson constants.length),
    ("rows", Json.arr sorted)]
  logInfo m!"H62_KERNEL_CENSUS {record.compress}"
