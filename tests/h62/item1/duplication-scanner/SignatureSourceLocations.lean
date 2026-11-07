import SignatureEnvironment

/-!
Guards namespace guesses and generated-declaration aliases in source binding.
Reports direct declaration-range metadata for each visible imported fixture
constant, without the parent-range fallback used by editor navigation.
Unavailable metadata stays null; a range alone is not source correspondence,
ownership, unloaded/private coverage, or evidence that moving a lemma is safe.
-/

open Lean Elab Command

#h62_environment

run_cmd do
  let env ← getEnv
  let target := Name.mkSimple "SignatureFingerprint"
  let mut rows : Array Json := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless env.header.moduleNames[idx.toNat]! == target do continue
    let ranges ← findDeclarationRangesCore? name
    let location := match ranges with
      | none => Json.null
      | some r => Json.mkObj [
          ("start", toJson r.selectionRange.pos),
          ("end", toJson r.selectionRange.endPos),
          ("range_start", toJson r.range.pos),
          ("range_end", toJson r.range.endPos)]
    rows := rows.push (Json.mkObj [("declaration", H62Signature.encodeName name),
      ("selection", location)])
  let sorted := rows.qsort fun a b => a.compress < b.compress
  let result := Json.mkObj [("format", toJson (1 : Nat)),
    ("module", H62Signature.encodeName target), ("rows", Json.arr sorted)]
  logInfo m!"H62_SOURCE_LOCATIONS {result.compress}"
