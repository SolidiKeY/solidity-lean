import Solidity.Frontend.Checked.Check
import Lean.Data.Json

/-! External execution controls against solc-extracted type fragments.
This is IO evaluation, not a kernel theorem or compiler-equivalence claim. -/
open Solidity.Source Solidity.Frontend.Checked Lean

private def rootKind : Syn .typeName → String
  | .elem _ => "ElementaryTypeName"
  | .userType _ => "UserDefinedTypeName"
  | .array _ _ => "ArrayTypeName"
  | .mapping _ _ _ _ => "Mapping"
  | .fnType _ _ _ _ => "FunctionTypeName"

private def fixtureMain : IO Unit := do
  let input ← IO.FS.readFile "tests/h28-sol/type-grammar/evidence/solc-type-cases.json"
  let parsed ← IO.ofExcept (Json.parse input)
  let cases ← IO.ofExcept (parsed.getObjValAs? (Array Json) "cases")
  unless cases.size == 13241 do throw (IO.userError "expected all 13241 current type cases")
  let mut failures : Array Json := #[]
  let mut positive := 0
  let mut negative := 0
  for c in cases do
    let src ← IO.ofExcept (c.getObjValAs? String "source")
    let expected ← IO.ofExcept (c.getObjValAs? Bool "expect_accept")
    if expected then positive := positive + 1 else negative := negative + 1
    match parseType src.toUTF8.data.toList with
    | .ok tree =>
      let kindOK ← if expected then do
        let kind ← IO.ofExcept (c.getObjValAs? String "root_kind")
        pure (rootKind tree == kind)
        else pure false
      unless kindOK do
        failures := failures.push (Json.mkObj [("source",toJson src),("error",toJson "unexpected acceptance/root kind"),("actual_kind",toJson (rootKind tree))])
    | .error err =>
      if expected then
        failures := failures.push (Json.mkObj [("source",toJson src),("error",toJson err.msg),("position",toJson err.pos)])
  unless positive == 13218 && negative == 23 do throw (IO.userError "fixture polarity coverage mismatch")
  let report := Json.mkObj [("positive",toJson positive),("negative",toJson negative),("case_count",toJson cases.size),("failures",toJson failures),("proof_boundary",toJson "External execution of actual parseType; no universal proof or solc AST equivalence is established")]
  IO.FS.writeFile "tests/h28-sol/type-grammar/evidence/lean-type-results.json" (report.pretty ++ "\n")
  IO.println s!"LEAN_TYPE_FIXTURES positive={positive} negative={negative} failures={failures.size}"
  unless failures.isEmpty do throw (IO.userError "type grammar fixture failures; inspect lean-type-results.json")

#eval fixtureMain
