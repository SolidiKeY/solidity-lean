import tests.h62.item2.«audit-v10-storage».SourceAstUnitResolutionControls
import Solidity.Source.Elaborate

/-! REQUIRED full elaboration acceptance; currently FAILS for both actual
caller bodies. The unchanged Source inference lacks these library Error(string)
try forms. Do not weaken to library-only or conversion-only success. -/
namespace H62.StorageAudit.SourceAstUnitControls
open Lean Solidity.Source

#eval do
  let mut failed := false
  for (file, pipeline) in fixtureInputs do
    let raw ← IO.FS.readFile file
    let .ok resolved := (do inspect (← Json.parse raw) pipeline)
      | throw (IO.userError "unit conversion/ownership failed")
    for d in resolved.env.decls do
      if d.hasBody then
        IO.println s!"{file}: {d.scope.getD ""}.{d.name} body elaborates={(elabBody resolved.env d).isSome}"
    if (elaborate resolved).isSome then
      IO.println s!"{file}: actual Source resolution and elaboration passed"
    else
      failed := true
  if failed then throw (IO.userError "actual Source unit did not elaborate; acceptance remains blocked")
end H62.StorageAudit.SourceAstUnitControls
