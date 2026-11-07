import tests.h62.item2.«audit-v10-storage».SourceAstUnitResolutionControls
import Solidity.Source.Elaborate

/-! Manual full-unit elaboration probe: no automated gate invokes this file.
It currently raises an error for both actual caller bodies because Source
inference lacks these library Error(string) try forms. The full acceptance
obligation remains open; do not substitute library-only or conversion-only
success. This is not an expected-failure test counted as a passing gate. -/
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
