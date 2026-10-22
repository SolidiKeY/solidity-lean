import Solidity.Frontend.Import
import Solidity.Frontend.Testing

/-! The runner checks bare external calls and specified rows with callbacks. -/
namespace Solidity.Examples.Tactics.RunnerAudit

solc_import "../../../tests/solc/AuditCallbacks.ast.json" hash 0x21910c3fb5a915a3
  as Imported.AuditCallbacks testing

solc_scoped_problems Imported.AuditCallbacks

open Lean Elab Command Solidity.Frontend

run_cmd do
  for name in ["bare", "specified", "specifiedTrue"] do
    let some row := Imported.AuditCallbacks.report.find? (·.name == name)
      | throwError "audit fixture is missing {name}"
    unless row.status == .elaborated && row.writingCall do
      throwError "external call was lost in {name}: {repr row}"
    let (status, detail, _) ← testObligation ``Imported.AuditCallbacks row
    let expected := if name == "specifiedTrue" then "proved" else "pending"
    unless status == expected do
      throwError "{name}: expected {expected}, got {status}: {detail}"

/-- The harmless specified row is proved under the callback reading. -/
example : ValidT (.noCallback invariant[Imported.AuditCallbacks])
    (cspec[Imported.AuditCallbacks]{ specifiedTrue }) :=
  Imported.AuditCallbacks.specifiedTrue.tested

end Solidity.Examples.Tactics.RunnerAudit
