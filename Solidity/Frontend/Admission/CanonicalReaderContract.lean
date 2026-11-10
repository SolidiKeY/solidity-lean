import Solidity.Frontend.Import
import Solidity.Frontend.ExecutableAst.Shared.Compose

/-! CR canonical-reader migration contract controls (H68).

One H68 fixture (`tests/solc/CanonicalReaderContract.ast.json`, produced by
`scripts/solc-ast.mjs` at H68 metadata retention with the pinned 0.8.34
compiler) is read twice:

* by the actual existing import route (`solc_import`: compilation-unit reader,
  `readContract`, printed bodies, `sol` parser and typed elaboration), whose
  per-function rows are pinned below;
* by the canonical executable reader `Shared.executableReader` through the
  public `Shared.function` root, whose per-function outcomes and exact
  diagnostics are pinned below.

The controls are observations, not a migration. For this fixture, every row
the existing route elaborates is either admitted by the canonical reader or
pinned here as a named support reduction; the corpus-wide gap is measured in
the contract document, not checked here. No fallback from one reader to the other exists or
is introduced, and neither reader is changed. See
`docs/feature-work/cr-canonical-reader-contract.md`. -/
namespace Solidity.Frontend.Admission.CanonicalReaderContract
open Lean Solidity Solidity.Frontend Solidity.Frontend.ExecutableAst

solc_import "../../../tests/solc/CanonicalReaderContract.ast.json" hash 0x86bd4cd2be87c02a
  as CR.CanonicalReaderContract

/-- Existing route: every probe function is elaborated, including both narrow
`uint8` shapes. -/
example : CR.CanonicalReaderContract.report.map (fun r => (r.sourceName, r.status.toStr)) =
    [("wide", "elaborated"), ("narrowParam", "elaborated"), ("narrowLocal", "elaborated"),
     ("signedWide", "elaborated"), ("flag", "elaborated"), ("memoryArray", "elaborated")] := by
  decide

/-- Canonical reader outcome per function of the same fixture, in source order:
`ok` or the exact final diagnostic. -/
def canonicalOutcomes (fixture : String) : IO (List (String × String)) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile fixture))
  let ast ← IO.ofExcept (j.getObjVal? "ast")
  let some c := (J.nodes ast).find? (fun n => J.kind n == "ContractDefinition")
    | throw (IO.userError "fixture contract missing")
  let nodes ← IO.ofExcept (c.getObjValAs? (Array Json) "nodes")
  return nodes.toList.filterMap fun n =>
    if J.kind n != "FunctionDefinition" then none else
      some ((J.str? n "name").getD "",
        match Shared.function Shared.executableReader n c.compress with
        | .ok _ => "ok"
        | .error e => e)

-- Canonical reader: the narrow parameter is refused with the reader's
-- unsupported-type diagnostic; the other five shapes are admitted.
/--
info: [("wide", "ok"),
 ("narrowParam", "compact verifier: unsupported type uint8"),
 ("narrowLocal", "ok"),
 ("signedWide", "ok"),
 ("flag", "ok"),
 ("memoryArray", "ok")]
-/
#guard_msgs (whitespace := lax) in
#eval canonicalOutcomes "tests/solc/CanonicalReaderContract.ast.json"

end Solidity.Frontend.Admission.CanonicalReaderContract
