# Root/gate registration fragment

These are explicit test fixtures outside production library roots. No generated
root, central module map or axiom pin is edited by this lane.

| Fixture | Role | Invocation after the required source closure is built |
|---|---|---|
| `FrozenInterfaces.lean` | Inventory every assigned module-owned declaration, type, body and theorem axiom boundary | `measure.py --inventory-imports <completed-closure>/lib` with the same toolchain |
| `StringApiControls.lean` | Eight finite String API case proofs; no general parser-correctness claim | `check-api.py --toolchain <official-release> --imports <outputs>/lib --out <fresh-directory>` |

`StringApiAxioms.lean` is the separate post-compilation axiom audit imported by
check-api.py; it adds no theorem. experimental.module=true is enabled only for
these isolated cases on both releases, with unchanged heartbeat budgets.

Use `interfaces.py OLD_LOG [NEW_LOG]` to normalize/hash the inventory and compare
all declaration/type/executable-body fingerprints. Require the corresponding
Lean process to have exited successfully; parsing a log alone is not a Lean gate.
Use `compare.py OLD_MEASUREMENT NEW_MEASUREMENT` only for completed clean assigned
source-closure runs. The root migration lane owns the final `lean-toolchain`
change and full fleet cut-over. The live producers retain all original ownership.
