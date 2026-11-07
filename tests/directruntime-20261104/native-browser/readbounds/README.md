# ReadBounds consumer wrappers

The scripts in this directory retain reviewable build, closure, axiom and
functional-check commands for the native/browser ReadBounds consumer. They use
external pinned source, toolchain, cache and request inputs; inspect each script
before use. Historical absolute paths describe its original execution layout.
A wrapper being present does not establish that its inputs exist or that its
checks pass on the current tree.

Qualification records, exact wrapper inventories, source/binary provenance and
failure logs are archived in the private coordination repository under
`evidence/solidity-directruntime-20261104/native-browser/`. Bulk runtime and
cache packs remain on the original VM for coordinator pull. Consult the sealed
private handoff for exact hashes and source revisions before reuse.

Ordinary executable checks and optional certificates remain separate. Preserve
all recorded failures and timing STOPs; these wrappers do not authorize an
unchanged stopped rerun or establish whole-assignment acceptance.


The closure audit takes `--baseline-evidence-dir /absolute/private/directory`.
For `scripts/remaining-checks.sh`, set `NATIVE_BROWSER_BASELINE_EVIDENCE` to that
same directory. It must contain the original `native-audit.json`,
`native-input-identities.json` and `native-stub-classification.json` receipts;
`baseline-inputs.py` checks their existing exact reference hashes before use.
There is no public-layout fallback, receipt refresh or alternate classification.
The references authenticate a historical body comparison, never a fresh verdict.

The native-negative CLI owns its writer lease and a maximum 300-second local
invocation deadline, including lock wait. Child output remains provisional;
only the parent can publish the final result after timing and reaping checks.
Keep the external invocation exit/deadline receipt authoritative. A result JSON
alone is not crash-proof invocation or H127 cleanup acceptance. Unknown rollback
or interrupted publication remains failure. No cached verdict may replace replay.

Both WASM entry paths delegate to the tracked lock-owning builder. Proof and
symbol gate scripts likewise invoke tracked implementations rather than `.lake`
script copies. Toolchain, source, cache, bounded-resource and current binary
identity obligations still apply; these repairs do not establish their freshness.
