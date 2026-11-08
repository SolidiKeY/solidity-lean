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


The replay supervisor handles SIGTERM, SIGHUP and SIGINT before forking. A
ready/acknowledgement handshake keeps the action idle until its process group
is confirmed; interruption closes that acknowledgement before group cleanup.
SIGKILL-safe control and containment of escaped descendants still require the
full H127 container protocol. Symbol and selected-C provenance drivers reject
optimized Python before creating outputs, keeping their validation checks active.


The native negative replay admits the exact seven-group request journal and its
fourteen named expected outcomes through `negative-inventory.py`. Expected
statuses are fixed independently of observed completion replies; changing a
false assertion to `proved` with unchanged wire/source hashes is refused.
This admission does not run the checker or repair the retained browser failure.

The shared ReadBounds and registration-parent validation entry points dispatch
fixed tracked recipes through `validation-admission.py`. The supervisor owns
the writer lease until process-group cleanup/reaping, includes lease waiting in
the 300-second local invocation deadline, and checks actual memory/swap/CPU
quota, thread configuration and outer reserve before setup and while running.
The serial Lake configuration and cached shim must match tracked sources.
These local guards rely on the existing trusted checkout and external bounded
cgroup mapping. They are not H127 sealed-input, complete resource/measurement
provenance or whole-container cleanup acceptance. All STOPs remain unchanged.

The `retained-transfers.py` API inspects the sealed historical ReadBounds6513
native binary against the current tracked transfer classifier. Fixed binary,
build and selected-inventory pins identify its inputs; the independently pinned
baseline supplies exact reviewed origin bodies. All six reviewed functions are
disassembled anew, including conditional branches and unknown/indirect targets.
Canonical absolute binary paths and end-of-options separators prevent filenames
from becoming tool options. Tool versions/hashes and input stability are recorded.
The caller must hold the writer lease and bound the invocation.

This inspection executes GNU data-inspection tools only. It does not execute
the verifier, rebuild current source, authenticate a current native/WASM closure,
prove semantic purity or release a runtime/performance STOP. Historical static
results and current-source acceptance remain separate. Raw results belong in the
private coordination repository, never beside these scripts.
