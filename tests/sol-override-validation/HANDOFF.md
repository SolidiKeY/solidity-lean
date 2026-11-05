# SOL-OV H44 reviewable split

H44 changes packaging only. The 13 implementation modules are already on master;
this increment retains seven Lean proof/replay controls, scripts, documentation
and BULK-MANIFEST.sha256. Theorems, gates, premises and budgets are unchanged.

Repository: /workspace/solidity-lean
Branch: codex/solidity-sol-20261103/override-validation
Original base: b6ba0696102a7a038afe2ed333c09dff397cc5b2
Reviewable parent: 260441fd82852fc1c294e62f6818e15de6375ceb
Pre-split head: acf387973a24cfd81571763c9c5228f144422918
Preserved backup: codex/solidity-sol-20261103/override-validation-pre-H44

Bulk fixtures, JSON matrices, compiler inputs, generated outputs, logs, patches
and historical evidence remain at their existing VM paths. Their retrieval
archive is /workspace/solidity-lean/tests/sol-override-validation/runtime/H44/bulk.tar.gz
(125428964 bytes). The committed manifest records its SHA256. Archive members
retain repository-relative paths. Extract at repository root in another checkout
to restore bulk inputs; no checker expectation or gate was removed or relaxed.
The scripts still require those inputs. Data was not deleted from this VM.
The full pre-split Git history remains reachable through the backup branch.

Prior evidence: 943 compiler rows (448 parsed), 25 adversarial controls,
12 getter pipeline controls, 135 standard-only theorem pins. Saved replay
validation is external differential evidence, separate from kernel equivalence
and identity proofs. Historical Lean 4.24.0/Lake 5.0.0-src+797c613 and KeySort
PASS remain in the archive. H44 itself is not a new proof/compiler/full-gate run.

Whole assignment remains blocked pending central pin validation/registration,
verified local cache readiness and required final gates. Last shared inventory
reported zero errors/614 unrecorded changes including the 135 lane subset;
cache readiness exit 3 is historical. No RUNTIME_GATE_PASS or completion claim.
H41 retained: no ship-cache.sh. No Source/ExtCall/shared registry edit or scope
expansion. Existing goal is unchanged; get_goal is unavailable.

H44 checks and read-only finder/skeptic reviews are summarized in the feature doc;
full raw split outputs remain in runtime/H44, outside Git.
