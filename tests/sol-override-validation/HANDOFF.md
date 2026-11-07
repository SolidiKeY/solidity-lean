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

## Review corrections (2026-11-06)

Old final-gate aggregate successes do not certify acceptance: the old runner
ignored failures and the old helper could synthesize pin expectations. Both
are replaced with failure-propagating, read-only checks of committed fixed
expectations. The actual corrected control checker passed all four files
without modifying Lean. Nine regression tests, 25 semantic mutation controls,
H44 archive verification and frozen 943-row compiler evidence validation pass.
The changed gate invalidates historical replay fingerprints: --replays now
correctly fails until fresh evidence is produced and reviewed. Final full gates
remain pending. No old replay hash was changed to match the edited script.

Retrieve the archive named in BULK-MANIFEST.sha256, then run:
python3 scripts/check-sol-override-validation.py --bulk-archive PATH --restore-bulk
The digest anchors restored data; the checker refuses tracked source overwrite.
Use --verify-bulk-only for digest-only verification. For Lean gates use an
explicit bounded --runner command or --local, with caller-owned writer.lock,
prepared PATH/SOLKEY_RULES, zero swap and 4GiB VM reserve. No runtime paths are
assumed. See the feature doc for exact review fixes and trust boundaries.

Replay entry verifies frozen archive inputs before execution, fingerprints the
shared runner, and places timeout inside the selected execution environment.
SOL_OV_BULK_ARCHIVE can locate the retrieved archive outside its recorded path.

## H82 current checkpoint

Fresh replay execution and archive-bound validation now PASS; this supersedes
the earlier stale-fingerprint wait. See H82-HANDOFF.md for new archive/hash,
actual gate outputs, trust boundaries and inheritance relay barrier. Central
inventory and full-cache/final gates remain waits; C3's authenticated final
handoff and stopped acknowledgement are still missing. No completion claim.
