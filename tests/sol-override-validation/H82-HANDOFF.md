# Inheritance successor: H82 checkpoint

Existing goal retained; no goal creation/reset/pause/completion or master push.
Repository /workspace/solidity-lean; branch
codex/solidity-sol-20261103/override-validation; original base
b6ba0696102a7a038afe2ed333c09dff397cc5b2. Execution head for these checks:
4bdd5952823dd6d76f7081719230b27b67f07cbf. Only docs/manifests change afterward.

## Ready SOL-OV work completed

Actual replay.py execution exited 0: narrow dependency build completed (44 jobs),
candidate and current replays each executed all 943 rows, 448 parsed; candidate
accepts 90 with zero mismatches, current accepts 175 and reproduces documented
fallback/receive/getter/modifier false passes. No historical log was rehashed as
if newly executed. A new VM-only archive replaces eight produced replay files;
only candidate TSV and replay manifest bytes differ from the historical archive.
All frozen fixtures, expectations and archive member inventory are unchanged.
The old H44 archive remains available at its original path.

New archive: /workspace/solidity-lean/tests/sol-override-validation/runtime/H82/validated-bulk.tar.gz
Bytes: 125428585
SHA256: a78a6951b658780f93d634acf3da81f5734ea80f502e329c44a5eda47de29163
BULK-MANIFEST.sha256 now anchors it. Archive-bound --replays validation PASS.
Fresh hash-pinned solc 0.8.38 matrix PASS (943 rows); supplemental code-generation
controls PASS (12 pipeline rows). Constant getters overriding pure remain valid;
regular/immutable getters cannot; accepted ABI getters remain view. No EVM claim.

KeySort PASS: parsed 377 taclets, 131 read-bearing, table covers 131; annotations
match canonical pinned rules. Lean 4.24.0, commit
797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake 5.0.0-src+797c613.
Four committed guarded control proof files PASS without source changes.
Nine targeted regressions and 25 adversarial controls PASS. Roots/fragments/layers
PASS. Repository trust wrapper PASS: 6147 sources, 289 sites, zero findings.
An initial direct trust-script invocation lacked its required stdin; the approved
wrapper corrected that invocation. Its failed log is retained, not relabeled.
No library, control theorem, premise, exclusion, axiom or budget changed.
Kernel proof/equivalence evidence and external compiler/replay evidence remain
separate. Whole acceptance and RUNTIME_GATE_PASS are NOT claimed.

Runtime cap 10737418240 bytes, swap 0; parent cap 17179869184 leaves >=4GiB
reserve. Cgroup lifetime peak 766091264 bytes, zero OOM/max events. This is not
per-command RSS. Runner proof timings are in controls/control-gates.json;
compiler/replay/KeySort wall times were not separately instrumented.
Raw outputs remain in runtime/H82, hashed by H82-MANIFEST.sha256; no bulk in Git.

## Real waits after independent work

- H21/CENTRAL REG-OV-1104: shared inventory exits 1, zero axiom errors and
  4133 unrecorded changes globally, including exactly 135 lane pins. Shared
  registries remain outside the live exclusive scope; no registry edits made.
- H21/H41: full cache-only readiness still exits 3 after the narrow successful
  build. Final full run-lean/default/TestSuite/Bridge gates await verified cache
  readiness. No unchanged cold timing STOP was rerun; no ship-cache.sh on VM.
- C3 retirement/frozen-assignment barrier: successor relay accepted, but no
  authenticated final bundle/full original rendered assignment/exact scope bytes
  or explicit stopped/goal-paused acknowledgement has arrived. Supplied head
  70845978ab616a63b13d0dee8b31b28893ccf591 exists and is already an ancestor
  of this checkout, so merge-first ancestry is present; no new merge is needed
  or performed. The remote lane branch is not advertised and the supplied
  /workspace/c3-exactness-artifacts/rebase-70845978-from-e408d326f4c36fd2274a20994afbc83d314b031e/HANDOFF.md
  does not exist on this VM. No C3 scope edit/integration or stop request made.
  Coordinator read-only retrieval/relay is required, preserving earlier failures.

No remaining independent original SOL-OV item or assigned backfill is ready.
C3 queue remains inherited and open, not guessed or narrowed: H70 retrieval,
shared inventory/full readiness, all original acceptance/backfill obligations.
No exact-file agreement is pending; H82 statement-preserving rules acknowledged.
Applicable H68/H69/H78/H80/H81 rules and full retiree frozen bytes must accompany
its authenticated relay; inaccessible coordinator-host receipt paths are not
claimed retrieved. get_goal remains unavailable; existing goal unchanged.

Separate read-only finder/skeptic reviews of the new archive/provenance found
no substantive findings. Neither used Lean or wrote files. Review results and
raw checks are checksum-bound in runtime/H82. Status blocked only after all
ready independent checks above were completed.
