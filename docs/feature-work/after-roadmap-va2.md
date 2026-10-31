# VA2 AU03/AU04 handoff

Status: blocked at runtime setup; no implementation or proof completion claimed.

Repository: `/workspace/va2-sharing`. Branch:
`codex/solidity-automation-20261031/va2-sharing`. Exact base:
`8bd8742ad987d566f7ba7624372cec1c020be07c`.

## Setup checkpoint

Fetched `origin master` and the exact base from the configured GitHub remote.
`origin/master` equals the base; merge-base ancestry passed. Preserved the
older clean `/workspace/solidity-lean` checkout at `9b24b57311b8daf0d4cd01b52bf420fd024c1d3a`
on `work`, creating this isolated worktree instead. Recorded exact AQ1/AQ2
human answers in `docs/solidity-scope.md` before implementation. No Lean
source edits. `git diff --check` passed.

Independent read-only finder `/root/setup_finder` and skeptic
`/root/setup_skeptic` both found no issues with branch/base/ancestry or exact
approval receipt; neither used the Lean server. Evidence:
`/workspace/va2-sharing-artifacts/evidence/reviews.md`.

## Runtime blocker

Actual tools: Lean 4.24.0, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake 5.0.0-src+797c613
(Lean 4.24.0). Cgroup memory.max is 17179869184 (16 GiB), swap.max is
`max`; OS reports no swap. Required 12 GiB/no-swap process-group bound
is not available: cgroupfs is mounted read-only, user systemd has no bus,
system systemd is not PID 1, and sudo is absent. Per-process address-space
limits do not establish an aggregate process-group limit. No heavy job,
LSP session or build was started. No aggregate build RSS measurement exists.
KeySort and RUNTIME_GATE_PASS remain pending. Raw command outcomes:
`/workspace/va2-sharing-artifacts/evidence/setup.json`.

Unblocking requires an executor with a delegated writable cgroup or an
already-enforced 12 GiB/no-swap scope. No theorem, budget or resource
requirement has been weakened. No automatic approval rejection occurred.

## Full queue accounting

All implementation remains pending: baseline PolySize, doubling family,
joined mapping-key failure, loop leaf past anon and speed-history audit;
AU03 located warning and controls; dependent-assignment joins and general
soundness/size proofs; conditional notation/printer roundtrip and restored
chain rows/ifTrace; Boolean-key kernel split; two-base/beyond-splitMax
joined values; AU04 fresh intrinsic call-result locals with freshness,
evaluation and validity transport; loop repeated-leaf repair and controls.

All backfill remains pending: notation/printer/chain controls;
Int.negSucc affine controls; SplitTo Solidity docstrings; proof_size
relocation/pins; certifyLong context discovery; warning/sharing/loop
fixtures. Integrated narrower gap-worker deliveries still need auditing.
Return to dependencies after backfill; do not take VA1 Decision/Residue,
AU05/AU06 or compiler files.

All required proof/validation gates remain pending: per-file diagnostics,
affected closure, full bounded ./run-lean.sh, strict automatic gate,
trust/axiom audits, docs-versus-exact-base comparison, measurements of walk
and leaf growth/time/RSS, and independent finder/skeptic reviews for each
implementation milestone. Setup reviews do not cover those milestones.
No new theorem premises or external-test correctness claims exist.

Artifacts will include a cumulative patch and Git bundle, this handoff,
evidence archive and SHA256 manifest under `/workspace/va2-sharing-artifacts`.
No push, merge, PR or tags were performed. The assignment is incomplete.
