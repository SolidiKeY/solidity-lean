# VA2 AU03/AU04 handoff

Status: runtime setup recovered; AU03/AU04 implementation and proof work remain pending.

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

## Investigated runtime recovery (2026-10-31)

The earlier cgroupfs/systemd failure evidence remains intact. No unchanged
cgroupfs/systemd probe was retried. Consulted the supported
`cloud-environment-runtime` skill and its `references/docker.md`.
The same attached VM has the platform-managed Docker 28.4.0 daemon at
`unix:///var/run/docker.sock`; no daemon was installed, started or restarted.
Explicit local endpoint selection cleared Docker endpoint/context/TLS
selectors only, as required by the skill. No policy, authentication,
privilege, catalog or VM changes were made. Podman/nerdctl are absent.

A task-owned child container using pinned image
`debian@sha256:f6b08b09a05725f9431502d3b5714f5c4576e82c1a84fa1debe0c24a7e0c3ec4`
mounted the exact existing `/workspace` tree, including the isolated checkout
and existing toolchain. It ran as UID/GID 1000 with `--network=none`,
`--memory=12g --memory-swap=12g`. Actual child cgroup values were
`memory.max=12884901888` and `memory.swap.max=0`. The daemon reports
MemoryLimit=true and SwapLimit=true. This is the aggregate hard limit;
the RSS sampler is measurement only. Containers were removed on exit.

Actual toolchain in that bounded container:
Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake 5.0.0-src+797c613 (Lean 4.24.0).
With `LEAN_NUM_THREADS=1`, the command
`lake env lean -j1 --tstack=131072 Solidity/KeySort.lean` passed.
The evidence script prints RUNTIME_GATE_PASS only after those cap checks,
version outputs and successful KeySort exit. Recorded wall time is 1 second
(coarse whole-second measurement), sampled aggregate process RSS peak
301932 KiB, and cgroup peak accounted memory 114503680 bytes. These are
different measurements; shared resident pages can be accounted outside this
child cgroup. Neither number is a walk/leaf growth benchmark.

An initial Lake build attempt failed with `permission denied` for `//.cache`
and emitted a Lean command without explicit -j1; it is retained as a failed
attempt and does not support the runtime gate. The passing explicit invocation
sets the existing writable `XDG_CACHE_HOME=/workspace/.setup/cache`.

Original checkpoint `29aec17e607a5dfc585a0e4a49990dc8e3f751c3` and every
original artifact were preserved; all original SHA256SUMS entries verified.
New evidence is separately stored under
`/workspace/va2-sharing-artifacts/runtime-recovery/`, with exact command arrays,
exit codes, raw logs and reproducible probe scripts. No implementation files
were edited; all work/backfill/proof/validation obligations listed above remain
open. The same existing blocked goal awaits coordinator reactivation based on
this evidence; no replacement goal or competing continuation was created.

Independent recovery finder `/root/setup_finder` accepted the runtime evidence
and requested a committed handoff with separately checksum-bound recovery
artifacts. This recovery checkpoint addresses that finding. Independent skeptic
`/root/setup_skeptic` accepted the KeySort runtime gate and flagged that RSS
sampling sums visible `/proc` processes without a separately recorded PID
isolation assertion; treat that RSS number as a visible-process sample, not an
independently certified process-group maximum. Both reviews were read-only,
without Lean server or gate reruns. Evidence: `runtime-recovery/reviews.md`.
