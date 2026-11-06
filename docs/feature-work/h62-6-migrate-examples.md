# H62 item 6: examples migration overlay

Assignment: `solidity-h62-6-20261106/migrate-examples`.
Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Branch: `codex/solidity-h62-6-20261106/migrate-examples`.
Repository: `/workspace/solidity-lean-migrate-examples`.
Original clean checkout `/workspace/solidity-lean`, branch `work`, is preserved.
Fetched exact base and master; `git merge-base --is-ancestor BASE origin/master`
passed. Assigned remote branch did not exist; created assigned local branch at BASE.
No push, merge, root registration, tracked toolchain change or producer edit.

## Checkpoint state

1. Census partial: all 354 explicitly assigned example files match coordinator
   ownership snapshot exactly. 1,067 direct imports, 885 external edges to 233
   distinct modules, 7,518 lexical declaration entries. Source hashes are complete;
   lexical entries are not a Lean parser or complete generated-declaration inventory.
   Clean old comparison remains pending.
2. Official pinned v4.35.0 provisioned. No adaptation or new-toolchain full build
   has passed. Archive SHA256:
   `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
3. New builds, clean comparison, regression escalation and acceptance pending.
4. Final migration patch, elaborated frozen-interface hashes and root-gate
   dependency handoff pending. This initial tooling checkpoint is not completion.

## Toolchains and resource boundary

Old Lean 4.24.0 / Lake 5.0.0-src+797c613, official commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
New Lean 4.35.0 / Lake 5.0.0-src+eb6cafb, official commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Coordinator input hashes all verified. Private toolchain wrappers serialize the
unchanged official Lean executable with `flock` and explicit `-j1`;
`LEAN_NUM_THREADS=1`. No systemd-run and no shared/per-master old cache.
VM cgroup hard cap 16 GiB, host swap zero. Sampled guard: maximum owned-group
RSS 12 GiB, minimum host and cgroup reserve 4 GiB, every 0.5 seconds.
This is a sampled guard, not a hard 12 GiB per-job cap. Resource stops fail.
The runner kills surviving owned-group children and rejects orphaned work;
processes may not detach. Writer lock is held through builds and before writes.

## Actual gates and evidence

Evidence directory: `/workspace/h62-migrate-examples-evidence` (bulk off Git).

- `python3 scripts/h62/item6/migrate-examples/census.py --output OUT`: pass;
  repeated outputs byte-identical SHA256
  `ab85ba2f770ef45b85ca111896303466e3caef78a0b57ca1325b9ad4a803cf6f`.
- `PYTHONDONTWRITEBYTECODE=1 python3 tests/h62/item6/migrate-examples/acceptance.py`:
  scanner comment/string/modifier controls, successful command and rejected orphan
  cleanup controls pass. These are external Python tests, not Lean proofs.
- Bounded old `bash scripts/check-solkey.sh`: pass, exit 0, 22.6803 s,
  sampled peak group RSS 808,235,008 bytes. Output: 377 taclets, 131 read-bearing,
  table covers 131; annotations match explicitly supplied SolKey rules file.
  `old-keysort.log` and `.json` retain output and measurement.
- Initial clean `bash run-lean.sh` attempts: missing GNU time and hidden Node PATH
  stopped before Lean work. Third attempt passed layer checks (857 core modules,
  zero reach elaborator/parser adapters), built `Solidity.KeySort` and more,
  then was deliberately interrupted to measure only the assigned examples closure.
  Exit 130, `MONITOR_ERROR:KeyboardInterrupt`, 148.8484 s, not a passing gate or
  completed clean baseline. All attempts retained as `old-clean-{1,2,3}.*`.
- No `RUNTIME_GATE_PASS`: new-toolchain KeySort and all required final gates pending.

## Frozen statements and dependency boundary

No original Lean files edited, no added/changed theorem statements, proof budgets,
axioms, sorry or trust shortcuts. Zero lexical trust tokens in the assigned source
census is not an elaborated transitive axiom audit. Full original source blobs are
hashed; frozen-interface expression hashes must follow successful elaboration.
Examples transitively import about 713 external local modules (1,067 total module
closure), chiefly Calculus, Semantics, EVM and frontend dependencies. Source/API
repairs there belong to directory owners. Coordinator relay.sh is absent in this
VM and pinned tree; exact-file owner requests will be saved for coordinator relay
once concrete failures identify them. No absent reply will be treated as approval.

## Independent reviews

Read-only finder and skeptic (neither used Lean/server) confirmed source coverage
and caught scanner omissions, line errors, string false edges, cleanup and
provenance issues. Fixes and negative controls are recorded in
`/workspace/h62-migrate-examples-evidence/review-initial.md`.
Skeptic final tooling review passed. Finder final review requested a fresh process
snapshot after leader exit; applied. The entire four-checkpoint queue remains open.

## Typed dependency blocker DEP-SORTCHECK-435

Bounded new `bash scripts/check-solkey.sh`: fail, exit 1, 18.1622 s,
sampled peak group RSS 1,798,197,248 bytes. The script suppresses Lake output;
reproduction `lake build solkeycheck` exposed the exact error (exit 1, 4.0337 s):
`Solidity/SortCheck/Parser.lean:76:13: Invalid field trim`, because Lean 4.35
removed `String.trim`. Follow-on evaluation errors are compiler error recovery,
not source sorry. Owner: `solidity-h62-6-20261106/migrate-sortcheck`;
root integration: `solidity-h62-6-20261106/migrate-root-gate`.
Exact-file request is saved in `/workspace/h62-migrate-examples-evidence/owner-requests.json`
for coordinator relay; no repair or original-file edit made here. No new-toolchain
runtime prerequisite pass, complete timing comparison or full gate is claimed.


## Continuation from this tooling checkpoint

The original persistent goal is unchanged and unfinished. Coordinator inputs are
`/workspace/h62-coordinator-inputs/`; absence of get_goal is explicitly permitted
by the coordinator. Never create a replacement goal or change producer ownership.
Next clean baseline command (the script holds writer lock, cleans outputs and
refuses reused cache/results):

```sh
bash scripts/h62/item6/migrate-examples/measure.sh \
  /workspace/.setup/tools/lean-4.24.0-linux \
  /workspace/h62-migrate-examples-evidence/bounded-4.24.0 \
  /workspace/h62-migrate-examples-evidence/cache-old-examples-clean-1 \
  /workspace/h62-migrate-examples-evidence old-examples-clean-1
```

Inspect its `.json`, `.log` and settings/source-hash files in the evidence directory;
if still running, do not write while writer lock is held. Check owned process
status; do not launch a second heavy process. On successful completion, save
wall/RSS without treating it as a new-toolchain gate. Resume checkpoints 2–4
only when required owner overlays and prerequisites permit; continue only assigned
backfill meanwhile. Any slowdown escalates; greater than 10 percent stops.
No before/after timing delta exists yet. Required final policy remains `./run-lean.sh`.

Export a committed checkpoint with
`python3 scripts/h62/item6/migrate-examples/export.py --evidence /workspace/h62-migrate-examples-evidence`.
Exports contain full committed head/base, patch, thin overlay bundle, source blob
hashes, evidence snapshot and SHA256 manifest. Re-export after final measurements;
an initial snapshot never proves later or pending gates. Fresh-thread continuation
belongs to coordinator/original goal, never a self-created replacement.
