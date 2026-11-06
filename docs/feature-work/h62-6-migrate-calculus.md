# H62 item 6: isolated Calculus toolchain migration

Assigned branch: `codex/solidity-h62-6-20261106/migrate-calculus`.
Pinned base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
VM checkout: `/workspace/migrate-calculus` (separate worktree).
Original `/workspace/solidity-lean` checkout remains on `work` unchanged.
The base was fetched from origin and its ancestry to fetched origin/master verified.

## Preparation checkpoint (not migration completion)

The deterministic source census covers all 385 pinned Calculus Lean modules,
490 local modules in their import closure, 83 direct boundary imports and 1,213
reverse boundary imports across tracked Lean files, including roots and Bridge.
No reverse header was unparsed. All 385 Calculus files and all 490 closure
sources remain byte-identical to base. Whole-file hashes cover every original
statement, declaration, case, proof and resource option. These are source hashes,
not elaborated semantic API hashes: that migration obligation remains pending.
No existing Lean file, generated root, central map, pin or lean-toolchain changed.
No new theorem/helper, sorry, axiom, native_decide or proof-budget increase.

Generators: `scripts/h62/item6/migrate-calculus/census.py` and `bounded.py`.
Controls: `tests/h62/item6/migrate-calculus/test_tooling.py` (eight passing tests).
Bulk evidence is off git at `/workspace/migrate-calculus-evidence`.
Current census: `base-census-v3/census.json`, `source-sha256.txt` and
`ordered-modules.txt`. Reproduce with:

```sh
python3 scripts/h62/item6/migrate-calculus/census.py /workspace/migrate-calculus /workspace/migrate-calculus-evidence/new-census
PYTHONDONTWRITEBYTECODE=1 python3 tests/h62/item6/migrate-calculus/test_tooling.py
```

## Toolchain and measurement policy

Coordinator input manifest verifies all five supplied files. The required official
`leanprover/lean4:v4.35.0` archive has SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Actual Lean: 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Lake: `5.0.0-src+eb6cafb (Lean version 4.35.0)`.
Actual old Lean: 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake: `5.0.0-src+797c613 (Lean version 4.24.0)`.
Full extracted-install verification checked 11,574 old files and 17,938 new files
against their respective archives. Deliberately pairing the new archive with the
old installation was rejected (`share/lean/lean.mk` mismatch).
See `installation-verification.json` off git.

Measurements use a fresh output directory with artifact caches disabled,
Docker memory.max=12884901888 and swap.max=0, one CPU, 4 GiB outer available
reserve, LEAN_NUM_THREADS=1 and explicit Lean -j1 behind a serial lock. No systemd-run.
The runtime image is pinned by local image SHA256
`d9b8c34d61a9b9a3c44cab883d7d2f2619d674966ab520186f799cf32e3e0377`;
read-only host executable/library mounts are recorded in each result.
The harness validates the full source inventory before and after, records
config/source/harness hashes, and times the 490-module directory closure.
It is a directory measurement, not the repository final `run-lean.sh` gate.
Any measured regression must be escalated; over 10 percent requires STOP.

The preliminary `old-clean-01` run was deliberately stopped after review found
monitoring/provenance gaps. Its 81.691 s partial timing is invalid as a baseline.
The initial new KeySort probe passed (2.527 s; sampled aggregate RSS 617336832
bytes), but predates final archive/install admission checks. Retain as diagnostic
only; repeat under the final harness before accepting prerequisites.
RUNTIME_GATE_PASS is pending. Full old clean build, new directory build,
matched timing comparison, final validation, semantic interface validation and
migration patch acceptance are all unfinished.

## Independent reviews

Finder and skeptic were separate read-only agents; neither ran Lean or a server.
Initial reviews requested: complete reverse imports, validate census/source
provenance, reserve before workload, bounded monitoring, support module headers,
and bind archive to the selected installation. Confirmed findings were fixed.
Finder accepted the focused census/harness fixes; skeptic accepted the original
census/monitoring fixes and requested the final archive/install binding, now
implemented and checked by positive and deliberately mismatched-install controls.
Both independent reviewers accepted the final archive/install binding and process-guard fixes. This is no full migration review.

## Ownership and remaining work

No `relay.sh` is present in the actual checkout or supplied coordinator inputs.
Exact-file requests must be saved for coordinator pickup when a required source
adaptation is identified. No absent reply is treated as permission. Live producer
ownership continues unchanged; no H55 work is claimed. External dependency
sources in the census are read-only to this lane. No cut-over, push, merge,
pre-gate, deployment or freeze announcement has occurred.

Next: final-harness new-toolchain dependency probe, clean old closure measurement,
owner relay for concrete external failures, scoped acceptance/fixture backfill,
owner-coordinated Calculus adaptations, full new build and matched timings,
independent milestone reviews, final patch/bundle/hash handoff to root/gate.

## Backfill checkpoint and explicit STOP

The full new probe (`new-clean-02/result.json`) passed KeySort, AST and SpecSyntax,
then failed in the out-of-scope `Solidity/Syntax/Raw.lean` at 597, 650, 665, 682
and 684 (String versus String.Slice, absent Slice.toList, changed dropRight,
and polymorphic partially applied endsWith). It blocks 374/385 assigned modules.
All 105/105 external local dependencies have unique migration owners in
`backfill/cross-directory-owners.json`. The full source and import census remains
385 assigned modules, 490 closure modules and 1,213 reverse boundary edges.

The independent-subset probe (`new-independent-03/result.json`) checked all 11
assigned modules not depending on Syntax.Raw: nine pass unchanged,
LinearCountermodel fails at falseNode_spec line 134, and PresburgerDecision is
blocked by that failed import. No excluded module is counted as migrated.

`backfill.py` deterministically generates the isolated full-file countermodel
candidate, preserving every byte except one proof simp-list addition:
`[Bool.not_eq_true']` becomes `[falseNode, Bool.not_eq_true']`.
Two appended axiom reports are fixture instrumentation. It does not modify
`Solidity/Calculus/LinearCountermodel.lean`. The generated test copy is removed
from the checkout after checking; the preserved source and proposed one-line
patch are in the off-git `backfill/` directory. The original file and all other
385 Calculus sources remain unchanged. Owner coordination is still required.

`StringApiCases.lean` contains three test adapters, one bounded test-only tactic,
and eight fixed theorem statements: ASCII/Unicode slicing, negative identity,
zero/overrun slicing, character preservation, suffix success and suffix refusal.
The old suffix implementation needs its private well-founded loop equations;
the tactic locates that existing definition and unfolds its checked equations
at most four times. The final proof is checked by Lean, with no native_decide,
new axiom or budget override. New versions use public standard-library lemmas.

Final byte-identical fixture checks:

| Evidence | Outcome |
|---|---|
| `old-candidate-09/result.json` | PASS: four dependency modules plus both fixtures; actual Lean 4.24.0 |
| `new-candidate-08/result.json` | PASS: same sources and settings; actual official Lean 4.35.0 |
| Both `StringApiCases.lean.log` files | All eight theorems check. Old slicing axioms empty; old suffix axioms `[propext]`; new sets only the standard three |
| Both `GeneratedCountermodelCandidate.lean.log` files | falseNode_spec and searchCountermodel use only `[propext, Classical.choice, Quot.sound]` |
| Python tooling controls | Eight PASS, including stale inventory and live-worker/zombie negative controls |

The matched subset wall time is 21.1943729 s old versus 16.4929547 s new
(-22.1824 percent), but sampled aggregate peak RSS is 867917824 bytes old versus
1756893184 bytes new (+102.4262 percent). This is a diagnostic subset, not the
required full-directory before/after comparison. **ESCALATE: the RSS regression
triggers STOP on further new-toolchain migration work pending root/gate
classification.** See `backfill/matched-diagnostic-comparison.json`.
No attempted production migration change follows this STOP. Completing the
already-authorized old baseline and preparing read-only handoff evidence remain.

Typed requests are committed at `tests/h62/item6/migrate-calculus/owner-requests.json`
and preserved off git: `DEP-SYNTAX-RAW-V435` (syntax owner migration dependency)
and `OWNER-LINEAR-FALSENODE` (live VA1 owner coordination before an exact-file
proof-only overlay). The delivery field explicitly says saved for coordinator
pickup; no request was sent and no absent response is treated as approval.
The RSS STOP is an additional root/gate blocker. No scope or statement exclusion
is proposed. There are no human scope questions.

Independent finder and skeptic re-reviewed the candidate, eight fixtures,
source and scope hashes, 105 owners, and recomputed the timing/RSS deltas.
Both confirmed matching final fixture sources and standard-only axioms; both
accepted the escalation/STOP and retained the unfinished full-directory gates.
Neither used Lean or a Lean server.

The first corrected old baseline attempt (`old-clean-02`) passed 176 modules
then was stopped by the process observer at SoundSummary: 1331.084 s partial,
1695682560 bytes sampled RSS. It is **not** an accepted baseline. Its rejected
snapshot was not retained, so the historical process condition is unclassified.
The observer now records STAT, ignores zombies, retains rejected raw snapshots,
and still rejects two live Lean processes or missing -j1. Both reviewers accepted
the fix and the fresh complete old baseline must be repeated (`old-clean-03`).

## Persistent goal and continuation

This remains the original launcher goal for rendered prompt SHA256
`0992f14182a95808d7e2bf1d1e1610b8677b2b85e79f2c8697c7fb782cd1eb59`.
No replacement goal or competing continuation was created. get_goal is not
exposed; coordinator explicitly confirmed that optional absence is not a blocker.
Original VM environment:
`ccarenv_b64_Y2NhcmVudl9kODQ1MTc2ZjEzOTg4MTkxOGM0YzMyZmJjYzQ5Y2U4YQ`.
Coordinator owns the fresh-thread handoff after the completed preparation/backfill
items; this worker never self-launches a replacement. Whole-goal completion is
blocked by owner dependencies and the RSS STOP. Full old baseline, full new
build, semantic interface validation, full comparison and final gates must never
be inferred from the passing subset or this handoff.

## Resource recovery before the fresh old baseline

`old-clean-03` was correctly stopped at RuleShapes after 262 successful modules:
2005.496787837 s partial wall and 3460091904 bytes sampled aggregate RSS.
The failure was the 4 GiB parent reserve guard, not a reported proof error.
It is not an accepted clean baseline and is not combined with another run.

At idle, the VM cgroup charged 9468493824 bytes, including 8757678080 bytes of
file cache, with no Lean process active. The allowed-memory calculation remains
conservative: min(host MemAvailable, parent memory.max - memory.current).
No cap, swap setting, reserve, thread setting or theorem budget was relaxed.

`cache.py` applies POSIX_FADV_DONTNEED only to specified regular files opened
read-only, skipping symlinks. It neither deletes nor modifies file contents.
It is advisory cache conditioning, not a guarantee that every page is evicted.
The three roots are this task's evidence directory, the verified old toolchain,
and its archive. The evidence directory includes the verified new toolchain
and all retained prior attempts. Thus the same old/new inputs can receive the
same policy before any later authorized full comparison. No global drop_caches
or sysfs resource write is used. All historical logs and build products remain.

`cache-recovery.json` records usage falling 9468493824 to 3458945024 bytes,
a recovery of 6009548800 bytes, with file cache falling 5853618176 bytes.
The bounded runner conditions after archive/install verification but before
workload admission, records all roots/pre/post readings and helper SHA256,
and saves executed-cache.py alongside executed-bounded.py. It also now retains
the exact offending memory reading before any reserve stop.

The cache byte-preservation/symlink control passes in the authorized worker,
bringing Python controls to nine. The finder independently passed eight
nonwriting controls; its read-only sandbox could not create the temporary
control file. Both finder and skeptic accepted the advisory method with
unchanged limits and required the same policy for later comparisons. The
finder's cache-helper provenance request was implemented before rerunning.
The fresh complete old baseline is now `old-clean-04`; all prior attempts remain
partial/invalid for acceptance. The RSS STOP on new-toolchain work remains.
