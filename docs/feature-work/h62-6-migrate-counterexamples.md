# H62/H63 Counterexamples migration overlay

Status: **blocked**, not a completed migration. Saved on the isolated branch
`codex/solidity-h62-6-20261106/migrate-counterexamples`, based exactly on
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4` in `/workspace/solidity-lean`.
The committed head is recorded in the exported `evidence/committed-head.json`.
No production Lean source or tracked toolchain file changed.

| Checkpoint | State | Evidence |
| --- | --- | --- |
| 1. Pinned census and clean v4.24.0 directory build | Done | All 78 local modules in the closure pass; all 29 declarations/examples accounted for. |
| 2. Identical pinned v4.35.0 toolchain and adaptation | Partial | Archive SHA verified; KeySort and DeleteFamily pass; three roots need the Syntax owner. |
| 3. All new modules and clean before/after comparison | Blocked | Full target build fails; comparator refuses a partial ratio. Matched modules show an RSS regression. |
| 4. Patch/bundle, frozen hashes, dependency handoff | Partial | Blocked handoff and artifacts prepared; sixteen new rendered types and full gates remain pending. |

## Frozen scope and interfaces

The four assigned originals remain byte-identical to the base. The census has
14 named theorems, four definitions and eleven anonymous examples. It lists
74 transitive local dependencies outside Counterexamples plus four toolchain
imports. None of those dependencies was edited. No statement, hypothesis,
exclusion, definition, observation, proof budget or live ownership changed.
New proof fixtures live only under the assigned tests directory; no generated
root, module map, axiom pin or dependency was added.

| Original | Declaration count | SHA256 of unchanged source |
| --- | --- | --- |
| DeleteFamilyGenericOverlap | 7 | `e5ae7376b4012afd650fbebbe49f9017c1b3261a82960a4984ee747a77e02deb` |
| DiamondTry | 2 | `951eae97e8f58c4ef5d5dcc7a758aa674729787b1c7b084e766d3226552c0ce5` |
| PreFixSortAnnotations | 11 | `762e8484d2d4fe50f5f4b39c6a03708425f6d4f94de5d32e41feacd85a02dc7f` |
| StaticRuntimeSort | 9 | `1b4895f71a6fbcfb4d4c273421cdff58f643d4b4b0a5eb42eb0caf25fb8590d9` |

The old interface probe checks all 18 named declarations and prints their axioms.
Its extracted rendered-type SHA256 is
`01f319cf204eb2f7218d74b64b3dd3dac4ccc068961fab7ffc19f6bea88fbb9f`.
Both old/new overlap rendered-type streams hash to
`248f71b8ba9576e7dd59721613c876666887374d42bb0ffd558390b26f6a590e`.
These are pretty-printed elaborated type hashes, not canonical kernel Expr
hashes. Source hashes freeze exact statements and proof bytes. Sixteen named
target types remain unvalidated behind owner dependencies. The overlap raw
axiom output differs only because v4.35 prints `Quot.sound.{u}` with universes.
No new axioms, `sorry`, `native_decide` or heartbeat overrides were introduced.

## Toolchain and fixed resources

The coordinator inputs under `/workspace/h62-coordinator-inputs` all match their
SHA256 manifest. The sole target is `leanprover/lean4:v4.35.0`, downloaded from
the official URL in `toolchain-pin.json`; archive SHA256:
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
The extracted binary versions are:

- Old Lean: `4.24.0`, Release, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.
- Old Lake: `5.0.0-src+797c613 (Lean version 4.24.0)`.
- New Lean: `4.35.0`, Release, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- New Lake: `5.0.0-src+eb6cafb (Lean version 4.35.0)`.

Both runs use fresh Git source exports of the exact base, a fresh `.lake`,
`enableArtifactCache = false`, `--no-cache`, private empty XDG caches, CPU 0,
`LEAN_NUM_THREADS=1`, explicit Lean `-j1`, and the existing `--tstack=131072`.
Topological module invocations keep heavy Lean work serial. The VM exposes five
CPUs and a 16 GiB cgroup memory cap. Each child has an 11 GiB address-space limit;
the watchdog stops above 12 GiB whole-cgroup usage or below 4 GiB MemAvailable.
`/proc/swaps` contains no swap devices. `memory.swap.max` is `max`, so a kernel
swap cap of zero is not claimed. No systemd-run or cache from master was used.
Only private exports override lean-toolchain/lakefile; the root lane owns cut-over.

Clean means cold build artifacts, not flushed OS page cache. Both source exports
are freshly extracted before measurement. Per-module RSS is Linux wait4
`ru_maxrss` in KiB; the cgroup metric also includes file cache and other processes.
The legacy old result key `aggregate_rss_limit_gib` actually means the cgroup
usage bound. The final harness corrects that label without changing the bound.

## Actual gates and measurements

Evidence root: `/workspace/h62-migrate-counterexamples/evidence`.
Every module entry records its actual absolute command, exit, wall, child RSS,
CPU time and guard outcome. KeySort passes first in both runs.

| Command from repository root | Exit / result | Decisive evidence |
| --- | --- | --- |
| `python3 scripts/h62/item6/migrate-counterexamples/measure.py /workspace/.setup/tools/lean-4.24.0-linux old-clean-2` | 0, 78/78 pass | `old-clean-2/result.json`; 601.537180 s; max child RSS 6,917,544 KiB; peak cgroup 11,694,444,544 bytes. |
| `python3 scripts/h62/item6/migrate-counterexamples/measure.py /workspace/h62-migrate-counterexamples/lean-4.35.0-linux new-clean-1` | 1 | 12 pass, 1 failed external module, 65 dependency-blocked; partial wall 27.541270 s. |
| `python3 tests/h62/item6/migrate-counterexamples/scanner_test.py` | 0, three controls pass | `scanner-tests.log`. Nested comments/strings ignored; 29/18 inventory; a statement mutation breaks the frozen hash. |
| `python3 scripts/h62/item6/migrate-counterexamples/verify.py ... old-probes-2 FrozenInterfaces.lean OverlapInterfaces.lean OverlapModel.lean` | 0 for all three | Full absolute argv and source SHA per probe in `old-probes-2/result.json`. |
| `python3 scripts/h62/item6/migrate-counterexamples/verify.py ... new-probes OverlapInterfaces.lean OverlapModel.lean` | 0 for both | `new-probes/result.json`; two new interfaces plus three fixture theorems check. |
| `python3 scripts/h62/item6/migrate-counterexamples/compare.py .../old-clean-2/result.json .../new-clean-1/result.json` | 1, correctly blocked | `comparison.json`: no settings mismatches; full wall/RSS deltas null. |
| Layer, generated registration, generated fragments, documentation paths | All 0 | `static-gates.json` and individual logs; 857 core modules, zero forbidden reaches. |
| Full target `./run-lean.sh`, affected-root revalidation and final acceptance | Pending | Owner dependency must be repaired first; no runtime gate pass asserted. |

All Lean/check mutations acquired the repository writer lock. Private baseline
builds use unchanged proof sources. The final harness adds explicit source-ref,
archive/version checks, failure propagation and safe guard shutdown; passing-run
thread/cache/CPU/memory settings remain those recorded above.

`ESCALATE PERF-RSS-01`: the completed overlap module uses 223,616 → 489,020 KiB
(+118.7%); its wall is 0.402324 → 0.402177 s. All twelve matched completed modules
show approximately 47–157% more maximum child RSS. `partial-metrics.json` records
all deltas, including small positive wall deltas. No observed matched wall delta
exceeds 10%, and no full-directory slowdown verdict is possible. The comparator
escalates any regression and stops above 10% in wall or RSS for complete runs.
The new partial aggregate must never be compared with the old complete aggregate.

## Dependency request and remaining work

`DEP-SYNTAX-RAW-01`, owner `solidity-h62-6-20261106/migrate-syntax`, relay
`solidity-h62-6-20261106/migrate-root-gate`: supply an owner-reviewed exact-file
migration overlay for `Solidity/Syntax/Raw.lean`. The v4.35 errors are:

- 597:44: `f.drop 1` has type String.Slice, expected String by HashKind.ofName?.
- 650:23: String.Slice.toList is unavailable on `s.drop 9`.
- 665:27: `(rest.drop 8).dropRight 1` is a slice, expected String by splitTopCommas.
- 684:34: String.dropRight is unavailable.
- 682:46: polymorphic `c.endsWith` no longer fits `String → Bool` for List.find?.

Raw is outside this lane's write scope. No compatibility patch was applied to it.
The full closure with ownership routing is in `dependency-report.json`:

| Assigned root | Direct dependency | v4.35 result |
| --- | --- | --- |
| DeleteFamilyGenericOverlap | Solidity.KeySort | Pass unchanged. |
| DiamondTry | Solidity.Calculus.CallbackHolds | Blocked transitively by Raw. |
| PreFixSortAnnotations | Solidity.SortCheck.Faithfulness | Blocked transitively by Raw. |
| StaticRuntimeSort | Solidity.Typing.Sorts | Blocked transitively by Raw. |

After the owner overlay and root resource disposition arrive: build all four
roots and every affected dependency with the same official pin; capture the
remaining sixteen target types/axiom sets; run complete comparable clean builds
and escalate every regression, stopping above 10%; complete the repository final
gate and independent reviews. Do not weaken statements or raise proof budgets.
No goal completion, push, merge, default-branch edit, PR or freeze is authorized
by this handoff. Existing proving lanes retain ownership.

## Authorized backfill and reviews

`OverlapModel.lean` defines Store = Nat → Int, Value = Sum Store Int, field = Unit,
zero defaults, typed casts and same-field writes. Its three theorems establish
all common consistent equations, refute delValueDefault, and separately refute
selectStDelNodeDefault. Both toolchains check them. The shared witness uses no
axioms; the two refutations use only propext and Quot.sound. The concrete model
is extra isolated case coverage and does not replace either original abstract
inconsistency theorem or relax any premise. No solc/EVM external tests ran;
these kernel checks do not establish upstream matcher/extractor equivalence.

Independent read-only finder and skeptic used neither Lean server nor builds.
Their first review found comment-prose imports, the missing time executable,
live/export graph mismatch, mislabeled cgroup memory and inferred toolchain
version. Fixes include a comment-aware scanner with negative controls, wait4
accounting, explicit source-ref/actual export census and pinned binary versions.
The final review confirmed all 29 cases, model correspondence, unchanged original
sources and correct dependency propagation. The skeptic's guard termination race
was fixed by tolerating ProcessLookupError and reaping/saving the child. Probe
provenance support was added. RSS growth is retained as an open escalation.
Raw review messages and dispositions are saved in `reviews.json`.

Earlier failed setup/probe attempts are retained in `historical-attempts.json`:
missing /usr/bin/time and the probe-only pp.width typo. They are superseded by
the passing baseline/probes and are never counted as accepted gates.

## Saved artifacts and reproduction

All bulk output stays off git under `/workspace/h62-migrate-counterexamples`:

- Original patch: `/workspace/h62-migrate-counterexamples/original.patch`.
- Bundle: `/workspace/h62-migrate-counterexamples/migration.bundle`.
- Handoff copy: `/workspace/h62-migrate-counterexamples/handoff.md`.
- Evidence directory: `/workspace/h62-migrate-counterexamples/evidence`.
- Evidence archive: `/workspace/h62-migrate-counterexamples/evidence.tar.gz`.
- SHA256 manifest: `/workspace/h62-migrate-counterexamples/SHA256SUMS`.

The repository scripts census.py, measure.py, verify.py, compare.py and
summarize.py reproduce census, cold builds, probes, refusal/threshold gates and
receipts. Run them from the repository root under the writer lock. measure.py
refuses to overwrite a label; use fresh old/new labels when dependencies change.
It accepts an explicit committed --source-ref whose ancestry includes the base.
The saved tests contain no production registration requirements; coordinator
registration fragment: **none** (only standalone test modules were added).
The existing persistent goal remains unfinished; no replacement goal/thread was
created. get_goal was unavailable, as allowed by the coordinator clarification.

## H82 retirement and final successor handoff

The human explicitly stopped this worker after accepting the successor queue relay.
The survivor is `solidity-h62-6-20261106/migrate-root-gate`; integration belongs to it
after the final stopped/head acknowledgement. The complete original assignment,
original queue, exact scope and successor instructions are committed under
`tests/h62/item6/migrate-counterexamples/retirement/`.
Current H78 static evidence qualifies the earlier named API census: all original
public generated declarations are still unenumerated, including visibility and
exact generated signatures. No blanket generated exclusion or shim is claimed.
Retirement exports use `/workspace/h62-migrate-counterexamples/retirement-h82/`;
original snapshots/manifests remain unchanged. PAUSED was requested but no pause
operation is exposed (stop_goal supports only complete/blocked); the worker stops
without a substitute state change or automatic implementation continuation.
No H71 push permission was supplied; this branch is committed locally only.
