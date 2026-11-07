# H62/H63 Automation migration overlay

Status: blocked on owner migrations and unchanged producer acceptance. This is an isolated migration overlay, with no transfer of live H28 producer ownership.

Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. Branch: `codex/solidity-h62-6-20261106/migrate-automation`. Checkout: `/workspace/solidity-lean`. The fetched published base is an ancestor of `origin/master` (`c73b8b33f4e75228c78b2752cf078bbc3f211b56` at setup). The pre-existing clean `work` branch remains at `6cf853aea0417155aca29ddb91f1767d3f3a3cc4`. No reset, merge, push, deployment, freeze announcement, generated-root change or axiom-pin edit occurred.

## Checkpoint 1: census and clean old baseline

The census inventories all four Automation files, three Lean modules, five named declarations (the context function, its two theorems and two tactic syntax declarations), and both `elab_rules` registrations. The repository import closure contains 88 Lean modules. Direct cross-directory imports are `Solidity.Calculus.RewriteChains` and `Solidity.Calculus.TacticSyntax`; the closure also depends on core/Syntax/Semantics/Theory/Typing modules and eight Lean/Std modules. There are no new external package dependencies.

`census.py` reads the exact Git commit, handles nested comments and string literals, and emits direct/transitive import edges, named declaration and elaborator records, and source hashes. Source byte identity is the frozen-interface evidence for this unchanged overlay. The Context fixture additionally kernel checks the three exact original public types and prints elaborated types. Raw `Lean.Expr` representations contain compiler hygiene names and imported Context representation changes; they are evidence, not a promise of identical serialization across releases.

Final corrected old clean timing: **479.041052479 seconds**, sampled aggregate RSS **1,455,058,944 bytes**, wait-rusage maximum single-process RSS **1,314,824 KiB**, exit 0, 89 Lake jobs, one concurrent Lean process, no resource stop. Preliminary old timing, excluded from the final comparison: 562.093496304 seconds, sampled aggregate RSS 1,349,750,784 bytes, exit 0, 89 Lake jobs, one concurrent Lean process. The final run repeats this build with the corrected cgroup-aware harness and all-target private arguments.

## Checkpoint 2: exact toolchain and API compatibility

All coordinator input hashes in `/workspace/h62-coordinator-inputs/sha256.json` passed. The official pinned archive is `/workspace/migrate-automation-evidence/toolchains/lean-4.35.0-linux.tar.zst`, from the exact URL in `toolchain-pin.json`, SHA256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.

Actual versions:

- Old Lean: 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Release. Lake: `5.0.0-src+797c613`.
- New Lean: 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release. Lake: `5.0.0-src+eb6cafb`.

`compiler.extract_closed` remains registered and consumed in the official new compiler. `Lean.Core.Context` now extends `Context.Cold`; the unchanged context function and both universal preservation lemmas compile on v4.35. No production edit is needed or justified by this isolated result. No existing owned source was edited, so no producer edit authorization was inferred. The original tracked `lean-toolchain` remains v4.24.0; only disposable test snapshots override it.

Frozen source hashes:

| File | SHA256 |
|---|---|
| `Solidity/Automation/H28/Chain.lean` | `c6ff73664c9f4ee70db158a3218f14f05f4cea6876db75372bca8fce91db2240` |
| `Solidity/Automation/H28/Context.lean` | `3f084f71f8150f8fda7129da2aa92302324fc960c566b00b4e59f9b8a1ffdd6e` |
| `Solidity/Automation/H28/Prove.lean` | `2461c7c833d2162ee1a05a6efc967988ad1f5bf44427d583dc948c1f42b14551` |
| `Solidity/Automation/H28/registration.json` | `fc37552a8cd84a2b71b352c055b0af58c6b20fcdb390c64f78f8774578eda63d` |

## Checkpoint 3: builds, acceptance and measurements

The new clean three-module build fails in out-of-scope `Solidity/Syntax/Raw.lean`. Its decisive errors are String/Slice API incompatibilities at lines 597, 650, 665, 682 and 684. The exact request `DEP-SYNTAX-RAW` is saved in the in-scope `owner-requests.json` for `solidity-h62-6-20261106/migrate-syntax`. No dependency file was changed. The failed run took 24.797312013 seconds with sampled aggregate RSS 1,676,226,560 bytes; these are failure-reproduction metrics, **not** a before/after comparison.

The unchanged original `tests/h28-sol/automation-benchmark/ContextControls.lean` passes v4.24 and fails v4.35. Concrete option proofs fail at lines 95 and 103, and the audit helper's theorem replays report unknown `_inhabitedExprDummy` at lines 106–111. `DEP-H28-CONTEXT-CONTROLS` requests an owner proof/API adaptation preserving every original statement, observation and budget. The original fixture is read only. Failed elaboration includes recovery `sorryAx` output and must never be counted as a proof or trusted axiom report.

The added `ContextInterface.lean` passes on both versions. It checks the exact public signatures, the original two universal lemmas, an inhabited caller, cached heartbeat preservation, and the exact universal options equation. The concrete option=19/cached=23 assertion is explicitly an external execution check. It does not discharge the original producer's failed kernel proofs or replay requirements. The added `SyntaxControls.lean` passes four positive forms and four malformed-argument refusals on v4.24; v4.35 import validation remains blocked. It proves parser compatibility only, not original tactic-owner proof/refusal semantics.

Accepted Context logs report `[propext, Quot.sound]` on v4.24 and `[propext, Classical.choice, Quot.sound]` on v4.35. `AUDIT-AMBIENT-AXIOMS` retains this transitive ambient delta for migrate-root-gate audit. Zero new source `axiom` or `sorry` declarations were introduced; unchanged transitive axiom sets are **not** claimed.

| Command (within the recorded snapshot/environment) | Outcome | Evidence under `/workspace/migrate-automation-evidence/` |
|---|---|---|
| `lake --no-cache build Solidity.KeySort` (old final) | pass | `old-final-keysort/{output.log,result.json}` |
| `lake --no-cache build Solidity.KeySort` (new) | pass | `new-keysort/{output.log,result.json}` |
| `lake --no-cache build Solidity.Automation.H28.Context Solidity.Automation.H28.Prove Solidity.Automation.H28.Chain` (old final) | pass | `old-final-automation-clean/{output.log,result.json}` |
| Same three targets (new clean) | fail, Syntax.Raw dependency | `new-automation-clean/{output.log,result.json}` |
| `lake env lean --tstack=131072 -j1 -M10000 <ContextInterface.lean absolute path>` (old/new) | pass | `old-context-pass/`, `new-context-pass/` |
| Same per-file command, `SyntaxControls.lean` (old) | pass, 4 accept + 4 reject markers | `old-syntax-controls/` |
| Same per-file command, original producer ContextControls (old/new) | pass / fail | `old-producer-context-controls/`, `new-producer-context-controls/` |
| `PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/h62/item6/migrate-automation -p 'test_*.py'` | pass, 20 tests | `static-checks.json` after final collection |
| `./run-lean.sh`, full original owner proof/refusal acceptance and new syntax controls | pending owner migration / acceptance fixes | owner requests; no passing full-gate or runtime-acceptance claim |

Each measurement receipt contains its literal command, cwd, exit and resource outcomes. No callable Lean MCP tools were exposed; bounded per-file CLI checks and targeted Lake builds were used. The full final repository build is still an obligation after dependency fixes; a directory import failure cannot establish that gate.

## Fixed resources and reproduction

The VM cgroup hard cap is 16 GiB, CPU quota 400000/100000 (four CPU equivalents), and actual `SwapTotal=0`. The swap cgroup limit is `max`, not zero; no stronger provisioning claim is made. No systemd scope was created. The harness uses a 12 GiB per-process address-space hard limit plus an 11 GiB aggregate sampled-RSS guard, and stops below 4 GiB available in either the host or finite cgroup. Polling is 50 ms, so the aggregate maximum is labelled sampled. Child wait-rusage maximum is separately labelled as single-process high water, not aggregate RSS. All heavy jobs are serial with `LEAN_NUM_THREADS=1`, explicit Lean `-j1`, `-M10000`, and the repository's `--tstack=131072`. No heartbeat/recursion proof budget was raised.

Both final snapshots have identical private Lake configuration SHA256 `ea7a2ddf116c56f3852cd1750341706da0666e15a4c9b3216375820488e8041c`. They are independent Git archives of the pinned source, start with no Lake products, disable `enableArtifactCache`, and build with `--no-cache`. They neither read nor replace the checkout's v4.24 per-master cache. OS page caches are not flushed or claimed cold. Only cache-clean build products are claimed.

Reproduce from the assigned checkout while holding `/tmp/solidity-lean-feature-groups-20261025/writer.lock`:

```sh
python3 scripts/h62/item6/migrate-automation/prepare.py --repo /workspace/solidity-lean --output /workspace/migrate-automation-evidence/REPRO-old --toolchain old --pin /workspace/h62-coordinator-inputs/toolchain-pin.json
python3 scripts/h62/item6/migrate-automation/prepare.py --repo /workspace/solidity-lean --output /workspace/migrate-automation-evidence/REPRO-new --toolchain new --pin /workspace/h62-coordinator-inputs/toolchain-pin.json
```

The helper intentionally archives BASE for initial compatibility/baseline, not an eventual dependency overlay. Future overlay validation needs an explicit reviewed source revision/patch and a new manifest; do not silently reuse this helper as overlay acceptance. Select the corresponding exact official toolchain `bin` in PATH, run bounded KeySort first, then `lake clean`, then invoke `measure.py --output <new receipt directory> --cwd <snapshot> -- lake --no-cache build <the three targets above>`. Output directories must be new. Source snapshots live outside Git. `assess.py --repo /workspace/solidity-lean --evidence /workspace/migrate-automation-evidence` refuses incomplete/failed/mismatched comparisons; it escalates any measured time/RSS increase and returns STOP above 10% wall slowdown. With a failed new build its deltas remain null.

## Reviews and handoff

Independent finder and skeptic reviews were read only, with no Lean server or Lean invocation. Confirmed fixes: census comment/string handling and both elaborators; cgroup-aware headroom; distinct sampled aggregate versus wait-rusage RSS; complete/finite matching comparison receipts and targets; propagation of STOP/escalation. Final re-review status is recorded in the exported `reviews.json`.

Only additive scripts, two Lean test fixtures, Python negative controls, this document, owner requests and checksum references are delivered. No new area module is registered; no central map/root/pin was touched. Source facts, parser controls, runtime observations, kernel-checked proofs, failed attempted proofs and whole-repository acceptance are distinguished above.

Saved exact-file requests are for coordinator relay. No `relay.sh` was found on this VM, so delivery to another worker is not claimed. No scope decision or premise/exclusion approval is requested. The coordinator can retrieve this branch's committed artifacts from this VM. Full committed head, original patch, bundle, handoff, evidence archive and checksums are recorded in the final off-git seal manifest and CLOUDVM-RESULT. The goal remains blocked, not complete, until all four checkpoints, original acceptance, axiom audit and final comparison/gates pass.

## H82 retirement and successor acknowledgement

The user authorized stop-and-handoff to `solidity-h62-6-20261106/migrate-root-gate`; the later H70/H82 ordering correction expressly preserves retirement over concurrent continue wording. This checkpoint adds only assignment/queue/scope and state preservation under `tests/h62/item6/migrate-automation/retirement/`. No Lean run or proof implementation resumed. The original complete visible assignment and original goal objective are transcribed from this thread, with actual transcription checksums and an explicit limitation that the launcher rendered byte stream was not exposed. The reported launcher hash is retained without asserting byte identity.

The original full work/backfill queue and exact original scope manifest are committed with the final cumulative patch/bundle. Actual local coordinator payloads are in a separate off-Git checksum-bound archive so the successor need not rely on coordinator-local provenance paths. Later H70/H78 ticket payload and all open waits are preserved; H78 generated-public-API exports/shims remain incomplete and no implemented shim is claimed. The earlier five named declarations/two handlers are a source census, not exhaustive public generated API coverage.

The existing goal was previously observed blocked. No pause/get/update operation is exposed: `codex_goals.stop_goal` accepts only `complete` or `blocked`. Therefore tool-level PAUSED cannot be set here; no unsupported call or goal completion/reset/replacement is attempted. The authorized pause and prohibition on automatic implementation continuation are recorded for the controller. This worker stops after final exports and acknowledgement; successor integration is required.

No H71 permission text is available here; conditional permission to push is not assumed. No branch is pushed, and no master/other branch or preserved VM/evidence is changed/deleted. Final base/head/clean status and exact artifact hashes are in the H82 off-Git handoff/report/SHA256SUMS. Prior technical validation and all failing/pending gates remain unchanged.
