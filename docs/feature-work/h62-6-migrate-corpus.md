# H62/H63 Corpus toolchain migration

## H82 preservation checkpoint: current disposition

The lane-specific H82 instruction orders retirement after preserving a final
checkpoint for `solidity-h62-6-20261106/migrate-root-gate`; the coordinator reports
that successor queue relay accepted. A later generic H82 standing-rules relay
says continue. Q-H82-RESUME was explicitly resolved: KEEP RETIREMENT AND HANDOFF. Generic
continue broadcasts do not revoke this lane-specific stop; no new proof
implementation starts. The coordinator will set the existing goal PAUSED after
the final head report and idle turn because the worker tool lacks pause. This checkpoint preserves work and acknowledges
stopped implementation; the goal is not complete. No automatic implementation
continuation is authorized by the retirement instruction.

Current H82 standing agreements supersede this document's earlier exact-file
agreement prose for statement-preserving proof-only changes, additive
lemmas/definitions, splits, imports and documentation fixes. Any pending request
solely for that permission is withdrawn. Existing dependency failures are actual
unrepaired/unvalidated inputs, not proof-only permission waits. Changes to an
existing statement, a depended-on definition body, interface, budget, axiom set
or exclusion still require the owner; frozen changes require H57 versioned pairs.
Earlier paragraphs below are retained as historical evidence, not current
proof-only permission policy. No Claude-owned source edits or owner messages
have been made in this preservation checkpoint.

The full original assignment, objective, queues, scope and subsequent relays are
committed under [h82-handoff](../../tests/h62/item6/migrate-corpus/h82-handoff/README.md).
The original rendered-prompt digest is preserved as coordinator provenance;
unavailable raw renderer bytes are not falsely equated to the transcript hash.

H71 push permission is absent from supplied local inputs and the visible thread;
therefore no push is performed under the conditional H82 permission. The original
lane branch remains local and is exported as a cumulative patch and bundle.
The PAUSED state is requested, but no callable goal pause/set-state tool exists:
the sole goal operation only accepts complete or blocked. It is not used as a
substitute for pause; no goal is completed, created or reset. Earlier relay turns
also lacked trusted goal/source-turn context. Goal pause requires host support;
implementation is stopped locally regardless. No new Lean check, timing STOP
rerun or resource-policy assumption is introduced; H81's full text is not locally
available and the prior measurements remain historical H62 evidence.


This isolated overlay remains **blocked and incomplete**. No producer ownership
was transferred, no original Lean file or root toolchain pin was edited, and no
push, merge, PR, deployment or cut-over was performed.

Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Branch: `codex/solidity-h62-6-20261106/migrate-corpus`.
Repository: `/workspace/solidity-lean`.
Original frozen prompt identifier supplied by launcher:
`ef334e40480cb8325ca7943fbc986e0d359a7b8928d753133302e731e3f266f2`.
The existing goal was retained; get_goal is not exposed and coordinator has
explicitly confirmed that optional inspection absence is not a blocker.

## Census and frozen boundaries

The nine assigned files are byte-identical to the pinned base. Source census
records 340 local modules, 331 outside-directory dependencies, and eight direct
outside imports. Every outside dependency maps to exactly one migration owner.
All 639 scoped expected rows are retained: 552 derived, 68 proved, 11 refuted,
one excluded, two skipped, five unsupported. No exclusion or premise changed.
The full 774-row expected table is also hash-pinned.

[Source hashes](../../tests/h62/item6/migrate-corpus/frozen-sources.json) freeze all
source bytes, including unnamed examples, program bodies and proof budgets.
They are not elaborated API compatibility evidence. The interface probe generator
is supplied for a separate type-expression inventory for all nine modules on the old toolchain. New-version imports remain blocked.
[Case summary](../../tests/h62/item6/migrate-corpus/frozen-case-summary.json) is
small; full census/case/dependency outputs stay off Git with final checksums.

## Toolchain and resource policy

Official new pin: `leanprover/lean4:v4.35.0`, Linux x86_64 archive SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Actual Lean: 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Lake: `5.0.0-src+eb6cafb (Lean version 4.35.0)`.
Old Lean: 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake: `5.0.0-src+797c613 (Lean version 4.24.0)`.
All five coordinator input SHA256 checks passed.

KeySort passed on both versions before migration validation. Its preliminary
sampled RSS increased from 307396608 to 638472192 bytes; wall fell from
2.211549377 to 1.809531277 seconds. This resource regression is escalated to
migrate-root-gate; it is not a full-directory performance comparison.

The VM hard cgroup memory cap is 16 GiB; the driver samples complete task
process ancestry, including detached MCP sessions, at 200 ms. It stops above
12 GiB aggregate RSS or below 4 GiB host/cgroup headroom. Host swap total is zero;
cgroup swap.max is max, so no cgroup swap prohibition is claimed. No systemd-run
or shared/per-master cache retrieval is used. Official binaries are unchanged;
private symlink sysroots add explicit `-j1`, serial worker locking and no changed
proof budgets. `LEAN_NUM_THREADS=1`. Private TOMLs disable artifact caches and
use isolated output directories; they must not enter the final patch.

## Gates and measurements so far

* Clean old attempt: exit 1 after 2032.551216607 s, sampled aggregate RSS
  3510403072 bytes. An added 12 GiB virtual-address cap caused thread creation
  failure at Calculus.TermSize. This attempt is **invalid as a baseline**.
* Removing that inappropriate address-space cap: TermSize passed in
  34.209311049 s, sampled RSS 1267032064 bytes. This focused run is not a clean
  full build. The fresh full old retry result follows below.
* Clean new diagnostic build: exit 1 after 60.376878436 s, sampled RSS
  1675653120 bytes; no resource stop. Outside-scope dependency failures are
  recorded below. This failed run supplies no valid performance delta.
* Five finite boundary fixtures passed old-toolchain per-file MCP diagnostics:
  complete, success true, no errors, no failed dependencies. The fixtures cover
  successful execution, require(false) rejection/revert, assert(false)
  rejection/panic. They do not establish global compiler totality or new-version
  compatibility. MCP Python shutdown emits a known event-loop warning after the
  successful diagnostic response; driver exit is zero.
* Acceptance v5 passes byte mutation, missing/immediate/nested module controls,
  stopped-child exit-zero handling, external SIGTERM cleanup, detached 32 MiB
  descendant accounting/cleanup, and synthetic timing-policy controls. Identical
  synthetic measurements pass; exactly 10% escalates; above 10% stops; failed,
  nonfinite, mismatched-source/config/cache/target/AS records are blocked.
* Static baseline: 857 core modules reach neither elaborator nor checked parser
  adapters; generated roots and fragments match. These are not a full new gate.

## Independent reviews

Read-only finder and skeptic used no Lean server and made no edits. Confirmed
findings fixed: process cleanup and external termination, false-success stop
status, preflight headroom, misleading hard-limit labels, detached process
accounting, nested source injection, benchmark provenance, nonfinite values,
required fields in both records, and strict decimal >10% threshold. Both final
comparison reviews found no remaining blocker for the clean old retry.
The initial AS-capped run and failed MCP setup attempts remain preserved as
failed evidence. They are never counted as passing gates.

## Owner requests and remaining queue

[Exact-file requests](../../tests/h62/item6/migrate-corpus/owner-requests.json):
`DEP-SYNTAX-RAW` goes to migrate-syntax for String/Slice API errors at
Solidity/Syntax/Raw.lean:597,650,665,682,684.
`DEP-CALCULUS-LINEARCOUNTERMODEL` goes to migrate-calculus for the proof mismatch
at Solidity/Calculus/LinearCountermodel.lean:134.
Both are actual transitive corpus prerequisites. Requests are prepared for
coordinator retrieval; relay.sh is absent, so no delivery/acknowledgement is
invented. No existing owner file was edited.

Still required: owner dependency overlays
and any resulting exact-file coordination; successful new build of all nine
modules; cross-version elaborated interface comparison; deterministic corpus
acceptance and full affected/final repository gates; valid paired timings with
any regression escalated and >10% slowdown stopped; final finder/skeptic evidence
review; final patch/bundle and checksum manifest. The goal remains unfinished.

Evidence directory: `/workspace/migrate-corpus-evidence`.
Reproduction tools: `scripts/h62/item6/migrate-corpus/`.
Final committed head, artifact hashes and all command outcomes will be recorded
in the external HANDOFF.md and final-state.json after the final local commit.

## Completed baseline checkpoint and backfill handoff

Checkpoint 1 is complete. The corrected **fresh clean old build passed**:
`lake -f .h62-migrate-corpus-old.toml --no-cache build SolidityCorpus`, with
`LEAN_NUM_THREADS=1`, worker `-j1`, no AS cap, existing hard VM cap and headroom
policy above. Wall: **3983.395159041 seconds**; sampled aggregate RSS:
**5872992256 bytes (5.47 GiB)**. Exit 0, no resource stop. The output directory
was verified absent before launch, artifact caches were disabled, and all
base-tracked current input bytes were fingerprinted before timing.
Input tree fingerprint:
`5ceac4d6694ee027a20fbe53ce94581319825a52c893e68fe6fce5363d47a50e`.
Common configuration policy fingerprint:
`0661d945df37f0cd5c2e8c14b9bcf6229512dfec9f57ee73b142b3ea984fcd71`.
Clean means fresh project outputs with artifact-cache retrieval disabled;
OS page-cache contents were not purged. RSS is sampled, not a kernel-exact
simultaneous high-water measurement.

All nine assigned modules and the standard corpus root passed. The compiler's
setup manifests exactly match the scanner's 340-module closure. The root also
checks 13 additional validation dependencies; all have unique migration owners
and are included separately in the dependency report. All 354 timed modules
were below 300 seconds; maximum: Derived20, 181 seconds.

The generated old-interface probe passed complete one-file MCP diagnostics and
exported **703 environment constants owned by the nine corpus modules**,
including compiler-generated auxiliary constants. These are not 703 source
functions. JSONL SHA256:
`fc7fec3db0468a46df98246a685fe242cde1042f32e41349ed4fe5457dc10db4`.
Per-constant representation hashes and module counts remain off Git. Expression
representation hashes are baseline evidence; no cross-version equivalence is
claimed while new imports fail. The generated probe is test-only, ignored by
Git, and recreated by export-interfaces.py; no production registration is
requested and no library/module-map fragment was modified.

`bash scripts/check-corpus.sh` also passed under the old private toolchain and
configuration: 774 obligations, no source/verdict/scoreboard drift, exit 0;
38.878758036 seconds and 1087324160 sampled RSS bytes. This is a separate warm
acceptance check, not the clean benchmark. It preserves the scoped 639 rows and
the full table (including four Net proof mappings outside Corpus). Kernel proofs
and interpreter outcome pins retain their existing boundaries; this is not
Solidity compiler/extractor or EVM equivalence evidence.

Final static checks pass: layers, generated roots/fragments, whitespace, original
corpus/toolchain/lakefile equality to the base, local report links, and byte-stable
summary regeneration. New Lean source contains five finite examples, zero new
axiom declarations, zero sorry, zero native_decide and zero heartbeat raises.
Original declarations, premises, exclusions and frozen statements touched: zero.

The old result is valid; the new build still exits 1. compare.py therefore emits
BLOCKED with both deltas null. The failed 60-second new build must never be
reported as a speedup. The preliminary KeySort RSS regression remains escalated
for migrate-root-gate. Full successful new builds, new acceptance/final gates,
new type hashes, and an admissible paired comparison remain outstanding.

| Queue checkpoint | State |
|---|---|
| 1: census, pinned old compatibility and clean measurement | done |
| 2: exact official new pin and directory adaptation | blocked on two owner migrations |
| 3: all new modules, final gates and comparison | blocked |
| 4: reviewable overlay and root-gate evidence | partial: artifacts prepared; new interface/gate evidence absent |

Backfill completed: full source/case/dependency census, adversarial negative
controls, five old-toolchain finite fixture proofs, deterministic regeneration,
source/proof-budget preservation checks, and reproducible timing/interface
instrumentation. Additional production work requires the named owner inputs;
there is no authorized substitute for those dependencies.

## Reproduction and continuation

Use the original VM context
`ccarenv_b64_Y2NhcmVudl80NzJkZGIzYjRmNDQ4MTkxODkzMTUzNDBmZjRiNDYzOQ`,
the existing launcher goal identified above, this same branch, and the committed
head recorded in external final-state.json. No replacement goal/thread was
created. The coordinator should resume the original goal after supplying the
exact owner migrations; this is a fresh-thread handoff, not completion.

Recreate testing configuration with prepare-config.py MODE OFFICIAL_DIR
EVIDENCE_DIR under the repository writer lock. Use a fresh evidence/output
location for a new clean measurement; existing benchmark output is intentionally
refused. serial-toolchain.py OFFICIAL_DIR PRIVATE_SYSROOT creates a private
symlink tree over the unchanged official release. Set LEAN_SYSROOT to that tree,
LAKE_OVERRIDE_LEAN=true, and LEAN_NUM_THREADS=1. For MCP also set
H62_LAKE_WRAPPER to the generated commands-MODE/lake wrapper and put that command
directory first on PATH, preserving the private configuration in setup-file.

The actual old benchmark command, excluding its safe environment prefix, is:

```sh
python3 scripts/h62/item6/migrate-corpus/bounded.py \
  --out /workspace/migrate-corpus-evidence/clean-old-retry \
  --benchmark-config .h62-migrate-corpus-old.toml -- \
  /workspace/.setup/tools/lean-4.24.0-linux/bin/lake \
  -f .h62-migrate-corpus-old.toml --no-cache build SolidityCorpus
```

That output path now exists and must be preserved, not reused as a clean run.
The corresponding new command and exact environments/versions are recorded in
HANDOFF.md and the gate result JSONs. Paired comparison requires matching
source/config/cache/resource provenance and successful builds. Source-changing
owner overlays require re-establishing comparable workloads, not disabling the
provenance check. Any regression escalates; strictly above 10% wall slowdown
stops. No root toolchain edit, integration, push, freeze announcement or cut-over
is authorized to this lane.

All bulky census, case, module-time, type-expression and build outputs remain
outside Git. Deterministic generators are committed; final SHA256SUMS covers
saved artifacts and evidence. Absolute final artifact paths and committed head
are in the external handoff and CLOUDVM-RESULT.

## Final independent milestone review

The final finder and skeptic independently checked the completed old baseline,
all 340 compiler/scanner modules, unique ownership of 13 validation extras,
703 old constants and their hash, distinct 354 module timings, deterministic old
acceptance, scope and proof boundaries. Neither used Lean/server or wrote files.
Both found no remaining concrete defect. Both explicitly retained states
**done / blocked / blocked / partial**; neither approved a completed migration.
Export/checksum verification is recorded in external final-state.json and
HANDOFF.md after this local commit. No private root TOML is exported.
