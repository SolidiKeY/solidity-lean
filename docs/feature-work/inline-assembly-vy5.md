# VY5: assembly composition and differential backfill

Status: **partial implementation checkpoint; full lane blocked on concrete
prerequisites**. No general Yul support or whole-pipeline theorem is claimed.

Repository: `/workspace/solidity-lean`. Base:
`0b078cefaf7daad79007b87b72df64eb6936420f`. Branch:
`codex/solidity-inline-assembly5-20261031/vy5-composition`.
The exact committed head is recorded in the external handoff after committing,
avoiding a self-referential commit ID. The previous `work` branch at
`2fe1f8932f96be15b00df03ba2cde46f64a87758` and existing caches were preserved.
The pinned base was fetched by exact SHA and its direct-parent relationship
verified. No other lane was integrated or modified.

## Queue accounting

| Item | Result and remaining obligation |
|---|---|
| Work 1: Y10 composition | Pending. The G03 extension has 24 explicit pending obligations, six constructor combinations and exact dependency/owner validation. No concrete V16/VY3/VY4 assembly interfaces exist in this tree. No residual predicate or generic certificate wrapper substitutes for them. |
| Work 2: G52 assembly differential harness | Partial. All 80 pinned upstream fixtures are inventoried and probed in both pipelines, optimizer off/on. Raw compiler input/output, hashes and original expectations are retained. The existing bounded EVM adapter is reused unchanged for upstream-required default profiles; its unsupported cases remain blocked. Lean comparison, full memory/world observations and source correspondence are pending. |
| Work 3: whole-pipeline witnesses/closure | Pending. External reference controls cover all six combinations, success/failure, malformed import, incorrect opcode, constructor failure, dirty bits, allocation, storage, logs and rollback. Three narrow recognizer-refusal equalities are kernel checked. These are not whole-pipeline witnesses. Final joint imports and composition remain open. |
| Backfill A | Inventory, byte-preserving extraction, fixture parser reuse, compiler runner/provenance validation and local mocks implemented; actual pinned compiler/EVM output retained. No V17 or legacy generated output was copied/replaced. Full observation adapters remain pending. |
| Backfill B | Independent expected outcomes, advisory policy controls, constructor combinations, exact child/owner dependencies and missing/stale-proof rejection implemented. Closure is intentionally rejected until reviewed concrete interfaces can replace pending entries. Wire-up remains pending. |

The human-approved [YQ1–YQ7 decisions](../solidity-scope.md#inline-assembly-decisions-2026-10-31)
are implementation directions. The manifest still reports the actual excluded
`inlineAssembly` row with empty evidence. The pre-existing importer still
recognizes only declaration-sensitive `memoryRethrow?`; no source definition,
frontend dispatch, core state or owner prerequisite was rewritten.

## Artifacts and reproduction

Lane-owned files:

- [Pinned extraction](../../scripts/yul-composition/inventory.py): standard library only; validates the pinned archive and every selected file before writing raw bytes. Populated extraction drift is rejected.
- [Harness](../../scripts/yul-composition/harness.mjs): actual solc AST preflight, raw input/output preservation, compiler/source/settings/output hashes, original fixture settings/expectations, both-pipeline probes and optional bounded reference execution.
- [Fixtures](../../tests/yul-composition/fixtures.json): independent outcomes for six combinations plus positive/negative controls. The incorrect-opcode control retains the source expectation 42, then deliberately substitutes a SUB target slice that returns 40. A separate corrupted target always reverts. Both remain recorded mismatches.
- [Ledger](../../tests/yul-composition/ledger.json): supplement to G03, with real source-constructor names checked and no closed assembly row.
- [Finite proof catalog](../../tests/yul-composition/proof-controls.json): source/signature/dependency hashes reject stale or missing recognizer controls; the separate kernel gate is mandatory.
- [AST feature collector](../../scripts/yul-composition/coverage.mjs): provenance-bound presence inventory for actual manifest rows, explicitly without semantic/admission coverage.
- [Mock tests](../../scripts/yul-composition/harness.test.mjs) and [inventory tests](../../scripts/yul-composition/inventory_test.py).
- [Rethrow controls](../../tests/yul-composition/RethrowControls.lean): isolated boundary tests, outside public core imports.

Run under the required writer lock and hard resource scope:

```sh
python3 scripts/yul-composition/inventory.py --extract /workspace/vy5-composition/corpus --out /workspace/vy5-composition/corpus/inventory.json
node --test --test-concurrency=1 scripts/yul-composition/harness.test.mjs scripts/yul-composition/coverage.test.mjs
python3 scripts/yul-composition/inventory_test.py
node scripts/yul-composition/harness.mjs --compiler /workspace/vy5-composition/soljson-v0.8.38+commit.1835d247.js --corpus /workspace/vy5-composition/corpus --out /workspace/vy5-composition/reviewed-reference --execute-reference --optimizer-also
node scripts/yul-composition/coverage.mjs /workspace/vy5-composition/reviewed-reference /workspace/vy5-composition/feature-coverage.json
```

Use the exact compiler SHA-256
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`,
version `0.8.38+commit.1835d247.Emscripten.clang`, upstream revision
`1835d247de183f23e7b0e2bc4a50732af525b77c`, Osaka. Archive SHA-256:
`9200f2a26b08be5b77faf877c44f5cfbf5ea95f1bccc45dae559d2fbc7cefb2d`.
Original fixtures/expectations are immutable; compiler probes may be outside
an upstream EVM-version constraint and never become upstream matches.
`slotnum_pre_amsterdam_function.sol` retains the existing adapter's unsupported
`<amsterdam` constraint rather than silently inventing its interpretation.

## Actual coverage and proof boundary

The reference matrix has 416 compiler probes (80 upstream + 24 lane fixtures,
two pipelines, optimizer off/on): 72 observation matches, eight deliberate
corrupted-target mismatches, four precise missing-import diagnostic matches,
303 pending and 29 blocked rows. An exit 0 requires every owned local control
in every requested profile (including precise refusal, allocation sanity and
negative-target sensitivity), without missing/duplicate rows; it does not mean these pending/blocked rows passed.
The unchanged upstream adapter returned 32 working and 40 blocked fixture
reports (64 working and 80 blocked pipeline variants); eight fixture-level
adapter failures remain on their probe rows. It runs only upstream-required
unoptimized profiles, separately from the four-way compilation probes.

The actual execution adapter observes exact success/failure, return/revert
bytes, literal raw logs and deployment addresses (plus a relative `self`
projection for independent log oracles), selected deployed-account storage slots,
runtime installation bytes and reverted writes/logs. Memory effects are
observed through these outputs. It does not compare raw final VM memory,
complete account worlds/balances/nonces, adversarial callees or source-state
writeback. Mock world/memory comparison tests only test the comparator.
Reference host limits stay at the existing 100,000,000 message gas and
5,000,000 steps; host/instruction-budget exhaustion and unknown engine
exceptions are blocked. Actual EVM out-of-gas/stack-overflow are machine failure
observations, and cannot satisfy the local controls that specifically expect
`revert`. Non-memory-safe/compiler-dependent/callcode controls are advisory
AST policy scans, not evidence the absent VY1 importer implements them.
The canonical exception remains owned by the existing importer.

Dirty high bits are independently observed as `0x142` when copied directly
inside assembly and `0x42` through a Solidity uint8 return, in each tested
pipeline/settings pair. Allocation pointers and layout sanity are recorded
individually, without requiring cross-pipeline equality or asserting YQ3
refinement. Runtime installation checks are finite reference evidence only.

The modifier fixture combines an assembly `x.slot` write with Solidity reads
and post-body writes; unchecked combines Solidity overflow with assembly;
loops exercise for/while/do-while/break/continue. Separate try success,
plain/bytes/Error/Panic catches, nested creation and ordered Yul-log/Solidity-emit
controls retain their independent outcomes. The feature collector records
16 actual manifest rows across 416 AST probes, all with assembly semantic
coverage pending and zero assembly obligations closed.

Corrupted targets are explicitly separate from unmodified solc evidence.
Original installed bytes are checked and retained. The incorrect-opcode control
first validates the specified ADD slice `0x60016029015f5260205ff3` against 42,
then replaces it with SUB slice `0x60016029035f5260205ff3`; only return bytes
must differ. The always-revert control first validates the original compiler
runtime against 42, then installs `0x5f5ffd`; failure, bytes and exception must
differ, with actual exception `revert`. Every replacement is read back, and
original compiler bytes and their hash, reference bytes and successful preview,
and mutant bytes/hash/observations are retained. Neither
mutation is presented as an unmodified compiler output.

Three exact theorem signatures, all without premises, live in namespace
`Solidity.Yul.Composition.RethrowControls`:

```lean
extra_statement : memoryRethrow? [dataDecl] (block [stmt 32, stmt 32] [ref 7, ref 7]) = none
different_names : memoryRethrow? [dataDecl] (block [stmt 32 "other"] [ref 7, ref 7]) = none
malformed : memoryRethrow? [dataDecl] (Json.mkObj []) = none
```

Each is proved by kernel reduction and reports only `propext`,
`Classical.choice`, `Quot.sound` inherited through the recognizer. Seven
runtime `#guard` checks cover the positive canonical exception, absent/mismatched
declarations, wrong offset/location/type and slot references. Those paths cross
the existing opaque JSON numeric parser and are not presented as kernel proofs.
Failed `decide`/`rfl` experiments are retained in evidence, including their error
placeholders; no such placeholder or new axiom is in the passing source.
No budgets, semantic premises, observations or expected outputs were weakened.

## Concrete prerequisites still required

The ledger maps Y01/Y01.02/Y02/Y03/Y09.01 to VY1 (intrinsic scope/arity,
checked parsing, semantics and word rules); Y04/Y05/Y06/Y09.02 to VY2
(physical views, V04b MemOK, memory-safe preservation, allocation refinement
and V10/V11 layout agreement); Y08.01/.02 to VY3 (actual V12 lowering and V15
opcode/EVM correspondence); Y07.01/.02/Y09.03 to VY4 (actual V13/G42 world,
creation, returndata, rollback and log/emit observation amendment).
V04 source semantics and V04b MemOK remain explicit inputs. V16 must supply
G48 source coverage, G49.01 backend composition, G49.02 runtime theorem,
G49.03 failure/nonvacuity/progress, G50.01 deployment, G50.02 transactions,
G51.01 soundness and G51.02 specification transfer. `G51.interface` is a
prerequisite interface obligation distinct from final G51.01, avoiding a cycle.

Existing `Solidity/Roadmap/Contracts.lean` provides contract *types*:
`Admission.sound/complete`, `Lowering.dom/agrees/cert`,
`Compilation`, `Execution` and `PublicCorrectness` (coverage, both pipelines,
environment onto, fixed/session agreement, creation table, hash preimages,
refinement and reachable decode). These are not assembly instances.
Existing Bridge instruction-boundary composition explicitly excludes source
storage refinement and does not supply VY3/Y10 correctness.
The final proof must instantiate the actual contracts and discharge their real
hash/resource/environment premises, allocation/log amendments and every source
constructor. No full theorem signature is fabricated here.

## Validation and resources

Actual toolchain: Lean 4.24.0, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`; Lake 5.0.0-src+797c613.
Docker image digest:
`sha256:fe81560990fae86dc4743202b2cb4d3df98d0bcf949173cecef15ce1127ef852`.
Each heavy invocation is serial, with `LEAN_NUM_THREADS=1`, Lean `-j1`,
Docker memory 12 GiB and memory+swap 12 GiB (cgroup swap max 0). The
attached outer cgroup has a 16 GiB hard limit and no host swap. No additional
12 GiB OS reservation was imposed. OS availability, aggregate RSS, disk and
kernel memory/OOM counters are retained. Private caches remain on disk.

| Gate | Recorded result |
|---|---|
| Exact base/branch/ancestry | Pass; original branch preserved. |
| KeySort | `lake -f lakefile.vy5.toml build Solidity.KeySort`: exit 0, two jobs; 25,776,128-byte cgroup peak, zero OOM. Temporary config supplies Lean `-j1`; tracked config unchanged. Initial unsupported Lake `-j1` attempt retained as failure. |
| Focused affected build | Body and its ten prerequisites: 11 jobs passed; existing AST unused-variable warning retained. |
| Rethrow per-file/axioms | `final-focused.log`: three scoped axiom reports plus seven guards pass. Installed local MCP 0.29.0 was later discovered and invoked through stdio: `final-mcp.log` reports success, partial=false, no errors/dependency failures. Its nonfatal Pydantic/shutdown warnings remain raw. No MCP/build overlap. |
| Mock/inventory | 31 JavaScript tests and two Python tests pass; `reviewed-backfill.log`. |
| Four-way reference | Exit 0 with eight required corrupted-target mismatches; 468,725,760-byte sampled aggregate RSS, 501,911,552-byte cgroup peak, zero OOM. |
| Full repository policy | `./run-lean.sh` via the untracked serial-config wrapper: exit 0, 981 library jobs, 262 TestSuite jobs; 377 taclets / 131 read annotations match the frozen rules. Peak sampled aggregate RSS 11,558,801,408 bytes; cgroup peak exactly 12 GiB, max/reclaim events 3438, zero OOM. Minimum observed OS availability 5,388,128,256 bytes. |
| Full public assembly closure | Pending missing actual V16/VY3/VY4 interfaces and G01 amendments. |
| Base/head comparisons | Layer check passes. Documentation checker retains the same 48 missing references; original G03 checker retains the same stale-generated-output failure. Raw base/head outputs are identical; no unrelated generated output repaired. Final newly tracked paths/links and scoped checks are recorded in the handoff. |

## Independent reviews

Separate read-only finder and skeptic reviewed implementation and subsequent
fixes, without Lean server/builds. Confirmed findings fixed: stale settings
metadata, mutable dependency/owner edges, vacuous negative controls, ignored
nested reference mismatches, omitted expected logs, missing raw replay compiles,
G51 dependency cycle, legacy-success gating of viaIR reference execution,
missing emitter identity, weak loop/modifier/constructor controls, deployment
exception classification, snapshot metadata, engine/host provenance and precise
malformed-import diagnostics. A real log run exposed object-key-order comparison;
the failed output was retained, comparator corrected and regression added.
The final expanded source is independently re-reviewed before committing; results and any remaining limitations are in the handoff. Every owned local control/profile is now required, and source-bound finite-proof registrations reject staleness without closing assembly obligations.

## Handoff locations

Absolute artifact root: `/workspace/vy5-composition`.
Evidence directory: `/workspace/vy5-composition/evidence`.
Raw final four-way reports: `/workspace/vy5-composition/reviewed-reference`.
Feature-row evidence: `/workspace/vy5-composition/feature-coverage.json`.
Pinned extraction: `/workspace/vy5-composition/corpus`.
Final handoff, original patch, Git bundle and checksum manifest are generated
at that root after committing. They contain full head/base/branch identities,
commands, exits, raw failures, resource/review evidence and all pending work.
The full assignment remains unfinished; no push, PR or merge is authorized.
