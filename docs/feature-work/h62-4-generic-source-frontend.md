# H62 item 4: generic Source/Frontend controls

Status: **blocked, assignment incomplete**. Branch
`codex/solidity-h62-4-20261106/generic-source-frontend` starts at exact base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4` in `/workspace/solidity-lean`.
The original clean `work` branch was preserved. Fetch verified the base is an
ancestor of the published `origin/master`; no push, merge or PR was performed.
The supplied persistent goal remains the only goal; `get_goal` is not exposed,
as the coordinator explicitly permits. No replacement goal/thread was created.

Only the exclusive `tests/h62/item4/generic-source-frontend/`,
`scripts/h62/item4/generic-source-frontend/` and this document changed.
All owned originals are read-only. No interface, premise, observation,
exclusion, generated root, module map, axiom pin or proof budget changed.

## Queue and inventory

| Checkpoint | State | Evidence and remaining work |
|---|---|---|
| 1. Census and audit match | Partial | Complete file/source inventory saved, lexical declaration headers and exact file hashes; elaborated statement/type inventory remains pending. |
| 2. Intrinsic lemma and typed table | Partial | Generic proof and typed witnesses pass; original 45-row table is generated but blocked/unvalidated. Numeric consolidation is not proved. |
| 3. Correspondence/refusals/reproduction | Partial | Generic semantic correspondence and actual-refusal theorem pass; static reproduction and mutation regressions pass. Real parser/table adapters and full acceptance remain blocked. |
| 4. Matched timing and original inventory | Blocked | Full source inventory retained. The real 45-case timing baseline cannot import FixtureData; no timing delta or speedup is established. |

The census retains all **490** Frontend Lean files and **7,576** enumerated
term declarations, including anonymous examples. All file bytes are hashed.
Conservative path labels identify **136** control-candidate files and **1,645**
declarations; those labels are not a semantic claim that other files contain
no controls. Header hashes are lexical source hashes, **not** Lean environment
type hashes. Equation/approximate boundaries are labelled rather than silently
represented as elaborated types. Whole-file hashes and the unchanged-original
Git check retain stronger byte-preservation evidence.

Audit item 16: all **45** `StatementGrammarH28/FixtureControls/Case00` through
`Case44` theorems and all **30** NumericLiteralProofs WordTable parts containing
**439** theorems are inventoried. The full original per-case/declaration list
is `/workspace/h62-runtime/evidence/frontend-inventory.json` (3.3 MiB, off git).
Its SHA256 is
`06c25d329befbce1872769a3eafaa46fe69b439a1fab27b9b37a2f12a78cc64f`.
Every original fixture is also retained by exact name in the generated typed
table and exact source proposition in the owner proposal.

The 45-case verdict/profile inventory is
`/workspace/h62-runtime/evidence/statement-case-inventory.json`.
Negative cases are 28–41 inclusive (14); out-of-profile cases are 22, 23, 27.
There are 31 expected accepts; profile refusal is distinct from syntax refusal.
No cases were removed, padded or reclassified. `requireTyped` duplicates live
in `Solidity/Source/Progress/{LiteralBuiltinControls,BuiltinControls}.lean`,
outside this sole Frontend scope; they are recorded for their owner, not claimed.
Audit items 9/11 target Backend/Evm twins/shared lemmas and do not authorize
those families here. H55 retains Yul Raw/vector generation; no duplicate
producer or generator was introduced.

## Implemented additive work

[Core](../../tests/h62/item4/generic-source-frontend/Core.lean) imports only the
existing intrinsic Source syntax. `check_iff` proves Boolean control/semantic
specification correspondence for arbitrary parser results, syntax category,
profile and tag observers. Its accepted tree is `Syn category`; no alternate
untyped AST is introduced. `negative_requires_refusal` proves negative checks
require an actual error result. `Row` stores an existing fixture with its exact
checker proposition, without copying its schema.

[CoreControls](../../tests/h62/item4/generic-source-frontend/CoreControls.lean)
checks accepted trees, profile mismatch, missing tags, rejection of an accepted
tree by a negative fixture, failure on unexpected refusal and expected refusal.
It supplies inhabited accepted/refused semantic witnesses and a typed row.
These are **generic controls**, not proofs that the actual parser accepts the
original sources.

The deterministic [generator](../../scripts/h62/item4/generic-source-frontend/generate.py)
produces [FixtureTable](../../tests/h62/item4/generic-source-frontend/FixtureTable.lean)
and [owner proposal](../../tests/h62/item4/generic-source-frontend/owner-migration-proposal.json).
Each of the 45 original finite kernel decisions remains in its own theorem,
retaining the original per-declaration budget. The table collects those
certificates and supplies exact original propositions as instances. The
structural semantic proof is separate; it is not replaced by deciding a table.
These generated parser-dependent proofs/adapters are **not validated** yet.
The proposed owner imports have no apparent source-level cycle; Lean validation
and measured performance remain required.

No authored `sorry`, new axiom, `native_decide`, trust option or raised
`maxHeartbeats` is present. Passing printed axiom sets are:

| Declaration | Axioms |
|---|---|
| `check_iff`, `Controls.accepted_witness` | `propext`, `Quot.sound` |
| `negative_requires_refusal`, `Controls.refused_witness` | `propext` |
| `row_checked` | none |

The generic proofs use structural cases and explicit simplifier lists.
Finite `decide +kernel` certificates are exactly the original checker facts;
none are claimed to prove universal parser completeness or AST equality.

## Runtime, gates and proof boundary

Coordinator inputs in `/workspace/h62-coordinator-inputs/` passed all five
published SHA256 checks. The required official Lean 4.35.0 release archive
matches `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Actual versions:

- Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release.
- Lake 5.0.0-src+eb6cafb (Lean 4.35.0).

No v4.24/master cache was used. Fresh source imports build into
`/workspace/h62-runtime/objects`, using the explicit pinned compiler.
The VM has a 16 GiB cgroup memory cap and no active swap. Each heavy job uses
`LEAN_NUM_THREADS=1`, explicit `-j1`, `--tstack=131072`, a hard 12 GiB virtual
memory limit, a 4 GiB effective reserve (minimum of host available memory and cgroup remaining memory) and a 300-second timeout.
The address-space cap is conservative and may stop sooner than an RSS cap.
The runner acquires the repository writer lock and signals only its own process
group. No systemd-run was used. No exposed Lean MCP tool is available; bounded
per-file compiler diagnostics were used rather than starting a v4.24 LSP.

The exact commands, exits and log paths for the passing packet are in
`/workspace/h62-runtime/evidence/gate-results.json`. Reproduce with:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 scripts/h62/item4/generic-source-frontend/validate.py
```

| Gate command (from repository root) | Outcome / decisive output |
|---|---|
| `python3 scripts/h62/item4/generic-source-frontend/test_census.py` | Pass, 10 tests |
| `python3 scripts/h62/item4/generic-source-frontend/test_bounds.py` | Pass, 2 cgroup/host headroom regressions |
| `python3 scripts/h62/item4/generic-source-frontend/test_generate.py` | Pass, 4 tests; missing/weakened originals refused |
| `python3 scripts/h62/item4/generic-source-frontend/census.py --output /workspace/h62-runtime/evidence/frontend-inventory.json --check` | Pass, 490 files / 7,576 declarations, matching digest |
| `python3 scripts/h62/item4/generic-source-frontend/generate.py --check` | Pass, `GENERATION_MATCH 45 original statements; no originals modified` |
| `python3 scripts/h62/item4/generic-source-frontend/acceptance.py --inventory /workspace/h62-runtime/evidence/frontend-inventory.json --output /workspace/h62-runtime/evidence/static-acceptance.json` | Pass, `STATIC_ACCEPTANCE_PASS`, `runtime_gate_pass: false` |
| `python3 scripts/h62/item4/generic-source-frontend/bounded.py --log /workspace/h62-runtime/evidence/keysort-final.log -- /workspace/h62-runtime/toolchains/lean-4.35.0-linux/bin/lean -j1 --tstack=131072 Solidity/KeySort.lean` | Pass, exit 0, 1.767103 seconds; silent compiler output |
| `python3 scripts/h62/item4/generic-source-frontend/build_closure.py tests.h62.item4.generic-source-frontend.CoreControls` | Pass, Source.Syntax + Core + CoreControls; printed axiom sets above |
| `node scripts/check-layers.mjs` | Pass, 857 core modules, zero elaborator/checked-parser reachability |
| `bash scripts/coord-tools/register.sh --check` | Pass, no generated-root edits |
| `bash scripts/coord-tools/fragments.sh --check` | Pass, no fragment/map/pin edits |
| `python3 scripts/h62/item4/generic-source-frontend/build_closure.py Solidity.Frontend.StatementGrammarH28.FixtureData` | **Fail**, unchanged Token line 38: `String.ofByteArray` needs 2 fields; supplied `List Char`, expected ByteArray |
| `python3 scripts/h62/item4/generic-source-frontend/measure.py --baseline /workspace/h62-runtime/evidence/baseline-command.json --candidate /workspace/h62-runtime/evidence/candidate-command.json --output /workspace/h62-runtime/evidence/fixture-batch-timing.json` | **Blocked**, baseline cannot import FixtureData; `delta_percent: null` |
| `./run-lean.sh` with pinned serial migration configuration, full affected/table/adapters/trust gates | Pending the real parser migration and owner integration; not executed/passed |

The migration failure is retained at
`/workspace/h62-runtime/evidence/build/Solidity.Frontend.Checked.Token.log`.
KeySort success is only the prerequisite, not RUNTIME_GATE_PASS.
The full acceptance switch deliberately refuses promotion while these known
required obligations remain; it is not an implemented completion detector.
The static tests validate tooling, not Lean semantics. The passing Core
compiler checks and printed axiom sets are the semantic proof evidence.

Before proposing consolidation, checking slowdown was explicitly warned about
and fixture history inspected (`661311b08474ee6af539ab39f11af7e06e1c0855`).
[measure.py](../../scripts/h62/item4/generic-source-frontend/measure.py) compares
alternating, bounded checks with the same source/import snapshots and rejects
>10% slowdown. Its baseline generator concatenates all 45 original declarations
without importing precompiled case proofs; the candidate checks the new table.
This is a batch proof-cost comparison, not original per-module timing closure.
Full original per-module timings and candidate adapter timings are still due.
The initial single-case import diagnostic is retained as diagnostic evidence
only; it is not a valid whole-workload comparison. No failed import timing is
reported as a speedup. Timing delta: **unavailable**.

## Reviews and disposition

Independent read-only finder and skeptic reviews used no Lean server/builds
and made no writes. They found and prompted fixes for nested/default `:=`
header truncation, attribute/opaque omission, missing-scope acceptance,
`where` token boundaries, `||` misclassification, type-level `let` and the
combined-table proof budget, cgroup headroom guard and complete object-set timing snapshots. Scanner/generator/resource regressions cover the resolved boundary cases. Older diagnostic logs used host-only available-memory samples; final gates use the corrected effective reserve. Small historical proofs remain below both limits.
Reviewers explicitly retained the source-vs-elaborated hash boundary and the
pending real-table/numeric/timing obligations. Final review evidence is saved
in `/workspace/h62-runtime/evidence/reviews.json`; no full checkpoint is
claimed done by those source reviews.

## Owner requests and resumption

[Exact owner requests](../../tests/h62/item4/generic-source-frontend/owner-requests.json)
retain these typed blockers:

- **B-MIGRATION-TOKEN**, producer dependency: frontend migration owner must
  publish the compatible `Checked/Token.lean:38` repair, plus subsequent
  dependency migration fixes. This lane must not change that owned original.
- **B-OWNER**, owner agreement: H28-STATEMENT-GRAMMAR must approve/apply the
  exact 45-file adapter proposal after validation/timing. SOL-NL owns the
  30 WordTable parts and umbrella; their 439-prefix generic proof remains open.
- **B-WORDTABLE**, implementation pending: inventorying preserves all prefix
  facts but does not prove numeric consolidation.
- **B-FULL-GATES**, validation pending: real table/adapters, elaborated type
  hashes, full axiom/trust inventory, final affected run-lean and matched timings.

No owner relay agreement has arrived. `relay.sh` was not present in the
discovered checkout/tooling. The coordinator retrieves the saved exact-file
requests; no outbound message or ownership permission was invented.
[Registration fragments](../../tests/h62/item4/generic-source-frontend/registration-proposal.json)
are unapplied proposals; no central root/map change is authorized here.

Resume this **same VM/branch/goal** after the owner publishes compatible
inputs. Revalidate pinned toolchain and original hashes; build actual dependency
closure, prove/check table and exact adapters, finish the numeric generic proof,
run real acceptance and both batch/per-module timing gates, stop for >10%
slowdown, get independent reviews and commit each reviewable checkpoint.
Owner alone applies approved migrations. Full assignment remains unfinished.
The useful unblocked backfill increments (census, intrinsic lemma/witnesses,
reproduction acceptance, bounded measurement tooling) are ready for a fresh
coordinator thread handoff; this worker must not self-launch another thread.

## Scoped successor recut at b7c3cc511

This increment preserves every fixture statement and all 45 original owner
control files. It repairs checker_exact by splitting on the actual parser
result and rewriting the existing checker/profile equalities. The published
statementFixtureCheck_profile bridge preserves the original Syn.rejections
observation. The deterministic generator emits the same proof repair.

The annotation guard tests reject changed proofs, unexpected paths, modes and
untracked Frontend files. Their historical census base remains unchanged; newer
published Frontend changes can still block full static acceptance. No census or
central axiom pin is regenerated by this increment. Previous live timing results
belong to the preserved c16efd4ed checkpoint and are not fresh recut evidence.
