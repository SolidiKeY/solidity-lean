# H62 item 2: audit-memory-operations

Status: **blocked; full assignment incomplete**. No checkpoint is complete.
This is reviewed additive backfill, not acceptance of the frozen assignment.

## Checkout and authorization

- Batch: `solidity-h62-2-20261106`; owner: `audit-memory-operations`.
- Repository: `/workspace/audit-memory-operations`.
- Branch: `codex/solidity-h62-2-20261106/audit-memory-operations`.
- Frozen base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
- Original clean checkout `/workspace/solidity-lean`, branch `work`, head
  `6cf853aea0417155aca29ddb91f1767d3f3a3cc4`, was preserved.
- Fetched published base and `origin/master`; base ancestry verified before
  creating isolated worktree. No remote task branch existed. No push or merge.
- Coordinator inputs in `/workspace/h62-coordinator-inputs` passed all five
  supplied SHA256 checks. Optional `get_goal` is not exposed; no new goal created.
- All tracked changes stay within the three authorized paths. No existing
  producer files, interfaces, roots, module maps, axiom pins, or toolchain pins
  were edited. No H55 work duplicated. No registration performed.

## Checkpoint ledger

| Checkpoint | Status | Remaining obligations |
|---|---|---|
| 1. Exact frozen inventory and owners | partial | Kernel FQNs/signatures, implicit/section hypotheses, exact record-field census, producer owner per statement, global versus per-input classification |
| 2. Simultaneous witnesses | partial/blocked | Almost all mapped statements remain without verified witnesses; small passing entry fixture below is not general coverage |
| 3. Supported compiler success/totality | blocked | Actual compiler contracts, reject-all and always-revert compiler controls, observable gas/fork/failure boundaries |
| 4. Fidelity and coverage verification | blocked | Exact-once elaborated census, witness reconciliation, full affected/final validation and owner report |

No statement was weakened by this backfill. The H70 source-supported legacy V1 capacity finding below retains its blocker; kernel replay is still pending.
No statement repair, new premise, axiom, trust shortcut, or budget increase was
introduced. There are **zero new `sorry`, `axiom`, or `native_decide` commands**.
Failed dependency elaborations print temporary `sorryAx` in error diagnostics;
those are failed checks and are never accepted as proofs or imported.

## Deterministic source census (backfill item 1)

Generator: `scripts/h62/item2/audit-memory-operations/census.py`.
Bulk JSON remains outside git at `/workspace/h62-audit-memory-evidence/census.json`.
It expands the frozen module map (including braces, globs and already-prefixed
paths), yielding **550 modules, 3,932 theorem/lemma source regions and 209
structure/class regions**, with no missing paths and no duplicate source
identities. All 4,141 rows remain explicitly **unverified**. The source-qualified
name is not a kernel FQN, especially for private declarations. Full source
regions and their offsets/hashes preserve conclusion-local `let` bindings.

This deliberately includes unconditional/private candidates and whole records;
it neither excludes statements based on filename nor asserts that every row has
propositional hypotheses. No exact signature, exact field count, inferred owner,
or automatic witness credit is claimed. Global record inhabitation and per-input
feasibility still require separate kernel verification and exact-once accounting.
The census has zero automatically verified witnesses. The separately checked
fixture below is not silently used to relabel its rows.

Acceptance: `PYTHONDONTWRITEBYTECODE=1 python3 tests/h62/item2/audit-memory-operations/check-census.py`.
It exercises confirmed review regressions: nested comments, conclusion-local
lets, private name collisions, record/definition boundaries, exact region offsets,
all 550 module paths, and fail-closed missing build target. Two generated census
files compared byte-for-byte equal. Bulk manifest is committed under the owned
tests directory; full external checksum manifest accompanies the handoff.

## Passing additive witness fixture (backfill item 2)

`tests/h62/item2/audit-memory-operations/EntryAudit.lean` imports unchanged
`Solidity.Backend.AbiEntry.CompositionInterface` and `EntryComposition`.
This ABI family is included in the assigned memory-operations module map.

Exact targeted frozen names and owner:

| Frozen statement | Evidence | Producer owner |
|---|---|---|
| `Solidity.Backend.AbiEntry.Interface.EntryCompositionCertificate` | `compositionCertificate` inhabits both global fields for the same append operation | V13, G40/G41 ABI-world family |
| `Solidity.Backend.AbiEntry.EntryComposition.prefix_failure` | Concrete nonempty prefix, same input/fuel/cursor/error, actual frozen theorem application | V13 |
| `Solidity.Backend.AbiEntry.EntryComposition.tail_failure` | Joint dependent hypotheses with same entries/reached cursor; empty and nonempty successful prefix cases; actual frozen theorem applications | V13 |

Kernel `#check @...` output for both record projections and both frozen theorems
is in the final fixture log. The nonempty prefix advances the head by 32 bytes;
an invalid Boolean in the tail rejects, while allocated cursor 7 is retained.
`word_classes` and `word_location_hypothesis` provide nonempty per-input
feasibility controls for the related RawFree family; no successful import or
application of the failing RawFree module is claimed.

`entry_success` decodes an actual Boolean entry from 36 zero bytes at fuel 2.
Fuel 1 gives `.fuel`, and short calldata gives `.revert`. The negative control
`always_revert_rejected` proves a semantic result inequality at that fixture.
**It is not a compiler-contract negative control**. Interpreter fuel is not EVM
gas; these results say nothing about fork boundaries or compiled decoder success.
Checkpoint 3 remains blocked, without an invented compiler premise.

Final fixture log reports only `propext` and `Quot.sound` (or no axioms) and no
warnings. No new logical axiom is declared. Optional registration fragment for
coordinator: keep this audit outside generated production roots; if area
registration is authorized later, list the existing test path as an audit fixture
with the semantic-only boundary above. No production module import is requested.

## Typed migration owner tickets

Tickets are saved here for local coordinator retrieval. `relay.sh` is absent
from this published checkout; no delivery through an unavailable relay is claimed.
These require migration/proof compatibility work by existing owners, not weakened
statements or edited axiom expectations by this audit lane.

- **MIG-RAW**: unchanged `Solidity/Syntax/Raw.lean` fails required v4.35.0 at
  597, 650, 665, 682, 684: String/Slice API mismatches (six errors). Route via
  coordinator to the Syntax migration owner. Options: owner supplies compatible
  isolated migration overlay preserving semantics; coordinator supplies the
  corresponding already-reviewed pinned-toolchain prerequisite artifacts.
- **MIG-HASH**: unchanged `Solidity/Hash/CollisionBound.lean` has unsolved goals
  at 407, 660, 680 and message guards failing from 950 onward. Route to Hash
  migration/proof owner via coordinator. Options: repair proofs preserving exact
  statements; supply reviewed compatible owner overlay and rerun audit gates.
- **MIG-SLICE**: unchanged `Solidity/Backend/Scalar/Slice.lean:303` has axiom guard
  drift: `ternary` now reports `propext` instead of none. Route to Scalar
  migration/proof owner via coordinator. Options: owner preserves the expected
  proof/axiom budget on pinned toolchain; coordinator resolves the budget with
  the owner before a new reviewed overlay. This lane does not edit the pin.
- **MIG-RAWFREE**: unchanged `Solidity/Backend/AbiEntry/RawFreeTransport.lean`
  fails proofs at 16 and 91 plus dependent axiom guards. Route V13/migration
  owner. Options: repair unchanged proof statements on v4.35.0; supply compatible
  reviewed owner overlay. Failed temporary `sorryAx` is not a source theorem.
- **AUDIT-REST**: all remaining exact signatures/owners, simultaneous witnesses,
  compiler success, gas/fork controls and final gates remain open. Primary
  memory-operation roadmap owner V11; mapped ABI family V13; MemoryCopies live producer identity is unresolved (H70 routing below supersedes any attribution inferred from the CR lane name);
  other mapped aggregate/byte families require exact ownership reconciliation
  against the supplied snapshot. Do not infer all 550 files belong to V11.

Read-only import inspection found 534 mapped modules depend on Raw; another 12
on CollisionBound without Raw; WordValidationInterface encounters Scalar/Slice;
RawFreeTransport fails separately. CompositionInterface and EntryComposition
are the remaining passing mapped modules used by the fixture. This dependency
inspection is source-level, not an elaborated whole-project graph proof.

## Commands, outcomes and budgets

Toolchain archive: official `lean-4.35.0-linux.tar.zst`, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Actual Lean: 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Lake: 5.0.0-src+eb6cafb (Lean 4.35.0). No v4.24 cache used.

Every Lean invocation is serial, explicit `-j1 -M8192 --tstack=131072`, with
`LEAN_NUM_THREADS=1`, 12GiB address-space ceiling, a 4GiB available-memory
reserve check, host swap absent, and 300s/module stop. No systemd-run or Lean
server used. Writer lock surrounds generated writes and Lean checks. Isolated
prerequisite caches live off git under evidence; no central build config changed.

The diagnostic runner is not a substitute for repository `./run-lean.sh` gates.
Full final build/import validation remains pending because unchanged dependency
failures are established. **No RUNTIME_GATE_PASS** is claimed.

| Gate | Command/evidence under `/workspace/h62-audit-memory-evidence` | Outcome |
|---|---|---|
| Toolchain versions/archive | coordinator pin and checksum verified; versions above | pass |
| KeySort | pinned `lean -j1 -M8192 --tstack=131072 Solidity/KeySort.lean`; `keysort.json`, `keysort.log` | pass, 1.297s, 507032KiB max RSS |
| MemoryCopies prerequisite | bounded-build.py target `Solidity.Backend.MemoryCopies.InterfaceV2Laws`; `prerequisite/commands.json` | fail at unchanged Raw |
| Calldata-view prerequisite | target `Solidity.Backend.MemoryOps.CalldataViewPacking`; `view-prerequisite/commands.json` | fail at unchanged CollisionBound |
| Word validator prerequisite | target `Solidity.Backend.AbiEntry.WordValidationInterface`; `word-prerequisite/commands.json` | fail at unchanged Scalar/Slice |
| Raw-free prerequisite | target `Solidity.Backend.AbiEntry.RawFreeTransport`; `rawfree-prerequisite/commands.json` | fail |
| Final additive fixture | target `tests.h62.item2.audit-memory-operations.EntryAudit`; `entry-audit-final/commands.json` and module log | pass, fixture 0.567s, aggregate max RSS 526964KiB |
| Census acceptance/reproduction | check-census.py and two census.py runs, then `cmp` | pass |
| Scope/diff/trust | final saved verification log and manifest | pass for additive changes only |
| Full final `./run-lean.sh` | pending owner prerequisites | pending |

Each `commands.json` contains exact argv, exit, elapsed time, log path and
resource peak. An initial KeySort timing attempt exited 127 before Lean because
`/usr/bin/time` is absent; Python timing rerun passed. Failed exploratory fixture
import of RawFree is retained separately; final fixture does not import it.

No existing Lean code was refactored. Unchanged EntryComposition timing was
0.502s before and 0.466s in the final prerequisite pass (about -7%); subsecond
samples are noisy, not an end-to-end performance gate. The new, expanded fixture
has a 0.567s initial final-shape baseline and no preexisting equivalent. Full
before/after build timing and the >10% slowdown gate remain pending; no performance
acceptance is claimed. Peak across recorded prerequisites was about 1.44GiB RSS.

## Independent read-only reviews

Finder and skeptic used neither Lean server nor writes. Initial scanner findings:
297 local-let signatures truncated, record regions swallowed later definitions,
private spellings not kernel names. Fixed by full source regions, broader
boundaries, explicit unverified/private labels and regression acceptance. Finder
also caught a nonexistent requested module falsely returning runner success;
fixed with a fail-closed target check and acceptance case. Final reviews accepted
these changes and the fixture without statement weakening. Skeptic requested the
Prop-valued certificate be a theorem (fixed), and nonempty-prefix coverage was
added. Both explicitly retain compiler/gas/fork limitations.

## Committed handoff and resume

This is two reviewed backfill work items, not completed checkpoints. No fresh
replacement thread or competing continuation was created. Exact committed head,
patch checksum and artifacts are in external `/workspace/h62-audit-memory-evidence/HANDOFF.md`
and `result.json`, avoiding a self-referential commit hash. Coordinator retrieves
this same VM; no push, merge, PR, pre-gate or publication occurred.

Resume the existing goal and branch after compatible owner overlays/artifacts:
verify ancestry and input hashes again, reconcile exact kernel signatures and
owners/fields, prove all remaining simultaneous witnesses, add real compiler
success/negative/gas/fork controls, run fidelity and full affected/final gates,
and repeat finder/skeptic reviews. Keep all four checkpoints open until then.


## H70 continuation: area routes and remaining premise bundles

Third reviewed backfill item; full frozen assignment remains **blocked** and all
four checkpoints remain unfinished. H70 reports the owner relays accepted by
`solidity-h62-6-20261106/migrate-syntax`, `migrate-hash`, and `migrate-backend`.
The referenced host receipt and failed VM reads were not supplied here; no
unavailable source, remote repair or owner overlay is treated as retrieved.
`relay.sh` is host-only, not a VM installation task. No failing prerequisite was
rerun, no migration changes imported, and no new passing Lean/final gate claimed.

### Area responsibility versus live producer ownership

New `owner-routes.json` records evidence-backed routing rules from the pinned
ownership snapshot, module-map fragments and existing producer documentation.
`reconcile.py` checks those references and exact evidence substrings and hashes,
then enriches every existing source row. Source identities remain unchanged and
ordered; no candidate is filtered out. These routes establish where audit tickets
belong, not who may write each file. Every exact live-file-owner confirmation
remains pending; H62 migration overlays do not take producer ownership.

| Source area | Modules | Responsibility evidence |
|---|---:|---|
| MemoryCopies | 300 | V11 roadmap G33/G35; producer documentation also references historical `parallel-20261103/memory-copies`; exact live producer identity unresolved |
| MemoryOps except StructDefaults | 191 | V11 G32/G34/P6 and V11 source provenance |
| StructDefaults | 12 | MRS: documented memory-reference-structs lane and G33 split |
| G18 aggregate family | 22 | V16 G18.02/.03 |
| Byte parameter aggregate family | 2 | V14 G18.04/.05 |
| ABI entry core | 10 | V13 G40 |
| ABI calldata-view premise files | 2 | V11 G34 boundary; V13 discharges actual decoder view coherence |
| ABI mixed-premise file | 1 | CalldataSlice/CopyAgreement V11; Statement V09 G24.03 |
| FunctionValues | 6 | V13 G42.05 |
| Bounded known-self TryCall | 4 | DT H8 producer documentation; no reassignment of generic G36/G42 |

Seven declaration overrides distinguish the mixed ABI boundary, the MRS
S03-PANIC41 responsibility with VY5 Source writer/dependency role, joint V10 G27.05/V11 G35.02/.03 reached steps,
and the V13 caller discharging V11's view-coherence schema. The prior broad
reference to CR was not exact file ownership: CR's P8a ownership does not assign
MemoryCopies files. No CR, H55, migration, or helper scope is taken over here.
The historical memory-copies producer hint remains a hint until the coordinator
confirms it against its live registry.

All 4,141 declarations now carry an area route. Counts by routed key are V11
3,749; V16 200; V13 86; MRS 51; V14 33; DT 20; V09 1; joint V10+V11 1.
The two panic-premise rows retain VY5 as a separate Source dependency/discharger
role, supported by H16 single-writer authorization; the S03 snapshot names MRS
as area owner. The old S03 serialization note does not override H16.
A joint boundary is counted once, not once per owner. `uncovered-statements.tsv`
contains one row per original source identity with area keys and pending status;
these are source spellings, not kernel FQNs.

### Bundle classification and its limits

The enrichment retains exact source spans for 711 own-field candidates and
19,796 recognized header binders. It does not count them as exact kernel
hypotheses. All record fields must be satisfied together with their shared
parameters and all per-input assumptions. Field/source parsing does not establish
Prop-versus-Type, section generalization, inherited fields or satisfiability.
Twenty-three ambiguous header boundaries stay explicitly unresolved, with full
source regions retained. No-header-binders-recognized never means no hypotheses.

| Source bundle candidate | Rows |
|---|---:|
| Global uniform obligation | 99 |
| Global obligation with explicit input witness | 5 |
| Global dependent function bundle | 2 |
| Named contract plus input binders | 11 |
| Per-input binders | 2,541 |
| Per-input data and predicates carrier | 45 |
| Per-input parameterized record | 39 |
| Record bundle unresolved | 19 |
| No header binders recognized; conclusion/implicit premises pending | 1,380 |

For example, V1 `StorageWordCertificate` is a global conditional obligation;
V2 adds its actual fitting `AllocatorWitness`. `AllocatorWitness` is itself an
input carrier: represented heap/machine and strict fit must hold simultaneously
for the same fields. `SourceDefaultCertificate` concerns a particular reached
input/output state. `CopyAgreement` quantifies over states through its supplied
operation and reference; those nested function arguments are not supplied input
states. Candidate labels alone prove none of these bundles inhabited.

EntryAudit remains **a local fixture only**, byte-identical to the preceding
commit. No public-contract or census witness credit is added by this source
reconciliation. The enriched counts explicitly retain zero verified kernel
signatures, exact live-file-owner confirmations, and public compiler credits.

### Existing V1 capacity finding and owner request

`source-findings.json` records exactly one qualified conditional-field finding:
`Solidity.Backend.MemoryCopies.StorageWordCertificate.correct`. At `cost = W`,
its strict capacity antecedent has no natural cursor witness. The unchanged
memory-copies documentation explicitly describes the resulting empty-code
vacuity. This is source-supported evidence of that field's vacuity, **not** a
new pinned-toolchain replay or a complete bad-compiler certificate proof.
`escalations.txt` contains exactly one ESCALATE line for that qualified statement,
including evidence and two owner repair options. No frozen statement, exclusion,
interface, axiom pin, or proof budget is edited. The first option explicitly
reuses/audits existing V2; no H55 interface-pairs conversion or repair work is
implemented. Source evidence is not used to waive a required failing gate.

Coordinator requests, with exact existing source paths:

- Confirm the live producer for the 300 MemoryCopies files listed individually
  in the new census; route this legacy finding for
  `Solidity/Backend/MemoryCopies/Interface.lean` without inferring CR ownership.
- Keep waiting for migrate-syntax's `Solidity/Syntax/Raw.lean`, migrate-hash's
  `Solidity/Hash/CollisionBound.lean`, and migrate-backend's
  `Solidity/Backend/Scalar/Slice.lean` and
  `Solidity/Backend/AbiEntry/RawFreeTransport.lean` prerequisites.
- Supply compatible reviewed owner results and exact hashes via the existing
  coordinator channel; no overlay or unavailable artifact is assumed received.

### H70 acceptance, review and handoff

Bulk outputs are off git in `/workspace/h62-audit-memory-h70-evidence`:
`reconciled-census.json`, `uncovered-statements.tsv`, `escalations.txt`, acceptance,
reviews, command records and checksums. Their small SHA256 manifest is committed
under the assigned tests directory. The deterministic generator and all routing
and finding inputs are in git. The old evidence/patch/manifest remains intact.

Acceptance uses `PYTHONDONTWRITEBYTECODE=1 python3 tests/h62/item2/audit-memory-operations/check-reconcile.py`
and two identical `reconcile.py` invocations followed by byte comparison.
Regressions cover global versus actual input carriers, existential output versus
supplied witness fields, let/equation/match boundaries, exact source identities
and spans, mixed owner/caller roles, missing/ambiguous area routes, missing source
evidence, frozen hash drift, and duplicate escalation rejection. These are
external source-processing tests; they are not Lean proofs.

Independent read-only finder and skeptic reviews used no Lean server/builds or
writes. Skeptic found carrier-by-name classification and equation-proof header
contamination; both were fixed and covered by regression acceptance. The
quantifier flag was renamed to accurately describe the whole recognized header.
Both final reviews accepted the source boundaries, routing, no proof credits,
and the limited legacy finding. Exact kernel reconciliation remains pending.

There are no Lean or EntryAudit changes, no new axioms/sorry/trust shortcuts,
and no budget changes. No Lean performance refactor or new Lean timing claim;
full before/after timings and final gates remain pending behind owner repairs.
H70 timings measure the Python enrichment only. Original prerequisite failures
and their historical passing KeySort/fixture checks remain in the prior evidence.

This is the third reviewed backfill work item. Coordinator fresh-thread handoff
is due within the requested 3–5-item window using this same VM, branch and existing
goal. No replacement goal/thread, competing continuation, push, merge, pre-gate,
publication or deployment is created. Exact new committed head and patch hashes
will be saved in the external H70 handoff/report after committing this item.
