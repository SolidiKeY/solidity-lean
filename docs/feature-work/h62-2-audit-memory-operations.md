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

No weakened or vacuous frozen statement was established by this backfill.
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
  memory-operation owner V11; copy-recovery owner CR; mapped ABI family V13;
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
