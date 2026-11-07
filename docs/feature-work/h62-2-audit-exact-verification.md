# H82 retirement: STOPPED, PAUSED requested, incomplete

Final successor: solidity-v12-v17-20261031/v17-validation-release.
The worker performs only this preservation checkpoint and stops; no automatic
continuation is authorized. Full original assignment, scope and queues are
committed under tests/h62/item2/audit-exact-verification/handoff/.
H82 permits the single proof-only falseNode unfolding edit; it remains UNVALIDATED
under the timing STOP. The old exact-file permission request is withdrawn.
The new lexical census draft accounts563saved names with no witnesses/exclusions;
review found provenance/partition hardening gaps, retained for successor.
No H71 push authorization is available, so the branch is not pushed.
The exposed goal schema has no PAUSED operation; no completion/reset/new goal.
See committed handoff/retirement.md and queues.md for every open obligation.

## Prior H70 record (historical)

# H62 item 2: H70 independent-module audit — blocked

Same VM `/workspace/solidity-lean`, branch
`codex/solidity-h62-2-20261106/audit-exact-verification`, frozen base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. Resumed from
`dee26790869de6ace73aa7cfd8c72a666c6f34ea` under the H70 router.
The original persistent goal is unfinished; no replacement goal, merge, push,
publication, pre-gate, budget increase or original-interface edit was performed.

## H70 outcome

All eight remaining modules have buildability/audit status recorded:

| Frozen module | Source theorem candidates | Current result |
|---|---:|---|
| `Solidity/Calculus/BitArith.lean` | 16 | 16 simultaneous input instances kernel checked. |
| `Solidity/Calculus/LinearDecision.lean` | 80 | 80 simultaneous input instances kernel checked. |
| `Solidity/Calculus/LinearHypotheses.lean` | 1 | Joint input checked; local success/reject-all/fuel controls checked; timing stop below. |
| `Solidity/Calculus/LinearSyntax.lean` | 0 | No source or compiler theorem declarations; no padding witnesses added. |
| `Solidity/Examples/Tactics/Recovery.lean` | 2 | Both unconditional statements checked with empty input tuples; local invalid-parity and reject-all controls checked. |
| `Solidity/Calculus/LinearCountermodel.lean` | 14 | Blocked by unchanged line 134 under official v4.35. |
| `Solidity/Calculus/PresburgerDecision.lean` | 88 | Blocked by its LinearCountermodel import. |
| `Solidity/Examples/LinearDecision.lean` | 34 | Blocked by its LinearCountermodel import; includes anonymous candidates. |

This adds **99** source-statement instances. The nine earlier VisitedSet bundles
retain their separately validated source/log receipt; they are not called fresh
H70 Lean replays. Total named source statements accounted for across the six
buildable modules: **108**.

The compiler-level census includes generated/private theorem declarations:
BitArith 64, LinearDecision 523, LinearHypotheses 11, LinearSyntax 0,
VisitedSet 68, Recovery 5: **671 total**, with **563 additional declarations still
uncovered** beyond those 108 source statements. No generated declaration is
excluded; full names, exact kernel expressions, signatures, levels, axiom sets
and unresolved owner labels are off git in
`/workspace/h62-audit-h70-evidence/h70-compiler-census.json`.
The earlier conversational total 771/663 was an arithmetic error, corrected
before handoff. The deterministic checker computes the actual totals from JSON.

The full 305-file source census remains 5,277 candidates. The 5,169 candidates
outside the 108 accounted named statements and the 563 additional compiler
entries are separate incomplete sets, not a claim of an exact global remainder.
Generated declarations from the other 299 modules remain unenumerated by the
compiler until imports can elaborate. Live producer identities remain unresolved.

## Statement fidelity and proof boundaries

`tests/h62/item2/audit-exact-verification/JointWitness.lean` reads the actual
unchanged theorem type, head-normalizes aliases/lets that hide binders, and
constructs a dependent existential for every binder. It checks supplied terms in
order, applies the original theorem to those same terms, packages explicit
Exists predicates, rejects unresolved/free/sorry terms, and submits the declaration
to normal kernel checking. It then rejects transitive axioms outside propext,
Classical.choice and Quot.sound. No original statement is weakened or replaced.

Nonempty singleton formula sets/frontiers and inhabited predicates witness the
global exploration/round contracts together with feasible inputs; round length
is positive, and walkFrom_closed has an actual closed walk. Bounds and all
nonzero/sign conditions share the same concrete tuple. The synthetic hidden-False
alias regression is deliberately outside the frozen census and must reject; it
creates no witness. Every recorded source instance has its original type and
axiom evidence. H44 bulk outputs remain off git; source inputs/generators are in git.

The five new local controls concern certificate success, reject-all certificate
or recovery behavior, zero-fuel exhaustion and invalid parity. They do not prove
supported-program source-to-bytecode compiler success, always-revert compiler
exclusion, or EVM gas/fork contracts. Checkpoint 3 remains incomplete.
No frozen theorem has been shown false/vacuous by these results, so no production
theorem ESCALATE line is asserted.

## Required stop and owner dependencies

**B-PERFORMANCE-STOP:** final
`python3 scripts/h62/item2/audit-exact-verification/h70-check.py --run` exited 1.
All four bounded compiler subprocess phases exited 0, but unchanged
LinearHypotheses measured median **0.520586729 s before → 0.622912645 s after,
+19.655883%**, five samples each under the same tree/cache/resources.
The assignment says stop above 10%; Lean work stopped immediately. No further
Lean or timing runs followed. The 0.1-second monitor may quantize these short
samples, but that explanation is unproved and does not waive the failed gate.
See `tests/h62/item2/audit-exact-verification/performance-stop.md` and
`/workspace/h62-audit-h70-evidence/h70-timing.json`.

**B-MIGRATION-LINEAR-COUNTERMODEL:** coordinator relay requested to
`solidity-h62-6-20261106/migrate-calculus` for unchanged
`Solidity/Calculus/LinearCountermodel.lean:134:2`, a type mismatch in
Solidity.Linear.AFml.falseNode_spec. Exact ticket:
`tests/h62/item2/audit-exact-verification/owner-ticket-linear-countermodel.md`.
Request owner-reviewed v4.35 proof migration preserving the frozen statement and
budget, with base/head/patch/hash; otherwise retain the blocker.

**B-MIGRATION-RAW:** the existing ticket to migrate-syntax was accepted by H70;
the 296 dependent modules remain waiting. Relay is host-only coordinator work;
relay.sh absence is not an installation task. No original-file permission is
inferred from these requests.

## Gates and read-only reviews

Actual runtime remains official Lean 4.35.0 commit
eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Lake 5.0.0-src+eb6cafb. KeySort passes.
All Lean work uses the unchanged capped runner: one heavy job, explicit -j1,
LEAN_NUM_THREADS=1, 300s per file, 12GiB memory/no swap, 4GiB host and effective
outer-VM headroom checked every 0.1s, source/toolchain mounts read only and no
v4.24 cache. No Lean MCP tools are exposed, so serial per-file checks are used.
No proof budget was raised. Core remains intrinsic and dependency free.

The H70 checker binds all source/proof/driver hashes, exact four phases, commands,
plans and ordered CHECK/PASS workloads, compiler versions, resource markers,
completion/exit records, exact source membership, all axiom reports and positive
finite timing samples. It separately binds/verifies the earlier VisitedSet
proof, ledger, checker, receipt, log, exit and source census. Its final result is
a failed timing gate, not a full passing gate. Full ./run-lean.sh and broader
acceptance remain blocked/pending.

Independent finder and skeptic used no Lean/server or edits. They found and
verified fixes for hidden binder aliases, transitive axiom checks, dependent
Exists packaging, receipt phase omission, workload completeness, finite timing,
prior-evidence binding and the census arithmetic correction. Full review record
is exported in `/workspace/h62-audit-h70-evidence/reviews.md`. Lightweight negative
receipt checks and repository checks are recorded in gates.json. The performance
failure remains visible and unwaived.

## Handoff and continuation

Five buildable remaining-module items have been handled; request a fresh
coordinator thread on this exact VM/goal/branch, never self-launch a replacement.
All four assignment checkpoints remain incomplete. Remaining obligations include
563 compiler declarations already named, other blocked inventories/witnesses,
live owners, supported-program totality and negative compiler/gas/fork controls,
performance resolution and full final validation. Do not mark the goal complete.

New retrieval paths are `/workspace/h62-audit-h70-evidence/original.patch`,
`/workspace/h62-audit-h70-evidence/handoff.md`,
`/workspace/h62-audit-h70-evidence/evidence.tar.gz`,
`/workspace/h62-audit-h70-evidence/receipt.json`, and
`/workspace/h62-audit-h70-evidence/SHA256SUMS`. Full committed head and hashes are
in the exported receipt. The initial checkpoint below remains historical evidence.

---

# Initial checkpoint: dee267908 (historical record)

Batch `solidity-h62-2-20261106`, worker `audit-exact-verification`.
Repository `/workspace/solidity-lean`; branch
`codex/solidity-h62-2-20261106/audit-exact-verification`; frozen base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
The exported receipt records the full committed head and artifact hashes.
The full persistent assignment remains unfinished. No complete checkpoint is
claimed, and no RUNTIME_GATE_PASS is emitted.

## Saved work and exact limits

1. Source-census backfill: 305 distinct mapped files, 5,277 declaration
   candidates (4,393 named and 884 anonymous), with all area memberships retained.
   All table-row module references resolve, including sibling Tools and benchmark
   globs. Each file and map is byte-compared to the exact base before generation.
   Signatures, lexical section variables, source locations and hashes are saved.
   The output is off git at `/workspace/h62-audit-evidence/source-census.json`.
   This is NOT an elaborated interface census: implicit binders, generated
   declarations, actual interface membership and area-producer owners remain
   unverified. Its candidate status deliberately stays uncovered.
2. Independent helper backfill: all nine named frozen declarations in
   `Solidity/Calculus/VisitedSet.lean` have one mapped local witness bundle in
   `tests/h62/item2/audit-exact-verification/witness-ledger.json`.
   `tests/h62/item2/audit-exact-verification/VisitedSetAudit.lean` imports the
   unchanged interface and prints its nine elaborated signatures. `closed_inputs`
   jointly witnesses the result equation and invariant at one nonempty input.
   `cache_inputs` binds every original input together, proves the global cache
   preservation/agreement contract and Good(0), and applies original walkC_eq.
   Nat supplies inhabited node/state/cache types and its DecidableEq instance.
   Other helpers have no global premise structure; their per-input success
   equations are witnessed on the same concrete tuple.
3. Reproduction/evidence backfill: frozen-source generator, parser regressions,
   receipt validation, import plan and serial bounded Docker checks. Current
   receipts bind exact proof/interface/log hashes and successful completion.
   The full-audit completion gate deliberately fails with 5,268 uncovered source
   candidates. That number is a source-candidate remainder, not a proved count
   of interfaces with logical hypotheses.

The three controls prove a stored-node walk closes, a reject-all checker cannot
produce that observation, and zero fuel produces out. They are local graph-walk
controls, not source-to-bytecode compiler totality or always-revert compiler
controls. Gas, fork and broader observable-failure obligations remain pending.
No frozen statement was edited or shown vacuous/false, so no theorem ESCALATE
line is justified by this work.

## Blocking dependency and owner ticket

`tests/h62/item2/audit-exact-verification/owner-ticket.md` records
B-MIGRATION-RAW for `solidity-h62-6-20261106/migrate-syntax`, matched to the
verified ownership snapshot. Official Lean 4.35.0 rejects unchanged
`Solidity/Syntax/Raw.lean` at 597:44, 650:23, 665:27, 682:46 and 684:34.
String/Slice API mismatches block the initial interface import closure; a source
import sweep finds this dependency in 296 of the 305 mapped modules. Of the nine
independent modules, only VisitedSet has witness backfill so far.

Await an owner-reviewed migration overlay with exact base/head/patch/hash through
the coordinator. The assignment's relay.sh is absent locally; the saved ticket
is for coordinator retrieval, not a claim that a live producer was messaged.
Original owned files stay read only; no owner-coordination permission was needed
for these new additive files. No H55 work was duplicated.

## Runtime, proof budget and measurements

All five files in `/workspace/h62-coordinator-inputs/sha256.json` verify. The
coordinator pin is official lean-4.35.0-linux.tar.zst, SHA256
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Actual Lean: 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
Release. Actual Lake: 5.0.0-src+eb6cafb (Lean 4.35.0).
KeySort passes. No v4.24 per-master cache is reused; fresh compiled artifacts live
under `/workspace/h62-audit-evidence/build435`.

Heavy work is serial, LEAN_NUM_THREADS=1, explicit -j1, --tstack=131072,
300 seconds per file, Docker memory.max=12884901888 and memory.swap.max=0.
Sources and toolchain are mounted read only, network disabled. The repository
writer lock is held. The final runner checks a 4 GiB reserve against both host MemAvailable and
outer VM cgroup memory.max minus memory.current at admission and every 0.1 seconds
during each Lean command. It conservatively gives no credit for reclaimable
file cache and terminates only its own timeout process on a reserve stop. No systemd-run or Lean server is used.
No proof heartbeat budget was raised. New source contains zero sorry/new axiom/
native_decide/trust shortcuts. All nine helpers and three controls report only
subsets of propext, Classical.choice and Quot.sound.

History 5154e4e979a9527e6b7f6f62e247d6d75c7acf21 introduced the fast hashed walk.
Its implementation is unchanged. Final same-tree/cache/resources measurements
compile that same interface five times before and after the additive audit:
median 0.730938 s before, 0.728613 s after, delta -0.318%. This is a small local
measurement, not a full-build timing. No >10% slowdown was observed. An initial
empty reproduction-run attempt lacked Docker stdin; it was discarded, the
runner now requires -i and a terminal workload marker, and only real completed
samples count.

## Gates and evidence

Commands below run from the repository root. Logs and exact exits are saved in
`/workspace/h62-audit-evidence/gates.json` and corresponding logs.

| Command | Result and scope |
|---|---|
| `python3 scripts/h62/item2/audit-exact-verification/census.py --output /workspace/h62-audit-evidence/source-census.json` | Source inventory generated; byte-for-byte deterministic replay. |
| `python3 tests/h62/item2/audit-exact-verification/test_census.py` | Three regressions pass: attributes/comments/equations, escaped newlines, binder defaults. |
| `bash scripts/h62/item2/audit-exact-verification/bounded-check.sh keysort` | Exit 0; real pinned KeySort pass. |
| `bash scripts/h62/item2/audit-exact-verification/bounded-check.sh audit` | Exit 0; nine local bundles plus three controls and axiom reports. |
| `bash scripts/h62/item2/audit-exact-verification/bounded-check.sh timing` | Exit 0; ten real interface samples, no slowdown. |
| `bash scripts/h62/item2/audit-exact-verification/bounded-check.sh imports` | Exit 1 at unchanged Raw syntax; owner dependency blocker. |
| `python3 tests/h62/item2/audit-exact-verification/test_receipts.py` | Five negative acceptance controls pass: stale hash, missing completion, failed exit, optimized Python, incomplete full assignment. |
| `python3 scripts/h62/item2/audit-exact-verification/verify.py` | Provisional evidence and local bundle receipts validate. |
| `python3 scripts/h62/item2/audit-exact-verification/verify.py --require-complete` | Exit 1; FULL_AUDIT_GATE_FAIL, intentionally no false completion. |
| `./run-lean.sh` and full affected library/corpus/acceptance gates | Pending behind pinned-toolchain import failure; never counted as passing. |

## Independent read-only reviews

Finder and skeptic used neither Lean server nor builds. Both caught six omitted
inline-attribute theorems, sibling Tools module resolution and escaped-newline
masking. Finder additionally required byte-checking frozen inputs. Fixed and
regression checked. Both caught omitted cache-instance binders; fixed by binding
them jointly and applying original walkC_eq. All helpers now print axiom sets.

The final evidence review caught stale-log acceptance, missing successful-run
provenance, unidentified controls, and Python optimized-mode bypass; fixed by
source/log hash receipts, exit/marker checks, explicit expected names and -O
rejection. Continuous host and effective VM cgroup memory-reserve monitoring was added
after review. Final
review messages and disposition are exported in reviews.md.

## Required continuation

Resume this exact VM, goal and branch after coordinator relay. Do not create or
reset a goal. This thread saved three bounded work items (source census, local
helper witness audit, reproduction/evidence tooling); request a fresh coordinator
thread after this handoff, never self-launch a replacement.

All four assignment checkpoints remain incomplete: exact elaborated inventory
and confirmed owners; joint witnesses for every actual interface; meaningful
supported-program compiler success with reject-all/always-revert and gas/fork
boundaries; full witness/fidelity census and final gates. Review the untouched
independent modules as in-scope backfill when useful. Keep the full assignment
blocked/unfinished until these obligations and validation are complete.

## Exported handoff

Coordinator retrieval paths: `/workspace/h62-audit-evidence/original.patch`,
`/workspace/h62-audit-evidence/handoff.md`,
`/workspace/h62-audit-evidence/receipt.json`,
`/workspace/h62-audit-evidence/evidence.tar.gz`, and
`/workspace/h62-audit-evidence/SHA256SUMS`. No push, merge, PR, pre-gate or
publication was performed. Large census/toolchain/cache outputs remain off git.

## Successor census partition controls

The additive `scripts/h62/item2/audit-exact-verification/census_partition.py`
checks complete saved/raw name sets, exact retained kernel-field metadata,
an independently supplied source-census digest and coverage membership derived
from source candidate names. Six synthetic host-only tests in
`tests/h62/item2/audit-exact-verification/test_partition.py` pass. These tests
reject equal-count coverage swaps, substituted/duplicate names, field drift,
unknown labels, corrupt digests and malformed JSON. Historical witness labels
are checked for consistency only; they supply no witness evidence.

This helper is not yet wired into the historical Core-dependent runner.
Original raw artifacts remain UNVERIFIABLE; actual census replay and proof
validation remain pending. No Lean or timing STOP was rerun, no Core change
was made, and no original obligation or release row is closed.

The `partition_pinned` byte-input wrapper additionally requires exact external
SHA256 inventory roles for compiler rows, annotations and source census before
strict JSON parsing. Ten synthetic host controls pass, including coordinated
compiler/annotation edits with stale pins. Pins must originate in an independent
authenticated inventory; this helper cannot certify their provenance or turn
matching bytes into historical execution evidence. Actual replay remains open.

The helper now exposes a reproduction CLI: provide `--compiler`,
`--annotations`, `--source` and a corresponding `--compiler-sha256`,
`--annotations-sha256`, `--source-sha256` from an authenticated inventory.
Successful metadata comparison prints JSON and exits zero; missing inputs,
digest drift or inconsistent metadata exit two without a success JSON record.
The eleventh host test covers CLI roundtrip, changed bytes and missing files.
A zero exit certifies metadata consistency only. The CLI does not run producers,
load Lean artifacts, discharge hypotheses or authenticate the supplied inventory.

CLI inputs must be regular files of at most 16 MiB each. Nonblocking, no-follow
opens reject FIFOs and symlinks; bounded reads also reject growth past the cap.
A twelfth host test rejects oversized, FIFO, symlink and directory inputs. This
intake bound does not change any historical proof or timing budget.
