# H62 item 2: exact-verification audit — blocked handoff

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
