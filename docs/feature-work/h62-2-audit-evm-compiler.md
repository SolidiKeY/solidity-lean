# H62 item 2: frozen EVM compiler hypothesis audit

Status: **stopped by human retirement instruction; full assignment partial**.
Handoff to `solidity-v12-v17-20261031/v17-validation-release`.
No implementation continuation is authorized. The exposed goal tool cannot
set PAUSED (it accepts only complete or blocked); neither substitute state
was requested. This capability failure does not authorize resuming work.
 Human H69
accepts checked joint-impossibility proofs for intentional negative controls,
separation lemmas and refutations. SCOPE1 and TC1 are resolved. Ordinary interface
statements still require simultaneous witnesses. No original statement changes.

## Frozen checkout and scope

Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Branch: `codex/solidity-h62-2-20261106/audit-evm-compiler`.
Repository: `/workspace/audit-evm-compiler`; older clean checkout
`/workspace/solidity-lean` preserved. Published remote ancestry was verified.
All 160 mapped originals and module map match their frozen Git blobs. Writes
are confined to the assigned scripts/tests prefixes and this document. No push,
merge, PR, generated root, central registration, axiom pin or interface edit.

## Checkpoint ledger

1. Inventory remains partial. All 1,830 authored theorem declarations in 160
   mapped modules are counted once, including private and no-premise declarations.
   Core: exact kernel Expr types, universe parameters and axiom sets extracted
   for all 1,721 declarations in 156 modules. Four optional Bridge modules contain
   109 declarations pending extraction; the exact-pinned dependency build was
   interrupted for retirement.
   Source scanner schema 2 corrects 48 truncated source signatures involving
   root lets, root matches and tuple constructors; counts/identities and kernel
   expressions are unchanged. The correction ledger retains old and new text.
   Generated recursors/equations, standard instances and 224 anonymous examples
   are separate from this authored-theorem census; the finder checked for custom
   public theorem-generating macros and found none in this mapped corpus.
   Only 18 Opcode records have confirmed producer owner master, from the supplied
   G45.05 key and module header. Other producer owners remain unresolved. The
   ownership snapshot supplies write candidates on 570 rows; migration overlays
   on all rows never establish producer ownership.
2. Witness audit remains partial. The ledger has 46 unique exact-signature links:
   five original compiler headlines with joint witnesses, 23 intentional
   impossibility cases, 16 Opcode declarations with joint input packages and two
   closed Opcode equalities with no input binders. The other 1,784 declarations
   remain pending classification or witnesses. Every intentional case has its
   exact original name, reason, checked impossibility proof and classification
   in coverage.json and the audit source. Layout accounts for five separation
   lemmas; IntentionalAudit accounts for 18 empty-heap, shape-separation,
   occurrence-kind and argument-alias refutations. No exclusion or premise added.
3. Success/totality remains partial. A supported nonempty setAge program admits,
   writes slot 13 from zero to ten and terminates with zero pending jumps.
   Reject-all, constant REVERT, empty code and trailing-jump candidates fail that
   observation. Overflow has exact reversion. The generic non-paying source
   success transfer has all premises jointly witnessed on setAge. OpcodeAudit
   proves encoder totality with decoding round trips for every intrinsic program,
   rejects none/empty/constant-REVERT encoders, and checks PUSH1 0x2a; STOP bytes,
   undefined-byte and truncated-PUSH failure. CLZ decoding documents the fixed
   Osaka table only. General supported-source totality, public-contract coverage,
   observable gas and historical-fork boundaries remain unfinished.
4. Fidelity/validation remains partial. All 46 links have unique frozen source
   IDs and hashes. Reconciliation checks bookkeeping; separate Lean checks and
   independent reviews establish their proof meanings. Full affected-library
   and run-lean.sh gates remain pending; no RUNTIME_GATE_PASS or full completion.

## Premise meaning and proof boundary

Headline fragment admission, actual-input Sim, capacity/push bounds, flags,
execution and initial balance consistency are per-input conditions. Each joint
witness uses one coherent program/state/machine tuple. Layout exhibits separately
inhabited mapping regions and proves their forbidden overlap impossible.
JointImpossible packages every original dependent forall binder into nested
Exists ending True, applies the unchanged original theorem to the unpacked
arguments, and installs a closed kernel-checked theorem. It only accepts a
terminal False and rejects ordinary statements. Type-valued certificates are
included. Syntactic is_prop_binder metadata alone never establishes feasibility.

There are 63 new checked theorem declarations across the audit modules: 23 from
Layout/Success/Headline, 18 H69 generated impossibilities and 22 Opcode facts.
The JointImpossible metaprogram generates proofs checked by Lean addDecl; it
introduces no axiom. Printed proof axiom sets contain only propext,
Classical.choice and Quot.sound. No authored sorry, new axiom, native_decide,
trust shortcut or raised maxHeartbeats. External compiler/cache tests, parser
controls and measurements are evidence outside these Lean proof statements.

## Toolchain, builds and resources

Actual Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake `5.0.0-src+797c613`. TC1 explicitly keeps this lane on v4.24.0; v4.35
belongs solely to the separate migration batch. KeySort passed before proof
work. Lean MCP is unavailable, so checks use bounded per-file Lake env lean,
explicit -j1, LEAN_NUM_THREADS=1, the writer lock, no swap and four GiB reserve.
No systemd-run, source proof-budget change or concurrent heavy Lean job.

Core dependency build completed 321 modules: 260 built, 61 existing artifacts,
zero failures/blocked. A separate successful Lake --no-build freshness gate for
all 156 mapped core targets validates their traces; presence alone is not a
freshness claim. One default metadata budget per declaration avoids accumulation
in a large module without raising any proof budget. Prior failed instrumentation
and successful replacement receipts are retained.

Optional Bridge uses the frozen manifest's exact Git revisions and root v4.24.0,
private external serial package configs and ignored runtime package links. Public
Mathlib cache requests returned CONNECT 403; serial source compilation had proceeded
with bounded 300-second batches retaining completed artifacts. The fifth
batch was terminated under the human retirement instruction (exit -15 after
182.917 s), preserving completed dependencies through logged target 934/939.
No further builds are running. Queued new witness-file creation was canceled
before execution; the 63 checked theorems and 46 coverage links are unchanged. Dependency source
and tracked Bridge/core configs remain unchanged. Runtime provisioning is not a
proof result. Full optional Bridge extraction is still pending.

Static milestone gates pass: scanner boundary acceptance, dependency layers
(857 core modules, zero elaborator/parser-adapter reachability), generated
fragments and global documentation paths. The previous missing optional Mathlib
attribution now resolves through the exact-pinned runtime source checkout.
The documentation gate reports 115 resolving ambiguous references as warnings.

Matched unchanged Layout checking, same tree/cache/resources: median 2.84262 s
before and 2.82415 s after, delta -0.65%, within the 10% rule. This is not a
whole-build performance claim. Exact commands, resource records, errors and
passing replacement checks reside in the external evidence directory.

## Independent review and reproduction

Read-only finder and skeptic use neither Lean server nor writes. They checked
full dependent witness tuples, the impossibility generator, every intentional
reason, Opcode coverage and the scanner fixes. Confirmed signature truncations
were fixed without changing kernel statements. Final receipts preserve findings
and remaining limits. The reconciler does not certify proof links or resolve
unknown owners. Full-task findings remain open as listed above.

Scripts deterministically regenerate source census, exact-type inspection,
reconciliation, bounded serial builds and private optional dependency setup.
Bulk outputs stay outside Git at `/workspace/audit-evm-compiler-evidence` with a
SHA256 manifest. coverage.json is the small reviewed link ledger. Registration
suggestions are additive fragments under tests for the coordinator; no root or
module-map registration is performed here.

The external handoff records full committed head, original goal/VM identity,
commands, patch/bundle paths and pending obligations. The original VM/goal/branch are preserved. The successor integrates the final
head; this worker stops. No new/reset/replacement goal or automatic continuation.
No H71 push permission was supplied, so the original no-push rule remains.
The retirement supersedes earlier instructions to continue.

## Retirement preservation checkpoint

The authenticated patch/bundle includes the original user-rendered assignment
from this thread, its complete original work/backfill queues, exact scope
manifest (all 160 mapped paths) and effective decisions under the assigned
tests handoff directory. The local prompt copy's SHA256 is separately recorded;
it is not asserted equal to the coordinator's older rendered-goal digest.
Bulk census/kernel/build logs remain off Git with checksums.

All four checkpoints remain partial. Pending: 109 Bridge captures/reconciliation,
1,784 joint-witness/classification records, 1,812 producer-owner assignments,
general supported-source success/totality, all-contract negative controls and
observable gas/historical-fork boundaries, full affected-library/run-lean.sh
gates and final fidelity/reviews. Backfill remains scanner/census, within-scope
negative controls, isolated fixture proofs and deterministic acceptance/timing
tooling; no new unclaimed candidate was taken. The interrupted Bridge build and
cache CONNECT403 are the concrete dependency state, not a new scope question.
The queued Jumpdest plan was not saved or checked and earns no coverage.

The external retirement handoff enumerates waits, commands, exports, full final
committed head and SHA256SUMS. No new proof implementation, owner message,
Claude-owned edit, root/module-map/axiom pin change, push or merge was performed.
