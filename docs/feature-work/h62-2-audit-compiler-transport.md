# H62 item 2: compiler-transport empty-statement audit

Task: `solidity-h62-2-20261106/audit-compiler-transport`.
Frozen base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Assigned branch: `codex/solidity-h62-2-20261106/audit-compiler-transport`.
Only additive owned test/script/document paths are changed. No frozen interface,
root, module map, trust pin, heartbeat or dependency is changed.

## Current result: partial; H69 decision applied

The source inventory accounts for all 122 first-column module-map entries and
560 declarations exactly once (539 public, 21 private). A prose reference to
`Evm/Signed.lean` is not an extra table entry. The scanner freezes both the map
and every original source file against the base. Signature spans, exact text,
source-prefix context spans, hashes and owner records are in external census
JSON. This source-level evidence is distinct from the completed theorem-constant
reflection below; semantic interface classification remains pending.

No positive theorem is reported witnessed until the additive proof passes Lean
and its exact hypothesis coverage is reconciled with the original statement.
Per-input feasibility and global premise structure inhabitation remain distinct;
Prop-versus-data reflection alone does not classify a semantic producer premise.

## H69: intentional negative hypotheses

The human decision H69 (2026-11-06) resolves Q-NEG-01: checked joint
impossibility is the audit result for deliberately contradictory hypotheses.
Ordinary interfaces still require joint satisfiability. No statement changes.
The [owner ticket](../../tests/h62/item2/audit-compiler-transport/owner-ticket.md)
is closed by that decision; no owner edit is requested.

The checked registry `tests/h62/item2/audit-compiler-transport/h69-classification.json`
classifies every one of 68 intentional negatives by exact name, reason and
impossibility proof: two public P12 incompatibility controls, private empty-heap
and stale-pointer refutations, and 64 generated False-branch helpers under 35
source parents. The ordinary parent obligations remain independent records.
Only the original telescope and a literal False conclusion (metadata stripped)
are used. A negated conclusion does not add its refuted proposition as a premise.
The registry includes the verbatim H69 decision.

Historical escalation lines below are resolved by H69, retained once for traceability:

ESCALATE: Solidity.Backend.Passes.P12MemoryCapture.nonempty_revert_incompatible — frozen P12MemoryCapture.lean:75 concludes False, so simultaneous witnesses for its full hypothesis tuple are impossible; options: retain the exact statement and authorize joint-impossibility evidence for negative controls, or retain the literal witness criterion and await an owner-authorized interface plan (Q-NEG-01; V09/V07).
ESCALATE: Solidity.Backend.Passes.P12StorageCapture.nonempty_revert_incompatible — frozen P12StorageCapture.lean:64 concludes False, so simultaneous witnesses for its full hypothesis tuple are impossible; options: retain the exact statement and authorize joint-impossibility evidence for negative controls, or retain the literal witness criterion and await an owner-authorized interface plan (Q-NEG-01; V09/V07).

## Validated additive proof artifacts

- `tests/h62/item2/audit-compiler-transport/JointHypotheses.lean` existentially binds every original parameter together,
  in dependency order, ending in True. Its impossibility terms use the original
  False-conclusion theorem and existential elimination. No separate premise
  inhabitation is substituted for a joint witness.
- `tests/h62/item2/audit-compiler-transport/Audit.lean` retains the frozen P12 interfaces and gives unconditional public
  selection, source success, target success, full mapped output and allocator
  cursor 264 for two associations of the existing allocating scoped-call
  fixture, for every saved stack. Reject-all and always-revert candidates fail
  that strengthened audit contract. Actual public contracts are not edited.
- `tests/h62/item2/audit-compiler-transport/Witnesses.lean` places original acceptance, admission, payment freedom,
  source result, target result and selected map in one correlated tuple for
  the generic compiler boundary statements named in its docstring.
- `tests/h62/item2/audit-compiler-transport/Reflect.lean` writes exact elaborated types, raw Expr representations,
  universe parameters and binder types for imported theorem constants. Private
  kernel names and auxiliary declarations must be reconciled separately.

The H69 additions `H69.lean`, `NilFixture.lean`, `OptimizerFixture.lean`,
`ExplicitCases.lean`, `AutoWitness.lean` and `CarrierInventory.lean` pass
bounded checks. The explicit optimizer fixtures use `ULift.{u} Nat` at the
original universe, a validator accepting equal inputs and rejecting unequal
inputs, and nonempty pass/proposal lists. Original optimizer premises are
inhabited together; no reject-all validator is used as a success witness.

The constructive generator preserves each original universe parameter and
rejects unresolved expression or universe metavariables. Successful tuples go
through normal kernel declaration checking outside the search-failure catch.
Each candidate has a smaller search budget inside the original declaration
budget; no heartbeat limit is raised. Search failure remains uncovered.

The final expanded census matches all 560 source theorems once and records
1,134 proof constants: 1,114 theorem constants and 20 proof-valued definitions.
Three proof-field projections remain semantic interface obligations. It also
records 91 proof-bearing data producers separately; direct proof fields alone
do not establish their coupled domain inhabitation or exhaust nested carriers.

The reconciled statuses are 5 correlated compiler-boundary joint witnesses,
97 additional syntactic joint witnesses, 466 checked empty syntactic premise
tuples, 68 checked intentional impossibilities, and 498 uncovered constants.
Empty telescopes certify only the empty conjunction, not feasibility inside a
defined universal predicate. Global-versus-input semantic review remains pending
except where the existing correlated physical fixture is explicitly recorded.
All 46 named owned theorems and successful generated declarations have at most existing standard axioms
`propext`, `Classical.choice`, `Quot.sound`; no new axiom, sorry, native_decide
or trust shortcut is introduced.

The existing success family is finite and intrinsic. It does not prove totality
for every supported Source program or inhabited global P12 producers. The
abstract `Evm.Machine` explicitly has no gas or fork parameter; `Evm.Out.ok`'s
final Nat is pending jump skip, not gas. Bytecode gas/fork adequacy remains pending.

## Checks and resources

The actual frozen toolchain is Lean 4.24.0, commit
797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake 5.0.0-src+797c613.
The v4.35.0 official archive pin in coordinator inputs is scoped to migration
lanes. This lane does not migrate or reuse a per-master cache.

Fresh KeySort: `lean -j1 --tstack=131072 Solidity/KeySort.lean`, exit 0,
2.7163 s, sampled direct-process peak RSS 257884160 bytes. An earlier attempt
could not invoke `/usr/bin/time` (absent); it is not counted as a passing gate.
The Python runner records the actual exit and bounded run separately.

`build_serial.py` checks the full dependency closure one file at a time with
`LEAN_NUM_THREADS=1`, explicit `-j1 -DElab.async=false`, original proof budgets, fresh external
OLEans and a 4 GiB available-memory guard. Inherited VM cap is 16 GiB;
RLIMIT_AS is 12 GiB per child. Host swap is zero. Sampled RSS is direct-child
only, not aggregate Lake/shell evidence. The lane holds the repository writer
lock for the build. No other worker is terminated and no systemd-run is used.

The initial async-default run aborted at unchanged Calculus/TermSize with a
native thread-creation error; the same-limit retry measured 44 threads and
11710242816 virtual bytes despite less than 1 GiB resident memory. The serial
elaboration retry passed in 32.7625 s, with five threads, 3029798912 virtual
bytes and 930349056 sampled resident bytes, without raising any limit. Both
failed attempts and the recovered passing check are retained externally. The
resume compares prefix sources with BASE and records current artifact hashes;
it checks artifact presence but has no earlier artifact digest to authenticate;
it does not use the pre-existing Lake cache. The matched timing gate uses
serial elaboration and symmetric target warmup on both sides. It measures
unchanged CompilerWholeScope checking, not whole-closure/end-to-end cost.

Source acceptance passes: nested comments, quoted fake declarations, inline
attributes, default-binder `:=`, frozen per-module hashes and counts, independent
token counts and rejection of a removed map row. Layer checking passes (857
core modules; zero paths to elaborators or checked parser adapters). Generated
root and fragment checks pass. The first 327 successful modules used async-default elaboration; the
remaining 323 use explicit serial elaboration after recovery. Every command
used `-j1`, and exact historical commands are retained in metrics.
Fresh original diagnostics pass for the entire 650-module dependency closure.
H69 reflection passes for all 122 mapped modules (42.418 s); carrier scanning
and all 21 generated driver checks pass. Expanded once-only reconciliation
passes with the counts above. H69 KeySort passes in 1.408 s, Lean 4.24.0,
Lake 5.0.0-src+797c613. A first carrier-reflection attempt panicked on a
nonstructure; the optional structure-info guard fixed it. A generated-driver
attempt exposed unresolved universe metavariables; those now remain uncovered
and every final driver passes. Earlier failed attempts are retained externally. Final `./run-lean.sh` remains pending. No RUNTIME_GATE_PASS is claimed.

No production refactor is made. Original modules are byte-for-byte frozen.
The matched original-file median is 3.127804369 s before and 3.427619808 s
after, a 9.585492 percent increase (below the strict >10 percent stop boundary).
Both sides use three samples, symmetric warmup, the same original source/import
artifact hashes, CPU 0, Lean flags and resources. This narrow measurement is
not a whole-build performance claim. It was not repeated or cherry-picked.
Full affected/end-to-end measurements remain pending.

## Independent reviews

Read-only finder and skeptic used no Lean compiler or server. Both found and
confirmed fixes for the prose-reference scope error and absent frozen-map
comparison. Finder also confirmed inline-attribute and command-whitespace
handling; skeptic identified direct-child RSS limits and explicit VO1 ownership.
The corrected source acceptance passes. Follow-up reviews found no weakening
in the dependent existential construction or finite success controls. Skeptic
requested explicit right-associated source success; it has been added. All new Lean now passes compilation. Final reviewer findings also clarified
that resume records current artifact hashes and requested symmetric timing
warmup; both evidence corrections are applied. No review is represented as a proof.

Both H69 reviewers independently found inherited source-scan feasibility fields
that contradicted checked statuses. The reconciler now retains those only as
`source_scan_*` observations and supplies proof-qualified feasibility and witness
pointers. No semantic domain is upgraded by a syntactic tuple. Final read-only
follow-up checks found no unresolved defect; both accept this as a partial H69
checkpoint. Findings and dispositions are retained with the evidence.

## Remaining queue and original-VM handoff

1. Complete semantic global/input classification for the 1,134 proof records
   and coupled domain review for the 91 proof-bearing producers. Reflection
   and empty syntactic tuples do not finish that work.
2. Prove the 498 remaining joint tuples or classify further genuine intentional
   contradictions with checked evidence under H69; do not weaken an ordinary
   statement. Preserve parent obligations and owner routing V09, V12, VO1,
   with V07/P12 dependencies and H55 owner work left intact.
3. Extend supported-program success/totality beyond the finite fixture family,
   retain reject-all/always-revert controls, and resolve observable failure,
   bytecode gas and fork boundary obligations without invented premises.
4. Complete full `./run-lean.sh`, affected/end-to-end measurements and final
   finder/skeptic reviews. The narrow passing timing comparison is unchanged.

This H69 checkpoint covers four work items: intentional controls, expanded
proof/carrier inventory, empty-telescope checks, and universe-preserving
constructive cases. After committing, hand off for the required fresh thread
on the exact original VM, branch and existing persistent goal. Do not create
or reset a goal; keep it unfinished. There is no open scope question.

Reproduction uses the fresh external OLean cache built by `build_serial.py`,
then `h69_validate.py` under the repository writer lock. Bulk proof drivers,
per-declaration outputs, failed attempts and exact commands/exits/resources
live at `/workspace/h62-audit-compiler-transport/evidence/h69/`; deterministic
generators remain committed. Checksums cover the original patch, handoff,
bundle and evidence. The full gate is pending, so no RUNTIME_GATE_PASS is claimed.

No H55 producer work is duplicated. No push, merge, PR, pre-gate, deployment
or publication occurred. Only the coordinator may register area modules;
the committed test-only import fragment does not change a central root/map.

## H82 retirement: stopped, incomplete

The human explicitly retired this worker and assigned handoff to
`solidity-v12-v17-20261031/v16-correctness-transfer`. Implementation stopped.
The unvalidated Boolean-write draft is preserved byte-for-byte as
`tests/h62/item2/audit-compiler-transport/handoff/Totality.lean.pending`; its
single check exited1 at public_accepts (dependent compiler match), so it adds
no validated witness or totality result. No repair followed retirement.

Complete original thread assignment, original work/backfill queue, exact scope
manifest, later decisions and local checksums are committed under the same
`handoff` directory. The launcher-rendered goal object itself cannot be retrieved:
get_goal is unavailable. Its coordinator-reported hash is retained distinctly
from the saved thread-assignment byte hash. Remaining498 constants,91 producers,
semantic domains, broader success/gas/fork and final gates stay unfinished.

The only goal mutation exposed accepts complete or blocked, with no PAUSED
operation. The requested PAUSED state cannot be set via this API; no substitute
state, new goal or automatic continuation is authorized. This worker stops.
No H71 push permission is available here, so the original no-push restriction
remains in force. No branch or master was pushed. waits=[]; no external owner
wait is invented for unfinished work. Final head and exported patch/bundle,
handoff and evidence hashes are in the retirement result and SHA256SUMS.

Independent retirement finder and skeptic reviews passed with no preservation
findings: original queue/scope/owner routing and all seven handoff-file hashes
were verified read-only, without Lean/compiler/server calls. Review limitations:
pre-move draft byte identity has no separate independent snapshot; final commit
and export checks occur after review. No failed proof is upgraded by the review.

## 2026-11-07 authorized resumption and versioned re-baseline

The coordinator explicitly instructed this lane to resume after reporting its
head merged and gate.sh touched/finder/skeptic passed on origin/master.
Fetched and verified master `5da4771e63a4278ed53932ac39a032e3d7aea6ed`;
fast-forwarded this same assigned lane from its clean pre-existing coordinator
merge head `76a6dc24bb1b7805e2623f4c72773451719bcc7f`. The original retirement
head `9f773cbdc5f4d9e5996bb5e040dae638243c7e73` remains an ancestor.
No reset, discard, push, replacement goal or competing continuation occurred.
This explicit later instruction supersedes retirement's implementation stop;
the original scope/queue/evidence and all unfinished obligations remain.

The compiler-transport map now contains134 modules. Its original122 module
files are byte-for-byte unchanged;12 optimizer modules add248 source theorem
declarations. `rebaseline.py` writes separate exact-ref source snapshots and
transition evidence:560 retained source declarations,248 added,808 total,
zero removals. Added declarations retain their optimizer-owner routing and
are uncovered current-tree obligations. No original proof status is promoted
by source equality: transitive dependencies have changed, so current Lean
census/replay, proof-valued-definition/producer inventory and semantic domain
review remain pending. Historical1134 proof constants/498 uncovered/91
producer obligations remain distinct from this new source-only inventory.

Scanner coverage now includes mutual blocks, absolute `_root_` theorem names
and equation-style bodies. Independent finder and skeptic identified a first
attempt's confusion between type-level match arms and equation-body arms;
offside match tracking fixes the three reported truncations. Regression cases
cover both forms, nested comments, strings, root names and default binders.
Independent per-file keyword counts account for all808 declarations once.

Comparison with preserved historical census bytes also finds three older
signature spans that had consumed equation-proof text: `typed_sequencing_assoc`,
`MemoryJoinCost.cost_join`, and `MemoryJoinFrame.frame_join` (all in
`Solidity.Backend.Passes`). This is an extraction correction, not a Lean
statement or premise change. `acceptance.json` records old/corrected signature
hashes and unchanged full-module hashes; historical files are untouched.
Whole-module identity supports source preservation. Historical signature hashes
alone do not establish exact statement fidelity for these three cases.
Source-only extraction still needs elaborated Lean name/type reconciliation.

Reproduction, under the writer lock:

```sh
python3 scripts/h62/item2/audit-compiler-transport/rebaseline.py --ref 5da4771e63a4278ed53932ac39a032e3d7aea6ed --output /workspace/h62-audit-compiler-transport/resume-20261107/evidence
python3 scripts/h62/item2/audit-compiler-transport/resume_acceptance.py --ref 5da4771e63a4278ed53932ac39a032e3d7aea6ed --historical /workspace/h62-audit-compiler-transport/evidence/census.json --output /workspace/h62-audit-compiler-transport/resume-20261107/evidence/acceptance.json
```

Both commands pass. Original `census.py generate` remains frozen against the
original map and intentionally rejects the expanded map; its constant/criterion
was not silently repinned. The new versioned path reports the extension.
No Lean file was changed in this checkpoint. Actual tools remain Lean4.24.0
(797c613eb9b6d4ec95db23e3e00af9ac6657f24b) and Lake5.0.0-src+797c613.
No new runtime, KeySort or timing pass is claimed, and no RUNTIME_GATE_PASS.
The prior narrow+9.585492% timing evidence is historical, not a measurement of
this new tree. Full affected/end-to-end/final gates remain pending.

Next queue: replay/reconcile the current tree, complete retained498 uncovered
constants and91 producer domains, account for248 newly mapped source theorems
and their generated/proof-valued counterparts, then broader supported-success
and failure/gas/fork obligations and full validation. The preserved Boolean-write
draft is still unvalidated; no proof from it has been promoted. Independent
backfill remains the original scanner/census, negative controls, isolated
fixtures and deterministic acceptance/measurement work. waits=[]; no external
owner dependency wait is invented for unfinished proof/audit work.

Final independent read-only finder and skeptic follow-ups accept this source-only
checkpoint with no unresolved concrete finding. They do not establish current
Lean fidelity or semantic/proof completion. Four completed work items are the
safe re-baseline, scanner repairs, versioned inventory and acceptance regressions;
the required fresh-thread checkpoint handoff retains this VM/branch/original
unfinished goal. No competing continuation is created.
