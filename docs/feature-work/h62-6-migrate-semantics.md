# H62 item 6: migrate-semantics

Status: blocked, assignment incomplete. No RUNTIME_GATE_PASS or cut-over.

Repository `/workspace/solidity-lean`, branch
`codex/solidity-h62-6-20261106/migrate-semantics`, pinned base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. Published base fetched and verified
as ancestor of origin/master before branch creation. No push, merge, PR,
freeze, root registration, pin edit or tracked toolchain/configuration change.
Coordinator clarified that this isolated lane is the registered directory
writer and relay.sh exists only on its host. The prior owner-ack blocker is
resolved; no VM relay is needed. Exact committed head is in exported handoff.json.

## Changes for live owners at cut-over

- `Solidity/Semantics/AbiAccess.lean`: replace 15 obsolete Except.noConfusion
  applications with constructor case elimination. Move bodyValuesA_off's
  simplification after Entered constructor splitting; remove an empty simp.
  No declaration signature, executable definition, import, guard or budget change.
- `Solidity/Semantics/AbiEntryProofs.lean`: prove tailFits_of via symbolic bounded
  modular arithmetic, retaining its exact statement. Seven new private declarations:
  subAt, subAt_eq_sub_of_le, tailFits_at, tailFits_transfer, slt_of_toInt_lt,
  lim_add_one_lt_H, H_lt_W. subAt is a private arithmetic helper matching existing
  sub; the other six are proved lemmas. Zero-tail wraparound and positive-tail
  subtraction are separate cases. The opaque reflection lemma avoids kernel
  recursion in instantiated decision procedures. Reorder regionFits_of's
  reflection/case splitting; explicitly simplify cvalAt's false branch.
  All original statements, executable definitions, axiom guards and limits remain.
- Add scoped census, clean diagnostic, compatibility survey, freeze-manifest
  tooling, five scanner negative controls and four isolated Except proof examples.
  No additional production module/import registration is requested.

The arithmetic refactor warning was given before work. File history contained
4fad27235 and 2e7af4b2e, with no speed change being undone. Failed experimental
proofs are not retained in the committed source; their logs remain off Git.
No new sorry, axiom, native_decide, premise/exclusion, or heartbeat/recursion limit.

## Checkpoints

1. Partial: 82 scoped source files and 162-module dependency closure inventoried.
   Full source hashes account for every original file. Old clean diagnostic
   passes 111 modules then stops in out-of-scope Source.Horizon at 300.188759636s,
   exit -9/MODULE_300S_STOP. Interrupted total wall 989.583601066s and peak child
   RSS 3728392 KiB are not a full baseline. BASELINE_INCOMPLETE remains open.
2. Partial: official coordinator archive SHA256
   7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d verified.
   Lean 4.35.0 Release commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
   Lake 5.0.0-src+eb6cafb. Old Lean 4.24.0 Release commit
   797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake 5.0.0-src+797c613.
   KeySort passes on both. All five independent ABI modules now pass on 4.35.
   Both modified files also pass on 4.24, including unchanged axiom guards.
3. Blocked: full clean new build, affected validation and run-lean.sh pending.
   Compatibility survey visits all 162 modules: 19 pass, 4 fail, 139 dependency
   blocked. The in-scope failure AbiEntryProofs is repaired in later samples;
   5 assigned modules pass, remaining 77 retain external dependency blockers.
   The survey itself has not been rerun after that repair. No old-version
   artifacts were imported into new checks and no per-master cache was used.
4. Partial: patch/bundle, source and lexical theorem-header hashes, dependency
   request report and checksums exported for coordinator retrieval. 80 of 82
   sources are identical to base. Public theorem headers in the changed two
   match base exactly. These hashes/reviews are not elaborated API equivalence.
   Delivery to migrate-root-gate and final cut-over remain coordinator work.

## Matched samples and escalation

sample-old-02 and sample-new-01 rebuild the same two modified files, using
identical source hashes, module order, serial settings, corresponding already
built import libraries, 12 GiB address-space cap, no host swap and 4 GiB reserve.
This is incremental file checking, not a clean full-directory benchmark.

| Measure | Lean 4.24 | Lean 4.35 | Change |
|---|---:|---:|---:|
| AbiAccess wall seconds | 5.769160289 | 4.015150842 | -30.40% |
| AbiEntryProofs wall seconds | 6.779386821 | 4.763259294 | -29.74% |
| Combined wall seconds | 12.548547110 | 8.778410136 | -30.04% |
| Peak child RSS KiB | 410744 | 560936 | +36.57% |

ESCALATE: MEMORY_REGRESSION_OBSERVED. Heavy checks are held pending QMEM:
does the >10% stop apply to this RSS increase or only wall slowdown? Options:
hold while gate investigates, or coordinator clarifies wall-only threshold and
proceeds within unchanged memory bounds. Neither full-directory wall delta nor
resource acceptance is established. Later lightweight checks do not clear the hold.

## External owner requests

No edits outside assigned scope. Request statement- and budget-preserving
migration overlays from corresponding owners/root gate:

- Syntax.Raw: String/Slice API failures at lines 597, 650, 665, 682, 684.
  New drop returns Slice, Slice.toList/String.dropRight availability and endsWith
  method shape differ. Most assigned modules transitively depend on this.
- Hash.CollisionBound: countP/contains goal at 407, omega failures at 660/680,
  resulting axiom guard failures. Do not repin failures or weaken statements.
- Source.Ctor: original 200000-heartbeat exhaustion at 641 and dependent
  elimination failures at 715. Preserve that budget and all admission exclusions.
- Old baseline Source.Horizon: original source exceeds diagnostic 300s bound.
  Coordinate baseline/gate resolution; no theorem or resource limit was relaxed.

Exact commands, errors, source hashes and per-module dependency statuses are in
survey-01 and old-clean-02, under `/workspace/h62-migrate-semantics-evidence/`.
The original new-clean-01 failure is superseded only for the repaired files.
old-clean-01 was invalid tooling (missing GNU time); sample-old-01 used a
version-specific lemma alias and failed. Neither is a passing gate.

## Reproduction, reviews and remaining work

Run the following from the repository root; diagnostic commands write off Git:

```sh
python3 scripts/h62/item6/migrate-semantics/census.py --out /workspace/h62-migrate-semantics-evidence/census.json
python3 scripts/h62/item6/migrate-semantics/measure.py --toolchain /workspace/.setup/tools/lean-4.24.0-linux --out /workspace/h62-migrate-semantics-evidence/old-clean-02
python3 scripts/h62/item6/migrate-semantics/probe.py --toolchain /workspace/h62-migrate-semantics-evidence/lean-4.35.0-linux --lib /workspace/h62-migrate-semantics-evidence/new-clean-01/lib --out /workspace/h62-migrate-semantics-evidence/survey-01
python3 scripts/h62/item6/migrate-semantics/freeze.py --base c6f550e281a7e5affa9a99bc2cdaed556dec00e4 --out /workspace/h62-migrate-semantics-evidence/frozen-source-and-signatures.json
python3 tests/h62/item6/migrate-semantics/scanner_controls.py
node scripts/check-layers.mjs
```

Existing output directories are refused; choose new names on repeat. The two
sample commands use probe.py with --only Solidity.Semantics.AbiAccess --only
Solidity.Semantics.AbiEntryProofs and corresponding old/new toolchain/lib paths.
All actual module commands/exits/timings are recorded in summary.json. survey-01
predates final probe hardening (unknown target rejection, public import handling,
nonzero exit on failures); its recorded module statuses remain valid.

Independent read-only finder and skeptic reviews used no Lean/server or edits.
Both found proof-only repairs preserve statements, cases, pins and budgets.
Findings fixed: unused simp arguments; scanner comments/strings/attributes and
root consumers; missing time dependency; source cleanliness; resource summaries;
process cleanup and exit race; survey unknown targets/public imports. Reviewers
confirmed matched hashes, metrics and limits of lexical/interface evidence.
Existing conditional-lemma deprecation warnings remain for old/new compatibility.

Five scanner controls pass. Four isolated constructor proofs pass both versions
but do not validate production modules themselves. Layer check passes: 857 core
modules, zero elaborator or checked-parser reachability. Python AST checks pass.
No Lean MCP tools exposed; bounded serial CLI diagnostics were used. Final
repository run-lean.sh, frozen SolKey conformance and affected validation remain
pending, so no RUNTIME_GATE_PASS. VM cap is 16 GiB; no systemd-run used.

Three work items completed this turn: AbiAccess repair, full compatibility survey,
and AbiEntryProofs repair/review. Fresh-thread handoff goes to the coordinator
with this same original VM/branch/goal, not a replacement goal. Resolve QMEM and
external migration overlays, then repeat clean matched builds, verify elaborated
interfaces, finish affected/final gates and root-gate handoff. Full assignment
remains unfinished; maintain all original proof/resource budgets.
