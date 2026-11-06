# H62 item 2: typing/frontend empty-statement audit

Status: partial; resumed on v4.24.0. RAW-435 and QRAW-435 are resolved by coordinator clarification. No global checkpoint is complete.
Owner: solidity-h62-2-20261106/audit-typing.
Branch: codex/solidity-h62-2-20261106/audit-typing.
Frozen base: c6f550e281a7e5affa9a99bc2cdaed556dec00e4.
Repository: /workspace/solidity-lean.

## Current coordinator clarification and v4.24 evidence

Coordinator answer, verbatim: Lean v4.35.0 applies ONLY to the toolchain-migration batch (solidity-h62-6) on its migration branch. Your lane stays on master's toolchain v4.24.0; do not install or overlay v4.35. Continue your queue on v4.24.0 and end the turn with a CLOUDVM-RESULT.

This supersedes every v4.35 requirement and RAW-435 blocker/escalation below. QRAW-435 is answered; no Raw producer edit or overlay is requested. No goal was created or reset. No get_goal/resume tool is exposed. Branch, base, frozen interfaces and exclusive scope remain unchanged.

Current binaries: `/workspace/.setup/tools/lean-4.24.0-linux/bin/{lean,lake}`. Actual Lean 4.24.0 release commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Lake 5.0.0-src+797c613 (Lean 4.24.0). Evidence/output path: `/workspace/h62-audit-typing-evidence/v4.24.0/`. No historical v4.35 artifacts are consumed.

All 28 frozen Typing.Values prerequisites passed on v4.24.0, including KeySort and Raw unchanged. All 23 Closure source witnesses passed again. Its actual v4.24 census is 32 constants: 23 source plus 9 generated with interface/witness obligations pending. The historical 33-count is specific to v4.35.

Nine new simultaneous association-list witnesses cover Values.lean source declarations at lines 39–145, using two inhabited Bool carriers and the actual key DecidableEq instance. Their explicit whitelist extends the restricted premise-comparison helper; every data/proposition binder is retained. ValuesListsWitnesses.lean and ValuesListsFidelity.lean live under the owned tests directory. Exact signatures for all 228 Values theorem constants are saved off Git; only these nine Values declarations are witnessed so far. None of the remaining statements is excluded or certified.

Reproduce: `python3 scripts/h62/item2/audit-typing/build_typing_values.py`, then `python3 scripts/h62/item2/audit-typing/check_closure.py`. The first records frozen-source and output hashes for all 28 dependencies. The second verifies those hashes before consuming artifacts and checks seven files, 23 Closure + 9 Values-list witness mappings, both omitted-premise rejection controls, and axiom reports. Both retain writer locking, serial -j1, explicit memory/time bounds and a continuous 4 GiB reserve guard.

Independent read-only finder/skeptic reviewed the toolchain correction and all nine bundles without Lean/server. No omitted premise found. Both requested explicit dependency artifact provenance; source/output hashes now address that finding. Only existing propext or no axioms appear in witness dependency reports. No frozen source edits, new axioms/sorry/native_decide or increased heartbeats. Full assignment gates, live owner resolution, remaining modules and compiler success contracts remain pending. No proof-refactor timing comparison is claimed.

## Historical saved work (superseded toolchain/blocker claims)

## Saved source backfill

The deterministic generator is `scripts/h62/item2/audit-typing/source_census.py`.
Run from this checkout:

```
python3 scripts/h62/item2/audit-typing/source_census.py --output /workspace/h62-audit-typing-evidence/source-census.json
```

It reads frozen Git objects, expands every code-first Lean module row in the typing/frontend maps, deduplicates paths, and preserves exact complete source including section variables. Bulk JSON stays off Git. Current output: 309 unique modules, 3207 lexical candidates, zero unmatched patterns. These counts are NOT verified interface statement counts. Comments/strings may create candidates; macros may be missed. Fully qualified names, elaborated signatures, owner resolution, classification of global versus per-input hypotheses and all simultaneous witnesses remain unresolved. The Closure subset below now has elaborated signatures and checked premise witnesses; other source candidates remain unresolved.

## Setup and checks

Initial checkout was clean `work` at 6cf853aea0417155aca29ddb91f1767d3f3a3cc4. Exact base absent locally. `git fetch origin master c6f550e281a7e5affa9a99bc2cdaed556dec00e4` exited 0. `git merge-base --is-ancestor c6f550e281a7e5affa9a99bc2cdaed556dec00e4 origin/master` exited 0. Assigned branch created at exact base under writer lock; existing clean branch preserved. No push/merge/PR.

All five coordinator input hashes matched `/workspace/h62-coordinator-inputs/sha256.json`. Downloaded the official pinned v4.35.0 Linux archive into off-Git evidence. SHA256: 7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d.

Actual binaries: `/workspace/h62-audit-typing-tools/lean-4.35.0-linux/bin/`.
Lean: 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release.
Lake: 5.0.0-src+eb6cafb (Lean 4.35.0).
Tracked lean-toolchain remains unchanged; no v4.24 cache was used.

KeySort command: `LEAN_NUM_THREADS=1 /workspace/h62-audit-typing-tools/lean-4.35.0-linux/bin/lean -j1 --memory=11000 --tstack=131072 Solidity/KeySort.lean` under writer lock, Python 120-second timeout. Exit 0, empty diagnostics, 1.416963547 seconds, peak RSS 507048 KiB. Evidence: `/workspace/h62-audit-typing-evidence/keysort-result.json`. Initial timing wrapper failed before running Lean because `/usr/bin/time` is absent; recorded in keysort.log and superseded by the successful Python-timed run.

VM: cgroup memory.max 17179869184 bytes; no active swap; approximately 16 GiB initially available. No systemd-run, no concurrent heavy Lean processes, no raised proof budgets. Runtime prerequisite only: no full RUNTIME_GATE_PASS or proof audit pass is claimed.

Generator run twice; `cmp` exited 0. `git diff --check` passed. No frozen Lean sources or statements edited; additive audit modules now exist under the owned tests directory. New axioms/sorry/native_decide: 0. No before/after proof timing comparison exists because no proof refactor was made.

## Independent reviews

Finder and skeptic agents reviewed read-only, neither using a Lean server or running Lean. Both verified every retained source and SHA256 against frozen Git objects, unique paths, all 21 typing and 264 frontend map rows, and the preliminary-only disclaimers. Neither found a material issue. Finder flagged unused import and wildcard crossing directory boundaries; removed import and constrained wildcard matching per path segment. Regeneration retained the same 309/3207 counts and was byte-identical across two runs. No claim of reviewing the unfinished proof audit is made.

## Remaining checkpoints and continuation

1. Inventory: exact elaborated frozen signatures and live producer owners for EVERY interface theorem with hypotheses. Source candidates are only backfill.
2. Witnesses: simultaneous inhabitant of every complete hypothesis bundle, importing unchanged interfaces. Closure source statements have 23 checked witnesses; all other modules remain pending.
3. Success: supported-program totality/success and negative reject-all/always-revert controls, observable failure/gas/fork boundaries. None yet.
4. Fidelity: Closure has a 23-source/10-generated provenance reconciliation (generated interface status pending); other modules and live owner resolution remain pending.

Next: use verified official binary and an isolated output/cache configuration to elaborate imports for a Lean environment-based declaration census. Reconcile it with frozen source candidates and resolve owner mapping; do not claim regex as signature fidelity. Maintain the 4 GiB reserve and serial bounded checks. Existing-file edits outside owned paths remain forbidden; owner registration fragments and tickets go through coordinator. No frozen theorem weakness has been established, so no theorem ESCALATE lines or repair premises have been invented.

No get_goal tool is exposed; coordinator explicitly confirmed this is not a blocker. No goal was created/reset/stopped. Three useful items are saved: source backfill, the Closure witness/fidelity subset, and the frozen typing dependency reproduction/owner ticket. No global checkpoint is complete. The 3–5-item fresh-thread handoff threshold is now reached; handoff is to coordinator, with no replacement goal/thread self-launched. Full affected validation, acceptance, census/witness audits, totality proofs and final finder/skeptic milestone reviews remain pending.

## Closure witness/fidelity subset (second saved work item)

Owned additive modules:

- `tests/h62/item2/audit-typing/DeclarationCensus.lean`: exact theorem type reflection and a deliberately Closure-restricted premise-bundle comparison command.
- `tests/h62/item2/audit-typing/ClosureCensus.lean`: reflects unchanged imported Closure.
- `tests/h62/item2/audit-typing/ClosureWitnesses.lean`: 23 kernel-checked simultaneous feasibility bundles.
- `tests/h62/item2/audit-typing/ClosureFidelity.lean`: one comparison for each original source theorem, dependency reports, and a deliberately mismatched witness rejected under `#guard_msgs`.

Reproduce with `python3 scripts/h62/item2/audit-typing/check_closure.py` from this checkout. It verifies frozen source bytes and the official archive hash, takes the writer lock, runs five serial bounded checks with explicit `-j1`, preserves a 4 GiB reserve throughout each process, uses isolated outputs, and records commands/exits/timings. No Lean MCP tools are exposed; per-file CLI diagnostics are used. Full `./run-lean.sh` remains a final assignment gate, not claimed here.

Final run: all five commands exited 0. Frozen Closure has only upstream deprecation warnings; owned modules have empty warning/error diagnostics apart from intended census/fidelity/axiom reports. Latest sampled times in seconds: Closure 1.308, reflection helper 2.708, witnesses 0.404, census 1.108, fidelity 0.907. These are subprocess samples, not a controlled before/after performance comparison; cache/resource variation prevents such an inference. Maximum cumulative child RSS: see `closure-check-results.json`. No speed refactor or original-interface edit occurred; no comparable before/after refactor delta is claimed.

Exact closed kernel expressions and universe parameters are retained in `closure-coverage.json`, alongside supplementary pretty signatures. Per-binder expressions contain local free-variable identifiers and are NOT standalone closed signatures. The census contains 33 unique theorem constants: 23 source interface declarations and 10 generated equation/proof/recursor constants with interface status explicitly pending. Generation is provenance, not an authorized exclusion: public constants such as `iter.eq_1`, `iter.eq_def`, `insertNew.eq_1` and `Reach.brecOn` may still require interface witnesses. All ten retain pending interface/witness obligations. The generated constants receive no feasibility certification; local contradictory assumptions in compiler-generated proof fragments must not be passed off as public premise witnesses.

All 23 source names are reconciled exactly once against frozen source declarations; all 23 witness names appear once. Twenty-one have proposition premises, including membership implications after the result colon. `foldl_insertNew_length` and `iter_closed_or_long` have no proposition premises but retain their global carrier/equality data and all residual inputs in explicit data/True witness bundles. Bool is an actual inhabited carrier and the elaborator supplies its actual DecidableEq instance where the original theorem retains one. The two `omit` theorems (`Reach.trans`, `Closed.reach`) have no such instance binder. These are existential feasibility claims, not claims that every carrier or program is feasible.

The witness proofs are checked by Lean's kernel. The correspondence checker is metaprogrammed definitional-equality comparison, not a separately proved equivalence theorem. Its allowed signature family is restricted to reviewed Closure originals; it validates the first carrier shape and requires Closure's module index explicitly. Broader use needs explicit handling of dependencies on proof binders and carrier shapes. The negative control tries to replace `foldl_insertNew_grows`' simultaneous membership/nonmembership premises with a Nodup-only bundle, and must fail. Dependency reports contain only existing `propext` or no axioms; no `sorryAx`, custom axioms or trust shortcuts.

Finder and skeptic independently reviewed the original 21 bundles, then the two global-data bundles and final deltas, without Lean/server. Both confirmed every source theorem mapping and simultaneous hypotheses. Fixed findings: explicit global-instance accounting; fail-closed module-index guard (prevent None/None success); unique-name acceptance rather than marker count. The runner additionally generates `closure-coverage.json` with explicit source/generated provenance classification with generated interface status pending and owner nulls. Live producer identity remains unresolved: source history points to G12 (`a76a7490321cbaac906872513501955139c34591`, author Claude), which is historical attribution, not current ownership. Coordinator follow-up is needed for current exact producer mapping; no producer file edits or theorem repairs are requested. No relay.sh exists in the checkout, so no relay delivery is claimed.

Unchanged AST also compiled successfully with the pinned toolchain into isolated output (`ast-build.log`); this is only dependency provisioning, not the typing audit. Next work: build the remaining frozen dependency graph serially, extend elaborated census, resolve producers, then add per-statement feasibility bundles and supported-program/compiler success contracts. The full four-checkpoint assignment remains partial. No weakened/vacuous source interface was established in this subset, so no theorem ESCALATE line was invented.

Final finder caveat retained: no complete Closure-module coverage is claimed. Generated constants are not silently excluded. Full census must settle their interface status and audit included declarations before any checkpoint can close. Both final reviews otherwise passed the current 23-source subset and runner hardening.

## RAW-435 dependency blocker and coordinator handoff (third saved item)

`python3 scripts/h62/item2/audit-typing/build_typing_values.py` constructs the 28-file frozen dependency order for Typing.Values, checks every source byte, and compiles serially with the pinned official binary into isolated outputs. It stops at the first error. Actual results: KeySort/AST/SpecSyntax exit 0; unchanged Syntax.Raw exits 1 with five String/Slice API errors at lines 597, 650, 665, 682, 684. No resource or timeout stop. Commands and measured times are in `typing-values-build-results.json`; decisive diagnostics are in `Solidity_Syntax_Raw.lean.build.log`.

Owner ticket: `tests/h62/item2/audit-typing/RAW-MIGRATION-TICKET.md`, stable blocker RAW-435 and question QRAW-435. It includes the exact import path, diagnostics, constraints, two authorized-handoff alternatives and independent finder/skeptic confirmation. No producer-owned source was edited. No relay is available, so delivery is pending coordinator retrieval rather than claimed sent.

ESCALATE: action compile frozen Solidity/Syntax/Raw.lean on mandated Lean v4.35.0 fails with five String/Slice API errors (RAW-435); options: producer-approved compatibility overlay preserving public interfaces, or coordinator-supplied approved source-correlated dependency overlay with hashes/fidelity evidence. Neither option weakens a theorem or authorizes this worker to edit Raw.

Full completion is blocked until an approved dependency handoff exists; remaining frontend/scanner/fixture backfill is not asserted blocked or exhausted. No 8–10-hour queue completion is claimed. All four checkpoints, all global final gates, live owner resolution and pending generated-constant interface/witness obligations remain unfinished. The persistent goal must remain unfinished, with this typed dependency blocker retained.

Fresh-thread handoff: original VM environment ccarenv_b64_Y2NhcmVudl8zMWE4NTM2NTg3MWM4MTkxYmM5NDM2MzdlNTU1N2FhZQ; repository /workspace/solidity-lean; assigned branch and base above. Existing original persistent goal is the supplied SHA256 38c86c8ae936d7d46882834692303bd39eccdd174f345bb4e862706b89d21d5e. get_goal remains unavailable; no goal creation/reset/replacement is authorized. Coordinator should continue the same saved goal/state after dependency resolution or schedule the remaining unaffected in-scope backfill in the required fresh thread. Never self-launch a replacement.

## Latest v4.24 acceptance and handoff

Final hardened prerequisite run: 28/28 exit 0, no resource/time stops, total measured subprocess time 107.802 seconds. Commands, individual times and source/olean SHA256s: `v4.24.0/typing-values-build-results.json`. Actual versions: `v4.24.0/versions.txt`. KeySort passes as the first bounded prerequisite. Raw passes unchanged, closing the obsolete migration question for this lane.

Final hardened subset run: 7/7 exit 0, no guard stops. Times in seconds: Closure 0.803; reflection helper 1.405; Closure witnesses 0.502; Closure census 1.005; Closure fidelity 0.803; Values-list witnesses 0.803; Values-list fidelity 1.806. Acceptance records: `v4.24.0/closure-check-results.json`. The runner validates results against the saved 28-file plan; the plan's full frozen dependency closure and topological order were independently reviewed. It checks every planned frozen source hash and corresponding artifact hash before importing Values. It does not independently reconstruct the plan on each acceptance run.

Both read-only reviews independently verified all 28 source/artifact hashes and confirmed all seven checks. No omitted hypothesis in the nine added bundles. Fixed findings: dependency artifact provenance and duplicate Python import. No new/custom axioms; witness dependency reports show only pre-existing propext or no axioms. The comparison helper remains deliberately restricted to reviewed signatures. No source theorem weakness or vacuity was established; no theorem repair or premise change is requested.

Queue remains unfinished. Thirty-two source witnesses do not complete an area-wide checkpoint. Other Values source declarations, generated constants, remaining module-map files, current producer owners, compiler success/failure/gas/fork controls, full affected builds/acceptance and final whole-audit reviews remain pending. Historical v4.35 results do not count as current gates. No RUNTIME_GATE_PASS or full assignment completion is claimed. Before/after proof-refactor timing remains unavailable because no frozen proof implementation was refactored.

This continuation adds toolchain recovery/validation and the nine-lemma witness/fidelity item to the saved work. Preserve the same original goal and branch; do not create/reset a goal or self-launch a replacement. Coordinator fresh-thread handoff can continue from the exact original VM and saved state recorded above. RAW-435 is resolved, not a reason to stop work. The next in-scope work is additional Values witnesses and broader elaborated census coverage, then supported-program compiler success contracts.

## Defaults input-telescope milestone

Before selecting this item, fetched origin/master (96788a953) and inspected its history/code. No master changes to frozen Typing.Values or overlapping audit files were present, so the conditional rebase was not triggered. Assigned branch/base and all producer files remain unchanged.

Six new witnesses: SVal.dfltBelow_irrel, SVal.dfltBelow_dflt, SFields.dfltBelow_eq, SVal.dflt_all, SFields.dflt_all, SVal.dfltBelow_all. ValuesDefaultsWitnesses.lean retains all original data and proof inputs in one existential telescope. One actual Hered predicate truthH simultaneously inhabits harr/hfix/hmap; default_below also supplies its per-input rank proof. Individually inhabited assumptions are not substituted for this simultaneous bundle.

The additive #audit_full_inputs helper is restricted to these six original names and rejects unreviewed universe parameters. It builds nested Exists over every original binder, including proof-dependent inputs, terminating in True; the unchanged conclusion is deliberately not asserted as a feasibility premise. Fidelity is checked by metaprogrammed definitional equality, while kernel-checked witness proofs establish feasibility. Negative control drops all three shared global conditions and is rejected; zero_rank_rejected proves that a satisfiable global predicate does not make an impossible per-input rank bound feasible. The negative control is not counted as statement coverage.

Run python3 scripts/h62/item2/audit-typing/check_closure.py: now nine files, all exit0/no guard stops. Six distinct defaults mappings add to previous32, yielding38 distinct source witnesses. Timing samples and commands are in v4.24.0/closure-check-results.json. No source implementation was refactored; no controlled before/after proof-refactor delta is claimed. Frozen Values bytes remain exact. Standard propext or no axioms only; zero new axioms/sorry/native_decide/heartbeat increases.

Independent read-only finder and skeptic reviewed all six original signatures, the full-telescope construction, both controls and recorded acceptance. Neither used Lean/server; neither found a missing hypothesis or padding. Both confirmed same-P simultaneous global conditions and per-input rank evidence. Remaining Values/module-map statements, generated-constant obligations, live owners and supported-program compiler contracts remain pending. This is another subset milestone, not completion of a global checkpoint.

Recorded timings: Closure.lean=0.803s, DeclarationCensus.lean=1.609s, ClosureWitnesses.lean=0.502s, ClosureCensus.lean=1.105s, ClosureFidelity.lean=0.904s, ValuesListsWitnesses.lean=0.803s, ValuesListsFidelity.lean=1.907s, ValuesDefaultsWitnesses.lean=0.803s, ValuesDefaultsFidelity.lean=1.004s
