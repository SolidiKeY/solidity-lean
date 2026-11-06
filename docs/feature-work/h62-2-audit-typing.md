# H62 item 2: typing/frontend empty-statement audit

Status: partial; none of the four checkpoints is complete. Persistent goal remains unfinished.
Owner: solidity-h62-2-20261106/audit-typing.
Branch: codex/solidity-h62-2-20261106/audit-typing.
Frozen base: c6f550e281a7e5affa9a99bc2cdaed556dec00e4.
Repository: /workspace/solidity-lean.

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

No get_goal tool is exposed; coordinator explicitly confirmed this is not a blocker. No goal was created/reset/stopped. Two useful items are saved: source backfill and the Closure witness/fidelity subset. Neither completes a global checkpoint; fresh-thread threshold has not been reached. Full affected validation, acceptance, census/witness audits, totality proofs and final finder/skeptic milestone reviews remain pending.

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
