# H62 item 4 — generic compiler passes

Status: **blocked, not complete**. Branch `codex/solidity-h62-4-20261106/generic-passes` starts at exact published base `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. Repository: `/workspace/solidity-lean`. No original family source, frozen interface, generated root, central module map, axiom pin or toolchain file was edited. No push, merge, pre-gate or deployment.

## Checkpoints and original inventory

1. **Census done at the lexical source level.** All 313 original Passes Lean modules, including 83 `*Controls` modules, are inventoried: 3,519 declarations, 1,946 in Controls. The complete original declaration/case inventory and exact source-signature hashes are `/workspace/h62-generic-passes-evidence/original-census.json`; its SHA256 is `9f5ba355c076e5328e8542a9d478b442a7dc4e6505c5c122b83750fa128c5c94`. All 313 whole-file hashes match the pinned base. All files, including pins, negative controls and fixtures outside the Controls filename suffix, are retained. Names are local, disambiguated by source path/line; these hashes are lexical source signatures, not elaborated type hashes. Independent scanner review found and fixed inline-attribute and equation-header omissions. The reproducible manifest stays in [inventory-manifest.json](../../tests/h62/item4/generic-passes/inventory-manifest.json); bulk inventory stays off git under H44.
2. **Generic lemma and fixtures partial.** [Generic.lean](../../tests/h62/item4/generic-passes/Generic.lean) proposes `H62Generic.prefix_value` on `Prog C Γ Δ`, the actual `CompiledProg`, dependent `CompiledVal`, original compiler Input, source run and reached-state evaluation. It preserves full mapped output, one canonical machine/address map before every saved tail, value representation and both stage/whole executions. `saved_tail_refused` is an additional parameterized negative lemma. No arithmetic producer is duplicated. [Fixtures.lean](../../tests/h62/item4/generic-passes/Fixtures.lean) has six dependent records: addition/subtraction/multiplication × legacy/viaIR. Every record carries the actual selected program and dependent value code, original populated machine, original final machine, exact expected word and complete ordered cell list. **Neither file has passed Lean validation.**
3. **Correspondence and reproduction partial.** [Instances.lean](../../tests/h62/item4/generic-passes/Instances.lean) copies all three original execution signatures exactly, renaming only the theorem. Each proof calls the generic lemma and retains its live owner Source transport. Three `exact_*_type` declarations target the original full types. [Correspondence.lean](../../tests/h62/item4/generic-passes/Correspondence.lean) retains exact-type aliases for all 36 original Controls theorems (11 addition, 12 subtraction, 13 multiplication), including stale RHS, short frame, corrupted tail, pipeline distinctions, unmasked result and range controls. Fixture correspondence also references owner proofs. Lexical identity checks pass; elaborated equivalence and axiom sets remain pending.
4. **Before/after measurement blocked.** [measure.py](../../scripts/h62/item4/generic-passes/measure.py) prepares paired original/candidate pass bodies with identical imports/signatures/cache/resources, five alternating-order samples after warmup, and stops above 10% median slowdown. It refuses to run without full additive acceptance bound to current source/artifact hashes and the exact official toolchain pin. No measured delta is claimed. Frozen inventory is available in full, not reduced to six rows.

## Audit matching and boundaries

Audit 9 explicitly names `Assignment{Addition,Multiplication,Subtraction}{Pass,Controls}`; these six files are the selected factoring candidates. Original physical composition was repeated across the three Pass execution proofs. Their Source transport and operator-specific `reached_value` proofs remain with the proving lanes. History inspected: `f14b2f071`, `8de18e2ce`, `346d0d8ec`; no earlier speed change was reverted. Refactor slowdown warning was given before candidate work.

Audit 11 is addressed by consuming existing `compilation_success_shared_mapped` and `CapturedValueStability.value_shared`, with local `pushes_zero`/allocation-cost consumers recorded in the manifest. Evm/MemoryCopies producers and fixtures are outside this lane. Audit 16 supplies the table/parameterized-lemma pattern; this lane does not take its named other-area work. H55 retains Yul Raw/vector generation. This work neither generates Yul vectors nor edits or duplicates that producer. Intrinsic dependency-free core and Gate G0 are preserved; no indexed-family evaluator or frozen statement was changed.

## Actual checks and decisive evidence

All evidence below is under `/workspace/h62-generic-passes-evidence/`.

| Gate / command | Result | Evidence |
| --- | --- | --- |
| `git fetch origin master`; exact base object and `git merge-base --is-ancestor c6f550e281a7e5affa9a99bc2cdaed556dec00e4 origin/master` | Pass; assigned branch created at base | Branch ancestry rechecked before commit; setup uses published base, no reset |
| Coordinator input SHA256 verification | Pass, all five files | `input-verification.log`; input manifest `/workspace/h62-coordinator-inputs/sha256.json` |
| Official release archive SHA256 | Pass: `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d` | `toolchain-verification.json` |
| Actual Lean/Lake versions | Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake 5.0.0-src+eb6cafb | `versions.log` |
| `python3 scripts/h62/item4/generic-passes/bounded.py keysort-v435 -- -j1 --tstack=131072 Solidity/KeySort.lean` | Pass, exit 0, 2.2904 s, 495012 KiB peak group RSS | `keysort-v435.json`, `keysort-v435.log` |
| `python3 scripts/h62/item4/generic-passes/accept.py --lexical-only` | Pass, scanner boundaries plus 3 exact signatures/36 aliases | `final-lexical-check.json` |
| `python3 scripts/h62/item4/generic-passes/census.py --check /workspace/h62-generic-passes-evidence/original-census.json` | Pass, exact census and all original files unchanged | `final-census-check.json` |
| `python3 scripts/h62/item4/generic-passes/accept.py` (initial invocation, before adding required unique IDs) | **Fail**, frozen `Solidity/Syntax/Raw.lean`, exit 1, 4.2380 s, 1462220 KiB peak group RSS | `accept-first.log`, `closure-0003-Raw.log`, `closure-0003-Raw.json` |
| `python3 scripts/h62/item4/generic-passes/accept.py --run-id final-plan --plan-only` | Pass, complete plan of 329 sources; no Lean invoked | `final-plan.log`, `final-plan-closure.json` |
| `python3 scripts/h62/item4/generic-passes/measure.py --run-id blocked-final --acceptance /workspace/h62-generic-passes-evidence/missing-acceptance.json` | Correct refusal, exit 1; no successful acceptance exists | `final-timing-prerequisite.json` |
| Python AST parse of all four scripts | Pass | `python-source-parse.log` |
| Additive theorem elaboration, exact type/axiom checks, affected validation and final `./run-lean.sh` under migrated configuration | **Pending / blocked** | No `RUNTIME_GATE_PASS`, no acceptance-pass manifest |

The first three closure sources (KeySort, AST, SpecSyntax) passed under 4.35. Raw fails at lines 597, 650, 665, 682/684: String operations now return `String.Slice`, `.toList`/`.dropRight` no longer resolve as before, and the method section `c.endsWith` has a different inferred type. These are existing source incompatibilities outside write scope; no workaround, trust change or 4.24 cache was used.

The runner uses official 4.35 only, `LEAN_NUM_THREADS=1`, explicit `-j1`, a per-process hard 12 GiB address-space cap, sampled aggregate 12 GiB RSS cap, host+cgroup 4 GiB reserve and no host swap. The enclosing VM has a 16 GiB cgroup limit. Limits are reported accurately: the group RSS cap is sampled, not a hard cgroup limit. It locks the shared writer lock and cleans only its own process group. Neither systemd-run nor concurrent heavy Lean jobs were used. No Lean MCP tools were exposed. The existing v4.24 installation was discovered but no migration proof used it.

## Independent reviews and fixes

Read-only finder `/root/finder` and skeptic `/root/skeptic` used no Lean server/build and made no writes. Both reviewed the census, resource runner, typed fixture/instance candidates and reproduction/timing boundary. Confirmed findings were fixed: 17 omitted attributed declarations, equation-body signature pollution, `where` token boundaries, v4.24 hardcoding, explicit thread enforcement, cgroup reserve, descendant cleanup, repeated-run log collisions, missing actual generic instances and stale-output timing acceptance. Final narrow review found no remaining concrete static issue. `reviews.json` records findings and limitations. Static reviews establish no Lean theorem or axiom claim.

## Typed blockers and owner relay

- **B-TOOLCHAIN-RAW (prerequisite / outside scope):** coordinator's migration owner must repair or supply an approved migrated `Solidity/Syntax/Raw.lean` on the pinned 4.35 baseline. Do not edit it here. Resume the full 329-source additive closure after that dependency arrives; additional compatibility errors may still surface.
- **B-PROOF (required validation):** all four additive Lean files, exact original-type checks, axiom audits and retained negative controls remain unvalidated because that prerequisite failed. Textual scan finds zero new `sorry`, `axiom`, `native_decide` or raised `maxHeartbeats`; actual dependency axiom sets are **unknown/pending**, not zero.
- **B-OWNER-MIGRATION (ownership):** V09 retains the six exact candidate originals listed above. Before any existing-file edit, relay exact-file agreement through the coordinator. No `relay.sh` is present on this VM; no permission is inferred from silence. The isolated additive candidates are ready for owner review, not application before proof gates pass.
- **B-REGISTRATION (ownership):** after approval/proof validation, owner/coordinator chooses an area module path for Generic, registers the module and writes its area map fragment. Suggested descriptive row: `Backend/Passes/<owner-selected-name>.lean | Intrinsic mapped-prefix/value composition retaining original Input, selected map and arbitrary saved tails.` No root/map edit was made here.
- **B-FINAL-AND-TIMING (dependent gates):** owner application, full affected validation, repository final gates and before/after measurements remain mandatory. No performance claim, exclusion, premise weakening, final theorem weakening or completion is authorized by this handoff.

## Reproduction and resume

Use the supplied official archive/pin and this same branch/VM. Do not create or reset the persistent goal. New logs require a fresh run ID:

```sh
export H62_GENERIC_PASSES_EVIDENCE="$(pwd)/../h62-generic-passes-evidence"
python3 scripts/h62/item4/generic-passes/accept.py --run-id resumed-1
# Only after successful full additive closure and unchanged source/artifacts:
python3 scripts/h62/item4/generic-passes/measure.py --run-id paired-1 --acceptance "$H62_GENERIC_PASSES_EVIDENCE/resumed-1-acceptance.json"
```

The scripts derive the checkout root, use a fresh v4.35 artifact tree and preserve older logs. The generated census can be reproduced using `census.py --output PATH` and compared with its manifest. Full external evidence, original patch, committed head/base, hashes and unfinished obligations accompany the final external `HANDOFF.md` and `SHA256SUMS`. This checkpoint is not completion of the four-checkpoint queue.

## H82 retirement update

Human-authorized stop-and-handoff to `solidity-inline-assembly5-20261031/vy3-compilation`. No new proof implementation. Original assignment, queues, exact scope and retirement record are committed in `tests/h62/item4/generic-passes/handoff/` with their own SHA256SUMS. The original thread was transcribed; ownership JSON formatting is normalized, and the rendered-prompt SHA is provenance only. H82 withdraws earlier exact-file requests for statement-preserving proof-only work; statement/dependent-definition/interface/budget/axiom/exclusion changes still need the owner. Earlier blocker sections above describe the historical checkpoint, not permission requirements after H82. All unvalidated proof, final-gate and timing obligations pass to the successor. No H71 push permission is available, so nothing is pushed. No tool exposes PAUSED: only stop_goal(complete|blocked) is available; no completion/block substitution or replacement goal is created.

## Scalar-passes successor adoption

The successor merged exactly the acknowledged stopped head
`98646221b6998afe688e105111a87c5d4af3111e` after verifying the committed
original-assignment, queue and scope hashes against the coordinator receipt.
The later remote merge was not included. The assignment is a thread
transcription; no launcher byte-hash equivalence is asserted. External prior
evidence and runtime results have not been independently verified here.

Fresh source-only acceptance passed the lexer regressions, three exact
execution source signatures and 36 control aliases. Reproducing the frozen
census yielded the original manifest SHA256
`9f5ba355c076e5328e8542a9d478b442a7dc4e6505c5c122b83750fa128c5c94`:
313 files, 83 Controls modules, 3519 declarations and 1946 control declarations.
The census check also confirmed every inventoried original source unchanged.
These are lexical checks, not elaborated type, axiom, witness or generic-proof
validation. Raw migration, additive Lean checks, affected/final gates and
paired proof timings remain open; the failed baseline was not rerun unchanged.

## Explicit resumption after coordinator integration

The coordinator explicitly requested merging origin/master and continuing. The clean lane at e7eccfe0bd31f000b65584c4d8e66e59ac9b7d6c fast-forwarded to 20e492ee99a3fa8679aa526de0b6e731d85e4134. Earlier stopped/retirement records remain historical; this explicit resumption creates no replacement goal. Coordinator-reported touched/Bridge gates and reviews were not rerun or represented as local proof evidence. No push performed.

Completed independent reproduction backfill: accept.py now blanks inactive comments/strings, requires exactly one declaration for each expected control alias, and checks the complete type/body reference. Ten isolated CLI regressions accept the original and refuse changed execution signatures, omitted negatives, substituted alias types/bodies, exact/mixed duplicates, commented declarations, comment-masked substitutions and multiline body suffixes. Independent finder/skeptic reviewed the changes without Lean/server or writes; their initial gaps were fixed. This is source-only coverage and does not establish semantic correspondence or axiom sets.

Fresh adversarial, lexical and complete pinned-census checks passed; evidence: /workspace/h62-generic-passes-evidence/resumed-20e492ee9/. Original inventory still matches every frozen file. Solidity/Syntax/Raw.lean is unchanged and no approved syntax-migration input is delivered locally; the known failed v4.35 import gate was not rerun unchanged. Checkpoints2–4 and negative/isolated-fixture proof validation remain pending that dependency. No new Lean source, frozen statement, definition body, axiom declaration, proof budget or timing claim changed. The assigned scanner/census/reproduction backfill is saved; semantic fixture/negative work, acceptance and measurement require the absent prerequisite.

## Scheduled integration and portable task locations (2026-11-07)

The clean assigned lane at 2a58d70d23d7587b1bbf57a1b94442110ecddcde fast-forwarded to verified origin/master 4f0a2d6abe3a920d8c5a20c8c06d373a1014824d. Coordinator-reported touched/review gates are attributed, not new local Lean evidence. No history rewrite or push.

The executable task scripts now share runtime_paths.py. Defaults derive from the checkout parent: h62-generic-passes-evidence and h62-coordinator-inputs. Set H62_GENERIC_PASSES_EVIDENCE and H62_GENERIC_PASSES_INPUTS for another layout; nonempty paths with spaces are supported and empty overrides refused. Overrides select locations only: archive SHA256, exact pin, serial/resource guards and acceptance provenance checks remain in force. Historical absolute artifact locators in earlier records remain unchanged for traceability. The reproduction example above runs from the checkout root.

All15 isolated source-only tests pass (ten acceptance adversaries plus relocated defaults, spaces, empty overrides, stable relative paths across working directories and changed-pin refusal), as do lexical identity, full frozen census and dependency-plan checks. No executable task script contains a /workspace literal. Evidence is in the default evidence directory under resumed-4f0a2d6ab/. Independent finder/skeptic reviews cover these changes without Lean/server or writes. No Lean source/statement/definition/budget/axiom change; no timing delta or runtime-pass claim. Raw.lean remains unchanged; no approved syntax-migration delivery is available locally. The known failing4.35 prerequisite was not rerun unchanged. Semantic generic/fixture/negative checks, axiom audits, application/registration, final gates and paired timings remain pending that wait; independent source-only reproduction backfill is preserved.

Review fixes: relative overrides resolve against the checkout root, so accept/measure and bounded children select the same locations even when their working directories differ. load_pin() validates all four fields against the exact mandatory official4.35 release; a different directory cannot silently choose a different release. Tests accept the canonical pin and reject each altered field. Existing acceptance manifests contain absolute artifact paths: moving evidence requires fresh acceptance; those paths are not silently rewritten. Both source and artifact hashes must still match before timing can run.
