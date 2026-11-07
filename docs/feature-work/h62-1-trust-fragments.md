# H62 item 1: TrustAudit fragments — incomplete work

H145 archival notice: historical receipts, source-hash manifests, routing/chain
records and handoffs named below now live in the private coordination repository:
https://github.com/SolidiKeY/solidity-lean-coord/tree/4cb216278ddc62582604b4348d65749fcf9bfeb6/evidence/solidity-h62-5-20261106/statement-graph/
The private archive preserves their exact bytes and source revision. References
to “committed evidence” in older milestones describe those earlier revisions.
Current checker inputs, executable fixtures and checksum constants remain here;
evidence records are no longer code-branch inputs.

Base `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. The isolated branch contains a prototype ordered raw-byte collector, a baseline splitter, 44 fragments, six external Python tests, and an unapplied central-file marker patch. The central `TrustAudit.lean`, theorem statements, axiom allowlist and generated roots were not edited. No new theorem, axiom, `sorry`, `native_decide`, or proof-budget change is claimed. This is a partial checkpoint, not acceptance of the migration.

The frozen baseline is 106217 bytes, SHA-256 `ece2e6cebbee95d82fec246892993662e81dcfd895831981583d2b0867a37482`. The external census counts 44 `run_cmd` blocks and 44 identical `[``propext, ``Classical.choice, ``Quot.sound]` allowlists, 17 `#print axioms` commands and 1380 quoted `Solidity` occurrences. Raw concatenation reproduces all baseline bytes, including the imports and output commands. The first fragment contains the header and print commands. A migration patch adds a generated-file marker only; a test applies the patch to a temporary copy and compares the result to `collect.py --migration --stdout`. It does not integrate generation into CI or establish producer ownership.

Commands observed passing:

- `python3 -B -m unittest discover -s tests/h62/item1/trust-fragments -p 'test_*.py' -v`: six external tests, including dropped and mutated fragments.
- `python3 scripts/h62/item1/trust-fragments/collect.py`: exact original reproduction.
- `git apply --check scripts/h62/item1/trust-fragments/migration.patch`: patch applies; it has not been applied.
- Pinned official archive SHA-256 `7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`; Lean 4.35.0 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake 5.0.0-src+eb6cafb. `LEAN_NUM_THREADS=1 lean -j1 --tstack=131072 Solidity/KeySort.lean` passed with a 12 GiB virtual-memory limit, no configured swap, and at least 4 GiB available before launch. This is only the prerequisite, not a runtime gate or proof of the audit.

Remaining: producer-facing lane naming/ownership and registration design; robust fragment and coverage acceptance for future additions; review and completion of the migration integration patch; independent read-only finder and skeptic reviews and fixes; full affected Lean validation and repository final gates on the official toolchain; controlled same-tree/cache/resource before/after timings and the 10% gate; committed completed-checkpoint handoffs; and any remaining explicitly assigned backfill. No full build, audit elaboration, Lean proof/axiom analysis, timing comparison, or independent review is claimed. The splitter's textual heuristic is not a Lean parser and must not be treated as a proof of coverage for future syntax. The numbered fragment scheme still needs an ownership and concurrent-addition solution. H58's held generated axiom audit was not started.

## Continuation: baseline acceptance and migration dependency

`accept_baseline.py` compares the collector output and checkout audit against the exact Git base object, first validating its SHA-256. Matching mutations to both the central file and fragments therefore do not pass. The deterministic `census.py` records the existing audit's 77 imports, 44 blocks, 1,380 headline occurrences (1,373 distinct names), and 17 print commands; `/workspace/h62-trust-evidence/census.json` contains the complete ordered inventory. This is a census of the frozen audit, not a generated audit of other declarations. Eight Python tests pass, including altered allowlist, altered print command, missing fragment, and matching-mutation controls.

`Fixture.lean` and `check_fixture.py` exercise the same audit loop using a theorem that depends on the existing `propext`: the permitted case succeeds, an empty test allowlist causes `unexpected axioms`, and an unknown declaration is rejected. Each Lean invocation is serial, `-j1`, uses the pinned 4.35 binary, checks zero swap and at least 4 GiB effective host/cgroup headroom, and monitors headroom during execution. This fixture proves no project theorem and is not the real audit. The first test run correctly failed because its expected text used lowercase while Lean emitted `Unknown constant`; the harness was corrected and the three controls then passed.

The original audit cannot currently be checked in this worktree: `lake env lean -j1 --tstack=131072 TrustAudit.lean` failed because the 4.35 project artifacts were absent. A fresh, no-cache Lake build of `+Solidity.Examples.Tactics.PaymentSource:olean` using the pinned release, an alternate `-j1` configuration, and a serialized Lean wrapper failed in the existing `Solidity/Syntax/Raw.lean` at lines 597, 650, 665, 682 and 684. Lean 4.35's `String.Slice` return types no longer match the old `String` uses. The ownership snapshot assigns that file to `H62-6-MIGRATE-SYNTAX` (`solidity-h62-6-20261106/migrate-syntax`); no out-of-scope edits were made. The build is not an audit or final-gate pass. Its wrapper checked host headroom at process launch, but did not monitor cgroup headroom during each child; do not reuse it as a complete resource guard.

Non-Lean repository checks passed: `bash scripts/check-trust.sh` (6,401 sources, zero findings), `node scripts/check-layers.mjs` (857 core modules, zero prohibited reaches), `bash scripts/coord-tools/register.sh --check`, and `bash scripts/coord-tools/fragments.sh --check`. Detailed outputs, including the failed dependency build and earlier direct-probe failure, are under `/workspace/h62-trust-evidence/`. Full audit elaboration, owner-integrated migration, the before/after comparison and independent finder/skeptic reviews remain pending. The baseline acceptance is intentionally frozen to the original bytes; future additive fragments require a separately reviewed acceptance design and cannot be claimed covered by this check.

The blocked-work timing tool `scripts/h62/item1/trust-fragments/time_audit.py` requires the official archive and its pinned hash, the matching extracted Lean/Lake, a clean checkout, existing project `.olean` artifacts, and an external output directory. It holds the writer lock, records checkout and artifact metadata, runs up to three alternately ordered pairs with `-j1`, monitors available host/cgroup memory and zero swap, stores successful Lean output externally, and stops on any failure, changing snapshot, or candidate slowdown over 10%. The unit test covers the threshold boundary. This tool has not produced a timing result: a successful Lean 4.35 build of the affected imports remains a prerequisite. Metadata checks do not prove identical machine load or cache state, so the final comparison still requires reviewer judgment and recorded resource conditions.

## Additive lane prototype

The collector also accepts optional per-owner `lanes/<owner>/<fragment>.json` files with exactly `imports` and `headlines` arrays. Each nonempty fragment supplies `Solidity.*` headline names and optional `Solidity.*` imports. The collector sorts owner and file names, rejects malformed names, duplicate headline entries, duplicate JSON keys, symlinks and unrecognized entries, and inserts new headline names into the first existing audit block. It prepends deduplicated new imports. With no lane files it reproduces the original bytes exactly. Existing audit checks, list entries, printed reports, and allowlists are retained; new imports can affect the Lean environment, so this textual guarantee does not replace elaboration of the whole audit.

Two synthetic owner directories in an external test verify deterministic order and removal of the additions to recover the original bytes. The isolated Lean fixture verifies a generated additional existing theorem succeeds and a generated missing theorem fails, alongside the original positive and negative controls. Eleven Python tests and all five fixture controls passed. The timing tool now includes lane additions in its candidate. Its real timing attempt correctly failed before measuring: `Solidity.Examples.Tactics.PaymentSource.olean` was absent following the upstream syntax failure. No timing delta is claimed.

This is an additive proposal, not owner registration or an approved integration. The actual ownership registry and producer paths must be coordinated by the coordinator; the input validator does not establish ownership or check that added names exist. Producer changes must pass Lean and the trust gate. The original first block remains a large historical fragment, and the central patch currently only adds a generated-file marker; CI enforcement and the full migration patch still need review and completion.

## H70 standalone migration acceptance

`python3 -B scripts/h62/item1/trust-fragments/accept_migration.py` retrieves the original from the pinned Git base, verifies its SHA-256 and byte-for-byte fragment reconstruction, applies the supplied migration patch only to a temporary copy, and independently checks that the generated candidate retains every original byte after removing the explicitly enumerated additive imports and headlines. It supports an original checkout for preflight and a generated checkout or `--candidate PATH` for a coordinator's migration overlay. Its output records which checkout state was inspected and the candidate SHA-256. Current acceptance passes with the central checkout still original and zero real lane additions.

Thirteen external tests cover two independent synthetic lane inputs, omitted imports or headlines, changed allowlists or printed reports, matching changes to baseline and generated inputs, a corrupted patch, invalid and duplicate inputs, installed versus unmodified candidates, and symlink rejection. The synthetic Lean controls exercise the generated form but do not prove any actual project declaration. Independent finder and skeptic reviews remain required; this work is not an independent review and no milestone acceptance is claimed.

The `Solidity/Syntax/Raw.lean` 4.35 blocker and owner remain as recorded above. Do not run the real TrustAudit, its timing gate, or final-gate claim until the owner supplies the migration and the affected imports are built under the pinned toolchain. The ownership registry is not modified and additions are not authorized merely by passing this script.

## H70 requester follow-up: author review and integration proposal

An author review found three integration gaps. First, preflight acceptance can pass with the original central file; `--require-installed` now rejects that state. Second, simply collecting current lane files could miss deletion or reassignment of earlier lane entries; `--prior-commit <full-sha>` now compares every prior lane import and headline by owner against the current files, refusing missing or reassigned entries. Third, the timing helper formerly expected the original file in the checkout and could not run after installation; it now loads the pinned baseline from Git and accepts either the original or the exact generated checkout for comparison. Fifteen external tests cover the installed-state, prior snapshot, ancestry, malformed history, and timing-input cases. These are author findings and tests, not the separately required independent finder and skeptic reviews.

For coordinator review, a proposed post-migration registration command is:

```sh
python3 -B scripts/h62/item1/trust-fragments/accept_migration.py --require-installed --prior-commit <coordinator-approved-prior-commit>
```

The placeholder must be replaced with the full lowercase SHA of the appropriate approved prior lane state. The script requires that commit to be an ancestor of the checkout, but does not establish that it is the correct protected prior state, authorize owner claims, or register the command in CI. The coordinator must establish those facts and review integration. The baseline audit still must be elaborated with the prescribed toolchain and the unchanged allowlist; the acceptance command is an external byte and input-coverage check, not a Lean proof. Real elaboration and before/after timings continue to wait on `H62-6-MIGRATE-SYNTAX` for `Solidity/Syntax/Raw.lean`.

## H82 independent acceptance hardening

The author review found that the proposed installed gate could be pointed at untracked or noncanonical lane inputs. Strict mode now requires the canonical lane directory and exact file bytes and paths from committed `HEAD`, rechecks the snapshot and central file before returning, and rejects noncanonical, uncommitted or changed inputs. The previous-history Git pathspec now includes the lane root itself, so a root symlink or gitlink is rejected rather than silently omitted. The coordinator still must choose the authoritative prior commit and verify producer ownership: ancestry and committed bytes alone do not establish either. Preflight remains separate from the strict post-migration gate.

These are author-reviewed external acceptance safeguards, not an independent finder or skeptic review, and not a Lean proof. The H82 standing agreements do not supply the awaited `migrate-syntax` artifact or the coordinator's prior-commit/ownership choice. No central audit, theorem, axiom allowlist or proof budget was changed.

## H82 retirement checkpoint

The latest isolated fixture adds a generated lane import and theorem: its module build and positive generated audit passed under the pinned Lean 4.35 binary, while a missing import, missing declaration and non-allowlisted dependency were rejected. This is a small external fixture, not the project audit. The strict installed gate also checks lane paths and bytes against committed HEAD and rejects a lane-root symlink or gitlink in prior history. Independent finder and skeptic reviews remain outstanding.

Human instruction requests retirement and handoff to `solidity-h62-5-20261106/statement-graph`. The complete original rendered prompt bytes were not available through any exposed tool or located file; `tests/h62/item1/trust-fragments/handoff/original-prompt-provenance.md` records the missing SHA-verified artifact. The scope manifest and coordinator-provided decisions, audit and toolchain pin are committed under that handoff directory; the full ownership snapshot remains outside Git in the evidence directory, with checksums. H71 is absent from the available decisions snapshot, and the original explicit no-push rule remains in force. No push was made.

## Post-merge standalone check

After the coordinator reported `ff650f670` integrated and the lane was fast-forwarded to `20e492ee99a3fa8679aa526de0b6e731d85e4134`, the original audit bytes and standalone acceptance still matched. A new external test checks the strict installed gate against the real committed Git tree using a temporary candidate file; after successor hardening it confirms that an uncommitted candidate is refused and makes no edit to `TrustAudit.lean`. The test uses the frozen base only as a fixture, not as the coordinator's authoritative prior commit for production registration. The syntax migration is not present in the merged tree, so the real Lean audit and timing remain open. The coordinator separately reported its touched/Bridge gates and finder/skeptic review passed for the merged commit; this document does not independently reproduce those gate receipts.
## H82b successor: snapshot and resource hardening

The survivor verified the authenticated full assignment/scope and stopped/head
receipt and integrated exact final head 8dc693e46409928791b2eeb89650fe0eaf46149a
before member work. Metadata waits are resolved; the historical missing-prompt
note above is superseded by the H82b authoritative assignment envelope. No legacy
rendered-wrapper byte equivalence is asserted.

Independent read-only finder identified a prior-preservation race: generation,
coverage and preservation reparsed different live inputs. They now derive from
one captured byte map; validated lane types/paths and raw fragment bytes are
rechecked before acceptance returns. Strict mode additionally requires that the
generated central audit is committed in HEAD. A controlled change-and-restore
regression checks the former false acceptance, and raw mutation, same-byte
symlink replacement and uncommitted-central cases are rejected. Sorting remains
by owner then filename, including prefix-related owners a/a-b. Both independent
reviews found no remaining static blocker and used no Lean/server.

Skeptic confirmed inherited resource gaps. Isolated fixture and timing runners
now share an 8 GiB process bound, official archive/path/version validation and
process-group cancellation/reaping on timeout or reserve failure. Mocked guards
exercise timeout and headroom aborts. The real audit/timing was not run; central
TrustAudit.lean, its allowlists and H58's held generated audit remain untouched.

Actual final external controls: 21 tests, exit 0. Official Lean 4.35.0 fixture
addon compilation and seven positive/negative controls pass under -j1,
LEAN_NUM_THREADS=1, 8 GiB limit, zero swap and 4 GiB available reserve.
Preflight reproduces the original 106217 audit bytes; strict installed mode
correctly exits 1 because migration is absent. Timing of the external preflight
CLI, one warmup and seven serial runs on unchanged zero-lane inputs, measured
median 57.532156 ms before and 60.022572 ms after (+4.3287%, below 10%). This
is not a real Lean audit timing result; child RSS is cumulative high-water,
not isolated per-command RSS. Output, source/evidence hashes and review findings
are recorded in h82-successor-evidence.json and the off-git evidence directory.
A source-manifest path error occurred after successful gates and was corrected
without repeating those gates.

All original checkpoint obligations remain partial until real audit elaboration,
authoritative prior/owner registration inputs, controlled real-audit timings,
full affected/final gates and coordinator integration are complete. The syntax
migration dependency is retained. These checks do not prove actual production
declarations, authorize owners or install the proposed central marker patch.

## H70 queued coverage backfill

Current-source deterministic census records 44 blocks, all 1380 headline
occurrences (1373 distinct), 77 imports and 17 print commands. Two outputs match;
concatenated fragments equal the unchanged central bytes and pinned digest.
Evidence: /workspace/h62-statement-graph-evidence/h70-trust-coverage/ and the
committed h70-controls-evidence.json in the surviving statement-graph tests.
No declaration existence, real project audit or unavailable original runtime
receipt is inferred. H58 generated-audit HOLD remains intact. The coordinator's
latest consolidated compatibility route is migrate-root-gate for Syntax.Raw and
Contracts:1104; earlier route names above are historical, no stale owner contact.
