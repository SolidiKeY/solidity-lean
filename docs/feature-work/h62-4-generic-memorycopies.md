# H62 item 4: generic memory copies

Status: **blocked; full four-checkpoint assignment is unfinished**.
Batch `solidity-h62-4-20261106`; lane `generic-memorycopies`.
Repository `/workspace/solidity-lean`; branch
`codex/solidity-h62-4-20261106/generic-memorycopies`; exact base
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
The base was fetched from origin and verified an ancestor of published master.
No push, merge, PR, cut-over, generated-root change, axiom-pin change, or owner
file edit was performed. No second goal was created. Goal inspection is not
exposed; the coordinator explicitly says this is not a blocker.

## Delivered source census and backfill

The deterministic scanner inventories **300 files / 3,905 declarations /
2,075 theorems**, including **97 Controls files / 2,828 declarations /
1,519 theorems**. It records each complete file hash and each declaration's
name, kind, line, exact header bytes, UTF-8 byte offsets, header hash and source
region hash. The full named inventory is off Git at
`/workspace/h62-generic-memorycopies-evidence/frozen-inventory.json`:

`9edeca091a08071f42b17f698c4a184a7debc4cf6367d58bac81162eba845de5`.

These are lexical headers, not elaborated signatures. Structure and inductive
headers exclude fields/constructors; complete file hashes preserve those, proof
budgets, imports, section variables and all original bodies. The scanner is a
source tool for this frozen family, not a complete Lean parser.

Audit matching is deliberately conservative and retains every inventory row:

| Audit item | Candidate mapping | Count |
|---|---|---:|
| 9 | Declarations in path-labelled family files | 787 |
| 11 | Named repeated intrinsic heap/allocator/representation fixtures | 371 |
| 16 | Every theorem in Controls-labelled files | 1,519 |

There are 402 negative/refusal name signals across all family files, including
controls outside Controls filenames. These signals are navigation aids, not an
exhaustive semantic classification. Every case is protected by full-file pins.
`audit-candidates.json` retains all 3,905 rows and has SHA256
`492b0870104bf630491306b1d1d3a694fc78ad8b7eb78c7d2082c556110f6242`.
No H55 Yul Raw/vector generator was copied or replaced. Audit 16's H55 part
remains outside this lane.

## H70: reviewed semantic per-case grouping

The H70 routing message accepts owner tickets at CR, V11 and migrate-syntax.
It explicitly leaves the Raw prerequisite and exact-file permission pending.
No original-file edits or passing semantic gates are implied.

`semantic_groups.py` now assigns every original declaration to a reviewed
source-operation family and a separate declaration role. The complete output is
`/workspace/h62-generic-memorycopies-evidence/semantic-inventory.json`, SHA256
`cb5a9efc35593899b995f98f63971a62f58a93875e6df41b0a3f82b8044f4acd`.
It contains **300 module rows, 3,905 declaration rows, 26 operation groups,
13,177 exact statement-evidence spans and 40 curated exception cases**.
Import-only `SourceInterface` is retained as a module with zero declarations.
The original frozen inventory and all old audit candidates remain unchanged.

Roles separate control fixtures/types, control-support lemmas, public control
statements and witnesses, contract predicates/data, and semantic definitions
and support lemmas. Each declaration keeps its original path, line, name,
header hash and source-region hash; grouping neither discards nor combines
statements. Multiple literal evidence axes and observations remain together.
Statements in structures/Prop predicates include body clauses; theorem proof
bodies never supply statement evidence.

The registry separates alias binding from allocating rebinding; it preserves
arbitrary map-free element types for empty-reference arrays. Family domains
separate Source execution, intrinsic typed heaps/scoped statement execution,
word targets and byte targets. Source bytes/string traversal is not labelled
as byte-EVM execution. Constructor equalities use neutral syntax names because
`.ok` occurs in several semantic layers. Evidence may occur in hypotheses;
its presence is not an assertion that a hypothesis is inhabited.

The curated cases retain distinctions among actual target revert, intrinsic
Option refusal, Source stuck, Source timeout with unchanged or partially
allocated state, certificate/witness impossibility, arithmetic room failure,
compiler-selection refusal, absent-path observations, successful corruption,
wrong-success observations and code-only huge-demand refusals. Mixed
success/refusal statements remain mixed. Aliases, shallow capture, fresh deep
children, shadow noninterference, old frames and successful prefixes are
recorded separately; an EVM revert is not said to return an intermediate state.

The output indexes **615 refusal/negative-related declarations** and **468
alias/identity-related declarations**. These overlapping navigation indexes
retain all 402 original negative-name signals, including positive cases with
negative-looking names. They are not counts of runtime refusals or aliasing
executions. Reviewed family/role routing maps 1,011 rows to audit 9, 1,743
fixture/support rows to audit 11 and 1,093 public control/witness rows to audit
16; prior heuristic routes remain available as a separate field.

Acceptance with `--semantic` verifies exact base blobs, regenerates both
inventories and audit data, and runs nine census plus eight grouping tests.
The grouping tests independently check every identity/hash join and all evidence
byte spans, empty aggregators, overloaded constructors, result distinctions,
mixed observations, alias/refusal retention and rejection of an unreviewed new
family. `semantic-acceptance.json` records exit 0 for both suites and
`EXTERNAL_ACCEPT_PASS`. A separately saved tamper check rejects a changed
semantic row. Finder and skeptic independently checked the source grouping
without Lean servers and their confirmed findings were fixed.

This completes source-family/per-case grouping. It is not exhaustive semantic
terminal-result classification, a correspondence proof, proof replay, owner
permission or refactor performance acceptance. The remaining three checkpoints
keep their proof and validation obligations unchanged.

## H70 requester disposition: concrete proof/correspondence plan

The requester disposition records no pending current-owner delivery, while
explicitly requiring the Raw migration and CR/V11 exact-file agreements before
original edits. Host journals establish delivery, not agreement or validation.
The original branch and goal remain unchanged.

The next reviewable artifact is an **unproved owner plan**, generated by
`proof_plan.py` at
`/workspace/h62-generic-memorycopies-evidence/proof-plan.json`, SHA256
`2f6fd654707e06259fc7c755988041fbba5a50dc3bc81fa62823d365517e3317`.
It preserves all **137 declarations and 41 public control theorem headers**
across the three pending files, with **25 existing source anchors**. Every
public theorem has an explicit route; all private support/fixture declarations
remain retained until checked correspondence. An omitted route is rejected.

The proposed intrinsic fixture stores H, source/result Ty, Heap H, SVal source,
its map-free proof and an existing typed Path. It stores no desired execution
or contents theorem. Proposed lemma text postcomposes the existing semantic
`copy_path_contents` law with a typed SVal projection by `congrArg`; primitive
word-projection commutation remains an explicit separate obligation. The text
is a proposal in JSON, not a registered/checked Lean module. No generic lemma
is counted as proved. The singleton-HRef fixture helper is likewise pending.

The plan retains exact reference IDs 1/2/4, long child ID 64 and second-copy
IDs 1/8 as separate layout obligations: contents, bounds and separation alone
cannot establish those equalities. Storage shadows and live path absence
remain separate observations. The alias routes refer to original resolution,
compiled alias code and adopted-state fixtures; they do not use allocating
copy results as alias proofs. Derived pair/empty/long and wrong-observation
routes identify their actual local producer statements.

Dynamic and fixed fixtures remain distinct. At cursor 256 the dynamic
reservation is n+1 with payload offset 1 and cursors 257/259/321 for 0/2/64;
fixed reservation is max 1 n with payload offset 0 and cursors 257/258/320.
The indexed fixtures separately start at cursor 40, ending at 42 (dynamic,
payload 41, old payload 17) or 41 (fixed, payload 40, old payload 16). Both retain
old alias 24 at cell 2 and stack 77. The empty dynamic header-zero conjunct is
not invented for fixed arrays. Universal fitting payload-list quantification
and arbitrary pair Fin W words remain intact; finite fixture rows cannot
replace those quantifiers.

Indexed refusal retains both path error/revert and emitted-target revert.
The invalid-path room implication is vacuous and is not presented as an
inhabited capacity-refusal witness. Original negative controls and assumptions
are preserved, with no new premise, exclusion or proof-budget change.

`accept.py --semantic … --plan …` regenerates the plan, preserves exact base blobs, and runs
the existing nine census/eight grouping checks. `proof-plan-acceptance.json`
records exit 0 and explicitly limits validation to source preservation and route
coverage. The omission-refusal evidence records rejection when fixed_overrun
has no plan. Independent finder and skeptic verified the exact 41 headers,
all 137 hashes and 25 anchors without Lean calls; confirmed anchor issues were
fixed. No new Lean check or timing gate was run against unchanged blockers.

After the Raw prerequisite resolves, establish the bounded baseline on the
approved overlay and elaborate additive fixture/projection/helper lemmas within
this lane scope; these additive steps do not require original-file agreement.
Prove original input/fixture correspondence at the original types. Original
body patches remain for owners after exact-file agreement, with original
statements kept exact.
Run affected semantic/negative checks and final gates, compare identical
cache/resource conditions, and stop on a slowdown over 10%. None of these
pending gates is discharged by the source plan.

## Checkpoint state

1. **Done (source classification):** complete census, reviewed semantic-family
   grouping and audit 9/11/16 routes with exact preservation of all original
   declarations. This does not prove terminal behavior or migration equivalence.
2. **Blocked:** no new intrinsic generic copy lemma or typed semantic fixture
   table is claimed. Existing declarations have not been replaced.
3. **Partial:** deterministic external reproduction acceptance passes and all
   original negative/refusal source is unchanged; kernel correspondence and
   affected semantic validation remain blocked.
4. **Blocked:** full inventory is delivered, but family baseline/candidate
   measurements under equal cache/resource conditions have not been obtained.
   No speed delta, >10% acceptance, or final runtime gate is claimed.

There are **zero new Lean declarations, zero new axioms, zero new sorrys and
zero frozen statements touched**. This backfill is not semantic completion.

## Toolchain, resources and gates

All five coordinator input files passed their SHA256 manifest. The official
archive `/workspace/h62-toolchain/lean-4.35.0-linux.tar.zst` matches the pin:
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Actual versions: Lean **4.35.0**, release commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake **5.0.0-src+eb6cafb**.
The tracked toolchain pin was not edited, and the old v4.24 cache was not used.
An off-Git alternate configuration selects a private `build-v4.35.0` directory.

The VM has a 16 GiB cgroup memory cap and no host swap. Checks used the writer
lock, `LEAN_NUM_THREADS=1`, `-j1`, `-M8192`, `--tstack=131072`; no systemd-run.
The dependency-order runner checks one module at a time, samples process-tree
RSS every 0.25 s, enforces a 4 GiB available reserve and stops at 300 s/module.
Sampled peaks are not exact maxima or a separate hard cgroup cap.

| Command/check | Outcome and decisive evidence |
|---|---|
| Official `lean --version`, `lake --version` | Pass; `toolchain.json` records versions and archive hash |
| Bounded direct `lean -j1 -M8192 --tstack=131072 Solidity/KeySort.lean` | Pass, exit 0, fresh 2.0507 s, child maxrss 507,276 KiB; `keysort.json`, `keysort.log` |
| Private Lake `build Solidity.AST` | Pass, exit 0, 10.8105 s including KeySort; AST deprecation warnings retained; `ast-prerequisite.json` and log |
| Serial CopyPaths prerequisite chain | KeySort, AST cached checks pass; SpecSyntax passes; **Syntax.Raw fails**, exit 1, 4.5214 s, sampled peak 1,612,214,272 bytes; `module-checks.json` and per-module logs |
| `python3 -B tests/h62/item4/generic-memorycopies/test_census.py` | Nine parser/regression tests pass |
| `accept.py --frozen … --audit … --output …` | `EXTERNAL_ACCEPT_PASS`; exact 300 published-base blobs, repeat census bytes and audit reproduction, tests exit 0; `acceptance.json` |
| Layers, registration, fragments, diff whitespace | Read-only checks pass; saved command/exit logs in evidence |
| Full affected Lean checks, `./run-lean.sh`, axiom replay, same-condition before/after | Pending, blocked by unowned Syntax.Raw prerequisite and missing candidate migration |

The first timing wrapper could not run because `/usr/bin/time` is absent
(exit 127); it was replaced with Python timing before counting KeySort as
passed. One read-only sandbox parser-test attempt could not create a temporary
directory; the authorized writable-temp retry passed all nine tests, with both
outcomes retained in evidence. Cached ~0.25 s prerequisite checks are not fresh-build measurements.
No `RUNTIME_GATE_PASS` is asserted.

## Typed blockers and relay handoff

**B-RAW-435 / prerequisite-owner:** `Solidity/Syntax/Raw.lean` at lines
597, 650, 665, 682 and 684 does not typecheck with v4.35 String APIs. Examples:
`HashKind.ofName? (f.drop 1)` now supplies `String.Slice` instead of `String`;
`String.Slice.toList` and `String.dropRight` are absent. This is a real compiler
failure, not a resource stop. Its registered migration owner is
`solidity-h62-6-20261106/migrate-syntax` (ownership snapshot). No repair was
attempted outside scope. Resume after the coordinator supplies an approved
migration overlay, then rerun the same serial prerequisite command.

**B-OWNER-RELAY / owner-agreement:** family originals remain read-only.
The saved exact-file relay request for CR/V11 is:
`Solidity/Backend/MemoryCopies/CopyPathControls.lean`,
`Solidity/Backend/MemoryCopies/MemoryPathCopyControls.lean`, and
`Solidity/Backend/MemoryCopies/FixedPathCopyControls.lean` for a first
path-copy fixture migration review. This is a request for owner coordination,
not permission inferred from silence. H70 confirms that CR, V11 and
migrate-syntax accepted the tickets, but no
exact-file edit agreement or owner-applied migration patch is present.
`relay.sh` is host-only; its absence is not a VM installation task. Keep the
exact-file requests in the saved result for the coordinator. Owners retain live
producer ownership.
Other family controls remain inventoried and in scope for later groups.

**B-SEMANTIC-GATES / dependent:** generic proofs, typed data tables, exact
instance proofs, negative/refusal correspondence, all affected checks and
same-condition timing with the >10% stop rule remain pending. No exclusions,
weakened statements, increased proof budgets or trust shortcuts are proposed.

Resume commands (repository cwd; one heavy check at a time):

```sh
python3 -B scripts/h62/item4/generic-memorycopies/check_modules.py \
  --toolchain /workspace/h62-toolchain/lean-4.35.0-linux \
  --evidence /workspace/h62-generic-memorycopies-evidence \
  Solidity.Backend.MemoryCopies.CopyPaths
python3 -B scripts/h62/item4/generic-memorycopies/accept.py \
  --frozen /workspace/h62-generic-memorycopies-evidence/frozen-inventory.json \
  --audit /workspace/h62-generic-memorycopies-evidence/audit-candidates.json \
  --semantic /workspace/h62-generic-memorycopies-evidence/semantic-inventory.json \
  --plan /workspace/h62-generic-memorycopies-evidence/proof-plan.json \
  --output /workspace/h62-generic-memorycopies-evidence/proof-plan-acceptance.json
```

After an approved original-file migration, preserve the original frozen
inventory and build a separate correspondence acceptance mode; do not overwrite
the baseline merely to make byte-preservation acceptance pass. New canonical
module registrations must be supplied as coordinator fragments, not root edits.

## Independent read-only reviews

Finder and skeptic used no Lean server and made no edits. The finder discovered
truncation at type-level lets, a top-level match, and control statements outside
Controls filenames. Fixes cover all family declarations and add chained-let,
match, equation, where and nested-file regressions. The skeptic requested
precise header terminology and recursive discovery; both were fixed. Both
independently reproduced all 300 file hashes and 3,905 header slices/hashes.
Final hardening fixes resolve all driver path arguments, verify the official
archive and actual Lean/Lake versions, and describe resource peaks as sampled.
Review records are saved in `reviews.md` in evidence. All accepted findings
were fixed; semantic checkpoints remain explicitly unfinished.

The first handoff covered three independent backfill items (census, audit
mapping, deterministic acceptance) and the prerequisite diagnosis. H70 adds
complete source grouping as the fourth additive work item. The requester
disposition adds this source-pinned proof/correspondence plan as the fifth
preparatory item. The next thread belongs to the coordinator. Continue the
same original VM, branch and goal; do not create a replacement goal/thread.
The coordinator must arrange the next thread after resolving the blockers.
Artifact metadata records the full committed head, patch, evidence archive and
SHA256 manifest under `/workspace/h62-generic-memorycopies-artifacts/`.

## H82 final retirement acknowledgement

STOPPED for handoff to `solidity-parallel-20261103/memory-copies`. The explicit
stop-and-handoff and subsequent ordering correction override routing to continue.
No new proof implementation is authorized. Original full assignment, original
queues and scope are committed under tests/h62/item4/generic-memorycopies/handoff/.
The original rendered-prompt digest is recorded as provenance; the transcript
file has its own independently reported checksum, not a claimed rendering match.

H82 withdraws blanket exact-file waits for statement-preserving proof-only work.
Dependent definition bodies, statements, interfaces, budgets, axioms and exclusions
still require owner. Historical earlier blocker descriptions are not new policy.
The Raw prerequisite and all unfinished proofs/gates pass to the survivor.

H71 push permission is unavailable in this worker's inputs, so no branch was
pushed; original no-push authorization remains. Only a preservation commit and
cumulative patch/bundle export were made. No source, VM, branch or evidence was
deleted. The goal is not complete. PAUSED was requested by the user, but no
pause goal tool exists: exposed stop_goal permits only complete or blocked.
Neither is a pause, so no misleading transition was attempted. Implementation
is stopped locally and must not automatically resume. Successor integration
begins only after this final stopped/head acknowledgement.
