# H55 vectors and tables: inventory preparation

Base: `4d3790eadb8a5212233bc7d5e345817476b2f590`. The 2026-11-02
coordination correction makes existing producer and consumer files read-only
migration inputs until an explicit owner handoff transfers the exact files.
This preparation changes no such input.

`python3 scripts/h55/vectors-tables/vector_census.py` checks the complete bytes,
count and sequential declaration names of nine frozen vector modules against
`tests/h55/vectors-tables/vector-manifest.json`. It reports 6,903 declarations.
The nine SHA-256 values were independently compared with the corresponding Git
blobs at the stated base. The manifest contains hashes and metadata, not bulk
vector data. `python3 -m unittest discover -s tests/h55/vectors-tables -p
"test_*.py" -v` passes missing, extra, order, schema and altered-output negative
controls as well as the full inventory check.

This is an integrity census, not the requested generator, an independent EVM
oracle, or a Lean proof. Source equality alone proves no opcode semantics.
The full generator, deterministic reproduction, lossless generation, compile,
Raw family case accounting and validation, table migration patches, timings,
KeySort and full affected-module gates remain outstanding. A filename census
finds 102 tracked `Solidity/Yul/Raw*.lean` files; that is not case accounting.
The independent finder and skeptic reviews remain outstanding. No runtime
pass is claimed. Lean 4.24.0 (797c613), Lake 5.0.0-src+797c613 were observed.
No cache pack or full export has yet been created. The H58 hold remains in force.

## Additive codec preparation

`vector_codec.py extract /workspace/scratch/h55-vectors-tables/vectors.json`
extracts structured rows from the authenticated frozen files, and `check` renders
all rows and compares each complete output file byte-for-byte with its input.
A second independent invocation produced identical data bytes. The off-Git bulk
file is `/workspace/scratch/h55-vectors-tables/vectors.json`; its SHA-256 is
committed in `tests/h55/vectors-tables/bulk.sha256`. The four Python tests pass,
including per-file missing, extra, reordered, malformed schema and changed-output
controls. The extracted expected results are transcribed from the originals;
this neither validates the arithmetic oracle nor substitutes for kernel checks.
The codec is preparation, not acceptance of the full requested generator.

A KeySort prerequisite check ran with `LEAN_NUM_THREADS=1`, Lean `-j1`,
`--tstack=131072`, the repository writer lock and a preflight 4 GiB available
memory guard. It exited 0 in 1.634 seconds with no diagnostic output; log:
`/workspace/scratch/h55-vectors-tables/keysort.log`. An initial attempt did not
run Lean because `/usr/bin/time` was absent; the successful retry used the shell
timer. No whole-task runtime gate, compile, speed comparison or review is claimed.

## Emitted modules: serial Lean check

`vector_codec.py emit` checks all records against the authenticated original
bytes, then writes nine Lean files to a new directory outside the checkout. It
refuses an existing destination. End-to-end tests verify complete emitted bytes,
no overwrite, and refusal of a changed result before creating the destination.
The five Python tests pass. The 30 WordTable parts contain 439 theorem
headings; the 45 FixtureControls files contain 45. These preliminary counts are
not exact migration case accounting or an owner-approved patch.

`PYTHONDONTWRITEBYTECODE=1 python3 -u scripts/h55/vectors-tables/compile_vectors.py`
compiled the six local imports and all nine emitted modules, serially, using
Lean 4.24.0, `LEAN_NUM_THREADS=1`, `-j1`, `--tstack=131072`, and a guard of
4 GiB against both available host memory and cgroup headroom. Full command and
per-file outcomes are in `/workspace/scratch/h55-vectors-tables/compile.log`.
The first attempt failed because the generated source was outside the default Lean
root; `/workspace/scratch/h55-vectors-tables/compile-attempt1.log` retains
that failure. The successful retry supplies an explicit root and strengthened
the memory guard. No source theorem or owner file was edited. This validates the
emitted declarations against these freshly built imports, not universal opcode
agreement, full acceptance, or a whole-repository build.

The isolated object cache is `/workspace/scratch/h55-vectors-tables/lean-objects.tar.gz`;
its SHA-256 is recorded in the external handoff checksum manifest. The baseline
and post-migration speed comparison, independent finder and skeptic reviews,
exact Raw case accounting, table migration patches and production owner
handoffs remain pending. The current compile timings are not that comparison.

## Fixture control generator preparation

`PYTHONDONTWRITEBYTECODE=1 python3 scripts/h55/vectors-tables/fixture_controls.py
check` reproduces all 45 complete StatementGrammar FixtureControls modules and
checks the ordered 45 corresponding definitions in FixtureData. `emit --output`
writes to a new directory outside the checkout. A committed manifest pins the
FixtureData bytes and every control file; their hashes were checked independently
against the base Git blobs. Missing, extra, wrong-position, changed proof schema,
and missing/renamed fixture definition controls pass. Seven Python tests pass
across both vector and fixture helpers. This preparation does not edit owned files,
provide a production migration patch, compile these fixture controls, or prove
anything beyond the stated byte and inventory comparisons. WordTable migration,
actual owner handoff and full acceptance remain pending.

## WordTable proof extraction preparation

`word_table.py` extracts 30 pinned parts into external structured proof text and
renders all 439 complete theorem declarations and module bytes. A second extraction
was byte-identical. The bulk JSON and emitted files are under
`/workspace/scratch/h55-vectors-tables/`; the committed `word-table-bulk.sha256`
pins the JSON. All 30 source hashes match the published base Git blobs. Negative
controls cover missing, extra, reordered and malformed entries and changed proof
text. The first schema matched only 438 headings because it omitted
`table_prefix_root`; the full-count test failed and the corrected schema rejects
unrecognized theorem headings. Attempt-one data and manifest are preserved in
that scratch directory. This transcribes proof bodies, does not synthesize them,
compile them, or provide an owner-approved production migration patch.

## Raw source census preparation

`raw_census.py` pins all 102 Raw source files and records eight inductive headings,
20 recognized constructor headings, and 1,839 candidate branch lines. Detailed
line records are off Git at `/workspace/scratch/h55-vectors-tables/raw-census.json`,
with a committed checksum; a second extraction matched byte-for-byte. All 102
source hashes match the published base. Negative controls exercise missing and
extra files, missing, extra, changed and reordered-looking branch declarations,
and a changed family schema. The candidate-line scan is textual and may include
non-case syntax or omit cases not written at line starts. It does not establish
semantic case accounting or prove that any parametrisation preserves behavior.
All source-file migrations, meaningful Lean validation and owner handoffs remain
pending. Eleven Python tests passed after the WordTable correction.

## H70 table annotation proposals

`table_proposals.py` produces two exact owner-reviewable patches without writing
to the owner files. The WordTable proposal adds one provenance comment in each
of 30 parts; the FixtureControls proposal does so in each of 45 controls. The
patches are `/workspace/scratch/h55-vectors-tables/word-table-annotation.patch`
and `/workspace/scratch/h55-vectors-tables/fixture-controls-annotation.patch`.
Their hashes are committed in `table-proposals.sha256`. Both apply-check against
the frozen sources and repeated generation produced identical bytes. Tests show
that removing each proposed marker restores the exact source, including all
proofs, assumptions, imports and observations. These annotations do not migrate
the tables or replace proof generation; substantive migration patches and Lean
validation remain pending owner coordination. No owner files were edited.

## H70 Raw lexical token accounting

`raw_tokens.py` scans all 102 pinned Raw files for pipe and `case` occurrences
outside line comments, nested block comments and strings. It records 1,933
occurrences with line and column locations in the external
`/workspace/scratch/h55-vectors-tables/raw-tokens.json`; a second extraction
matched and its checksum is committed. Tests cover comments, nested comments,
escaped strings, inline occurrences, malformed input and missing, extra and
reordered tokens. This scanner is not the Lean parser: occurrences are not all
semantic cases, and exact semantic case coverage and meaningful Lean validation
are still pending. Current master includes an additional RawFrameLogic module
and changes RawFrame and RawBoundary, so this 102-file frozen census is not a
claim about the updated master inventory. Sixteen Python tests pass.

## H70 Lean parser node inventory

`run_raw_parser.py` runs `ParseProbe.lean` against all 102 frozen Raw files
with Lean 4.24.0, `LEAN_NUM_THREADS=1`, `-j1`, one process, and a 4 GiB
host/cgroup available-memory guard. Two runs exited 0 and their logs matched.
The selected node inventory contains 20 constructor declarations, 440 term
match alternatives, 1,347 tactic induction alternatives, 20 tactic case nodes,
833 cases tactics and 79 induction tactics: 2,739 nodes in total. Their byte
spans and source-slice hashes are in the external
`/workspace/scratch/h55-vectors-tables/raw-syntax.json`, pinned by the committed
manifest and bulk checksum. `raw_syntax.py` checks the complete file order,
node schema and spans. Missing, extra, file-order, malformed-schema and invalid
span controls pass. Seventeen Python tests pass overall.

The probe uses `Lean.Parser.testParseFile` with the built-in Lean environment;
it does not elaborate the project imports or execute proofs. These counts cover
the six selected parser node kinds only; they do not establish semantic case
coverage, constructor inhabitation or preservation by a parametrisation. The
102 frozen files also predate the extra RawFrameLogic file on current master.
The production migration, meaningful Lean validation, independent finder and
skeptic reviews and owner handoffs remain open.

## Master Raw reconciliation and semantic obligations

Fetched master `5f7bb1441566aaad64a34436904afc61de762fd2` was compared with
frozen base `4d3790eadb8a5212233bc7d5e345817476b2f590`. The external snapshot
contains 103 Raw files; their paths and SHA-256 values are pinned in
`master-raw-source-manifest.json`. A guarded Lean built-in parser run and a
second identical run cover the entire snapshot. The reconciliation records 100
unchanged files with identical selected nodes, two changed files and the new
`RawFrameLogic.lean`. No file is removed. `RawBoundary.lean` changes documentation
wording and retains identical selected parser-node content. `RawFrame.lean` adds
four theorems and six `cases` tactic nodes. The new logic module adds two term
match alternatives, 12 tactic alternatives and 11 `cases` tactics. The selected
node total rises from 2,739 to 2,770. The complete counts and hashes are in
`tests/h55/vectors-tables/master-raw-reconciliation.json`.

The source-pinned ledger at
`/workspace/scratch/h55-vectors-tables/master-raw-semantic-ledger.json` records
two modal definitions, all 17 new logic theorem statements and all four added
frame theorem statements, together with human classifications and declaration
hashes. In particular, box quantifies completed runs and diamond requires a
completed witness; absence at one fuel is not noncompletion at every fuel.
Whole-outcome results and the clean, world and view equalities in `run_agrees`
and `holds_agrees` remain explicit. `run_captured` requires an actual completed
run; sparse-target exclusion does not exclude completion generally. Skip
observes a full captured snapshot. These are source observations, not new proofs
or an independent review. The parser uses the built-in environment without
elaborating project imports. It does not establish the semantic case accounting
for all 103 files or validate a parametrisation. No owner file was edited.

The first ledger inventory test failed due to a recursive validation helper;
`/workspace/scratch/h55-vectors-tables/python-tests-ledger-failure.log` retains
the failure. The corrected helper and 19 Python tests pass. The external source
snapshot archive, parser log, ledger and reconciliation hashes are in
`master-raw-artifacts.sha256`. Owner handoffs, independent finder and skeptic
reviews, production changes, full Lean gates and speed comparisons remain open.

## Declaration and grouped-pattern accounting

The 103-file master snapshot remains byte-identical in the Raw area to fetched
master `0b2a648b32335f35ff323ff468f75907e926fc13`; every snapshot blob hash
was compared with that master. `ParseContext.lean` and `raw_context.py` associate
all 2,770 selected parser nodes with 624 enclosing declaration spans. Their
flattened node stream matches the earlier separate parser pass exactly. Two
guarded parser runs and extracted context data matched byte-for-byte. The
off-Git `/workspace/scratch/h55-vectors-tables/master-raw-context.json` records
headings, spans and source hashes; its manifest and data checksum are committed.

`raw_case_labels.py` further records 1,914 syntactic patterns across 1,821
alternative nodes, splitting grouped patterns while retaining their shared node,
declaration spans, and hashes. The external data is
`/workspace/scratch/h55-vectors-tables/master-raw-case-labels.json`; a second
extraction matched byte-for-byte. Missing, extra, order, malformed schema and
invalid span controls pass; 22 Python tests pass in total.

This is parser and source accounting, not exact typed semantic case accounting.
Identical pattern labels may refer to different types. In particular, a `cases`
or `induction` tactic can generate implicit subgoals without explicit named
alternatives; source labels do not establish the number or type of those goals.
The built-in parser run does not elaborate project imports. Full semantic
accounting and preservation by parametrisation require elaborated Lean evidence,
owner handoff, and validation of the actual migration. No owner files changed.

## H82 retirement checkpoint

`vector_generator.py` extracts an operand-only external input and independently
computes finite integer results before rendering all 6,903 theorem declarations.
All nine complete generated module bytes equal the frozen originals. A second
operand extraction matched byte-for-byte; the input data stays off Git with its
committed SHA-256. The 25 Python tests pass, including complete inventory,
signed and boundary examples, and missing, extra, order, schema and operand
mutations. The external integer oracle is finite testing, not a Lean theorem of
universal opcode agreement.

`compile_oracle.py` compiled six local dependencies and all nine independently
generated modules in an isolated object tree with Lean 4.24.0, `-j1`,
`LEAN_NUM_THREADS=1`, one process and a 4 GiB host/cgroup memory guard. The log
is `/workspace/scratch/h55-vectors-tables/oracle-compile.log`. Earlier failed
and successful runs are retained. Independent finder and skeptic reviews, full
final gates, timing comparisons and other queue items remain incomplete.

Retirement is directed to successor `solidity-inline-assembly5-20261031/vy1-words`.
The original exact rendered prompt is not available through the worker tools;
`tests/h55/vectors-tables/FROZEN-ASSIGNMENT-RECOVERY.md` and
`FROZEN-SCOPE-BASE-DERIVED.txt` are explicitly labeled reconstructions, not
substitutes authenticated against the requested prompt digest. The coordinator
must supply the exact original prompt and backfill details. Raw interface changes
and owner-retained table migrations await their owner handoffs. No H71 lane-push
permission was available; the original no-push rule remains in force.

The isolated oracle compile cache pack is `/workspace/scratch/h55-vectors-tables/oracle-lean-objects.tar.gz` with SHA-256 `1be228d4e98c915bdc7628d5f5d3ccd1078fd0564da16fd7a82e4369f4b3a9bf`. The worker exposed no goal-pause API; its only goal tool accepts complete or blocked. PAUSED could not be set here. No goal was reset or marked complete.

## H82b successor intake (2026-11-06)

The surviving VY1 branch verified all 557 entries in the authenticated H82b
metadata package, including the full assignment, current words scope and final
stop/pause record. This resolves the metadata-only retirement wait above.
Final Git object `f6860dea3e12122b8dd3567dbf1d5e1e095321d9` was fetched
and merged after the P16-generator final head. No worker evidence archive or
oracle cache was present; their reported hashes are not independently verified.

The inherited 25-test suite first failed on the live tree: frozen Raw checks
expect 102 files, while master has 103, and pinned FixtureData differs.
That failed log is retained at
`/workspace/vy1-words-evidence/h82b-inherited-python-checks.log`.
The same current tooling/tests then passed all 25 checks against an isolated
Git snapshot of their exact base
`4d3790eadb8a5212233bc7d5e345817476b2f590`, without modifying production
inputs or reducing assertions. Snapshot evidence is
`/workspace/vy1-words-evidence/h82b-frozen-python-tests.log`.
This validates frozen-source reproduction and negative controls, not current
semantic Raw coverage, production parametrisation or migrated FixtureControls.

Both final member deltas are confined to the authenticated words scope; no
production Lean source changed in these merges. Semantic case accounting,
meaningful Lean preservation, substantive table migration, independent full
acceptance and same-resource before/after timings remain incomplete.
The previous failed v4.35 prerequisite build was not rerun unchanged.

## Reproducible frozen-input validation runner

`python3 -B scripts/h55/vectors-tables/validate_frozen.py --report REPORT`
runs current tooling and its complete discovered Python suite against an isolated
snapshot of the authenticated frozen Git base. REPORT must be a new path outside
the checkout. The runner records the source archive hash, actual tooling head
and per-file tooling hashes, exits with the suite result, removes its disposable
snapshot and never edits production inputs. Git environment overrides are
cleared, and symlinked tooling inputs are refused. This is deliberately not a
live-tree coverage check, a Lean gate or a migration acceptance claim.

The first read-only skeptic review found that directory-root symlinks were
not covered by descendant checks. The runner now rejects every tooling-area
path component before Git access. Two focused isolation tests cover root,
parent and descendant symlinks and require refusal before a Git call. Both
reviewers passed the fix read-only. The complete frozen suite, now 27 tests,
passed twice with identical JSON reports and verified snapshot cleanup.
Existing-report and in-checkout report destinations were refused without
overwriting or creating those files. Logs are under
`/workspace/vy1-words-evidence/h55-frozen-runner-*`.

## Successor fresh oracle kernel check

At source head `71c5963f3cd9da2eb2989be1e19c810def6ff019`, two operand-only
extractions were identical and matched committed operand SHA-256
`1b55bbe41a160d767f50087caca296dbf64cc6d8dd972de43564651366456aef`.
The integer oracle regenerated all 6,903 declarations, matching the complete
bytes of all nine original modules.

A fresh external output tree compiled KeySort, six dependencies and all nine
generated modules with Lean 4.24.0 / Lake 5.0.0-src+797c613, explicit `-j1`,
`LEAN_NUM_THREADS=1`, stack 131072, enforced 12 GiB/no-swap container cap
and the compiler runner's 4 GiB host/cgroup headroom guard. The bounded job
exited zero in 168.74 seconds, peak aggregate VM RSS 3,820,744 KiB, with no OOM
events. Per-command wall times and the raw tool versions are retained in
`/workspace/vy1-words-evidence/words-oracle-kernel-recheck.log` and sibling
resource/host-configuration records. No production source or theorem changed.

Both independent read-only reviewers found no oracle, lossless-inventory or
negative-control defect. They did not run Lean. This checks finite generated
kernel controls, not universal opcode agreement, semantic Raw parametrisation,
table migration, full-lane acceptance or a before/after performance delta.
The failed v4.35 migration gate was not repeated.

Fresh operand data, emitted sources, provenance hashes and object cache are
under `/workspace/scratch/words-oracle-recheck-71c5963/`, off Git.
The object pack is `oracle-objects.tar.gz`, SHA-256
`2c34c1a8bca044687e5a2dadf4d38a392e993ee7c070ebcfc531c55e9d5ad3c9`; it is left for coordinator pull, not shipped.

## Additive typed-scope closure slice (gh#77 option A)

The coordinator approved additive generic lemmas over existing context-indexed
RawFrame and RawTypedScope operations. No stronger element abstraction, new
state file, representation rewrite or H58 hold release is supplied.
RawTypedScope now exposes generic clean-tail/world preservation, full captured
closure metadata, and `project_close`: existing clean-backup projection
commutes with typed closure without a coherence premise. The original
`close_correct` signature and coherence premise are unchanged; its proof
reuses the new generic projection lemma.

`tests/h55/vectors-tables/typed-scope-case-ledger.json` accounts for exactly
the scope projection's semantic cases: arbitrary halt, normal, break, continue
and intrinsically impossible leave. An arbitrary halt covers every halt value
parametrically; the impossible branch claims no joint inhabitant. This ledger
does not count all Raw files as covered. These are existing clean-backup
projections, not H109 dirty-readback or general Source execution semantics.

## Selected-local Source read boundary (H121)

DirtyReadback now exposes an additive selected typed local read and an explicit
boundary that invokes actual Source.evalE with the same global, frame, fuel and
runtime plan. It uses the global pipeline and prepares only the selected local;
an unrelated dirty unsupported neighbor does not block the read. The full Source
result and prepared Source state are returned alongside the untouched original
RawFrame.State. Unsupported decoding is outer none; zero fuel is an actual
Source timeout. No decoder body, Source core or state representation changed.

The source-readback-case-ledger.json in tests/h55/vectors-tables accounts for
decode refusal, decoded zero fuel and decoded successor fuel; the typed-index
helper covers here and there. It does not claim all Raw or Source cases.
Six existing LocalBlock controls check both pipelines, raw 511 cleaned to u8 255,
a dirty fixed-bytes neighbor, timeout/refusal separation and raw 511/5 retention.
The inhabited empty-program fixture is solely a local-read control.

Read-only finder and skeptic both passed the core and all six controls without
Lean servers. MCP reported zero errors; affected LocalBlock, existing decoder
controls and P16 built successfully. Scoped axiom checks show the index lemma
uses no axioms; the other ten new lemmas/controls use only propext,
Classical.choice and Quot.sound. The bounded check exited zero in 90.44 seconds,
with no swap or OOM; this is not a before/after speed comparison or full gate.
Earlier fixture syntax and proof-attempt failures remain in the evidence logs.

Ordinary Source evaluation still does not consult raw frames automatically.
General expression/statement integration and raw-copy propagation remain open
H121 work; address/bytesN/enum dirty decoding remains refused. Full inherited
Raw/table/generator acceptance, affected whole-lane gates and timing remain open.

## Selected-read conservation

After adopting master 7683091e7, three additive generic laws complete the
selected-read boundary's conservation slice. Setting a typed local to its own
value preserves the entire Source local environment (here/there induction).
Outer admission equals selected decoding admission for every fuel and runtime
plan: an admitted timeout remains distinct from unsupported decoding.
If selected decoding returns the existing clean backup, evalLocal equals
actual Source.evalE on the original complete Source state, with the original
raw frame retained. This explicit premise is not replaced by a claim that
all clean materialized frames decode definitionally.

MCP and the focused 93-job build passed. The local-environment lemma is
axiom-free; admission and compatibility use only the standard three axioms.
No decoder, evaluator or state definition changed. This does not close general
Source integration, raw-copy propagation or the whole Raw-family queue.

Read-only finder and skeptic both passed these conservation laws without Lean
servers or writes. The affected LocalBlock, existing decoder controls and P16
build passed (201 jobs), including the exact standard-axiom pins. The bounded
run took 94.40 seconds with no swap or OOM. It is not a before/after timing gate.

## Public generic readback pipeline laws

After adopting master 806a972a4, the previously private value/local/context
pipeline lemmas in RawFrameLogic were promoted to DirtyReadback's generic API.
Both plain context readback and backup-aware readback retain full optional
results, including refused reads and unchanged unsupported-value fallback.
The frame-level theorem keeps its exact signature and now reuses the public
backup-aware theorem. Existing decoder and evaluator definitions are unchanged.

Selected-local readback also agrees across pipelines. The new evalLocal law
changes only G.pipeline, with every other global field, frame, fuel, raw state,
typed index and runtime plan identical. Fuel zero and successor cover actual
Source timeout and local lookup; full Source result/state plus original raw
frame are equated. Arbitrary Source execution and unchecked arithmetic are
outside this law. Context induction covers nil/cons, not all Raw-family cases.
The existing semantic ledger records these exact boundaries.

Focused MCP/builds and scoped audits passed for all six new public lemmas;
each uses only propext, Classical.choice and Quot.sound. No new state file,
representation rewrite, proof-budget change or H58 release is supplied.

Read-only finder and skeptic passed the public API, unchanged frame contract and
narrow evalLocal pipeline statement, using no Lean server or writes. Affected
LocalBlock, original dirty-readback controls and P16 built successfully (201
jobs), including the six exact axiom pins. The bounded affected run took 84.37
seconds with no swap/OOM; this is not a controlled before/after speed comparison.

## Source read observations under view agreement and capture

After adopting master 05d2c2587, four additive generic laws connect selected
readback to the existing authoritative RawFrame view. Equal clean backups and
word views give equal selected decoding, with no world premise. Equal worlds
additionally give equal complete optional Source result/state under the same
global, frame, fuel, index and runtime plan. Only the original raw-frame return
component is projected away; its metadata is deliberately not equated.

The existing capture operation preserves backup, world and authoritative view,
so it preserves selected decoding and the Source observation. One concrete
LocalBlock control exercises both pipelines and records that sparse flag
metadata is none while captured flag metadata is some(view flag). Equal Source
observations therefore do not imply equal raw frames. Refusal remains explicit.

The semantic ledger records decoder none/some cases and exact premises.
Read-only finder and skeptic both passed the four laws and the control without
Lean or writes. MCP and the 121-job LocalBlock build passed; all five declarations
use only the standard three axioms. The bounded control/audit run exited zero in
122.50 seconds with no swap/OOM. Its earlier inference failure is retained;
the repair supplies the captured frame explicitly and changes no statement.

No existing decoder, Source evaluator, representation, premise, exclusion or
proof budget changed. General Source expression/statement integration,
raw-copy propagation, complete Raw-family accounting and timing acceptance
remain open; H58 remains on HOLD.

The affected LocalBlock, original decoder controls and P16 build passed (201
jobs), including exact axiom pins. This run took 80.33 seconds within the
existing memory/no-swap bounds; no before/after speed acceptance is claimed.

## Generic integer cleanup algebra

The next independent slice proves residue preservation, residue congruence and
idempotence of the existing Source.wrapBits for every signedness, width and
integer. Idempotence is lifted to the complete intrinsic intWrap value.
For every valid Source integer type and both pipelines, equal low-bit residues
of two raw words imply equal complete optional integer readback. This is a
sufficient preservation law, not a stated iff. Bool remains nonzero testing.

These are universal Lean laws, not additional finite vector copies. They do
not prove a general Source integration or integer encode/decode roundtrip.
The exact ledger records subtracting/non-subtracting cleanup branches.
Existing cleanup/evaluator/state definitions and frozen statements are unchanged.
The initial failures at local let-bindings are retained; explicit reduction
repaired the proofs without changing statements or budgets.

Read-only finder and skeptic passed the five laws without Lean or writes.
Focused MCP/builds passed. Residue congruence is axiom-free; residue preservation
and numeric idempotence use only propext; the two full intrinsic-value laws use
the standard three axioms. Exact axiom pins are in existing LocalBlock controls.
Full Raw/source/table/generator acceptance and controlled timing remain open.

Affected LocalBlock, original decoder controls and P16 built successfully (201
jobs) with exact axiom pins. The bounded run took 80.35 seconds with no
swap/OOM; this is not a controlled before/after speed comparison.

## Intrinsic integer and Boolean encoder-cleanup roundtrips

With master unchanged at 05d2c2587, the next slice connects cleanup to actual
Source.Val.word. The existing intWord encoder carries the nonnegative 256-bit
residue; for every valid width, 2^bits divides 2^256 and preserves the narrower residue,
including for negative inputs. Cleanup after encoding any integer yields the
complete intrinsic intWrap value. An unsigned/signed range proof then establishes
that every already bounded intrinsic integer is returned unchanged by its actual
word encoder and published cleanup, in both pipelines. Boolean false/true
roundtrip separately through the existing nonzero test.

These are universal kernel proofs, not a new finite oracle or decoder.
The exact unsigned, signed-nonnegative, signed-negative and Boolean cases are
recorded in the semantic ledger. An initial header elaboration failure is retained:
Word erases the layout, so the new roundtrip statement supplies D explicitly.
No existing statement or definition was changed to accommodate a proof.

Focused diagnostics/builds and axiom audits passed. Numeric encoder/range helpers
use propext and Quot.sound; the decoder laws use only the standard three axioms.
No unsupported-type roundtrip, arbitrary materialized-frame adequacy, complete
Source execution agreement or raw-copy integration is inferred. Those broader
queues and acceptance/timing gates remain open; H58 remains on HOLD.

Read-only finder and skeptic passed the six laws without Lean or writes.
Affected LocalBlock, original decoder controls and P16 built successfully (201
jobs), including all exact axiom pins. The bounded affected run took 78.32
seconds with no swap/OOM; no controlled before/after timing is claimed.

## VY2 Raw adapter producer handoff

H70 requested exact producer contracts under the H123 generic scope.
tests/h55/vectors-tables/raw-adapter-producer-handoff.json pins producer source
head 239f71cd3d547c01c0d751f9053c6442c918d0fc and the bytes, Git blobs,
source commits, line positions and 20 exact signatures in RawFrame, RawCoherent
and RawTypedScope. Pure Tier-A projection/preservation, certified Source
coherence transport and generic typed closure remain distinct contracts.

Completion and coherence premises remain explicit. RawSource.Supported remains
the existing LocalBoolControl-certified expression-statement slice.
Coherence is equality with the clean backup, not successful dirty cleanup.
No arbitrary physical adapter correctness, VY2 integration, gate acceptance,
new admission predicate or H58 release is claimed. The consumer must instantiate
the exact contracts and retain every premise.

Both static reviewers found a direct-proof signature extraction error; all
entries were corrected and reauthenticated, and both final reviews passed.
No Lean source changed. Prior source gate provenance is recorded separately
from consumer acceptance; the handoff does not close VY2's whole waiting item.

## H125/H57 environment-aware typing pair — H128 checkpoint

Source/TypingV2.lean adds Source.envLocOK and a v2 statement/block judgment
alongside byte-identical v1. A generic fold over actual v1 derivations checks
only declVar/declInit, recursively through all control/item bodies; every other
v1 premise is retained. The kernel-evaluated Boolean folds use generalized
casesOn with explicit structural recursion (the initial indexed-match G0
finding was fixed). No Lowering module is imported by Source.

V2 declarations derive the unchanged locOK evidence from envLocOK. Projection
retains an actual v1 derivation. The reverse bridge uses CompatibleAt, restricted
to nameable types passing v1 location rules; mapping-free-nameable environments
supply that premise, with an inhabited Boolean declaration control. The universal
declaration_admissible theorem needs no compatibility premise and supplies the
positive v2 H24 local-declaration obligation. The existing Loop memory witness
and intentional negative v1 theorem remain valid; v2 refuses that memory
declaration and admits a genuine initialized storage pointer.

Controls and seven core standard-axiom pins passed. Finder and skeptic passed
final code read-only without Lean; no budgets, maxHeartbeats, axiom sets or
exclusions changed. All 21 existing statement cases and 3 item cases are in the
case ledger. Tuple premises are deliberately unchanged. V1 is not retired and
existing inference/elaboration still uses v1.

H16 HOLD: three serial warm runs measured a sum of medians of 42.1964 seconds
before and 46.0804 seconds after, including 1.2825 seconds for the new v2 module
(+9.2046%). The five old Source files are byte-identical and the measurements do
not establish causation. The mechanical 10% threshold was not exceeded, but
H125's qualitative instruction to stop on noticeably slower checking applies:
Source work stopped, no unchanged timing rerun or library implementation followed.
That historical stop was released by the newest user decision on 2026-11-07:
the recorded +9% is accepted for H128 v2 and H125 library try/Error. Raw timing
logs and the original H16-HOLD report remain unchanged off Git. This Source-owner
checkpoint is ready for integration after its focused gates; consumer migration
and v1 retirement are not implied. Any further noticeable checking slowdown
still stops and reports; no budget or axiom change is authorized.

typing-v2-consumer-migration.json gives separate notes for V10 H24 first and the
direct H24/P8 refusal consumers. Consumers must version/reprove their predicates;
the positive v2 theorem must never be supplied to the false v1 predicate. Global
frontend/physical/compiler adequacy, automatic migration and library try/Error
support are not claimed. Coordinator approval is still required before any v1
retirement. Library support will be published as its own checkpoint/head.


## H125 library try/Error(string) — separate candidate checkpoint

H154 authorizes a typed delegated Source entry, preserving storage identity,
with explicit unavailable-calldata refusal and no physical/linkage adequacy.
H157 authorizes the one new StmtD.tryLibrary constructor: the family grows from
21 to 22 constructors; every existing constructor/premise remains byte-identical
and old theorem statements remain unchanged. No H57 pair is needed for this
new syntax. The environment-aware H128 pair and its negative v1 H24 controls
remain separate; v1 retirement and V10-first migrations remain open.

ExpressionTyping is a byte-preserving module split, re-exported through the
public Typing import. LibraryTyping reuses existing type elaboration, overload
selection and argument conversion for qualified and current-scope using calls.
Only public/external library functions with value/storage-pointer parameters
and value results are admitted by the new boundary. The caller may still
return a string from the Error handler. Memory/calldata library arguments,
non-value library results, Panic/multiple catch clauses and broader using
forms remain unsupported, with no claim of complete library coverage.

The typed entry preserves this/sender/value/static/storage context, increments
depth, uses fresh memory, restores caller memory, and rolls back callee
storage/logs on revert before the handler. Arguments and successful return
extraction are outside the callee catch. Value-only input uses the existing
Source ABI encoding; pointer input has no fabricated bytes and never uses
caller calldata. The generic withLibraryCalldata guard propagates through
internal computation and explicitly refuses unsupported calldata observation.
Its ordinary mode is the original action. Normal callAddr/enterInstance/
envLoop/dispatch source text is byte-identical to H128.

Both original LibraryTry JSON inputs resolve, elaborate every original body,
and execute f/g success and Error paths with Source results 8/18 and 9/19,
including the failure string. A separately labeled derived Source-only stress
input writes 13 through the library pointer, then reverts; the caller storage
observation remains 9. It is not compiler provenance for the derived input.
Malformed/foreign Error payloads, target shadowing/type/member refusals, actual
unavailable-calldata evaluation and zero-horizon timeout are controlled. Five
new guarded axiom reports are standard-only. Finder and skeptic found no
confirmed defect read-only without Lean. The optional descriptor experiment
and unsuccessful proof attempts are retained as raw failures off Git; no
budget/maxHeartbeats change, sorry, native_decide or new axiom was introduced.

The final same-resource timing comparison and affected/checkpoint gates are
tracked separately; this candidate is not declared mergeable before they pass.
Physical storage-pointer ABI encoding, linked-library installation and G01/
compiler adequacy remain gaps under H154. Source-only execution is not a fresh
EVM replay or an active-catalog rescope approval.


H16 STOP for the separate library candidate: the final three-run sum of
medians is 48.6740s versus accepted 46.0804s (+5.6284%, another 2.5936s),
counting all added/split modules. H132 requires stop/report on further
noticeable slowdown. No Source edits/checks or unchanged timing rerun follow.
This is a preserved draft, DO NOT MERGE. KeySort/version/layer checks passed;
raw timing samples and the new H16-HOLD report remain off Git.

The affected H24 gates are not passing: Frontend/Static/InferStmt lacks the
new library form and InferStmtComplete needs its new proof case. The failure
is a 200000-heartbeat elaboration timeout, not permission to raise budgets.
H125-STATIC-COMPLETE-01 requests the two live companion files or their owner
patch. Existing H24 negative source text is unchanged; no new passing H24
kernel claim is made across the failing dependency.

A final enabled-resource-plan review also found a real pending repair:
callLibrary needs preflight before positive-fuel early refusals/encoding and
when exposing completed success/revert outcomes after rollback. The current
frame wrapper alone does not preserve the pending-stop outcome protocol.
Plan=None functional controls remain valid; enabled-plan integration is not
accepted. The proposed repair is saved off Git for work after H16 release.

H141 resumed library checkpoint: the authorized Static helper, inferS branch and unchanged-statement completeness case compile. Both actual JSON units pass Static body checking, Source elaboration/execution, and derived rollback controls. The enabled-plan repair now checks preflight before entry and before exposing success/revert; request/ancestor, own-frame, early-depth and disabled controls pass. Frozen V07 SourceRefusal and TypingV2 controls pass. Independent read-only finder/skeptic found no concrete defect. Existing Static modules remain registered; their module-map rows now name the new case.

A new same-resource three-repeat Source measurement is 51.550647435 s, 5.9100% above the H141-accepted 48.673995498 s. This is a new H16 STOP, requested as H125-LIBRARY-TIMING-03. No causal attribution, unchanged timing retry, full affected/checkpoint pass, physical ABI/linkage adequacy or completed assignment is claimed. Prior sealed packets and raw STOP evidence remain unchanged. Current evidence is under /workspace/vy1-words-evidence/h141-library-after/.
