# H62 item 2: v10-storage empty-statement audit

Status: blocked on pinned-toolchain migration dependencies; full assignment unfinished.
Owner: solidity-h62-2-20261106/audit-v10-storage.
Branch: codex/solidity-h62-2-20261106/audit-v10-storage.
Frozen base: c6f550e281a7e5affa9a99bc2cdaed556dec00e4.
Repository: /workspace/solidity-lean.

## Scope and inventory

The initially clean work branch was 6cf853aea0417155aca29ddb91f1767d3f3a3cc4.
Fetched origin/master and the exact published base, verified base ancestry in
origin/master, and created only the assigned isolated branch at that base.
No pushes, PRs, merges, pre-gates, owner-file edits or H55 work were performed.
Coordinator inputs under /workspace/h62-coordinator-inputs matched all five supplied
SHA256 entries. get_goal is unavailable; the coordinator explicitly states that its
absence is optional and no goal was created or reset.

The deterministic generator is scripts/h62/item2/audit-v10-storage/census.py.
It unions 118 explicit module-map paths with 230 backend wildcard paths, deduplicating
to 322 files. Wildcards come from the frozen Git tree. Every input's bytes must equal
its BASE blob. It records 3281 theorem/lemma source signatures exactly once by stable
path/line/name ID, hashes signatures and source context, and records V10 area ownership.
It conservatively includes controls and private helpers. This is a lexical inventory,
not an elaborated interface-theorem census. Fully qualified names, semantic hypothesis
classification, simultaneous witnesses and statement-fidelity proofs remain pending.
Every row is explicitly uncovered. Bulk JSON stays outside Git; the generator is tracked.

## Checkpoint obligations

| Checkpoint | Status | Remaining |
|---|---|---|
| 1. Exact signatures/owners/premise classification | partial | Elaborated names/types, interface selection and global/per-input classification |
| 2. Simultaneous hypothesis witnesses | blocked | All statements; zero new verified witnesses |
| 3. Supported success/totality and trivial-compiler negatives | blocked | All new theorems/controls and failure/gas/fork boundary validation |
| 4. Witness/fidelity census | blocked | All semantic verification; source census reports every row uncovered |

No frozen theorem was weakened, no premise invented and no statement repair attempted.
No weakened/vacuous theorem has been established by this preliminary work; this is not
an assurance that there are none. Typed dependency tickets and next steps are in
[the blocker queue](../../tests/h62/item2/audit-v10-storage/BLOCKERS.md).

## Verification and resource evidence

Actual official binary: Lean 4.35.0, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
Lake 5.0.0-src+eb6cafb (Lean 4.35.0). Archive SHA256 matches toolchain-pin.json.
Pinned KeySort check passed with explicit -j1 and --tstack=131072; guarded reproduction
elapsed 1.617805099 s, observed peak group RSS 507736064 bytes. No RUNTIME_GATE_PASS is
claimed because required dependency checks fail. Initial v4.24 version inspection was
setup discovery; its KeySort attempt did not run because /usr/bin/time was absent.
It supplies neither a proof nor a migration baseline.

Five source-scanner regression tests pass, covering nested comments, misleading strings,
nested default assignments, equation-style proofs, let conclusions and match branches.
Two final census runs are byte-identical. Each input matches the frozen base.
Pinned dependency build and resource-guarded reproduction both exited 1 in unchanged
Syntax.Raw, Hash.CollisionBound and Source.Ctor. Reproduction took 54.7867672 s with
1608388608 bytes observed peak group RSS. Owners are migrate-syntax, migrate-hash and
migrate-source. No dependency fix is within this lane's write scope.

Validation uses validate.sh (writer lock), validate.py (12 GiB per-process address-space
cap and aggregate RSS guard, 4 GiB available reserve, zero host swap), and an isolated
TOML with explicit Lean -j1, disabled artifact cache and dedicated v4.35 build directory.
Inspected traces use only the pinned build path. One Lean child was observed. Guard
cleanup is bounded and only kills the runner's own process group. No systemd-run was used.
Full affected validation/acceptance/run-lean gates and before/after proof timing comparison
remain pending behind the failed dependency gate. No proof refactor or slowdown claim exists.

## Independent reviews

Read-only finder and skeptic, neither using a Lean server, reviewed the census and runner.
They found and drove fixes for swallowed equation bodies, truncated let/match conclusions,
unvalidated frozen inputs, working-tree wildcard omissions, unbounded TERM cleanup,
misleading raw resource-stop exit records, relative runner cwd and lock documentation.
After fixes, both found no further concrete census defect in the current corpus. Both
explicitly limit acceptance to lexical scanning and preserve all semantic/proof gaps.
Runner closure review and detailed evidence are exported off Git with the handoff.

## Handoff boundaries

Zero new Lean declarations/helpers, axioms, sorry, trust shortcuts or heartbeat overrides.
No generated roots, module maps, axiom pins, library imports or interfaces changed.
No registration fragment is needed until additive proof modules actually exist.
All four checkpoints and the original persistent goal remain unfinished. Owner migration
resolution is required before proof-bearing imports can check. The saved tickets are
for coordinator retrieval; no relay delivery or external message is claimed.

Final runner regression: a process ignoring SIGTERM was killed by the resource guard
in 2.608168363 s, child/effective exit -9, stopped=resource guard. Final locked-wrapper
KeySort passed in 1.814585664 s, observed peak RSS 518316032 bytes. Relative to the
previous guarded 1.617805099 s sample this is +12.163%, so further Lean runs stopped
under the >10% timing rule. These are repeat prerequisite samples with runner changes,
not a validated before/after proof-refactor comparison; no cause is inferred. Comparable
proof/build timing remains outstanding. The failed dependency JSON predates the final
runner cleanup and child_exit-field fixes; its command/exit/timing provenance is retained.

Final static boundary checks passed: layers (857 core modules, zero frontend/parser
reaches), register.sh --check and fragments.sh --check. Independent final finder and
skeptic reviews found no concrete handoff status/scope mismatch. No full gate was run
past the known failed dependency boundary.

## H70 candidate classification while Lean is held

The coordinator acknowledged accepted migration-owner relays and explicitly held all
further Lean runs pending Syntax/Raw, Hash/CollisionBound, Source/Ctor and root-gate's
KeySort timing disposition. No Lean/Lake/MCP, build, runtime gate or timing check was
run for this continuation. No repair was fetched or original-file permission inferred.

The five candidate bundles are recorded in
[candidate-bundles.json](../../tests/h62/item2/audit-v10-storage/candidate-bundles.json).
Their complete frozen source signatures and hashes are attached by the deterministic
classify_candidates.py generator to off-Git evidence. Shared inputs are a single tuple
per theorem, with binder order retained; existing fixture definitions are referenced
without editing or replacing them. Exact names come from explicit frozen namespaces,
not a new Lean elaboration. All five signatures have zero global premise-structure
arguments: Env, functions and machine/state values are data parameters, while the
listed hypotheses are per-input observations or execution feasibility.

| Exact namespace suffix | Joint hypotheses on the same inputs | Contract role |
|---|---|---|
| LoopLaws.turn_step | nonzero, cond and step for the same rc/rb/machine/result/flag | Conditional single-turn adapter |
| LoopLaws.turn_exit | cond on the same rc/rb/machine; rb remains unrestricted | Zero-guard exit; no body-success premise |
| LoopLaws.run_single_loop | finished on the same cond/body/machine/result | Assumes whole-loop success; no independent termination claim |
| SourceWordRead.read_total | ordinary on the same E/context/frame/path/locals/state | Total outcome equation, retaining missing-cell failure |
| SourceWordRead.complete | ordinary, present and coherent on one shared dependent tuple | Source/fixed-readCode success derived from raw input observations |

LoopLaws means Solidity.Backend.StorageOps.LoopLaws; SourceWordRead means
Solidity.Lowering.StorageOps.SourceWordRead. The loop candidates use frozen populated
controls: turn_step uses yes/body/initial/after and flag 1; turn_exit and run_single_loop
use no/pending/initial. The latter loop exits without executing its faulting body.
The read candidates use the same frozen environment, frame, left path, nil locals and
initial state. complete adds read value 11, the frozen machine and root slot 0.
SourceWordWriteControls.value is 53 and must not be substituted for that read value.
Negative candidates record exactly which input premise would fail after such changes;
these are unproved case plans, not executed controls or results.

No compiler parameter/selection contract, gas cost or EVM fork appears in these five
signatures. Their classification does not finish checkpoint 3: supported compiler
success, reject-all/always-revert negatives and observable failure/gas/fork boundaries
still need the originally required separate proofs and controls. Conditional adapters
are not classified as vacuous merely because they assume successful executions.

All 3281 original census rows remain uncovered and all four checkpoints unfinished.
This source-only classification adds zero Lean declarations, proofs, axioms or sorry.
The original failed dependency and timing holds are unchanged. Finder/skeptic review
and deterministic consistency evidence for this continuation are exported separately.

H70 review closure: independent read-only finder and skeptic confirmed all five binder
orders, joint input assignments, source roles and zero-promotion status. The finder
identified an older combined resume sentence that wrongly attributed complete-only
binders/premises to read_total; it was split into the exact two bundles above, and the
resume command now explicitly requires coordinator hold release. The skeptic found
no status/scope/path mismatch. Neither reviewer used Lean or edited files. Generator
consistency and two byte-identical outputs passed; no witness satisfiability was checked.

## H70 requester continuation: all-row static classification

Starting head: 2d53437157aeb2385aeaaab7b7bb891e92566058. The requester directs
continued static work across all 3281 uncovered rows, retaining zero verified
witnesses and waiting on migrate-syntax Raw, migrate-hash CollisionBound and
migrate-backend producer repairs. Earlier Source/Ctor and root-gate timing holds
have not been explicitly released. This continuation runs no Lean, MCP, Lake,
build, timing or runtime gate; no original file or toolchain is edited.

surface_classification.py adds a deterministic off-Git ledger with exactly one row
per original census ID. Each retains its exact source signature/hash/context hash,
owner and uncovered status. It extracts grouped declaration binders with source
offsets/types, leading forall source text, the complete result text, and occurrences
of selected representation/endpoint markers. Bare or unsupported syntax is retained
as unresolved. Section dependencies remain unresolved explicitly; in particular,
PublishedOps.lean has source variable declarations, so a no-declaration-binders
label must not be interpreted as a closed theorem or absence of logical premises.

| Static syntax class | Rows |
|---|---:|
| declaration-binders | 1247 |
| declaration-binders plus leading-forall | 40 |
| no-declaration-binders | 1672 |
| no-declaration-binders plus leading-forall | 322 |
| Total, all still uncovered | 3281 |

Signature-marker occurrences: FiniteRun: 275, Represented: 592, Transport: 410,
PathSupported: 28. Counts overlap and include conclusions, so they are not counts
of hypotheses, global structures or feasible inputs. No inference about semantic
premise class, statement vacuity or satisfiability is made from token occurrence.
No statement is excluded; semantic interface selection/verification remains pending.

Manual candidate metadata now has thirteen exact selected declarations: the original
five and TargetOperations.ofSlot_toSlot/toSlot_ofSlot/toSlot_injective/add_keysFit/
run_read/run_write/run_copy/run_copy_self (namespace Solidity.Backend.StorageOps).
Local bounds and equality in the conversion cases share the same root values.
The four run cases have data binders but no logical success hypotheses. Populated
read/write/nonself-copy plans observe stored11, write bool-true word1 over11, and copy
root 0 = 11 into root 1 = 0 respectively. All are fixed symbolic target-code contracts,
not arbitrary compiler selection or gas/fork correctness. Self-copy preserves the
machine, so empty code also meets that identity; it is not presented as a useful
reject-empty-code control. These are source plans only. Thirteen manual source
classifications leave 3268 rows without manual semantic analysis and all 3281 without
new checked witnesses. The existing five were not counted again as new work.

[Producer field inspection](../../tests/h62/item2/audit-v10-storage/producer-field-classification.md)
separates the three local endpoint structures from a universal compiler producer,
and retains FiniteRun.hash_bound over ALL preimages. It is not a checked structure
inhabitant or an added theorem row. No backend repair diff was supplied or applied.

External consistency checks: five static-extractor regressions pass; candidate and
all-row outputs each generated twice and compared byte-identical; all frozen input
bytes matched BASE; no row was lost, duplicated or promoted. Independent read-only
finder and skeptic reviews found no concrete mismatch in extraction or the eight
new shared-input plans and preserved all semantic/proof limitations. Neither used
Lean/server or edited files. Detailed review and generated bulk evidence are off Git.
All four checkpoints and the original goal remain unfinished; no new Lean helper,
axiom, sorry, heartbeat override, root registration or interface change was made.

Final static review closure: both reviewers checked producer field fidelity, including
the universal hash bound and the same after state, and found no concrete mismatch.
Source-only counts and the new backend wait are accurate; old holds stay unreleased.
The ledger explicitly defines binder offsets relative to the signature suffix after
the declaration name. No semantic or proof coverage is promoted by successful parsing.

## H70 semantic premise and feasibility planning: 25 selected statements

Starting head: 166c529477b3767cd6362fe73dd1c9072c9f0a5e. The owner supplied a
partial Hash overlay; the requester directs continued semantic premise planning and
waits on migrate-syntax Raw, migrate-hash CollisionBound and migrate-source Ctor.
No ticket destinations or current-owner delivery are pending in this routing pass.
No repair application, owner agreement, permission, validation or hold release is
inferred. No Lean/MCP/Lake/build or new timing runs were made.

The selected plan set now contains every explicit theorem in four modules:
LoopLaws(3), SourceWordRead(2), TargetOperations(14), LayoutAccess(6), total 25.
Twelve are new manual classifications; the previous thirteen are not counted twice.
The remaining 3256 census rows lack manual analysis; all 3281 lack new verified
witnesses. The deterministic all-row ledger retains every original ID/signature/hash
and uncovered status. Its syntactic class/marker totals are unchanged.

The new TargetOperations plans retain all local fitting, membership, raw read,
representation and target-agreement premises. represented_copy also retains one
FiniteRun structure, numeric transport, performed graph copy, support, graph apart,
symbolic nonaliasing and all source/target/query footprint coverage on one SC tuple.
The selected certificate includes the global function-range field ∀ pre, H pre < N;
this is not weakened to pre ∈ P. It is not a universal Source compiler producer.
SC is a proposed local fixture using the existing public Schema0, a bool-to-bool
mapping, source keytrue/destination keyfalse, nonempty source-observation query,
source word1/destination word0, numeric addresses4/2, N8/L1/R1, selected preimages
entry00/entry10 and bounded hash outputs2/4 (otherwise0). All fields still require
joint proof. Target observations are constructed from the same symbolic store.
The getD-defined graph result is not itself proof of successful copying.

LayoutAccess.resolve_bounded/resolveMany_length/resolveMany_bounded distinguish layout
fit and placement from successful resolution. The LS plan uses a two-word struct at
root0 with L1/R2 and keeps repeated field0/field0/field1 requests and repeated
root0/root0/root1 results. mem_runPreimages uses a nonempty hashed address with its
actual entry00 preimage. resolved_families_commute uses two nonempty disjoint resolved
families at roots0/1; partial effects write true/false and are not required to succeed
by the frozen theorem. Matching failure remains in its contract. resolved_family_outside
DOES require performed success and keeps the same independently resolved outside
query, combined family-plus-query preimages and full hash-range premise. Its getD
result also needs an actual success proof. Root-only LS preimage lists are empty
because those actual accesses hash nothing, not because accesses were dropped.

SC/LS entries are plan aliases only, not new Lean declarations. The binder checker
now compares selected source binder order with metadata. It distinguishes the two
SourceWordRead initial forall input blocks from retained universal conclusions in
write_agreement and resolveMany_bounded. The latter remain statements about EVERY
location/address member; they are not reduced to existential selected observations.
The first draft check caught this distinction and was corrected before acceptance.
No input premise or conclusion was removed from any frozen statement.

[Hash overlay review](../../tests/h62/item2/audit-v10-storage/hash-overlay-review.md)
verifies the routed checksum and context, reconstructs the advertised new blob only
in memory, and compares 65 exact source theorem headers unchanged. The canonical
artifact passes git apply --check. It was NOT applied or Lean-checked; full migration,
axiom/guard-message checks and all earlier holds remain pending. The first transcription
had one extra context-space; its failed receipt is kept distinct from the corrected,
SHA256-matching canonical artifact. These dependency checks add no v10 witness rows.
The deterministic review reproducer is tracked, while bulk patches/receipts stay off Git.

Independent read-only finder/skeptic reviews are required for this checkpoint and
exported with the final evidence. Static binder/field checks, deterministic generation
and source-header equality do not imply satisfiability or checked theorem fidelity.
All four checkpoints and the original goal remain unfinished. Zero new Lean helpers,
axioms, sorry, heartbeat increases, registration edits or original-file changes.

Final review closure for this checkpoint: both independent reviewers found no concrete
mismatch in the twelve new correlated plans, binder scopes, producer/global-field
limits, overlay script or routing status. The finder independently reproduced the
canonical checksum/context/new blob and 65 unchanged source headers, without Lean or
application. The ledger now carries the same SC/LS plan definitions as its companion
candidate artifact, so shared aliases remain available in either static output.
The canonical/initial-transcription receipts remain distinct. No witness is promoted.

## H82 retirement: final preservation only

Human-approved stop-and-handoff and the explicit H70/H82 ordering correction override
all concurrent continue receipts. Successor: solidity-v07-v11-20261030/v10-storage-operations.
No new proof implementation or automatic continuation is authorized. This checkpoint
adds only the full original assignment/goal/queue, exact original ownership and
322-file scope manifests, retirement directives and complete open-queue state under
[retirement/](../../tests/h62/item2/audit-v10-storage/retirement/OPEN-QUEUE.md).
The predecessor work head was b99808cca35e0cee53df6aa3d11f79616cf35b58; the final
preservation head is recorded in the exported result/bundle to avoid circular hashes.

The complete assignment transcript was read from the original thread; both read-only
reviewers found no omitted requirement, queue content or owner-map entry (123 entries).
Its file hash differs from the reported original renderer fingerprint, explicitly
recorded in prompt-provenance.json; renderer-byte identity is not claimed. The exact
queue and all three original write scopes plus 322 frozen paths/hashes are preserved
as files in the committed patch/bundle, not merely coordinator-local references.

No pause operation is exposed. The only goal tool supports complete or blocked, so
PAUSED cannot be requested through its schema. No completion/block transition is used
as a substitute, and no goal is created/reset. Worker implementation stops; coordinator
must persist the authorized PAUSED state. The prior trusted-context errors remain
historical evidence. Original VM/branch/artifacts are preserved without deletion.
No H71 push authorization was available in thread/files; no push, merge, PR, master
change, source edit, Lean/MCP/build or timing rerun occurred. All four checkpoints and
all open proof/backfill obligations remain as listed in retirement/OPEN-QUEUE.md.

## H82 successor: checked loop premise bundles

The additive LoopWitnesses test checks joint witnesses for all hypotheses of
LoopLaws.turn_step, turn_exit and run_single_loop on actual condition/body
programs and the existing populated intrinsic machine. The same frozen loop
module is byte-identical to the original audit base. A companion map records
its exact declaration signatures and witness names without rewriting the
conservative frozen census. These are three checked premise bundles, not a
claim that all 3281 rows have been audited.

The positive step changes the stack; the zero-condition witness skips an actual
REVERT body. Separate controls preserve body-revert propagation, the distinction
between a nonzero returned control index and a fault, and the failed nonzero
premise at zero. The declarations pass Lean 4.24.0 with only the existing
standard logical axioms. The original scratch attempt confused the pending
jump body's nonzero index with a direct fault; that failed attempt is retained.

No production interface, representation, heartbeat or Source implementation
changed. There is no arbitrary compiler/reject-all compiler contract proof,
physical gas/fork result or v4.35 migration hold release. Full elaborated census,
remaining joint witnesses, compiler totality controls and final validation stay
open. The existing inventory and earlier failed gates remain unchanged.

The finished-loop premise also has a positive-iteration witness: the existing
populated store starts at header 11, the body writes zero, and the second
condition exits. The actual loop program returns that changed machine. A direct
monolithic reduction exceeded the original heartbeat limit; composing three
checked instruction equations through the existing turn laws passes without
a budget change. The concrete 11-to-zero observation uses no axioms. This is
one supported terminating program, not arbitrary positive-loop termination
or a compiler totality theorem.

## Checked slot-key premise bundles

KeyBoundsWitnesses adds six joint premise bundles for the unchanged frozen
TargetOperations slot roundtrip, injectivity, offset, typed-step, path and query
key-bound adapters. A nested hash/data location with key 7 supplies the same
concrete inputs throughout. The typed path crosses a Boolean mapping key and
a dynamic-array index using the existing schema fixture. The injectivity
witness selects the same location on both sides; it does not claim distinct
locations can have equal slots or that every input pair is feasible.

A key equal to the word modulus fails the exact bound. A separate control
shows that the fitting address still has an unavailable live graph read in
the default value. That observation is not a Source or compiler refusal. All
nine proof declarations are axiom-free. The companion map preserves six exact
frozen signatures; the original conservative census is unchanged. These six
bundles plus the earlier three loop bundles do not close the full audit,
compiler totality, physical separation or migration obligations.

## Populated representation and agreement witnesses

RepresentedWitnesses checks all joint premises of the frozen represented_read,
write_agreement and represented_copy adapters using the existing concrete scalar
endpoint. The reached target state contains the true word; the unwritten target
fails that initial cell agreement. Actual SLOAD returns the populated word,
SSTORE changes it from one to zero while the covered agreement is derived, and
actual scalar self-copy preserves the whole machine.

The self-copy witness uses dst=src and an explicitly empty query frame; its
apartness and nonalias frame predicates are vacuous on that empty list. It does
not cover a nonempty disjoint frame. FiniteRun and transport come from the
existing concrete local endpoint, with their original parameters and fields.
This is not a universal Producer or a physical/source/compiler bridge.

All eleven declarations and their axiom guards pass with only the standard
logical axioms. An intermediate malformed record update was rejected, and its
error-recovery axiom guards failed as intended; that receipt is retained, never
accepted as a proof or pin. The corrected source passes without recovery axioms.
The companion map records three exact frozen signatures. Twelve premise bundles
are now checked across these three audit packets; the full conservative census
and compiler totality/failure/gas/fork obligations remain open.

## Deterministic witness reference accounting

The witness_registry tool exports the exact frozen Git inputs to a temporary
tree and reuses the original conservative census, including all byte checks.
The live census and its drift rejection remain unchanged. At checkpoint C198 the registry accounted
for all 3281 rows exactly once: 12 mapped witness references and 3269 unmapped
rows. It checks unchanged mapped interface files, exact signatures and context
hashes, witness declarations and the three kernel-checked test source hashes.
The source lexer is not a complete elaborated-type or semantic fidelity checker;
manual reviews and separately executed Lean/axiom-guard checks remain necessary.

All twelve audit tooling tests pass, including seven corruption variants for
duplicate/unknown rows, changed signatures, missing witness names, altered proof
sources, changed interface files and stale kernel-source pins. Bulk registry
output remains outside Git; only its deterministic generator, small source pins
and tests are committed. No global axiom inventory is rewritten.

During the preceding packet, an empty-list lemma refinement was committed before
its failed check result was inspected. Commit f5010fe17 is not an accepted proof
checkpoint. The corrective commit 4e83a94a3 followed a passing kernel and axiom
guard check; its repaired source is the one pinned here. The failed receipt and
history are retained. Full lane, compiler-totality and migration gates remain
open.

## Actual Source cell-read premise witnesses

SourceReadWitnesses reuses the published Source fixture and concrete read
certificate. Ordinary-root, raw cell presence and target-word coherence hold
jointly at the same typed inputs. Readonly/static Source reading preserves the
whole input state. Missing ordinary cells keep their Source stuck result; a
transient root cannot meet the ordinary premise. Wrong-slot SLOAD still runs
but violates raw word coherence, so this is not a target-refusal claim.

The Source path and target slot remain independent parameters of the frozen
adapter, coupled here only by its existing word observation. No Source address
compiler, general world relation or physical adequacy is supplied. No Source
implementation or frozen interface changed. Two more exact frozen premise
bundles are checked; the original conservative ledger remains unchanged.

The updated registry has fourteen mapped references and 3267 unmapped rows,
with unchanged original row identities. Kernel-source pins include this fourth
checked test module. Source paths and target slots remain independently chosen
inputs; the new certificate reuse does not establish their compilation relation.

## Actual Source write premise witnesses

SourceWriteWitnesses reuses the published Source fixture and complete write
certificate. Its writable/ordinary flags and int53 word observation jointly
inhabit source_write, storeVal_word and complete at the same typed inputs,
with actual storeVal fuel one. Standard decide discharged the full raw bundle.
Static, zero-fuel and type failures retain their distinct outcomes. A static
zero-fuel call times out before write refusal; a scalar Boolean word observation
does not make it compatible with the fixture's uint destination. A different
target operand still executes, while violating the selected word agreement.

The source path and target slot remain independent as the frozen statement
specifies. No address compiler, value lowering, world relation or general
preservation theorem follows. Three additional frozen premise bundles are
checked without Source implementation or interface changes. Registry source
pins and exact original row identities are extended, not replaced.

The current reference ledger has seventeen mapped bundles and 3264 unmapped
rows, with five kernel-checked test modules. The earlier counts are historical
checkpoints; no original census row or failed receipt has been discarded.

## Nonempty finite layout and operation-family witnesses

LayoutWitnesses checks all six LayoutAccess premise bundles using a mapping
to a fixed two-word array, repeated left requests and a nonempty separate right
family. Existing fit/placement conditions remain exact. Actual clear/set families
commute; both selected cells change under the combined families, while the
left family alone preserves the separately resolved right/outside query. A later invalid offset rejects the complete request list.

The hash is a concrete finite-model function, not Keccak or a globally injective
function. Its complete stated run contains one repeated preimage; adding a
different preimage breaks the region premise. No global crypto premise or new
Source cap is introduced. Request resolution and operation indices are explicit;
no actual emitted-access, Source/layout, liveness, packing or physical bridge is
inferred. All original frame/coverage/region premises are retained.

Six more frozen signatures are mapped to checked joint inputs. The original
conservative census and pending compiler/world/migration obligations remain open.

The current reference ledger maps twenty-three bundles, leaving 3258 original
rows unmapped. Six kernel-checked test modules supply those references. Both
layout-family selected cells change in the positive control; left-only execution
preserves the outside cell. This is a finite layout/operation-family result,
not physical execution or a general Source storage compiler.

## Data-only statements kept separate

Five remaining statements in the original 25 source plans have no logical
hypotheses: the reverse slot roundtrip and the four target read/write/copy
execution equations. TargetInputWitnesses checks Nonempty input tuples using
existing slots, the published populated machine and word. These do not certify
arbitrary compiler success or supply new logical-premise bundles. Registry
counts now distinguish data inhabitance from joint-premise evidence explicitly.

The original 25 source-planned statements have 20 checked joint-premise bundles
and five data-only classifications; three additional Source-write bundles were
checked separately. This remains a small reviewed subset of the conservative
3281-row ledger, not a completed elaborated census or full assignment acceptance.

## Bounded checkpoint after the witness packet

At source head 5a12b4c8adcb6367b37f32bea33e4da63e69624e, the shared checkpoint
affected-module build exited 124 after 600.66 seconds under its existing
600-second limit. Peak sampled aggregate RSS was 1137885184 bytes, with no
resource stop or OOM. This is a timeout, not a diagnosed source proof failure.
The prerequisite guard refused the subsequent library build; no unchanged
retry or larger limit was used. Full affected validation remains unfinished.

The initial trust, orphan, layer, fragment and inventory commands lacked Node
in the checkpoint PATH. Separate checks with the installed Node directory
restored passed trust, orphans, layers and fragments. Roots passed in the
original checkpoint. The inventory check still fails with zero errors and
4552 unrecorded changes; pins were not rewritten. Raw documentation checking
fails with five missing and 126 ambiguous references. These receipts remain
separate from historical baseline failures and do not establish a checkpoint
or whole-lane pass. Independent read-only finder and skeptic confirmed the
timeout/infrastructure distinction without running Lean or changing files.

## Generated nonempty operation families

GeneratedFamilyWitnesses checks both original OperationTransport contracts at
the same finite inputs. The left touched list contains two repeated addresses
(stride zero, count two); the separate right list is a singleton. Every bound,
recursive preimage, region, separation and performed-result premise is retained
in its joint bundle. Both selected cells change under the combined effects,
and the left-only successful effect preserves the outside query. A distinct
additional preimage breaks the constant-hash region premise. This supplies no
global injectivity, physical execution or Source compiler bridge.

All 17 theorem axiom guards passed at the unchanged Lean4.24 resource limits.
Independent read-only finder and skeptic found no semantic or coverage issue.
The frozen reference ledger now maps 30 of 3281 conservative rows: 25 joint
bundles and five data inhabitants, leaving 3251 unmapped. This is additive
test-only progress; the failed C203 full checkpoint is not superseded.

## Exact touched-set transport inputs

The same finite generated-family packet now witnesses the six logical-premise
contracts in Touched and classifies its two data-only contracts separately.
Numeric membership retains query bounds and query preimages. Nodup uses a
nonempty singleton; the repeated left list and its numeric duplicates are
explicitly retained, rather than passed to the distinctness contract.
Cross-family numeric separation and individual write commutation retain the
original per-run region and footprint coverage premises. A positive-stride
visit changes index zero and preserves index two outside its footprint.

The extended module passes all 32 theorem axiom guards under unchanged limits.
The initial strengthened conjunction proof failed elaboration; that recovery
artifact was rejected, and the corrected explicit tuple passed before guard
acceptance. Independent read-only finder and skeptic found no fidelity issue.
The frozen registry now records 38 mapped rows: 31 joint bundles and seven
data inhabitants, with 3243 rows unmapped. These finite test witnesses do not
close general compiler success, physical adequacy, migration STOP holds or the
failed C203 full validation. Existing production statements remain unchanged.

## Push lifecycle premise witnesses

PushWitnesses maps the six original OperationPush contracts: four checked
joint-premise bundles and two data-only inputs. Primitive reuse resets the
newly live scalar from true to false while an older retained slot remains
true. Aggregate reuse preserves the captured child identity and changes the
selected live read from unavailable to available; another retained raw child
remains nonlive. Fresh allocation supplies the existing primitive default.
A saturated length of 2^256−1 fails the original push capacity check, while
the fresh case succeeds; no new admitted-source cap is introduced.

The initial Extent/Index mismatch and reflexivity-tactic failure are retained
as rejected elaborations. The corrected source passes all 14 axiom guards at
unchanged limits. Both independent read-only reviews found no fidelity issue.
The frozen reference ledger now maps 44 of 3281 conservative rows: 35 joint
bundles and nine data inhabitants, with 3237 unmapped and nine pinned witness
modules. These graph lifecycle inputs do not establish Source allocation
identity, physical target lifecycle, compiler adequacy or world rollback.
The failed full checkpoint and all original producer holds remain open.

## Semantic push and pop inputs

The lifecycle extension retains the semantic push premises separately from the
operation adapter: nonprimitive retained reuse and fresh defaults share the
same original values and actual successful results. Pop uses the exact former
last index of a populated child. Its successful result keeps allocated extent,
clears the retained raw word and invalidates the live read. One pop succeeds
and the second fails; this Option result supplies no world rollback theorem.

All 22 guards in the combined push/lifecycle test module pass. Independent
read-only finder and skeptic found no fidelity issue. Five more frozen rows
are mapped: three joint bundles and two data-only failure-iff inputs. The
conservative registry now maps 49 of 3281 rows, with 38 joint bundles, eleven
data inhabitants and 3232 unmapped rows. Original Source/physical/compiler
obligations and broad validation remain unfinished.

## New-head bounded checkpoint and exact documentation baselines

At source head 3eb4734bdcc4da2f3b0b5cbab9368d3edf795229, C210's affected
build exited 124 after 600.36 seconds under the existing 600-second limit.
Peak sampled aggregate RSS was 1593192448 bytes, with no resource stop. The
prerequisite guard blocked the library build. Trust, orphan, layer, root and
fragment checks passed; this is not checkpoint acceptance. Raw documentation
checking still fails with five missing and 127 ambiguous references; the
axiom inventory reports zero errors and 4611 unrecorded changes. Pins were
not rewritten, and all prior failed receipts remain separate.

compare_doc_trees.py runs the same current strict checker against exact
committed current, published and frozen trees. Only checker working-directory
selection is adapted; exclusions and strict logic remain unchanged. Snapshot
tracked paths are checked, with no untracked cache or rescue files imported.
The current and published-master trees have identical five-missing/127-ambiguous
findings, with zero new findings between them. The frozen tree has zero missing
and twelve ambiguous references under that same checker; its comparison still
FAILS with 129 new formatted findings and nine removed findings. The published
comparison does not replace the frozen requirement or make raw strict PASS.

Five helper tests cover root adaptation, unsafe archives, formatted findings,
committed-tree isolation and infrastructure failure. An independent skeptic
found that absent checker completion could masquerade as no new findings.
The helper now validates recognized strict exit status and the matching final
summary, retaining raw logs before rejecting infrastructure failures. The fix
was independently confirmed and all three recorded completions validated.
No production Lean source changed during this tooling/disposition checkpoint.

## Operation-level totality and rejecting generators

TargetTotality proves existential successful runs of the existing readCode,
writeCode and copyCode for every typed slot/machine (and typed word for writes),
using their unchanged public run equations. An always-reverting code generator
and an empty-code generator cannot match the full public read equation for
any machine. The empty-code refutation observes actual finite stack-length
growth. Concrete populated machines establish that the quantified domain is
inhabited, and write/copy controls observe changed cells with context preserved.
A revert prefix skips the following write; no after-state or rollback is
inferred from the revert outcome. The final zero is a jump index, not gas.

All twelve theorem axiom guards passed; independent read-only finder/skeptic
reviews found no issue. The initial namespace-qualification error is retained
as a rejected elaboration. This is totality for the existing symbolic-slot
operation code, not Source compiler admission, packed/physical expansion or
EVM gas/fork adequacy. The 49 mapped premise/data references and 3232 unmapped
rows are unchanged. The published Source changes required separate revalidation of Source-dependent
historical witnesses; the C213 section below records that completed check.

## Revalidation after the published Source update

C213 rechecked all nine pinned witness modules against the adopted owner
publication. Seven Source-free files passed first, then the Source read file
built its updated shared imports and passed, followed by the Source write file.
All 126 theorem axiom guards passed with unchanged witness source bytes and
unchanged proof limits. Reference corruption tests also passed. Kernel-source
metadata now points to the fresh receipts and their dependency head.

Coverage remains 49 mapped references (38 joint bundles and eleven data inputs),
with 3232 unmapped. This establishes current compatibility of those selected
witnesses, not general Source compiler admission, numeric/physical adequacy,
world rollback or release of the separate v4.35 timing/trust STOP holds. No
Source producer, frozen contract or witness statement was edited.

## Dependency routing after published Source proof updates

C217 compares the exact Git trees at the C213 kernel-receipt head and the
adopted master head. Seven of the nine witness source/import closures have
identical bytes. SourceReadWitnesses and SourceWriteWitnesses each reach one
changed file, Source/Ctor.lean. This is a lexical one-line import routing aid,
not an elaborated dependency certificate. It records external imports without
comparing toolchain/package objects or generated artifacts. Equal source bytes
do not transfer kernel, axiom, performance or resource acceptance. Historical
kernel pins remain unchanged, and current-head Lean validation remains pending.

The two additive tool files were initially created without the required writer
flock. No concurrent modification was observed; unobserved activity cannot be
ruled out. Subsequent edits, checks and commit preparation used the lock. The
C216 resource-stop receipt is retained; no unchanged Lean retry was performed.

Coordinator option 1 for V10-R217 authorized recovery of the same bounded
runtime. It recovered with the original 12 GiB memory cap, zero swap and serial
threads. The fresh unchanged preflight exited 1 before Lean started because
other parent-cgroup usage exceeded the existing headroom allowance. The
prospective command sets only the stack limit as authorized by H111; the
preflight refused before that shell or Lean executed. No proof budget,
memory cap, guard or historical failed receipt was changed.

## Focused Source witness revalidation after H113

C222 freshly kernel-checks the two unchanged Source witness files after adopting
the published Source/Ctor proof update. SourceReadWitnesses passes after rebuilding
its changed imports (235.99 seconds); SourceWriteWitnesses then passes serially
(1.85 seconds). All sixteen existing axiom guards pass. Peak sampled aggregate
RSS is 1696296960 bytes, with no resource stop under the H113 accounting formula.
These are separate import/cache states, not a matched performance comparison.

Only the two source-specific checked_head/kernel_log receipts change. The
validated_dependency_head field continues to name the historical complete
nine-module check; seven unaffected modules retain their original receipts.
No source-identity comparison is promoted to a fresh kernel run. The reference
ledger remains 49 mapped rows (38 joint bundles,11 data inputs),3232 unmapped.
This checks the selected Source word-read/write premises and existing controls,
not general Source compiler admission, physical adequacy, world rollback, or
release of any separate v4.35 timing/trust/compatibility hold. No Source producer
or witness statement was edited.

## Populated target reuse joint witnesses

C223 adds a Source-free TargetReuseWitnesses fixture. The same populated Machine
simultaneously satisfies capacity and the selected empty-child-header premise
for both TargetRetainedCycle.after_reuse and run_reuse. Its retained child payload
is71 despite the zero header. Existing generic laws establish whole-Machine
execution and repeated reuse, rather than only sampled stores. The premise-free
run_pop_regrow_pop input is classified separately as data inhabitance.

Fifteen measured axiom guards pass. Positive observations retain payload71 and
outside99. An uncleared child actually executes but changes the Machine; a
saturated header refuses at push, an empty initial header refuses at pop, and
an always-reverting program differs from the successful reuse program. The
initial-pop cycle changes header1 to0 while preserving older payload71, so it
is not restoration of the original state. These are existing symbolic-slot
Evm.run endpoints; the final zero is an execution index, not a gas bound. No
Source compiler admission, physical-word bridge or world rollback follows.
Both independent read-only reviewers found the joint premises non-circular,
inhabited and faithful to the exact frozen hypotheses. Production interfaces,
definitions, statements, budgets and axiom inventories remain unchanged.

The C223 reference ledger adds exactly three frozen rows: two joint-premise
bundles and one data input. It now records52 mapped rows (40 joint,12 data) and
3229 unmapped rows. The new module has15 measured guards; source-specific pins
record its actual checked source commit. Earlier complete/partial validation
heads remain unchanged. Twelve additional success/negative/observation controls
are not counted as extra mapped interfaces. Full semantic/elaborated census,
compiler totality, gas/fork boundaries and original Source/physical/world
composition remain incomplete.

The corrected C223 registry checks pass, including targeted new-source and
new-pin corruption controls. The initial stale nine-module expectation failed
and its receipt is retained; the ledger now has ten witness modules. Trust and
roots pass. The current strict axiom-inventory check remains FAIL:16301 pinned
theorems,zero errors,260 unrecorded changes. No inventory write or trust-policy
change was made; H30 coordinator reconciliation remains separate. Local measured
guards establish only their recorded axiom sets, not global inventory acceptance.
