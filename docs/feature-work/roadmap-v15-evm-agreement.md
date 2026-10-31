# V15 pinned EVM correspondence: independent backfill and blocked integration

Batch `solidity-v12-v17-20261031`, task `v15-evm-agreement`.
Base: `2fe1f8932f96be15b00df03ba2cde46f64a87758`.
Branch: `codex/solidity-v12-v17-20261031/v15-evm-agreement`.
Repository: `/workspace/solidity-lean`.

**Lane status: blocked, not complete.** G46 and G47 remain open. This checkpoint
contains independently useful transport lemmas, not a pinned-EVM simulation,
compiler preservation theorem or transaction interpreter. No production
`Roadmap.Execution` instance is supplied. A generic transport theorem does not
discharge its hypotheses. No scope decision or new approval is requested.

## Binding inputs and ownership

The [intrinsic gate](../intrinsic.md), [G01 contracts](roadmap-g01-interfaces.md),
[G03 ledger](roadmap-g03-ledger.md), [G04 restrictions](roadmap-g04-restrictions.md),
[G06 interface](roadmap-g06-evm.md), [Osaka record](roadmap-g06-osaka.md),
[G02 measurements](roadmap-g02-measure.md), [decisions](../solidity-scope.md) and
[decision impacts](roadmap-decisions-impact.md) remain binding. The source
profile, observations, refusals, verdicts and `Fml.inTarget` are unchanged.
The core remains dependency-free. New imports are only in the Bridge umbrella.

Published components were inspected read only: [assembler/control components](backend-assembler.md),
[failure emission](backend-failure-emission.md), [creation artifacts](backend-creation-artifacts.md),
[hash premises](hash-collision-bound.md) and [precompiles](precompiles.md),
including their local-versus-parent proof boundaries. The local checkpoint
proofs consume `Backend.Failure.Local.finish`, `restore` and `outer_rollback`
unchanged; hash proofs consume the existing `HashPremise` and its two existing
membership monotonicity results. No reserved implementation is repaired,
recreated or imported from an unmerged branch.

## Queue accounting

| Item | Status and exact outstanding obligation |
|---|---|
| 1 / G46.01 | Open. No new opcode selection/truncation/control correspondence against Osaka. Published numeric/control bridges remain read only; their hypotheses are not discharged here. |
| 2 / G46.02 | Open. Compiler byte-memory/calldata representation transport to an actual pinned transition still needs the published memory bridge, padding, driver and exact expansion/resource clauses. |
| 2 / G46.03 | Open. Persistent/transient numeric-slot consumers still need symbolic-path representation, approved per-run region premise and published slot adapter composition. |
| 3 / G46.04 | Open. Environment/balance/metadata instructions need full frame/account and compiler representation agreement, beyond published local environment slices. |
| 3 / G46.05 | Open. Hash-region membership transport is proved below. Actual memory-preimage/cryptographic observation consumers and existing decoder/precompile agreement remain prerequisites. No global injectivity is introduced. |
| 4 / G46.06 | Open. No actual pinned transition/resource adequacy composition. Exact stack, memory, gas, fuel and approved abstraction clauses remain obligations. |
| 4 / G47 | Blocked on integrated V13/V14 interfaces and actual Osaka account execution. CALL/STATICCALL, arbitrary permitted callees, CREATE/initcode, RETURN/REVERT, persistent/transient/balance rollback, transaction validity/upfront fees, precompiles and finite/infinite traces remain unproved. A payment-acceptance Boolean is not substituted. |
| 5 / dependencies | Local availability and an actual failed Azure cache request are recorded below; reference-word imports requested 860 files and downloaded 0 after CONNECT 403 failures. No dependency or toolchain was upgraded. |
| Backfill A | Partial: existing G01 finite-prefix order, consistency, completion and resource-indexed noncompletion observation transport proved. Published assembler/failure/scalar word/byte encoding and inhabited signed/truncation/boundary transport are now proved in recovery; full pinned-reference transition integration remains open; no actual infinite EVM execution is constructed. |
| Backfill B | Partial: approved hash-premise suffix/membership and published local-checkpoint observation/relation transport proved. Published intrinsic world rollback consumers are proved in recovery below; production ledger/nonce/log and bytecode/world composition, actual execution-prefix linkage and application to actual opcode transitions remain open. The secondary obligation checklist is now explicit and tested in recovery; all recorded proofs remain open. |

V11 → V12 → V13 → V14 → V15 → V16 → V17 is still serial for full completion.
This checkout has G01/G06 abstract contracts and component results, not a
published production instantiation of the required whole assembly/world
execution correspondence in the inspected roadmap/Bridge namespaces. The toy
G01 controls do not supply it. Existing scalar, storage/layout/hash, environment,
failure, creation, assembler/control, precompile, stipend and fixed-point owners
retain all their implementations and unfinished parent obligations. Source,
copy-recovery, numeric/memory/slot/control/Widths, decoder/precompile adapters,
frontend/world/transient/panic and generated differential work stay reserved.
No shared prerequisite edit is proposed: the coordinator must integrate the
owners' completed interfaces and the approved Osaka reference implementation.

## Exact theorem boundary

Namespace: `SolidityBridge.RoadmapV15`.

| Declaration | Inputs/premises and result | Axioms |
|---|---|---|
| `mapPrefix_le` | Event/outcome maps and existing `p.Le q`; mapped prefixes preserve that order. | `propext` |
| `mapPrefix_final_none` | Arbitrary maps; mapped final is absent iff original final is absent. | `propext` |
| `mapPrefix_consistent` | Existing resource-indexed family consistency; consistency after observation mapping. | `propext` |
| `mapPrefix_diverges_iff` | Same arbitrary admissibility predicate and family; noncompletion at each admissible bound is equivalent after mapping. No injectivity needed. | `propext` |
| `mapPrefix_completes` | A completed original family; exact mapped outcome completes at the same bound. No reverse completion claim. | `propext` |
| `hashPremise_mono` | One cumulative `HashPremise F runHashes runSlots` and separate membership inclusions for all hashes and slot hashes; the identical approved premise on the selected lists. | none |
| `hashPremise_suffix` | Cumulative premise on concatenated before/transaction lists; premise on the transaction suffix. Separate transaction premises alone do not suffice. | none |
| `checkpoint_relation` | Relation on two existing typed local journals, same `Outcome`, related live journals and related restored snapshots; related `finish` results. | none |
| `checkpoint_observation` | Same outcome and observation maps agreeing on both live and restored snapshots; equality of outcome/observation pairs after `finish`. | none |

`PrefixTransport.lean` and `PremiseTransport.lean` introduce no semantics or
source representation. `mapPrefix` only maps the existing prefix's events and
optional final observation. Neither arbitrary observation maps nor local journal
observations are asserted to be the approved EVM/public observation map.
`Bridge/SolidityBridge/RoadmapV15/Controls.lean` includes nonempty prefixes, exact bytes `[0,255]`, completed versus
noncompleted families, differing persistent/transient snapshots, success commit,
nested rollback, differing-snapshot rejection, cross-transaction collision
rejection and positive/negative root-region controls. These controls do not cover
numeric signedness/truncation or actual EVM call/transaction execution.

## Actual reference and cache availability

Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`;
Lake 5.0.0-src+797c613. The configured executable directory is
`/workspace/.setup/tools/lean-4.24.0-linux/bin`; it was absent from the inherited
shell PATH. No Lean MCP diagnostics or `get_goal` tool is exposed. CLI diagnostics
are used per edited file, without a Lean server. The existing goal is preserved.

The Bridge manifest pins Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`
(v4.24.0), CSLib `e1fea784d55eae30275c205291f12a1b4868eed3` and lean-auto
`36d85bf6372f1a35fb5487325d1ef965b33c6296`. At inspection Mathlib has source
and 5 oleans, CSLib has source and 0 oleans, and lean-auto source is absent.
This initial snapshot was availability evidence only. Recovery later tested the
actual pinned cache endpoint and received CONNECT 403 failures, recorded below.
No external packages were fetched. The small Docker runtime image was fetched separately.

The vendored interpreter still declares `TargetSchedule := "Cancun"` in
`Bridge/vendor/EvmYul/Wheels.lean`. The existing assembler record documents
Osaka CLZ parsing/execution and truncated-PUSH right-padding disagreements.
Its shared arithmetic fragments cannot silently stand for an Osaka transition
or full account/transaction correspondence. This lane may not rewrite the
vendored or reserved reference implementation.

`scripts/roadmap-v15-obligations.py` reads and validates the published backend
opcode table and its bounded-family formulas, then emits 150 individual
byte/mnemonic rows with explicit open primary/secondary obligation clauses.
The recovery section below describes the expanded schema. The original commit's
primary-routing-only schema was insufficient and is retained only in the old
exported artifact. This report is not a semantics, opcode coverage certificate
or decision that every opcode is emitted by the admitted profile. It also lists
the 168 existing G03 feature IDs whose EVM owners include this lane. No global
ledger/manifest was edited. Coordinator reconciliation: attach the backfill and
accounting evidence to G46.05/G46.06/G47, retaining every open proof status.
No feature closes.

## Runtime and checks

Evidence directory: `/workspace/v15-evm-agreement-evidence`.
The VM enclosing cgroup limit is 16 GiB, host swap zero. systemd is not PID 1,
no user bus is configured, and delegated cgroup writes are unavailable.
A task-owned offline Docker container enforces a 12 GiB process-group cap:
`memory.max=12884901888`, `memory.swap.max=0`. It uses the existing checkout,
toolchain and source-keyed artifact cache, `LEAN_NUM_THREADS=1`, explicit Lean
`-j1` and `--tstack=131072`. The external runner samples aggregate Lean/Lake RSS
and retains container peak memory. No other worker was terminated.

| Gate | Result and decisive evidence |
|---|---|
| Base/branch | Clean `work` checkout at exact base before writes; assigned branch created from that commit, ancestry passed. |
| KeySort runtime | PASS: `lake -f .v15-runtime.toml build Solidity.KeySort`, `Build completed successfully (2 jobs).` Peak cgroup 24,694,784 bytes. RUNTIME_GATE_PASS applies only to runtime readiness. |
| Published import closure | PASS: bounded 900-second build of `Solidity.Roadmap.Contracts` and `Solidity.Backend.Failure.Checkpoint`, 8 jobs; peak cgroup 1,248,837,632 bytes. |
| Per-file checks | PASS: both transport modules, serial core-environment Lean CLI checks; peak cgroup 75,309,056 bytes. |
| Controls/axioms | PASS after fixing an explicit nested-checkpoint instantiation; `controls-reviewed.log` contains the final nine axiom reports and direct theorem controls; peak cgroup 82,063,360 bytes. |
| Full/import-closure Bridge gate | Pending. The focused core-environment checks do not validate the registered Bridge umbrella or missing external dependency closure. |
| Full repository gate | Pending; no claim of lane or final gate completion. |
| Layers | PASS: 172 core modules, 0 reach the elaborator. |
| Orphans | PASS: 996 reachable, 0 orphaned, 0 not allowed. |
| Trust | PASS: 1011 sources, 246 inventoried implementation/recovery sites, 0 findings. |
| Docs full checker | FAIL: 46 missing references at current tree and exact base; both raw failures retained. |
| Docs no-new-findings | PASS: 0 new missing-reference findings against exact base; all 14 owned local links resolve. |
| Diff whitespace | PASS: staged diff check. |

Initial failure evidence remains in `keysort-invalid-option.log`, `focused-initial.log`,
`controls.log`, and `inventory-initial-failure.log`. Lake has no `build -j1`
option; explicit `-j1` belongs in the temporary library Lean arguments. First
focused imports were absent, so their actual closure was built before retry.
The KeySort-option and inventory failure files are tool-transcript reconstructions
with explanatory annotations, not raw redirected process logs. The focused and
controls logs are directly redirected raw command output. The controls failure was an underinstantiated use of the existing rollback
lemma, fixed with explicit arguments without changing its statement. The
inventory extractor initially omitted digit-bearing opcode names, then asserted
all 150 distinct bytes successfully. No proof budget was increased.

## Independent reviews and handoff

Independent read-only finder and skeptic reviews found no unsound proof or
forbidden premise. Both requested direct applications of the new transport
theorems; cross-representation checkpoint, prefix completion/consistency and
actual-Keccak repeated-query premise controls were added. The finder requested
exact secondary opcode obligations; primary routing is now explicitly labeled
incomplete. Both identified the assembler link label, corrected here. The skeptic
requested accurate log provenance and saved runtime probes, also addressed.
Separate follow-up finder and skeptic reviews inspected the final staged diff,
hypotheses, non-vacuity and external handoff and found no new defect. Both
cleared only this partial preparation; the results are retained externally. Full lane review remains open
until actual composition, all controls and every required gate pass.

The final external handoff records the exact committed head, original patch,
bundle, command outcomes, absolute artifact paths and checksums. The patch does
not include build trees, external packages or caches. This saved checkpoint is
partial preparation; the persistent goal must be blocked rather than completed
while the prerequisites and obligations above remain missing.


## Initial preparation checkpoint handoff (4511898e)

The initial commit packages partial backfill only; G46.01 is not marked passed and the
work queue has not advanced past its missing actual Osaka prerequisite. Nine
transport theorems are kernel-checked in the core dependency environment, with
explicit premises and scoped axiom output. Independent controls now directly
apply the new checkpoint observation, prefix order/consistency/completion and
cumulative hash-premise transport theorems. No registered full Bridge closure or
whole-lane theorem has been validated. Full/import-closure Bridge and repository
gates, actual pinned-EVM numeric/byte/slot/environment/hash consumers, V13/V14
integration and final finder/skeptic lane reviews remain required.

The next authorized step is to consume the coordinator-integrated production
V13/V14 and Osaka reference interfaces read only, then return to G46.01 and each
subsequent queue checkpoint. This does not authorize rewriting the vendored
Cancun semantics or reserved components. Until those prerequisites are supplied,
the goal is blocked rather than complete. No push, merge or PR was performed.


## Auditor recovery 201ebab8: documentation comparison correction

The earlier no-new-findings comparison considered missing references only. It
missed an owned ambiguous basename citation: the frozen base had 37 ambiguous
findings and the first checkpoint had 38, although both had 46 missing paths.
That historical claim was incomplete. The ambiguous citation now uses the
explicit owned path. Original failing logs and exported artifacts are retained;
new evidence is under `/workspace/v15-evm-agreement-evidence/recovery-201ebab8`.
The recovery comparison checks both missing and ambiguous findings, including
multiplicities, against the exact frozen-base log. The global checker still
fails on inherited missing references; only a separate zero-new-regressions
comparison may pass.


### Recovery checkpoint: secondary opcode accounting

The owned accounting script now records explicit open obligation clauses for each
of the 150 byte/mnemonic pairs, not only a primary group. Common clauses preserve
actual decoding/fork, intrinsic representation, stack capacity/operand order,
resource/fuel/failure and continuation obligations. Secondary clauses cover
word padding, source/destination byte intervals and expansion; calldata/code
zero padding versus returndata bounds failures; RETURN/REVERT extraction before
rollback; persistent/transient paths; account/metadata/static permission;
KECCAK/code hash bytes and approved region premises; call input/output buffers,
actual callee frame execution, forwarded gas/stipend/depth/funds, precompiles,
world rollback/session observations; CREATE initcode/address/hash/result buffer;
LOG and SELFDESTRUCT lifecycle obligations when admitted code emits them.
Every clause remains open. This checklist does not implement transitions, certify
semantics, decide source admission or discharge any G46/G47 proof. All clauses
must be checked against the production Osaka interface when it is published.

`python3 scripts/test-roadmap-v15-obligations.py` passes 12 tests, including
mutations removing rows/secondary clauses, duplicating rows/clauses, swapping
bytes without creating duplicate bytes, and falsely marking a row discharged.
Positive combination controls cover every CALL-family member and distinct copy
source/destination obligations. Documentation regression controls detect new
ambiguities even when missing counts match, and preserve finding multiplicities.
The report also continues to record actual pinned dependency/cache availability.


Recovery accounting reviews: separate read-only finder and skeptic identified
unchecked indexed-family formulas, acceptance of incomplete checker logs and
missing explicit storage-refund accounting. Those are fixed: family shapes and
bounds are validated with drift mutations; both input logs must carry valid
completed checker summaries and recorded exits, with fatal/truncated controls;
SSTORE original/current/new values, warm/cold/refund journals and transient reset
are explicit open clauses. The skeptic also identified the obsolete current
schema description, corrected above. No Lean server or builds were used by
reviewers. Final follow-up results are retained in the new evidence directory.

Separate follow-up finder and skeptic reviews cleared this documentation/accounting
checkpoint after inspecting the actual staged diff and evidence. All 12 script
tests pass; the corrected complete-log comparison has zero added missing or
ambiguous findings. G46/G47 semantic obligations and final gates remain open.


## Recovery checkpoint: word/byte and cumulative consumers

New owned modules consume existing definitions without editing reserved code:
`Bridge/SolidityBridge/RoadmapV15/WordByteTransport.lean`,
`Bridge/SolidityBridge/RoadmapV15/CumulativeTransport.lean` and
`Bridge/SolidityBridge/RoadmapV15/ConsumerControls.lean`.
The core still imports no Bridge module. Only Bridge/module-map append-only
registration changes accompany these new modules.

### Exact statements and premises

All names below are in `SolidityBridge.RoadmapV15`.

| Theorem | Exact consumer contract/premises |
|---|---|
| `digits_toBytesBE` | Existing failure digits equal existing assembler vector bytes, for every length and number. No bound or implicit padding. |
| `readImmediate_ofBytesBE` | Existing failure and assembler byte readers are identical. |
| `keccak_ofBytesBE` | The existing Keccak Nat-byte reader on mapped UInt8 bytes equals the assembler reader; this is byte-integer conversion, not hash equality/injectivity. |
| `encoded_bytes_injective` | Equal encoded bytes at the same explicit width imply equal input numbers, with both numbers below 256^width. |
| `pushed_immediate_toNat` | Existing scalar BitVec and failure-slice Fin immediate readers have equal Nat observations on every byte list. |
| `word32_immediate`, `word32_pushed` | Full 32-byte assembler encoding round-trips an existing 256-bit word through those existing readers. |
| `bounded_immediate` | Width <=32 and number <256^width yield exact numeric decoding; no truncated-code or implicit-pad claim. |
| `signed_word_bytes`, `unsigned_word_bytes` | Existing intrinsic int/uint value encoding, 32-byte representation and scalar reader retain the original signed/unsigned value; reuse the published typed encoding theorems. |
| `typed_bytes_toWord` | Scalar encoding bytes equal bytes of the existing intrinsic ABI-word observation, consuming `Scalar.encodeValue_toWord` unchanged. |
| `word32_bytes_injective` | Equal full-width byte observations imply equality of existing words; consume `word32_immediate`. |
| `unsigned_cleanup_bytes`, `signed_cleanup_bytes` | Compose published local width-cleanup code/proof with explicit word bytes, preserving arbitrary stack tail. No actual gas/resource simulation is supplied. |
| `written_immediate_bytes`, `written_immediate_suffix` | Existing local byte writes/readback observe exactly the encoded interval; a suffix written after it cannot become padding inside it. Reuse the published byte-memory lemmas unchanged. |
| `hashPremise_append_iff` | Exactly equivalently decompose the approved cumulative HashPremise into two component premises plus its cross-preimage CollisionFree clause and cross-region non-overlap clause. Same Fixed/hash/region length/roots throughout; repeats allowed. |
| `hashPremise_append_comm` | Query-list segment permutation transports the same approved premise; no assertion that executions commute. |
| `checkpoint_relation_nested` | Compose existing local finish/restore under arbitrary inner/outer outcomes, given related live state and both related restored snapshots. No world/nonce/log/balance preservation is inferred. |

The first sixteen word/byte theorems and three cumulative/checkpoint theorems
have scoped axiom output in `consumers-final.log`. The only axioms reported are
Lean's `propext`, `Classical.choice` and `Quot.sound`, in the exact subsets shown
there; there is no new axiom, sorry, native-decide or implementation hook.
The new numeric statements are consequences of the existing local scalar and
failure slices, not direct EVMYul dispatch agreements. The reserved external
`Solidity.Evm.External.encode`/`decode` and arithmetic/Widths/byte-memory adapters
remain unchanged. The vendored full reference still declares Cancun; this work
does not resolve CLZ, truncated-PUSH behavior, gas/fuel or full Osaka execution.

Actual EVM consumers must still establish selected input/output intervals,
compiler representation and padding, 160-bit account correspondence, stack
bounds, memory expansion, exact gas/failure and fuel-prefix clauses. Local
Nat-addressed memory laws are not an assertion of resource adequacy. The
cumulative equivalence only re-expresses the approved premise: individual
transaction premises alone still do not suffice. Linking recorded query lists
to actual production prefixes, and transaction/nonce/log rollback, remains with
the production interfaces and is not replaced by local journals.

### Controls and bounded checks

Controls directly apply the new consequences to nonempty `[1,2]` encodings,
nonzero words, maximum uint256, signed -1/minimum/maximum int256, 8-bit unsigned
truncation (257 to 1), sign boundaries 127/128/255, framed stack tails, byte
endianness, zero-width/empty encoding, wrong offset, insufficient-width loss and
the difference between `[1]` and right-padded `[1,0]`. A real-Keccak sane fixture
with nonempty repeated preimages inhabits the cumulative equivalence. Negative
controls separately show that two collision-free singleton segments can collide
when joined and that distinct collision-free hashes can have overlapping
positive-length regions. Arbitrary nested success/revert outcomes transport
observations across distinct local journal representations; wrong restored
snapshots remain distinguishable.

The published prerequisite closure (`Scalar.Widths`, `Scalar.Typed`,
`Failure.Immediate`) passed 23 build jobs under the existing serial cap,
peak cgroup 587,501,568 bytes. Per-file focused checks pass. Initial controls hit
unchanged heartbeat/recursion limits while elaborating large definitional
normalizations; explicit published rewrite lemmas and Nat-to-Int casts removed
that work, without increasing any budget or weakening any boundary. Original
failures remain in `word-bytes-initial.log` and `consumer-controls-initial.log`.
The final control/axiom command passed, peak cgroup 224,301,056 bytes, before the
two trivial empty-encoding controls were added; final validation is recorded
separately below. Full Bridge/default/TestSuite gates remain distinct obligations.


### Recovery cache gate and review fixes

The existing pinned Mathlib cache executable was invoked for the exact eleven
Mathlib imports of the vendored `EvmYul.UInt256` module, using current source
paths and the existing source/toolchain cache. Under the same 12 GiB/no-swap
cap, normal configured Docker proxy and verified TLS trust, it requested 860
cache files: **0 downloaded, 860 failed**, exit 1, with `CONNECT tunnel failed,
response 403`. Raw output is `reference-cache.log`; command, duration and RSS
are in `reference-cache.json`. A separate lightweight host request to the same
Azure endpoint also failed CONNECT 403 (`http_code=000`), confirming the error
is not specific to the inner container. Runtime status still reported connected
and enforced policy; that status did not establish successful endpoint access.
No proxy bypass, alternate fork, upgrade, vendor edit or unmerged prerequisite
fetch was attempted. The unchanged failed cache gate will not be repeated.

The precise cache-dependent closure remains `EvmYul.UInt256` and the existing
external `encode`/`decode`/numeric adapters; its Mathlib oleans are not available.
CSLib has no built oleans and configured lean-auto source remains absent.
Full Bridge execution/import confirmation remains pending. Independently, a
production Osaka `Roadmap.Evm.Pinned`/`Certificate` and V13/V14 assembly/world
interfaces are required before G46/G47 can close. The current vendor pin is
Cancun, not a proof of `Certificate.pin` at the approved Osaka pin. These are
separate blockers; restoring cache access alone would not close the lane.

Both proof reviewers found no soundness, premise or ownership defect. They
requested a genuinely distinct-preimage cumulative positive, nontrivial query
segment permutation and direct cross-region failure through the equivalence.
Those controls now use explicitly labeled non-production Fixed fixtures with
two-slot regions at 4 and 8 (disjoint), or 4 and 5 (overlapping), with one root
at 0. They instantiate the exact generic approved premise shape, without any
claim that these fixtures compute Keccak. The separate actual-Keccak repeated
query fixture remains. An inhabited intrinsic maximum uint256 now directly
uses `unsigned_word_bytes`. The appended module-map table formatting is fixed.
The reviewed control/axiom check passed at peak cgroup 160,821,248 bytes; all
nineteen scoped axiom reports are retained in `consumer-controls-reviewed.log`.


### Reviewed consumer checkpoint and repository cold gate

Separate follow-up finder and skeptic reviews cleared both the word/byte and
cumulative/checkpoint areas after inspecting the actual diff, hypotheses,
non-vacuity and evidence. The final owned six-module import closure passed,
including all original nine and new nineteen scoped axiom reports. Peak cgroup
224,215,040 bytes. Structural/layer/orphan/trust and 12 accounting tests passed.
The full documentation checker still exits 1 with the same 46 missing and 37
ambiguous findings as exact base; complete-log comparison reports zero added
findings of either class, with multiplicities retained.

One cold repository command, `timeout 5400 ./run-lean.sh`, **failed with exit
124 at its unchanged outer guard**, after 806/981 reported default-build jobs.
TestSuite and sort-check phases were not reached. The log contains no Lean
error marker before termination; it is nevertheless a failed gate, never a
passing build. Raw output and metadata are `repository-gate.log` and
`repository-gate.json`. Peak process-group cgroup memory 12,652,908,544 bytes;
sampled aggregate Lean/Lake RSS 9,693,794,304 bytes; swap cap 0. The 12 GiB cap
was not increased. Successful source/toolchain-keyed cache artifacts are kept;
no duplicate build tree was made. No unchanged broad heavy gate was repeated.

Exact-base comparison (`core-input-base-comparison.log`) verifies that core
Lean sources, root imports/executables, Lake/toolchain/run scripts and the listed
AST/sort fixtures are byte-identical to the frozen base. This identifies the
cold check's unchanged inputs; it is not a baseline runtime result and does not
waive the timeout or mark the mandatory gate green. Remaining bounded targets
and full Bridge confirmation are still open.

QNET1 was answered: the human authorized restoring normal access to the existing
configured Azure endpoint and then rechecking the pinned cache. Available Cloud
Environment tools expose status/diagnostics only, with no configuration setter;
diagnostic metadata returned no records. Restoration was not applied by this
worker. A later lightweight authorized probe still returned CONNECT 403, with
runtime specification revision 1 unchanged. The authorization persists; a runtime
owner must repair actual endpoint access before another heavy cache request.
No new VM, package/fork switch, proxy bypass or additional permission is sought.


## Recovery checkpoint: published world and transaction API consumers

The frozen base already publishes partial intrinsic world APIs in
`Solidity/Semantics/ContractWorldCertificates.lean` and
`Solidity/Semantics/TransientWorld.lean`. These were consumed READ ONLY after
inspection, rather than treating every world component as missing. They are not
the missing production V13/V14 assembly/world correspondence: their own contract
retains supplied Entry/Library bodies, external-response tables, source admission
and opt-in transaction selection. They have typed accounts/storage, funds,
timestamp and code roles, with a logical transient-region boundary; they do not
provide nonce/log state or the full Osaka account/transaction semantics.

New `Bridge/SolidityBridge/RoadmapV15/PublishedWorldTransport.lean` contains only
consequences of those existing definitions/results and the owned word-byte law.
No new World, Operation, interpreter, source IR or payment-acceptance oracle is
defined. Its exact nine declarations (same V15 namespace) are:

| Theorem | Exact premises and conclusion |
|---|---|
| `world_failure_balance_bytes` | An actual frame errors at w.resetTransient; the failed boundary retains the original world's exact 32-byte intrinsic balance observations. |
| `world_failure_accounts` | Same actual failure evidence; accounts are the original accounts mapped through the published storage transient reset, not falsely equated to arbitrary unnormalized input stores. |
| `world_sequence_failure` | Actual first.run w = ok mid and second.run mid = error e; the existing sequence errors with exactly e. |
| `world_transaction_prefix_failure` | Actual first.run w.resetTransient = ok mid and result-valued tail mid = error e; the existing outer boundary returns w.resetTransient with the exact halt e. |
| `world_transaction_prefix_success` | The same actual prefix and successful result-valued suffix; commits next.resetTransient and the exact returned value. The suffix receives mid, never mid.resetTransient. |
| `world_operation_transaction_failure` | The same two operation-run premises at the normalized entry; the existing operation transaction returns the normalized input and unchanged halt. Exhaustion/divergence are not converted to completed steps. |
| `world_failure_persistent` | Actual frame failure plus an intrinsic SRef whose root is not declared transient; persistent path observations equal the input world's observations. Transient roots are expressly not covered by that preservation premise. |
| `world_caught_creation_tail` | Mutable context, actual creation error and the owner's catchable=true condition; the suffix resumes at the exact creation input world, which may already include a paid caller prefix. |
| `world_argument_failure_tail` | A supplied argument-evaluation error stays outside the creation catch and prevents the suffix, preserving all halt/revert data. |

No admission, execution or representation premise is silently discharged. The
nine new scoped axiom reports in `world-controls-initial.log` contain only the
standard Lean axioms in their reported subsets. All statements pass focused
kernel checking. The initial syntax error used Lean's reserved keyword prefix
as a binder; renaming the binder fixed it with no statement or budget change,
and `world-initial.log` is retained.

`Bridge/SolidityBridge/RoadmapV15/PublishedWorldControls.lean` reuses the old
owner's actual successful funded factory run, unchanged. Controls prove its
prefix installs code and changes balances before a later failure, and apply
the new sequence/transaction laws to restore the proper entry observations.
They retain nonempty returned/revert bytes, preserve a persistent path in an
actually installed account, and use a real creation collision in that world to
inhabit the creation-catch law. Argument revert/exhaustion propagates outside
the catch; exhausted/diverging halts are not catchable. The persistent-path
condition is unavailable for the published scratch transient root. The failed
suffix uses the existing guard operation as a test failure, not as an oracle
for whether a callee accepts payment. No reserved test program is rewritten.
Peak cgroup in the initial world consumer/control check: 173,264,896 bytes.

Full EVM nonce/log/transient numeric-slot correspondence, permitted arbitrary
callees, exact resources and source/bytecode/Bridge trace linkage are still open.
These stronger available component laws do not close G46, G47 or the lane.


Published-world reviews: both independent read-only reviewers found no theorem,
premise or ownership defect, but identified a genuine control gap: the original
factory has no transient declarations. Stronger controls now create a typed owner
from the published transient Cell, run an actual Entry body that writes scratch
17 and persistent saved 23, and feed its actual successful intermediate world
to a result-valued suffix. That suffix reads scratch 17 through the published
SVal.beq fold. A prematurely normalized intermediate world observes false,
so it cannot satisfy the tested success/failure suffix premises. Direct
applications of both prefix consumers pass. Outer success clears scratch but
retains saved 23; outer failure returns the original normalized world. A second
failure begins from the occupied non-normalized intermediate account, directly
uses world_failure_accounts, and proves the mapped normalized account differs
from its raw input while saved 23 survives. No indexed-family matcher, new
storage/world interpreter or callee-payment Boolean was added. The balance-byte
docstring now accurately limits its conclusion to balance bytes; exact halts
are stated by the separate result theorem.

The initial additional control used an unavailable simplification lemma; the
actual reduction rule fixed it without budget changes. Raw failure and corrected
pass are world-transient-controls.log and world-transient-controls-fixed.log.
The corrected check includes all nine axiom reports, peak cgroup 185,012,224
bytes. Follow-up review results and final import/structural/doc checks are retained
with the handoff; full lane obligations remain open.

World checkpoint handoff: separate follow-up finder and skeptic cleared the corrected actual transient-owner controls and nine conditional consumer laws. Final focused owned closure passed (world-reviewed-closure.log, peak cgroup 200,577,024 bytes). Structural, trust, orphan and whitespace checks pass; full docs still fails with 46 missing/37 ambiguous, with zero added findings against exact base. The wider core import closure is running, not counted passed; cold full timeout and full Bridge/cache/Osaka/V13/V14 prerequisites remain open. Evidence is /workspace/v15-evm-agreement-evidence/recovery-201ebab8; exact committed-head patch/bundle/handoff will be exported under /workspace/v15-evm-agreement-artifacts/recovery-201ebab8. Final finder identified one further available G06 halt-observation consumer, retained as the next Backfill A checkpoint.
