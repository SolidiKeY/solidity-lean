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
| 2 / G46.02 | Open. Published memory sources are now incorporated read only; a pure reference encoding consumer source proposal is prepared, but local kernel validation is cache-blocked. Actual pinned transition, conditional serialization, padding, driver and exact expansion/resource clauses remain open. |
| 2 / G46.03 | Open. Persistent/transient numeric-slot consumers still need symbolic-path representation, approved per-run region premise and published slot adapter composition. |
| 3 / G46.04 | Open. Environment/balance/metadata instructions need full frame/account and compiler representation agreement, beyond published local environment slices. |
| 3 / G46.05 | Open. Hash-region membership transport is proved below. Actual memory-preimage/cryptographic observation consumers and existing decoder/precompile agreement remain prerequisites. No global injectivity is introduced. |
| 4 / G46.06 | Open. No actual pinned transition/resource adequacy composition. Exact stack, memory, gas, fuel and approved abstraction clauses remain obligations. |
| 4 / G47 | Blocked on integrated V13/V14 interfaces and actual Osaka account execution. CALL/STATICCALL, arbitrary permitted callees, CREATE/initcode, RETURN/REVERT, persistent/transient/balance rollback, transaction validity/upfront fees, precompiles and finite/infinite traces remain unproved. A payment-acceptance Boolean is not substituted. |
| 5 / dependencies | Local availability and an actual failed Azure cache request are recorded below; reference-word imports requested 860 files and downloaded 0 after CONNECT 403 failures. No dependency or toolchain was upgraded. |
| Backfill A | Partial: existing G01 finite-prefix order, consistency, completion and resource-indexed noncompletion observation transport proved. Published assembler/failure/scalar word/byte encoding and inhabited signed/truncation/boundary transport are now proved in recovery; exact G06 completed-halt observations now instantiate finite-prefix transport below; full pinned-reference transition integration remains open; no actual infinite EVM execution is constructed. |
| Backfill B | Partial: approved hash-premise suffix/membership and published local-checkpoint observation/relation transport proved. Published intrinsic world rollback consumers are proved in recovery below; production ledger/nonce/log and bytecode/world composition, actual execution-prefix linkage and application to actual opcode transitions remain open. The secondary obligation checklist is now explicit and tested in recovery; all opcode semantic discharge obligations remain open. |

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
That initial inspection did not fetch external packages. Its auto-source-absent
statement is historical, not the current availability result below. The small
Docker runtime image was fetched separately.

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

## Initial preparation runtime and checks (4511898e)

This historical table predates the recovery checks below; it does not report the
current full-gate outcome. The recovery retains the raw cold full-gate timeout
and compares both missing and ambiguous documentation findings.

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
The final actual package check confirms source repositories for CSLib, lean-auto
and Mathlib at their configured revisions: respectively 0, 0 and 5 oleans.
Lean-auto source is present now; the initial absence snapshot is not current.
actual-package-heads.log verifies each actual git root and exact pinned HEAD.
No package revision or toolchain was upgraded.
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


## Recovery checkpoint: exact G06 halt observation consumer

The final finder identified one further independently available Backfill A item:
consume the published G06 Halt.observe instead of leaving prefix maps entirely
arbitrary. The new owned modules are
`Bridge/SolidityBridge/RoadmapV15/HaltObservation.lean` and
`Bridge/SolidityBridge/RoadmapV15/HaltObservationControls.lean`.
They depend only on published core definitions and the owned prefix transport.
The existing G06 observer fixes the Bool and all return/revert bytes; the new
conversion and its canonical representative introduce no execution semantics.

| Declaration | Exact premise/result boundary |
|---|---|
| `outcomeOfHalt_section` | Every existing Outcome round trips through its canonical completed-halt representative. |
| `haltOfOutcome_observe` | Every G06 halt retains its exact existing Bool/byte observation after conversion and canonicalization. |
| `outcomeOfHalt_eq_iff` | Two converted Outcomes are equal iff their existing G06 observations are equal; no further observation is discarded. |
| `outcomeOfHalt_success_iff` | Success with exact bytes d iff the original halt is success d, consuming the owner's success characterization. |
| `outcomeOfHalt_revert_iff` | Failure with exact d iff original revert d, or exceptional with d empty; equality of halt constructors is not asserted. |
| `input_halt_payload` | Every published failure/return Input retains its existing bytes, including the owner's panic/reason encoders unchanged. |
| `input_halt_terminal` | Its canonical observation's success bit agrees with the actual existing Input terminal's RETURN-versus-other classification. |
| `halt_prefix_completed` | Given p.final = some h, conversion retains every existing Event and the exact converted final payload. No execution/consistency premise is fabricated. |
| `finite_intrinsic_halt_observation` | Requires the owner's inputOfResult t = some i; its existing ResultObserves proof transports through the canonical observer round trip. No EVM dispatch witness is inferred. |

Controls use nonempty success/revert data, wrong-byte and success-bit negatives,
exceptional versus nonempty revert, distinct exceptional/empty-revert halt
constructors, exact panic/custom payloads, and the owner's rejection of exhausted
or diverging intrinsic results. A nonempty concrete G01 call/answer prefix and
resource-indexed proper extension instantiate the existing finite completion,
consistency and noncompletion transports with the same admissibility predicate.
These are observation fixtures, not actual finite/infinite EVM executions.
Separate static finder and skeptic reviews found no premise, observation or
ownership defect. Focused kernel/control checks pass in halt-fixed.log with all
nine axiom reports (only propext/Quot.sound where used; other reports have no
axioms), peak cgroup 163,303,424 bytes. An ambiguous empty-list type in one
control was fixed with an explicit Bytes annotation, without statement or budget
changes; halt-initial.log retains the raw failure. The noncompletion predicate
also has an explicit positive resource witness. Follow-up review and full owned
closure results are recorded with the final handoff.

The reference encoding obligation remains exact and open: published EvmYul
fromBytesBigEndian/fromByteArrayBigEndian and uInt256OfByteArray must be related
to the existing compiler big-endian readers, and the reverse of EvmYul toBytes!
(which is little-endian and right-padded) must agree with the exact 32-byte
compiler encoding. Width, length, truncation/modulo and padding clauses cannot
be omitted. These declarations live in the unchanged pinned reference word
module, whose existing Mathlib import closure is cache-blocked (860 requested,
0 downloaded, CONNECT 403). The available core encoder/reader consumers above
are proved separately; neither these pending reference equations nor Osaka
transition correspondence is silently counted discharged.

The separate pending core import-closure target now passed: timeout 5400 lake build +Solidity, 970 jobs in 4,921.916 seconds, peak cgroup 9,834,909,696 bytes and sampled aggregate Lean/Lake RSS 9,214,480,384 bytes, swap cap 0. This does not relabel the earlier failed cold full command or validate the external Bridge umbrella. TestSuite/native/sort phases remain separately accountable. The latest lightweight authorized endpoint probe still fails CONNECT 403 (curl exit 56); cache-host-probe-final.log retains the raw result.

Halt checkpoint handoff: independent follow-up finder and skeptic cleared the actual staged proofs, hypotheses, inhabited/negative controls, ownership and evidence. All ten owned modules and their import closure pass in owned-final-closure.log, including all 46 scoped axiom reports; peak cgroup 224,415,744 bytes. The layer/orphan/trust/owned-structural/whitespace gates pass. Raw docs still fails with 46 missing and 37 ambiguous findings; halt-docs-comparison.json reports zero additions of either class, with multiplicities. All 150 opcode rows retain open obligations and empty dischargedByV15. The temporary runtime configuration is removed before this commit. Exact-head exports and final remaining-phase results belong in /workspace/v15-evm-agreement-artifacts/recovery-201ebab8; raw recovery evidence remains /workspace/v15-evm-agreement-evidence/recovery-201ebab8. G46/G47 and the full lane remain unfinished.


## Final recovery validation and handoff

The original cold full command remains **failed**: exit 124 at its unchanged
5,400-second outer guard, 806/981 jobs, raw repository-gate.log/json. No unchanged
broad full command was repeated or relabeled green. The previously unchecked
constituents were then checked separately with the populated single cache:

| Command | Actual outcome and decisive output |
|---|---|
| timeout 5400 lake build +Solidity | PASS, 970 jobs, 4,921.916 s; cgroup peak 9,834,909,696 bytes, aggregate sampled Lean/Lake RSS 9,214,480,384 bytes. |
| timeout 900 lake build solkeycheck solidity-lean | PASS, 15 jobs, 1.638 s; cgroup peak 27,009,024 bytes. |
| timeout 5400 lake build SolkeyTestSuite | PASS, 262 jobs, 1,158.520 s; cgroup peak 11,458,535,424 bytes, aggregate sampled Lean/Lake RSS 11,857,256,448 bytes. Existing source profile, skips, exclusion and pins unchanged. |
| timeout 900 ./scripts/check-solkey.sh | PASS: parsed 377 taclets, 131 read-bearing, table covers 131; annotations match the actual configured SolKey rules file. Cgroup peak 379,105,280 bytes. |
| Existing vendor SHA256SUMS checks (EvmYul, Loom, CaseStudies) | PASS, without changing any vendor or pin. This integrity result does not turn the Cancun reference into Osaka. |

The separate passing stages do not retroactively pass the timed-out cold full
command. LEAN_NUM_THREADS=1 and explicit Lean -j1 stayed in force. All heavy
checks were serial, with a 12 GiB hard cgroup limit and swap limit 0, leaving the
16 GiB task cgroup headroom for the OS. No proof, fuel, node, process or TestSuite
budget was increased. The temporary runtime TOML is removed, its exact effective
contents retained externally. The actual Lean/Lake versions and passing KeySort
runtime output are retained in prior-runtime-probes.log and prior-keysort.log.

The owned ten-module closure and all 46 scoped public consumer axiom reports pass;
only subsets of propext, Classical.choice and Quot.sound occur. The local
accounting tests pass all 12 tests, the fresh manifest lists all 150 byte-distinct
rows with open secondary obligations and empty dischargedByV15, and ownership,
append-only registration, layer, orphan, trust and whitespace checks pass.
The raw documentation checker still fails with 46 missing and 37 ambiguous
findings, matching exact base with multiplicities; the separate complete-log
no-new-findings comparison passes. Raw base/current failures, including the
initial extra ambiguity, remain retained. The global checker is not passed.

Full external Bridge confirmation is pending. The native pinned cache request
failed (0/860 downloads, CONNECT 403), and the latest normal-route lightweight
probe still fails (curl exit 56). Human authorization to restore the existing endpoint
persists; exposed runtime tools have no configuration setter and no restoration
was applied. Actual pinned package/source/cache availability is recorded in
handoff-obligations.json. No upgrade, alternate fork, new VM, proxy bypass,
unmerged worker fetch, reserved edit or extra premise was used.

All queue items G46.01 through G46.06 and G47 remain open/blocked. Backfills A/B
are partial at the lane boundary: the available core encoding, completed-halt,
prefix, cumulative-region and published-world consumers are kernel checked,
but reference-word equations and actual Osaka instruction/memory/slot/environment/
hash execution, resource adequacy, V13/V14 production composition, arbitrary
permitted callees, nonce/log/fee rollback and finite/infinite EVM traces remain
unproved. No local journal or payment Boolean supplies these missing facts.
No bounded external EVM/compiler differential test was run. Kernel component
proofs, core TestSuite/profile checks, static obligation accounting and actual
external machine correspondence are distinct evidence.

Coordinator reconciliation: keep G46.01, G46.02, G46.03, G46.04, G46.05, G46.06
and G47 open; link only the scoped component evidence, without promoting parent
status. Exact affected feature IDs are listed in the fresh manifest's
coordinatorFeatureIds field. No generated G03 ledger, global coverage, manifest,
TrustAudit pin, SolKey name or source admission rule was edited. No reserved
patch is needed for the new checked laws; missing reference/cache/production
interfaces remain publication/infrastructure prerequisites for subsequent work.

The recovery exports are located under
/workspace/v15-evm-agreement-artifacts/recovery-201ebab8: original.patch (full
frozen-base diff), recovery.patch (since 4511898e), v15.bundle, owning-document
snapshot, exact committed-head handoff.md/json, evidence.tar.gz and SHA256SUMS.
Raw evidence is /workspace/v15-evm-agreement-evidence/recovery-201ebab8. Original
checkpoint artifacts and raw failures remain intact in their original parent
directories. The final handoff records the full actual committed head/base,
branch and repository, exact commands/outcomes, theorem statements/premises,
review results, proof/testing boundaries and unfinished work. This checkpoint
and its report do not mark the persistent full assignment complete.

Separate final read-only finder and skeptic reviews cleared the validation/handoff section and actual component diff, retaining full-lane incompleteness. A fresh availability check corrected stale historical lean-auto wording: all three actual source repository HEADs match their configured pins, with CSLib/auto/Mathlib olean counts 0/0/5. Both follow-ups cleared that correction. Actual exported-artifact/head/checksum review is retained externally after export; no Lean server or builds were used by reviewers.


## Publication recovery 7499c0a3: read-only memory producers

The origin master observation is 93920309f5c800c9ce4809bc74700ed4fde65fb2.
The audited previous owned checkpoint is 6ef28db20af0a73597e492bb1e5555f95440856c;
the frozen base and assigned branch are unchanged. The actual local remote ref
was older, so the exact genuine published commit was fetched from configured
origin, with its remote-master observation and incorporated ancestry retained.
No master merge or unmerged worker fetch was performed. Only the four published
memory source blobs are incorporated, byte-for-byte, with append-only Bridge
and module-map registration. No core, vendor, dependency/toolchain pin, source
profile or other owner's implementation is edited. Other published core/editor/
CI/document changes are not part of this selective producer consumption.

`Bridge/SolidityBridge/ExternalEvm/MemoryBytes.lean` publishes encoding_spec:
for every actual EvmYul.UInt256, pure encoding has exactly 32 bytes and the actual
fromByteArrayBigEndian reader returns its toNat. This theorem has **no
PaddingCorrect premise**. The bytes_list/list_bytes laws are also available as
source. In contrast, serialize_eq/serialize, readback/store/refinement and
composition retain explicit allocator and preallocated-capacity conditions.
PaddingCorrect has no published inhabitant and is not assumed or axiomatized by
V15. Represents covers preallocated numeric cells; the supplied-opcode runner
charges zero gas and proves neither fetched-bytecode/driver adequacy nor Osaka,
resource, arbitrary-account or transaction correspondence.

Exact source blob identities and publication/ancestry evidence are retained at
/workspace/v15-evm-agreement-evidence/publication-7499c0a3. Existing sealed exports
and every historical failed gate remain unchanged. Narrow external import/cache
availability and the owned encoding consumer are assessed in this recovery;
publication alone does not claim a new kernel or full Bridge pass. No cache
fetch, CONNECT probe, giant cold external closure or failed full gate is repeated.

The first offline per-file producer check (producer-import.log/json) fails before elaboration: unknown module prefix EvmYul. No newly published producer is kernel-checked in this VM. Current total .olean counts are Mathlib/CSLib/auto 6/0/1; library-output counts are 5/0/0, with the Mathlib five belonging only to its cache tool. Configuration oleans do not supply the missing EVM/Mathlib closure. The bounded process cap is 12 GiB with swap 0; peak for this failed narrow check is 60,473,344 bytes. The existing cache 0/860 CONNECT403 failure and original cold full exit124 remain retained, not rerun or waived. The exact checked Core byte-encoding helpers and candidate reference consumer are the next assigned Backfill A work.

Producer checkpoint handoff: separate independent read-only finder and skeptic verified all four source blobs against the genuine published commit, its frozen-base ancestry, append-only registration, exact hypothesis/driver boundaries and the actual failed import. Both clear source-only incorporation, not kernel compatibility or lane completion. Layer/whitespace checks pass; raw docs still exits 1 with the same 46 missing/37 ambiguous findings and zero additions in the separate exact-base comparison. Source publication does not resolve the authorized but still unperformed cache endpoint repair. The next checkpoint continues the original Backfill A encoding consumer, rather than ending at this source-only checkpoint.


## Publication consumer checkpoint: exact bytes and explicit kernel boundary

The new `Bridge/SolidityBridge/RoadmapV15/EncodingUniqueness.lean` proves four
source-independent consumer laws over the existing Backend encoder/reader:

| Checked declaration | Exact statement boundary |
|---|---|
| bytes_encoding_roundtrip | Every List UInt8 is exactly reconstructed by toBytesBE at its original length after ofBytesBE, including leading zeroes. |
| bytes_value_bound | Every such list decodes below 256^length. No word-width/modulo premise is silently added. |
| bytes_eq_of_length_read | Equal lengths AND equal decoded naturals imply equality of complete ordered bytes. Omitting length is false. |
| bytes_canonical | A producer's exact width and decoded-value clauses determine its entire ordered encoding, not just a numeric projection. |

All four pass per-file kernel checks and print only propext/Quot.sound.
`Bridge/SolidityBridge/RoadmapV15/EncodingUniquenessControls.lean` passes with
nonempty/nonzero distinct words 258/513, leading zeroes, wrong endian and length,
right-versus-left padding, signed -1/minimum, unsigned maximum, narrow unsigned
257-to1/signed128-to-128 cleanup, full-word wrapping and preserved word order.
Existing G06 success/revert observations keep their bit and every payload byte.
The previous 46 checked consumer laws and all earlier controls remain unchanged;
there are now 50 locally checked public consumer laws, not 65.

`Bridge/SolidityBridge/RoadmapV15/ReferenceEncoding.lean` and
`Bridge/SolidityBridge/RoadmapV15/ReferenceEncodingControls.lean` are complete
source proposals with **15 reference declarations NOT locally kernel-checked**.
The failed producer import prevents their elaboration; their axiom reports and
reference-specific controls are pending, not passed. No alternate cache fetch,
endpoint probe, cold external closure, synthetic reference semantics or driver
was used to bypass that blocker. Source-only static review cannot replace it.
Their actual intended cross-representation result is full ordered-list AND
ByteArray equality between the published pure encoding and Backend.toBytesBE32,
proved in source from encoding_spec plus the checked bytes_canonical consumer.
The existing reserved External.encode/decode numeric adapters are reused unchanged.
No allocator hypothesis is introduced and no conditional serialize_eq result is
used. UInt256.ofNat inputs retain the explicit modulo 2^256 clause.

The exact pending declarations are reference_big_reader, reference_array_reader,
reference_encoding_bytes, reference_encoding_array, reference_encoding_scalar,
reference_encoding_nat_modulo, reference_encoding_injective,
reference_scalar_immediate, reference_signed_observation,
reference_unsigned_observation, reference_typed_abi_bytes,
reference_unsigned_cleanup, reference_signed_cleanup,
reference_encoding_sequence and reference_complete_observation.
They preserve signed/unsigned scalar and typed ABI representation, stack tails,
full ordered byte sequences and existing completed-frame success/revert observers.
Encoding injectivity is a finite word-encoding fact, never hash injectivity.
No actual reference instruction execution, fetched-bytecode driver, gas/resource,
account-world, CALL/CREATE/transaction or finite/infinite trace proof follows.

The new scripts/roadmap-v15-memory-publication.py source-boundary report verifies
all four exact publication blobs and distinguishes unconditional pure encoding
from allocator-conditioned serialization/read/store results, preallocated numeric
representation, and supplied zero-charge opcode execution. Its 18 mutation tests
reject source drift, missing modules, added pure-encoding hypotheses, omitted or
wrong allocator clauses, weakened capacity, changed runner scope, weakened full
bytes, invented witnesses, missing/duplicate consumers/conditional rows and false
kernel/driver/Osaka/transaction promotion. This is structural accounting, not a
semantics or proof certificate. All 15 reference rows explicitly remain pending.
Existing 150 opcode obligation rows remain open; no status is promoted.

Focused failures are retained: the first owned import needed a unified namespace
cache index (symlinks to unchanged previous outputs, no copied old cache); new
proof normalization needed explicit dependent-length transport and the actual
implicit length_reverse argument; a uint control initially used an arithmetic
Prop instead of the intrinsic Boolean inRange=true. All were fixed without
changing public statements, definitions or heartbeat/recursion/time budgets.
Actual passing evidence is uniqueness-checked.log and uniqueness-controls-checked.log;
uniqueness-final.log is an earlier FAILED attempt and is not relabeled green.
Source-boundary tests pass 18/18 in memory-boundary-tests-reviewed.log. The actual
producer import remains failed in producer-import.log, and the full registered
Bridge gate is pending. The old full 5400-second exit124 and cache 860/403 failure
remain sealed historical failures, not rerun. Independent reviews and final
publication-specific export paths are recorded at checkpoint completion below.

Consumer review finding: the skeptic observed that text-mode file loading could normalize CRLF and mask published-byte drift. The source loader now decodes raw bytes without newline translation, and a temporary-fixture CRLF mutation test exercises actual loading and rejects that drift. The real four producer files remain exact published blobs. The checked Core laws are unchanged; the reference-specific source remains uncompiled, including all axiom/control requests.

Consumer checkpoint handoff: separate independent read-only finder and skeptic
inspected the actual source, hypotheses, non-vacuity, negative/combination
controls, publisher identity and kernel/source-only status split. Both cleared
the four checked laws and static proposals, with all fifteen reference laws
still uncompiled. The confirmed CRLF provenance finding was fixed and both
follow-ups cleared the raw-loading control. New core closure passes in
checked-encoding-closure.log; four axiom reports pass in
uniqueness-controls-checked.log (peak cgroup 179,539,968 bytes). All 18 boundary
tests pass; all fifteen reference rows remain pending. Layer/orphan/trust,
append-only/ownership and whitespace checks pass. The full docs checker still
fails with 46 missing/37 ambiguous; the separate exact-frozen-base all-findings
comparison has zero additions. Prior sealed artifacts and all ten original own
modules remain unchanged. The final new exports are under
/workspace/v15-evm-agreement-artifacts/publication-7499c0a3; raw evidence is
/workspace/v15-evm-agreement-evidence/publication-7499c0a3. Full G46/G47 and
Backfill A/B remain unfinished. The already-authorized runtime action is normal
access restoration to the existing cache endpoint; it needs no reapproval.


## Published byte-image consumer checkpoint (audit 57995d33)

Recovery parent is 6a32b2bf2768005a96e7f4531e73d85b625c5bd8 on the existing
assigned branch; frozen base and the blocked persistent goal are unchanged.
The normal origin publication was verified at
4165de133bafd522ab18099e18cad489bb1aa7d6. Only its exact dependency-free
`Solidity/Evm/TryByteImage.lean` leaf was incorporated (blob
58bdce849cc7a5dfaeea2fa2497fad3c04f70efe; SHA256
bcf9bc3576dcc08cad4be80c997a324e5d2f1a0f5e82600044304823f242ba81).
Its direct State/RevertBytes dependencies are byte-identical to this checkout.
No master merge, producer repair, external import, dependency/pin/profile or
budget change was made. Registration is append-only; core stays independent.

`Bridge/SolidityBridge/RoadmapV15/ByteImageTransport.lean` proves fourteen new
consumer laws: backend_byte_at, image_wordByte_backend, image_store_backend,
image_store_observation, image_store_surrounding, image_store_read,
image_store_typed, image_store_signed, image_overlap_backend,
image_disjoint_backend, image_store_scalar, image_store_modulo,
image_unsigned_cleanup and image_signed_cleanup. The backend indexed-encoding
law holds for every natural input with j < width, including truncating widths.
The full-word laws consume the actual producer wordByte/store32/snapshot and
existing scalar/toWord encodings. They preserve the complete increasing-address
32-byte list at any natural bounded offset (no alignment premise), the full
intrinsic State and FrameKey, and every outside byte. Disjoint framing requires
one natural interval to finish before the other starts; overlapping last-writer
observation requires no disjointness. Readback uses the intrinsic uint range;
arbitrary natural inputs explicitly reduce modulo 2^256. Signed and narrow
cleanup reuse the published encodings/local scalar runner with the same stack
tail. No custom machine, simulation premise or byte-memory adapter is defined.

The producer's FrameMem includes ScalarFrame, aligned representation capacity,
resident-word and zero-above fields. These laws do not restrict compiler/source
admission or permit overwriting live physical typed heap roots. They show pure
side-image observations only: no physical allocator, PaddingCorrect witness,
MSTORE execution, calldata/copy semantics, resident expansion/gas adequacy,
fetched-code reachability, Osaka relation or account/transaction correspondence.
Optional TryByteCapture was not copied or used; no ghost capture is being counted
as a physical allocation. Published ExternalEvm TryMemory/Code/Driver were read
only: scoped fetched MSTORE/zero-fuel equations keep X admissibility and actual
FFI/padding/resource obligations separate. Their unavailable EvmYul closure was
not retried or treated as kernel-checked in this recovery.

`Bridge/SolidityBridge/RoadmapV15/ByteImageControls.lean` inhabits the image with
an actual State, nonzero ledger/balance/call metadata and full invocation/declaration
key. Controls cover offsets0/1, nonzero distinct words258/513, actual partial
overlap [1,33)/[2,34) with changed earlier bytes, nonzero disjoint preservation,
[64,96) capacity boundary, rejected overrun65, far-offset empty slices, signed
-1/minimum and unsigned maximum, modulo overflow, unsigned8/signed8 cleanup and
nonempty framed stack tails. Wrong endian,31/33-byte length and complete word
order are rejected. Whole lists, not numeric-only or final-byte observations,
are retained. The fourteen #print axioms reports use propext/Quot.sound and,
for image laws, inherited Classical.choice; no new axioms or trust shortcuts.

Separate read-only finder and skeptic reviews found no statement, premise,
nonvacuity, producer ownership or scope defect. The finder flagged key.value13
versus the fixture's default tx.msgValue0; tx.msgValue is now13 and the controls
were rechecked. This was witness clarity, not a missing theorem hypothesis.
Final handoff/artifact review follows before export. Raw focused failures
(first cache-prefix lookup, record layout and proof elaboration) are retained.
The corrected runtime probe prints Lean4.24.0 commit797c613 and
Lake5.0.0-src+797c613, followed by successful KeySort (2jobs), before
RUNTIME_GATE_PASS. The initial wrapper-version probe failed and remains failed.
The changed core closure passes971jobs under enforced12GiB/no swap; changed
consumer/control closure also passes. Detailed commands, metrics, raw docs
failures, complete finding comparisons and reviews are saved under
/workspace/v15-evm-agreement-evidence/byteimage-57995d33. Exact committed-head
patch/bundle/handoff/checksums will be exported under
/workspace/v15-evm-agreement-artifacts/byteimage-57995d33, preserving prior seals.

Full queue status remains unfinished: G46.01 numeric/control-to-Osaka is open;
G46.02 now has these checked pure representation consequences, but actual
reference execution, memory/calldata driver and padding/resource clauses remain
open; G46.03 symbolic persistent/transient path composition is open;
G46.04-.05 environment/hash/precompile actual pinned correspondence is open;
G46.06/G47 production V13/V14, exact driver/resources/account/call/create/return/
revert/transaction and finite/infinite trace composition are blocked. Backfill A
is partial (64 checked laws total,15 reference proposals still UNCOMPILED), and
Backfill B is partial (existing cumulative approved per-run hash/prefix/checkpoint
laws and150-row secondary accounting; all150 opcode rows OPEN, no emitted/raw
opcode equivalence claimed). No global hash injectivity or local journal/payment
Boolean replaces missing account execution. The old cold full5400s exit124 and
cache860-file CONNECT403 remain retained failures; the full Bridge gate remains
pending. No unchanged failed heavy/cache gate was repeated. QNET1 already
authorizes normal access restoration to the configured endpoint; runtime-owner
restoration evidence and the pinned cache recheck are still required, without
reapproval. This checkpoint does not complete the lane or goal.

Final checkpoint review: independent finder and skeptic cleared the actual
fourteen statements, explicit modulo clause, checked controls/gates and handoff
status split. Both flagged the fixture description's imprecise “call data”;
it now says call metadata, since no calldata payload was constructed. The finder
also caught a blank line breaking the append-only module-map table; the new rows
now continue that table. Only the three newly generated V15 Python bytecode
files were relocated to the task evidence directory; unrelated bytecode and all
Lean/dependency caches were preserved. Layer/orphan/trust and whitespace checks
pass;12 opcode-accounting plus18 reference-boundary tests pass. Raw docs exits
remain1: current/frozen46missing37ambiguous; publication48missing37ambiguous.
Complete class/multiplicity comparisons add zero findings against either
baseline. This is a no-new-findings pass, not a global documentation pass.

Artifact review refinements: the independent finder verified the actual committed
patches, bundle/ref, source snapshot and theorem inventory. The skeptic corrected
two export metadata descriptions: this lane supplies no PaddingCorrect inhabitant
or negation proof, so the new handoff states only that no published/supplied
witness is available; G46/G47 names are work-package IDs, while feature IDs come
from the actual existing opcode-obligation/G03-ledger report (168 entries, all
coverage obligations still open). These artifact corrections change no theorem,
profile, approved premise, ledger or proof status. Final seal follows the reviewed
exact-head export; archive/checksum verification is a separate gate.


## Offline-cache reference-reader checkpoint (8dc66c8f recovery)

Recovery parent is4788e69db46fbd8b4e738b55c048952a84d66e7a on the unchanged
assigned branch/frozen base. The coordinator's partial offline restoration is a
real changed prerequisite: the actual pinned cache unpack reports853files,
exit0, memory.max12884901888/swap.max0/peak709640192. Its raw log/JSON are
preserved in the new evidence directory. The supplied transfer bundle's reported
SHA256 is0aaa29a1189090a6302cc783a6542cb5acce5a40e8d8e5cc364f237fde7e792d;
coordinator payload reviews and chunk transport are upstream evidence, while
this VM's unpack/source checks are local evidence. No source, pin, toolchain,
profile, proxy or policy change is inferred.853archives do not establish all860
original requests, the actual reference import closure, or a kernel theorem.

The smallest actual pinned source check exposed missing Batteries.CodeAction.
Deprecated, Aesop.Search.Expansion.Norm and five Mathlib dependencies. Each was
compiled serially from the unchanged pinned source under the existing300s
per-file cap and12GiB/no-swap limit. Actual EvmYul.UInt256 then kernel-checked.
Three more small Mathlib modules for the larger memory imports also compiled;
no reserved source was edited and no conflicting cache product overwritten.
The reference MemoryBytes/ExternalEvm source closure still requires684 absent
Mathlib-cache modules (plus source-built vendor/CSLib adapters). This is not a
request to build that large closure cold. The pinned Cache.Hashing.getHashMemo
API identified exact module/source-SHA256/LTAR names, recorded in
/workspace/v15-evm-agreement-evidence/offline-reference-8dc66c8f/missing-cache-request.json
with its checksum. For example Mathlib.Data.List.Lookmap requires
734d5b5f3d64b709.ltar. QOFF1 asks the coordinator for matching existing host
archives; normal proxy restoration is neither claimed nor reprobed.

The two original reader statements/proof bodies were moved unchanged from
`Bridge/SolidityBridge/RoadmapV15/ReferenceEncoding.lean` into
`Bridge/SolidityBridge/RoadmapV15/ReferenceReader.lean`, importing only actual
EvmYul.UInt256 and the already-checked backend encoding transport. Public names
reference_big_reader/reference_array_reader and transitive import compatibility
are preserved. This is an owned import-closure factoring, not a reserved adapter
repair or duplicate reference semantics. Both laws now kernel-check.

`Bridge/SolidityBridge/RoadmapV15/ReferenceWordObservation.lean` adds five checked
consumer laws: reference_backend_bounded, reference_word_toNat,
image_reference_reader, image_reference_word and image_reference_signed.
The first keeps exact width and value<256^width; the actual UInt256 constructor's
modulo is discharged only using a full bounded backend word. The image laws
consume actual published snapshot/store32 and existing intrinsic uint/toWord/
BitVec representations. Offsets/spans remain natural and capacity-bounded;
ScalarFrame remains a producer image field, never a compiler-profile exclusion.
The signed theorem explicitly uses BitVec's signed observation after the actual
reference reader. No reference signed-operation execution, allocator/FFI witness,
physical MSTORE, gas, stack/driver adequacy or Osaka agreement is asserted.

`Bridge/SolidityBridge/RoadmapV15/ReferenceReaderControls.lean` passes actual
reader/UInt256 and inhabited image controls: distinct nonzero258/513, exact
complete32-byte lists, leading-zero/empty numeric collisions versus unequal
lists, wrong endian/31/33-byte lengths/word order, insufficient one-byte width,
modulo overflow, unsigned maximum, signed-1/minimum, unsigned8/signed8 cleanup,
unaligned overlapping last writer, exact upper capacity and full State/FrameKey
preservation. Seven #print axioms reports pass: two readers use propext/Quot.sound;
five observation laws also use existing Classical.choice. No new axiom, sorry,
native_decide, implemented_by or budget increase was introduced. Focused import
closure passes. Runtime output prints Lean4.24.0 commit797c613 and
Lake5.0.0-src+797c613 followed by KeySort2jobs passing before RUNTIME_GATE_PASS.

The source-only publication checker now loads the moved readers together with
the remaining encoding source, still requiring all15 original names exactly
once. Its status explicitly says it cannot certify kernel checking, rather than
incorrectly labeling the now-checked readers uncompiled. Missing/duplicate moved
reader mutations are rejected;20 publication controls pass alongside the12
opcode-accounting controls. Separate independent read-only finder/skeptic source
reviews found no proof, premise, nonvacuity, ownership or observation-scope defect.
Final docs/registration/handoff and artifact reviews follow before sealing.

Evidence limitation discovered and corrected: the new dependency driver reused
two early unsealed retry filenames when its counter restarted. The earlier
Nat.Find raw error is separately retained; the earlier Unbundled.Defs per-attempt
raw text/timing was overwritten. The first failed closure report was captured
before replacement and preserved. Future filenames/reports use unique run IDs.
This is disclosed in logging-correction.txt, not relabeled a passing gate or
reconstructed by rerunning failures. All previous-turn sealed artifacts and
original raw full/cache/docs failures remain intact.

Full queue remains unfinished.71 consumer laws are checked (64prior, two moved
original readers, five new observation laws);13 original encoding proposals and
the old full ReferenceEncodingControls module remain uncompiled. G46.01 still
needs actual Osaka numeric/control correspondence; G46.02 needs the remaining
reference encoding/memory/calldata compiler/driver/resource clauses; G46.03 needs
symbolic persistent/transient path composition; G46.04-.05 actual environment/
hash/crypto observations remain open under approved per-run premises only.
G46.06/G47 still require productionV13/V14, actual driver/resources/arbitrary
callee/account/call/create/return/revert/transaction/rollback/fee/nonce/log and
finite/infinite trace composition. Backfill A/B are partial; all150 opcode rows
and every secondary obligation remain OPEN. No global hash injectivity, desired
simulation, payment Boolean or local journal closes those obligations.

The existing goal is unchanged; get_goal is not exposed and no goal mutation,
reset/reactivation/recreation/completion or competing continuation was made.
No unchanged network403 probe/cache fetch or whole5400s failed gate was repeated.
The historical cold full gate exit124 remains failed and fullBridge gate pending.
New raw evidence is under
/workspace/v15-evm-agreement-evidence/offline-reference-8dc66c8f; cumulative
exact-head patch/bundle/handoff/checksums will be exported under
/workspace/v15-evm-agreement-artifacts/offline-reference-8dc66c8f, preserving prior
seals. Immediate cache action is QOFF1 matching existing host archives; it adds
no pin/profile/toolchain or source-scope change. Completion is not claimed.

Precommit handoff review correction: finder and skeptic independently caught
stale inherited queue metadata saying15 pending readers/encodings and18 source
mutation tests. The draft now says13 remaining encoding declarations plus the
old full controls, and20 source tests. No proof/profile/status premise changed.
Both reviews require the disclosed retry-log loss to remain a limitation, not
a passing retention claim.


## Original reference encoding checked (a359b418 recovery)

Parentc80a48fa497f93cd10466b6a494ca6fa21aa4fd6 remains on the assigned branch
and frozen base.684 exact requested archives arrived, independently rehashed
against all684 current source files and installed cache bytes; bundle SHA256
is e9c798dfb770d5ef72811fdbec031520317c8c88c7c1c3a0d6d01f40c59daddf,
25292800bytes. The unchanged offline unpack ran ONCE with the original300s cap,
processing1537 available files, exit0, cgroup peak479084544bytes under
memory.max12884901888/swap.max0. QOFF1 is fulfilled for the requested archives
and actual reference imports; no endpoint-access restoration is inferred.
No source/pin/toolchain/profile change or giant cold Mathlib build occurred.

The actual published MemoryBytes/ExternalEvm/CSLib dependency closure now passes
serial kernel checks from unchanged sources. `Bridge/SolidityBridge/RoadmapV15/ReferenceEncoding.lean`
passes all13 remaining original encoding statements, and
`Bridge/SolidityBridge/RoadmapV15/ReferenceEncodingControls.lean` passes actual
nonzero/signed/narrow/modulo/length/endian/order/terminal controls and all15
original reader/encoding #print axioms reports. Pure encoding_spec supplies its
exact32-byte length and actual reader value for every UInt256, without an
allocator hypothesis. These laws preserve complete ordered List/ByteArray
observations, existing typed scalar/ABI representations, constructor modulo,
stack tails, sequence order and completed-frame success bit/payload.
71previous checked names plus13 newly checked names gives84; zero original
encoding proposals remain uncompiled. Source-only accounting remains distinct
from kernel evidence and does not certify any opcode correspondence.

The first real proof check hit the ORIGINAL200000-heartbeat limit at the empty
case of reference_encoding_sequence. Its full ordered statement is unchanged;
List.flatMap_congr now applies pointwise reference_encoding_bytes instead of
reduction-heavy induction. No heartbeat, recursion, stack, fuel or time budget
was increased. Three initial controls failed to rewrite through a private first
fixture; explicit unfolding fixes elaboration without changing expected bytes.
Both failures are retained as failures. All headlines use only propext,
Classical.choice and Quot.sound (the two reader laws need no choice).

Separate independent read-only finder/skeptic source reviews clear the exact
statements, hypotheses, inhabited controls, ownership and unchanged budget/profile
boundaries. Focused import/control closure passes. Lean4.24.0 commit797c613 and
Lake5.0.0-src+797c613 are printed before KeySort2jobs passes and RUNTIME_GATE_PASS.
Structural/trust/orphan,32 mutation tests and full raw docs/no-new comparison
results accompany this checkpoint's handoff. Original raw full5400s exit124,
network403, docsexit1 and the earlier unsealed retry raw/timing loss remain
historical failures/limitations, never manufactured or relabeled green.

This checkpoint does NOT prove UInt256.toByteArray serialization, provide a
PaddingCorrect witness, execute physical stores, discharge fetched-code/X gas
prechecks or establish Osaka/resource/account/transaction/trace correspondence.
G46.01-.06/G47 and Backfill A/B retain all remaining productionV13/V14,
compiler-symbolic-path, driver/resource, arbitrary permitted-callee and exact
account/call/create/return/revert/fee/nonce/log/rollback/finite-infinite trace
obligations. All150 opcode rows and secondary obligations stay OPEN. The goal
is unchanged blocked; get_goal unavailable, no mutation/reactivation/recreation.
New evidence: /workspace/v15-evm-agreement-evidence/encoding-a359b418. Next ready
owned work consumes the newly checked encoding in typed image and preallocated
observation consequences, without duplicating reserved memory adapters.


## Typed images and preallocated reference observations

After the checked84-law checkpoint1d82d0715dea2f43226174852d4e56b42dddc932,
new owned consumers use the now-checked pure reference encoding and the unchanged
published MemoryComposition/MemoryRefinement producers. Both producers also
kernel-check under the original serial300s per-file/12GiB/no-swap limits.

`Bridge/SolidityBridge/RoadmapV15/ReferenceImageTransport.lean` proves
 typed_image_reference_bytes, typed_image_reference_observation,
image_pair_reference_bytes and disjoint_image_reference_bytes. Every intrinsic
scalar uses its existing toWord/Scalar encoding. The complete ordered32-byte
reference observation equals the actual published store32/snapshot image;
full intrinsic State and FrameKey identity are retained. Two successive snapshots
retain observation order even with overlap: this does NOT assert that both
values remain in the final overlapping image. Preserving the earlier final
observation requires the explicit natural interval-disjointness clause. The
producer's ScalarFrame remains a representation field, not a compiler exclusion.

`Bridge/SolidityBridge/RoadmapV15/PreallocatedObservation.lean` proves
populated_backend_observation, populated_typed_observation, populated_load_frame
and populated_supplied_load. They consume the actual published inhabited
populatedState/populatedCore/Represents constructor: its complete64 physical
bytes equal the two backend big-endian words, including leading zeros and order.
The typed law uses the actual intrinsic ABI encoding, including signed values.
The load-frame law preserves the entire actual MachineState for in-capacity
indices. The supplied-opcode law proves the real EvmYul.EVM.step equation with
positive fuel and zero charged gas plus preservation of all64 bytes. Its returned
word is deliberately the actual lookup expression. No padding/read-value contract,
serialization/allocation witness, stack-height/gas/X precheck, fetched bytecode,
source reachability, Osaka/account/transaction or resource adequacy is supplied.
Preallocation is numeric representation capacity only.

`Bridge/SolidityBridge/RoadmapV15/ReferenceObservationControls.lean` passes all
new controls and8 explicit axiom reports (propext, Classical.choice, Quot.sound).
Witnesses include actual nonzero distinct258/513 cells, signed-1 ABI bytes,
full64-byte target order/length negatives, unaligned overlap and disjoint framing,
both cell indices and upper-capacity refusal, nonempty stack tails, and actual
zero-fuel OutOfFuel refusal. Both legacy/viaIR FrameKey identities are exercised;
these pure identity fixtures do not claim compiler-pipeline execution. Initial
controls required explicit numeral bounds to remove a free pipeline variable
before decide and explicit private-fixture unfolding; expected bytes were not
changed. Their raw failures and passing follow-up are retained uniquely.

The new8 laws/control closure pass, bringing the total to92 checked laws. All
original15 reader/encoding laws are checked; no original encoding proposal is
left uncompiled. Separate read-only finder and skeptic source reviews clear the
exact premises, non-vacuity, temporal-versus-final ordering, ownership and actual
supplied-opcode boundary. Neither reviewer runs Lean/server/builds. Final
registration/docs/handoff and sealed artifact checks follow before export.

Remaining full-gate runtime dependency was inspected without a giant cold build.
A naive text inventory was retained but superseded because it mistook comment
text and truncated apostrophe module names as imports. The final inventory uses
Lean.parseImports on actual headers:1971 modules across the configured mandatory
default Bridge targets, zero unresolved source names or parse errors,96 further
missing cache modules and240 other unbuilt products at inspection. These96
LTAR names are DISJOINT from the fulfilled684 request, and none is installed.
The unchanged pinned Cache.Hashing API supplies exact source-SHA256/LTAR identities
in /workspace/v15-evm-agreement-evidence/encoding-a359b418/full-bridge-cache-request.json,
SHA256 aa6df5806a1a1ddb8f7a2c7a81a81cb35da69b4a659cff5ce80260f24d2a5aad.
QOFF2 requests matching existing host archives for the broader mandatory Bridge
gate only. It does not reopen QOFF1, infer availability, request pin/profile
changes or certify that imports alone will make the full gate pass. No403 probe,
cache fetch, tunnel/mirror or unchanged full5400s failed gate was repeated.

Full G46.01-.06/G47 and Backfill A/B remain unfinished: actual Osaka primitive
correspondence, symbolic compiler paths/calldata, environment/hash/cryptographic
observations under approved per-run premises, driver/exact resource abstraction,
productionV13/V14 and actual arbitrary permitted-callee account/call/create/
return/revert/transaction/fee/nonce/log/rollback/finite-infinite trace composition
remain open. All150 opcode rows and secondary obligations stay OPEN. No new
axiom, sorry, native/implemented_by shortcut, desired simulation, global hash
injectivity, weakened observation/profile or increased budget was introduced.
Original full exit124, raw docs exit1 and previous retry-retention loss stay
explicit failures/limitations; goal remains unchanged blocked, never mutated.

Cumulative exact-head artifacts will be sealed at
/workspace/v15-evm-agreement-artifacts/encoding-a359b418; actual commands, raw
failures, resource/axiom outputs, full cache request and reviews are under
/workspace/v15-evm-agreement-evidence/encoding-a359b418. First checkpoint and final
head/base/branch, proof-versus-external-test boundaries and all queue statuses
are recorded in the handoff. No new external execution test was substituted for
kernel proof; old source/compiled-pipeline fixture expectations are untouched.

Final92-law handoff review correction: both independent reviewers caught the
stale G46.02 instruction to kernel-check consumers; it now names only the actual
remaining physical read-value/allocator/compiler-path/calldata/driver/resource
and full-gate obligations. The finder also required QOFF2's draft to carry its
full standalone question, source tags and mutually exclusive consequences;
these are now present. No theorem, premise, expected observation or scope changed.


## QOFF2 recovery: reference environment consumer (cd80b3fc)

Frozen base and branch remain unchanged. The96 requested same-pin archives were
verified against every original source hash, bundle and installed cache bytes;
one offline unpack passed under12GiB/no swap. Lean4.24.0 and Lake5.0.0-src+797c613
were recorded; `lake build Solidity.KeySort` passed (2jobs). QOFF2 archive supply
is fulfilled; endpoint access and the original semantic goal remain blocked.

[EnvironmentReference.lean](../../Bridge/SolidityBridge/RoadmapV15/EnvironmentReference.lean)
adds eight consumer laws over actual intrinsic/backend and reference definitions:
`environment_address_word`, `environment_address_roundtrip`,
`environment_word_encode`, `environment_observe_reference`,
`environment_selected_backend`, `environment_selected_reference`,
`environment_reference_bytes`, `environment_source_observation`.
The arbitrary reference frame uses its actual account map (including absent
accounts), caller/self identities, value and timestamp modulo256bits. The selected
reference theorem retains the whole result state and arbitrary stack tail under
positive fuel and zero charged gas. The source theorem explicitly requires the
published five-clause environment representation relation; no source execution
or preservation is assumed. The byte theorem retains all32 ordered bytes.
BALANCE, other metadata instructions and resource/fetched-driver adequacy remain
open; Cancun reference arithmetic is not full Osaka correspondence.

[EnvironmentReferenceControls.lean](../../Bridge/SolidityBridge/RoadmapV15/EnvironmentReferenceControls.lean)
checks distinct self7/caller11 accounts with balances29/31, value13, timestamp
2^256+17 wrapping to17, absent-account zero, caller changes, credited self balance,
complete observation order and full byte lists, wrong endian/length negatives,
arbitrary nonempty stack tail and zero-fuel failure. A matching intrinsic state
inhabits the exact source relation; a mismatched self balance refutes it.
All eight headline axiom sets are only propext/Classical.choice/Quot.sound.
Focused source and controls pass, bringing the checked consumer inventory to100.
No axioms/sorry/native shortcuts or proof budgets were added.

Review findings corrected before checkpoint: finder and skeptic requested the
inhabited source relation and mismatch negative; both were added. Runtime finder
identified fail-open process inspection and a guard-status race; the revised
runner records inspection outcomes, rejects monitoring failure for a live
container, and cannot report exit0 with a guard violation. The first mandatory
Bridge attempt retained exit137: its monitor mistakenly classified a defunct Lean
zombie as an active compiler missing-j1. The corrected runner ignores statZ only;
all live compilers retain-j1, one-at-a-time and original300s limits. Reusing the
same build cache after this diagnosed wrapper correction does not waive that
failure. Original full5400s exit124, cache403, raw docs1 and disclosed historical
unsealed retry data loss remain unchanged and retained. Final gate outcomes and
exact committed-head export are recorded in the recovery handoff.

G46.01 remains incomplete (actual Osaka primitives/control/resource adequacy);
G46.02 remains incomplete (physical read-value, allocator/padding, compiler-path,
calldata and driver clauses); G46.03 remains incomplete (actual symbolic-slot
representation/target composition); G46.04 is partial (the five selectors above,
with BALANCE/other metadata/world composition still open); G46.05 is partial
(approved per-run hash-premise transport only); G46.06/G47 remain blocked by
actual general V13/V14, Osaka driver/resources/account/call/create/transaction
and finite/infinite trace composition. BackfillA andB have useful checked laws
and controls, but do not close those parent obligations. All150 opcode rows stay
OPEN, including every secondary obligation. The unchanged persistent goal is not
reset/reactivated/completed by cache arrival or a narrow/full Bridge check.


Environment checkpoint gate/handoff: actual `timeout 5400 ./scripts/check-bridge.sh`
passed all four configured targets (2150jobs,443.195s), cgroup peak1911181312bytes,
memory.max12884901888/swap.max0, no process-guard violation. Task-local config
copies change only weakLeanArgs-j1/--tstack131072; source pins and defaults are
unchanged. Layer/orphan/trust/whitespace and32 accounting/publication mutation
tests pass. Global docs still fails rawexit1 (46missing/37ambiguous); complete
finding-class/multiplicity comparisons against frozen and published baselines
have zero additions. Independent finder/skeptic source/control/runner reviews
clear after the recorded fixes; neither reviewer ran Lean/server/builds.
Exact checkpoint evidence: /workspace/v15-evm-agreement-evidence/bridge-cd80b3fc.
Full-source5400s historical exit124 remains failed/pending; no rerun or waiver.
All100 checked laws are partial consumer progress; all150 opcode rows stay OPEN.
Next independent original item is operandful BALANCE, preserving actual target
accessed-account effects. Full remaining G46/G47 obligations above are unchanged.


## Operandful BALANCE checkpoint (cd80b3fc continuation)

Following committed environment checkpoint289f36f974ff8e6cf71edec503b5848999ff4a8b,
[BalanceReference.lean](../../Bridge/SolidityBridge/RoadmapV15/BalanceReference.lean)
proves `environment_balance_value`, `environment_balance_backend`, and
`environment_balance_reference`. These connect the existing backend account
truncation and local selection to the actual reference `State.balance`, including
absent-account zero and its actual accessed-account update. The reference theorem
retains the complete target state and arbitrary tail, using positive fuel and
zero charged gas. It does not establish warm/cold gas sufficiency, X admissibility,
fetched code, Osaka agreement, compiler reachability, arbitrary callee/account
execution or source-world/transaction preservation. No new interpreter, journal,
account semantics, payment Boolean or simulation premise is introduced.

[BalanceReferenceControls.lean](../../Bridge/SolidityBridge/RoadmapV15/BalanceReferenceControls.lean)
uses operand2^160+7 to read actual account7 balance29, distinct account11 balance31,
absent accounts, and the maximum256bit operand (not maximum stored balance).
It checks complete ordered observations[29,31,0,0], rejects wrong zero/caller
balances, witnesses accessed-account insertion for present and absent accounts,
retains the actual account map and nonempty[258,513] tail, and checks backend and
reference underflow plus zero-fuel refusal. All three scoped axiom reports are
only propext/Classical.choice/Quot.sound. Focused source/controls pass; the total
checked inventory is103, zero original encoding proposals remain uncompiled.

Separate independent read-only finder and skeptic reviews cleared the actual
statements/definitions, complete state/tail, controls and ownership; neither ran
Lean/server/builds. Their only clarification was to distinguish maximum operand
from maximum stored balance, as above. Initial clean-check preparation stopped
before source creation because three task-test Python bytecode files remained
untracked; only those generated files were removed, and the preparation failure
is recorded separately. No semantic failure, expected value or budget was waived.

G46.04 remains partial despite these six instruction families: broader metadata,
actual gas/stack/fetched-driver/fork adequacy and source-world/account composition
remain open. All150 opcode rows and secondary obligations remain OPEN. G46.01,
G46.02, G46.03, G46.05, G46.06/G47 and both Backfill queues retain the exact
outstanding clauses in the environment checkpoint and final handoff. Full-source
historical5400s exit124, network403, docs rawexit1 and the lost earlier unsealed
retry evidence remain retained/disclosed, independently of the passing Bridge
closure. No goal state or authority changed.


BALANCE checkpoint gate/handoff: focused source and controls pass; final mandatory
four-target Bridge closure passes2152jobs in7.149s, cgroup peak350277632bytes,
12GiB/no swap, no guard violation. Layer/orphan/trust/whitespace pass. Global docs
remains rawexit1 with complete no-new comparisons separately against frozen and
published baselines. Both independent read-only source reviews clear;103 laws
remain partial and all150 opcode rows OPEN. Next newly enabled original consumer
work will inspect the already-genuinely-published TryMemory/Code/Driver sources;
these were previously unavailable only because their reference imports could
not be checked. No prerequisite is counted proved merely from its publication.


## Published fetched-store checkpoint (cd80b3fc continuation)

After BALANCE checkpointd36f35db06238076d269b15fd56531ebb348a401, the restored
imports enabled checking three previously inspected genuine published producers.
Only the exact byte-identical files from the already-fetched normal-origin
commit4165de133bafd522ab18099e18cad489bb1aa7d6 were incorporated:
[TryMemory.lean](../../Bridge/SolidityBridge/ExternalEvm/TryMemory.lean),
[TryMemoryCode.lean](../../Bridge/SolidityBridge/ExternalEvm/TryMemoryCode.lean),
[TryMemoryDriver.lean](../../Bridge/SolidityBridge/ExternalEvm/TryMemoryDriver.lean).
All56 vendor dependency files match that publication; only its VENDOR.md narrative
differs from the inherited checkout, and that reserved document is untouched.
The initial stricter all-file comparison stopped on that documentation mismatch;
the failure and exact subsequent semantic-source comparison are retained.
No master merge, unmerged dependency, producer repair, pin/toolchain upgrade or
source/profile/budget change occurred. All three per-file kernel checks pass;
Code took46.174s with942108672byte cgroup peak, within original300s/12GiB limits.
Publication, Git blobs, SHA256 values, normal-origin fetch and frozen-base ancestry
are recorded in bridge-cd80b3fc/trymemory-publication.json. Independent finder and
skeptic verified the exact incorporation and boundaries read only.

[CompiledStoreCheckpoint.lean](../../Bridge/SolidityBridge/RoadmapV15/CompiledStoreCheckpoint.lean)
proves five new public consumer laws: `compiled_store_decode`,
`compiled_store_gate`, `compiled_store_supplied`, `compiled_store_fetched`, and
`compiled_store_driver`. The existing Pipeline type selects the two complete
published runtime inputs. The explicit checkpoint is positioned atPC4 with empty
memory/activeWords0, stack[64,128], gas12 and permissive static flag; arbitrary
seed world/account/context fields otherwise remain. These are constructed
checkpoint inputs, not a restriction on admitted source/compiler profiles or
proof of entry reachability/installation. The actual driver's complete gate is
discharged, using9 expansion plus3 base gas, without any gas-success/simulation
premise. The actual whole fetched/supplied result retains the real vendor mstore
serialization/padding expression. One actual X continuation follows with positive
fuel; it asserts neither final success nor observation/source/transaction/trace
agreement. No physical padding/read-value/allocator witness is inferred.

[CompiledStoreControls.lean](../../Bridge/SolidityBridge/RoadmapV15/CompiledStoreControls.lean)
preserves the complete result tuple(pc5,gas0,activeWords3,execLength20,stack[])
for both real runtime inputs and checks actual code/account/caller identity,
12-gas gate success,11-gas base refusal,8-gas expansion refusal, actual underflow,
zero fuel and wrongMSTORE8 opcode. Static-context MSTORE remains legal; no profile
exclusion is added. Full code lengths1673/1965 remain distinct. All five headline
axiom reports are only propext/Classical.choice/Quot.sound. The total public checked
consumer-law count is108 (92previous+8environment+3BALANCE+5checkpoint); private
word-charge/control helpers are excluded from that count.

Proof iteration failures are retained: record-layout and explicit finite-word
subtraction/let-normalization errors were fixed without changed statements or
budgets. The first new control eagerly reduced a whole runtime/state expression;
only its task-owned container was stopped with exit137 after45.877s before the
12GiB cap. A pre-stop cgroup peak snapshot was10475413504bytes; aggregate sampled
Lean/Lake RSS peak was11555598336bytes, with final cgroup reading unavailable due
to that stop. No final peak is manufactured. The same complete expected tuple is
now proved by explicit small projection and published size/expansion lemmas;
controls pass with296423424byte cgroup peak and unchanged limits. Both independent
finder/skeptic reviews cleared actual statements, hypotheses, non-vacuity,
complete state/controls, exact source ownership and scope; neither ran Lean/builds.

G46.02/G46.06 gain one actual fetched/gated checkpoint only. EntryPC0 reachability,
installed-code/source association, physical returned bytes/padding/allocation,
compiler paths/calldata, whole-driver resources and approved Osaka/full V13/V14
account/call/create/transaction/finite-infinite trace composition remain open.
All150 opcode rows and their secondary clauses remain OPEN. No approved hash
premise, original refusal, expected observation or compiler pipeline was changed.
QOFF2 is fulfilled and mandatory Bridge closure is now checked, but full-source
historical5400s exit124 and original semantic goal remain blocked independently.


Fetched-store checkpoint gate/handoff: final mandatory four-target Bridge build
passes2157jobs in65.717s, cgroup peak1081344000bytes,12GiB/no swap,
no monitor violation. Layer/orphan/trust/whitespace pass; raw docs remains exit1
with separate complete-class/multiplicity no-new comparisons against frozen and
published baselines. Separate independent read-only producer-incorporation and
consumer finder/skeptic reviews clear; all108 public consumer laws are checked.
No producer theorem is counted as a new owned consumer. Full original lane and
unchanged persistent goal remain blocked; all150 opcode rows remain OPEN.
Next available metadata work consumes committed selectors/address-function
packing against actual reference immediate reading and supplied PUSH dispatch;
no missing producer is silently replaced or assumed discharged.


## Metadata immediate consumer checkpoint (cd80b3fc continuation)

Following401b337d029ccd945084bee4078ee606a09dd220,
[MetadataReference.lean](../../Bridge/SolidityBridge/RoadmapV15/MetadataReference.lean)
adds four public checked consumer laws: `metadata_reference_read`,
`metadata_selector_reference`, `metadata_abi_reference`, and
`metadata_function_reference`. The existing Fin33width and Fin(256^width)value
remain intrinsic. The actual reference uInt256OfByteArray reads the backend's
exact ordered bytes; numeric canonical selectors feed actual supplied PUSH4,
left-aligned ABIbytes4 feeds PUSH32, and existing address/selector packing feeds
PUSH24. Whole result states, arbitrary stack tails and PC increments5/33/25 are
retained. Selector backend pushStep correctness is part of the first dispatch
law. No new decoder/function representation or metadata resolver is introduced.
Canonical metadata refusal, raw msg.sig admission and declaration/code association
remain unchanged; no fetched-byte/resource/X/Osaka or source correctness follows.

[MetadataReferenceControls.lean](../../Bridge/SolidityBridge/RoadmapV15/MetadataReferenceControls.lean)
checks complete emitted5/33/25byte lists for selector0x01020304 and receiver7,
full32byte reference observations at both alignments, wrong endian/length/alignment,
width0 and full32-byte width maximum256bit value, nonempty258/513stack tails,
missing canonical metadata/constructor refusal, missing immediate and zero fuel.
All four headline axiom reports are only propext/Classical.choice/Quot.sound.
Focused proofs/controls pass. Total checked public consumer laws:112; private
helpers/control witnesses are excluded. Both independent finder/skeptic source,
hypothesis, non-vacuity, ownership and full-observation reviews clear read only.
The initial Array/List coercion and finite-width rewrite errors were corrected
by using the actual reader's data projection and explicit Fin constructors,
without changed statements or limits. A brief executor disconnect lost only its
process handle; the saved actual exit1/log/json were inspected on the same
expected checkout/head before continuing. No completion was inferred from it.

The final source/Bridge gate is revisited for a diagnosed changed build cause:
the original cold5400s run stopped after806/981jobs, whereas its remaining core
971job closure, native targets and262job TestSuite subsequently passed in saved
separate bounded runs. This recovery has now built/replayed the complete core
and newly restored external closure in actual four-target Bridge builds. Those
materialized shared products change the original cold-gate condition; this is
not an unchanged timeout retry or a larger budget. The original exit124 and
separate historic outputs remain immutable. A fresh bounded run uses the same
5400s global/300s per-file/12GiB/no-swap limits and task-local exact config copies
that only add-j1/--tstack131072. It checks default source targets, TestSuite,
all four Bridge targets and actual SolKey annotations; no result is assumed.

G46.01-.06/G47 remain incomplete, all150 opcode rows/secondary clauses OPEN.
Metadata decoder/code association and production compiler paths, physical
read-value/padding/allocator/calldata, approved hash/crypto target adapters,
actual Osaka/fork/resource/general V13/V14 and account/call/create/transaction/
finite-infinite trace composition remain explicit prerequisites. The six
supplied environment/balance instruction families, three supplied metadata PUSH
forms and concrete one-store fetched driver checkpoint do not close those.


Metadata/final checkpoint gate/handoff: actual `timeout 5400 ./run-lean.sh --bridge`
PASSES in8.666s with982default-target jobs,262TestSuite jobs,2160Bridge jobs (all
four configured targets), and actual SolKey377parsed/131read-bearing/131covered
annotations match. Cgroup peak383291392bytes, memory.max12884901888/swap.max0;
no guard violation. The prior cold exit124 remains historical failure, not a
current failure or waived gate. Runtime copies preserve original configuration
and package pins; root/Bridge command dispatch only selects their exact task-local
configs with weak-j1/tstack flags. Layer/orphan/trust/whitespace and original32
mutation checks pass; all150 raw opcode rows still OPEN, source accounting never
certifies execution. Global docs remains rawexit1 with46missing/37ambiguous;
complete finding/multiplicity comparisons against frozen and published baselines
have zero additions. The newly meaningful consumer milestones were independently
reviewed read only, without reviewer Lean/server/builds. Final exact-head artifacts
and post-seal checks are separate from these kernel/structural gates.

The original full goal remains BLOCKED by semantic producer/composition work,
not a cache or current import-gate failure: G46.01 actual Osaka numeric/control;
G46.02 physical read-value/allocator/padding/compiler paths/calldata and general
memory/driver resources; G46.03 symbolic persistent/transient slots; G46.04 general
metadata decoder/compiled-code/source-world association and resources; G46.05
actual target hash/crypto/precompile agreement under only approved per-run
CollisionFree/RegionsDisjoint; G46.06/G47 general approved Osaka/resource and
production V13/V14 arbitrary-callee/account/call/create/return/revert/fee/nonce/log/
rollback/transaction/finite-infinite trace composition. BackfillA/B retain the
same outstanding execution clauses; their112 checked consumer laws, existing
prefix/hash/checkpoint helpers and150-row exact obligation accounting do not
close the lane. PaddingCorrect has no inhabitant supplied; no allocator axiom or
approval is requested. QOFF1/QOFF2 archive supplies are fulfilled; endpoint403
repair remains unverified, but it no longer blocks the checked mandatory imports.
Historical raw failures and the disclosed lost early unsealed retry text/timing
remain retained/explicit; that retention requirement is not called passed.

Final runtime review: independent finder corrected the metadata boundary unit from32bit-width to32-byte width (256bits); actual theorem/controls were already correct. Both runtime reviewers verified the complete gate log, exact configs and null monitoring violation; no other finding. Final artifact reviews follow the committed-head export separately.
