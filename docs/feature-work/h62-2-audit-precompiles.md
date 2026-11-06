# H62 item 2: precompile empty-statement audit

**Successor update (2026-11-06):** the retired member's authenticated final head is now
merged on the original precompile-agreement branch. Fresh frozen-v4.24 evidence
accounts for 97/138 cases, with 41 pending; details are in the successor checkpoint
below. The retirement notice immediately below applies to the retired member,
whose goal remains paused. The successor continues its existing original goal.


**H82 retirement: STOPPED / PAUSED BY USER INSTRUCTION.** No implementation continuation
is authorized in this worker. Handoff target: solidity-sol-20261103/precompile-agreement.
Successor integrates final committed head after the final stopped/head acknowledgement.
No H82 proof edit was started. The exposed goal tool cannot set PAUSED (only complete/blocked);
no substitute transition, completion or goal reset was performed. Original assignment, full queues,
exact scope and retirement state are committed under tests/h62/item2/audit-precompiles/handoff/.
No branch push: H71 authorization content is unavailable and the original no-push rule remains.


Status: blocked; this is a committed partial audit, not completion of the four-checkpoint queue.
Owner: solidity-h62-2-20261106/audit-precompiles. Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`.
Branch: `codex/solidity-h62-2-20261106/audit-precompiles`.
Actual worktree: `/workspace/solidity-h62-audit-precompiles`.
The existing clean `/workspace/solidity-lean` checkout was preserved. The required base was fetched,
verified as an ancestor of published origin/master, and used directly for this branch.
No push, merge, deployment, central registration, axiom-pin edit, or frozen-interface edit occurred.

## Checkpoint accounting

| Checkpoint | Saved result | Remaining obligations |
|---|---|---|
| 1. Frozen inventory and owners | 17 module-map files, 138 source theorem declarations (134 public, four private), complete source signatures/context/owners and classification for all 138; 24 public types kernel checked | Remaining kernel signatures, four private constant names, and feasibility proofs |
| 2. Simultaneous witnesses | Seven implication statements have joint proof-premise witnesses; 17 unconditional statements have concrete data-domain samples | 114 remain: 30 joint proof-premise cases, 56 data-domain cases, 28 closed fidelity checks; no case is silently excluded |
| 3. Success and trivial implementations | IDENTITY exact output/total success, reject-all and constant-empty negative controls; basic/P256 totality; MODEXP success/gas and BLAKE2F valid-size success/failure | Actual compiler success contract, executable stipend control, full gas/fork and Bridge boundaries |
| 4. Fidelity and verification | Exactly-once partial ledger, frozen source/scope guards, eight scanner regression tests, independent reviews | Full statement-fidelity acceptance, all remaining witnesses, full affected validation, complete queue handoff |

The deterministic source census rejects any module-map or source-byte change from BASE.
Its `preceding_variable_commands` field is lexical history, **not** a list of actual premises:
closed namespace variables can appear there. The new inventory tracks active source scopes separately and retains the effective implicit
Contract binder in all 12 Stipend declarations; full kernel verification is still pending for 114 types.
Private keys are source identifiers, not a claim about Lean's private mangled names.
`Solidity.Stipend`'s implicit `{C : Contract}` is retained in the source context.
All 138 candidates appear exactly once in the off-git statement ledger, including pending rows.

The seven checked originals are `Solidity.Precompiles.words_mono`,
`Solidity.Precompiles.sha256Gas_mono`, `Solidity.Precompiles.ripemd160Gas_mono`,
`Solidity.Precompiles.identityGas_mono`, `Solidity.Precompiles.Modexp.modexp_length`,
`Solidity.Precompiles.Modexp.gas_ge`, and `Solidity.Precompiles.Blake2f.blake2f_length`.
Each witness binds all relevant inputs together with every proof hypothesis and instantiates
that exact unchanged theorem. A successful call's input and output are the same pair throughout.
No independently inhabited premises are substituted for a joint witness.

`BasicWitnesses` and `CoreWitnesses` contain 17 checked named declarations: seven premise
witnesses plus success/control helpers. `DataWitnesses` adds 17 checked named declarations for
unconditional data domains, not extra proof-premise cases. `TypeFidelity` checks 24 anonymous
full-type assignments directly against the frozen constants. `JointPremiseFixture` adds two checked named declarations (one private helper and one joint
numeric fixture), bringing checked named audit declarations to 36. It imports Field only,
so original-statement coverage stays 24. `StipendControl` retains two **unchecked** proposals. No source `sorry`, new axiom, native_decide, or increased proof limit.
Failed elaboration logs can print `sorryAx`; those failures are retained and never accepted.
Accepted new declarations use only the recorded standard propext/Classical.choice/Quot.sound sets.

## Global structures and input feasibility

The stipend obligation takes global gas/failure functions. These are distinct from a feasible
execution on a particular admitted source input. Its Fitted component bounds reported gas;
it does not assert execution success. The proposed negative control sets gas to zero and failure
to True, then uses the already admitted empty body to rule out an empty source-body domain.
This is an abstract contract assignment, not an implemented always-revert compiler.
The control is blocked from kernel checking by the unchanged import closure.

The BLS generic gas theorems need a **single** table with both its length and monotonicity proof,
plus the same k/l relation for msmGas_mono. An isolated kernel fixture now supplies one zero table, cap and k/l pair satisfying all three
constraints together, including the table/cap boundary. It is not an imported BLS theorem
witness: BLS type instantiation and original statement coverage remain pending. No separately
inhabited assumptions are substituted for this joint tuple. Osaka gas_mono likewise needs one p with
LengthPriced p and one related input pair. Its witness remains pending behind BLS.

## Typed owner blockers and decision

Concrete tickets, evidence and delivery state are in
[owner-tickets.json](../../tests/h62/item2/audit-precompiles/owner-tickets.json).

* OBL-SUCCESS: **decision resolved; theorem pending**. The coordinator answered H62 item 2:
  “the totality obligation is met by a SEPARATE compiler-success theorem proved for the owner's
  compiler (it does not reject everything / always revert on the stated inputs); do not change
  any frozen interface statement.” The current owner `claudecloud/move5-20261106/v14-g43` must supply that
  theorem for its actual compiler and stated supported success inputs. Its route is staged pending
  delivery; its qualified name,
  source path, compiler identity and commit remain pending in
  [compiler-success-pending.json](../../tests/h62/item2/audit-precompiles/compiler-success-pending.json).
  The audit will check it alongside the original obligation. Existing precompile totality and
  data-domain samples do not discharge this owner-compiler obligation. No frozen repair is requested.
* DEP-RAW-435: pinned Lean rejects frozen Syntax/Raw String APIs, preventing Stipend imports.
  A partial producer patch is available with verified content hashes, but 30 reported axiom-growth
  entries require root review. No trust acceptance, dependency acceptance or hold lifting occurred.
  The migration Syntax owner must supply the accepted prerequisite; this lane cannot edit it.
* DEP-BLS-435: frozen Bls12381 discount length proofs at 171/172 hit the existing recursion budget.
  The assigned migrate-precompiles producer owns the fix, without raised proof budgets.
* DEP-BRIDGE-435: the frozen optional Bridge pins v4.24 dependencies, and no compatible packages
  are installed in this worktree. Migration/Bridge and live SOL-PC producer coordination remains required.

relay.sh is **host-only**. H70 records the historical recipient plan and corrected current routes in
[h70-waits.json](../../tests/h62/item2/audit-precompiles/h70-waits.json). No local relay call is
needed or attempted. Corrected relays are migrate-syntax, migrate-precompiles, migrate-bridge
and precompile-agreement. The current Claude G43 route is staged, not delivered. Routing grants
no original-file edit permission. Await the actual compiler-success theorem, accepted Raw and
BLS prerequisites, and compatible pinned-v4.35 Bridge dependencies from BOTH Bridge providers.
The scope decision is resolved; the actual theorem/receipts remain pending.
H55-G49 work is untouched. None of these blockers is an exclusion or a weakened statement.

## Toolchain, gates, timings and evidence

The coordinator's five input hashes verified. Official Lean archive SHA256:
`7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d`.
Lean: 4.35.0, release eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
Lake: 5.0.0-src+eb6cafb, Lean 4.35.0. No v4.24 per-master cache was reused.
The owned alternate config disables artifact caches and passes explicit -j1.
The original core and Bridge toolchain files were preserved.

Current evidence directory: `/workspace/h62-audit-precompiles-evidence-4`.
The supplied Raw inline diff and its content-only verification are retained here; previous
evidence-3/delivery-3 and earlier deliveries are preserved unchanged.
The H70 readable per-declaration inventory is `hypothesis-inventory.md`; machine-readable
rows, all binders, package/import/open context and full source types are in `hypothesis-inventory.json`. Both are generated
by committed inventory.py; bulk output remains off git. Source classification is complete,
not the kernel witness/fidelity audit. Previous evidence-2 and delivery-2 are preserved.
The original evidence archive and SHA256 manifest at `/workspace/h62-audit-precompiles-delivery`
are preserved and still verify. Its old census record remains historical, not the current corrected census.
Every bounded receipt contains its full actual command, cwd, exit, wall time and resource fields.
Final proof receipts also bind the exact source import closure and config hashes and reject edits
through the run. The ledger verifies every recorded proof/config/import-source binding before marking seven proof-premise witnesses and 17 data-input samples.

| Evidence stem / command purpose | Outcome |
|---|---|
| census-tests-continuation / python3 scripts/h62/item2/audit-precompiles/test_census.py | Eight tests pass, including frozen scope/source mutation rejection |
| frozen-census / census.py --check | 17 files, 138 declarations, exact frozen bytes |
| basic-final / bounded lake env lean BasicWitnesses | Exit 0; seven declarations, four simultaneous witnesses |
| core-final / bounded lake env lean CoreWitnesses | Exit 0; ten declarations, three simultaneous witnesses |
| data-final / bounded lake env lean DataWitnesses | Exit 0; 17 unconditional concrete-domain samples |
| type-fidelity-final / bounded lake env lean TypeFidelity | Exit 0; 24 direct full-frozen-type assignments, retaining every binder |
| core-signatures / bounded lake env lean CoreSignatures | Exit 0; 24 public type checks with pp.all |
| coverage-mutations-continuation / test_coverage.py | Six tests pass: valid partial input, failed exit, wrong cwd, stale import, failed axiom log, missing data receipt |
| doc-paths / bash scripts/check-doc-paths.sh | Exit 1: existing archived after-roadmap-va1.md reference to absent optional MathlibTest/SplitIfs.lean; owned handoff link resolves |
| receipt-inventory / inventory.py --check | Existing source classification retained; exact waits cover 29 BLS + 12 Raw + 73 Bridge cases, no status promotion |
| receipt-inventory-tests / test_inventory.py | 17 tests pass; partial acceptance and staged-delivery guards retained |
| h70-inventory / inventory.py | All 138 source signatures/binders classified; 114 kernel obligations remain |
| h70-inventory-tests / test_inventory.py | 14 tests pass, including member-vs-data classification, active C, scope endings, closed/private status, failed type receipt and no fixture promotion |
| joint-fixture / bounded lake env lean JointPremiseFixture | Exit 0; one joint table/cap/k/l fixture and private helper, propext only; no original BLS coverage increment |
| coverage-check-continuation / coverage.py | Partial ledger: 138 statements, 7 proof-premise + 17 data-input witnesses, 114 pending; never full acceptance |
| keysort-control-a, keysort-control-b / bounded lean -j1 Solidity/KeySort.lean | Both exit 0, 1.505269 s and 1.509260 s |
| import-prerequisite / bounded lake build Basic and Stipend imports | Exit 1; Raw String API errors at 597/650/665/682/684 |
| osaka-imports / bounded lake build Osaka import | Exit 1; frozen BLS discount proofs hit max recursion depth |
| stipend-blocked / bounded lean StipendControl | Exit 1; missing Rule.olean after failed producer build |
| full-run-lean-fixed / bounded bash ./run-lean.sh using owned lake wrapper | Layer/roots/fragments passed; frozen proof/API failures; stopped only its own group after decisive errors, signal 15 (shell 241), 185.393 s; NOT a passing full gate |

Full-run errors include frozen Hash/CollisionBound, Backend/AbiEntry/RawFreeTransport,
Source/Ctor and Yul/ReservedNames failures. The log preserves all decisive diagnostics.
Earlier failed setup attempts are retained: missing GNU time, quoting error, Node path correction,
and an initial BLAKE witness reduction failure fixed with symbolic list lemmas, without budget changes.

The VM has a 16 GiB cgroup cap and no enabled swap. Owned checks hold the writer lock,
set LEAN_NUM_THREADS=1, and use a per-process 12 GiB address-space cap. The final runner samples
aggregate process-group RSS, 4 GiB available reserve and single Lean worker count every 0.25 s,
stopping its own group on a breach. These are sampled guards, not a separate hard RSS cgroup.
The full-gate sampled peak was about 3.30 GiB, with at least 13.89 GiB available memory.
Older receipts before monitoring was added retain only their original resource fields.

KeySort's same-source/same-runner control delta is +0.265%; no slowdown above 10% was measured.
This is a stability control, not a compiler speedup or a completed migration before/after comparison.
No production refactor or original-source change occurred. Basic/Core/TypeFidelity checks take about 0.50 s each; DataWitnesses took 2.34 s. The H70 isolated joint fixture took 0.51 s.
No RUNTIME_GATE_PASS, full sort-check pass, external EVM test, or cryptographic agreement is claimed.

## Corrected signature census and resolved owner approach

The continuation's full-type checks exposed one audit-parser defect: top-level `let x :=`
inside a theorem conclusion was mistaken for the proof delimiter. The old recorded signature
for Solidity.Precompiles.Bn254.decodeG1_eq_none_iff stopped before its full conclusion.
The scanner now tracks pending top-level let assignments; the regression includes two
successive lets. The regenerated census contains both lets and the polynomial condition.
Only that signature record changed (`census-correction.json`); no frozen source byte changed.
The initial generated full-type file failed before correction; its failure receipt is retained.
The corrected generated file passes all 24 assignments without removed binders or raised budgets.
Local unused-variable lint is disabled solely for these exact-type examples so original unused
proof-binder names can be retained. This does not alter any theorem or proof limit.

## H70 full source classification and receipt waits

The complete source inventory accounts for every declaration exactly once:

| Source category | All declarations | Kernel checked | Still pending |
|---|---:|---:|---:|
| Explicit proof hypotheses | 37 | 7 | 30 |
| Data/type parameters without proof hypotheses | 73 | 17 | 56 |
| Closed statements without input or hypothesis binders | 28 | 0 | 28 |
| Total | 138 | 24 | 114 |

The 37 proof-bearing statements contain 47 top-level proof-hypothesis binders: seven configuration constraints
(BLS hlen/htab in two statements, Osaka hp, Stipend pow h/hq) and 40 per-input conditions. Nested quantifiers remain inside their exact predicate types.
This is a source classification, not proof that any pending tuple is inhabited.
There is no quantified global premise-record binder in these 138 source types. Implementation
FieldOps/NeZero instances, the Osaka.fixed data object and the global Stipend.Obligation
predicate are context, not replacements for per-input validity or actual compiler success.
C : Contract is data and must be the same C used by every dependent typed input.

The full inventory explicitly handles Controls.blake_malformed_lengths.member as a membership
proof; compress_size.h as array data; all 12 implicit Contract binders; both BN254 let
bindings; and all four unresolved private constant IDs. Dependent Loc/Val/Prog/Body domains
have a same-contract caution. identity_unaffordable requires a logical versus feasible-allocation
distinction; pointEval_result needs one real successful KZG input/output pair, not a computed
#guard treated as a kernel hypothesis witness. These cases remain pending.

Closed statements receive no artificial exists-True witness: after receipts they need whole
frozen-statement and axiom fidelity checks. All 30 remaining proof-premise cases must prove
one joint data/configuration tuple; all 56 data-domain cases need faithful input instantiation.
Corrected H70 relays are recorded for migrate-bridge, migrate-precompiles, migrate-syntax
and live SOL-PC precompile-agreement. The previous V14 recipient plan is explicitly historical;
current Claude owner delivery remains staged. No receipt is substituted by routing. New source classification and isolated-fixture work
introduce no original-file changes and do not discharge the V14 compiler-success obligation.

## Corrected H70 wait disposition and partial Raw receipt

No independent queue item was established by this disposition. This update only records the
producer receipt/current routes and refines existing pending hypothesis/source classification.
No Lean job was run, no supplied patch was applied, and no witness/type status advanced.
The same 114 pending cases have exclusive primary wait groups (transitive providers overlap):

| Primary prerequisite | Cases | Proof-premise | Data-domain | Closed |
|---|---:|---:|---:|---:|
| BLS, including PointEval/Osaka dependents | 29 | 10 | 16 | 3 |
| Syntax/Raw for Stipend | 12 | 2 | 10 | 0 |
| Compatible Bridge dependencies | 73 | 18 | 30 | 25 |

The Raw producer head is 72441d298484976c48dd14b4e095c9149b852025; its partial source commit
is 074e62c1840dd2d7ab19c95ca5d437ebfe57dbb8. Supplied patch SHA256
34fc66ea93a8a2c956ebb51f225b03593109239c5b46631aaa28bfb24efb2a9a and reconstructed source SHA256
a463aa0f978da5d5bae6ba5cffdfa95861a495a8d69942502b706b7b157ec506 match. Verification checks
all five hunks strictly in memory against unchanged Raw source. The first inline transcription
had one extra whitespace character; corrected before either hash was accepted. The host path
is not mounted here; identical supplied inline bytes are content-address verified. Producer
Git commit containment and the 30 reported axiom-growth entries were not reviewed here.
[partial-Raw-receipt.json](../../tests/h62/item2/audit-precompiles/partial-Raw-receipt.json)
retains all acceptance flags false and root review pending. Content identity is not acceptance.

The source inventory's 138 signatures, all hypotheses and 24 checked/114 pending statuses
remain unchanged. Seventeen inventory regressions plus eight census and six receipt tests
now pass (31 total); guards prevent partial availability or staged routes from advancing status.
Wait specifically for claudecloud/move5-20261106/v14-g43's actual compiler-success theorem
for Solidity.Stipend.Obligation; migrate-syntax's accepted Raw prerequisite; migrate-precompiles'
actual Solidity/Precompiles/Bls12381.lean:171/172 prerequisite (the disposition used the shorter
Solidity/Bls12381.lean label); and compatible pinned-v4.35 Bridge dependencies from
migrate-bridge AND precompile-agreement. Holds and original-file permissions are unchanged.

## Reviews and continuation handoff

Independent finder and skeptic reviews were read-only, used no Lean server/build, and confirmed
seven statement-faithful proof-premise witnesses, 17 unconditional data-domain samples,
24 direct full-type checks, and the narrow negative-control interpretation. Their findings
were fixed: mutual block namespace handling; comment offsets; section-variable overclaim; frozen
module-map/source guards; resource evidence wording and sampled monitoring. The scanner regression
line-number typo was corrected. Continuation reviews independently confirmed the let-signature
fix, separate witness counts, and the coordinator-resolved separate owner theorem requirement. H70 finder/skeptic reviews independently checked all 138 source signatures and every remaining
114 row; both confirmed the 30/56/28 split, proof-role counts and isolated-fixture limit.
The sole caution improvement (Val C in pow_not_fits) was added and regression-tested.
Their final review text is saved off git in reviews.md.

The original assignment remains unfinished, but this worker is explicitly retired/paused.
Only the successor/coordinator may arrange authorized continuation after the final handoff;
this worker must not resume, create/reset a goal or launch a replacement. Original prompt digest:
39585f8ffb6629c51fc8d1e0fca1808807d9cb06983d0c558dcdc019112450f3.
Original VM/environment:
ccarenv_b64_Y2NhcmVudl83YjM2Yzc3YzA3Njg4MTkxODg3Yjc3MTBhZWVkNzdhMg.
get_goal is not exposed; the goal objective in this thread is authoritative.
The final stopped/head acknowledgement transfers the saved scope to the named successor,
who is responsible for integration and any authorized continuation. This is not permission for
automatic implementation in the retired worker. Successor open work includes the migration
prerequisites and pending actual compiler-success theorem from the current Claude G43 owner, then
finish 30 joint proof-premise cases, 56 data-domain cases and 28 closed fidelity checks,
complete exact kernel types/private names,
Bridge/gas/fork/compiler boundaries, independent milestone reviews and all final passing gates.
The assignment remains blocked, not complete; the 8-10 hour useful queue has not been exhausted.

## Successor checkpoint: authenticated intake and frozen-v4.24 evidence

The exact final head `bd86434e0f193422309f15bad579c171cac2eb3b` was fetched from its
published lane branch and merged as `b6019bd1a3b9908af3d74700ae62660c6e3ce6cc`.
Frozen rendered prompt SHA25639585f8ffb6629c51fc8d1e0fca1808807d9cb06983d0c558dcdc019112450f3
and scope SHA25630e1b7cf905fbd4915b265ffd0acdbb5241bdaaa6213f51016d9d4aa199e67c4
match the final relay. All 557 H82b metadata-file hashes and the archive/manifest
hashes match. Final stop/pause/quiescence is authenticated; the retirement barrier
is resolved. Historical off-git executable/cache/evidence artifacts were not
received, and their old gates are not claimed reverified from those bytes.

Five completed work items are: final-member intake; fresh reproduction of the
24 existing applicability cases; ten IDENTITY applicability cases; whole-type
fidelity for all 73 Bridge declarations; and the existing abstract Stipend
negative controls. The latter needed four missing core products and a stale
Scoped object refreshed from unchanged sources. Cache-enabled and no-cache Lake
commands returned0 while leaving products absent; those mechanical exits are
not treated as successful imports. Actual direct materialization and final
Stipend control elaboration succeeded. No producer source or frozen statement,
definition, interface, budget, axiom set or exclusion was edited.

The new IDENTITY cases construct all data and each hypothesis jointly for the
same input: six proof-premise witnesses and four data-domain samples. They retain
the full original conclusions. Nonempty input, exact/short gas and a reject-all
flag-function control are checked. The huge-array case is symbolic mathematical
inhabitance, not a claim of executable allocation or practical feasibility.
The reject-all flag function is not an actual compiler; G43's separate actual
compiler-success theorem remains required. The two Stipend controls are also
abstract parameterized controls, not twelve new original-case witnesses.

[BridgeFidelity.lean](../../tests/h62/item2/audit-precompiles/BridgeFidelity.lean) directly checks all 73 full frozen types. Four private terms
resolve the unique actual imported kernel constants and undergo ordinary term
checking at the entire expected type; no axiom or declaration is substituted.
Twenty-five closed statements receive fidelity checks, not fabricated exists-True
witnesses. Cumulative fresh accounting is 13 joint-premise cases,21 data samples,
25 closed-fidelity cases:59 distinct accounted cases,79 pending. Full-type checks
cover97 declarations; that is a separate measure, not97 applicability witnesses.

A fresh focused axiom audit also passes all204 imported Bridge declarations,
including private helpers, against only propext,Classical.choice andQuot.sound.
All results here target the unchanged Lean4.24.0/Lake5.0.0 frozen setup. They do
not establish v4.35 migration compatibility, accept the partial Raw receipt or
its30reported axiom-growth entries, supply native crypto/FFI equality, or discharge
H45/full-build/owner-success waits. No RUNTIME_GATE_PASS or full-audit claim.
KeySort passes freshly; no new module exceeds60s. The small proof cleanup measured
2.538s to2.542s under the same guard (+0.16%); different-monitor or different-version
runs are not used as a regression baseline. No proof budget was increased.

Acceptance checks the exact pinned executable/argv, tool hashes/versions, complete
input closures, log hashes/markers and measured resource bounds. Finder/skeptic
found optional closure and permissive receipt checks; these were fixed. Twenty-one
mutation tests reject omitted/substituted closures, query commands, altered logs,
wrong tools and resource failures. Six inherited receipt and eight census tests
pass freshly. Bulk output is off git under successor-evidence/, with generators
and checksum-bound summaries in git. See [successor-summary.json](../../tests/h62/item2/audit-precompiles/successor-summary.json),
[successor-intake.json](../../tests/h62/item2/audit-precompiles/successor-intake.json),
[successor-registration.json](../../tests/h62/item2/audit-precompiles/successor-registration.json)
and the final successor handoff.

Continue the same VM/branch/goal in a fresh thread after this five-item milestone,
as the frozen handoff policy requires. Ready work remains: Bytes10,Gas11,Header16,
malformed-membership1,BLS/PointEval/Osaka29 and Stipend12 original cases at the frozen
pin. Do not mark blocked or complete while these independent cases remain.
No retired goal is woken, recreated or reset. No Claude source edit/message, master
push or host cache shipment occurred.

## Bytes/Gas and Header/membership continuation, 2026-11-06

The next 38 original cases now pass at the unchanged frozen4.24 pin: Bytes10,
Gas11,Header16 and malformed-membership1. These construct12joint-premise and
26data-domain witnesses; the general word-rounding lemma is not counted as an
extra original case. Current exactly-once totals are25joint,47data,25closed
fidelity =97accounted/138,41pending. Full-type coverage remains97, a separate
measure. No source statement, body, interface, budget, axiom set or exclusion
was changed. New modules name the guarded regressions in their docstrings (H90),
and no roadmap/phase folder or core dependency was added.

[BridgeBytesGasWitnesses.lean](../../tests/h62/item2/audit-precompiles/BridgeBytesGasWitnesses.lean)
retains both word-size/affordability bounds, all original conclusions, private
list-loop data and actual success flags in error-capable gas projections.
Its general rounding lemma applies to every n. All22 public axiom guards pass.
[BridgeHeaderWitnesses.lean](../../tests/h62/item2/audit-precompiles/BridgeHeaderWitnesses.lean)
uses17guards and keeps padding, four-byte common domain and one-byte zero-header
exception distinct. Validation size/flag/gas are constructed together for one
input; flags0/1,flag2,insufficient gas,invalid size and membership are inhabited.
A general header decoding lemma avoids opaque computation. Compression outputs
are not equated to crypto implementations. Actual private constants are reused
through ordinary term checking. Final checks took2.762s and4.520s respectively,
no resource stop or budget increase. Initial failures and passing receipts remain
off git; none is an unchanged timing STOP.

Acceptance requires both new genuine receipts, exact commands/tool identity,
complete frozen input closure, log hashes/markers and measured resource bounds.
Twenty-five failed/stale/missing/query receipt mutations pass. Finder/skeptic
read-only proof reviews found no meaning, vacuity, scope or H90 issue.

H70 updated disposition: H85/H86 replace the old H45 blanket hold with the fixed
host bridge-build.sh package/user allow rule and unchanged lane budget. These
have not been verified or executed by this worker. All Raw/BLS/Bridge migration
waits now belong to migrate-root-gate; retired producer goals are not contacted.
Historical raw-evidence absence is a regeneration limitation underH86. Actual
G43 compiler success remains staged for forwarding; Exp integration is separate.
Current continuation/handoff: BYTES-GAS-HEADER-HANDOFF.md under the audit tests.
Ready work remains29 BLS/PointEval/Osaka and12Stipend cases; no full-goal,
full-build, migration435, native-crypto or actual-compiler claim is made.


## Frozen v4.24 applicability completion; final integration blocked

The successor now accounts for all138 original statements exactly once:
37joint witnesses,73data-domain samples,28closed fidelity cases. All138 full
types are checked separately. PointEval has an actual infinity input decoder
and verification proof, with gas price and malformed controls; no crypto equality
or actual compiler-success premise was added. General public-law composition
avoided four preserved memory-exhaustion attempts without budget increases.

Finder and skeptic read-only reviews pass; skeptic gas-price wording correction
is applied.26receipt-mutation tests and14inherited census/coverage tests pass.
Full validation remains open: core cache targets out-of-date, host Bridge wrapper
execution/allow rule unverified, actual G43 compiler-success missing, migration435
API/axiom evidence pending and five external documentation references missing.
No whole-goal completion or RUNTIME_GATE_PASS is claimed. Exact commands,
failures, limits and remaining producer/setup waits are in
`tests/h62/item2/audit-precompiles/ALL-CASES-HANDOFF.md`.
