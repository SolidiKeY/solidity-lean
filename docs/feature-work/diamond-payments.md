# Diamond payments: guarded rules and the original PiggyBank callback proof

## Portable payment regression setup repair (2026-10-30)

Attempt 27's required `payment-reference.test.mjs` gate failed three checks
before compilation because it assumed a sibling SolKey checkout. The focused
repair uses the verified repository snapshot and its unchanged 0.8.34 Gradle
pin. The payment source/fixture and reference replay checks now locate the
unchanged 0.8.38 compiler through `scripts/test-compiler.mjs`, using
`.lake/soljson/`, `SOLJSON_DIR` or `SOLC_REFERENCE`. Missing or mismatched
compilers still fail; no guard, observation, assertion or budget was removed.
[Setup instructions](../solidity-upstream-tests.md#reproduce) document both
exact compiler files, their hashes, overrides and prerequisite artifacts.

Focused results, with compilers copied locally only after hash verification:

| Check | Result |
| --- | --- |
| `node --test scripts/payment-reference.test.mjs` | Exit 0; all 4 tests, 5.50 s. |
| `node --test scripts/evm-reference/payment-replay.test.mjs` | Exit 0; all 7 tests, 1.00 s. |
| `node --test scripts/evm-reference/replay.test.mjs` | Exit 0; all 14 tests, 1.00 s. |
| `node scripts/payment-source-fixtures.mjs --check` | Exit 0; exact existing AST bytes, 0.50 s. |
| Source-world test invocation | Exit 1; 5 checks pass, resume check refuses the runner's explicit prerequisite build. |
| Compiler negative controls | Wrong SHA and missing locations rejected. |
| Layer check and diff whitespace check | Exit 0; 172 core modules, none reaches the elaborator. |

The source-world invocation included a negative-lookahead name filter intended
to select five checks, but the runner also executed the resume test. Its full
exit remains failed; no subset pass substitutes for the required full gate.
The coordinator owns that prerequisite build, the resume recheck and combined
gates. This repair's local wrapper permits only no-build Lean probes and adds
`-j1`. One check ran at a time under the inherited 12 GiB/no-swap cgroup and
12 GiB host reserve monitor, with `LEAN_NUM_THREADS=1`. The focused sequence
sampled at most 1,380,044,800 bytes of cgroup usage and at least 34,488,840,192
bytes of available host memory. Logs and samples are in
`.lake/payment-portability/` and `.lake/payment-portability-replay/`.
Earlier sandbox process-control failures and an accidentally removed path
import caught by replay tests are retained separately; the import was restored
before the final 14-test pass. Optional EVM dependencies were installed from
the existing lock with offline `npm ci --ignore-scripts`.

The supplied retrieval and coordinator manifest hashes, seven artifact hashes
and eleven coordinator file hashes were reverified. The original checksum
manifest still verifies exactly 175 source records. Source/base commits,
bundle head, executor/thread identity and provenance agree. Coordinator
baseline evidence remains separate from original checksum coverage; the
documentation scans remain failed with 26 identical findings and zero new
findings. Source-VM OS headroom and the LOCAL host reserve remain distinct.
No historical gate or new combined validation pass is inferred.

Independent read-only finder and skeptic reviews used no Lean server. Neither
found a pin, observation or semantic weakening; the finder requested the setup
documentation added above. Both final read-only refreshes found no remaining
defect or code/documentation mismatch. No Lean source was edited, so no Lean MCP document
was opened. The existing registration repair below is already in the candidate.
No index, commit, remote branch, source VM, skill or monitor is changed, and
there is no pending semantic decision.

## Core layer registration repair (2026-10-30)

The retained review of candidate `e6fb7d45` correctly found that
`Calculus.PaymentWitness` and `Calculus.PaymentConditions` were absent from
`scripts/check-layers.mjs`'s `CORE` patterns. The focused repair registers both
and updates the core list in [parallelism.md](../parallelism.md). The layer
check now covers 172 core modules (previously 170), with none reaching the
elaborator. An in-memory negative control runs the actual checker with each
payment module importing `Syntax.Elab`; both paths are reported and it exits 1.
`git diff --check` passes. No Lean source, semantic condition or budget changes;
no Lean check or full combined build is needed for this registration edit.

The supplied supplement retrieval and coordinator-context manifest match their
pinned SHA256 hashes. All seven supplemental artifacts, 177 archive members
and eleven coordinator-context files verify. Source/base commits and executor
environment/thread identities agree; exact Git tree and scanner hashes agree
with the retained comparison. The original checksum manifest still covers
175 records only. Both documentation exits remain 1, with 26 identical findings
and zero new findings at the exact source/base commits. The separate coordinator
evidence supplies no original historical execution or passing global gate.
The frozen source prompt excludes the local host's extra 12 GiB reserve from
source-VM requirements; the local integration reserve remains required.

Fresh independent read-only finder and skeptic review launches both failed with
`invalid thread-store request: no rollout found`; no new independent review is
claimed. The coordinator must obtain both reviews and owns staging, fresh
combined validation and candidate approval. This repair makes no commit or
publication and requires no semantic decision. Retained integration regression
logs still record stale-target rebuild failures; they remain failed evidence,
and this repair runs no competing rebuild.

## Integration boundary (2026-10-29)

The combined candidate `cec7507b` failed the frozen verdict/scope guard: it
registered `PaymentCorpus.breakPiggyBank_callback` as the original `.key` case,
changing both its verdict and source mapping. The integration base is
`204eb154`. The repair removes that registration and restores
`tests/solkey/expected.tsv` byte-for-byte from that base. PiggyBank remains
`unsupported`, with source `solkey net/piggybank-breakPiggyBank-withcallback.key`;
the generated totals are again 72 proved / 35 unsupported / 101 unported.
The frozen reason describes the corpus adapter, not the capabilities of the
separate typed term language. No source/snapshot pin or guard is changed.

The retained snapshot's `net/PiggyBankNet.sol` and
`net/piggybank-breakPiggyBank-withcallback.key` supply the correspondence:
the typed theorem transcribes the eight fields, payment-last body, invariant,
zero-value entry update and owner-not-self assumption. It uses `ValidC piggyInv`,
which assumes invariant-preserving callback resumptions and omits the other
source functions. It does not prove an import/translation equivalence for the
original corpus obligation or the omitted functions' invariant preservation.
Keep it as separate kernel evidence, reachable through `Solidity.lean`, with
the guarded rules and their soundness proofs. `SolidityCorpus.lean` retains the
four existing Net proof references and no PaymentCorpus registration.

Earlier source-branch validation below is retained as historical evidence.
Its accepted PiggyBank pin improvement and associated review conclusions are
superseded by this frozen integration boundary. The failed guard remains in
the coordinator's integration ledger; it was not a passing combined check.
The coordinator owns the full combined gates after this focused repair.

### Refreshed integration recheck (2026-10-30)

At `6d5f631d`, the registration repair is already present. Against the refreshed
integration base `fb379ae2`, `tests/solkey/expected.tsv`,
`docs/solidity-scope.md`, `lakefile.toml` and `lean-toolchain` all match
byte-for-byte. The generator reproduces all ten generated corpus files exactly;
`node --test scripts/payment-corpus.test.mjs`, frozen snapshot hash verification
and the complete static TestSuite gate pass (552 derived, 11 refuted,
1 excluded, 2 skip, zero pending). The test initially failed because the sandbox
blocked its Node child process with `EPERM`; the unchanged host rerun passed.
The recheck record is `.lake/integration-repair/frozen-refresh-check.json`.

No Lean source needs another edit for this discrepancy. The earlier retained
`SolidityCorpus.lean` MCP diagnostics are partial, with no reported errors;
they are not a completed check. Fresh finder and skeptic review launches both
failed with `invalid thread-store request: no rollout found`; no new independent
review is claimed. Earlier review evidence and failed logs remain intact.
The coordinator must complete independent reviews and full combined gates.
This recheck introduces no semantic decision, commit, index write or guard waiver.

### Review repair and evidence boundary (2026-10-30)

The review of `1b561734` identified missing explicit types in the combined
payment additions. The focused repair annotates the local facts in
`Calculus/CallbackSound/Payments.lean`, `Calculus/PaymentConditions.lean`,
`Calculus/PaymentWitness.lean` and the PaymentRules/PaymentWitness tactic
examples, and gives PaymentSource's `fundingRun` its result type. PaymentClose
inlines the owner-frame rewrite and types its dynamically inferred integer
equality. The theorem statements, observations, target predicates, invariants
and budgets are unchanged. All seven edited files pass complete per-file Lean
MCP diagnostics, one open document at a time with `-j1`; all 45 printed axiom
audits contain only the standard axioms. No full combined build was run here.
The coordinator's combined gates must include `Examples/Tactics/PaymentCorpus.lean`,
which exercises `sol_payment_close`; checking the edited tactic quotation alone
does not exercise that caller.

The requested bytecode regression suite passes all seven tests, and pinned
source AST regeneration with `--check` passes. The source-reference and
source-world regression commands exit 1: their no-build probes require stale
artifacts to be rebuilt (`SolSpec`, `FunContract`, `ProveChunked`, `LazyStorage`
and `Tools.PaymentReplay`). The source-world resume test also requests an
explicit build, which the repair's local wrapper refuses. These are retained
failures, not passing regressions; the coordinator owns rebuilding and rerunning
the combined gates. The compiler download matches the unchanged 0.8.38 SHA256
pin. Raw diagnostics, failed and passing test output, Lake failure output and
sampled regression resource records are checksum-bound in
`tests/upstream/diamond-payments-integration-20261030/manifest.json` and its
adjacent archive. These records concern this integration checkout only.

The initial retrieval indexed zero raw-evidence members (one container maps to
an empty list). The supplemental evidence audit below supersedes that absence;
the original retrieval and integration-repair archive remain intact. The later
coordinator-evidence repair below verifies the documentation comparison and
corrects resource attribution; it does not turn failed gates into passes. No
source VM, skill, monitor, external index, commit or remote branch is modified
by this repair.

Independent read-only finder and skeptic reviews found no remaining repair
defect or new semantic decision. Both caught an ambiguous count of the original
retrieval index: its one container key holds zero raw-evidence members. The
wording and manifest now report both counts explicitly. The skeptic also
required the PaymentCorpus caller check in the coordinator's combined gates,
as recorded above. Neither review used the Lean server.

### Supplemental original-evidence audit (2026-10-30)

At `3c0af8ff`, the supplied immutable supplement's retrieval SHA256 is
`9d762c79c1c3aaaaa8e14fc56e704cb2ab7578e365d5455672ff0faf41f8f9e1`.
All seven artifacts match their recorded sizes and hashes. Its archive contains
177 verified members: the original 175 records, their checksum manifest and
snapshot provenance. Every original path and hash agrees with the retained
175-record manifest (SHA256
`0ae506f378730c2a813f4c12de0acd859a924f3dc4e56508a2b92ef07291a8b3`).
The archive and retrieval are retained beside the integration manifest as
`original-source-evidence.tar.gz` and `supplemental-retrieval.json`.
`original-evidence-verification.json` records member hashes and the audit.

All three named original source reports are complete and working in legacy and
viaIR. Their paired bytecode reports cover every declared required profile;
all reported observation and gas matches are true, and compiler/snapshot
provenance agrees. Original build, gate, proof/axiom and cgroup resource logs
are now available. The retained trust audit reports 545 headline theorems using
only standard axioms; the repaired imported-constant audits pass. Earlier
failed scratch-relocation audits remain in the archive. These are inspected
historical records, not new checks of the combined candidate.

The documentation gate exits 1 with 20 missing references. Its final and
reviewed logs are identical. The original 175-record manifest contains no
baseline raw log and explicitly excludes the unlisted historical checkpoint.
The separately pinned coordinator evidence below supplies extra baseline bytes
and an exact-commit comparison, without expanding that original coverage.

The original summary reports 8,598,601,728 bytes of available host memory
during a heavy build. The source assignment requires a 12 GiB hard cap, no swap,
serial Lean and VM OS headroom; it explicitly excludes the local machine's
extra 12 GiB reserve from the per-VM requirements. The earlier attribution of
historical reserve noncompliance was incorrect. The raw cgroup log measures
usage, not continuous host available memory, and establishes no such samples.
The LOCAL integration host still requires its full 12 GiB available-memory
reserve. No resource budget or gate is waived. Earlier integration regression
failures remain recorded; the coordinator owns full combined gates.

Fresh read-only finder and skeptic review launches both failed with
`invalid thread-store request: no rollout found`. No independent review of this
supplemental audit is claimed; the coordinator must complete those reviews.
Artifact/member hashes, paired-report completeness and reported matches,
unchanged hashes for the seven previously repaired Lean files, and
`git diff --check` pass. The current combined tree's documentation path check
exits 1 with 46 missing references and no findings in these payment files;
this is separate from the original source run's 20-reference failure.

### Coordinator evidence correction (2026-10-30)

The independently pinned context manifest has SHA256
`616cae7d7f64b8ae733455cac84e2f3392fb6dc91c6e3ead13066e026564706b`.
All eleven listed files match their hashes; source/base commits, executor
environment and thread match the immutable supplement. The exact manifest,
extra records, frozen source prompt and fresh comparison logs are retained in
`tests/upstream/diamond-payments-integration-20261030/coordinator-evidence.tar.gz`.
Its adjacent `coordinator-evidence-verification.json` records hashes and scope.
The original supplement, 175-record checksum manifest and archives are unchanged.

The extra retrieved baseline log names base `f4dee4a2` and reports exit 1;
its separately retrieved comparison reports 20 identical missing references
and both exits 1. These records have separate coordinator retrieval provenance,
outside original source checksum coverage. They do not authenticate the time
or execution of an original historical baseline run.

The coordinator's fresh comparison and this repair's independent recomputation
use exact committed base `f4dee4a2` (tree `3386c829`) and source `20bbb107`
(tree `299f250a`). All 3,508 snapshot blobs verify against Git object identities,
and the unchanged scanners reproduce both retained logs byte-for-byte. All
26 findings (20 missing references and six ambiguities) match the original
source log and extra baseline log; zero findings are new. This establishes
unchanged findings at those commits, not an original historical execution.
Both documentation exits remain 1. The global documentation gate has failed.

`evidence_verified` now records the verified records and comparison.
`original_validation_verified` remains false because the required documentation
gate failed, rather than because a baseline comparison is unavailable.
The former missing-comparison and source-reserve prerequisites are closed on
that limited basis. Earlier reviews and checks do not approve these new edits;
fresh reviews are recorded below, and coordinator combined gates remain required.
This repair changes no Lean source and runs no Lean checks or full build.

Fresh read-only finder and skeptic reviews of this correction found no remaining
defect or new semantic decision. The skeptic independently recomputed the same
26 findings from all 3,508 committed Git blobs. The stale top-level manifest
prerequisite was cleared, and its original retrieval counts and earlier
validation/reviews are explicitly labeled historical. Neither reviewer used
the Lean server. The current worktree documentation scan still exits 1 with
46 missing references and 37 ambiguities, with no payment-file findings;
hash links, unchanged Lean-file hashes and diff formatting checks pass.
These reviews cover this evidence repair; the coordinator still owns fresh
combined validation and approval of the resulting candidate.

### Combined payment-closer regression repair (2026-10-30)

Attempt 25's checksum-verified build log fails in the unchanged PaymentCorpus
caller because the local payment closer quotes `Eq Int _ 2`. `Eq` takes its
type argument implicitly, so this applies a proposition as a function when
the tactic runs. The focused repair writes `(_ : Int) = 2`, retaining the
same state-value lemma, proof search, invariant and budgets.

Per-file MCP diagnostics on PaymentClose pass without warnings or errors.
To check the actual failed caller against the edited tactic without loading
a second document or using stale imported tactic code, a temporary probe
appended the exact PaymentCorpus declarations and their existing imports to
that same file. All declarations check; the three existing axiom prints
report only `propext`, `Classical.choice` and `Quot.sound`, without `sorryAx`.
The probe and extra imports were removed, and final per-file diagnostics pass.
Raw probe/diagnostic records are local under `.lake/integration-equality-repair/`.
PaymentCorpus and its theorem statements remain unchanged. No full build or
combined gate is claimed; the coordinator must rerun those gates.

The supplied context manifest, all eleven context files, the supplemental
retrieval, all seven artifacts, all 177 archive members and the original
175 checksum-listed records were reverified. Source/base commits and executor
identity agree. The frozen prompt distinguishes source-VM headroom from the
LOCAL host's required 12 GiB reserve. A fresh exact-commit documentation
comparison is recorded beside the probe: both exits remain 1. No original
checksum coverage, historical execution claim or review approval is added.

Fresh independent read-only finder and skeptic launches both failed with
`invalid thread-store request: no rollout found`. Independent review remains
pending with the coordinator. Local read-only inspection confirms the probe
replays the unchanged caller, and the final diff contains only this equality
annotation and its milestone record. No semantic decision is required.

Current scope after the explicit human decision on 2026-10-29: keep existing
semantics and prove exact conditional success and certified failure conditions.
For this assignment only, that replaces the unconditional transfer-success
requirement. The original unconditional statements and their refutations remain
unchanged evidence. The semantic-choice blocker is resolved, not awaiting another
profile decision. The new exact family and source-reference repair are below.
Original observations, callback judgment, target predicates and budgets remain.
The two remaining original source rows now execute through a narrow typed
world-source bridge, with kernel witnesses and paired independent bytecode/gas
validation. All three named source rows pass both required pipelines. Earlier
validation and blocker lists below are historical checkpoints; the final source
bridge milestone records the current bounded scope and actual checks.

Baseline: `f4dee4a29c2e208b36db4a4161a4723c735cd775`, origin
`https://github.com/SolidiKeY/solidity-lean.git`, branch
`codex/next10-diamond-payments`. Lean 4.24.0, Lake 5.0.0-src+797c613.

## Checkpoint 2edd52bf: historical record

All subsections until the resumed milestone record the earlier witness-only
checkpoint, including its then-blocked PiggyBank attempt and then-current pins.
They are retained as evidence history, not current scope or validation claims.

### Proved scope

`Calculus/PaymentWitness.lean` contains semantic rules over the existing intrinsic
run and callback relation. Deterministic transfer normal completion is equivalent
to fundedness/recipient acceptance and the booked postcondition. Deterministic
send returns the actual accepted/refused outcome. Callback transfer has an exact
characterization by acceptance, invariant on exit and every invariant-preserving
resumption. Callback send sufficiency requires both success and failure
continuations, including accepted-but-reverted sends. No alternate interpreter,
formula language or assumption about gas sufficiency is introduced.

The callback resumption quantifies storage, ledger **and balance** (`sb`), matching
current `State.havoc`. Stipend sends fork only under the selected callback option;
full-gas value calls fork under either option. Deterministic send exactness is
not a theorem about `ValidT.noCallback` for full-gas calls.

`Examples/Tactics/PaymentWitness.lean` proves funded payout effects, ledger
invariant preservation with callbacks, insufficient-balance and recipient-revert
countercontrols, failure preserving funds/ledger, accepted sends that may fail,
callback replacement of the ledger, and broken exit invariants. These are kernel
payment-boundary proofs, not full proofs of the three original callback contracts.

### Exact dependencies left

SolKey `transferNoCallbackDiamond` and `transferWithCallbackDiamond` have no
fundedness/recipient-acceptance premise. A positive transfer from zero balance,
or a funded transfer answered by `.other []`, reverts in the existing runtime.
The new countercontrols prove why unconditional booking is not a sound port.
A registered rule needs formula-level acceptance evidence linked to the typed
transaction oracle and balance, plus notation/printers, dispatcher and sequent
integration. No new oracle atom or narrowed reading is fabricated here.

`piggybank-breakPiggyBank-withcallback`, `casino-decideBet-withcallback` and
`auction-makeBid-withcallback` remain at their original unsupported pins. Their
complete bodies, msg.value entry booking and exact CInv instantiation still need
proofs through the corpus adapter. The generated reason saying no term reads
`net` is stale: ledger formula terms already exist. The missing proof/adapter is
not evidence that the ledger primitive is absent. The local nonpositive-ledger
witness specializes the payment boundary of `net-call-withcallback-simple`; it
does not claim that original whole-function problem is ported.

### Validation and review

Runtime gate: `lake build Solidity.KeySort` passed before edits in a Docker
cgroup reporting memory.max=12884901888 and memory.swap.max=0, peak 24371200
bytes. Lake rejects a build-level `-j1`; a temporary TOML passes `-j1` through
weakLeanArgs, with LEAN_NUM_THREADS=1. The failed syntax attempt is retained.
Writer lock: `/tmp/solidity-lean-feature-groups-20261025/writer.lock`.
Caches remain on disk. No build runs concurrently with Lean MCP.

Final per-file MCP diagnostics pass for both new modules. Actual axiom outputs
for all five rule theorems and the headline controls contain only propext,
Classical.choice and Quot.sound. Initial failed diagnostics are retained and
are not passing audits. The existing dependency build passed 116 jobs; its
log spans 410.34 seconds by file timestamps.

Independent read-only finder and skeptic reviews used neither the Lean server
nor checks. They confirmed the missing acceptance premise and required
accepted-but-failed send controls, exact callback transfer conditions and
unrestricted balance havoc. Those findings are reflected in the witnesses.
Final review and remaining gate outcomes are recorded below when available.

Shared edits: two imports in Solidity.lean; additive module-map rows; narrow
rule-map/kernel-port/options/calls-exceptions documentation; two partial inventory rows
gain local evidence. Generated outputs are `Solidity/Language/Features.lean`
and `docs/solidity-feature-inventory.md`, regenerated by the audit script.
No shared syntax, runtime, dispatcher or tactic file changes.

External evidence directory: `/workspace/diamond-payments-evidence/`.

Final read-only finder and skeptic reviews found no soundness defect or support
inflation. The skeptic requested that both regenerated inventory outputs be
listed explicitly in the shared-edit record; that correction is applied.

### Focused upstream results

The KeySort runtime gate preceded edits. Source fixtures were subsequently
reproduced in a separate untouched baseline worktree at the exact published SHA,
then in the task checkout. Their results remain blocked; no required pipeline
or ordered observation was deleted to obtain a pass. Reports are in
`/workspace/diamond-payments-evidence/{baseline,after}/{0,1,2}/results.json`.

| Fixture suffix | Baseline | After | Preserved blocker |
| --- | --- | --- | --- |
| `functionCall/send_zero_ether.sol` | blocked | blocked | transaction/block/self-address or cross-contract host behavior not adapted |
| `expressions/uncalled_address_transfer_send.sol` | blocked | blocked | same host adapter blocker |
| `revertStrings/transfer.sol` | blocked | blocked | unadapted `revertStrings=debug` setting |

Each runner invocation exited 1 because its fixture remained blocked. The first
baseline invocation took 78.104 seconds; the other five took 0.842–1.212 seconds.
The measured group peak through these runs was 1,247,952,896 bytes. Compiler
0.8.38+commit.1835d247 was SHA-checked against
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`. These are
source adapter classifications, not successful source execution or EVM evidence.
The kernel proofs are separate and do not claim gas or bytecode correspondence.
No runtime/compiler/runner source changed. Full pipeline execution remains
blocked by the named existing prerequisites.

### Original PiggyBank proof attempt (blocked)

The scratch obligation included the original eight fields, complete method body,
preconditions, parallel zero-value entry booking and invariant (one equality
reversed symmetrically). Both independent read-only reviewers confirmed fidelity.
Omitted helpers do not narrow this single-function abstract callback target: the
reading assumes invariant-preserving resumptions; it does not prove every helper
keeps the invariant or establish whole-contract reentrancy safety. This is a
manual typed transcription, not compiler/EVM correspondence.

With `CallbackDerive` loaded, default `sol_prove` discharged resumption but left
the invariant-on-exit sequent open, after entry booking, all original guards and
captures, `state := 2`, receiver capture, and `pay(se10,se4)`. The complete leaf
is retained in `piggy-probe-2.log` (the three-candidate probe took 121.681 seconds).
The optional reduced-leaf pretty-print hit the unchanged 200,000-heartbeat limit
in 104 seconds; removing that print still hit the same limit at the closer.
No limit, target, invariant or expected verdict changed. The exact dependency is
a bounded proof/closer repair for that recorded invariant-exit sequent. No
refutation is claimed. The failed prototype is outside the checkout as
`/workspace/diamond-payments-evidence/PiggyBlocked.lean`; no unfinished theorem
is imported or committed. All original callback corpus pins remain unchanged.

The success send control now starts with `ok=false` and proves the true result,
ledger -5 and balance 5. Its paired failure witness uses exactly the same state,
invariant, option and operands. The separate `noCallback`/full-gas failure control
still starts with `ok=true` and proves the false overwrite. Both new controls
pass per-file MCP and use only the standard three axioms.

### Cold full confirmation

`./run-lean.sh` exited 0 in 8,821.350 seconds: 687 default jobs, 259 TestSuite
jobs, 377 parsed taclets and all 131 read-bearing annotations matched.
`lake env lean --tstack=131072 -j1 TrustAudit.lean` exited 0 in 96.313 seconds;
529 headline theorems use only the standard axioms. The cgroup peak reached the
12 GiB cap (12,884,901,888 bytes); memory-pressure events occurred, with no OOM
or OOM kill. `OpenLoops` passed in 542 seconds, `DecisionHashes` in 286 seconds
and `Decision` in 612 seconds. This is a measured cold pass at the cap, not an
established margin below it. Actual output and counters are retained.

The first corpus invocation exited 1 because the saved copied snapshot lacks
its adjacent `.pin.json`. The committed snapshot under `tests/migration/solkey`
has its original sidecar and identical PiggyBank source/key hashes; the retry
uses that snapshot without changing setup files or re-pinning. The first trust
and diff scans also exposed Docker bind-mount ownership checks. Their retries
use a command-scoped Git safe-directory entry for this authorized checkout,
without changing the user's Git configuration.

Final finder and skeptic review confirmed the strengthened paired controls.
The skeptic also corrected the callback summary's exhaustive-sounding exception
list: it now states that nonforking statements reuse the deterministic run and
payment/control constructors use relational clauses, covering sends and paying
loops/blocks accurately without changing those rules.

Warm final `./run-lean.sh` confirmation exited 0 in six seconds after the paired
control edit. The timed strict automation gate passed all 26 freshly timed
TestSuite modules against the unchanged 300-second per-module budget: 491
automatic, 61 existing step-budget replays, zero manual, 11 refuted, zero pending.
The repaired trust scan passed 716 sources and 240 inventoried sites with zero
findings; the committed-snapshot corpus consistency gate passed in 88 seconds
(72 proved, 35 unsupported, 101 unported), retaining every original pin.

### Final artifact state

Final MCP diagnostics pass for `Solidity.lean` and generated
`Solidity/Language/Features.lean`. Final structural checks report 702 reachable
modules, zero orphans, and 152 core modules with no elaborator dependency. Trust
remains 716 sources / 240 inventoried sites / zero findings. Feature generation
is current for 212 features and 783 classified upstream symbols; both affected
features remain partial. The final source reports are in `after-final/{0,1,2}`
and compare exactly to the baseline results, including every blocker. All three
carry the final model hash. No fixture observation or required pipeline was
dropped; those pipeline executions remain blocked.

Machine-readable commands, exits, timings, resource figures and scope are in
`/workspace/diamond-payments-evidence/evidence-summary.json`; all raw logs remain
beside it. No tracked script changed, so script-specific unit tests were not
required; the unchanged corpus generator was exercised by its consistency gate.
The temporary single-threaded Lake configuration and shim are retained in that
evidence directory before removal from the checkout. No push or merge is part
of this handoff. The original gap remains open; this is a reviewable partial
implementation, not completion of coverage-plan step 11.


## Resumed milestone: original PiggyBank and conditional dispatch

Retained checkpoint `2edd52bf` is preserved on the same saved branch and VM.
The original `/workspace/diamond-payments-evidence/PiggyBlocked.lean` exit sequent was isolated: after `state := 2`,
the owner frame and old state-one invariant establish that the booked ledger
at the owner is zero. `Calculus/PaymentClose.lean` supplies explicit typed lemmas for
that frame, conditional debit, written state and invariant-preserving resumption.
Its opt-in solver uses the existing incremental prefix peeler and budget.
No generic closer, proof/fuel/test limit or original formula was weakened.

`sol_auto_theorem ... := by ...` separates derivation, normalization and each
checked named auxiliary theorem, under unchanged per-phase limits. Existing
syntax/default behavior is unchanged. History was inspected (`3b03ac58` owns
this command's earlier checking-cost separation). The changed declaration
creation site uses checked `.thmDecl`/`addDecl`, with no skip-kernel option,
new axiom or recovery escape; the trust scan and actual axiom audit are required.
This optional explicit leaf proof is manual evidence, not automatic completeness.

`Examples/Tactics/PaymentCorpus.lean` proves a typed transcription of the PiggyBank callback
body and invariant: all eight fields, original guards/order/captures, state write, payout,
zero-msg.value parallel entry booking, owner-not-self premise and both invariant
branches. The entry update is proved under both modalities. The body and full
box theorem pass per-file MCP with only propext, Classical.choice and Quot.sound
(`resume-extracted-corpus.log`). Omitted unrelated helpers do not establish
whole-contract reentrancy safety. The typed transcription is kernel evidence,
not automated source translation, compiler or EVM correspondence. All frozen
corpus pins, including PiggyBank, stay unchanged at integration.

`Calculus/CallbackSound/Payments.lean` proves existing modal normality
`¬ [r.transfer(a);] false` implies runtime acceptance. `ProvesC.transferD` and
`transferDetD` and the guarded dispatcher retain the exact same simple operands,
all surrounding hypotheses, exit invariant and arbitrary callback storage,
ledger and balance resumptions where applicable. They are sufficient conditional
rules, not an unconditional SolKey port. The original bare diamond is refuted by
refusal, even if funded. No acceptance atom, profile decision or target narrowing
is introduced. Stipend/full-gas behavior and all send failure paths are unchanged.
`Examples/Tactics/PaymentRules.lean` passes automatic guarded derivations, funded normality,
insufficient funds, recipient refusal, bare-diamond and failed-update-prefix
controls. The global callback soundness theorem's audit remains the standard three.

Read-only finder and skeptic reviewed the guarded rules, command, specialized
solver and exact original corpus statement without Lean servers or checks. Neither
found a concrete soundness/fidelity defect. Both required root registration and
updated claims; these are addressed. Final documentation review also required
explicit historical headings and precise unconditional-taclet versus adapter wording;
those corrections are applied. They explicitly rejected describing the
conditional adaptation or handwritten corpus proof as unconditional taclet or
general source-adapter completion. Their remaining validation requirements are recorded below.

Continuation shared edits: `Solidity.lean`, `Calculus/Callback.lean`, `CallbackDerive.lean`,
`CallbackSound/Calls.lean`, `Closers.lean`; additive Payments/PaymentClose and two
example modules; module-map, kernel-port, options, rule-map and this owning handoff;
two partial feature rows and audit-generated inventory/Features outputs. No
runtime, compiler, source runner, target certificates or exclusions change. The
PiggyBank callback theorem remains separate from its frozen `.key` pin. All earlier evidence above describes the earlier checkpoint, not this
continuation. New final commands/results are appended after they actually run.


The integrated `KEY_SUITES.Net.ported` retains its four original mappings.
The generator emits their evidence imports and checked theorem references in
`SolidityCorpus.lean`. The source branch's proposal to register the PiggyBank
theorem was rejected by the frozen integration guard, despite its earlier
reviews. The generator's scoreboard distinguishes abstract kernel proofs from
translated initial-state runs and EVM results. The repaired script regression
compares every corpus row in all six columns and exact TSV bytes, checks the
original PiggyBank source mapping, retains legacy proof reachability and
callback countercontrols, and keeps PaymentCorpus reachable separately.
Additional shared edits are `scripts/solkey-port.mjs`, its payment-corpus test,
and generated `SolidityCorpus.lean`, `tests/solkey/expected.tsv`,
`docs/corpus-parity.md`. No snapshot or upstream-source re-pin occurs.


## Resumed final validation and remaining blockers (historical 1b9bf3a9)

`./run-lean.sh` passed in 5,168.874 seconds: 691 default jobs, 259 TestSuite
jobs, all 377 parsed taclets and 131 read-bearing annotations. This is a cached
dependency rebuild, not a cold-bound guarantee. The same executor briefly
returned to starting during TestSuite; the original Docker worker survived.
The retained branch/HEAD and limits were verified, the lost outer writer lock
was adopted, and no duplicate build or VM was created. Final warm canonical
confirmation passed in 1.025 seconds with all temporary target configurations
passing `-j1` (libraries, native executables and LeanTeX).

The whole retained container group's cumulative peak was 12,203,151,360 bytes,
below memory.max=12,884,901,888; memory.swap.max=0. `memory.events` low/high/max/oom/oom_kill
counters stayed zero. PSI pressure was not measured. VM `free -b` reports physical memory 18,882,674,688 bytes,
rather than the nominal 16 GiB description; this measured environment drift is
reported, not substituted silently. Raw OS headroom snapshots and cgroup counters
are retained in `resume-resources.log`. Peak figures in per-gate JSON are
cumulative group peaks, not isolated per-command RSS. Caches and temporary files
remain on disk. Builds and MCP were serialized under the documented lock.

All eleven final per-file MCP diagnostics report success=true, partial=false,
no errors (including generated roots/Features). Actual `lean_verify` for the
new callback soundness theorem and full original PiggyBank case reports only
propext, Classical.choice and Quot.sound. Its source scan flags the conventional
local `InContract` instance selecting the original contract; this introduces no
axiom or additional proposition. Full-build printed audits also cover entry,
body, full case, guarded controls and global `ProvesC.sound_of`. The unchanged
`TrustAudit.lean` passed in 84.277 seconds: 529 headline theorems, standard axioms.
The source trust scan passed 720 sources, 240 inventoried sites, zero findings.

Structural gates passed: 706 reachable modules, zero orphans; 152 core modules,
zero elaborator dependencies. Strict automation timed all 26 TestSuite modules
against unchanged 300-second budgets: 491 automatic, 61 existing step-budget
replays, zero manual, 11 refuted, zero pending. All five script tests passed,
including exact preservation of every other TSV row. The first test invocation
failed because the chosen disk TMPDIR did not exist; creating that directory
resolved it without changing tests or limits. The inventory check remains
current for 212 features/783 symbols, both affected features partial.

The owning corpus update passed in 63.513 seconds, then its consistency check
passed in 10.553 seconds. Only the original PiggyBank callback row improves:
73 proved / 34 unsupported / 101 unported (previously 72/35/101). The generated
root imports the evidence modules and checks all five handwritten references.
No upstream source/snapshot pin changes. Final read-only finder and skeptic
reviews covered rules, soundness, bounded proof command/solver, original corpus
fidelity, generator/test, generated outputs and current/historical claims; no
concrete soundness or fidelity defect remained. Their requested registration,
all-other-row regression, historical headings, precise source-adapter wording,
and kernel-checked terminology corrections are applied.

The additional global doc-path check still exits 1 for twenty missing historical
references (external library/test paths). The identical twenty reproduce on the
existing untouched exact-base worktree. Task-owned shorthand citations were
qualified; no task-owned missing reference remains. Neither historical evidence
files nor checker policy were changed. Raw baseline/current logs and comparison
are retained. This optional extra gate is not reported as passing.

Final source runs are `after-resume/{0,1,2}` and compare exactly to baseline
results, with model hash
`cf70da9dbe56a9767bee810110f8863da31be995ed96c7c694ff31bdc3f0477c`.
All required pipeline/ordered-observation inputs and expectations remain intact;
existing classification blockers prevent those executions. The two send/transfer
host fixtures remain blocked on transaction/self/cross-contract adaptation; the
transfer revert-string fixture remains blocked on `revertStrings=debug`.
Runners exit 1 in 0.902, 0.867 and 0.800 seconds. Compiler 0.8.38 SHA remains
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`.
These are blocked source-adapter classifications, not compiler/EVM success.

The original unconditional transfer diamond still cannot be a sound port:
recipient refusal can revert even with funding. A semantics/profile decision
would be required to assert that rule without acceptance evidence; this task
makes none. The conditional rules and exact witnesses are implemented, and the
original representative callback corpus proof is closed and connected. The
remaining source fixtures and unconditional taclet gap prevent claiming the
entire original assignment or step 11 complete. Six original closer gap
statements, `inTarget` certificates, exclusions, waivers and decision theorem
retain their meaning; no residue or completeness claim is introduced.

Machine-readable continuation results are in `resume-gates.json`,
`resume-final-mcp-summary.json`, `resume-fixture-comparison.json` and
`resume-doc-paths-comparison.json` in the external evidence directory. Failed
attempts and the earlier checkpoint artifacts are retained. The original user
Lake configuration is restored byte-for-byte; temporary configuration/shim
copies are retained externally before removal. No push or merge occurred.


## Checkpoint d426b23f: human-approved conditional family (historical)

`Calculus/PaymentConditions.lean` separates funding from recipient policy.
`recipient_iff` proves exactly no oracle entry or an explicit `.ok data`;
`canPay_iff` combines that with sufficient live funds, even for self-payment.
Missing-entry acceptance establishes neither deployed code nor receive dispatch.
`transfer_success_iff` and `transfer_callback_conditions_iff` expose exact
necessary and sufficient deterministic/callback conditions. The callback case
retains the booked exit invariant and every storage/ledger/live-balance resumption.
`transfer_failure_iff` certifies insufficient funds or recipient rejection;
`transfer_failure_bytes` and `transfer_does_not_bubble` certify bare-revert behavior.

`send_accepted_run` and `send_refused_run` specify exact states and result locals.
`send_flag_iff` characterizes the deterministic Boolean. `send_deterministic_iff`
characterizes universal diamond validity when the statement does not fork; it is
not an individual accepted-callback classification. `send_refused_outcome_iff`
gives the unique refused callback outcome. `send_callback_iff` proves the missing
necessity direction: the unbooked false-result continuation is mandatory for
every response; acceptance additionally requires the exit invariant and every
successful invariant-preserving resumption. Full-gas calls cannot satisfy the
nonforking premise merely by selecting the noCallback stipend option. Concrete
controls cover error/panic/zero-value/funding/payload/full-gas cases. The original
unconditional claims/refutations and all earlier payment witnesses are retained.

The original `uncalled_address_transfer_send.sol` now passes its complete `f()`
observation in both legacy and via-IR with pinned solc. It executes only f(),
so this is not evidence of fallback or payment invocation. The reader evaluates
discarded native member receivers into fresh typed locals, retaining their
writes, calls and reverts. The dependency scanner starts at actual invocations,
uses existing callee arms/options/native kind IDs, and retains refusal for actual
unsupported self-payment dispatch. The host exception applies only to an
uninvoked native reference with a total self receiver. Source proof controls
retain receiver writes/reverts; actual direct/parenthesized/conditional self-call
negative controls retain the old dispatch refusal. No global profile or core
operational/callback definition changes.

The remaining `send_zero_ether.sol` observations are constructor value20,
actual Receiver creation, receive invocation, s()=true, and SIX exact gas/code-gas
observations for irOptimized/legacy/legacyOptimized. Default oracle acceptance
proves neither dispatch nor gas. Existing WorldImport handles direct creation-
return factories, not creation-then-send; the upstream runtime has no value/world
sequence adapter. The new separate optional payment EVM replay retains these observations and
implements the pinned test host intrinsic/refund/code-deposit accounting, with
metadata disabled in its gas profiles. Actual results are recorded below.
This independent bytecode execution does not fill the typed source-world gap.
No observation is dropped.

The original debug transfer sequence is empty-calldata receive with value10,
g()=10, f()=Error(no_receive), then insufficient-funds h() with empty failure.
It first creates A in C's state initializer. Actual receiver code/error bytes
need typed source-world payment execution. Existing single-contract transfer
maps every refused response to bare revert, even if it contains a reason. The
new generic theorem certifies that this route cannot produce the frozen nonempty
f() observation. No posthoc bytes or separate revert-agent proposal are adopted.
Remaining dependencies are source-world creation/initializer/receive dispatch,
payload-preserving source-world payment frames above the unchanged run. Independent bytecode observations are recorded
separately below. These are not the resolved semantic-
choice blocker. The latest human instruction authorizes fixture repair; the remaining issue
is the absent typed source-world sequence interface, not lack of authorization.
The current reader explicitly refuses these shapes rather than erasing effects.
Until those dependencies exist, both full fixtures and the overall assignment
remain incomplete. Independent payment proofs and the complete uncalled-reference
fixture are carried forward with the actual validation below.

Shared edits: two additive modules/root registrations, narrow Body/Contract
payment-reference lowering/dependency fixes, upstream host check, payment-reference
source/script tests, owning docs and audit-generated inventory evidence. Statuses
remain partial. No target/exclusion/waiver or original expected observation changes.


### Human-choice milestone validation, 2026-10-29

Same retained VM, `codex/next10-diamond-payments`, parent
`1b9bf3a9bc342ba8807b681a14c3ec8168610a9e`; earlier `2edd52bf` and all
unconditional claims/refutations are preserved. No new clone/container/branch,
push or merge. Lean4.24.0/Lake5.0.0, explicit Lean `-j1` through temporary Lake
configuration, `LEAN_NUM_THREADS=1`, one writer/check under the documented lock.
Original user Lake configuration restored after MCP. Docker memory.max
12884901888, swap.max0, network none; caches/TMPDIR on disk. Observed physical
RAM18882674688 bytes differs from nominal16GiB; initial MemAvailable17158901760.
Full build aggregate peak12884901888, memory.events max377, oom0/oom_kill0:
the cap was reached with reclaim, not a measured spare margin. No limit increase.

Actual logs are retained in
`/workspace/diamond-payments-human-choice-evidence/` (outside the repository):

- `full-run.log`: `./run-lean.sh`, exit0, 2349.445s, 693 build jobs and259
  TestSuite jobs;377 taclets/131 read annotations matched. Baseline and current
  KeySort runtime output is retained; current `runtime-gate.log` exit0.
- `resume-gates.json`: orphans0(0.268s), layers0(0.271s), automatic strict0
  (0.172s;26 timed modules below unchanged300s;491 automatic/61 bounded/
  11 refuted/0 pending), trust0(4.031s), inventory0(0.157s), source/script tests0
  (32/32;15.257s), TrustAudit0(99.206s;529 standard-axiom headlines), corpus0
  (79.939s;73 proved/34 unsupported/101 unported), diff0. Wall times can include
  waiting for the writer lock. Global doc-paths remains exit1: the same20 baseline
  missing historical/external references; policy is unchanged.
- `mcp-final.log`: every new/edited Lean file, generated Features and root have
  success=true, partial=false and no errors. Actual `lean_verify` for exact
  callback transfer/send and original PiggyBank reports only propext,
  Classical.choice, Quot.sound; PiggyBank's existing local-instance scan warning
  is retained. Per-file printed audits include all new main exactness/control
  heads, with at most those standard axioms; expected nonempty-error bytes is
  axiom-free. No sorry or new axiom.
- `evm-tests-final.log`:21/21 optional reference regressions,2.507s; wrong output,
  wrong revert bytes, wrong gas, rollback, actual2300-gas receiver execution,
  unsupported failed-creation payload gas, broken-before-unexecuted-gas precedence,
  and unchanged instruction-exhaustion handling. The initial parser test failure
  was a missing constructor ABI in the test setup; retained and repaired.

All original fixtures were rerun without changing source, expected observations
or callback/profile semantics. Before: all three Lean source adapters blocked.
After (`after-human-choice/{0,1,2}/results.json`):

| Original fixture | Lean source result | Separate bytecode reference |
|---|---|---|
| functionCall/send_zero_ether.sol | blocked: world/host sequence absent | all modes working; constructor20wei, s()true and all6 gas/code-gas observations exact |
| expressions/uncalled_address_transfer_send.sol | working in legacy/viaIR: f(), success, empty values/return/revert bytes | same full observation working in both modes |
| revertStrings/transfer.sol | blocked: revertStrings debug/world payment adapter absent | both modes working: receive10wei; g()10; f()100-byte Error(no_receive); h()empty failure |

`evm-{send,uncalled,transfer}-final.json` retain every ordered original row,
required pipelines and any extra optimized gas profiles, exact actual bytes,
source/compiler/input/runtime hashes, adapter/engine/lock hashes, actual frame
step counts, created runtime hashes and gas/refund/deposit accounting. The send
trace records creation then a distinct2300-gas, zero-value, nonzero-step receive
frame. These are actual compiled-bytecode observations under pinned solc0.8.38
(SHA6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390)
and snapshot1835d247; they are not Lean source proofs or a compiler theorem.
The unchanged generic EVM backend retains its host refusals. The new optional
payment replay blocks failed CREATE/CREATE2 with nonempty output because its
host deposit rule is not adapted; no generic gas completeness claim.

Finder and skeptic independently reviewed core conditions, source lowering,
fixture scope, and optional replay without Lean/server/checks/writes. Confirmed
findings fixed: callee-head-only dispatch, failed-creation gas refusal, broken
verdict precedence, adapter provenance, portable disk TMPDIR and stale current
authorization/backend wording. No further semantic false-support finding after
repair. Retained original source/target/inTarget certificates, six gaps,
DecisionTheorem, exclusions and Waivers are unchanged. Inventory was regenerated
by the audit script from evidence-only manifest additions; partial status stays.

**Remaining implementation dependency, not a semantic-choice question:** the
existing WorldImport accepts whole direct creation-return factories, and
ContractWorld.call executes a typed callee entry. Neither lowers a creation or
state-initializer followed by a payment inside an arbitrary source body, nor
connects receive selection and a nested recipient halt to that caller's transfer.
The single-contract transfer provably returns empty halt bytes, so it cannot
be relabeled as the frozen debug payload observation. Required next integration
is an intrinsic world-aware statement/frame interface retaining catalog handles,
initializer storage, caller funds/rollback, receive selection and actual nested
halt bytes above the unchanged single-contract run. Removing host/debug refusals
or feeding reference bytes into Lean would not implement it. Independent gas
observations are now validated; the two Lean world-source adapters and therefore
the full assignment remain open. No human semantics decision remains pending.


Final read-only finder/skeptic review after fixes: no further substantive finding;
no reviewers used Lean/server/checks or wrote files. Final cached full confirmation
`full-final.log` exit0,1.027s. Post-review21 reference tests passed; inventory,
strict and trust rerun passed (trust722 sources,240 inventoried sites,0 findings).
Temporary Lake configuration removed from checkout after preserving it with the
shim in the evidence directory; tracked user configuration is unchanged.
Final doc-path invocation initially hit Docker Git ownership refusal; command-
scoped safe.directory repaired invocation, without changing Git/user configuration.
The check still reports the same20 baseline missing references.


## Typed payment source bridge: 2026-10-29 continuation

This milestone closes the two source rows left at d426b23f under the explicit
human-approved conditional payment assignment. Final validation results are
recorded below; historical checkpoint failures remain in their original logs.
No unconditional transfer-success claim is restored.

The retained branch started clean at d426b23f74d059dbc507e1a9f988bf5877922013.
Published origin/master was inspected at cc155f36. The only imported prerequisite
is the exact published ContractWorldCertificates module and the 11-line
Operation.guard/tryCreate addition to ContractWorld (published1e37a225). The
existing create/call/enter/finish/settlement definitions are unchanged. This is a
deliberate narrow prerequisite import, not a merge/reset or change of evidence
base; cumulative patches still start at f4dee4a2. No unpublished branch is used.

`PaymentWorld` composes actual typed calls above unchanged single-contract TRun.
`createSend` consumes the returned Handle from World.create and invokes receive
through that same handle even for zero amount. Its success witness exposes the
real creation and stipend operations; send true iff actual recipient completion,
and receiveRun_ok exposes the real funding, imported body and settlement.
Completed recipient failure returns false with the pre-receive world, preserving
preceding caller funding/creation. Exhaustion/divergence are not ordinary false.
Transfer transports the actual nested THalt and every byte. Funding failure
precedes receive execution. The atomic failure law preserves the entire original
world, not merely its observed balances.

`PaymentPlan` accepts complete source bodies and retains owner/target, receive,
creation, local/root and ordinary method/call identities. It rejects extra
statements/declarations, inheritance, modifiers, unresolved/mismatched receivers,
internal/private exposed methods and full-gas calls. `PaymentImport` imports the
original AST declarations, resolves receive/getter by exact sourceId, and quotes
the actual programs with kernel checking. It uses the existing external-entry
failure-data reading only for the receive boundary; legacy TRun.transfer still
has its certified empty-data behavior. No reference bytes are supplied to a
source execution.

For Main.s the whole source body is local new Receiver followed by send0.
Main's real payable constructor receives20. For C the sole new-A initializer is
executed while C is not installed, using A's source-implicit empty constructor;
then an intrinsic typed assignment stores the actual returned address in C.a
before World.create installs C. This staging is justified by the complete
recognized shape: A has no fields or user constructor and C has no other
initializer or constructor effects. Later transfers read C.a through a quoted
typed program, require equality with the typed handle, and dispatch A.receive.
The real C.receive and g() bodies are also imported and executed. All code-kind,
static/library, funding, settlement and rollback checks remain explicit.

The kernel proofs cover original constructor20/newReceiver/zero-receive/sendtrue
and the full debug sequence: receive10; g()10; actual100-byte Error(no_receive);
unfunded100ether empty failure; g()still10; both code accounts still installed.
Separate initialization, successful funding and getter witnesses avoid comparing
whole world functions in the elaborator. Earlier monolithic/reflexivity attempts
hit recursion/200000-heartbeat bounds; diagnostic counters and failing files are
retained. The final proofs use finite kernel observations and unchanged limits;
whole-world rollback is a separate universal equality theorem. Wrong bytes,
handle and code-kind controls retain their exact source/model distinction.

The frame and its proofs are deterministic and unmetered. Stipend send/transfer
have their own source kind; full-gas calls are not coerced into it. This is not a
2300-gas adequacy theorem or a change to legacy callback defaults. The generic
world API can execute other bodies, but this source reader cannot admit them.
All original callback rules, funding/recipient/invariant/resumption premises and
the original PiggyBank proof remain unchanged. The six original gap statements,
inTarget certificates, DecisionTheorem, exclusions and Waivers are untouched.

Whole-fixture completion requires both required typed source pipelines and a
fresh independent bytecode report matching source/compiler/snapshot/runner/
adapter/engine/lock provenance. It compares every ordered signature, failure,
value and revert byte, plus every original gas row/profile. Gas is never claimed
as a Lean observation. Intermediate reports stay blocked until reference evidence
is complete; pending rows really resume. Thus an unmetered functional match alone
cannot certify a gas-sensitive recipient outcome. The replayer currently refuses
repeated creation without a fresh-address allocator and calls following failed
explicit deployment, rather than inventing collision behavior or redeploying.
No universal source/compiler equivalence, general world-source language, general
callback source theorem or full decision completeness is claimed.

The actual source controls exercise wrong expected bytes, wrong receiver/native
kind/internal visibility, repeated creation, calls after failed deployment,
zero-value refusing receive with retained creation, wrong gas and provenance,
absent reference evidence, and saved pending-result recovery. Source balances are
audited as decimal strings. The two committed AST witnesses reproduce from the
unchanged pinned snapshot/compiler with payment-source-fixtures.mjs --check.
The optional bytecode engine retains its instruction/gas limits and failed-create
payload gas refusal; no old source expectation is changed.

Reviewed source-import evaluation sites are inventoried narrowly: four evalConst
reads of imported contracts/reports, one evalExpr of JSON observations. Every
quoted program and every theorem is still checked by the kernel. These are not
new axioms or an unchecked proof path. Feature evidence was updated only for
sendTransfer; partial status remains and inventory was generated by its audit.

Shared edits: narrow published world prerequisite, root/module registration,
upstream payment routing/provenance/build/report join, trust audit/inventory,
owning docs and audit-generated feature evidence. New payment-specific modules,
AST witnesses and scripts are isolated additions. No push/merge, other VM,
monitor, profile decision or rejected ABI/lazy-calldata assignment was touched.

Finder and skeptic reviewed the kernel/source/reference areas read-only without
Lean/server/checks. Confirmed defects fixed before final validation: unverified gas
completion, missing source/reference outcome pairing, repeated address reuse,
implicit redeployment after failure, pending-row resume skip, missing visibility
checks, uncaught preparation exceptions, cold dependency build and helper-hash
provenance. Their final frozen-code pass found no further confirmed defect.

### Actual final validation

- Full `./run-lean.sh`: exit0,2189.997s;699 library/default jobs and259
  TestSuite jobs. Aggregate sampled RAM peak12884570112 bytes; retained group
  peak12884901888 bytes (the12GiB cap). memory.events max1624 versus inherited377,
  oom0/oom_kill0. This is measured reclaim/pressure, not spare margin. A live
  heavy-build OS snapshot retained8598601728 bytes MemAvailable; physical RAM
  is18882674688 bytes, a reported drift from nominal16GiB. Disk had24GiB free.
- Its first terminal SolKey check was skipped because SOLKEY_RULES was absent;
  that actual skipped output is retained. After supplying the existing pinned
  path, a full cached confirmation exited0 in0.951s and actually matched377
  taclets/131 read annotations. No pin/configuration or budget was changed.
- Strict automatic gate exit0:26 timed TestSuite modules within300s;491
  automatic,61 step-budgeted,11 refuted,0 pending. Orphans/layers/inventory all0.
- Script regressions59/59 passed,43.717s. Source AST reproduction --check exit0.
  Trust inventory728 sources/245 reviewed sites/0 findings; TrustAudit545
  headline theorems use only propext/Classical.choice/Quot.sound. Corpus gate0:
  73 proved/34 unsupported/101 unported, preserving the old PiggyBank improvement
  and every other original pin.
- `fixtures-final.json`: original send source0(43.650s), bytecode0(5.584s);
  uncalled source0(2.231s), bytecode0(2.791s); debug transfer source0(6.409s),
  bytecode0(2.929s). Wall times may include waiting for the single writer lock.
  All ordered rows and required modes are retained in final-source-*/results.json
  and final-bytecode-*.json. Send also verifies all6 gas/code-gas rows across
  irOptimized/legacy/legacyOptimized. The uncalled fixture still executes only
  f(), not its uncalled fallback member references.
- Final per-file MCP in mcp-final.log: all10 files eventually success=true,
  partial=false,0 errors. One initial timeout was polled to completion. Three
  core lean_verify calls report only standard axioms. That combined command
  exited1 when lean_verify re-elaborated the relative-fixture source file in a
  scratch location and incorrectly collected its recovery sorryAx. The actual
  file diagnostics, kernel build and545-headline audit were already clean.
  Inspection of lean-lsp-mcp0.29.0 tools/analysis.py confirms it copies the file
  to scratch and filters only appended diagnostics, missing earlier relative-
  path errors. No source or proof was changed to conceal this failure.
  mcp-imported-axioms.log then audits the actual compiled source constants via
  the import-only root: original send/transfer, wrong handle/kind/bytes and
  original PiggyBank all return only standard axioms, with the explicit
  ALL_IMPORTED_AXIOM_AUDITS_PASS assertion. Repository source scanning remains
  covered separately by check-trust. Shutdown-loop messages are retained.
- Global doc-path check remains exit1 with the same20 baseline historical/
  external missing references. Its actual debt is not waived or rewritten.

Before/after from d426b23f: send blocked→working; debug transfer blocked→working;
uncalled working→working. Both repaired rows now run actual typed world source
compositions; their kernel witnesses and independent bytecode/gas observations
are distinct evidence. There is no remaining named source-row implementation
blocker or pending human semantics decision for this conditional assignment.
The broader language/profile/decision-completeness gaps above remain outside
this completion claim.

Evidence directory: /workspace/diamond-payments-source-evidence. Earlier
checkpoints, failed attempts, command output, timings and original exports are
preserved. The cumulative patch/handoff/checksum are exported only after the
final actual diagnostics and review complete. No push or merge.
