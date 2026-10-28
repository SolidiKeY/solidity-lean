# Diamond payments: guarded rules and the original PiggyBank callback proof

Current scope: sound conditional deterministic/callback transfer diamond rules,
positive and failure countercontrols, and the full original PiggyBank callback
kernel obligation. Its single `.key` corpus row is connected through the existing
handwritten-proof mapping, with build-checked evidence. This does not establish
source-runner, compiler/EVM or whole-contract callback support. The unconditional
transfer diamond and blocked source fixtures remain open; both features stay
partial. New final validation is recorded in the resumed milestone below.

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

`Examples/Tactics/PaymentCorpus.lean` proves the full ORIGINAL PiggyBank callback
case: all eight fields, original guards/order/captures, state write, payout,
zero-msg.value parallel entry booking, owner-not-self premise and both invariant
branches. The entry update is proved under both modalities. The body and full
box theorem pass per-file MCP with only propext, Classical.choice and Quot.sound
(`resume-extracted-corpus.log`). Omitted unrelated helpers do not establish
whole-contract reentrancy safety. The typed transcription is kernel evidence,
not automated source translation, compiler or EVM correspondence; the remaining original pins stay. The PiggyBank row alone improves after its full proof checks.

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
PiggyBank callback `.key` pin alone improves with its exact proof; other pins stay. All earlier evidence above describes the earlier checkpoint, not this
continuation. New final commands/results are appended after they actually run.


The `.key` integration follows the existing `KEY_SUITES.Net.ported` convention.
The generator accepts an explicit evidence path for the PiggyBank theorem,
preserves legacy defaults, and emits evidence imports and checked theorem
references in `SolidityCorpus.lean`. Independent finder and skeptic approved
this single proof-backed improvement: no further source adapter is needed for
this handwritten `.key` obligation. The generator's scoreboard distinguishes
these abstract kernel proofs from translated initial-state runs and EVM results.
The new script regression compares every other corpus row in all six columns,
checks legacy/custom proof reachability, and retains callback countercontrols.
These checks must pass before the new pin is accepted as final evidence.
Additional shared edits are `scripts/solkey-port.mjs`, its payment-corpus test,
and generated `SolidityCorpus.lean`, `tests/solkey/expected.tsv`,
`docs/corpus-parity.md`. No snapshot or upstream-source re-pin occurs.


## Resumed final validation and remaining blockers

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
