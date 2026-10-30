# External try execution witnesses — partial step 11

**Step 11 remains incomplete at its native source-adapter boundary.** The human
selected explicit conditional success/failure statements without stronger global
admissibility assumptions, and subsequently authorized the narrow Panic decoder
correction described below. Existing callback APIs/default universal reading and
source/profile scope remain; the decoder's raw-data behavior is the approved
delta. The conditional account retains exact typed outcome conditions, ordinary
formula transport and creation interfaces. Source bridges cover entry returns,
creation and scalar/storage linked-library try composition. Twelve original
fixtures pass native replay in both pipelines; eighteen pass separate fresh
compiler/EVM replay. Neither finite replay nor an existential typed execution
establishes universal source validity. The remaining dependencies are explicit.

All original unconditional source claims and their certified refutations remain.
The former exact36-byte decoder policy certificate is historical at ffabfb22;
its approved replacement does not change frozen source observations/verdicts.
`tryCallDiamond`/`catchDataDiamond`, callback judgments, the six original gap
statements and target certificates, exclusions, Waivers, DecisionTheorem,
profile choices and frozen expectations are unchanged. The historical sections
retain their original checkpoint results; the final section records the current
human-approved conditional account and fresh validation.

## Initial proved scope (`fab16f7c`)

`Solidity/Semantics/ExternalTryWitness.lean` handles `self = false` against the
current `TRun.tryCall`. Each alternative requires a nonzero receiver and the
actual oracle lookup. Success additionally requires successful return decoding.
The four `*_returns` corollaries require the selected clause's actual `.ok out`;
selecting a clause alone is not a normal-execution witness. Their output retains
the exact heap extension, return/Panic bindings and scope drop. Catches restart
from the caller state. Separate equations preserve zero-address, missing-entry,
and decode-error caller failures; none enters a catch.

`Solidity/Counterexamples/DiamondTry.lean` proves the precise callback
obstruction: for a modality whose leading statement is a reached try,
`ExecS.tryRevert` supplies a caller revert, `ExecP.halt` propagates it, and
`holdsC` universally checks it even under the diamond. Therefore this diamond is
false for every invariant, payment flag, self flag, continuation, frame and post.
An existential normal witness alone cannot soundly strengthen that reading.
This does not rule out deterministic oracle-backed witnesses.

The upstream SolKey file has `tryCallNoCallbackBox` and
`tryCallWithCallbackBox` (lines 6732 and 6847 in the frozen setup copy), with
success, Error, Panic and other-failure branch labels; it has no diamond try
rule. No new taclet or term/printer syntax is claimed here.

`Solidity/Examples/Tactics/ExternalTryWitness.lean` uses one quoted source-shaped
program without a box annotation and explicit transaction-oracle inputs. Its
four normal-completion controls and two caller-failure controls are checked by
`decide +kernel`; ordered `(tag, reasonCode)` observations are pinned by
`#guard_msgs`. It also refutes the source-shaped callback diamond for arbitrary
`pay`, including false. These are concrete kernel executions, not imported
Solidity obligation proofs or compiler/EVM equivalence. In particular,
`ExtResult.error []` is an oracle category, not raw EVM Error ABI bytes.

| Oracle/control | Ordered storage observation / halt |
|---|---|
| success with return word 9 | `(9, 0)` |
| Error alternative | `(2, 0)` |
| Panic with code 17 | `(3, 17)` |
| other failure | `(4, 0)` |
| missing entry | caller `revert` |
| success with missing return word | caller `revert` |
| zero receiver, general equation | caller `revert` regardless of oracle |
| callback diamond, either payment flag | proved false |

## Baseline and runtime evidence

Repository `/workspace/solidity-lean`, origin
`https://github.com/SolidiKeY/solidity-lean.git`, base
`f4dee4a29c2e208b36db4a4161a4723c735cd775`, branch
`codex/next10-diamond-try`. Initial fetch brought `origin/master` to that exact
base. Lean is 4.24.0 (`797c613`); Lake is 5.0.0-src+797c613.
The default PATH lacked the tools; the saved activation repaired that. Saved
artifacts also initially produced an incompatible-import error; rebuilding the
actual pinned sources repaired it. No replacement executor or project was used.

KeySort passed before code edits, with actual output retained before
`RUNTIME_GATE_PASS`. Chronology limitation: the assigned fixture comparison was
performed later from a pristine detached worktree at the pin, not before the
first proof edit. It does not retroactively satisfy the pre-edit fixture gate.
The comparison worktree is `/workspace/next10-diamond-try-baseline`; it shares the
on-disk artifact cache, and both runs use the same pinned compiler and budgets.

All writes and checks use the documented writer lock. Heavy checks are
serialized. Builds use `LEAN_NUM_THREADS=1` and a temporary alternate TOML adding
`-j1` to library weak arguments; replay Lean invocations also receive `-j1`.
The tracked lakefile and proof/fuel/node/test budgets are unchanged.
Systemd had no user bus, so Docker cgroup v2 enforced `MemoryMax=12 GiB` and
`memory.swap.max=0`, within the attached 16 GiB VM. There is no extra 12 GiB VM
reserve. Caches and replay scratch are on disk. Generated caches were restored
to UID/GID 1000 after the initial root-container checks.

The initial `./run-lean.sh` passed in **9,366 seconds**, including 687 library
jobs, 259 TestSuite jobs and the 377-taclet/131-annotation SolKey check. Accounted
cgroup peak was **12,884,901,888 bytes (12 GiB)**, including charged cache memory;
this is not a measured process-RSS peak. The retained cgroup snapshot records
402 limit-reclaim events and zero OOM/OOM-kill events. Sampled Docker usage
reached about 11.1 GiB. This is evidence for this run, not a general cold-build
headroom guarantee. No resource or proof budget was raised.

Initial focused module build passed; initial final per-file MCP results for all three files
report `success=true`, `partial=false`, no error items. An initial MCP dependency
setup timed out and is not counted as a pass. MCP also caught the regression's
missing Surface import, which was fixed. Its shutdown cleanup warning is
retained separately from the successful diagnostic result.

Actual axiom audits of all 20 headline proofs report only
`[propext, Classical.choice, Quot.sound]`; no new axiom or sorry was introduced.
The audit log also prints the four complete storage pairs and both caller
reverts. Source build passed in 2 seconds at a 200,519,680-byte group peak;
trust then passed: 717 sources, 240 inventoried sites, zero findings. The first
trust attempt failed on container Git ownership, not on source trust; the retry
uses the checkout user without changing global Git configuration.

## Assigned upstream fixtures

Compiler 0.8.38+commit.1835d247.Emscripten.clang was loaded and verified against
SHA-256 `6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`.
Both `node scripts/solidity-upstream.mjs run --filter semanticTests/tryCatch/`
runs completed classification and exited 1: **0 working, 0 broken, 20 blocked**.
Their complete result rows are identical. There were **zero Lean replay jobs**;
required-pipeline observations and fresh compiler/EVM parity remain unvalidated.
The gate was preserved rather than bypassed or reclassified.

H = `transaction/block/self-address or cross-contract host behavior not adapted`.
E = `upstream EVM constraint excludes osaka: <byzantium`.

| Fixture | Pinned baseline | Branch | Blocker |
|---|---|---|---|
| `assert_pre_byzantium.sol` | blocked | blocked | E |
| `assert.sol` | blocked | blocked | H |
| `create.sol` | blocked | blocked | H |
| `invalid_error_encoding.sol` | blocked | blocked | H |
| `lowLevel.sol` | blocked | blocked | H |
| `malformed_error.sol` | blocked | blocked | H |
| `malformed_panic_2.sol` | blocked | blocked | H |
| `malformed_panic_3.sol` | blocked | blocked | H |
| `malformed_panic_4.sol` | blocked | blocked | H |
| `malformed_panic.sol` | blocked | blocked | H |
| `nested.sol` | blocked | blocked | H |
| `panic.sol` | blocked | blocked | H |
| `require_pre_byzantium.sol` | blocked | blocked | E |
| `require.sol` | blocked | blocked | H |
| `return_function.sol` | blocked | blocked | H |
| `simple_notuple.sol` | blocked | blocked | H |
| `simple.sol` | blocked | blocked | H |
| `structured.sol` | blocked | blocked | H |
| `structuredAndLowLevel.sol` | blocked | blocked | H |
| `try_catch_library_call.sol` | blocked | blocked | H |

The 18 H rows need the upstream host/source-world adapter prerequisite before
try/catch replay can establish every required pipeline and ordered observation.
That prerequisite is not fabricated by installing an oracle in a concrete
kernel example. The two E rows retain their original EVM constraints.
The runner explicitly does not test generated EVM/SSA, gas, logs or the native
C++ harness. No fresh physical-EVM execution is claimed by this increment.

## Validation and review

Evidence directory: `/workspace/next10-diamond-try-evidence/`.

- `runtime-gate.log`, `RUNTIME_GATE_PASS`: actual KeySort gate.
- `proofs.log`, `mcp-final.log`, `mcp-source.log`: successful focused checks.
- `full.log`, `validation.tsv`, `full-cgroup-snapshot.log`: initial full gate,
  timings, aggregate memory accounting and limits.
- `fixtures.tsv`, `source-build.log`, `trust-fixed.log`: component and trust gates.
- `axioms-and-observations.log`, [Axioms audit](/workspace/next10-diamond-try-evidence/Axioms.lean): actual audits and observations.
- `upstream-before/`, `upstream-after/`, `fixture-comparison.json`: every retained
  classification row, source snapshot hashes and strict blocked results.
- `final-gates.tsv`, `full-final.log`: final checks after the last import change.
- `metadata.log`, `review.md`: repository/toolchain evidence and review record.

No repository script was modified; script-test changes are not applicable.
The feature audit is regenerated by its script, with no support-status increase.
Final policy and build exit codes are recorded in `final-gates.tsv`.

Independent read-only finder and skeptic reviews covered the semantic equations,
normal-return corollaries, caller-failure controls, callback obstruction and
source-shaped controls; neither reviewer used a Lean server. The initial scope
finding that clause selection alone is not a successful witness was resolved by
requiring `.ok out` in all four return corollaries. No final semantic finding
remains. Compiler diagnostics separately found and confirmed the missing import
repair. Review does not certify source automation or compiler/EVM parity.

## Shared edits and remaining work

Shared edits are only the five cumulative module registrations in `Solidity.lean`, five
module-map entries, and the owning calls/exceptions document link. All proof and
control implementations are new modules unique to this task. No checking-cost
refactor, payment/world/creation/library rule, quantified invariant, ordinary
recursive-type migration, top-level revert-outcome modality or profile decision
is included. No push or merge is performed.

Still open: integration of the deterministic interface into taclets and branch
automation; source data-binding catch rules under the diamond; source obligations without box
annotations; the host-adapter prerequisite and every blocked required-pipeline
observation. The existing universal callback reading cannot be proved from an
existential witness alone, as the new counterexample establishes. The original
step-11 gap remains open, and mandatory fixture validation remains blocked.

## Final confirmation

All final policy gates exited 0. The full check after the final source import
passed in 5 seconds using the warm artifacts, with a 728,072,192-byte accounted
group peak. Final cgroup counters record no OOM/OOM-kill events and zero swap
allowance. The feature audit regenerated its outputs without a support-status
diff. `git diff --check` passed. The initial full run remains separately retained.

Both final read-only documentation reviews found no confirmed discrepancy or
overclaim. The semantic review scope and blocked fixture status remain exactly
as recorded above. The step remains incomplete despite the passing component
and repository checks.

The staged whitespace check subsequently caught two trailing spaces on new
theorem declarations. They were removed; per-file MCP diagnostics passed again
(`mcp-whitespace.log`). This cleanup changed no statement, proof, import or
observation. The final staged whitespace check passed before commit.

## Investigated continuation (`b4b6f3b8-ee8a-4ec4-b964-c2cbb819f21a`)

This is a bounded increment, **not completion of the original assignment**.
The retained checkout was clean at `fab16f7c93baac06502c33ad01f42699fdee20b2`
on the same branch and remote, with the pinned base still an ancestor and
`origin/master` still at the pin. The attached executor's runtime status and
actual local Docker response were checked. KeySort again passed before edits
(actual tool output: two jobs, exit 0, 24,731,648-byte accounted cgroup peak;
12 GiB maximum, swap maximum 0, no OOM events). Lean/Lake versions remain as
above. The VM parent is still 16 GiB; host-visible `free` is not its allocation.
No replacement VM, global config/credential change, push, merge or cherry-pick.

### New proved component

`Calculus/Sound/ExternalTryWitness.lean` imports local `SoundKit`, the earlier
try witnesses, and `AllocBytes`. It adds:

- `holds_diamond_of_normal`: an explicit proved `Prog.runFrames σ P κ = .ok τ`
  plus `holds τ φ` yields only deterministic `holds σ ⟨P κ⟩ φ`. This helper
  performs one rewrite, with no search or synthesized oracle.
- Exact state-indexed equivalences for a statement's normal typed `Out` or
  normal state projection followed by unchanged continuation and frames.
- `externalTry_{ok,error,panic,other}_formula`: directly use the four earlier
  `*_returns` lemmas. Actual nonzero address, oracle lookup, successful return
  decoding when applicable, selected clause's `.ok out`, and normal
  continuation/frame execution remain explicit premises. The exact dropped
  scope and typed heap extension from that `Out` are preserved.
- `externalCatchBytes`: the actual external oracle supplies Error/Panic/raw
  data using existing ABI encoding. A successful call is not a catch witness.
- `catchData_normal` and `catchData_normal_formula`: reuse existing
  `CatchKind.decode` and `TRun.litBytesT_alloc` rather than duplicate allocation
  soundness. The body runs from the original caller state with exactly that
  fresh bytes object. Its typed output's state is transported through the
  precise scope drop and continuation/frames. The existing allocation theorem
  is a state-projection equation; no equality of fabricated heap proofs or
  untyped erased states is introduced.
- Generic caller-revert and failed catch-decoder refusals.

The existing `Premise.sound_catchDataBox` and `catch_alloc_sound` in
`Calculus/SoundCatch.lean` were inspected first. They prove box goals for all
admitted payloads, including external allocation, not this normal-execution
state-specific diamond interface. They, the dispatcher, all taclets and both
false diamond rules remain unchanged. No checking-cost refactor is included.

### Component controls and evidence boundary

`Examples/Tactics/ExternalTryFormula.lean` manually applies the bounded helper
to explicit proved executions and checked postconditions. No box annotation
is used. These are quoted source-shaped kernel programs, not imported Solidity
obligations or successful compiler/EVM replays.

| Control | Proved result / ordered storage observations |
|---|---|
| Actual success oracle word 9 | deterministic diamond, `(9, 0)` |
| Actual Error oracle | deterministic diamond, `(2, 0)` |
| Actual Panic code 17 | deterministic diamond, `(3, 17)` |
| Actual other failure | deterministic diamond, `(4, 0)` |
| Raw payload `[5,7]`, surviving local 31, remaining addition | deterministic diamond, `(2, 38)` |
| Same raw payload with explicit nonempty scope-pop frame | normal witness and checked post, `(2, 38)` |
| ABI-encoded Error reason `[65,66]` | deterministic diamond, `(2, 66)` |
| Wrong final-state post `tag = 8` after success | proved false |
| Missing entry / malformed return / zero receiver | cannot supply any normal final-state witness |
| Malformed reason bytes `[1,2]` | existing reason decoder returns `none` |
| Callback reading with either payment flag | helper application refused by type; old semantic counterexample still proves false |

The source formula with the caller local retains it in its final context;
the separate `payload_witness` checks the explicit nonempty pop frame. These
are stated separately. Old observations are unchanged; two new complete
ordered payload observations are guarded. Examples exercise the generic
complete-run helper, not direct concrete instantiations of every specialized
clause interface. Those specialized interfaces are kernel-checked general
proofs, not newly certified source automation.

### Exact blocked source interface

`Frontend/Testing.lean:220–228` computes whether the source obligation calls
back and constructs `ValidT (.noCallback invariant[...]) obligation`;
lines 270–282 also select that reading for ordinary callback-bearing source
obligations. `ValidT` (`Calculus/CallbackHolds.lean:172`) quantifies over every
starting state; `holdsT` uses `holdsC` even with payment callbacks disabled.
The new helper takes a *particular* state and a normal deterministic run at
its actual oracle. It cannot inhabit this universally quantified callback
goal. `ExecS.tryRevert` and the existing `callback_diamond_false` proof remain
unchanged. Making source testing accept this evidence would require an explicit
new evidence-bearing obligation interface or a semantics/profile decision;
this increment takes neither decision and does not strengthen source specs
with oracle assumptions. This blocked path is stopped here.

All 20 upstream rows retain the exact earlier blocked evidence: 18 host/world
adapter dependencies and two incompatible EVM constraints. No unchanged blocked
replay is retried, no classification is counted as pipeline success, and no
fresh legacy/via-IR compiler or EVM execution evidence is claimed. Required
successful source fixture pipelines and full source automation therefore remain
open, outside what these kernel component controls establish.

### Continuation validation and reviews

Evidence is `/workspace/next10-diamond-try-evidence/continuation/`. Owning-file
MCP diagnostics are retained, including failed attempts, and successful final
results must be read from structured `success: true`, not the Python exit code.
A payload equality initially exceeded unchanged 200,000 heartbeats; instead of
raising the limit, `normal_of_halt_none` derives its exact output equation from
a kernel-checked normal-completion certificate. Postconditions use kernel
checking separately. A source quotation's retained-local context mismatch was
also repaired explicitly; it was not papered over by dropping a frame.

[Axioms audit](/workspace/next10-diamond-try-evidence/continuation/Axioms.lean) audits all 28 new public helper/control theorems. Actual output in
`axioms-observations.log`: 27 depend exactly on `[propext, Classical.choice,
Quot.sound]`; `malformed_reason` has no axioms. There are no new axioms or
`sorry`. Ordered payload observations are `(2,38)` and `(2,66)`. These remain
separate from the original 20-theorem audit and blocked upstream observations.

Independent finder and skeptic reread the new interface and expanded controls,
without Lean servers, builds or writes. Neither found a confirmed soundness
error. Finder's validation limitation (generic helper examples do not directly
instantiate every specialized clause interface) is recorded above. Its earlier
scope/frame and stale-documentation comments were addressed. Final policy,
full-build, per-file diagnostics and resource results are recorded below. No product script was modified; script-test changes are not applicable.

### Final continuation confirmation

Final owning-file MCP checks (`mcp-interface-guards.log`,
`mcp-example-guards.log`) and the changed-root check (`mcp-root.log`) report
`success: true`, `partial: false`, empty errors/dependencies. MCP emits a
teardown event-loop warning; its structured result was inspected separately.
All new module build output is warning-free; existing replayed baseline linter
warnings remain unchanged.

| Check | Exit | Seconds | Evidence |
|---|---:|---:|---|
| KeySort | 0 | 0 | `gates.tsv`, `key-sort.log` |
| check-orphans | 0 | 0 | `orphans.log` |
| check-layers | 0 | 0 | `layers.log` |
| check-automatic --strict | 0 | 0 | `automatic.log` |
| full `./run-lean.sh` | 0 | 7 | `full.log`: 690 library jobs, 259 TestSuite jobs, SolKey check OK |
| final 28-theorem axiom/observation audit | 0 | 4 | `axioms-final.log` |
| check-trust after tool-path repair | 0 | 5 | `trust-repaired.log`: 719 sources, 240 sites, 0 findings |
| inventory regeneration after tool-path repair | 0 | 0 | `inventory-repaired.log`: generated files current; no support-status diff |
| whitespace after tool-path repair | 0 | 0 | `whitespace-repaired.log` |

The initial policy batch's trust exit 1 and inventory/whitespace exit 127 are
retained in `gates.tsv`: the minimal inner Ubuntu image lacked Git/Python on its
PATH. This was a tool setup failure, not a policy finding. Only those three
affected checks were rerun after exposing the existing executor Python runtime
and read-only Git binary/loader through evidence-local wrappers/mounts. No
packages, credentials, tracked configuration or global configuration changed.
`policy-repair.tsv` records all three successful results. Full build and other
already passing gates were not needlessly repeated.

The full validation group recorded **382,570,496 bytes** accounted cgroup peak
and **1,108,124 KiB** sampled aggregate RSS (shared pages can be counted in
multiple processes). The policy-repair group recorded 165,986,304 bytes and
182,068 KiB respectively. Both verified `memory.max=12884901888`,
`memory.swap.max=0`, with zero OOM/OOM-kill events; the 16 GiB VM parent leaves
OS headroom. The fresh large build from the initial increment remains retained
separately; the continuation confirmation reuses on-disk artifacts. All checks
were serialized under the documented writer lock, with `LEAN_NUM_THREADS=1`
and explicit Lean `-j1` (including the final MCP server invocation).

New shared edits in this continuation are the two module imports and two
module-map rows, plus this owning feature record. All other code is in the two
new task-specific modules. The generated inventory is unchanged. Required
successful source/compiler/EVM fixture pipelines and integrated source
obligation automation remain **unresolved**, for the explicit interface and
out-of-lane adapter/EVM blockers above. No original gap statement, target
certificate, verdict, observation, invariant, callback semantics or budget was
changed to obtain these component passes.

## Universal-family continuation: proved semantic blocker

The same saved executor was recovered and checked at clean HEAD
`b4b9329bacc6ced55189be37b240045733de99ae`, on the same branch and remote.
Lean 4.24.0 and Lake 5.0.0-src+797c613 remain pinned; `origin/master` remains
`f4dee4a29c2e208b36db4a4161a4723c735cd775`, an ancestor. No new VM,
thread, branch replacement or clone was created. Actual KeySort passed before
proof edits: exit 0, 1 second, accounted cgroup peak 24,485,888 bytes, with
`memory.max=12884901888`, `memory.swap.max=0` and no OOM events. The VM parent
remains 16 GiB. Evidence is the `universal/` subdirectory of the task evidence.

### Why the requested family cannot be constructed

`Examples/Tactics/ExternalTryUniversal.lean` defines the exact parameter-free
plain source domain using the existing builders:

- `sourcePre = Frontend.Problem.callPre Probe [] false [] false [] true`: no
  parameters or msg.value read, the original 160-bit self-address bound,
  no explicit deployment-address override, and **no oracle restriction**.
- `Admissible σ = holds σ sourcePre ∧ holds σ (Fml.wt Probe)`.
- `sourceProblem`: that call premise followed by the unmodified
  `Problem.fml .diamond [] probe`, retaining `wt(storage)` and post `true`.
- `NormalSourceFamily`: every original admissible typed state has an exact
  normal `Prog.runFrames` witness. This explicitly requests normal completion,
  not the exhaustion alternative the existing diamond can accept.

These are the existing quoted `Probe` and actual source-domain/obligation
builders, **not** a new theorem identifying an imported compiled declaration.
The module adds six kernel-checked theorems:

| Theorem | Evidence |
|---|---|
| `empty_oracle_admissible` | `State.init Probe` satisfies both original premises. Receiver is 7, not zero; the oracle is empty. |
| `successful_oracle_admissible` | The previous successful word-9 oracle also satisfies exactly those same premises. |
| `no_normal_source_family` | The proposed all-admissible-state normal family is false: instantiate it at the admitted empty-oracle state, then use the existing missing-entry refusal. |
| `deterministic_source_refused` | Even deterministic universal validity of this unchanged source-obligation shape is false: its admitted state has caller revert, not exhaustion. |
| `callback_source_refused` | Independent of missing-entry reasoning, the previous reached-try counterexecution refutes callback validity under every invariant and payment flag. |
| `source_profile_refused` | The source obligation cannot hold under any existing `TransferSem` profile. |

Consequently success/Error/Panic/catch-all transport cannot fill the proposed
family: the original domain also admits a caller failure **before any clause**.
Removing that state or assuming an oracle entry/decoding outcome would strengthen
the specification's assumptions. Even such a strengthening would not remove
the independent callback `tryRevert` counterexecution. No such change is made.

The source route remains the one recorded above: callback-bearing source
obligations use universal `ValidT`, and `.noCallback` disables payment callbacks,
not try callbacks. A deterministic witness family would still not establish
that false universal callback goal. Neither a syntactically unreachable try,
a vacuous precondition nor resource exhaustion supplies a normal witness for a
reached try. Existing box support is not reclassified as diamond support.

**This path is stopped as a proved semantic blocker, not left as another
unimplemented witness helper.** Positive reached-try universal source integration
requires a human decision about the intended obligation/admissibility or
callback judgement. The task expressly forbids taking that decision here;
no D1/D2/profile decision, rule replacement or automation bypass is introduced.
The original step-11 claim remains unresolved under its preserved meaning.

### Additional actual source/compiler/EVM checks

The unchanged original `scripts/check-call-exception-vectors.mjs` passed all
**88** vectors (44 in each legacy/via-IR pipeline), with its existing ordered
return-value/revert-byte assertions and original gas/settings budgets. Compiler
bytes are the already retained audited 0.8.38+commit.1835d247, SHA256
`6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390`.
Settings remain optimizer enabled, Cancun, each original pipeline; the source
is `tests/solc/CallExceptions.sol`. The unchanged script installs real compiled
code and executes it in EthereumJS VM. Evidence: `evm-vectors.log`, exit 0,
4 seconds, accounted peak 373,280,768 bytes, sampled RSS 396,992 KiB.

The script's pinned external packages (`@ethereumjs/{vm,common,util}` 10.1.3,
ethers 6.17.0) were absent, so they were provisioned only under
`universal/reference/`, with an evidence-local on-disk npm cache, ignored
install scripts, the configured proxy and CA trust. Installation passed (26
packages, 4 seconds). Core dependencies, repository/user config and credentials
were not changed. No test script, source fixture or expected observation was
edited. These are actual additional source/EVM reference passes, **not** a
kernel-to-EVM simulation proof or success for the blocked upstream replay rows.

An independent unchanged native source verification was also attempted:
`node scripts/test-solidity.mjs --no-build --json --contract CallExceptions
--function failureCode tests/solc/CallExceptions.sol`, with the saved default
SolKey compiler (0.8.34), source domain and budgets. It compiled/imported without
errors, but its original unannotated diamond remained `pending: open proof
goals`, exit 1, 7 seconds (`source-failureCode.log`, source hash
`25f860c97fe9d929993bbcfb17fee77d6feeffabc80f5fd10ea0dc322b4afa18`). Its EVM
counterpart succeeds in the reference vectors; this is precisely not a reason
to claim the current universal callback source judgement proved. No annotation,
verdict or source assumption was changed. The pending result remains open;
it is not counted as a successful proof pipeline and was not retried unchanged.

All earlier 20 upstream tryCatch rows remain separately blocked: 18 host/world
adapters and two incompatible EVM constraints. Those unchanged failures were
not rerun. The new reference passes do not clear any of them or complete the
required original fixture replay. No excluded host/world/payment/creation or
other task lane was implemented.

### Final universal-continuation validation

`mcp-verified.log` reports structured `success: true`, `partial: false`, no
errors or failed dependencies for the new owning file. Early failed attempts,
`lean_goal`/`lean_multi_attempt` inspection and the harmless new axiom-message
line-wrapping repair remain retained. The two earlier implementation commits
and their evidence are preserved unchanged.

[Axioms audit](/workspace/next10-diamond-try-evidence/universal/Axioms.lean) / `axioms.log` audit all six new public theorems: each depends
exactly on `[propext, Classical.choice, Quot.sound]`. `previous-axioms.log`
rechecks the previous 28 proofs and complete payload observations. The original
20-proof audit remains retained separately. No new axiom or `sorry`.

| Gate | Exit | Seconds |
|---|---:|---:|
| check-orphans | 0 | 0 |
| check-layers | 0 | 0 |
| check-automatic --strict | 0 | 0 |
| check-trust | 0 | 5 |
| inventory regeneration | 0 | 0 |
| full `./run-lean.sh` | 0 | 3 |
| six new axiom audits | 0 | 4 |
| previous 28-proof/payload audit | 0 | 3 |
| whitespace | 0 | 0 |

`gates.tsv` and `gates-driver.log` retain actual results. Trust reports 720
sources, 240 inventoried sites, zero findings. Automatic counts remain 491/61
budgeted/11 refuted/zero pending. The generated inventory remains current,
with no support-status change. Full build includes TestSuite and the successful
377-taclet/131-read-bearing SolKey check. Existing replayed baseline linter
warnings are not new module warnings.

The final validation group peaked at **958,058,496 accounted bytes** and
**1,465,256 KiB sampled aggregate RSS**, with zero OOM events and zero swap
allowance. Every build/MCP/source/EVM group verified the 12 GiB/no-swap cap,
used the documented writer lock and one heavy check at a time, with
`LEAN_NUM_THREADS=1` and explicit Lean `-j1` through the temporary Lake config.
Caches and replay temporary files stayed on workspace disk; no unrelated
worker was terminated. The temporary config is removed before commit.

Independent finder and skeptic reviewed the new proofs without Lean servers,
checks or writes. They found no confirmed defect, confirmed the exact default
source domain, and required the quoted-program versus imported-declaration
boundary to stay explicit as above. Both independently found no sound positive
reached-try source path under the unchanged assumptions and callback semantics.
At that checkpoint the remaining blocker was a human semantics/statement
decision, not executor provisioning. The subsequent human FIRST OPTION resolves
that choice for this assignment, as recorded below. New shared edits are one module import, one module-map row and
this owning record; the implementation is one new task-specific module.


## Human-approved conditional account and native adapter repair

The human explicitly chose **keep existing semantics; prove explicit conditional
success and certified failure cases**. This replaces the universal witness-family
requirement for this assignment only. It does not authorize an altered callback
judgment or a stronger global admissibility profile. No proposed revert-agent
judgment is imported or required. The original universal source counterexamples
remain proved in `Examples/Tactics/ExternalTryUniversal.lean`; the leading-try
callback obstruction remains in `Counterexamples/DiamondTry.lean`.

### Exact typed statements

[`Semantics/TryConditions.lean`](../../Solidity/Semantics/TryConditions.lean)
adds `TRun.tryCondition`, indexed by the complete `TRes (Out C σ.H Γ)`, and
`tryCall_eq_iff`, proving both directions under either self flag. The predicate
uses actual receiver evaluation, actual self-dispatch/callee result or oracle
lookup, actual decoding, actual selected-body result, exact environment binding,
heap extension composition and scope drop. It never invokes the try evaluator
it characterizes or changes the admissible state space.

| Actual condition | Exact operational consequence |
|---|---|
| Receiver is zero | Caller revert, before lookup/catch |
| Non-self call, lookup absent | Caller revert; empty oracle is not a caught alternative |
| Oracle success, decoder fails | Exact decoder halt, outside catches |
| Oracle success, decoded returns | Exact success-body result and return-binding scope drop |
| Oracle Error/Panic/other category | Exact selected body result; catches restart at caller state |
| Actual self-callee normal result | Actual returned state/heap passed to success body |
| Actual self-callee revert/data/panic | Existing Error/Panic decoding and catch selection, with actual code |
| Other self-callee halt | Exact halt forwarded |
| Selected success/catch body halts | That halt propagates; no recursive catching of its own body |
| Receiver/argument capture prefix halts | Exact halt before try; no catch is entered |
| Capture prefix normal | Exact typed captured state and composed heap extension are used |

`catchCondition`/`catchData_eq_iff` reuse the existing `catchBytes`,
`CatchKind.decode` and `litBytesT` machinery. This retains actual Error/raw
payload bytes, allocation and handler outcomes, including malformed data and
handler failure. Existing payload allocation witnesses/normal transport are
preserved rather than replaced with a second allocator theorem.

[`Calculus/Sound/TryConditions.lean`](../../Solidity/Calculus/Sound/TryConditions.lean)
transports each explicit actual-outcome condition to the ordinary deterministic
formula with arbitrary remaining program, frames and postcondition.
`diamond_result_iff` and `holds_diamond_outcomes_iff` explicitly retain the
current diamond's **normal postcondition OR exhaustion** reading. Exhaustion is
not certified normal completion. No theorem promotes these guards to `ValidT`,
`ValidC`, `holdsC` or a global source assumption.

[`Semantics/TryCreateConditions.lean`](../../Solidity/Semantics/TryCreateConditions.lean)
characterizes only the already-existing typed `World.tryCreate` interface:
argument errors and static callers are outside its catch boundary; actual
creation success uses the returned world/handle; catchable creation errors run
the handler at the original world; divergence/exhaustion and handler failures
propagate. No world implementation, creation source adapter or payment rule is
added.

[`Examples/Tactics/TryConditions.lean`](../../Solidity/Examples/Tactics/TryConditions.lean)
proves `guarded_source_success` for any typed state satisfying its explicit
actual oracle lookup premise. Its original source-shaped diamond has no box
annotation and consumes the new specialized condition/formula interface. It is
conditional ordinary `holds`, not unqualified imported-source proof automation.
The earlier bounded witness/postcondition helper remains available. New kernel
controls retain success-body, catch-body, payload-body, continuation and frame
failures; missing context and zero/wide/reference-only deployment contexts are
refused. Typed validator proofs and runtime JSON/decimal parser tests are
separate evidence. The complete, truncated and trailing Panic controls certify
the unchanged exact-36-byte model policy; they do **not** assert that solc
rejects trailing bytes. Original zero-address, missing-entry, malformed-return,
payload observations and callback refusals remain unchanged.

### Narrow native integration and original fixture evidence

`scripts/self-try-adapter.mjs` admits only resolved direct `this` try calls to
primitive-ABI functions for native replay. It records the actual CREATE address
for the existing replay caller/nonce. The separate bytecode control checks that
address against actual deployment and refuses a mismatched context. Foreign
calls, context observations, constructors, effectful initializers, assembly,
creation and unsupported calls remain refused. Constructor-helper/modifier and
initializer-helper negative tests cover the independent review's confirmed
predeployment finding; that finding was repaired before final validation.

`Tools/Upstream.lean` validates the explicit context kind and nonzero 160-bit
address before installing it, refuses a required-but-missing context, and
retains it on successful and partial/blocked reports. Jobs without context keep
their prior input/report behavior. This is a concrete bounded execution input,
not universal verification of arbitrary callers/worlds.

Only `testing entrypoints` enables the frontend's new default-false
`retainUncaughtTryData` flag. When no catch-all exists, its hygienic raw-data
catch rethrows through the existing canonical `revertRaw` path. Explicit
catch-all bodies and ordinary specification/source obligation import keep their
prior behavior. This repaired the original `panic.sol` prefix's lost Error
bytes; the full fixture still stops at the independent mixed-return adapter.

The optional EVM runner executes actual pinned compiler bytecode. Its distinct
`direct-self-try-reference` context permits non-scalar callee signatures and a
recursive whitelist of memory/arithmetic/return/revert Yul operations. Unknown
Yul shapes/instructions, context/world instructions and constructor effects
remain refused. The native validator rejects this context kind. Complete raw
calldata, return and revert bytes are compared; wrong bytes, invalid calldata,
wrong deployment address and forbidden nested Yul instructions are negative
controls. Gas, instruction and fixture budgets remain unchanged. Optional exact
reference packages live on workspace disk, outside the core; all twenty locked
transitive package versions/paths match the tracked lockfile.

The unchanged twenty original archived source files and expectations were
replayed, including every required legacy/viaIR pipeline. The native before
report has twenty blocked files (eighteen host/world, two EVM constraints).
Current native replay has **four working, sixteen blocked, zero broken**;
its strict command exits **1**, so the mandatory whole-family gate is still
open. Separate reference replay has **sixteen working, four blocked**. Its
successes do not clear native coverage. `fixture-account.json/.md` records each
before/after row, source hashes, report paths and full ordered native/reference
byte comparisons. Both modes' two observations in each complete native fixture
match reference bytes; `panic.sol`'s first four observations in each mode also
match, but that prefix is explicitly not a complete fixture pass.

| Original fixture | Before native | Current native | Reference EVM |
|---|---|---|---|
| assert_pre_byzantium.sol | blocked | blocked | blocked |
| assert.sol | blocked | working | working |
| create.sol | blocked | blocked | blocked |
| invalid_error_encoding.sol | blocked | blocked | working |
| lowLevel.sol | blocked | blocked | working |
| malformed_error.sol | blocked | blocked | working |
| malformed_panic_2.sol | blocked | blocked | working |
| malformed_panic_3.sol | blocked | blocked | working |
| malformed_panic_4.sol | blocked | blocked | working |
| malformed_panic.sol | blocked | blocked | working |
| nested.sol | blocked | blocked | working |
| panic.sol | blocked | blocked | working |
| require_pre_byzantium.sol | blocked | blocked | blocked |
| require.sol | blocked | working | working |
| return_function.sol | blocked | blocked | working |
| simple_notuple.sol | blocked | working | working |
| simple.sol | blocked | working | working |
| structured.sol | blocked | blocked | working |
| structuredAndLowLevel.sol | blocked | blocked | working |
| try_catch_library_call.sol | blocked | blocked | blocked |

Remaining native dependencies are precise:

* `lowLevel`, `nested`, `structured`, `structuredAndLowLevel`, and `panic` reach
  `Tools.Upstream.ABI.program`'s existing mixed return capture refusal at a
  reference result (`multiple reference returns need a typed return adapter`).
  The existing capture path uses primitive tuple targets. General reference
  tuple/native value-entry support belongs to the excluded prior task lane;
  no unmerged work is imported.
* The six malformed/invalid payload fixtures require physical assembly or a
  reference-valued self-call argument adapter. The intrinsic model does not
  expose physical EVM memory. In particular `malformed_panic_2/_3` accept
  trailing Panic data in actual compiled execution, whereas the unchanged
  model's `decodePanic` requires exactly 36 bytes. Both facts are retained;
  no decoder or expected result is changed to force parity.
* `return_function` requires an external function-valued ABI return adapter.
  Its actual reference execution passes both pipelines; native admission
  remains refused.
* `create` requires source/world creation composition; `try_catch_library_call`
  requires library host/linking integration. Both remain blocked in reference
  replay as well. They are outside this lane.
* The two `_pre_byzantium` files require `<byzantium`; the fixed Osaka replay
  profile remains incompatible. They stay blocked, not silently reprofiled.

No callback-source integration is sound for a reached leading try diamond
under the current universal callback judgment; its existing certified
counterexample remains. Unconditional deterministic source validity also stays
refuted on the original state domain. The approved conditional account is
separate and does not claim full source-proof automation or step-11 completion.

### Fresh validation and review

The retained executor, original branch/HEAD (`fbc7dd0a` before this increment),
base ancestry, origin and Lean/Lake versions were rechecked. The initial
resumption KeySort gate passed before changes: exit 0, one second,
24,993,792-byte group peak. The first attempt failed only because the documented
lock directory had disappeared; that failure is retained, the directory was
restored, and the same VM was used. No replacement VM/clone/branch was created.

All new/changed Lean owning-file diagnostics report structured `success: true`,
`partial: false`, no errors or failed dependencies. Final root diagnostics are
also clean. Early failed proof/decoder/parser attempts remain retained and are
not counted as passes. New theorem signatures and full outputs are audited in
[conditional axiom audit](/workspace/next10-diamond-try-evidence/conditional/Axioms.lean) and `axioms-expanded.log`: 23 new proofs, of which 13
use exactly `[propext, Classical.choice, Quot.sound]`, five use `[propext]`, and
five use no axioms. Together with the preserved/rechecked earlier 20, 28 and six
proof audits, **77 distinct named proofs** have actual axiom evidence. No new
axiom or sorry was introduced.

| Command/gate | Exit | Seconds |
|---|---:|---:|
| Pre-edit current KeySort | 0 | 1 |
| Full `./run-lean.sh` after frontend/import changes | 0 | 2340 |
| Final warm `./run-lean.sh` after decoder controls | 0 | 4 |
| 23-proof final axiom audit | 0 | 2 |
| Prior 28 / original 20 / universal six audits | 0 / 0 / 0 | 3 / 4 / 2 |
| Final root owning diagnostics | 0, structured success | 3 |
| check-orphans / check-layers / automatic --strict | 0 / 0 / 0 | 0 / 0 / 0 |
| check-trust | 0 | 4 |
| Inventory regeneration | 0 | 1 |
| Script regression tests (84, no skip/fail) | 0 | 3 |
| Original call/exception EVM vectors (88) | 0 | 4 |
| Fifteen compatible original EVM fixtures, both modes | 0 each | 48 total |
| Remaining five EVM fixture commands | 1 / 1 / 1 / 0 / 1 | 15 total |
| Original native family final strict replay | **1** | 13 |

The remaining-five order is assert_pre_byzantium, require_pre_byzantium, create,
return_function, try_catch_library_call. The driver loop's exit zero is not a
passing family gate; the individual blocked exits are retained. Final native
family driver exit 1 is likewise retained. `final-gates.tsv`, `confirmation.tsv`,
per-fixture reports, script logs and cgroup outputs are in
`/workspace/next10-diamond-try-evidence/conditional/`. The full build includes
695 library and 259 TestSuite jobs and the 377-taclet/131-read-bearing check.
Trust reports 724 sources, 240 inventoried sites, zero findings. Automatic
counts remain 491/61 budgeted/11 refuted/zero pending. The inventory was
regenerated by its script with no inflated support classification.

All writes/checks use the documented writer lock and serialize heavy jobs.
Every group verifies 12 GiB memory and zero swap, with `LEAN_NUM_THREADS=1`
and Lean `-j1` through the temporary Lake config, not unsupported lake-build
flags. The long confirmation group peaked at **12,519,370,752 accounted bytes**
and **11,453,388 KiB sampled aggregate RSS**, with zero max-limit/OOM events;
these are different measurements, not interchangeable. The final warm group
peaked at 762,048,512 accounted bytes and 1,609,412 KiB sampled RSS. The reference
15-fixture group peaked at 434,409,472 bytes and 379,512 KiB sampled RSS.
The cap reserves the remainder of the 16 GiB VM for OS/outside-group work;
resumption also checked available VM RAM. No unrelated worker was killed,
cache moved to RAM, configuration changed or budget raised. Temporary Lake
configuration is removed before commit; disk caches and all earlier evidence
remain.

Independent read-only finder and skeptic reviewed the exact condition/formula/
creation statements, guarded example, failure controls, native context and
uncaught-data transport, and reference-only Yul/byte comparison expansion.
Neither used Lean/server/checks/writes. The finder confirmed the predeployment
constructor/initializer issue; conservative refusal plus three negative tests
repaired it. Both final reviews found no further confirmed defect and required
conditional `holds`, native observations and compiled-bytecode observations to
remain separate. Their reviewed scope excludes proving a world adapter,
physical-memory equivalence or universal source automation.

Shared edits: four root imports/module-map registrations; narrow entrypoint
frontend state/try rendering; native replay context validation; native/reference
runners and shared structural admission helper/tests; retry adapter provenance;
this owning record, the upstream adapter documentation and optional EVM README. No frozen fixture,
coverage target, original gap definition, decision theorem or callback semantics
was edited. Full original native source automation and its blocked pipelines
remain open dependencies, not a completed assignment.


## Native entry return bridge after checkpoint 99d0049a

This continuation kept the original branch and baseline. Published origin/master
was inspected read-only at cc155f36dc163e221b1f8279c56fb2006113ee7d. Its existing
scalar-memory return and World/WorldImport APIs were reused where applicable;
no base integration, unpublished import, callback change or global world rewrite
was needed. The pre-edit KeySort gate actually passed in one second with
24,825,856-byte cgroup peak, before the runtime pass marker was written.
All detailed commands, failed attempts, diagnostics and reports live in
[/workspace/next10-diamond-try-evidence/return-bridge](/workspace/next10-diamond-try-evidence/return-bridge).

The first original row was structured.sol, selected from the retained conditional
fixture account. Its native entry mixed two uint results with a string memory
result. The first bridge attempt retained the exact error: synthetic call had
“narrow positions none” where byte width 8 and the source bytes marker were
required. Hoisting the actual synthetic call in its exact local function scope
before the ordinary memory declaration supplied its actual typed result. The
ordinary shape check remains active; no refusal was removed. The original row
then passed all ordered observations in both legacy and viaIR.

`Solidity/Tools/EntryReturn.lean` serializes the actual original return frame
through the existing one-memory-result CallRet. It resolves the original
FunDecl and original nonrecursive prefix scope, runs existing calleeBody once
(including early returns, loops and modifier continuation), then ABI-encodes
its actual named return locals in declaration order. The observer reads those
encoded bytes directly, without a second ABI envelope. Original C, source
entry identities, self-try callee lookup, actual caught bytes, rollback and
handler scope are retained. This changes native ABI entry observation only;
ordinary source obligation generation and legacy ValidT/holdsC are unchanged.

Two bounded extraction plans share that serializer. The memory plan accepts
primitive arguments/results followed by one final bytes/string memory result,
requiring the original bytes marker and width 8. It refuses storage results,
multiple references, ordinary uint arrays that share intrinsic bytesR, function
markers, recursion and reserved-name collisions. The output-only function plan
accepts one nullary external-void function value among primitive results,
retaining its exact original fnRow signature. It refuses function/reference
arguments, other function signatures and invocation. The host guard also checks
all function/modifier inputs are scalar whenever this new return-only fragment
is present, including an outer function returning a function value around a
scalar-returning try. General function-reference arguments and lazy calldata
remain outside this work; no decoder/dispatch for that pending task is added.

`Solidity/Semantics/EntryReturn.lean` proves conditional exact call reduction,
source/encoder composition, heap-extension transport, caller restoration,
reference/alias identity, primitive binder order and exact argument/body failure
propagation. The hypotheses are actual typed argument, entry, source and encoder
execution results; no EVM observation is injected. A separate approximation
lemma transports a proved nondivergent bounded result to ordinary runR.
The frontend admission implications preserve exact source metadata and lookup.
These are conditional typed correspondence statements, not a general proof that
arbitrary raw wrapper construction refines Solidity/compiler execution.

Five EntryReturn example modules provide kernel-checked concrete executions:
success and actual Error reason with the same once-only counter; malformed bool
and zero-self refusal; wrong reference/tuple/storage/byte-marker controls;
loop early return with a live mutated alias and exactly one modifier continuation
(counter 11), including viaIR; empty defaults, signed int8 and bytes2 order and
padding; actual returned external function address 0x1234 and selector 0x946644cd,
eight trailing ABI zero bytes, tuple order and counter 1 in both modes. Normal
certificates also yield ordinary execution equalities. String-marker parser
controls remain runtime frontend tests, distinguished from kernel implications.
Large IR quotations use the existing safe kernel-checked declaration mechanism;
no recursion/heartbeat/fuel/test allowance was raised.

The complete native original family is now **10 working / 10 blocked / 0 broken**,
strict exit 1. Newly working versus 99d0049a are lowLevel, structured,
structuredAndLowLevel, nested, panic and return_function. All ten working rows
pass every original ordered observation in both required pipelines (27 calls
per pipeline); this includes all eight panic observations, not a partial prefix.
The separate pinned compiler/EVM replay remains **16 working / 4 blocked**.
The fresh reports preserve the current shared helper hash; the full-byte parity
account and per-fixture before/after table are in the return-bridge evidence.
Neither compiler/EVM replay nor concrete native execution proves universal
source validity. All earlier universal callback counterexamples remain negative.

The remaining native blockers have specific boundaries:

- Six malformed/invalid-encoding sources use physical Yul mstore/revert byte
  slices. Existing intrinsic heap objects are not physical EVM byte-addressed
  memory. invalid_error_encoding additionally calls g(bytes memory), while the
  current ExtArg is a primitive Simple, not an Args memory binder. A source
  adapter cannot manufacture a witness for that missing call argument primitive.
  malformed_panic_2/_3 return a 256-byte Panic payload in d(), which pinned EVM
  catches as code 67; current decodePanic requires exactly 36 bytes. The retained
  kernel trailing-payload refusal certifies this concrete mismatch. Changing
  the decoder or injecting expected bytes is not authorized.
- create.sol requires contract-world creation/source composition; the existing
  standalone World.tryCreate and import APIs do not supply that composition for
  the native single-contract State. try_catch_library_call requires linked
  library and storage-receiver world execution. These excluded lanes are not
  replaced by a synthetic oracle or the entry serializer.
- Two pre-Byzantium sources explicitly require <byzantium and a literal gas8000
  self call. Current Osaka reports remain blocked. Both legacy and viaIR compile
  under the same pinned compiler for historical targets, as the retained profile
  probes show. A concrete separate-runner proposal is retained in
  [profile-proposal.md](/workspace/next10-diamond-try-evidence/return-bridge/profile-proposal.md);
  historical EVM execution is not claimed, and the current profile is unchanged.

Final full library/TestSuite, Corpus, frozen TestSuite, source-admission,
orphan/layer/strict-automatic/trust/inventory and actual axiom checks passed.
The post-function full run took 116 seconds; Corpus 12 seconds; source admission
2 seconds. Strict automation reports 491 automatic, 61 budgeted, 11 refuted and
zero pending; trust reports 731 sources, 240 inventoried sites and zero findings.
The new audit contains 46 named proofs; with the preserved 77 earlier proofs,
123 distinct names have actual axiom output, limited to the repository's
propext/Classical.choice/Quot.sound foundations. Native family and doc-path gates
retain their actual failing exits. Initial pin-path/CLI/compiler-setting and
proof/shape/quotation failures are preserved separately from corrected passes.

Heavy checks were serialized under the writer lock, LEAN_NUM_THREADS=1 and
Lean -j1 via the temporary Lake configuration. Every build/check group had
verified memory.max=12884901888 and memory.swap.max=0, disk caches and no OOM.
The final full-gate group peaked at 2,527,895,552 cgroup bytes and conservatively
sampled 4,912,096 KiB summed RSS. The earlier fresh per-file group peaked at
3,525,042,176 bytes. The 16 GiB VM retained OS headroom and 23 GiB disk space.
Temporary invocation settings do not modify tracked/user configuration.

Independent read-only finder and skeptic reviews covered typed capture,
serialization, source scope, admission, both-mode kernel controls and byte
replays, without Lean/server/checks/writes. Confirmed findings were fixed:
original-prefix visibility instead of all-C scope; bytesR source-marker/width
checks; combined byte-and-counter certificates; safe IR quotation without a
budget raise; and outer-function-return input-guard coverage. Both reviewers
found no further ABI/execution defect and retained the general raw/compiler
refinement limitation. Final evidence/doc review is recorded alongside logs.
Shared edits are limited to the native Upstream entry adapter, its structural
self-try helper/tests, root registrations/module map and owning adapter docs;
core syntax/operational judgments and frozen sources/verdicts are unchanged.
Step 11 is still incomplete where the original required native fixtures remain
blocked; this return bridge closes the compatible independent source layer.


Current confirmation evidence is `confirm.tsv`: all nine owning-file structured
MCP results are clean; `confirm-script-tests.log` records **93/93** current-helper
tests passing. The earlier missing-default-compiler-path test exit 1 remains in
`latest-script-tests.log`; it is not a current passing result. The checked
[fixture account](/workspace/next10-diamond-try-evidence/return-bridge/fixture-account.md)
and [full-byte parity manifest](/workspace/next10-diamond-try-evidence/return-bridge/fixture-parity.json)
verify 54 complete native/reference observations and 128 frozen/reference
observations in order, with current helper/compiler hashes and all twenty source
hashes. Four reference exclusions are explicitly historical, not fresh passes.
The [actual axiom account](/workspace/next10-diamond-try-evidence/return-bridge/axiom-account.json)
contains all 123 audited names. Corrected doc-path checks actually exit 1 for
both current checkout and pinned baseline, with the same twenty missing-reference
lines; two task-own external evidence citations were repaired. The earlier
baseline invocation exit 127 was a wrapper/mount error and supplies no baseline
evidence. Final current confirmation peaked at 3,474,202,624 cgroup bytes,
3,841,672 KiB sampled aggregate RSS, no OOM/swap, in 186 seconds. A script driver's
exit 0 does not replace the individual retained nonzero gate exits in its table.


## Creation-try source continuation after e7921de5

The task-specific source adapter now executes the complete unchanged original
`tryCatch/create.sol` through both compiler pipelines. It recognizes whole source
declarations and exact declaration references, rather than replacing creation by
an oracle outcome. The original source SHA256 is
`574de0c72abb81159c2d91801ba248006e403eea581e78f119a7966cd20a2058`.
The compiler is the existing pinned 0.8.38 artifact; neither profile nor decoder
changes are enabled. All original callback counterexamples remain negative.

`Solidity/Semantics/CreationTryFrame.lean` composes the existing `World.tryCreate`
with intrinsic caller programs and their actual heap extensions. Its conditional
laws cover argument failure before creation, actual returned handles, completed
caught constructor halts, uncaught divergence/exhaustion, handler scope, caller
tails and atomic rollback. Data-binding Error handlers use existing `decode` and
`litBytesT`, retaining actual bytes. An argument failure cannot enter constructor
handlers. A handler/tail failure cannot re-enter those handlers. `constructorArg`
binds the actual evaluated argument once before the actual imported constructor
call. These laws do not establish a new global source or callback judgment.

`Solidity/Frontend/CreationTryImport.lean` checks a closed source shape: stateless
noninheriting contracts, a single uint256 argument constructor with empty body or
literal Error revert, no payment or modifiers, and no-argument nonpayable methods
with named bool/string returns. Exact local declaration identities connect the
prefix argument, constructor target, returned handle, address comparison and
Error payload assignment. Numeric subdenominations, wrong references, unknown
contracts, constructor effects, extra tails and unsupported shapes are refused.
All source contracts are accounted for. The source command has no box annotation.
The existing ordinary source obligation representation is unchanged.

The adapter lowers admitted bodies to existing intrinsic programs, exact scoped
frames, real constructor calls and the existing ABI encoder. Temporary captures
are dropped using their typed extensions; the encoded output object is retained
outside that scope and read directly, without a second ABI envelope. Constructor
imports retain failure data and preserve the default self flag. The pending
caller frame is committed once. This composition is restricted to unpaid local
caller code and the explicitly checked constructors: it is not a general paid
world-call refinement. In particular, stale caller funds must not be used to
model arbitrary constructor payments. No global world semantics is changed.

The published prerequisite inspection is retained in
[/workspace/next10-diamond-try-evidence/creation-source/published-prerequisites.log](/workspace/next10-diamond-try-evidence/creation-source/published-prerequisites.log).
Published origin/master was `dedb3aee5743025aeb6d8f7219c9b6b9c1e00e5d`;
its ContractWorld blob was `9f22396da6266fa083413689a5c2e4141e545a95` and
WorldImport blob `8c5f0e05c9c5a4976612b05112a357e4e4d333ef`.
The first 390 ContractWorld lines containing the used primitives are identical
locally and published (SHA256
`de956c31582b2dcf2809326a440a866aee9b413b329603f66c0d33f0e4d696a9`).
No prerequisite commit was imported; the retained original branch/base survives.
Published later payment/certificate APIs are not required or copied here.

The legacy and via-IR AST fixtures come from the same unchanged full source,
using the existing compiler world-metadata option. Kernel examples prove both
complete ordered output vectors, actual arguments 3 and 8, successful installation
and failed-constructor rollback, collision refusal and a wrong-reason-byte
negative. Generated `run_approx` theorems quantify over this adapter's typed
world/context inputs; successful bounded executions agree with ordinary
execution. They are not universal Solidity/compiler refinement theorems or
`ValidT`/`holdsC` claims. Script recognizer checks and finite compiled-bytecode
replays remain separate evidence.

The replay context fixes the actual funded sender, deployed caller, zero value,
zero caller funds, timestamp and starting nonce. The task-specific standard RLP
address calculation supplies fresh addresses; it does not add a nonce primitive
to World. Actual EVM nested-creation receipts independently record failed creation
at nonce 1 with the original Error bytes and successful creation at nonce 2 with
runtime code. Targets match the native execution. Empty vectors, zero/wrong
context, unknown methods and altered expected bytes are explicit controls.

An initial recognizer review found that a numeric subdenomination could be lost;
both host and Lean admission now refuse it, with a negative test. Review also
required nonempty vectors and exact runtime context. Both were fixed. The new
runtime-only `evalExpr Json` site is explicitly inventoried; no new proof axiom
or trust exemption is introduced. The affected scripts have 110 passing tests.

Remaining native rows retain the six physical-assembly/nonprimitive-ABI cases,
linked-library composition and two historical pre-Byzantium profiles. The
malformed_panic_2/_3 256-byte payload versus 36-byte kernel decoder counterexample
and historical profile proposal remain human-review items, not enabled changes.
The complete assignment remains open at those boundaries.


### Creation continuation validation

Fresh complete-family replay is **11 working / 9 blocked / 0 broken** natively;
the native strict command retains exit 1 because those nine are unresolved.
Seventeen original fixtures complete both reference pipelines, with three
historical excluded reports retained as blocked, not counted as fresh passes.
All **58** native/reference ordered observations and **132** reference/frozen
ordered observations match signatures, failure flags and every return/revert
byte. The creation row also matches actual target addresses, creation nonces,
installation flags and full failed-constructor Error bytes. Its legacy and IR
kernel certificates independently compute the same original ordered outputs.

The full row-by-row before/after account and complete byte evidence are retained
at [/workspace/next10-diamond-try-evidence/creation-source/fixture-account.md](/workspace/next10-diamond-try-evidence/creation-source/fixture-account.md)
and [/workspace/next10-diamond-try-evidence/creation-source/fixture-parity.json](/workspace/next10-diamond-try-evidence/creation-source/fixture-parity.json).
Actual transitive audits cover **151 distinct declarations**: 28 new creation
statements/generated correspondences and all 123 retained task declarations.
Only `propext`, `Classical.choice` and `Quot.sound` occur; no new proof axiom is
introduced. Eight owning-file MCP checks report structured success, no partial
results and no failed dependencies. Script controls pass 110/110 and the existing
exception-vector regression passes all 88 controls.

Full library plus SolkeyTestSuite, Corpus, complete frozen TestSuite, source
admission, orphan/layer checks, strict automatic/trust checks and regenerated
inventory checks have actual successful exits. Documentation-path checking
retains exit 1 with exactly the same 20 baseline missing references and zero new
findings. The earlier optional audit invocation against the fixture-only archive
failed because that archive lacks upstream Changelog.md; its log is retained.
The documented default inventory regeneration and freshness check succeed; no
generated file was hand-edited. The original fixture sources and expected
verdicts/observations are unchanged.

The interrupted validation driver and surviving Corpus container were recovered
without replacement. Its actual successful run took 1,249 seconds, with
11,426,820,096 cgroup peak bytes and 11,570,276 KiB sampled aggregate RSS; no
OOM, max-limit or swap events occurred. A subsequent uninterrupted serialized
Corpus confirmation is separately recorded. The final bounded commands enforce
12 GiB memory and zero swap, one Lean thread and explicit Lean -j1. Disk caches
remain on disk. Timing footers describe command execution; driver wall times
also include writer-lock queue time. Interrupted/nonfinal rows remain recorded
rather than being relabeled as final passes.

| Final command | Exit | Actual command seconds | Cgroup peak bytes |
|---|---:|---:|---:|
| final-automatic.log | 0 | 1 | 21127168 |
| final-axioms-conditional.log | 0 | 2 | 159350784 |
| final-axioms-continuation.log | 0 | 4 | 155869184 |
| final-axioms-original.log | 0 | 4 | 154894336 |
| final-axioms-return.log | 0 | 4 | 176492544 |
| final-axioms-universal.log | 0 | 3 | 187637760 |
| final-axioms.log | 0 | 3 | 172756992 |
| final-doc-paths.log | 1 | 3 | 8622080 |
| final-frozen.log | 0 | 1 | 41648128 |
| final-full-confirm.log | 0 | 1172 | 9611038720 |
| final-inventory-check.log | 0 | 1 | 10723328 |
| final-layers.log | 0 | 1 | 77082624 |
| final-native-family.log | 1 | 61 | 484532224 |
| final-orphans.log | 0 | 1 | 63262720 |
| final-script-tests.log | 0 | 5 | 568836096 |
| final-source-admission.log | 0 | 2 | 242360320 |
| final-trust.log | 0 | 5 | 169148416 |
| final-vectors88.log | 0 | 4 | 372088832 |
| final-whitespace.log | 0 | 1 | 4685824 |
| corpus-recovered.log | 0 | 1249 | 11426820096 |
| corpus-final-serialized.log | 0 | 12 | 1118474240 |
| inventory-recovered.log | 0 | 1 | 10862592 |

Detailed gate, diagnostics and axiom accounts are in the linked creation-source evidence directory. Finder and skeptic independently reviewed code and owning claims read-only, with no Lean server or check execution. Confirmed denomination, vacuous-vector, runtime-context and stale-overview findings were repaired. The full assignment is still incomplete at the nine remaining native rows and the unchanged callback/profile/decoder boundaries described above.


## Linked library try source continuation after ca314a5b

The complete unchanged original `tryCatch/try_catch_library_call.sol` now executes
through the existing installed `World.libraryCall`, rather than a library oracle
or library-owned storage. Both original f rows were first checked in both native
pipelines, with g still explicitly blocked. The same proved composition was then
extended to g. The complete linked row now passes both native pipelines with all
four ordered original output tuples and every dynamic string/Error byte. Its
caller storage observations are 0, 0, 9, 9. Full-family counts and final gate
results are recorded below only after their actual confirmation.

`LibraryTryImport` checks whole caller and library declarations: actual library
kind, function/formal/argument/result IDs and names, using-for library/struct,
caller storage root and struct member, prefix, branch and Error payload binders.
The library bodies are quoted at caller contract types. The scalar argument is
read from its actual x=8 prefix. The storage formal is a fresh live alias to
C.t; existing name renaming preserves its source identity while avoiding the
model's prohibition on a local named like a state root. The actual view bodies
read their real arguments/root or emit their source Error("failure"). Neither
library storage nor library funds replace caller state. No general ABI/lazy
calldata, linking/world implementation, payment adapter or profile is introduced.

The caller enters once. Its actual prefix is run and committed before the
installed library operation reloads caller storage, so g's t.x=9 is visible to
the library and survives a caught callee revert. Resumption refreshes caller
storage/funds from the selected world, retaining its original heap, locals,
aliases and transaction context and clearing the already-settled incoming net
ledger. Actual source success/Error tails and the existing ABI encoder then
execute once; failures in argument evaluation, return decoding or a caller tail
do not enter/re-enter the library catch. Existing outer atomic failure rolls
back the candidate caller prefix for an uncaught failed linked boundary.

The general World Entry.result API may fail. This narrower typed interface
therefore requires `RawLibrary.total`: every successful body state's raw
extractor must return actual raw words normally. Generated getters prove this
by reading the actual typed uint result. Potentially failing uint decoding uses
the existing Binders decoder outside the catch. A raw descriptor whose extractor
can fail cannot inhabit this interface. This closes the initial review caveat;
no World.libraryCall or generic library semantics was changed.

Universal conditional laws cover the actual installed operation, exact caller
frame/context/ledger, storage-root alias, successful/caught/uncaught outcomes,
decode errors and tail failures. Generated per-method approximation theorems
compare bounded caller programs with their ordinary reading, using the identical
actual library operation. Kernel certificates prove all four ordered outputs
in one world, full ordinary execution equality, and the caller storage sequence.
The separately compiled IR source has its own complete ordered certificate.
Wrong role, installed identity, caller frame, absent library, missing raw result,
wrong caught bytes, malformed bool/byte input, static mode and atomic rollback
are kernel controls. Structural tests also refuse wrong root/field/type, using
or function identities, argument order, unsupported effects/tails and shapes.
These are conditional/concrete typed executions, not ValidT/holdsC or universal
Solidity/compiler refinement proofs. Legacy callback counterexamples remain.

Reference replay now consumes only the validated exact library directive,
deploys actual L, links C at pinned solc's exact FQN/20-byte placeholder ranges,
and deploys C on the same machine. It rejects overlaps, wrong/out-of-range sites,
unknown links and leftover nonhex placeholders before constructing bytes/hashes.
Actual library deployment is checked against the explicit runtime context.
Deployment/link evidence survives blocked/broken outcomes too. Complete receipts
record library501f…ebc9, caller8f04…6cb2, actual runtime code and each actual
DELEGATECALL's caller identity, sender/value, return words or full Error bytes.
The original optimizer, Osaka, 100M gas and 5M-step settings are unchanged;
requesting linkReferences is additional compiler output, not a new profile.

An initial combined source check hit the unchanged 12GiB limit. Isolating the
check found the actual generated alias-name error; a fresh declaration-preserving
alias fixed it without raising budgets. The failed source/check and OOM footer
remain retained. Corrected complete ordered checks and separate storage/ordinary
certificates pass under the original limits. No stopped check is relabeled pass.
Independent early finder/skeptic reviews also required total raw extraction,
actual linked-context address checking and retention of failure-path receipts;
all confirmed findings were repaired with controls. Final reviews/gates follow.

The published prerequisite inspection is in the task evidence: origin/master
204eb1545cbf57e436196e4cba346075515b7279 still has ContractWorld blob
9f22396da6266fa083413689a5c2e4141e545a95 and WorldImport blob
8c5f0e05c9c5a4976612b05112a357e4e4d333ef. The relevant existing library API is
unchanged. Published mutation-only WorldLinked/certificates do not provide this
scalar/storage try-and-return composition. No commit/base integration was needed.
Original base f4dee4a and all prior checkpoints/exports/failures are preserved.

Evidence is retained at
[/workspace/next10-diamond-try-evidence/library-source](/workspace/next10-diamond-try-evidence/library-source).
The six physical-assembly/nonprimitive-ABI rows, two historical profile rows,
and 36-byte versus trailing256-byte Panic review item are not changed here.
The original assignment is not complete while its remaining source rows/gates
are unresolved. No push or merge; installed controller alone owns integration.


### Linked continuation final validation

The full original native family is **12 working / 8 blocked / 0 broken**. Its
strict command retains **exit 1**, not a passing family gate. Eighteen original
fixtures complete both fresh reference pipelines; two retained historical-profile
reports remain blocked and are not counted as completed replays. All **66**
completed native/reference and **140** reference/frozen ordered observations match
signatures, failure flags and every return/revert byte. The linked row additionally
matches each actual library/caller address, one delegate invocation per call,
caller self/sender/value, complete library Error/return bytes and native caller
storage 0,0,9,9. The copied original test source retains its exact frozen SHA256.

Actual transitive axiom audits cover **191 distinct declarations**: all151 retained
checks plus40 new frame/source/transport/control statements. Only standard Lean
`propext`, `Classical.choice` and `Quot.sound` occur. No project axiom, sorry or
proof-budget increase was introduced. Nine changed Lean files have structured
MCP success, no partial diagnostics and no failed dependencies. All146 affected
script tests and88 existing exception-vector controls pass.

Full library/SolkeyTestSuite, Corpus, complete frozen TestSuite, source admission,
orphan/layer checks, strict automatic/trust gates, inventory freshness and
whitespace checks have actual successful exits. The final confirmation includes
the small unused-instance cleanup reported by the initial full build. Historical
documentation paths retain exit1 with the identical20 baseline missing references
and zero new findings. The earlier source OOM and subsequent alias/type/diagnostic
failures remain recorded; corrected final gates are separate successful commands.
No failed/stopped check is relabeled as a pass.

| Final command | Exit | Actual command seconds | Cgroup peak bytes |
|---|---:|---:|---:|
| inventory.log | 0 | 1 | 10661888 |
| full.log | 0 | 2393 | 11788374016 |
| corpus.log | 0 | 64 | 1114001408 |
| frozen.log | 0 | 1 | 41226240 |
| source-admission.log | 0 | 2 | 239771648 |
| orphans.log | 0 | 1 | 63401984 |
| layers.log | 0 | 1 | 62324736 |
| automatic.log | 0 | 1 | 20824064 |
| trust.log | 0 | 5 | 173752320 |
| script-tests.log | 0 | 3 | 485539840 |
| vectors88.log | 0 | 4 | 367812608 |
| axioms.log | 0 | 5 | 176689152 |
| axioms-creation.log | 0 | 3 | 177295360 |
| axioms-return.log | 0 | 4 | 175919104 |
| axioms-conditional.log | 0 | 2 | 159576064 |
| axioms-continuation.log | 0 | 4 | 157122560 |
| axioms-original.log | 0 | 4 | 155123712 |
| axioms-universal.log | 0 | 3 | 185266176 |
| native-family.log | 1 | 79 | 488886272 |
| doc-paths.log | 1 | 3 | 8425472 |
| whitespace.log | 0 | 1 | 4440064 |
| confirmation-full.log | 0 | 1 | 380973056 |
| invocation-control.log | 0 | 1 | 4673536 |
| axioms-final.log | 0 | 4 | 175607808 |

Final groups verify12GiB memory and zero swap, with disk caches, one Lean thread
and explicit Lean-j1 through the task-only temporary Lake configuration. Cgroup
physical peak and sampled aggregate RSS are retained separately. Driver wall
seconds include writer-lock queue time; actual command seconds are the footer
values above. MCP/builds were serialized. An earlier MCP internal import compile omitted explicit-j1 and the first root diagnostic timed out; both are retained as nonfinal evidence. The corrected container-only configuration mount and compiled imports support the final clean nine-file diagnostic pass at unchanged limits. See mcp-invocation-repair.md. The same VM/branch and all baseline
setup/cache files were preserved; no new VM, unpublished import, push or merge.

Per-fixture before/after/full-byte evidence, actual axiom sets, diagnostic
records, gate exits/timings/resources and repaired review findings are retained in
[/workspace/next10-diamond-try-evidence/library-source/fixture-account.md](/workspace/next10-diamond-try-evidence/library-source/fixture-account.md),
[/workspace/next10-diamond-try-evidence/library-source/fixture-parity.json](/workspace/next10-diamond-try-evidence/library-source/fixture-parity.json),
[/workspace/next10-diamond-try-evidence/library-source/axiom-account.json](/workspace/next10-diamond-try-evidence/library-source/axiom-account.json)
and the linked task evidence directory. Independent finder/skeptic reviews were
read-only, with neither Lean server nor checks/writes. Confirmed total-extractor,
linked-context and receipt-retention findings were fixed with controls.

The original assignment remains incomplete at its six physical-assembly/nonprimitive
ABI rows and two pre-Byzantium/gas8000 profile rows. The existing trailing256-byte
Panic versus36-byte decoder counterexample and historical runner proposal still
require human review; neither was changed or enabled. Legacy callback judgments,
all six original gap statements/target certificates, target/exclusion/admissibility
predicates and frozen observations/verdicts retain their meanings.


## Approved Panic decoder correction after ffabfb22

Human decision call_ce385a5125ae4d06b1e976f6c1561935 authorizes the narrow
Panic decoder correction, while retaining the existing callback/default/source
judgments. Earlier sections' exact36-byte policy/refutation and pending-review
statements describe the retained ffabfb22 checkpoint, not this corrected decoder.
The previous files/certificates remain in history and the panic-decoder evidence.

Pinned solc0.8.38's actual try_decode_panic_data uses gt(returndatasize(),0x23)
then returndatacopy(0,4,0x20). The intrinsic decoder now requires the exact selector
and at least36 bytes, reads only the first32 bytes after the selector and ignores
the suffix. Uint256 has no invalid full32-byte encodings; byte values are
intrinsic UInt8. Short/truncated or wrong-selector payloads remain refused.
Pat.notPanic excludes only short patterns or known selector mismatches, so long
unknown Panic-shaped data cannot unsoundly lose its handler. The original
universal Pat.notPanic_decode theorem retains its meaning; its length proof is
updated. Existing deterministic/callback soundness consumers use this theorem
and decoder directly; no broader callback rule or target/profile is changed.

Controls distinguish exact/trailing/256-byte data, unsigned byte order, zero and
high-bit words, incorrect/missing selectors, truncated data and partial patterns.
Actual typed self-call continuations and raw failure capture are tested separately
from source/EVM observations. An existential callback Panic alternative does not
eliminate legacy callback failure alternatives or establish holdsC/ValidT.
Physical-memory/Yul source admission is still absent for the six original rows;
no fixture may be promoted merely because its decoder discrepancy is repaired.

Historical-profile investigation compiled both original gas8000 fixtures in
both pipelines for five target forks and queried the existing pinned EVM opcode
tables. No historical fixture was executed and no historical runner was enabled.
See [/workspace/next10-diamond-try-evidence/panic-decoder/compatibility-proposal.md](/workspace/next10-diamond-try-evidence/panic-decoder/compatibility-proposal.md)
and exact compiler inputs/outputs/compatibility.json. The current profile's
blocked results and frozen observations remain unchanged. Runtime compatibility
is not established by compilation or opcode-table membership alone.

A static scan additionally finds REVERT(0xfd) instruction sites in both
historical generators while that opcode is absent from the pinned pre-Byzantium
engine tables. This is an exact compatibility boundary, not a proof that the
original valid rows fail: capped inner failure paths may intentionally trap.
No historical execution or profile support is claimed.

The original Osaka panic fixtures were separately replayed in both pipelines
with actual child-call receipts: all16 ordered observations match full frozen
outputs, child sizes3/6/36/256, and actual256-byte suffix has byte0x80 at offset95.
The kernel long zero-suffix datum is representative only. The proved arbitrary
suffix theorem establishes the decoder's independence of those bytes, without
injecting EVM reference bytes into Lean. The actual typed code-capture control
reads67 from caller storage after binding and scope pop.

Actual validation and retained nonzero exits follow.


### Panic correction actual final validation

The complete original native family is **12 working / 8 blocked / 0 broken**;
its strict command retains **exit1**, not a passing family gate. Eighteen original
fixtures complete both fresh compiler/EVM pipelines; two historical-profile
reports remain blocked, not successful replays. All **66** native/reference and
**140** reference/frozen ordered observations match signatures, failure flags
and complete bytes. The supplemental16 original Osaka panic observations add
actual child-call receipts, not extra unique rows beyond that family count.

Actual transitive axiom audits cover **217 distinct declarations**: all191 prior
names plus20 additional controls and six existing critical soundness consumers.
Only `propext`, `Classical.choice`, `Quot.sound` occur. The updated former
trailing-data policy theorem is explicitly identified above; no false old-model
claim is asserted under the corrected decoder. Five changed Lean owners have
structured MCP success, nonpartial results, empty errors and no failed imports.
All146 affected script controls and88 existing exception vectors pass.

Full library/SolkeyTestSuite, Corpus, complete frozen TestSuite, source admission,
orphan/layer, strict automation/trust, generated inventory and whitespace checks
have actual successful exits. Historical doc paths retain actual exit1 with the
identical20 baseline missing references and zero new findings. No failed,
stopped, rejected or blocked invocation is relabeled passed.

The first full attempt reported missing Decidable equality for the capture
control and was stopped after that real source error: overall143,3565s,
7394652160byte cgroup peak,zeroOOM. The SAME full result equality was repaired
via a kernel-checked positive toOption and constructor inversion, with no global
Eq instance or expected-output weakening. Rejected temporary done insertion did
not execute; safe read-only trials preceded the complete repair. Initial MCP
import timeouts, cache invalidations, direct-normalization recursion stops and
trial/API/layout errors remain in the evidence. No limits were raised.

Every final group verifies12GiB/no swap and one Lean thread/explicit-j1, with
private disk caches and OS/disk headroom. The documented writer lock is held
inside subsequent one-shot jobs and logs/footers write directly to task disk;
reattachment does not release the lock early. The same surviving initial full
container was adopted, not duplicated. No VM/service/monitor/timer or tracked
configuration was added. Exact runtime configuration is retained externally.

| Final command | Actual exit | Command seconds | Cgroup peak bytes |
|---|---:|---:|---:|
| inventory.log | 0 | 1 | 10743808 |
| full.log | 0 | 4778 | 12176072704 |
| corpus.log | 0 | 83 | 1142280192 |
| frozen.log | 0 | 1 | 41742336 |
| source-admission.log | 0 | 2 | 271446016 |
| orphans.log | 0 | 1 | 64249856 |
| layers.log | 0 | 1 | 64196608 |
| automatic.log | 0 | 1 | 20983808 |
| trust.log | 0 | 4 | 168980480 |
| script-tests.log | 0 | 4 | 498679808 |
| vectors88.log | 0 | 4 | 371331072 |
| axioms.log | 0 | 6 | 196743168 |
| axioms-library.log | 0 | 4 | 175718400 |
| axioms-creation.log | 0 | 3 | 175685632 |
| axioms-return.log | 0 | 4 | 175558656 |
| axioms-conditional.log | 0 | 2 | 160595968 |
| axioms-continuation.log | 0 | 5 | 156876800 |
| axioms-original.log | 0 | 4 | 155463680 |
| axioms-universal.log | 0 | 3 | 185905152 |
| native-family.log | 1 | 69 | 484274176 |
| doc-paths.log | 1 | 3 | 8679424 |
| whitespace.log | 0 | 1 | 4440064 |
| reference-assert.log | 0 | 3 | 406450176 |
| reference-require.log | 0 | 3 | 376475648 |
| reference-simple_notuple.log | 0 | 4 | 377458688 |
| reference-simple.log | 0 | 4 | 376172544 |
| reference-lowLevel.log | 0 | 3 | 383307776 |
| reference-structured.log | 0 | 4 | 383250432 |
| reference-structuredAndLowLevel.log | 0 | 4 | 387510272 |
| reference-nested.log | 0 | 4 | 371040256 |
| reference-panic.log | 0 | 4 | 399904768 |
| reference-return_function.log | 0 | 4 | 378736640 |
| reference-invalid_error_encoding.log | 0 | 4 | 433549312 |
| reference-malformed_error.log | 0 | 4 | 372355072 |
| reference-malformed_panic.log | 0 | 4 | 383725568 |
| reference-malformed_panic_2.log | 0 | 5 | 383332352 |
| reference-malformed_panic_3.log | 0 | 4 | 385687552 |
| reference-malformed_panic_4.log | 0 | 4 | 384155648 |
| reference-create.log | 0 | 4 | 385839104 |
| reference-try_catch_library_call.log | 0 | 4 | 374800384 |
| compatibility.log | 0 | 3 | 276107264 |
| compatibility-opcodes.log | 0 | 1 | 55480320 |
| panic-original-receipts.log | 0 | 1 | 77705216 |
| invocation-control.log | 0 | 1 | 4665344 |

Actual command footers distinguish command time from host driver/writer-lock
queue time and sampled aggregate RSS from physical cgroup peak. Evidence and
per-fixture before/after account:
[/workspace/next10-diamond-try-evidence/panic-decoder/fixture-account.md](/workspace/next10-diamond-try-evidence/panic-decoder/fixture-account.md),
[parity](/workspace/next10-diamond-try-evidence/panic-decoder/fixture-parity.json),
[axioms](/workspace/next10-diamond-try-evidence/panic-decoder/axiom-account.json),
[gates](/workspace/next10-diamond-try-evidence/panic-decoder/gate-account.json),
[diagnostics](/workspace/next10-diamond-try-evidence/panic-decoder/diagnostics-final.json),
[actual child receipts](/workspace/next10-diamond-try-evidence/panic-decoder/panic-original-receipts.json)
and [compatibility proposal](/workspace/next10-diamond-try-evidence/panic-decoder/compatibility-proposal.md).

Independent finder/skeptic reviews are read-only, with neither Lean server nor
checks/writes. Confirmed hash-label, representative-tail description and exact
capture-proof issues were repaired. Final evidence consistency review is retained
with the export. Historical investigation comprises20 compiler rows for the two
sources (12pre-Byzantium plus8Byzantium/Osaka controls), four extra Osaka panic
compile rows, five opcode tables and20linear scans. Candidate0xfd sites include
embedded code/data in creation streams and are not CFG reachability or execution
evidence. No historical runner was implemented/enabled or original row executed
at a new profile. Exact halt/gas/receipt compatibility remains an open proposal.

Whole-assignment completion remains blocked by six physical-memory/nonprimitive
ABI source rows and two historical-profile rows. The Panic trailing-data decoder
mismatch itself is corrected; its original assembly source producer/composition
is still absent. No rejected ABI/lazy-calldata work, world/payment rewrite,
callback-phase integration, target/exclusion change or frozen verdict adjustment.


### Static compatibility continuation after aca22c93

The evidence-only [historical PC/harness and six-obligation analysis](diamond-try-static/README.md)
separates executable creation from copied runtime, attributes each fd site using
compiler metadata, resolves local jump targets without claiming complete CFG
reachability, and names exact missing source producers/capture correspondences.
No runner/profile or Lean semantics changed; original native12/8 strict exit1,
reference18/2 and66/140 observations remain retained checkpoint evidence.
Historical execution is unauthorized and the physical/ABI producer lanes remain
explicit boundaries, not forced passes.


### Setup compatibility continuation after71e77d87

The [caller-entry setup/gas/frame/layout investigation](diamond-try-setup/README.md)
traces raw runCall and upstream harness nonce/checkpoint/address/gas boundaries,
adds static intrinsic/deposit arithmetic and occurrence-specific compiler return
labels, and refines the missing local layout relation. No historical engine,
runner, evaluator, profile or model was implemented; original fixture gates
remain open. Prior completed compilations/maps and Lean gates were not repeated.


### Fixture-local comparison design aftereef9fc8a

The [comparison dependency/relation/API decision design](diamond-try-comparison/README.md)
records exact compiler observation dependencies and two unapproved next directions:
a strictly fixture-local observational correspondence or the exact upstream host
API with a pinned bounded backend. No historical execution, trusted relation,
runner, model/profile change or source gate pass follows. Original12/8strictEXIT1
and all earlier proofs/receipts/exports remain retained.


### B backend prerequisite after4b9a4054

The [exact-host backend/ABI/instruction-bound investigation](diamond-try-backend/README.md)
records targeted installation absence, test-only host dependency closure, the
vendored README12/header13 discrepancy and exact missing shared abortable step
API. No backend was fetched/built/loaded/executed; A/B remain unapproved choices
and original12/8strictEXIT1 persists. All previous evidence is preserved.


### Complete physical producer DESIGN aftera9daa3bb

The human requested the [full intrinsic physical-byte producer/correspondence
design](diamond-try-physical-design/README.md), with [typed schemas](diamond-try-physical-design/typed-interface.md)
and [nonvacuous proof/milestone plan](diamond-try-physical-design/proof-plan.md).
No producer, admission/D3/target/profile or semantics change is implemented.
Exact five-row bundle/reference identities and existing mechanism/speed history
are retained; original native12/8strictEXIT1 and historical backend pause persist.

Official-source-only backend feasibility: [evmone0.22 pins, build edges and abort-interface limits](diamond-try-official-evmone.md). No backend/producer implementation or historical execution is approved by this addendum.

Human-approved bounded [M1 computed producer/capture](diamond-try-m1.md) implements only the reviewed first proof component. P4/P5b/P8, original source admission and all eight native blocked rows remain open.

[Post-M1 published-interface/readiness design](diamond-try-post-m1-design.md) updates P4/P5b/P8 only from current published source and actual M1; all execution permission and implementation boundaries remain in force.

Compatible Osaka validation after M1: [actual results and held groups](diamond-try-osaka-validation.md). Original native family remains exit1; no source-admission or P4/P5b/P8 change.

Original c()->f(36) static path/source milestone: [reviewable design](diamond-try-c36-path-design.md); held Cancun groups remain plan-only.

Cancun execution approval is recorded, but the mandatory pre-attempt envelope remains absent: [exact existing API/pins and minimal tooling proposal](diamond-try-cancun-envelope.md). Both groups remain unrun; no permission question is repeated.

Constructed closed carrier proofs and the approved modern5M pre-attempt facility: [actual kernel/runner validation](diamond-try-carrier-budget.md). Two Cancun groups now pass under enforced bounds; original native12/8 strictEXIT1 and P4/P5b/P8 stay open.
