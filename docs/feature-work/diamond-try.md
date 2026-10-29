# External try execution witnesses — partial step 11

**Step 11 remains incomplete at its native source-adapter boundary.** The human
selected unchanged semantics and explicit conditional success/failure statements
for this assignment. That resolves the earlier request for a profile decision;
no stronger global admissibility premise is introduced. The current increment
provides exact typed conditions for all external/catch-data outcomes, ordinary
formula transport, and conditions for the existing creation-try interface.
Four original fixtures now pass native replay in both pipelines; sixteen pass
separate compiler/EVM replay. Neither replay establishes universal source
validity. The remaining native dependencies are enumerated below.

All original unconditional claims and their certified refutations remain.
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
- `axioms-and-observations.log`, `Axioms.lean`: actual audits and observations.
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

`Axioms.lean` audits all 28 new public helper/control theorems. Actual output in
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

`Axioms.lean` / `axioms.log` audit all six new public theorems: each depends
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
`conditional/Axioms.lean` and `axioms-expanded.log`: 23 new proofs, of which 13
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
