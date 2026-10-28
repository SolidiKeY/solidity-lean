# External try execution witnesses — partial step 11

**Step 11 is not complete.** This increment adds deterministic external-try
execution equations, normal-return witnesses, and a state-indexed deterministic
witness-to-formula interface with allocated catch-data transport. It does not replace
`tryCallDiamond`, `catchDataDiamond`, or add symex/source-obligation automation.
The original gaps, target certificates, exclusions, Waivers, DecisionTheorem,
profile choices and existing verdict/observation pins are unchanged.

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
