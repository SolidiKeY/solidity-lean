# External try execution witnesses — partial step 11

**Step 11 is not complete.** This increment adds deterministic external-try
execution equations and normal-return witnesses. It does not replace
`tryCallDiamond`, `catchDataDiamond`, or add symex/source-obligation automation.
The original gaps, target certificates, exclusions, Waivers, DecisionTheorem,
profile choices and existing verdict/observation pins are unchanged.

## Proved scope

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

Focused module build passed; final per-file MCP results for all three files
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

Shared edits are only the three module registrations in `Solidity.lean`, three
module-map entries, and the owning calls/exceptions document link. All proof and
control implementations are new modules unique to this task. No checking-cost
refactor, payment/world/creation/library rule, quantified invariant, ordinary
recursive-type migration, top-level revert-outcome modality or profile decision
is included. No push or merge is performed.

Still open: a sound deterministic witness-to-formula/taclet interface and branch
automation; data-binding catch witnesses/rules; source obligations without box
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
