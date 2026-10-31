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
| 5 / dependencies | Local availability recorded below; external cache access was not tested and is not claimed blocked. No dependency or toolchain was upgraded. |
| Backfill A | Partial: existing G01 finite-prefix order, consistency, completion and resource-indexed noncompletion observation transport proved. Pinned-EVM word/byte encodings and signed/truncation/boundary controls are still open; no actual infinite EVM execution is constructed. |
| Backfill B | Partial: approved hash-premise suffix/membership and published local-checkpoint observation/relation transport proved. Transaction-world rollback, ledger/nonce/log composition, actual execution-prefix linkage and application to each opcode and exact secondary obligation accounting remain open. |

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
`Controls.lean` includes nonempty prefixes, exact bytes `[0,255]`, completed versus
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
This is availability evidence, not an external cache/network denial. No external
packages were fetched. The small Docker runtime image was fetched separately.

The vendored interpreter still declares `TargetSchedule := "Cancun"` in
`Bridge/vendor/EvmYul/Wheels.lean`. The existing assembler record documents
Osaka CLZ parsing/execution and truncated-PUSH right-padding disagreements.
Its shared arithmetic fragments cannot silently stand for an Osaka transition
or full account/transaction correspondence. This lane may not rewrite the
vendored or reserved reference implementation.

`scripts/roadmap-v15-obligations.py` reads the published backend opcode table
and emits 150 individual byte/mnemonic rows, each explicitly open for V15,
with a primary accounting area and G46.06 composition obligation. This is primary
routing only: exact secondary clauses (for example RETURN/REVERT byte ranges
and EXTCODECOPY/RETURNDATACOPY memory) remain open. This is not
a new semantics, an opcode coverage claim or a decision that every opcode is
emitted by the admitted source profile. Its output also lists the 168 existing
G03 feature IDs whose EVM owners include this lane; no global ledger or manifest
was edited. Coordinator reconciliation: attach this backfill evidence to
G46.05/G46.06/G47, retaining every existing open status. No feature closes.

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


## Preparation checkpoint handoff

This commit packages partial backfill only; G46.01 is not marked passed and the
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
