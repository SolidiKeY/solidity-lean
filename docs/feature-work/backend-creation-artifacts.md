# G44.02 creation artifacts

This lane supplies component proofs, not whole-contract source-to-bytecode
preservation. Base: `50658f41061b366d6e503d1e8a3a324a281e9fca`; branch:
`codex/solidity-independent5-20261029/creation-artifacts`.
The checkout is `/workspace/scratch/creation-artifacts-assigned`; the original
`/workspace/solidity-lean` checkout remains untouched.

## Scope and prerequisites

Manifest IDs: `constructors`, `inheritance`, `immutables`, `libraries`,
`creationTry`, `externalLibraryCalls`, `constructorLifetime`, `creationCode`, `runtimeCode`,
and `newContract`.
Their current local evidence includes `Frontend/SolcJson/Contract.lean`,
`Frontend/WorldImport.lean`, `Semantics/ContractWorld.lean`,
`Semantics/ContractWorldCertificates.lean`, `Frontend/Source.lean`,
`Frontend/SolcJson/Body.lean`, and `docs/solc-alignment.md`.
These interfaces are reused read-only. No source representation or semantics
is replaced. G04 R04 and G06 B25/D20 identify the missing deployment and installed
code composition. G01's `CodeUnit`, `Artifact`, `PublicCorrectness.creates_table`
remain integration interfaces, not consequences of this component.

The actual human decisions in [solidity-scope.md](../solidity-scope.md) apply:
Osaka; solc 0.8.38's two pipelines; code-size limits idealized; exact return/revert
bytes; whole-input libraries with no externally preassigned link map. Raw account
code observations and CREATE2 remain excluded. Linking here is internal artifact
construction, not permission to admit a user-provided link map. Source inheritance,
constructor execution/order, world/account/address/nonce/payment/rollback semantics,
resource-failure simulation and whole pinned-EVM step agreement remain parent
obligations. No full-group theorem is claimed.

## Runtime and reproduced gap

The exact base is clean on the assigned branch in an isolated worktree.
Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, and Lake
5.0.0-src+797c613 run in one ordinary task-owned Debian bookworm container.
Docker's actual child cgroup reports `memory.max=12884901888` and
`memory.swap.max=0`. The earlier systemd/namespace failures remain failures.
The original gap control (`tests/creation-artifacts/gap-before.lean.txt`)
checks an inhabited 20-byte assembler placeholder and then fails on the absent
`Solidity.Backend.Creation.installs_runtime` identifier. Its exact output is
`/workspace/scratch/creation-artifacts-evidence/gap.log`.

`lake -f creation-runtime.lakefile.toml build Solidity.KeySort` passed:
`Built Solidity.KeySort (1.7s)` and `Build completed successfully (2 jobs).`
The untracked alternate configuration adds explicit `-j1`; `LEAN_NUM_THREADS=1`.
Peak child cgroup usage at that gate was 138698752 bytes; OOM counters were zero.
RUNTIME_GATE_PASS applies to this measured runtime prerequisite only.
No Lean MCP diagnostics tools are exposed; serial per-file CLI checks substitute.

## Checkpoint 1: artifact layout

`Backend/Creation/Artifact.lean` defines `Immediate` (256-bit bound), minimal
`Immediate.width` using the existing `byteWidth`, and `Immediate.instr` using
existing `Instr` and `toBytesBE`. `Immediate.read` proves exact immediate decoding.
`wrapper` emits length, source offset, zero destination, CODECOPY, length, zero
return offset, RETURN. `wrapper_size` and `wrapper_length` prove its exact size
`2 * byteWidth length + 8`; `runtimeOffset_fits` proves the source offset always
fits PUSH1 (at most 72). Empty runtime uses PUSH0 length and offset 8; lengths
255/256 transition from offsets 10 to 12. Kernel equalities pin nontrivial and
empty byte encodings.

`Artifact` separates arbitrary runtime bytes, arguments and the assembler's
link-reference format. `runtime_slice`, `args_slice`, and `initcode_length`
prove exact extraction and argument separation without assuming successful
execution or decoding runtime bytes. `fromAssembly` preserves the committed
assembler output without changing its fixpoint or relocations. It explicitly
records the assembly base: references remain absolute in that coordinate system.
The later linking layer must certify/rebase them before runtime patching.
`Assembler.lean:632` (`link_patch`) concludes equality of patched whole-code bytes
and preservation of offsets/nonlibrary instructions; it has no creation execution
premise or installed-code conclusion. `Opcode.lean:498` only defines encoded size.

Per-file check command: `lake -f creation-runtime.lakefile.toml env lean -j1
--tstack=131072 Solidity/Backend/Creation/Artifact.lean`; clean exit 0.
Concrete control development first exposed dependent-immediate simplification
failures; explicit width and list congruence lemmas fixed them without increasing
proof budgets. Both independent read-only finder and skeptic reviews found no incorrect layout
theorem. Confirmed findings were fixed: added inhabited artifact and assembler
combination controls, negative range/separation controls, axiom pins, explicit
assembly origin, explicit local proof signatures and a supplemental import-closure
check. Neither reviewer used a Lean server. Review details are saved in the
evidence directory.

## Component queue status

1. Artifact layout: implemented; focused target and controls pass; two reviews complete.
   Final global gates remain lane-wide obligations.
2. Independent slice execution and installed-runtime theorem: implemented,
   kernel checks/controls and independent finder/skeptic follow-ups pass.
3. Certified assembler linking, disjointness, exact widths and refusal: implemented;
   focused target and independent review follow-ups pass.
4. Typed immutable patches and frame/installation proofs: implemented;
   focused target and independent review follow-ups pass.
A. Constructor-prefix return/revert composition: implemented; focused target,
   inhabited controls and independent review follow-ups pass.
B. Determinism, commutation, encoding/provenance and external vectors: implemented;
   kernel checks, 16 external vectors and independent review follow-ups pass.

Component work is complete. Final gate outcomes and exact-base comparisons are
recorded below; the inherited global documentation-path failure remains open.

Checkpoint 1 focused build: `Build completed successfully (6 jobs).`
Axiom output for `Immediate.read`, `wrapper_size`, `Artifact.runtime_slice`,
and `Artifact.args_slice`: `[propext, Classical.choice, Quot.sound]` only.
Static outputs: `168 core modules, 0 reach the elaborator`; `768 reachable,
0 orphaned, 0 not allowed`; `trust: 783 sources, 241 inventoried
implementation/recovery sites, 0 findings`. Task-local import closure passes.
The documentation path script fails with 46 missing references in inherited
files; same-base classification remains a final validation obligation. No new
creation-document finding appeared in the recorded output. This failure is not
marked passed.

## Checkpoint 2: independent slice execution

`Execution.fetch` decodes exactly one intrinsic instruction, refusing truncated
PUSH bytes. `fetch_encode` proves its exact instruction boundary. `effect`
independently specifies PUSH (modulo 2^256), zero-padded CODECOPY, RETURN and REVERT;
stack underflow and unsupported instructions are refused. `run` is a finite
fuelled byte interpreter. `Exec` means an actual successful finite run.
`run_add` proves successful outcomes persist with extra fuel;
`Exec.deterministic` proves unique outcomes, with only `[propext, Quot.sound]`.
This is not source fuel, a gas model, or whole pinned-EVM agreement. Memory lists
represent byte contents, not MSIZE, allocation rounding or resource charges;
in particular a zero-length write may change representation length without
changing any observed byte. Those operations are outside this exact slice.

`wrapper_exec` derives the wrapper's returned bytes from the independent runner.
`installs_runtime` states `Exec a.payload a.payload [] [] (.returned a.runtime)`
for every bounded runtime byte list and arbitrary constructor arguments.
`Placement.installs` handles relocated wrapper entry under an arithmetic
alignment certificate and empty entry stack/memory. It does not assume a source
constructor reaches that entry. Its offset uses minimal `byteWidth`; prefix
lengths 245/246 give offsets 255/257 (the second width increases the header).

Inhabited kernel controls cover empty runtime, nonempty arguments, lengths
31/32/33 and 255/256, and offset PUSH1/PUSH2 transitions. A literal malformed
wrapper (`wrongSource`) copies bytes `[0x2a, 0, 0xaa]` instead of the supplied
`[0x60, 0x2a, 0]`; `wrongSource_exec` proves that execution and determinism
refutes the desired output. Separate controls check too-short/long/wrong-offset
reads and correct zero-padding and overwrites.

Focused commands: `lake -f creation-runtime.lakefile.toml build
Solidity.Backend.Creation.ExecutionChecks` and separately
`lake -f creation-runtime.lakefile.toml build
Solidity.Backend.Creation.PlacementChecks`. Placement target passes (8 jobs).
No heartbeat/recursion budget was raised: a concrete associativity/control
reduction failure was fixed by explicit length simplification.
The two independent reviews initially found missing unique-outcome and actual
malformed-execution controls and offset-width transitions. These are now added;
both follow-up reviews confirm the fixes with no new correctness finding.
Neither review used a Lean server or build. Placement is a suffix-entry theorem,
not execution of its prefix (backfill A). `fetch` refuses truncated PUSH data,
unlike full EVM zero-padding; generated wrappers contain complete immediates,
and this refusal is an explicit slice boundary.

## Checkpoint 3: linking and certified regions

`Regions.patchAt_length`, `patchAt_get`, `patchAt_frame`, and `patchAt_commute`
prove exact bounds, byte replacement, untouched bytes and disjoint order
independence for the existing assembler overwrite. `LinkSite` fixes address width
at 20; `LinkTable` certifies exact metadata origin and pairwise region separation.
`assembler_regions` derives bounds and separation from every actual successful
assembler output, not from a caller-supplied separation premise.
`tableOfAssembly` constructs a typed table from actual base-zero runtime assembly.
`assembler_link_package` uses the committed `link_patch` theorem to link that
runtime, retain its jump-coordinate base zero, keep wrapper and arguments intact,
and derive exact installation by the independent runner. `assembler_link_wrapper`
is separately only a whole-code embedding equality; it is not an installed-runtime
jump relocation theorem. No assembler algorithm or fixpoint is duplicated.

`deployable` refuses unresolved metadata; raw artifact bytes remain representable
and executable as data, so this optional gate is not a global impossibility claim.
`resolve_missing` refuses a missing address before any patching; total addresses
are typed vectors of exactly 20 bytes. `linked_args`, `link_payload_bounds` and
`truncated_arguments_refused` preserve/validate the separate argument section.
Argument validation checks byte length, not ABI decoding. The public compiler's
refusal of externally preassigned link maps remains unchanged.

The actual two-library `actual_assembly_combination` is inhabited, constructs a
certified table and proves base-zero assembler/link/package/install composition
with nonempty arguments. Controls also reject wrong relocation by actual byte
inequality, missing/unresolved addresses, overlap/out-of-bounds intervals and
truncated arguments; an inhabited two-site control exercises disjoint commutation.
Both independent finder/skeptic reviews found the missing actual-assembly and
origin composition controls. Those were fixed as above; both follow-up reviews
report no new correctness finding, without Lean servers or builds.
Headline axiom pins contain only `propext`, `Classical.choice`, `Quot.sound` subsets.

## Checkpoint 4: immutable runtime patches

`ImmutablePatch total Key` carries a bounded location and exactly 32 encoded
bytes. `immutablePatch?` rejects a raw offset when the whole word does not fit.
`checkImmutableTable` checks pairwise separation; adjacent regions are accepted.
`patchImmutables_length` and `patchImmutables_frame` preserve size and every
untouched byte. `patchImmutables_read` consumes the disjointness certificate to
prove each member's bytes survive all later writes; `ImmutableTable.read`
proves its complete exact word can be extracted from the final runtime.
`patched_installs` composes that runtime with the independent installation proof.
`compatible_iff` specifies an executable check of every immutable/link pair;
`combinedArtifact` requires that cross-table certificate and `combined_installs`
installs its linked and patched runtime. `immutable_link_commute` proves the
single disjoint address/word rewrite commutes.

The immutable-only helper `patchedArtifact` retains unresolved metadata and is
not itself a combined linking API. The certified combined API must be used for
that claim. Keys identify provenance labels; proving source declaration identity,
repeated-reference value agreement, source initializer evaluation and postdeploy
write exclusion remains with source constructor/lifetime composition.

Inhabited controls cover two adjacent words, exact last-byte bounds, one-byte
overflow, internal overlap rejection, exact values/readback, untouched boundaries,
argument retention, actual installation and exclusion of the old unpatched result.
Mixed link/immutable controls accept separated tables, reject cross overlap and
install a combined artifact. Independent finder and skeptic initially identified
missing generic readback and cross-table safety. Both follow-up reviews confirm
those fixes with no remaining concrete correctness finding; no Lean servers or
builds were used by reviewers. Focused immutable target passes (10 jobs), axiom
pins use only standard `propext`, `Classical.choice`, `Quot.sound` subsets.

## Backfill A: constructor-prefix composition

`Prefix` certifies actual finite `fetch`/`effect` continuation steps.
`Prefix.exec` composes those steps with a final byte execution.
`exit_exec` proves CODECOPY followed by either RETURN or REVERT over arbitrary
prefix stack/memory. `read_write_zero` proves prior memory cannot contaminate
returned bytes. `constructor_compose` composes independently checked prefix
steps with an aligned exit wrapper, returning runtime or reverting the exact
supplied byte list. No source constructor execution is assumed or derived.
PUSH omits the EVM's stack cap in this byte-content slice; pinned-EVM agreement
must handle resources and headroom (the wrapper adds at most three entries).
Generated standalone wrappers start with an empty stack; arbitrary-stack prefix
composition is only a component theorem, not unrestricted pinned-EVM agreement.

`copyPrefix_steps` is a real nonempty prefix that copies the first code byte to
memory offset 32. `copyConstructor` proves its composition with return/revert
wrappers and nonempty arguments. Negative executions reject RETURN on the revert
path, truncated revert bytes, and argument-contaminated revert bytes.
Both independent reviews and their follow-ups pass; confirmed explicit-signature,
stack-boundary and exact-byte-negative findings were fixed. No Lean server/build
was used by either reviewer. Focused constructor target passes (9 jobs); its
headline axiom pins use only standard subsets of `propext`, `Classical.choice`,
`Quot.sound`. Parent source inheritance/initializer order, world rollback,
account installation and payment composition remain open exactly as scoped.

## Backfill B: laws, provenance and external creation vectors

`link_permutation` proves arbitrary permutations of pairwise-disjoint typed
library sites yield identical bytes. Its proof folds over length-certified byte
states and uses the existing assembler overwrite. `Exec.deterministic` already
proves unique slice outcomes. `Artifact.payload_deterministic` fixes runtime/args;
`Artifact.sections_unique` additionally requires equal runtime lengths before
recovering both sections from equal payloads. Link metadata is deliberately not
recoverable from raw bytes. `wrapper_decode` reuses the existing exact decoder law.
`Provenance` stores a bounded generated section interval and a bounded interval
of actual supplied source-file contents. `global_bounds` and `bytes_exact` certify
its global byte range. Source-map fidelity/semantic provenance is not inferred
from supplied labels or ranges and remains a producer integration obligation.

Inhabited controls include a three-site link permutation, a conflicting-overlap
order counterexample, distinct metadata records with identical byte payloads,
section recovery, valid provenance extraction and an uninhabitable out-of-bounds
location. Focused laws/provenance target passes (13 jobs); axiom pins contain only
standard subsets of `propext`, `Classical.choice`, `Quot.sound`.

`tests/creation-artifacts/Export.lean` exports actual artifact functions into
`vectors.jsonl`. The SHA256 of `vectors.jsonl` is
`d8453e2544375fd911a2077491e8dc40b2bc9c4fb506d77c4d37926c69d5b9fc`.
`node scripts/check-creation-artifacts-vectors.mjs` passed 16/16 actual Osaka CREATE
transactions under EthereumJS 10.1.3, checking installed account code or exact
revert bytes. It covers empty/word/PUSH boundaries, linking, immutables, combined
patches, constructor return/revert and malformed source/return ranges. Dependencies
are isolated task fixtures, not Lean/core dependencies. The offset-transition
external tests use executable JUMPDEST prefixes; the kernel placement witnesses
use zero prefixes as suffix-entry layout data and do not execute them. These are
finite independent external tests, not whole pinned-EVM or source preservation
proofs. The initial export failed on a Lean-version string-constructor name;
`String.mk` fixed it without a budget change, with failed output retained.

Independent finder and skeptic reviewed the laws, records, exporter, all generated
rows and the exact 16/16 output without Lean servers or builds. Their follow-ups
confirm no remaining concrete finding; the distinct-record uniqueness control
and explicit executable-prefix/suffix-entry distinction address their notes.

## Final validation and committed handoff

All component queues 1–4 and backfill A–B are implemented, with kernel proofs,
inhabited positive/negative/combination controls and independent finder/skeptic
reviews. Six source checkpoints are committed individually. Final cleanup only
renames the owned modules to `ArtifactChecks` and `ArtifactLaws`, updates their
imports, and guards all 36 headline axiom outputs with exact `#guard_msgs` pins.
The outputs contain only standard subsets of `propext`, `Classical.choice`,
`Quot.sound`; the cleanup changes no theorem, premise or proof budget. Independent
finder and skeptic checked the cleanup and recorded no remaining concrete finding.

The final source checks run serially inside the single measured 12 GiB/no-swap
container, under the documented writer lease. Lake uses a private disk cache
keyed by toolchain/source inputs and `--rehash`; every actual Lean invocation has
`-j1` and `LEAN_NUM_THREADS=1`. Per-file CLI checks use Lake-generated `--setup`
import mappings when present. Cached artifacts need not materialize named local
`.olean` files. Earlier direct checks with missing renamed import artifacts, and
one check requesting a nonexistent fetched-module setup file, remain failed
records; subsequent fresh checks correctly resolve the actual artifact mapping.
No Lean MCP diagnostics tool was available. No concurrent Lean/LSP ran.

| Gate command (inside bounded container) | Actual outcome / decisive output |
|---|---|
| `lake build Solidity.KeySort` with the task's alternate `-j1` configuration | PASS: built 1.7s; completed 2 jobs; RUNTIME_GATE_PASS |
| `lake build Solidity.TestSuite.Derived17` | PASS: 228 jobs; module 131s; full closure 29:46.57 |
| Per-file `lake env lean -j1 --tstack=131072` for all 17 owned files, with generated setup mappings where present | PASS: fresh diagnostics, including 36 guarded headline axiom reports |
| `./run-lean.sh` | PASS: 768 default/import jobs, 262 TestSuite jobs; parsed 377 taclets, 131 read-bearing, annotations match the real pinned rules |
| Exact-base `./run-lean.sh` in an immutable source snapshot with private Git metadata | PASS at the exact assigned base; no historical mismatch waiver used |
| Exporter plus exact `cmp` against committed JSONL | PASS: actual artifact functions reproduce every committed vector |
| `node scripts/check-creation-artifacts-vectors.mjs` | PASS: 16/16 actual Osaka CREATE transactions, EthereumJS 10.1.3 |
| `node scripts/check-layers.mjs` | PASS: 168 core modules, 0 reach the elaborator |
| `node scripts/check-creation-artifacts.mjs` | PASS: task-owned import closure restricted to existing assembler/opcode/jumpdest and this lane |
| `node scripts/check-orphans.mjs` | PASS: 783 reachable, 0 orphaned, 0 not allowed |
| `bash scripts/check-trust.sh` | PASS: 798 sources, 241 inventoried sites, 0 findings |
| `node scripts/check-automatic.mjs --strict` | PASS: 491 automatic, 61 with step budget, 0 manual; 11 refuted; 0 pending |
| `bash scripts/check-testsuite.sh --complete --solkey "$PWD/tests/migration/solkey/keyext.solidity.examples"` | PASS: 564 = 552 derived + 11 refuted + 0 pending + 0 divergent + 1 excluded; 2 skip; pinned snapshot and rules checksums agree |
| `bash scripts/check-doc-paths.sh` | FAIL: 46 inherited missing references; exact-base and final head finding lists are identical, including ambiguity records; no new finding |

The complete cold default/TestSuite/SolKey run took 2:08:52 and reported peak
RSS 8863664 KiB. The earlier Derived17 closure reported peak RSS 11429108 KiB;
the child cgroup peaked at exactly 12884901888 bytes, with 337 hard-limit events
and zero OOM/OOM-kill events. These are measured resource results, not increased
proof/test budgets. Per-file final logs also record time/RSS. Initial runtime and
failed configuration probes remain historical evidence and are not passed gates.
KeySort's measured successful timestamp is 2026-10-29T19:01:29Z; final validation
and export timestamps in the external handoff bound the measured work interval.

The global documentation-path failure is not marked green. Its 46 missing
references are outside owned files and already occur at the exact base; the
lane adds no finding. Repairing those inherited references is outside this
assignment's authorized write set. This required failing global gate prevents
marking the entire persistent goal complete, despite completed component work
and all Lean/build/TestSuite gates passing. No semantic scope question is needed.

Current source integration anchors (read-only) are `Language/Features.lean`
constructors `libraries`, `inheritance`, `constructors`, `immutables`,
`newContract`, `constructorLifetime`, `creationCode`, `runtimeCode`, and their
existing requirement clauses; `Frontend/SolcJson/Contract.lean`'s
`SolcFun.ctorMember`, `contractLineage` and immutable initializer processing;
`Semantics/Deploy.lean`'s `State.deploy` and `Contract.deployT`; and
`Roadmap/Contracts.lean`'s `CodeUnit`, `Artifact`, `Artifact.initcode`,
`Artifact.PrefixFree`, `createsOf`, `PublicCorrectness.creates_table`.
Manifest IDs and local-evidence paths are listed above. The coordinator must
connect these exact producers/consumers; no manifest status or global ledger was
changed by this lane.

Remaining parent integration requirements are source constructor/inheritance/
initializer order and ABI argument decoding; immutable declaration identity,
initializer values, repeated-reference agreement and later-write exclusion;
whole-input artifact-table prefix freedom and creation-event binding; library
session identity/internal addressing and refusal of externally supplied link
maps; source-map producer fidelity; and full source/lowering/pinned-EVM/Bridge
step agreement with gas, stack headroom, account/address/nonce/payment/rollback
and code-deposit behavior. Resource/code-size abstraction remains as approved,
with explicit 256-bit operand bounds. No CREATE2, fresh world implementation or
raw source code-observation feature is introduced. These composition obligations
are outside the preparation lane and are not assumed proved by its theorems.

Final artifacts are exported outside the checkout to preserve the original
committed patch and evidence. The external handoff records the full final HEAD,
base, branch, actual checkout, every checkpoint commit, exact commands/exits,
review findings/fixes, elapsed interval, checksums and this remaining gate blocker.
The original work checkout is preserved. No push, merge or PR was performed.
