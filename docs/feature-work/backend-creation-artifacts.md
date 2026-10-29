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

## Remaining queue

1. Artifact layout: implemented; focused target and controls pass; two reviews complete.
   Final global gates remain lane-wide obligations.
2. Independent slice execution and installed-runtime theorem: implemented,
   kernel checks/controls and independent finder/skeptic follow-ups pass.
3. Certified assembler linking, disjointness, exact widths and refusal: implemented;
   focused target and independent review follow-ups pass.
4. Typed immutable patches and frame/installation proofs: pending.
A. Constructor-prefix return/revert composition: pending.
B. Determinism, commutation, encoding/provenance and external vectors: pending.

All final focused/import/full/TestSuite/static/trust/document gates and inherited
failure comparisons remain pending. No completion claim is made for the lane.

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
