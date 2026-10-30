# G31 environment and metadata opcode lowering

This preparation component selects real `Solidity.Backend.Instr` instructions.
It does not complete G31's parent source-to-bytecode theorem or the pinned
Osaka EVM correspondence. Source denotation remains the existing intrinsic
`Val.evalT` and `ContractWorld.World.balance`, independent of selection.

## Ownership and frozen inputs

- Branch: `codex/solidity-independent5-20261029/environment-lowering`.
- Exact base: `50658f41061b366d6e503d1e8a3a324a281e9fca`.
- Repository: `/workspace/scratch/environment-lowering-assigned`.
- Preserved original checkout: `/workspace/solidity-lean`, branch `work`,
  head `dedb3aee5743025aeb6d8f7219c9b6b9c1e00e5d`.
- Owned modules: `Solidity/Backend/Environment/`; this document and append-only
  imports/module-map/document registry rows. No other new/unmerged lane is imported; committed reserved interfaces are reused read-only.

### Combined integration repair (2026-10-30)

Review of candidate `455a7e718377a9eaac45dc8e11662cc133521336` found inferred
`have` bindings in seven new modules and an ownership gate that attributed all
intervening integration work to this lane. The bindings in `Observations`,
`Metadata`, `ByteConstants`, `Crypto`, `Namespace`, `Composition` and
`CompositionChecks` now state their proposition types explicitly. Their theorem
statements, proof steps, semantics, observations, target scope and budgets are
unchanged; no axiom or unfinished proof was introduced.

`scripts/check-backend-environment.mjs` keeps dependency availability frozen at
the original exact base above. It separately audits the complete original
contribution through source head
`93e97b28e61f1466eafeb6163baed9da1f9e8240` and the complete requested integration
base `b965d675e260a374401b131e59d501f8ce5da147` through the current working tree.
A different committed review interval can be supplied
with both `--ownership-base <base>` and `--ownership-head <head>`; these options
never change dependency availability. The gate additionally checks the index
and working tree independently against the current HEAD, plus untracked files.
It retains the owned-path allowlist, append-only shared registries, forbidden
import closure and proof/budget checks. Other integrated contributions qualify
only at their exact pinned blobs and modes: scalar at `2a267e4f` and storage at
`8db4c673`, including the latter's backend gap-reference documentation repair.
These pins do not change the frozen dependency base or exempt source, frontend,
trust coverage or the append-only shared registries.

The read-only finder confirmed the annotation-only Lean changes. The skeptic
found that a single HEAD-to-worktree comparison could hide a staged unowned
edit or registry deletion canceled by an unstaged restoration. Independent
HEAD-to-index and HEAD-to-worktree checks now reject both. Final finder and
skeptic reviews reported no remaining findings; neither used Lean or its server.

The earlier annotation repair passed per-file MCP `lean_diagnostic_messages` with
`interactive=false`, `severity=error` on all seven edited Lean files, serially
with one open document and one Lean thread; the default Node gate; and
`node tests/backend-environment/ownership.mjs`. The isolated Git fixtures cover
valid contribution ranges and appends, unowned writes and renames, concealed
staged violations, registry deletion, explicit committed review ranges, frozen
dependency availability, forbidden import closure and proof shortcuts.
`git diff --check` passes, and no inferred `have` bindings or conflict markers
remain in this component. The process group retains its 12 GiB/no-swap cap.
The full combined build and unedited regression-check modules belong to the
coordinator; this repair does not claim those gates were rerun. Changes are
left uncommitted and unstaged for the coordinator.

### Requested integration base (2026-10-30)

The retained review of candidate `16b00b6f` found that it omitted the requested
base's source semantics and trust coverage, changed the ambiguous hex-call
verdict, and audited an older ownership base. Before this repair, the
coordinator's refresh through `f1cad31a` restored the complete `b965d675` source
integration. Read-only Git checks confirm that `b965d675` is now an ancestor and
that `Solidity/Source/`, `Solidity/Frontend/`, `TrustAudit.lean` and
`scripts/g07-axiom-pins.json` are identical to that requested base. In particular,
`hexCall_typed` still refuses the ambiguous call with zero derivations.

This repair restores the two missing README table-header lines and changes the
default ownership and live registry checks to the requested base. The complete
combined contribution is checked; the concurrent storage files are accepted
only when identical to the pinned integration snapshot above. Scalar pin
discovery retains its separate historical base. Dependency availability remains
frozen at `50658f41`. The gate retains independent index and worktree checks.

Focused validation: the default ownership gate and isolated ownership fixtures
pass. The fixtures now advance their integration base with reserved source,
frontend, trust and registry entries, then reject committed deletions of those
files and both live and committed loss of only the advanced registry rows.
They also accept exact integrated storage content and reject changed storage
content or mode. The existing frozen-import, scalar, proof-budget, closure,
unowned-write and concealed staged-violation controls remain in force.
All shared registries have zero deleted lines against `b965d675`.

Separate read-only finder and skeptic passes checked the complete changed-path
set, requested-base source retention, registry deletion counts, documentation
links, pin comparisons and fixture cleanup. The fixture cleanup now removes
only its temporary frontend file, preserving advanced-base frontend content.
No further findings remain from those local passes. An attempted independent
reviewer launch failed with `no rollout found`; independent follow-up remains
with the coordinator. The retained ledger has `validation: null` for this
rejection, so there is no combined-validation log to report as passed.

No Lean files are edited by this requested-base repair, so no Lean diagnostics
or competing build are needed. The coordinator owns the full combined gates;
this focused repair is left uncommitted and unstaged.

The manifest's actual IDs are `msgSender`, `msgValue`, `thisAddress`,
`addressBalance`, `blockTimestamp`, `keccakBuiltin` (not keccak256Builtin),
`erc7201Builtin`, `functionSelector`, `functionAddress`, `errorEventSelector`,
`interfaceId`, `typeName`, `typeBounds`, `creationCode`, and `runtimeCode`. Decisions are those in
[solidity-scope.md](../solidity-scope.md), including G00 Q2, sender funding,
own balance from the ledger, forced credits and fixed cryptographic functions;
[decision impact](roadmap-decisions-impact.md) distinguishes narrower existing
runs from the eventual history-dependent source world. No excluded field,
code/log observation, new premise, verdict or target predicate is introduced.

## Baseline gap

`Evm/Compile.lean` rejects `Val.hash` in its core fragment and emits `[]` for it;
`Evm/Machine.lean` has symbolic crypto/storage operations and simplified
transaction inputs. `Backend/Opcode.lean` has the actual Osaka bytes but no
intrinsic environment adapter at the frozen base. The saved reproduction is
`/workspace/scratch/environment-lowering-evidence/gap.txt`.
Nontrivial control: BALANCE of `2^160+7` reads account 7; SELFBALANCE ignores
an existing stack word and reads self's ledger entry. Treating them alike
changes stack height and, on the inhabited sample, returns 73 instead of 41.

## Checkpoint 1: environment observations

Implemented in `Observations` and `ObservationsChecks`, namespace
`Solidity.Backend.Environment`.

| Existing constructor / anchor | Selection | Interpretation |
|---|---|---|
| `EnvKey.msgSender`, `Syntax/Raw.lean:38` | CALLER, 0x33 | bounded frame sender, zero extended |
| `EnvKey.msgValue`, `Syntax/Raw.lean:39` | CALLVALUE, 0x34 | exact uint256 payment |
| `EnvKey.timestamp`, `Syntax/Raw.lean:40` | TIMESTAMP, 0x42 | arbitrary uint256 timestamp |
| `EnvKey.selfBalance`, `Syntax/Raw.lean:41` | SELFBALANCE, 0x47 | ledger at self |
| `EnvKey.selfAddress`, `Syntax/Raw.lean:42` | ADDRESS, 0x30 | bounded deployment identity, zero extended |
| `ContractWorld.World.balance`, `Semantics/ContractWorld.lean:72` | BALANCE, 0x31 | pop word, truncate low 160 bits, read arbitrary ledger |

Headline results: `account_value`, `account_address`, `select_correct`,
`balance_correct`, `balance_address`, `own_balance`, `world_balance`,
`intrinsic_correct`. `Represents` requires exactly matching frame identity,
sender, value, time and own ledger balance. It quantifies over arbitrary typed
source states, including arbitrary storage, heap, locals, net deltas and
external-response tables. `world_balance` quantifies over arbitrary catalogs,
roles and funds under exact ledger agreement. It is an observation adapter,
not world execution composition. The older intrinsic state does not enforce
160-bit sender/self bounds or own-ledger agreement, so these boundaries are
explicit; invalid transactions and deployment provenance remain parent duties.

The local meaning has no gas/fuel, stack-capacity or exception accounting.
Real EVM use needs sufficient gas/fuel and stack room below 1024. Stack tails
are universally preserved. Wrong-address truncation, confusing own balance
with BALANCE, wrong CALLER/ADDRESS selection, and underflow have inhabited
controls. Excluded CHAINID/NUMBER/ORIGIN/EXTCODEHASH/LOG are refused locally;
this is not an importer admission theorem.

`represented_ok` inhabits the boundary for every existing state and frame,
retaining its oracle and net ledger. `sample_observations` uses distinct
nonzero identities, value, time and balances. `inhabited_certificate` instantiates
the intrinsic certificate on an actual typed initial state.

Axiom pins: `select_correct` and `account_address` use only
`[propext, Quot.sound]`; `intrinsic_correct` uses
`[propext, Classical.choice, Quot.sound]`. No new axiom or proof shortcut.

Finder and skeptic independently reviewed read-only without a Lean server.
Both requested an explicit `World.balance` connection. Skeptic also requested
resource boundaries and an executed high-address balance control. All three
were added; finder verified resolution. Saved review evidence accompanies the
handoff. No slower refactor was performed; earlier speed commits were inspected
and existing hot source definitions were reused without changes.

## Queue accounting

| Item | Status |
|---|---|
| 1 environment instruction slices | Proved and controlled; checkpoint gates below |
| 2 metadata | Locally complete; final full/import gates pending |
| 3 intrinsic cryptographic builtin lowering | Locally complete at the assigned slice/CALL boundary |
| 4 composition certificate and mixed observations | Locally complete; final full/import gates pending |
| A erased emits / sequence fallback | Authorized typed-sequence fallback proved; frontend emit-hoisting remains parent duty |
| B frame/stability and all observation/refusal regressions | Locally complete with explicit stability/footprint assumptions |

## Runtime and validation evidence

Lean 4.24.0 (797c613eb9b6d4ec95db23e3e00af9ac6657f24b), Lake
5.0.0-src+797c613; these match `lean-toolchain`. No Lean MCP connector is exposed,
so focused kernel builds provide per-file diagnostics. Builds use the observed
absolute toolchain, `LEAN_NUM_THREADS=1`, explicit Lean `-j1` in the untracked
alternate TOML, and serial topological prerequisites. A private disk artifact
cache reuses source/toolchain keyed entries. No LSP runs concurrently.

Systemd user and system scopes are unavailable (no user bus, PID 1 is not
systemd). A Docker cgroup is verified at **12884901888 bytes memory, zero swap**;
this is an aggregate cap for Lake and all children, not an RLIMIT per process.
The outer VM has a 16 GiB cgroup and no host swap. The remaining VM memory is
OS headroom, without an additional coordinator-host reserve inside this VM.
The repository writer lock is held for writes/checks.

Evidence directory: `/workspace/scratch/environment-lowering-evidence`.
The first KeySort attempt failed because the container's default cache path
was unwritable. Retained as failed. The corrected task-private cache run:
`lake -f lakefile.environment.toml build Solidity.KeySort` printed
`Build completed successfully (2 jobs).`, exit 0. This establishes the runtime
gate only. `checkpoint1-deps.log`: serial 29-target closure, exit 0, 100 seconds,
cgroup peak 1360814080 bytes. `checkpoint1-controls3.log`: focused module/control
build, exit 0, 2 seconds, cgroup peak 184881152 bytes. Cgroup memory includes
page cache; it is not an RSS measurement. Early failed proof iterations are
retained and are not passing gates. Final full/import closure and same-base
failure comparison remain required. No full-group completion is claimed.

Checkpoint-1 gate closure: both touched files have clean JSON diagnostics
(`cp1-diagnostics2.log`, exit 0, 2 seconds, sampled peak aggregate RSS
717612 KiB). Direct checking needs Lake's `--setup` mapping for cached imports;
the earlier mapping-free attempt failed and remains recorded. Layer check:
168 core modules, zero reach the elaborator. Orphan check: 768 reachable,
zero orphaned. Trust check: 783 sources, 241 inventoried sites, zero findings.
Documentation-path check fails with exactly the same 46 missing references
at the frozen base (`base-doc-paths2.log`) and this checkpoint
(`cp1-doc-paths.log`); no new finding. This inherited failure is not marked
passed. Both independent reviewers confirmed all findings resolved. Checkpoint
1 is complete locally; final full/import-closure validation remains open.

## Checkpoint 2: metadata constants

`Metadata` reuses `Backend.Assembler.toBytesBE` and its roundtrip theorem.
`constant_correct` proves actual PUSH immediate decoding, exact word value,
zero extension and stack-tail preservation for every width 0–32. `truncate_correct`
states the explicit low-byte modulus; `zero_extension` proves widening keeps
values. `selector_correct` preserves the source's low numeric four-byte value;
`selector_alignment` and `selector_abi_bytes` give the separate ABI-left-aligned
value and exact big-endian immediate. `address_correct`, `function_correct` and
`function_projections` preserve bounded receivers and the existing
`address*2^32+selector` representation.

`metadataSelector` reads `SourceFunction.callable`'s existing canonical
`SourceCallable.abi`/`getter` selector. `declaration_correct` lifts any resolved
selector to code; `selector_intrinsic` connects it to existing `Val.evalT` literal
denotation. Missing ABI metadata, constructors and other non-ABI roles are
refused. No canonical signature is reconstructed from a generated model name.

The bounded `metadataBytes` adapter covers the existing four-byte interface/error
selectors and 32-byte event digests supplied by the importer. Their resolution
and interface XOR computation stay in `Frontend/SolcJson/Body.lean:1060–1095`;
this module does not replace or certify that frontend. `typeName` is also
accounted for: the core `Contract` does not retain its name, so the existing
importer resolves the String first. `nameCode` then materializes the standard
UTF-8 encoder's structural byte-array contents (`toUTF8.data.toList`) through
actual PUSH1/PUSH32/MSTORE8. `materialize_correct`, `writeBytes_at`,
`read_written` and `writeBytes_frame` prove exact bytes/order, stack preservation,
and unchanged memory outside a precisely bounded, nonwrapping interval.
Full string-object layout and allocator integration remain parent obligations.
This is a component-local target slice, not a duplicate source or memory IR.

Both independent reviewers found missing byte-name coverage and requested explicit
declaration/function adapters. Those were implemented and both reviewers verified
resolution without Lean/server/build use. The concrete UTF-8 witness includes
`Aλ`, both neighboring memory bytes and a nonempty stack. Exact byte regressions
cover PUSH4 numeric/ABI selector alignment, PUSH20 address, PUSH24 packing,
PUSH0/truncation, four-/32-byte metadata and PUSH/MSTORE8. Wrong selector alignment
has an inhabited counterexample. `MetadataChecks` pins headline axiom sets to
only propext/Classical.choice/Quot.sound (or the appropriate subset).

`cp2-controls4.log`: focused build passes (36 jobs), exit 0, 2 seconds, sampled
aggregate RSS 784232 KiB, cgroup peak 239304704 bytes. Earlier failed iterations
are retained; none is counted green. No proof/resource budget was raised.

Checkpoint-2 closure: `cp2-diagnostics.log` is clean on all three new Lean
files, exit 0, 4 seconds, sampled aggregate RSS 770068 KiB. Layer/orphan/trust
gates pass: 168 core modules with zero elaborator reach, 771 reachable modules
with zero orphans, 786 source files and zero trust findings. The global layer
checker enumerates core names explicitly; the new modules' import closure is
also reviewed and will receive the task-specific closure check in final gates.
`cp2-doc-paths.log` retains exactly the same 46 inherited path findings as the
exact base, zero new findings. Both independent reviews are closed. Checkpoint
2 is locally complete; full/import closure remains pending.

## Checkpoint 3: intrinsic cryptographic builtins

`Crypto` reuses `Solidity.Storage.keccak256_bytes`/`Solidity.Storage.ofBytes_lt` read-only
for `keccak_bound`. `source_digest` proves the existing intrinsic `keccakBytes`
agrees with the real computed digest on the exact normalized bytes. It adds no
hash axiom or injectivity premise. `digest_fixed` agrees with G06's concrete
`Roadmap.Evm.keccakWord`. `wireBytes_values` preserves the actual intrinsic
`b.toNat % 256` convention, including values above 255 and negative integers.

`keccakCode` emits PUSH32 length, PUSH32 offset, KECCAK256. `cryptoStep` states
its target memory/stack meaning independently of selection. `keccak_correct`
proves exact preimage/result and arbitrary stack-tail preservation.
`HashInput` requires exact represented bytes and a nonwrapping interval.
`intrinsic_keccak` connects the existing `Val.hash`/`MPath.mvalT`/`Heap.hash`
denotation to execution for arbitrary typed state, heap, ledger and external
response table. `lowerHash_success`, `lowerHash_failure` and
`intrinsic_hash_failure` preserve the one path evaluation and its precise halt.
No source semantics depends on compilation. The surrounding memory compiler
must establish source-object layout/allocation and the HashInput boundary.

`namespace_source` (module `Namespace`) proves the existing `ERC7201.root` on any represented
byte string. It emits two actual KECCAK256 instructions, SUB with wrapping,
MSTORE of exactly `Semantics.wordBytes` of the predecessor, and SHR/SHL by 8
to clear the low byte. `namespace_preimage`, `root_value`, `namespace_result`
and `namespace_suffix_correct` expose the intermediate bytes and result.
`NamespaceInput` requires the input and caller-owned 32-byte scratch intervals
to fit. Scratch can overlap the consumed input because its write follows the
first hash. Other live source regions must be framed by the caller. No physical
storage namespace disjointness or collision claim is made.

For SHA256/RIPEMD160/ECRECOVER, `precompileResult` reuses the existing committed
`Precompiles.Basic` computations. `precompileAddress`, `precompilePrefix`,
`precompile_operands`, `precompile_preimage` and `precompileCode` select real
STATICCALL code with exact input bytes and operands. GAS is forwarding machinery,
not an admitted source observation. The suffix POP/PUSH32 output/MLOAD extracts
the word. Output memory must fit, be caller-owned and be zero initialized for
ECRECOVER's empty result. The CALL/precompile execution/result-copy/gas/failure
composition remains explicitly open, as assigned; no symbolic instruction is
counted as executable lowering. Invalid intrinsic ECRECOVER lengths return zero
(`ecrecover_wrong_length`), so `builtinCode` preserves that case with PUSH0 after
argument evaluation instead of invoking the precompile's zero-padding semantics.
The valid 128-byte case has its own inhabited intrinsic heap/path control.

`CryptoChecks` includes a typed four-byte heap/path, a preserved nonempty stack,
normalized bytes, unset-argument failure, wrong operand/preimage order, namespace
execution, exact Keccak and precompile suffix bytes, and ecrecover128/fallback
controls. Headline axioms are pinned to propext/Classical.choice/Quot.sound only.

The first namespace proof hit kernel deep recursion while expanding a large
formula; it stayed failed. The final proof uses separate bounded-word/digest
lemmas, without raising maxRecDepth, maxHeartbeats or resource budgets.
`cp3-controls5.log` passes: 45 jobs, exit 0, 2 seconds, sampled aggregate RSS
781660 KiB, cgroup peak 229056512 bytes. Finder found missing positive 128-byte
ECRECOVER branch coverage; `recovery_positive` and `precompile_suffix_bytes`
were added, and finder verified resolution read-only without Lean/server/build.

`tests/backend-environment/Emit.lean` exports the actual Backend.encode outputs;
`vectors.mjs` runs them in pinned EthereumJS EVM 10.1.3, Osaka. The 12 programs
cover all five environment reads, arbitrary-address BALANCE with high bits,
numeric/ABI selectors, Keccak, ERC-7201, SHA256/RIPEMD160, invalid and valid
nonzero ECRECOVER, malformed-length fallback, and UTF-8 name materialization.
All pass (`cp3-evm-vectors2.log`, exit 0, 1 second, sampled RSS 728380 KiB).
These are external tests, not general pinned-EVM proofs or whole-pipeline proofs.
The runtime image installs only standard checking tools; Lean/Node toolchains
and the preserved original Git metadata are mounted read-only for checks.

Skeptic found that the external harness could silently accept omitted/duplicate
vector names. It now asserts exact equality with the expected program-name set;
this is fixed before checkpoint closure. `lowerHash` is explicitly an evaluated-
argument, state-indexed adapter, not a state-independent whole compiler. The
surrounding compiler must integrate hoisted argument effects, allocation and
runtime parameter placement. Those parent obligations are not claimed here.

Checkpoint-3 closure: all three per-file JSON diagnostics are clean
(`cp3-diagnostics.log`, exit 0, 6 seconds, sampled aggregate RSS 768168 KiB).
Layer/orphan/trust gates pass: 168 core modules/zero elaborator reach,
774 reachable/zero orphaned, 789 sources/zero trust findings. Documentation-path
check has exactly the same 46 inherited failures as the base, zero new findings.
The corrected exact-name harness passes all 12 programs (`cp3-evm-vectors3.log`).
Both independent read-only reviewers verified their findings resolved, without
Lean/server/build. Checkpoint 3 is locally complete; final import/full gates and
checkpoint 4/backfill remain pending.

## Checkpoint 4 and backfill A/B

`sliceStep` (module `Composition`) independently combines the three target instruction
slices; `runSlice_append` proves actual code concatenation. Support predicates
prove the data and crypto slice embeddings; byte materialization and hashing
therefore compose in one actual instruction stream. `ValueCertificate` and
`ValuesCertificate` read the existing intrinsic `Val C Γ .uint`, never a new
source IR. `environmentCertificate`, `literalCertificate`, `hashCertificate`,
`nilCertificate` and `consCertificate` construct certificates from kernel proofs.
`evalValues` is independently defined from existing `Val.evalT` in source order;
target results appear in reverse order on the stack, with arbitrary tails.
`mixed_observation_control` inhabits sender/metadata/Keccak composition over an
actual typed heap/path. `materialize_then_hash` universally composes byte
materialization with hashing over arbitrary memory and stack tails.

Backfill A uses the explicitly assigned fallback. The frozen typed `Stmt` has
no emit constructor or general expression-effect interface; raw `RawStmt.eval`
(`Syntax/Raw.lean:192–198`) represents erased arguments, and
`Syntax/Elab/Arms.lean:1244–1247` hoists them with `eagerArgsWith` before dropping
the residual `.eval []`. Proving that frontend transformation would edit or
reach reserved source/elaborator work. `source_sequence_success` and
`source_sequence_failure` instead prove independent composition through existing
typed `TStep`, `Out` and `TRun.seq`, including exact halts. `source_effect_control`
inhabits retained assignment/read effects (1 then +2 gives 3), and
`source_order_control`/`source_order_distinguishes` show panic/revert order changes
an actual typed run. No log observation is added; the emit-hoisting certificate
and general effect/allocator integration remain parent obligations.

Backfill B is implemented in `Frames`. `Stable` explicitly requires matching
frame identities, sender/value/time and ledger, and `Stable.observe`,
`stable_selection`, `repeated_read` and `repeated_across_stable` prove repeated
reads only under those assumptions. `balance_frame` and `repeated_balance`
need only agreement at the truncated read account, explicitly reinserting the
BALANCE operand. `ledger_other` proves ledger changes outside that footprint
are irrelevant. `overwriteFunds` is a generic mathematical overwrite, not a
claim that arbitrary decreases are legal forced credits. The inhabited
`forced_credit_counterexample` uses an actual increase from 41 to 42; the time
counterexample changes 13 to 14. Neither is assumed stable across world frames.
`source_environment_frame` allows arbitrary contract/context/heap/storage/net
changes under transaction and own-balance equality; `response_table_frame`
allows an arbitrary replacement of the existing response table. No source-world
or read-only-call theorem is edited or strengthened implicitly.

`refuse_non_environment` is exhaustive over the six-opcode environment relation;
`slice_refuses_unsupported` is exhaustive over the composed target slice.
`excluded_constructor_controls` preserves every excluded BlockField and raw
msg/tx field in the committed parser, with admitted positive controls.
`slice_refusal_controls` includes BLOBHASH, GAS, raw returndata/code/log fields,
and resource observations. Each admitted environment opcode's exact bytes are
pinned in checkpoint 1; metadata/byte/hash/precompile instructions have the
checkpoint 2/3 encoded-byte regressions and actual emitted EVM vectors.

Finder requested repeated BALANCE and exhaustive composed refusals; skeptic
requested explicit BLOBHASH/GAS refusals. Both changes were made. The final
component still has no CALL/precompile/world/gas composition theorem and claims
no whole G31 or whole-source-to-bytecode preservation. These exclusions are
assigned integration boundaries, not newly approved premises.

Checkpoint-4/backfill closure: `cp4-controls3.log` focused build passes (48 jobs),
exit 0, 3 seconds, aggregate RSS 761708 KiB, cgroup peak 199032832 bytes.
`cp4-diagnostics.log` is clean on all three new files, exit 0, 5 seconds,
aggregate RSS 760444 KiB. Task-owned closure gate passes for all 11 modules,
including no frontend/external/new-lane dependencies and append-only registries.
Global layer/orphan/trust gates pass: 168 core/zero elaborator reach,
777 reachable/zero orphaned, 792 sources/zero trust findings. The documentation
check retains exactly the same 46 base findings, none new. Both independent
finder and skeptic verified all final-milestone findings resolved read-only,
without Lean/server/build. No assigned component/backfill proof remains open;
required final full/import validation is still pending and no goal completion
is claimed. RUNTIME_GATE_PASS applies only to the previously recorded actual
versions and passing KeySort output, not to these pending full gates.

Final holistic review clarified the exact metadata-ID accounting: `typeBounds`
uses `typedConstant`/`typed_constant_correct`/`typed_literal_intrinsic`, preserving
existing `PrimTy.Denote` and `PrimTy.toWord` including signed two's complement.
The signed negative control encodes -1 as 32 ff bytes and distinguishes it from
an incorrect zero/Nat truncation. `creationCode`/`runtimeCode` use the same
`materialize_correct` payload adapter as other byte constants only after the
existing whole-input Artifact/importer has supplied validated compiler bytes.
This lane does not certify artifact provenance, admit deployed raw code reads,
or change the source's compiler/source/settings validation boundary. The exact
manifest IDs `interfaceId` and `typeName` are now explicit in the opening list.


## Final validation and handoff

All four numbered checkpoints and backfill A/B are implemented and reviewed.
The authorized backfill-A fallback is the typed sequence/control certificate
above; a frontend emit-hoisting theorem remains an explicitly separate parent
integration obligation. Full source/world/EVM/precompile composition is not
claimed. Final finder and skeptic independently found no new source defect;
their requested actual-output axiom pin is now guarded and kernel checked.

Final serial closure checked all 780 module targets, including all Derived
modules and `Solidity`, then all six native dependency targets (the last after
a runtime-wrapper repair). The initial closure command took 2:40:36 and ended
nonzero at native compilation because the wrapper bypassed bundled compiler
headers. Subsequent linker attempts exposed missing bundled library/unwind
flags. These are retained setup failures, not inherited Lean failures or
waivers. The corrected serial wrapper invokes the distribution's `leanc` with
`LEAN_CC` removed for that child, preserving its built-in flags. No repository
compiler/proof option, toolchain version, budget or expected output changed.

Actual final command `./run-lean.sh` passes (`final-run-lean3.log`):
`Build completed successfully (762 jobs).`,
`Build completed successfully (262 jobs).`,
`solkeycheck: parsed 377 taclets, 131 read-bearing, table covers 131`, and
`solkeycheck: OK — annotations match` the mounted exact frozen rule fixture.
Exit 0, warm elapsed 1.63 seconds, aggregate RSS 711048 KiB. No historical
SolKey mismatch or Derived17 OOM was waived: both actual gates passed.

The first full serial closure's measured aggregate RSS peak is 11275852 KiB; cgroup
peak 12884901888 bytes equals the fixed 12 GiB cap. Derived17 passed in about
148 seconds. Saved memory events report `oom 0`, `oom_kill 0`,
`oom_group_kill 0`; cap reclaim occurred. Swap remained zero. The original
output handle and a later executor restart were recovered by attaching to the
same running container, with complete intermediate log snapshots preserved.
No duplicate full closure was started during recovery; there was no concurrent
Lean worker or process termination.

`final-focused.log` checks all eleven files with per-file Lean JSON diagnostics
using each actual Lake setup mapping, then executes the actual `Backend.encode`
fixture in pinned EthereumJS EVM 10.1.3, Osaka. All diagnostics are clean and
all 13 exact-name programs pass, including the signed-bound addition. Exit 0,
18 seconds, aggregate RSS 795532 KiB. Kernel results and external EVM tests
remain distinct evidence; the latter do not prove a whole EVM correspondence.

The final handoff, original committed diff, gate scripts/logs and checksum
manifest are saved under `/workspace/scratch/environment-lowering-evidence`.
That handoff records the final full committed head and measured recovery-work
elapsed time, avoiding a self-referential commit hash in this document. The
preserved original worktree is not integrated or modified. No push, merge or
PR is performed. Final source/ownership/layer/orphan/trust/doc-delta gates are
recorded in the accompanying `final-static` evidence, with the raw inherited
documentation-path failure kept distinct from its zero-new-findings gate.

Final static results: task-owned gate passes for 11 modules; global layers
report 168 core modules and zero elaborator reach; orphans report 777 reachable,
zero orphaned/not allowed; trust reports 792 sources, 241 inventoried sites,
zero findings. Raw doc paths exit 1 for the same 46 missing-file references
plus 24 ambiguous-name diagnostics as the exact base, with zero new findings.
The first comparison mistakenly asserted 46 total diagnostic lines; comparing
the complete 70-line diagnostic sets resolves that bookkeeping error. Relative
links in this owning document resolve. Final handoff finder/skeptic confirmed
actual gate outputs, axiom pin and component boundaries; their wording findings
were fixed (cached serial closure is not called cold, and recovery is distinct
from the documented setup retries). No review used Lean/server/build.

## Integration ownership repair (2026-10-30)

Retained review P2 on candidate `22580806957a553479e473f1e07cf7a2137781f3`
found that the normal ownership gate audited only the frozen original lane.
Committed integration repairs escaped that interval, including deletions in
the shared documentation registries relative to integration base `8445c3fc`.
The gate now defaults to that integration base through the current worktree,
while preserving the original lane audit and frozen dependency availability
at `50658f41`. Existing scalar contribution files are exempted only when they
match the pinned scalar head `2a267e4f`; other unowned writes still fail.
Index and worktree checks remain separate so an unstaged restoration cannot
hide a staged violation. Explicit ownership-range options remain available.

The registries retain their complete integration-base contents and append the
new lane entries. Base-to-worktree numstat reports 5 additions/0 deletions for
`docs/README.md` and 56 additions/0 deletions for `docs/module-map.md`.
The existing Creation entries and blank lines keep their original positions.

Focused verification passes: `node scripts/check-backend-environment.mjs`
reports all 11 owned modules passing, and
`node tests/backend-environment/ownership.mjs` passes. The latter exercises
normal invocation against clean committed unowned edits and deletions in all
three shared registries, accepts committed appends, and rejects changes to a
pinned scalar file. It retains staged/unstaged, rename, frozen-import, closure
and proof-budget controls. Clean-status assertions prevent live edits from
accidentally providing the coverage intended for committed candidates.
Sandbox attempts stopped at Node/Git `EPERM`; the actual checks above passed
outside the sandbox. No Lean file, theorem, observation or budget changed;
the coordinator retains ownership of full combined validation.

Read-only finder review confirmed the base registry contents are preserved;
skeptic review found the committed fixtures retained an untracked allowed
file. That file is now removed before those cases, and explicit clean-status
assertions pass. Both review passes were performed by the repair worker:
attempts to start independent reviewers failed with a thread-store
`no rollout found` error. No review used Lean, the server or a build.
