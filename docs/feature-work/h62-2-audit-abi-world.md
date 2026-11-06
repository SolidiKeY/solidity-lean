# H62 item 2: ABI-world empty-statement audit

Owner: `solidity-h62-2-20261106/audit-abi-world`. Frozen base:
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. Assigned branch:
`codex/solidity-h62-2-20261106/audit-abi-world`.
Repository: `/workspace/solidity-lean`.

## Current status

The assignment is unfinished. Inventory, simultaneous witnesses and the independent
statement-fidelity census now cover all 177 frozen declarations across all 24
mapped modules. There are zero uncovered mapped statements. Of these, 54 have
proposition premises, 53 have data/type/instance binders only, and 70 have no input
binders. The 70 empty packages are explicit census accounting, not additional
semantic feasibility coverage. The remaining phase
is meaningful supported-program success/totality contracts, reject-all and
always-revert controls, observable failure/gas/fork boundaries, after timings,
and full final validation/review. Witness completion does not complete that phase.

| Checkpoint | Result |
|---|---|
| 1. Frozen signatures, ownership, premise classification | Complete source inventory; elaborated binders now also exported. |
| 2. Simultaneous hypotheses | 177 exact-type packages pass complete Lean diagnostics and reviews. |
| 3. Success/totality and behavioral controls | Pending. Reference interpreter provisioned; no gas/fork result claimed. |
| 4. Witness and statement-fidelity census | 177 independent type comparisons pass; 439 binders, 113 proposition binders. Full final gate rerun remains required after checkpoint 3. |

The accounting tool explicitly reports `witness_gate_complete=true` and
`assignment_complete=false`. All original Solidity sources, generated roots,
central maps, axiom pins, producer interfaces and the frozen root Lake config are
unchanged. No theorem statement, premise, exclusion or observation was weakened.
There are no new axioms, unproved proof placeholders, native_decide shortcuts or
heartbeat increases. No mapped statement required a frozen repair or owner ticket.

## Inventory and ownership

`census.py` regenerates the exact frozen map and signatures from Git, including
section context, source/signature hashes and provenance. It includes unconditional
statements so a hypothesis heuristic cannot silently omit an interface. It is a
reviewed scanner for this frozen grammar, not a general Lean parser. `coverage.py`
requires exact equality with canonical regeneration of all 24 modules/177 rows.

The verified ownership snapshot identifies
`H30-WRITER-solidity-v12-v17-20261031--v13-abi-world`, owner
`solidity-v12-v17-20261031/v13-abi-world`, status `coordination-only`, covering
`Solidity/Backend/AbiWorld/**`. Snapshot SHA256:
`7f5d40d46d386ed17731db55ed87f0564f5c9e667bddee00c0f12b28772f9cce`.
Git authorship is recorded separately and is not ownership authority. No original
owned file was edited; the audit's exclusive additive scope was sufficient.

Four directory files are absent from the frozen map: `MutatingByteLoad.lean`,
`MutatingByteLoadControls.lean`, `TypedPacketMaterialize.lean`, and
`TypedPacketMaterializeControls.lean`, under `Solidity/Backend/AbiWorld/`.
The census reports this map drift explicitly. These files are not counted among
the 177 or declared audited. Their Producer premises are not attributed to the
mapped statements.

## Global premises versus fixed-input feasibility

Independent finder and skeptic traces found no direct global Producer,
Admission or compiler-correctness oracle premise among the mapped signatures.
Seven statements assume fixed-input representation structures:

| Frozen suffix under `Solidity.Backend.AbiWorld` | Structures |
|---|---|
| `CallerWordBytes.recovered` | WordFrame |
| `CallerWordBytes.typed` | StateRepr, WordFrame |
| `NativeParentWord.represented_counter` | StateRepr |
| `NativeParentWord.native_parent` | InterfaceV1.Entry |
| `MutatingEntryWords.represented_element` | StateRepr |
| `MutatingEntryWords.observed_activation` | StateRepr, StructAllocatorRepr |
| `MutatingWritePhysical.write_prefix` | StateRepr, WordFrame |

Definition evidence: `RuntimeFrameInterfaceV1.lean:28`,
`Evm/MemorySource.lean:26`, `PhysicalWordFrame.lean:23`,
`Evm/MemoryStructAlloc.lean:16`. StateRepr's nested payment-oracle compatibility
(`Evm/Sim.lean:225`) quantifies address/amount pairs for the same supplied
transaction and machine. It is jointly witnessed, not replaced by an isolated
inhabitant. CheckedAddArtifact's universal fit condition concerns references in
one artifact. Widths is bounded metadata (`L → Fin 33`); tag_bound also needs its
DecidableEq instance. Fits is three independent local inequalities. The remaining
170 signatures have data/type/instance inputs, local feasibility, or no binders.

## Additive proof modules

| Audit module under `H62AbiWorld` | Mapped witness count |
|---|---|
| CodecWitnesses | 19: ErrorLayout and ErrorRoundtrip. |
| WindowWitnesses | 27: Error/Panic windows, heterogeneous results and return words. |
| ControlWitnesses | 93: every mapped control declaration; 70 have no input binders. |
| BasicWitnesses | 29: packet prefixes, layout/assembly and remaining plain data cases. |
| RepresentationWitnesses | 9: actual call/frame/heap/byte fixtures, including all seven representation statements. |

WitnessSchema reads each unchanged theorem's elaborated type. It existentially
packages every leading forall binder in dependency order, including unused proof
binders, and replaces only the conclusion with True. The original theorem's proof
and conclusion do not establish feasibility. This checks one simultaneous input
for each statement, not total compiler success over all programs.

The schema has two public controls and two private fixture theorems: a feasible
shared input and rejection of incompatible premises on one input. There are 181
new theorem declarations in total: 177 mapped witnesses plus those four schema
fixtures/controls. Of the 177 witnesses, 157 report no axioms; the remaining 20 use
only combinations of propext, Classical.choice and Quot.sound. No new axiom was
introduced. The generic assembler packages choose concrete labels/items and
library type Empty without assuming an impossible Empty value.

Fidelity uses a separate direct recursion over Expr.forallE, rather than reusing
the schema's forallTelescope function. It preserves dependent domains, fails closed
on exhausted traversal fuel and checks definitional equality against the actual
witness type. Its 177 records export complete original and witness types and all
439 binders, including 113 proposition binders. Every original/witness pair occurs
exactly once. Definition unfolding inside arbitrary conclusions is deliberately
outside both leading-spine checks; the frozen statements were reviewed for this
boundary. No required premise is hidden or discarded in these 177 statements.

## Gates and reproducibility

Run from the repository root:

```sh
python3 -B scripts/h62/item2/audit-abi-world/test_census.py
python3 scripts/h62/item2/audit-abi-world/census.py --output /workspace/audit-abi-world-evidence/census.json
python3 -B scripts/h62/item2/audit-abi-world/coverage.py --evidence /workspace/audit-abi-world-evidence --require-complete
python3 -B scripts/h62/item2/audit-abi-world/test_coverage.py --evidence /workspace/audit-abi-world-evidence
python3 -B scripts/h62/item2/audit-abi-world/test_bounded.py --evidence /workspace/audit-abi-world-evidence
```

All pass at this milestone. Four scanner tests pass. Seven accounting rejection
controls reject shrunk census, stale schema, unapproved axiom report, wrong tool,
fidelity mismatch, stale guard and unbound proof output. Five lifecycle controls
exercise normal completion, orphan cleanup, timeout, cancellation and parallel
fake compiler rejection; they use no Lean. Deterministic regeneration of the
control/basic/fidelity modules and isolated TOML reproduces identical hashes.

Each of the six proof modules and Fidelity passes complete per-file MCP diagnostics:
success=true, partial=false, timed_out=false, no failed dependencies or errors.
The guard owns proof stdout and records its path/SHA256 after verified cleanup.
Accounting checks that exact proof/resource pair, file/source/support hashes,
expected Lean build, tool identity and full-file noninteractive arguments. Fidelity
also binds every local audit Lean source before and after checking. Only the three
standard axioms above are permitted by the accounting gate.

For a per-file check, substitute the module and evidence names:

```sh
python3 -B scripts/h62/item2/audit-abi-world/bounded.py --receipt /workspace/audit-abi-world-evidence/CodecWitnesses-resource.json --output /workspace/audit-abi-world-evidence/CodecWitnesses.json --timeout 180 -- .venv/bin/python -B scripts/h62/item2/audit-abi-world/mcp_call.py lean_diagnostic_messages '{"file_path":"tests/h62/item2/audit-abi-world/H62AbiWorld/CodecWitnesses.lean","interactive":false,"timeout_s":120}'
```

For Fidelity, use fidelity_call.py as the guarded command; it binds all local
Lean dependencies. Regeneration scripts and exact commands are in the handoff.
Adding/changing audit Lean sources requires refreshing Fidelity's dependency-bound
receipt before the coverage gate can pass again.

## Runtime and measurement boundaries

Actual Lean: 4.24.0, x86_64 Linux, Release, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`. Lake:
5.0.0-src+797c613. The official preinstalled binaries are under
`/workspace/.setup/tools/lean-4.24.0-linux/bin/`. Current bounded KeySort diagnostics
pass. The verified coordinator 4.35.0 archive pin remains in coordinator inputs;
the latest instruction scopes that requirement to migration lanes. This additive
audit does not migrate the frozen base or use a v4.24 per-master remote cache.

prepare_config.py reproduces the frozen target configuration in the audit's
isolated TOML, adding explicit --tstack=131072/-j1 to every library/executable and
only the audit test library. Original defaults/dependencies/target settings are
preserved. No central registration or generated-root edit was made.

The launcher holds the writer lock, rereads tracked changes, uses one open MCP
file and LEAN_NUM_THREADS=1, and enforces timeout/no active swap. Linux subreaping,
retained PID/start-time identity and pidfd signaling keep cleanup within the task's
own descendants. Catchable cancellation is recorded rather than raised during
spawn; finally cleanup handles survivors before accepting success.

Per-process RLIMIT_AS is 12 GiB; the VM cgroup hard limit is 16 GiB. Aggregate task
RSS ≤12 GiB and available memory ≥4 GiB are sampled every 0.2 seconds; those are
sampling checks, not an additional hard cgroup. The seven current checks observed
maximum task RSS 1501900800 bytes, minimum available memory 15264714752 bytes,
maximum one heavy Lean job, no active swap, and complete cleanup. No systemd-run
was called. An initial dependency check in the first checkpoint omitted explicit
-j1 and was excluded from accepted resource gates; current checks were rerun after
fixes. Occasional MCP event-loop shutdown warnings do not replace structured
results, command exits or source/output hashes.

The current before baseline is seven warm CodecWitnesses samples after a discarded
warmup: median 1.219290965 seconds. Source/config/toolchain/guard/resource identities
are captured. measure.py after must retain them and exits 2 above 10% slowdown.
No after measurement or slowdown result is claimed yet. Earlier baselines preceding
necessary guard/config fixes are explicitly archived as superseded; none had an
after comparison. Full ./run-lean.sh and final acceptance are still pending.

## Reviews and handoff

Read-only census_finder and census_skeptic used neither Lean server nor builds.
Both accepted the exact 177 mappings, complete dependent packages, independent
fidelity traversal, final isolated configuration and seven proof/resource pairs.
They found and had fixed result-let signature truncation, owner attribution,
fail-open diagnostics, canonical-census/helper binding, axiom/receipt identity
checks, orphan/PID/cancellation cleanup, and proof/resource pairing. Current
negative controls exercise those rejection paths. No residual checkpoint finding
remains; their acceptance does not cover pending success/runtime/final gates.

Bulk proof/census/fidelity/resource evidence stays outside Git under
`/workspace/audit-abi-world-evidence/`. The committed evidence manifest points at
an immutable witness-milestone snapshot under its checkpoints directory. Latest
original.patch, handoff.md and sha256-manifest.txt are exported at the evidence
root with the full committed head. Registration proposals remain task-owned.

This milestone hands off after five useful items: continuous resource enforcement,
93 control packages, 29 basic packages, nine joint representation packages, and
the independent fidelity/accounting gate. Resume this same VM/branch/base and
existing persistent goal. get_goal is not exposed, which the coordinator explicitly
made nonblocking. Do not reset/create a goal or launch a replacement.

Next: add actual supported-program success contracts with Option-valued compilers
and jointly feasible nonempty inputs that refute reject-all/always-revert. Separate
checked-add assembly/layout availability from real branch execution. Prove actual
typed Panic-handler success. Use actual Backend.encode output for pinned reference
execution with exact/one-below gas and historical REVERT fork boundaries, labeling
external tests separately from Lean proofs. The pinned EthereumJS dependencies
are installed outside Git; reference results are not yet produced. Complete after
timings, full affected/final validation and independent final reviews. Keep Slice's
explicit gas/world limitations and H55 ownership intact. Any frozen repair must
retain a typed owner blocker and the required ESCALATE options. Do not merge,
push, publish, pre-gate or declare assignment completion while that work remains.
