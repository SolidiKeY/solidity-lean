# H62 item 2: ABI-world empty-statement audit

Owner: `solidity-h62-2-20261106/audit-abi-world`. Frozen base:
`c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. Branch:
`codex/solidity-h62-2-20261106/audit-abi-world`.
Repository: `/workspace/solidity-lean`.

## Scope and current checkpoint

This is an unfinished assignment. The source inventory covers all 24 modules in
`docs/module-map/abi-world.d/00-base.md`, with 177 declarations accounted for
exactly once. All 177 source signatures, their hashes, source hashes, section
context, ownership and provenance are in the external deterministic census.
The inventory deliberately includes unconditional statements as well.

Checkpoint 1's frozen-source inventory and premise classification are complete.
Checkpoint 2 has 46 checked simultaneous packages; 131 declarations remain
uncovered. Checkpoint 3's supported-program success/totality contracts, negative
trivial-compiler controls and gas/fork observations remain pending. Checkpoint 4
has a rejection-tested accounting tool, but its required completeness gate exits
2 because coverage is incomplete. Full affected validation, final acceptance,
and matched before/after checking measurements are pending.

All originals, generated roots, central maps, axiom pins and producer files are
unchanged. No statement, premise, exclusion or observation was weakened. There
are zero added axiom declarations, explicit proof placeholders, trust shortcuts,
or heartbeat overrides. No vacuity finding has yet been established for a mapped
statement; the remaining 131 packages must still be investigated.

The four directory files absent from the frozen map are `MutatingByteLoad.lean`,
`MutatingByteLoadControls.lean`, `TypedPacketMaterialize.lean` and
`TypedPacketMaterializeControls.lean`, under `Solidity/Backend/AbiWorld/`.
They are reported as map drift, not silently added to this census or declared
audited. In particular, the first pair's Producer premise is not evidence about
the 24 mapped modules.

## Ownership and premise classification

The verified coordinator ownership snapshot identifies
`H30-WRITER-solidity-v12-v17-20261031--v13-abi-world`, owner
`solidity-v12-v17-20261031/v13-abi-world`, status `coordination-only`, covering
`Solidity/Backend/AbiWorld/**`. Snapshot SHA256:
`7f5d40d46d386ed17731db55ed87f0564f5c9e667bddee00c0f12b28772f9cce`.
Latest Git authorship is separate provenance, not ownership authority. Existing
owned originals remain read only; no owner edit request was necessary.

Independent finder and skeptic traces found no direct global Producer,
Admission or compiler-correctness oracle premise in the 177 mapped signatures.
Seven statements assume fixed-input representation structures:

| Frozen theorem suffix under `Solidity.Backend.AbiWorld` | Structures |
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
`Evm/MemoryStructAlloc.lean:16`. `StateRepr.core` includes payment-oracle
agreement for every address/amount pair of the supplied transaction and machine
(`Evm/Sim.lean:225`). That compatibility still needs a joint witness; it is not a
global compiler producer. `CheckedAddArtifact.compiles` bounds references in one
artifact. `Widths L` is bounded metadata (`L → Fin 33`), with a DecidableEq
instance additionally required by `tag_bound`. Fits is three local inequalities.
The other 170 statements have data/type/instance inputs, local feasibility
conditions, or no binders. The census retains each full signature.

## Checked additive proofs

The isolated `H62AbiWorld` test library is declared only in the task-owned
alternate TOML. `hypotheses%` reads the unchanged theorem's elaborated type,
existentially packages its entire leading forall telescope in dependency order,
and replaces only the conclusion with True. Proof binders are retained even
when unused. This establishes joint feasibility independently of the original
proof or conclusion; it does not prove compiler success. The schema intentionally
does not unfold arbitrary definitions in conclusions. Future families must be
checked against their own statement shapes.

`WitnessSchema` has positive simultaneous and contradictory-premise controls.
`CodecWitnesses` covers every declaration in ErrorLayout (14) and ErrorRoundtrip
(5). `WindowWitnesses` covers every declaration in ErrorReadWindow (4),
ErrorOffsetWindow (3), PanicReadWindow (3), LibraryResultPacket (6), and
ReturnWordTransport (11). All 46 witness axiom reports say no axioms. Schema's
negative control uses only propext and Quot.sound. Complete per-file diagnostics
report success=true, partial=false, timed_out=false, no failed dependencies and
no errors. Witness receipts bind source, helper, configuration, checker driver,
wrapper, toolchain identity and frozen source state before/after checking.

## Reproduction and gates

Use the official preinstalled frozen-base Lean binary at
`/workspace/.setup/tools/lean-4.24.0-linux/bin/lean`:
Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`, Release;
Lake 5.0.0-src+797c613. The coordinator's 4.35.0 archive pin is retained in
`/workspace/h62-coordinator-inputs/toolchain-pin.json`; the latest message scopes
that requirement to migration lanes. This additive audit does not migrate the
frozen base or use a v4.24 per-master remote cache.

Commands run from the repository root:

```sh
python3 -B scripts/h62/item2/audit-abi-world/test_census.py
python3 scripts/h62/item2/audit-abi-world/census.py --output /workspace/audit-abi-world-evidence/census.json
python3 -B scripts/h62/item2/audit-abi-world/coverage.py --evidence /workspace/audit-abi-world-evidence
python3 -B scripts/h62/item2/audit-abi-world/test_coverage.py --evidence /workspace/audit-abi-world-evidence
python3 -B scripts/h62/item2/audit-abi-world/coverage.py --evidence /workspace/audit-abi-world-evidence --require-complete
```

The first four pass. The last exits 2, reporting 131 uncovered statements, each
with its owner. Its final status must remain failing until every package exists.
The source scanner handles the independently reviewed frozen grammar, not all
Lean syntax. Coverage regenerates all 177 exact frozen rows before accepting an
external census. Negative controls reject a shrunk census, stale schema,
unapproved axiom report and wrong tool identity.

Per-file Lean checks used this bounded serial command, substituting each module:

```sh
ulimit -v 12582912
flock -n /tmp/solidity-lean-feature-groups-20261025/writer.lock timeout 180 .venv/bin/python -B scripts/h62/item2/audit-abi-world/mcp_call.py lean_diagnostic_messages '{"file_path":"tests/h62/item2/audit-abi-world/H62AbiWorld/CodecWitnesses.lean","interactive":false,"timeout_s":120}'
```

All three current modules passed. `LEAN_NUM_THREADS=1`, explicit `-j1`, one open
LSP file and serial calls were used. The wrapper preserves the alternate TOML in
MCP's nested setup-file calls. The VM reports memory.max=17179869184, no active
swap; task proof processes had a 12 GiB address-space bound. Sampled aggregate
cgroup usage during the dependency checks was below 1.6 GiB. A continuous
aggregate/headroom monitor and full final resource evidence remain pending.
No systemd-run was called. KeySort passed bounded per-file MCP diagnostics with
no errors. Actual versions are saved in versions.log. No RUNTIME_GATE_PASS or
full-build acceptance is claimed.

One initial baseline dependency check omitted explicit -j1; it was stopped and
is not a resource-compliant gate. A following diagnostic completed while wrapper
repair was pending; it also does not count. Current witness receipts were rerun
after the nested-call configuration fix. Initial proof/gate-tool errors were
fixed before the successful current receipts. MCP can emit an event-loop cleanup
warning on shutdown; complete structured diagnostics, source hashes and command
exits are the decisive evidence.

## Independent reviews and resolved findings

Read-only agents `census_finder` and `census_skeptic` used no Lean server or builds.
Both accepted the 177-name source census after correcting twelve result-let
signature truncations (including inline `by have ... :=` values) and replacing
placeholder ownership. Both accepted the schema/19 codec and 27 window packages
within their stated source-review boundaries. The diagnostic wrapper now fails
closed on missing, partial, timed-out or unsuccessful structured results.

Their accounting-tool review found unanchored census input, stale helper/config
acceptance, unrestricted axiom reports and missing receipt identity checks.
Those findings were fixed and exercised by the four negative controls. Final
re-review is recorded in the external review receipt before export.

## Handoff and remaining work

Bulk census, proof diagnostics and proof-accounting data remain off Git in
`/workspace/audit-abi-world-evidence/`, with a committed evidence SHA256 manifest.
The same directory contains original.patch, handoff.md and sha256-manifest.txt
at export. The external handoff records the full committed head and exact paths.
Registration instructions are supplied in the task-owned registration fragment;
no central root/map registration was performed.

Resume this same VM, branch, frozen base and existing persistent goal. No goal
identifier/get_goal tool is exposed; coordinator verified the original goal and
explicitly made optional inspection absence nonblocking. Do not create/reset a
goal or launch a replacement. This checkpoint hands off after five useful work
items: inventory, schema controls, codec packages, window packages, and the
rejection-tested accounting tool. The assignment remains active and incomplete.

Next: cover all 93 control declarations (many have no input binders), then the
38 remaining non-control declarations. Build the seven representation packages
from the same concrete installed fixtures, not isolated structure inhabitants.
Add meaningful supported-program success and negative reject-all/always-revert
controls; preserve Slice's explicit absence of gas/fork semantics. Complete the
observable boundary work through suitable unchanged interfaces, or retain named
owner blockers if that requires a frozen repair. Run full affected/final gates,
matched same-cache/resource before/after timings (stop above 10% slowdown), final
independent reviews, and complete statement-fidelity accounting. Do not declare
completion, merge, publish, push, pre-gate or duplicate H55 work.
