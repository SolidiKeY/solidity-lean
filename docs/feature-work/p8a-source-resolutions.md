# P8a checked per-unit source resolutions

Partial P8a checkpoint. This implements the raw-input, original-byte parsing
and per-unit source-resolution stages, not complete G15 admission,
well-formed/global import typing or SourceSpec/Failures. Frozen H12 signatures
are unchanged. Revision is this document's commit; the sealed handoff records
the exact revision and cumulative artifacts.

## Typed implementation

`Solidity.Lowering.P8.SourceResolutions` exports `Packet`, `UnitResolves`,
`UnitsResolve`, `Resolves`, `produce`, `check`, `checker`, `checkInput` and their
soundness/completeness/uniqueness and preservation theorems.

`Packet.units` contains actual `Source.Resolution` values. For every parsed
source unit, `UnitResolves` requires the exact original name and actual
`Source.Resolves'` judgment. The structural `UnitsResolve` relation preserves
every position and length. It is not a relation defined by checker acceptance.
The producer computes `Source.resolveUnit` on each original parsed tree.
The checker compares all packet tags and complete resolution values,
including unit syntax, environment, pipeline and ABI coder. Equality instances
for settings/environment/resolution are local; published P9's intrinsic source
syntax/declaration identity is reused, without new global instances.

`check_iff` decides this relation exactly; `produce_resolves`/`produce_checked`
construct all of its outputs, `unique` proves resolution uniqueness for a
fixed parsed input. These are completeness/uniqueness of the existing
per-unit resolution relation, not parser or whole frontend completeness.
`names_preserved`, `resolved_entry` and `checked_tags` preserve exact names,
all source judgments, full input settings and main selection.

The frontend and Roadmap pipeline/ABI-coder types are distinct. Explicit
`sourcePipeline`, `sourceCoder` and `frontendCoder` bridges map their exact
constructors. `order_agrees` requires existing `Settings.Ok`; it proves the
selected pipeline agrees with the original admitted evaluation order.
`coder_agrees` preserves the unit's own pragma under legacy and forces v2
under viaIR. No semantic order or coder formula is changed.

`sourceSettings` uses the empty link map required by `Source.Resolves'`.
Standalone `produce_checked` does NOT validate arbitrary settings or links.
`checkInput` additionally checks the ORIGINAL `Input.Ok` and exact source
bytes/layout through `CheckedSyntax.check`. `input_sound` proves all three
stages; `checked_input_tags` and `checked_input_links` prove original tag
preservation and empty original links at that composed boundary. Nonempty
input links are refused, not silently discarded as admission. The linked
negative has matching parsed/packet settings and passes both later stages,
so its refusal isolates the original raw-input guard.

## Controls and remaining boundary

Both pipelines accept the existing explicit byte/tree/layout contract fixture.
A two-unit input with distinct A.sol/B.sol names, main A.sol, original bytes
and two matching certificates also passes the composed check. Same-label,
same-length packets with corrupt source pipeline or ABI coder are rejected.
Wrong packet settings/main, missing/reordered/duplicated results, wrong source
name, missing parse certificate and nonempty original links are refused.
A pragma-v1 source uses v1 under legacy and v2 under viaIR; those two controls
are axiom-free. The two-unit fixture proves the three stated stages only;
there is no claim of global import typing or source execution.

Per-unit `resolveUnit` constructs an environment; it does not establish its
well-formedness or the global imported-name/type judgments. No syntactic
profile verdict is promoted to exact G00 classification. Parser
completeness/uniqueness, metadata/global resolution, all execution/observation
roots and features, public compiler routing or solc-JSON correspondence,
operational failure/hash semantics and actual SourceSpec realization remain
open. No new SourceSpec/Producer inhabitant or universal EVM/world claim is
exported. Existing semantic claims and exclusions are untouched.

## Checks and handoff

Base: fetched published `d4e72c5d190e09f471df558dae8720ca224a1e10`. Its only new publication relative to
`19bf3ba677c45d35acc1907b8e35a866dd3bb02a` is runtime-frame V2; P8a/source
interfaces are unchanged. The private branch was rebased, preserving old
`64ebb2ed2635223cd201d62a543e32042f334af1` under
`refs/recovery/p8a/dispatch-64ebb2ed` and keeping every prior seal.

`timeout 300 lake build Solidity.Lowering.P8.SourceResolutionControls` passed
33 jobs, 2.068 seconds, peak aggregate RSS 713117696 bytes; no OOM/resource
stop. The base module checked in 1.5 seconds in resolutions-04; final controls
reported 1.7 seconds in resolutions-06 (separate checks, not a controlled
benchmark). Printed headlines use only propext/Quot.sound or no axioms; no
sorry, new axiom, native decision shortcut or increased budget. Failed
elaboration attempts remain failed under exclusive labels. Final per-file
`timeout 300 lake env lean --tstack=131072 Solidity/Lowering/P8/SourceResolutionControls.lean`
passed in 2.325 seconds, peak aggregate RSS 727740416 bytes, after strengthening
the link guard control.

Lean 4.24.0 / Lake 5.0.0-src+797c613, LEAN_NUM_THREADS=1 and explicit -j1,
hard whole-group 12 GiB/no swap and authorized 4 GiB host reserve. Per-file
MCP is unavailable; native touched-module checking is the fallback. H12
full/root/import, combined TrustAudit, TestSuite, corpus, strict/docs/sort
end-of-lane gates remain required. Focused passes do not substitute for them;
previous full interruption and historical documentation failures stay failed.

Independent read-only finder/skeptic used no Lean/server/builds. Corrected
control gaps: same-label resolution corruption, nonempty original link
refusal, and an inhabited TWO-unit full three-stage control. They approve
checkpoint accuracy only. Logs, terminal receipts, exact source hashes and
sealed cumulative exports are recorded by the machine-readable handoff.
Evidence: `/workspace/p8a-implementation-20261102-evidence`.

Consumers: V07/V08/V09/V16/V17/VY5. V16 retains P8b/G01. S02-IMMUT,
SS-CP5-HASHED and SS-NEW remain queued. Existing persistent goal unchanged;
no worker push, default-branch edit or controller integration claim.
