# MIC (memory-internal-calls): P9 handoff, cloud lane move6-20261106

Ownership moved from the Codex lane `solidity-compiler10-20261028/memory-internal-calls`
(H75). Base: `master` at `0b2a648b`. This file records the three work-queue items.

## 1. CheckedMul panic controls and packet-panic Q1

The packet-panic lane (`solidity-h62-1-20261106/packet-panic`) has not published
its shared helper. At `0b2a648b` no module or document mentions packet-panic,
and origin has no branch for that lane. `Backend/PrimitivePackets/CheckedMul/Controls.lean`
is unchanged: `exact_panic_bytes`, `panic_not_truncated` and `panic_not_empty`
still close by `decide`.

**Answer to packet-panic Q1: yes.** Replace `panic_not_empty`'s proof with the
shared helper, leaving the statement (`Source.panicData .arithmetic ≠ []`), name,
axiom print and MIC ownership unchanged. This is a proof-only change. MIC applies
it and checks the file after the helper's public signature is published. The
existing `Source.panicData_length` (`Source/Observe.lean:170`, length 36 for every
code) is enough to prove the helper for all panic codes. Wait: packet-panic,
"published shared helper and owner-applied proposal for the three CheckedMul
panic controls".

## 2. Frozen endpoints, NativeContext/Approved, β, ν and G38

Searched on master at `0b2a648b`:

- `NativeContext`: no declaration in `Solidity/`, `Bridge/` or `docs/`.
- `Approved`: `SourceSpec.Approved` (`Roadmap/Contracts.lean:760`) and
  `EvmSpec.Approved` (`:888`) are the frozen G01 predicates. Their session and
  fixed parameters are the `SourceSpec`/`IntrinsicSpec`/`EvmSpec` fields `fixed`
  and `session` (`:691–696`, `:819–823`, `:859–863`). The only instances are
  `toySource` and `emptySource` (`Roadmap/Controls.lean:283`, `:806`). There is
  no canonical source or IR spec, so no frozen canonical session endpoint, fixed
  β or executable ν exists for MIC to consume. `p8-admission.md` and
  `roadmap-v08-world-lowering.md` record the canonical `SourceSpec` as an open
  P8/V08 producer obligation.
- G38 branch obligation: the producer boundaries of `g38-failure-paths.md` are
  unchanged on master:
  - P7/VY4: `Transient.Instructions.step` still refuses nonempty `REVERT`
    (`Backend/Transient/Instructions.lean:32–36`).
  - V12: `RuntimeFrameInterfaceV1`–`V3` carry bare revert and success only, with
    no payload, panic or exhaustion transport.
  - VY5 H16: no failure-point equations are published.
  - V11 G41: `AbiWorld/PacketPrefix` covers prefixes of the packet emitter only,
    not general runtime value encoding, layout or readback.

None of these exists on master, so MIC cannot establish any of them itself.
Exact waits:

| Producer | Item |
|---|---|
| P8/V08 canonical-spec owner | canonical `SourceSpec`/`IntrinsicSpec` instance with session endpoints, `Approved` proof, fixed β, executable ν; any `NativeContext` |
| VY4 P7 | nonempty-payload rollback (`Transient.Instructions.step`) |
| V12 v12-flow-calls | payload, panic and exhaustion frame transport (interface after `RuntimeFrameInterfaceV3`) |
| VY5 | H16 failure-point equations |
| V11 v11-memory-operations | G41 runtime encoder prefix selection, layout and readback |

## 3. P9 CallsOK remainder: executable bound-body catalogues

Before this change, `source-progress-checked.md` ("Bound-body catalogues with
elaboration-derived frames") recorded that body/default admission and actual
selected-body identity were explicit proof obligations, not automatic recognition.
`Source/Calls/BoundRecognizer.lean` replaces it, for `BoundParentItems`
bodies only, with a sound (not complete) Boolean check, `catalogueB`, with
explicit default fuel. Concrete units still need proved dispatch and body-lookup
evaluation equations. See
[source-progress-checked.md](source-progress-checked.md#executable-bound-body-catalogue-recognition).

Backfill status follows `tests/h28-terra/drift-reports/evidence/item1-manifest.json`:
- SS-CP2 is "done-on-master (remainder queued)". `Roadmap/V16/SSCP2/` is
  unchanged, and `eval_new_mem`'s retained child-memory premise is not addressed here.
- S05-PROGRESS is "queued". It is the source progress theorem for the modelled
  fragment (coverage-plan S05: unmodelled features are `stuck`). This increment
  only makes bound-parent catalogue admission executable. It proves no progress
  theorem over all elaborated programs.

## Gates and reviews

Recorded in the final lane result.

## H121 P9 return checkpoint

The returned checkpoint `1ebcd0df16d3c8ba15cee9dccbd171ece5fb238e` was
merged with published master `a8f684928fa085d8976ead33e3d0db30208e7a4f`.
The existing recognizer statements and soundness claims are unchanged.
An independent finite-default recognizer-fuel completeness extension was
drafted, but its dependency build hit the unchanged 300-second cumulative
limit before reaching that extension. It is not a checked result and its
drafts are retained off the source tree, not registered.

The stopped group was compiling the published, unchanged
`Source/StmtProgress.lean`; this is not evidence of a per-proof timeout in that
file. No completed artifact for it was available in this worktree. Runtime
KeySort passed. Exact failure logs, setup/source hashes and static-review
outcomes are in the external handoff. Both draft reviews found no static
defect; neither supplies kernel evidence. Resume checking only after a
verified exact-input dependency-cache delivery or a demonstrated performance
repair; do not repeat the unchanged cold group or raise budgets.
