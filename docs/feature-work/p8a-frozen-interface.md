# H12 frozen P8a producer contract

**Interface only; no implementation or adequacy result.** Frozen module:
`Solidity/Lowering/P8/FrozenInterface.lean`, namespace
`Solidity.Lowering.P8.P8a`. Signatures change only after coordinator notice.

Consumers V07, V08, V09, V16, V17 and VY5 import that module. V16 retains
P8b G01 Lowering dom/agrees/cert and builds against the external
`S : P8a.Spec`, definitionally the existing `Roadmap.SourceSpec`.

## Frozen types and theorem obligations

- `Spec`, `SourceProgram`: existing G01 SourceSpec and actual environment-indexed
  Source programs, without a competing syntax or source contract.
- `OperationalReference`: independent resource type, G06 points projection and
  source execution relation. No reference value is exported.
- `SourceOrigins`: independent parsed/resolved meaning-origin interpretation.
- `RootModel`: independent execution-root/observation-root/feature relations and
  combination/settings-aware classifier. It is external to `Producer`.
- `Extraction`, `Extractor`: exact root and feature coverage and exact profile
  classification relative to the independently validated reference model.
- `FailureProjection`: full independent G06 choice coverage via `ofPoints` and
  `points_ofPoints`, plus necessary request/frame consequences of NoFail.
- `SourceRealization`: exact reference execution agreement, meaning-origin
  agreement and preservation of the resource's actual G06 plan.
- `Producer S reference origins roots`: required realization, extraction,
  checked frontend, sound/complete Admission, frontend agreement,
  Unambiguous/Approved/AllPipelines/NonVacuous and failure projections.

Every proof field is an explicit **unimplemented obligation**, not a new axiom,
proof, premise silently added to an existing theorem, or populated instance.
No `Producer`, operational reference or actual SourceSpec instance is supplied.
Actual Source adequacy of S, reference, origins and root relations remains
mandatory: arbitrary empty root relations or a self-chosen reference cannot be
used to claim actual-source completeness. Types are frozen; their realization
and its source correspondence are pending, not waived.

## Checkpoint handoff

Base `febf70a6ba99df908a69499aca026381c3993102`; branch
`codex/solidity-copy-recovery-20261030/memory-storage-copy-help`.
Revision is the commit containing this document; the sealed machine-readable
handoff records its full SHA. Only the interface, its root import and this
handoff document belong to the freeze commit; prior implementation WIP remains
separate and preserved.

Per-file command: `timeout 300 lake env lean --tstack=131072 Solidity/Lowering/P8/FrozenInterface.lean`
with explicit -j1, LEAN_NUM_THREADS=1, 12 GiB/no swap and the authorized 4 GiB
host reserve. Final diagnostic exit 0 in 0.775 seconds. No proof or admission
implementation was checked by that success. No sorry or axiom declaration.

The pre-H12 full run was explicitly stopped under H12 interface-first priority
to release the writer lock: container exit 137, OOMKilled=false; **interrupted,
nonpassing**. Its completed source/module checks, 740-second Horizon baseline,
592-second OpenLoops and 297-second DecisionHashes measurements remain evidence
of those modules only. The full build/TestSuite/sort pipeline did not pass.
No full gate is rerun for this interface-only turn.

VM receipts: `/workspace/p8-admission-help-20261102-evidence`.
Independent finder/skeptic reviewed the signature draft read-only, without
Lean/server/builds. Findings prompted external reference/root parameters,
meaning-origin/resource-point laws and full choice roundtrip coverage. These
are declarations of obligations, not completed producer proofs.

P8a G15/SourceSpec/Failures remains current. S02-IMMUT, SS-CP5-HASHED and SS-NEW
remain queued. No goal reset/completion, default branch merge or worker push.
