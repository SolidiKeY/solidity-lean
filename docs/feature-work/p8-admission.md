# P8: G15 admission and S05 failure resources

H10 helper lane, originally based on published `febf70a6ba99df908a69499aca026381c3993102`; rebased onto `63d3f9232416629146ab2f0a40d756dc9be43845` with the H12 frozen interface unchanged.
Branch: `codex/solidity-copy-recovery-20261030/memory-storage-copy-help`.
V16 retains G01 Lowering dom/agrees/cert. Existing source interpreter, static
frontend, importer and Horizon modules are unchanged by this checkpoint.

## Checkpoint 1: typed observation extraction and resource boundary

**Partial preparation, not complete G15, operational Failures or SourceSpec.**

- `Solidity/Frontend/Admission/Profile.lean`: `ScopeScan.certify_features`
  preserves the whole ordered feature list even after a diagnostic;
  `certify_iff`/`certify_rejected_iff` classify exactly the supplied uses by
  the existing model/abstract policy. `append_features`/`append_iff` preserve
  both root groups and their failures. These do not prove extractor coverage.
- `Solidity/Frontend/Admission/RootObservations.lean`: structural extraction
  over every current `RExpr`, `RArgs`, `RConvArgs`, `RLVal`, `RStmt` and
  `RItems` constructor. It includes nested index expressions, converted
  arguments, both conditional branches, loop init/test/body/post and both
  try outcomes. Sites retain exact builtin/member and call declaration
  identities. `root_observation_iff`/`accepted_roots` cover every supplied
  expression root. `ObservationSite.allowed_iff` requires a real frozen
  feature ID with model/abstract scope, in addition to S01's admitted status.
- `Solidity/Source/FailureResources.lean`: an extended bound carries G06's
  actual `FailurePoints`, ordered by horizon extension at fixed choices;
  replacement/retraction laws and the exact failure-free schedules are proved.
  `no_horizon_retraction` proves, without axioms, that independent G06 frame
  schedules cannot satisfy SourceSpec's failure replacement law over a bare
  Nat horizon. This is an obstruction, not a completed failure semantics.
- `Solidity/Frontend/Admission/Controls.lean`: inhabited timestamp/self roots,
  local shadowing, untaken branch and loop-post extraction, actual S01
  block-number type refusal, excluded/unknown metadata, retained uses after
  a rejection, dropped-request/frame-zero refusals and a false root-list
  expectation. These are kernel controls, not external EVM execution.

Gate G0: initial indexed matches were replaced by generalized-index
`casesOn` definitions after review; no exception or new executable syntax
representation was introduced. The final root module/controls build took
0.861s/1.4s versus 1.2s/1.8s for the preceding direct-match version (Lake
reported times, cache/dependency effects apply; not a controlled benchmark).
The whole focused closure passed 17 jobs. No heartbeat/fuel/search/test
budget, semantics, public statement or expectation was changed.

## Remaining original helper obligations

1. Close resolved declaration execution roots: bodies, modifiers, constants,
   constructor/base arguments and initializers, including recursive call
   closure and refusal of unresolved/missing targets. Current local call
   admission does **not** certify a callee body.
2. Complete feature extraction (types, all syntax/features and specification
   observations), prove its coverage against the independent source relation
   and combine exact metadata/settings/link classification. Current visitors
   extract observation sites, not all language features.
3. Prove solc-JSON import agrees with certified source or route the public
   compiler through the checked frontend. The current importer remains
   unchanged. `Checked.produceOpt_accepted` gives parse soundness, not its
   still-open completeness/uniqueness; the static frontend still has no
   complete multi-unit `FrontendSpec`/`Chain` instance.
4. Thread request/post-fee balances and frame failure schedules through real
   source execution, preserve rollback, depth and stipend behavior, extend
   resource consistency proofs, record monotone hash/slot preimages and
   construct the real `SourceSpec`. The resource module is not consulted by
   `sourceLangEvents`; its resource remains Nat and its state records no hash
   preimage trace. A constant/ignored failure schedule is not a solution.
5. Final source/adequacy controls, full gates and independent reviews for
   subsequent checkpoints. No universal bytecode/world result is claimed.

The updated coordinator registry assigns this lane serial Source Eval/Machine/Ctor/Horizon writes. V16 retains P8b/G01 and memory-internal-calls retains P9, SS-CP2 and S05-PROGRESS. The earlier FU2 ownership was historical; this checkpoint changes no evaluator or Horizon proof. The original memory-copy result remains
integrated at `92dbc1ce8971a3df3786fee32c8a2c5e506e8c3d`; H10 does not reset or
close its persistent goal.

## Evidence and review

VM evidence: `${VM_WORKSPACE}/p8-admission-help-20261102-evidence`.
Per-file checks, actual terminal reports, failed elaboration attempts, source
hashes and the final handoff are preserved there. Serial Lean 4.24.0 / Lake
5.0.0-src+797c613, explicit -j1, hard aggregate 12 GiB, zero swap and the
human-authorized 4 GiB available-host reserve. Final gate accounting is in the
checksum-bound handoff; a checkpoint is not assignment completion.

Independent read-only finder and skeptic inspected the source without Lean or
server use. Corrected findings: external-call feature ID, omitted self site,
precise scheduled-failure wording, generalized G0 recursors, and explicit S01
refusal instead of fabricating an excluded typed expression.

Current reconciliation evidence is separately retained at `${VM_WORKSPACE}/p8a-implementation-20261102-evidence`. The 32-job resource/controls and 42-job guarded-graph passes are focused checks, not a full build, complete admission, SourceSpec or EVM adequacy result. See [schema checkpoint](p8a-schema-checkpoint.md).

## Actual program containers

The [program roster checkpoint](p8a-program-observations.md) now scans all carried body/modifier-argument/constant/constructor/initializer/base-argument containers, retaining modifier/base target identities. Exact container occurrence is proved. Executed-target roster membership, complete feature/spec coverage, and operational SourceSpec/failure adequacy remain open.

## Selected dispatch bodies

The [finite dispatch checkpoint](p8a-dispatch-coverage.md) consumes published P9 selection membership and derives selected body/observation coverage from finite roster checks. Actual receiver/operational root closure and full profile admission remain open; this is not a new exclusion.

## Actual per-unit resolutions

The [source-resolution checkpoint](p8a-source-resolutions.md) now composes original raw-input/byte-parse checks with exact per-unit Source.Resolves' outputs and full tag/name/order preservation. Global typing, approved profile/execution-root coverage, public compiler correspondence and operational SourceSpec remain open.

## Component metadata

The [metadata checkpoint](p8a-source-metadata.md) composes existing strict/inheritance judgments across every resolved unit plus UnitsOK/settings/main, tied to original parsed trees. This does not establish full approved-profile admission or global imported-name typing. Nontrivial inheritance controls are delegated as M01–M03 in TERRA-TODO.md under H14.

## H14D current ownership and settings closure

This lane owns admission extraction and final P8a.Producer assembly. VY5 owns concrete OperationalReference, SourceOrigins, FailureProjection, SourceRealization and Source/FailureResources.lean; that file remains unchanged from relayed f9b23d61. The [settings/assembly checkpoint](p8a-all-settings.md) proves component-stage settings closure and freezes the split typed assembly boundary. No concrete Producer is supplied. Terra M01–M03 and R01–R02 remain pending.
