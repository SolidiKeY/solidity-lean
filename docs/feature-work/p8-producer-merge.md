# P8/P8b Producer merge with an inhabited Producer (H57, H60)

Lane `cloud/move5-20261106/p8-producer` (H75: single writer of P8a + P8b,
taking over `memory-storage-copy` P8a and `v16-correctness-transfer` P8b).
Base: `cloud/move5-20261106/v16-base` with `origin/master` merged.

## 1. Inventory

| Item | Where | State before this lane |
|---|---|---|
| Frozen P8a `Producer` (H12) | `Lowering/P8/FrozenInterface.lean` | Parameters `S reference origins roots`; ten fields; no inhabitant. |
| P8a V2 (split failure coverage) | `Lowering/P8/FailureContractV2.lean` | Lossless `toV1`/`ofV1` pair; same obligations. |
| Admission half / assembly | `Lowering/P8/ProducerAssembly.lean` | `AdmissionHalf`, conditional `assemble`. |
| P8-SPEC-LAW1 | `Lowering/P8/ResourceContractLaw1.lean` | Any `Nat`-encodable resource refutes `FailureProjection`, hence `Producer`. |
| H24 wrapper | `Lowering/P8/DeclarationGraphAdmission.lean` | `base : P8a.Producer` + V07 `LocationGraphInterface.Admission base`. |
| Frozen P8b output | `Lowering/P8b/Frozen.lean`, `P8b/P8aInterface.lean` | `Producer A I extends Lowering`; `ProducerOutput S I`; `CertifiedInput`. |
| P8b structural pass | `Lowering/P8b/Domain.lean`, `P8b/Controls.lean` | `pass/dom/agrees/assemble` for a given emitter; toy identity `Cert`. |
| V16 H24 consumer | `Roadmap/V16/H24Input.lean` | `Request` over the H24 wrapper. |
| V07 consumers | `Lowering/V07/P8Bindings.lean`, `V07/LocationGraphInterface.lean` (+ unmerged `SourceRefusal`, `GraphAdmissionAssembly` on `cloud/moved3-20261105/v07-lowering`) | Laws indexed by a `P8a.Producer`; documented as vacuous. |
| P8 conditional glue | `Lowering/P8/ConditionalAssembly.lean`, `Lowering/P8/DeclarationGraphCheck.lean` | Build `P8a.Producer` / H24 wrapper from supplied halves. |
| V07 graph producers | `Lowering/V07/AcceptedGraphProducer.lean`, `Lowering/V07/LocationGraphProducer.lean` | Parameterised by a `P8a.Producer`. |
| V08 premises | `Lowering/V08/CreationPremises.lean`, `Lowering/V08/LibraryPremises.lean` | `admission : DeclarationGraphAdmission.Producer` field. |
| P9 | `Lowering/P9/*` | Elaboration/admission controls; does not mention `Producer`. |

Why vacuous: the only `SourceSpec` in the repository is G07's
`Roadmap.Controls.toySource`, whose resource `Bound` (`Nat × Bool`) is
`Nat`-encodable, so P8-SPEC-LAW1 refutes every `FailureProjection` for it
(now kernel-checked: `MergedControls.toySource_no_producer`).

## 2. Merge (H57) — no frozen statement changes

`Lowering/P8b/Merged.lean` defines `Merged.Producer S reference origins roots I`
as the pair (frozen `P8a.Producer`, frozen P8b `ProducerOutput S I`), with
`toP8a`, `toV2`, `toP8b`, `toLowering`, `ofPair`, definitional round trips,
`nonempty_iff` (merged inhabited ⇔ both frozen halves inhabited) and the H24
variant `Merged.H24` (`toProducer` forgets only the graph admission).
No field is weakened, dropped or made optional, so **no versioned pair is
published and no consumer migration is required**.

## 3. Inhabitant and controls (H60)

`Lowering/P8/PlanWitness.lean`:

- `planSource : SourceSpec` — G07's toy frontend and programs; the resource
  `PlanBound` carries a horizon and a full `Evm.FailurePoints` plan;
  `Failures := Evm.FailurePoints`; `NoFail` is the existing `Source.FailureResources.NoFail`; a plan failing
  the first frame after 0 events makes the run revert with empty data (later
  failure points never fire, since toy runs emit no events); request fates are
  read only through `NoFail`.
- `planProducer : P8a.Producer planSource planReference planOrigins planRoots`
  — every field proved: identity failure projection with full plan coverage,
  realization into `Source.SrcProg`s whose program is empty (the toy is
  encoded in the deployed contract name), extraction exact by construction
  (one root per program, toy profile is everything), checked frontend (certificate = parsed
  program, recomputed by `check`), exact admission, unambiguity, approved
  readings, both pipelines, non-vacuity (four G01 witnesses).
- `planLowering : Lowering planSource planIntrinsic` via P8b's own
  `assemble` with a G01 `Cert` whose bound function is the identity.
- Pins: `producer_inhabited` and `planLowering` at standard axioms only.

`Lowering/P8b/MergedControls.lean`:

- Witness: `planMerged`/`merged_inhabited`; `quiet_admitted`,
  `quietReceipt` + `quiet_receipt_checks` (kernel `decide`),
  `bad_tag_refused`, `quiet_executes`, `failing_plan_reverts`,
  `failing_plan_not_noFail`, `covers_failing_plan`, `lowered_success`.
- Negative: `toySource_no_producer` (P8-SPEC-LAW1 on G07's original source),
  `wrong_reference_no_realization`, `empty_no_producer` (a source parsing
  nothing), `bad_emit_no_certificate`.

**Scope, not overstated.** `planReference` is a MODEL reference: it decodes
the toy program from the deployed contract name of the Source program and
runs G07's machine under the plan, ignoring environment and horizon; it is
not `Source.sessionAt`. `planOrigins` coincides with the realization's
program map (`meaning_origin` is `rfl`), so the origins are not independent. The witness
proves the frozen interface satisfiable (H60, H62 (2)); it is not actual
Source adequacy, G15 or S05, and says nothing about Solidity programs.

## 4. Freeze and migration notes

- **All lanes:** `FrozenInterface`, `FailureContractV2`, `ProducerAssembly`,
  `DeclarationGraphAdmission`, `P8b/Frozen`, `P8b/P8aInterface` and
  `Roadmap/V16/H24Input` are unchanged in statement. New code may take a
  `Merged.Producer` and project; existing code needs no change.
- **V07:** statements indexed by `P8a.Producer` are no longer vacuous in the
  type-theoretic sense: instantiate at `planProducer` to get a non-vacuous
  control. The H24 wrapper at `planProducer` additionally needs
  `LocationGraphInterface.Admission planProducer`; `planOrigins` maps every
  admitted input to the EMPTY Source environment, so `graphs` holds with
  `n = 0` and `source_refuses` should follow from V07's unmerged
  `SourceRefusal.refuses_of_decls` (no declarations). This is a CONJECTURE,
  not checked here; that H24 instance is left to V07. The docstrings in
  `V07/P8Bindings.lean` and `V07/LocationGraphInterface.lean` saying
  "uninhabited" should be updated by V07 to cite `PlanWitness` (resources
  carrying full plans), keeping the caveat that `Nat` resources stay refuted.
- **V08:** `CreationPremises`/`LibraryPremises` take an H24 wrapper; their
  non-vacuous instance follows the V07 path above (H24 at `planProducer`).
  Their "vacuous until P8-SPEC-LAW1" docstrings should cite `PlanWitness`.
- **Stale docstrings outside this lane's write scope** (owners update):
  `V07/P8Bindings.lean:8`, `V07/AcceptedGraphProducer.lean:7`,
  `V07/LocationGraphInterface.lean:92`, `V07/LocationGraphProducer.lean:7`,
  `V08/CreationPremises.lean:13`, `V08/LibraryPremises.lean:9`,
  `Roadmap/V16/H24Input.lean:7` (generated by
  `scripts/roadmap-v16-h24-interface.py`; regenerate rather than hand-edit),
  `feature-work/roadmap-v07-lowering.md`, `feature-work/roadmap-v08-world-lowering.md`.
- **CR (memory-storage-copy):** P8a ownership moved here (H75); the actual
  `AdmissionHalf` for real Source and a Source reference built on
  `Source.sessionAt` remain open. The real source resource must carry failure
  plans (not `Nat`) or P8-SPEC-LAW1 refutes it.
- **MIC:** consumers of `CertifiedInput` can use `Merged.CertifiedInput`
  (definitionally the P8b one at the source half); `quietReceipt` is a
  concrete instance.
- **V16:** the P8b obligation is unchanged; `planLowering` is a non-vacuous
  instance of `P8aInterface.ProducerOutput` (via `⟨planLowering⟩`).

## 5. Reviews (checkpoint 1)

Read-only finder and skeptic, no Lean server. Confirmed and fixed:
missing consumers in §1 (P8 glue, V07 graph producers, V08 premises) and V08
migration note; stale "no inhabitant" module-map rows (updated in
`module-map/v08-adapters.d/00-base.md`); fragment heading spacing;
`PlanNoFail` now reuses `Source.FailureResources.NoFail`; exhaustion now reads
G06's "fails after 0 events" instead of any failure point; scope notes on the
empty Source program, non-independent origins, tautological extraction,
merged-pairing coherence and the V07 H24 conjecture; new plan-ignoring
reference control. Stale docstrings in other lanes' files are listed in §4,
not edited.

## 6. Gates

- Per-file (`gate.sh per-file` on the three new modules): PASS. A negative
  probe importing `MergedControls` fails as expected (missing `.olean`), so the
  PASS is real elaboration.
- Static gates (layers, trust, orphans, roots, fragments): PASS.
  `doc-paths` and `axiom-pins` fail on inherited findings that this lane does
  not touch (`after-roadmap-va1.md` Mathlib path; 0 errors, 4385 unrecorded
  pins, the same on `master`).
- `gate.sh checkpoint` library build: stopped by the 2 h session limit at
  2641/5999 modules with no errors. The build then finished under `./run-lean.sh`.
- `./run-lean.sh`: layers, roots, fragments and the Lake build of the default
  targets plus `SolkeyTestSuite` all pass ("Build completed successfully (6417
  jobs)", which includes `MergedControls`). Exit is 1 only because the last
  step, `check-solkey.sh`, finds 167 sort-annotation mismatches against the
  unpinned sibling `../solkey` checkout. This lane touches no rule or
  annotation table (its commits touch only `Lowering/P8*` and docs), so the
  drift is inherited.
