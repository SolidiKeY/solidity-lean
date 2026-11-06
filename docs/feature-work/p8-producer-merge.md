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
  `Failures := Evm.FailurePoints`; `NoFail` is exactly G06's reading (every
  request runs without failure point, no frame fails); a failure point at the
  first frame makes the run revert with empty data.
- `planProducer : P8a.Producer planSource planReference planOrigins planRoots`
  — every field proved: identity failure projection with full plan coverage,
  realization into actual intrinsic `Source.SrcProg`s over the empty
  environment, exact extraction, checked frontend (certificate = parsed
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
runs G07's machine under the plan; it is not `Source.sessionAt`. The witness
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
  `n = 0` and `source_refuses` follows from V07's unmerged
  `SourceRefusal.refuses_of_decls` (no declarations). That H24 instance is
  left to V07 (it depends on its unmerged module). The docstrings in
  `V07/P8Bindings.lean` and `V07/LocationGraphInterface.lean` saying
  "uninhabited" should be updated by V07 to cite `PlanWitness` (resources
  carrying full plans), keeping the caveat that `Nat` resources stay refuted.
- **CR (memory-storage-copy):** P8a ownership moved here (H75); the actual
  `AdmissionHalf` for real Source and a Source reference built on
  `Source.sessionAt` remain open. The real source resource must carry failure
  plans (not `Nat`) or P8-SPEC-LAW1 refutes it.
- **MIC:** consumers of `CertifiedInput` can use `Merged.CertifiedInput`
  (definitionally the P8b one at the source half); `quietReceipt` is a
  concrete instance.
- **V16:** the P8b obligation is unchanged; `planLowering` is a non-vacuous
  instance of `P8aInterface.ProducerOutput` (via `⟨planLowering⟩`).
