# V15 H14 routine proof packet — EnvironmentTasksV1

Generated signatures: `Bridge/SolidityBridge/RoadmapV15/P10/EnvironmentTasksV1.lean`.
Regenerate/check with `python3 scripts/roadmap-v15-generate-environment-tasks.py --check`.
The JSON specification and generator own the frozen v1 signatures; announce V2 before changing them.
The frozen task module supplies no theorem, instance or axiom. Separate Sol producer lemmas now exist in `Bridge/SolidityBridge/RoadmapV15/P10/EnvironmentObservationProducer.lean`; they require LocalFacts at the actual site. Minimal finite clients exist in `Bridge/SolidityBridge/RoadmapV15/P10/EnvironmentObservationWitness.lean`. Universal routine facts and the unconditional frozen claims remain unproved.

Implement in NEW module `SolidityBridge.RoadmapV15.P10.EnvironmentObservationBatch`:

| Lemma | Exact statement type | Why routine |
|---|---|---|
| `origin_local_facts` | `EnvironmentTasksV1.OriginFactsClaim` | Unfold existing C', δ, α and memoryExpansionCost only; no execution proof. |
| `gasprice_local_facts` | `EnvironmentTasksV1.GasPriceFactsClaim` | Same finite base-cost/arity/no-expansion equations; no execution proof. |
| `chainid_local_facts` | `EnvironmentTasksV1.ChainIdFactsClaim` | Same finite existing opcode equations, no new environment/profile parameter. |
| `source_refusals` | `EnvironmentTasksV1.SourceRefusalsClaim` | Existing G31 admittedOp and step definitions refuse exactly these opcodes. |

Construct `glueBatch_discharged : EnvironmentTasksV1.PendingGlueBatch` ONLY after all four proofs exist; never take PendingGlueBatch or desired execution as a hidden premise. Retain original actual gas/stack/fuel order and full State/X observations. No new Scalar/environment slice, source key, pin/fork, maxHeartbeats, recursion or test budget.

Automation first under H14: use lean_multi_attempt with simp only/rfl/decide/omega and applicable repo tactics before manual steps. Record actual tool availability; never present CLI checks as MCP. Use the shared toolkit when present. No Solidity.lean edits; any eventual registrations/freezes must be generated.

Only after Sol supplies the producer proofs, add controls in NEW module `SolidityBridge.RoadmapV15.P10.EnvironmentObservationBatchControls`: populated origin19/source11/owner7 and nonzero account/memory/calldata/return buffers; gasPrice37 versus initial gas9/remaining7; actual pin chainId; complete ordered code/stack; inherited-static and writable cases; input1023 push success/1024 overflow; gas/fuel refusal order; source-profile refusal. Print actual axiom sets for headlines and controls. Preserve every original observation/profile refusal.

NOT TERRA: proving OriginClaim/GasPriceClaim/ChainIdClaim or their fetched/X agreement producers (these are statement-only Sol tasks), SIGNEXTEND word/Scalar producer (now proved below), compiler/source lowering, ABI, physical allocation/PaddingCorrect, Osaka approval, account/world/call/transaction/resource/trace producer proofs. These stay with Sol/original owners. No local or parent completion follows from this packet. All150 full opcode rows remain OPEN.

## Sol follow-up (not Terra)

After the universal facts are proved, Sol will instantiate `origin_at`, `gasprice_at`,
and `chainid_at` with the corresponding per-site fact to discharge the three
frozen producer claims. The existing finite witnesses are not proofs for all
sites. Sol retains these producer results and their semantic review. QH14AUTO
is resolved by the authorized bounded scratch-file automation fallback; use
one example per candidate, retain failures, and keep successful automation.

## Sol numeric progress

The positive SIGNEXTEND case is now proved in
`Bridge/SolidityBridge/RoadmapV15/P10/SignExtensionPositive.lean`, with minimal
nonzero and strict-domain witnesses in
`Bridge/SolidityBridge/RoadmapV15/P10/SignExtensionPositiveWitness.lean`.
General negative/truncating Scalar/reference primitive agreement is now proved below; source/compiler/Osaka origin work stays with Sol. This does not
change or complete the delegated environment fact/control tasks.

## Further Sol numeric progress

The existing positive module now additionally proves arbitrary high-bit
truncation when the selected low-width residue has a clear sign bit. See
`signextend_nonnegative_residue_word` and
`signextend_nonnegative_residue_agreement`; concrete clients are in
`Bridge/SolidityBridge/RoadmapV15/P10/SignExtensionResidueWitness.lean`.
Negative low-residue and all-index Scalar/reference extension are now proved below; source/compiler/Osaka work remains with Sol. This does not discharge or
change the delegated environment facts or unconditional frozen claims.

## Completed Sol primitive: all-index SIGNEXTEND

`signextend_negative_residue_word`, `signextend_width_word`,
`signextend_all_word`, `signextend_scalar_result` and
`signextend_all_agreement` now prove the actual pinned reference/Scalar
primitive for every index/value word, without a sign or residue premise.
Unified clients and negative controls are in
`Bridge/SolidityBridge/RoadmapV15/P10/SignExtensionAllWitness.lean`.
This does not complete any full opcode row or the compiler/source/Osaka/resource
composition, and does not change the environment work delegated above.

## Storage-isolation control continuation

Two Sol producer laws are checked in
`Bridge/SolidityBridge/RoadmapV15/P10/StorageWarmTransport.lean`:
`storage_keys_compare_eq` and `sload_distinct_cost`. Their numeric pair inequality
is not a hash injectivity or symbolic-path premise.

Module `SolidityBridge.RoadmapV15.P10.StorageIsolationControls` now has four
checked and registered clients: `cold_distinct_client`, `warm_distinct_client`,
`same_pair_counterexample` and `complete_ordered_observations`. Their original
proof bodies were accepted unchanged after the published-base rebase. This
routine continuation is complete; do not duplicate it. The original delegated
environment packet remains unchanged and pending.

## Invocation control continuation (source-only)

The three charged fetched producers in `Bridge/SolidityBridge/RoadmapV15/P10/InvocationEnvironment.lean`
are checked. Seven routine control bodies in the sibling `InvocationEnvironmentControls.lean`
are proposals only: corrected record layout has not passed the guarded kernel check.
Do not treat them as proved or register them before actual passing diagnostics.

| Module | Lemmas | Why routine |
|---|---|---|
| `SolidityBridge.RoadmapV15.P10.InvocationEnvironmentControls` | `address_client`, `caller_client`, `callvalue_client` | Instantiate checked producers in independent full expected records. |
| same module | `legal_capacity`, `resource_order` | Existing finite native checks at legal stack boundaries, exact gas and fuel. |
| same module | `distinct_identities`, `complete_ordered_observation` | Concrete nonzero identity/order distinctions and complete populated observations. |

Keep every statement and expected value; do not weaken resource or identity distinctions.
Monitor refusal is not a passing Lean check. The earlier EnvironmentObservationBatch
packet remains independent and pending; these proposals do not replace it.
# Preserved task lists after published adoption

## Existing owned list

# Routine proof queue — current G21 follow-up

Earlier superseded V2/P10 notes remain preserved in refs/checkpoints/v13-before-c467-rebase and the previous sealed exports. They are not silently re-adopted here.

## G21 readback compatibility glue (H14 cascade; not a discharged proof)

| Module/lemma | Why routine and exact prerequisites |
|---|---|
| Original V13 Solidity.Backend.AbiWorld.ReturnedBytes.memory_call_pushes_zero (source at main85d13e5c7db386fd832391be5f7d04970ad31f22) | Existing theorem statement is unchanged; add/refine the three newly published Compiler.Compilation cases memoryCopy/fixedMemory/copyConstruction. Each has isMemoryCalls=false and contradicts hc. Do not weaken hc or any representation/cost bound, edit producer semantics or increase budgets. This is owned compatibility glue for Terra, not work completed by this checkpoint. |
| Future G21 canonical Error packet entry/body composition | Apply existing BytesReadback.roundtrip after source_error codec equality, retaining size<=lim, free+allocationBytes<=lim and original2<=f. BLOCKED until the owned constructor glue above and V12 FrameLaws Binders/RetBinders interface repair are available. No desired verdict premise or new admission policy is allowed. No proof claimed or continuation scheduled. |

## Storage ABI finite success control (unchanged proof budgets)

Module: Solidity.Lowering.V08.LiteralFailureStorageDecodeControls.
Lemma: decode_true (pipeline : Roadmap.Pipeline) :
 (evalE (global pipeline) frame 35 decoder).run
  (.cons (.storRef rfl path) caller,canonical) =
 (.ok (.val (.bool true)),(.cons (.storRef rfl path) caller,canonical)).
Why routine: closed finite existing evaluator, actual storage word of31zero
bytes and final1; split byte recursion into short blocks or reuse an exact
read-loop equation, then normalize the existing bool decoder. Single rfl
exceeds maxRecDepth; no budget increase permitted. Validated generic
load_bytes/load_memory/bytes_ok/arm/local_ok proofs stay with Sol. The host
#eval outcome is testing only, not this kernel proof. Raw failed attempts and
deferred statement are sealed with this checkpoint. Do not edit Source or
replace any read/decoder result by an assumption. No sorry/axiom placeholder
is added to Lean sources.

### Resolved: storage ABI finite success control

The deferred decode_true statement above is now proved, without budget changes,
as LiteralFailureStorageSuccessControls.decode_true in commit
364b2a8d319fa133e49f860faeba175f28fa4d2e. copied_observed is actual kernel
computation (decide +kernel), copied_full combines it with stored_bytes state
preservation through an abstract run_from_observation lemma, and word_decoder
isolates actual Source bool decoding before the final evaluator rewrite.
No Terra work remains for this item. Original failed attempts/seal remain
immutable; generic and all-profile/runtime obligations are unchanged.


## Published list

# Routine handoff status

## NJ1 — completed for the fixed fixture

The exact original decoder equality, packet and compilation/source/model
endpoints are now kernel-proved in the actual module
`SolidityBridge.Yul.StructuredSwitchJsonKernelAttachment`, namespace
`SolidityBridge.Yul.StructuredSwitchJson.KernelControls`:

- `raw_nested_parsed`: `blockAux 20 ast = .ok tree`, with no parser premise.
- `raw_nested_packet`: the original `Packet [] 20 16 (Controls.fixture "1")`.
- `raw_nested_compiles`: exact `checkCompile` equality returning that packet.
- `raw_nested_source`: actual closed-word execution at horizon16.
- `raw_nested_low_fuel`: exact compiler horizon2 refusal for the same fixture.
- `raw_nested_model`: arbitrary mathematical machine/caller, with the real
  represented-stack premise retained.

Bounds20/16, dirty literal, fixture and expected prefix21/999/42/17 are unchanged.
Earlier failed attempts are preserved as evidence. No NJ1 proof remains pending;
this closes only the fixed-fixture obligation, not generic JSON correctness,
Solidity admission, Source/G24/native adequacy or the full original lane.
No earlier excluded Terra tasks or completed work are restored here.
# H14 routine glue — P8a-SPEC

These are statements for separate Terra commits, not Lean axioms or placeholders.
No frozen `Producer` or realization inhabitant is supplied. Producer and
soundness arguments, actual failure execution, origins and SourceSpec remain
with VY5; CR owns admission/extraction and final Producer assembly.

| Module | Lemma statement | Why routine |
|---|---|---|
| `Solidity/Lowering/P8/FailureProjection.lean` | `points_withPoints (r : Resource) (p : Choices) : points (withPoints r p) = p` | Existing transferred `Bound.failures_with`/field projections. |
| same | `horizon_withPoints (r : Resource) (p : Choices) : (withPoints r p).horizon = r.horizon` | Existing transferred `Bound.horizon_with`. |
| same | `failureFree_noFail (n : Nat) (balances : Nat → Nat) : NoFail (points (failureFree n balances))` | Existing transferred `noFailures_noFail`. |
| `Solidity/Lowering/P8/SourceRealization.lean` | `machineAgreement : MachineAgreement` — completed | Actual definitional equality proved; no resource adequacy asserted. |

Actual failure schedules are NOT consulted by the current bare-horizon Source
session. Do not fill this gap by ignoring schedules, choosing a favorable
operational reference, or weakening the frozen resource-point law. These routine
facts do not construct `FailureProjection S` or `SourceRealization` for a real S.

## Independent failure-plan routine glue

| Module | Lemma statement | Why routine |
|---|---|---|
| `Solidity/Lowering/P8/FailureProjection.lean` | `(points (requestCut h balances i b cut)).tx i = .runs b (some cut)` | Unfold requestCut/points, simp only if_pos rfl. |
| same | `j ≠ i → (points (requestCut h balances i b cut)).tx j = .runs (balances j) none` | One if_neg branch, no runtime adequacy. |
| same | `(points (requestCut h balances i b cut)).frame k = none` | Record projection. |
| same | `(requestCut h balances i b cut).horizon = h` | Record projection. |
| same | `¬ NoFail (points requestCutWitness)` — completed | Actual requestCutWitness_not_noFail theorem reuses request_cut_not_noFail. |
| same | `(frameDiagonal extract).tx i = .runs 0 none` | Definitional projection; makes minimal-counterexample request side explicit. |

These statements do not change Source resources or the frozen interface.
The request-cut and diagonal soundness arguments remain with VY5.

## H16 cursor interface routine facts

- `Source/FailureCursor.lean`: projection lemmas for nextRequest after
  enterRequest, nextFrame after enterFrame, and unchanged counters after
  leaveFrame/leaveRequest; constructor/record reductions.
- FrameBudget.grow preserves ordinal.val and emitted/cut; Fin.castSucc
  projections. Stop.growFrame/growRequest preserve kind and numeric owner.
- Prove new frame IDs exceed every existing frame ID using Fin.isLt;
  prove pop never reuses an ordinal. Resource execution, unwind soundness,
  actual hooks and horizon consistency remain VY5's producer obligations.

## H16 explicit-plan frame identities (routine; no placeholders in Lean)

Module `Solidity.Source.FailureMachine`, namespace `Source.FailureExecution`:
- `frame_none {E Γ α} (body : Source.EM E Γ α) : frame none body = body`.
- `check_none {E Γ} : check (E := E) (Γ := Γ) none = pure ()`.
- `pending_none {E Γ} : pending (E := E) (Γ := Γ) none = pure false`.
- `emit_none {E Γ} (event : Roadmap.Event) : emit (E := E) (Γ := Γ) none event = Source.emitEvent event`.
All are definitionally the None branch, routine `rfl`; immutable-plan execution
and owner/error soundness remain with Sol. Do not alter the Source evaluator.

## Actual Source event hook (routine glue; no Lean placeholders)

- `Source/FailureEventLaws`, `emit_disabled_run`: for arbitrary E/Γ/event/l/s, `(Source.emitEvent event none).run (l,s) = (.ok (), (l,{s with events := s.events ++ [event]}))`. Routine definitional compatibility, including stale cursor metadata.
- `Source/FailureEventLaws`, `emit_facade_eq`: `FailureExecution.emit plan event = Source.emitEvent event plan`. Routine facade identity.

The general reached-stop/full-state soundness law remains Sol-owned and is proved in the module. These routine statements are not assumed by any proof.

## Explicit-plan runtime compatibility (routine statements only)

- `Source/FailurePrimitives`, `preflight_none`: for every typed EM body, `preflight none body = body`; definitional None branch.
- `Source/FailurePrimitives`, `preflight_some`: `preflight (some points) body = (do check (some points); body)`; definitional enabled branch.

No placeholder theorem or assumption is used. The Source CALL-prefix reduction/entered-child proof and fixed-plan horizon soundness remain Sol-owned, not delegated as routine glue.
