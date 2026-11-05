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


<!-- Preserved V10 routine obligations; none is marked discharged by this merge. -->

# C157 routine adapter

Module: `Solidity/Lowering/StorageOps/SourceWordCommutation.lean`.
Lemma: `Solidity.Lowering.StorageOps.SourceWordCommutation.complete`.
Why routine: combine checked `run` in both orders, `world_commute`, and
`journal_order` in both orders; no new soundness argument or premise.

The statement elaborated in the failed automation scratch. It is NOT a compiled
Lean declaration or a closed proof. Keep every premise and exact journal snapshot.
Do not claim full Source states/journals commute, fresh lvalue compilation,
whole compiler or implicit rollback. No admission is permitted.

```lean
namespace Solidity.Lowering.StorageOps.SourceWordCommutation
theorem complete {E : Source.Env} {Γ : Source.RCtx} (frame : Source.Fr)
 (p : Source.SPath) (v : Source.Val E.layout (E.cellTy p))
 (q : Source.SPath) (w : Source.Val E.layout (E.cellTy q))
 (locals : Source.Locals E.layout Γ) (state : Source.St E)
 (writable : frame.static=false) (ordinaryP : E.transientRoot p=false) (ordinaryQ : E.transientRoot q=false)
 (different : p≠q) :
 let forward := (two frame p v q w).run (locals,state)
 let reverse := (two frame q w p v).run (locals,state)
 forward=(.ok (), (locals,SourceWordWrite.after frame q w (SourceWordWrite.after frame p v state))) ∧
 reverse=(.ok (), (locals,SourceWordWrite.after frame p v (SourceWordWrite.after frame q w state))) ∧
 forward.2.2.ex.world=reverse.2.2.ex.world ∧
 forward.2.2.ex.journal =
 .account frame.this ((SourceWordWrite.after frame p v state).ex.world.accounts frame.this) ::
 .account frame.this (state.ex.world.accounts frame.this) :: state.ex.journal ∧
 reverse.2.2.ex.journal =
 .account frame.this ((SourceWordWrite.after frame q w state).ex.world.accounts frame.this) ::
 .account frame.this (state.ex.world.accounts frame.this) :: state.ex.journal
end Solidity.Lowering.StorageOps.SourceWordCommutation
```

The historical twelve adapters remain in the preserved original checkout and prior handoffs; they are not resubmitted here. This adds one pending routine adapter.

## C159 routine captured failure adapter

Module: `Solidity/Lowering/StorageOps/SourceWriteRollback.lean`.
Lemma: `Solidity.Lowering.StorageOps.SourceWriteRollback.run_refused`.
Why routine: unfold the existing pair, use checked `SourceWordWrite.source_write`
for the first operation and `static_write` for the second through `Hoare.run_bind`.
The producer arguments and actual complete controls are checked separately.
This statement is uncompiled; no stub, admission or implicit rollback claim.

```lean
namespace Solidity.Lowering.StorageOps.SourceWriteRollback
theorem run_refused {E : Source.Env} {Γ : Source.RCtx}
    (writer rejector : Source.Fr) (p : Source.SPath)
    (v : Source.Val E.layout (E.cellTy p)) (q : Source.SPath)
    (w : Source.Val E.layout (E.cellTy q))
    (locals : Source.Locals E.layout Γ) (state : Source.St E)
    (writable : writer.static=false) (ordinary : E.transientRoot p=false)
    (static : rejector.static=true) :
    (refusedAfter writer rejector p v q w : Source.EM E Γ Unit).run (locals,state)=
      (.error (.revert []),(locals,SourceWordWrite.after writer p v state))
end Solidity.Lowering.StorageOps.SourceWriteRollback
```

Two routine adapters are specified here; the historical twelve remain preserved
separately, for fourteen pending adapters total. Neither statement is compiled.

## C166: complete primitive-copy fuel classification

Proposed owned module name: `Solidity.Lowering.StorageOps.SourceStorageCopyPhases`
(no file or root import registered).
Lemma: `Solidity.Lowering.StorageOps.SourceStorageCopyPhases.all_fuel`.
Why routine: case analysis on fuel versus count+2/count+3, then instantiate the
checked `SourceStorageCopyBarrier.copy_timeout`, `SourceStorageCopyPayload.copy_prefix`,
`SourceStorageCopyEmpty.copy_empty` or `SourceStorageCopyPrefix.prepared`; the
remaining work is natural-number substitution and zero-length log normalization.
This is an uncompiled statement, not a stub or an assumed future theorem.
The hard phase producers and nontrivial complete controls are checked separately.

```lean
namespace Solidity.Lowering.StorageOps.SourceStorageCopyPhases
theorem all_fuel :
∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (_writable : frame.static=false) (t : Solidity.Source.IntTy)
 (src dst : Solidity.Source.SPath) (_different : src≠dst) (fuel count oldLength : Nat)
 (payload : Nat → Solidity.Source.Val E.layout (.int t))
 (typed : E.pathTy dst=some (.array .storage (.int t) none))
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_sourceHeader : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame src).run (locals,state)=(.ok count,(locals,state)))
 (_reads : ∀ j<count,(Solidity.Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index j)) (.int t)).run (locals,state)=(.ok (payload j),(locals,state)))
 (_targetHeader : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame dst).run (locals,state)=(.ok oldLength,(locals,state))),
 let trace := Solidity.Backend.StorageOps.SourceStorageCopy.copyLog frame t dst count oldLength payload typed
 let written := Solidity.Backend.StorageOps.SourceStorageCopy.writes frame t dst payload
   (fun j => (Solidity.Backend.StorageOps.SourceStorageCopy.element_type t dst typed j).symm) 0 (count-1)
 (Solidity.Source.storeVal (E:=E) (Γ:=Γ) frame fuel (.array .storage (.int t) none) dst
   (Solidity.Source.Val.storRef (τ:=.array .storage (.int t) none) rfl src)).run (locals,state)=
 if fuel≤count+2 then (.error .timeout,(locals,state))
 else if fuel=count+3 then
   if count=0 then
     if oldLength=0 then (.ok (),(locals,{state with ex:=state.ex.run trace}))
     else (.error .timeout,(locals,state))
   else (.error .timeout,(locals,{state with ex:=state.ex.run written}))
 else if oldLength-count≤fuel-3 then (.ok (),(locals,{state with ex:=state.ex.run trace}))
 else (.error .timeout,(locals,{state with ex:=state.ex.run (trace.take (count+min (oldLength-count) (fuel-3)))}))
end Solidity.Lowering.StorageOps.SourceStorageCopyPhases
```

The prior subtotal was fourteen pending adapters; this statement makes fifteen.
No `all_fuel` theorem is registered or claimed proved.

## C169: byte capture-to-prepared-copy adapter

Module: `Solidity.Lowering.StorageOps.SourceByteStorageCapture` (not created).
Lemma: `prepared_copy`.
Why routine: unfold actual storRef capture once, use checked `load_bytes`
with OLD header/read premises, then `store_prepared`; rewrite list length.
The operation producers and their soundness proofs are already checked. No
new assumption about emitted target code or desired preservation is permitted.
This statement is type-validated only; no theorem/stub is registered.

```lean
theorem prepared_copy :
∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (_writable : frame.static=false)
 (src dst : Solidity.Source.SPath) (_different : src≠dst)
 (count oldLength padding : Nat) (payload : Nat → UInt8)
 (typed : ∀ j, (.fixedBytes 1 (by decide) : Solidity.Source.STy)=E.cellTy (dst.go (.index j)))
 (headerTyped : (.int Solidity.Source.IntTy.u256 : Solidity.Source.STy)=E.cellTy dst)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_sourceHeader : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame src).run (locals,state)=(.ok count,(locals,state)))
 (_reads : ∀ j<count,(Solidity.Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index j)) (.fixedBytes 1 (by decide))).run (locals,state)=
   (.ok (Solidity.Source.Val.fixedBytes (n:=1) (h:=by decide) [payload j] rfl),(locals,state)))
 (_targetHeader : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame dst).run (locals,state)=(.ok oldLength,(locals,state))),
 let bs := (List.range' 0 count).map payload
 (Solidity.Source.storeVal (E:=E) (Γ:=Γ) frame (count+padding+3) (.bytes .storage) dst
   (Solidity.Source.Val.storRef (τ:=.bytes .storage) rfl src)).run (locals,state)=
 (if oldLength-count≤count+padding then .ok () else .error .timeout,
  (locals,{state with ex:=state.ex.run (Solidity.Lowering.StorageOps.SourceByteStoragePrepared.phaseLog frame dst typed headerTyped bs oldLength padding)}))
```

This adds one routine adapter to the prior fifteen: sixteen remain pending.
The statement does not discharge generic storRef composition.

## C170: byte-capture barrier adapters

Module: `Solidity.Lowering.StorageOps.SourceByteStorageBarrier`.
Lemmas: `memory_timeout`, `copy_timeout`.
Why routine: unfold the existing loadMem/header bind once and apply the checked
`load_timeout`; unfold the distinct-path storRef bind once and apply that
memory adapter. No writable/destination/header/type hypothesis may be added.
The OLD valid-source read premises are material; malformed sources can fail
earlier. These proposition types are checked only, not proved or registered.

```lean
theorem memory_timeout :
∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (path : Solidity.Source.SPath)
 (fuel count : Nat) (payload : Nat → UInt8)
 (initial : Solidity.Source.Locals E.layout Γ × Solidity.Source.St E)
 (_short : fuel≤count+1)
 (_header : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame path).run initial=(.ok count,initial))
 (_reads : ∀ j<count,(Solidity.Source.readAt (E:=E) (Γ:=Γ) frame (path.go (.index j)) (.fixedBytes 1 (by decide))).run initial=
  (.ok (Solidity.Source.Val.fixedBytes (n:=1) (h:=by decide) [payload j] rfl),initial)),
 (Solidity.Source.loadMem (E:=E) (Γ:=Γ) frame fuel (.bytes .memory) path).run initial=(.error .timeout,initial)

theorem copy_timeout :
∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (src dst : Solidity.Source.SPath)
 (fuel count : Nat) (payload : Nat → UInt8)
 (initial : Solidity.Source.Locals E.layout Γ × Solidity.Source.St E)
 (_different : src≠dst) (_short : fuel≤count+2)
 (_header : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame src).run initial=(.ok count,initial))
 (_reads : ∀ j<count,(Solidity.Source.readAt (E:=E) (Γ:=Γ) frame (src.go (.index j)) (.fixedBytes 1 (by decide))).run initial=
  (.ok (Solidity.Source.Val.fixedBytes (n:=1) (h:=by decide) [payload j] rfl),initial)),
 (Solidity.Source.storeVal (E:=E) (Γ:=Γ) frame fuel (.bytes .storage) dst
   (Solidity.Source.Val.storRef (τ:=.bytes .storage) rfl src)).run initial=(.error .timeout,initial)
```

Two adapters added to the prior sixteen: eighteen remain pending.

## C171: nested allocating-capture wrapper

Module: `Solidity.Lowering.StorageOps.SourceNestedByteCapture`.
Lemma: `copy_timeout_prefix`.
Why routine: unfold actual storRef/loadMem outer capture, use OLD outer header,
then apply checked `timeout_prefix` at start0. The existing producer proves the
allocation prefix; do not assume full-state preservation or erase its heap.
No destination or writable-frame premise is required. Proposition type only;
no theorem/stub registered.

```lean
theorem copy_timeout_prefix :
∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (src dst : Solidity.Source.SPath) (_different : src≠dst)
 (count : Nat) (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_outerHeader : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame src).run (locals,state)=(.ok (count+1),(locals,state)))
 (_headers : ∀ j<count+1,(Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (src.go (.index j))).run (locals,state)=(.ok 0,(locals,state))),
 (Solidity.Source.storeVal (E:=E) (Γ:=Γ) frame (count+5) (.array .storage (.bytes .storage) none) dst
   (Solidity.Source.Val.storRef (τ:=.array .storage (.bytes .storage) none) rfl src)).run (locals,state)=
 (.error .timeout,(locals,Nat.repeatTR Solidity.Lowering.StorageOps.SourceNestedByteCapture.captureStep count state))
```

One adapter added to the prior eighteen: nineteen remain pending.

## C172: nonempty nested capture outer wrapper

Module: `Solidity.Lowering.StorageOps.SourceNestedByteValues`.
Lemma: `copy_timeout_prefix`.
Why routine: unfold the two existing outer storRef/loadMem binds and apply
checked `timeout_prefix` at start0. Keep the exact heap payloads and order;
add no writable/destination premise. Common inner length is a parameter of
this component theorem, not an admitted-source restriction. Proposition type
only; no compiled theorem, assumption or stub.

```lean
theorem copy_timeout_prefix :
∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (src dst : Solidity.Source.SPath) (_different : src≠dst)
 (count length : Nat) (payload : Nat → Nat → UInt8)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_outerHeader : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame src).run (locals,state)=(.ok (count+1),(locals,state)))
 (_headers : ∀ j<count+1,(Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (src.go (.index j))).run (locals,state)=(.ok length,(locals,state)))
 (_reads : ∀ j<count+1,∀ k<length,(Solidity.Source.readAt (E:=E) (Γ:=Γ) frame ((src.go (.index j)).go (.index k)) (.fixedBytes 1 (by decide))).run (locals,state)=
  (.ok (Solidity.Source.Val.fixedBytes (n:=1) (h:=by decide) [payload j k] rfl),(locals,state))),
 (Solidity.Source.storeVal (E:=E) (Γ:=Γ) frame (count+length+5) (.array .storage (.bytes .storage) none) dst
  (Solidity.Source.Val.storRef (τ:=.array .storage (.bytes .storage) none) rfl src)).run (locals,state)=
 (.error .timeout,(locals,(List.range' 0 count).foldl
  (Solidity.Lowering.StorageOps.SourceNestedByteValues.allocateAt length payload) state))
```

One adapter added to prior nineteen: twenty remain pending.

## C173: varying-length outer capture wrapper

Module: `Solidity.Lowering.StorageOps.SourceVaryingByteCapture`.
Lemma: `copy_timeout_prefix`.
Why routine: unfold the existing outer capture binds and apply the checked
runtime prefix theorem at start0. Preserve both fuel inequalities and the exact
heap payloads; add no destination/writable premise. This is a type-checked
proposition only, not a compiled theorem or assumption.

```lean
theorem copy_timeout_prefix :
∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (src dst : Solidity.Source.SPath) (_different : src≠dst)
 (count budget : Nat) (length : Nat → Nat) (payload : Nat → Nat → UInt8)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_enough : ∀ j<count,length j<count+budget-j) (_short : budget≤length count)
 (_outerHeader : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame src).run (locals,state)=(.ok (count+1),(locals,state)))
 (_headers : ∀ j<count+1,(Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (src.go (.index j))).run (locals,state)=
  (.ok (length j),(locals,state)))
 (_reads : ∀ j<count+1,∀ k<length j,(Solidity.Source.readAt (E:=E) (Γ:=Γ) frame ((src.go (.index j)).go (.index k)) (.fixedBytes 1 (by decide))).run (locals,state)=
  (.ok (Solidity.Source.Val.fixedBytes (n:=1) (h:=by decide) [payload j k] rfl),(locals,state))),
 (Solidity.Source.storeVal (E:=E) (Γ:=Γ) frame (count+budget+5) (.array .storage (.bytes .storage) none) dst
  (Solidity.Source.Val.storRef (τ:=.array .storage (.bytes .storage) none) rfl src)).run (locals,state)=
 (.error .timeout,(locals,(List.range' 0 count).foldl
  (fun state j=>Solidity.Lowering.StorageOps.SourceNestedByteValues.allocateAt (length j) payload state j) state))
```

One added to prior twenty: twenty-one adapters remain pending.

## C174: successful outer snapshot wrapper

Module: `Solidity.Lowering.StorageOps.SourceByteCaptureSuccess`.
Lemma: `snapshot_all`.
Why routine: unfold one actual array loadMem/header bind and apply checked
`capture_all` at start0, preserving both returned typed references and heap
payloads. Proposition type only; no theorem, assumption or stub registered.

```lean
theorem snapshot_all :
∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (path : Solidity.Source.SPath) (count budget : Nat)
 (length : Nat → Nat) (payload : Nat → Nat → UInt8)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_enough : ∀ j<count,length j<count+budget-j)
 (_outerHeader : (Solidity.Source.readLen (E:=E) (Γ:=Γ) frame path).run (locals,state)=(.ok count,(locals,state)))
 (_headers : ∀ j<count,(Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (path.go (.index j))).run (locals,state)=
  (.ok (length j),(locals,state)))
 (_reads : ∀ j<count,∀ k<length j,(Solidity.Source.readAt (E:=E) (Γ:=Γ) frame ((path.go (.index j)).go (.index k)) (.fixedBytes 1 (by decide))).run (locals,state)=
  (.ok (Solidity.Source.Val.fixedBytes (n:=1) (h:=by decide) [payload j k] rfl),(locals,state))),
 (Solidity.Source.loadMem (E:=E) (Γ:=Γ) frame (count+budget+4) (.array .memory (.bytes .memory) none) path).run (locals,state)=
 (.ok (Solidity.Source.Data.array (l:=.memory) (τ:=.bytes .memory) (n:=none) count (fun _ h=>nomatch h)
  (fun j : Fin count=>Solidity.Source.Data.val (Solidity.Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl (state.heap.next+j.val)))),
  (locals,(List.range' 0 count).foldl
  (fun state j=>Solidity.Lowering.StorageOps.SourceNestedByteValues.allocateAt (length j) payload state j) state))
```

One added to prior twenty-one: twenty-two adapters remain pending.

## C179: OLD-header commit wrapper

Module: `Solidity.Lowering.StorageOps.SourceByteCommitFrames`.
Lemma: `commit_from_old_headers`.
Why routine: apply the already checked `SourceCapturedByteCommit.commit_all`;
for each header premise apply `prefix_header`, then rewrite its OLD read with
`headersOld`. Keep all existing captured-object/type/fuel/cleanup premises.
Place the wrapper in this module to avoid an import cycle. The proposition below
is type-checked only; it is no compiled theorem, axiom, assumption or instance.

```lean
theorem commit_from_old_headers : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (_writable : frame.static=false) (dst : Solidity.Source.SPath)
 (typed : ∀ i j, (.fixedBytes 1 (by decide) : Solidity.Source.STy)=E.cellTy ((dst.go (.index i)).go (.index j)))
 (headerTyped : ∀ i, (.int Solidity.Source.IntTy.u256 : Solidity.Source.STy)=E.cellTy (dst.go (.index i)))
 (payload : Nat → List UInt8) (oldLength : Nat → Nat) (start count budget first : Nat)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_captured : ∀ j<count,state.heap.get (first+j)=some ⟨.bytes .memory,Solidity.Source.Data.bytes (payload (start+j))⟩)
 (_enough : ∀ j<count,(payload (start+j)).length≤count+budget-j)
 (_cleanup : ∀ j<count,oldLength (start+j)-(payload (start+j)).length≤count+budget-j)
 (_headersOld : ∀ j<count,(Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (dst.go (.index (start+j)))).run
 (locals,state)=(.ok (oldLength (start+j)),(locals,state))),
 (Solidity.Source.storeElems (E:=E) (Γ:=Γ) frame (count+budget+5) (.bytes .storage) dst start count
  (fun j : Fin count=>Solidity.Source.Data.val (Solidity.Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl (first+j.val)))).run (locals,state)=
 (.ok (),(locals,{state with ex:=state.ex.run (Solidity.Lowering.StorageOps.SourceCapturedByteCommit.plans frame dst typed headerTyped payload oldLength budget start count).flatten}))
```

One routine adapter added; twenty-three remain pending.

## C180: explicit rollback of the failed commit phase

Module: `Solidity.Lowering.StorageOps.SourceCapturedByteTimeout`.
Lemma: `rollback_cleanup_timeout`.
Why routine: rewrite the checked `cleanup_timeout` outcome, expand the existing
`rollbackTo` and apply `ExecState.journal_run`/`undoN_run`. Commit changes only
`ex`, so heap equality follows from unchanged heap, not from restoration of the
mark's heap field. This concerns the pre-COMMIT state with snapshots already
captured, not a pre-capture caller state or physical target rollback.
Type-checked proposition only; no compiled theorem, axiom or instance.

```lean
theorem rollback_cleanup_timeout : ∀ {E : Solidity.Source.Env} {Γ : Solidity.Source.RCtx}
 (frame : Solidity.Source.Fr) (_writable : frame.static=false) (dst : Solidity.Source.SPath)
 (typed : ∀ i j, (.fixedBytes 1 (by decide) : Solidity.Source.STy)=E.cellTy ((dst.go (.index i)).go (.index j)))
 (headerTyped : ∀ i, (.int Solidity.Source.IntTy.u256 : Solidity.Source.STy)=E.cellTy (dst.go (.index i)))
 (payload : Nat → List UInt8) (oldLength : Nat → Nat) (start count budget first : Nat)
 (locals : Solidity.Source.Locals E.layout Γ) (state : Solidity.Source.St E)
 (_captured : ∀ j<count+1,state.heap.get (first+j)=some ⟨.bytes .memory,Solidity.Source.Data.bytes (payload (start+j))⟩)
 (_enough : ∀ j<count+1,(payload (start+j)).length≤count+1+budget-j)
 (_cleanup : ∀ j<count,oldLength (start+j)-(payload (start+j)).length≤count+1+budget-j)
 (_short : budget+1<oldLength (start+count)-(payload (start+count)).length)
 (_headers : ∀ j<count+1,(Solidity.Source.readLen (E:=E) (Γ:=Γ) frame (dst.go (.index (start+j)))).run (locals,state)=
  (.ok (oldLength (start+j)),(locals,state))),
 let outcome :=  (Solidity.Source.storeElems (E:=E) (Γ:=Γ) frame (count+budget+6) (.bytes .storage) dst start (count+1)
  (fun j : Fin (count+1)=>Solidity.Source.Data.val (Solidity.Source.Val.memRef (D:=E.layout) (τ:=.bytes .memory) rfl (first+j.val)))).run (locals,state)
 (Solidity.Source.rollbackTo (state.ex.journal.length,state.logs.length,state.heap) : Solidity.Source.EM E Γ Unit).run outcome.2=
 (.ok (),(locals,state))
```

One routine adapter added; twenty-four remain pending.
