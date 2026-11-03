# P1 runtime frames: foundation, frozen interfaces v1–v3 and producers

This is a partial checkpoint of the V12 runtime-frame producer (P1, roadmap
items G37–G39). It is not a general runtime-call or source-to-EVM theorem.
All modules are in `Solidity/Backend/InternalFlow/` and use the existing
intrinsic syntax, states, `Evm.run` and the published `Evm.Memory`
certificates. They add no evaluator, AST or world model. Every theorem is
proved, with no `sorry`, axiom or heartbeat change.

## Foundation modules

| Module | Content |
|---|---|
| `RuntimeFrameSemantics` | Replaces `callRec f d args ret thunk` by its finite body `thunk ()`. `statement_run`/`program_run` prove that execution is unchanged, including `recBase` exhaustion. |
| `RuntimeFrameTarget` | Transports published `Calls` certificates along that equation. `callRec_index` compares only the same thunk at two indices. |
| `RuntimeFrameTransport` | Argument evaluation, entry/body extension and result export at the checked target endpoint (`call_return`, `target_return`, `target_recursive_return`). |
| `RuntimeFrameStack` | Word push/pop through a pointer read from target memory (`push_run`, `pop_run`, `push_pop`). Positivity, nonoverlap and no-wrap are explicit premises. |
| `RuntimeFrameSaved` | A frame word written above the caller locals and below the heap preserves the full `StateRepr` (`reserved_write`, `pushed_repr`), and scalar or reference saves read represented caller cells. The `Arena` record packages these bounds but is not used yet. |
| `RuntimeFrameFootprint` | `Footprint.Words`: an interval of words left unchanged by actual allocation, private rebinding and represented array writes. These cover the listed emitter leaves only, not arbitrary callees. |
| `RuntimeFrameComposition` | `Program`/`Statement` pair an existing checked certificate with a derived scratch-safety proof. The proof is built by constructors (`nil`, `cons`, `block`, `branch`, `assign`, `allocate`, …). The selectors `compileCall` and `compileRecursive` return `Option` certificates and accept only call-free bodies. Public selectors and refusals are unchanged. |
| `RuntimeFrameRestore` | Pops a saved word back into the original caller cell (`run`). `local_repr` keeps `StateRepr` when the consumed word equals the cell's content. Heap contents are not restored. |
| `RuntimeFrameContext` | Captures and restores the whole caller context (`capture_context`, `restore_context`), and composes them with a checked body (`program`). |

## Frozen interface v1

`RuntimeFrameInterfaceV1.lean`, namespace
`Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV1`, is a signature-only
contract for consumers. Signature changes go to a new version.

- `Emission` gives code, fragment, workspace need, local limit, pointer cell
  and two separate budgets: runtime arena words and source heap cost.
- `Entry` is the initial `StateRepr`, the runtime cursor read from the same
  machine, word bounds, header/payload separation and `AllocationInput`.
  `RealizableEntry` asks for at least one such entry.
- `Returned` asks for a successful `Evm.run`, the final `StateRepr`, an
  unchanged evaluation stack, `BaseExtends`, `GrowsAllocator`, the restored
  cursor and the older frame words (`Footprint.Words`).
  `ReturnClaim`/`BareRevertClaim` quantify these over source runs.
  `BareRevertClaim` covers bare `revert` only.
- `PendingCallProducer` and `PendingFixedCallRecProducer` are for ordinary
  calls and a fixed `callRec` thunk. `PendingRecursiveReturns` is for one code
  image over the `recUnroll` family (`RecursiveEmission`, `recursiveSource`,
  `RecursiveReturnCoherence`). `PendingRestoration` holds
  `RestoredRepresentationClaim`, which needs `NoAliasPromotion`.

The `Pending*` structures are unproved premise structures, with no instance.
Consumers take them as parameters.

Known weakness of v1: `RealizableEntry` does not make the return obligations
non-vacuous. `arenaWords` and `heapCost` depend on the caller state, so a plan
can admit (through `Entry.noWrap`) only one caller whose source run fails, and
then `ReturnClaim` and `BareRevertClaim` hold trivially. In
`PendingRecursiveReturns` the entry can be realized only at index 0, where
`recBase` always exhausts. Version 2 below closes this for the return obligation.

## Frozen interface v2: witnessed admission

`RuntimeFrameInterfaceV2.lean`, namespace
`Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV2`, replaces the v1
`Pending*` structures and reuses the v1 `Emission`, `Entry`, `Returned`,
`ReturnClaim`, `BareRevertClaim` and recursive-family definitions unchanged.

- `SuccessfulEntry` asks for an `Entry` and a successful source run for the
  same caller, so `ReturnClaim` must yield `Returned` for at least that caller.
  `RevertingEntry` asks for an `Entry` whose source run is a bare revert.
- `PendingCallProducer` and `PendingFixedCallRecProducer` (at each quotation
  index; `Stmt.run` ignores the index) require a successful entry.
- `PendingRecursiveReturns` requires a successful entry at some index. At
  index 0 the body is `recBase`, so the run never returns `.ok` and cannot
  supply the witness.
- `PendingBareRevertProducer` requires a reverting entry and `BareRevertClaim`.

These are minimum non-vacuity requirements. A plan may still admit only the
witness caller, and only the witness index (not necessarily `recDepth`), so
`ReturnClaim` can be vacuous elsewhere. Only `PendingBareRevertProducer` asks
for a reverting entry: in the other three, `BareRevertClaim` can still hold
vacuously. They do not calibrate the state-indexed budgets or establish
profile coverage. `PendingRestoration` stays in v1.

## Open

- G37.01: no `Pending*` instance yet. General caller save/restore agreement
  and runtime return control are still missing, and the scratch-safe
  selectors do not yet compile bodies that contain calls or loops.
- G37.02: unbounded recursion (running prefix, termination, divergence) is
  not covered. Source `recDepth` is unchanged.
- G38: payload and panic failures, the byte journal and world failure transport.
- G39: transient storage, reset and world composition.
- The P2 static-world premises (readonly-external) stay separate.

## Master integration review

Version 2 was merged from c3765ded: the module only; its controls stay on the
producer branch. Read-only reviews confirmed that each `SuccessfulEntry` or
`RevertingEntry` witness instantiates the matching claim, and found the
remaining weaknesses now listed above.

Version 1 was merged from f4fa6f12: the interface and its import closure only.
The other `RuntimeFrame*` modules (Bytes, CodeEquality, Mutation, Nested,
Result, Reference, ReferenceProgram; Result and Reference were merged later
with v3), the `tests/runtime-frame/` fixtures and
the modules of other lanes on that branch were not merged.

Read-only finder and skeptic reviews found no `sorry`, axiom or heartbeat
change, and no import or layer problem. They found the vacuity weakness above,
which is now documented. They also found overstated descriptions of
`local_repr`, `Arena` and the call selectors, which are now corrected in the
docs and docstrings. Signatures are unchanged.


## Restoration and export components (merged with v3)

- `RuntimeFrameRestoredRepresentation` implements the v1 restoration premise
  from the source-tail equation, reached representation, address extension,
  fragment compatibility and recovered context.
- `RuntimeFrameCapturedProgram` composes capture, checked body and restore,
  deriving full reached representation, stack and allocator transport. A bare
  failure after capture absorbs the following code; no failed-state or
  rollback claim is made.
- `RuntimeFrameResult` and `RuntimeFrameReference` export a primitive result
  or a reached memory reference into old or fresh caller bindings.
  `RuntimeFrameCapturedReference.after_reference` composes capture, body,
  restore and reference export; `older_words` preserves the older runtime
  interval and `then_program` derives the next caller's allocation input.
  Allocator transport is the existing conditional law, not allocator
  ownership.

None of these is general call-return dispatch, uncapped recursion,
full-signature dispatch or byte/world/transient closure.

## Frozen interface v3

`RuntimeFrameInterfaceV3.lean`, namespace
`Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV3`, adds coverage over
an explicit typed input domain. V1 and V2 are unchanged; the module has
signatures and pending duties only.

- `Admission` is a predicate over layout, frame, caller, address map, machine
  and cursor. `approved` and `admitted` are external parameters.
  `AdmissionAgreement approved admitted` is a pointwise equivalence duty. It
  does not authenticate `approved`: taking `approved := admitted` with
  `Iff.rfl` always discharges it, so it carries profile content only once
  `approved` is pinned to the source/resource profile, which no module does
  yet. P8a's frozen interface exists but supplies no `approved` domain.
- `EntryCoverage` requires `Entry` for each exact admitted input;
  `FamilyEntryCoverage` keeps the same index in the domain and `plan.at n`.
- Every structure requires independently quantified admitted success and
  bare-revert witnesses (`SuccessfulEntry`, `RevertingEntry`). Each
  `RevertingEntry` binds the same `L frame caller base machine start` that
  `BareRevertClaim` quantifies over, with the same `b`, `F`, statement and
  plan, so `required_bare_revert` yields a genuine
  `Evm.run plan.code machine = .revert`; this closes the v2 bare-revert
  vacuity for the ordinary call and the fixed thunk (for every `d`).
  `PendingRecursiveReturns` asks only `∃ n` for each witness, possibly at
  different indices, so its return and bare-revert claims can still hold
  vacuously at other indices (index 0 always exhausts).
- A source that never bare-reverts cannot inhabit these dual-outcome
  structures; that is an evidence-class limitation, not a source refusal.
  Panic, payload failures, exhaustion, running prefixes and divergence are
  not covered.

## Producers

- `RuntimeFrameCallAgreement.output_of_call` inverts an actual intrinsic call
  success into the evaluated arguments, entered body frame and exported
  caller result; `none_tail` and `memory_tail` derive caller-environment
  transport.
- `RuntimeFrameNoneProducer`: `plan` emits capture, the checked void call and
  restoration. `returns` and `bare_revert` prove the v1 duties; `make`,
  `make_failure` and `make_fixed` build the v2 `PendingCallProducer`, the
  failure producer and the fixed-thunk producer from the checked program,
  fragment compatibility and real entry witnesses, with no target
  correctness claim as input. `make_fixed` is not an unbounded recursive
  family.
- The v3 value-call producer is `RuntimeFrameV3CallProducer` (see
  [P1-CALL](p1-call-producer.md)).

## Recursive components (no v3 recursive instance)

- `RuntimeFrameV3RecursiveProducer.descent_prefix`: every reached
  `Evm.loopIterN` horizon of the runtime save loop, with one code image;
  caller representation, address map and stack survive and the cursor
  advances by the horizon. Bounds require frame room and no word wrap.
- `RuntimeFrameV3RecursiveUnwind.unwind_nonempty_iter`/`unwind_nonempty_run`:
  termination of the LIFO return loop for every positive frame count, the
  destination ending with the bottom saved word; `recover_clobbered` derives
  the final caller representation from a represented pre-clobber snapshot.
  Heap/world mutation between capture and return is not covered.
- `RuntimeFrameV3RecursiveSource`: an effect-free countdown family built from
  `Stmt.callRec`, `Args`, `CallRet.none` and `recUnroll`. `all_horizons`:
  for every horizon, `count < depth` returns the original parameter-frame
  state, otherwise `.exhausted`; `call_all_horizons` adds evaluated outer
  arguments and caller-environment recovery. `source_coherence` derives
  `InterfaceV1.RecursiveReturnCoherence` for this family from execution.
  Its only revert path (an unset memory reference) has no `StateRepr`, so the
  family cannot supply v3's dual-outcome witnesses.

These are target-side and source-side pieces; connecting recursive source
transitions to the descent and LIFO code, recursive target divergence and
approved-profile provenance remain open (P1 lane).

## Integration record (v3)

Merged from the lane head fd08f0c1: `RuntimeFrameInterfaceV3` and its import
closure (the modules above). Not merged: the `tests/runtime-frame/` clients
and controls, including the v3 interface controls, the void-call and
recursive descent/unwind/countdown clients and their axiom-check scripts, the
other `RuntimeFrame*` modules, staged modules of other lanes, and the lane's
uncommitted recursive-activation work. The lane documents those clients; on
master the producers above are checked, but no client of them except
`RuntimeFrameV3CallProducerControls` is. Read-only finder and skeptic reviews
confirmed the bare-revert closure and the remaining limits above.
