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

- G37.01: `PendingCallProducer` (P1-CALL) and `PendingBareRevertProducer` (P1-REVERT, below) instances exist for fixed fragments; no recursive one. General caller save/restore agreement
  and runtime return control are still missing, and the scratch-safe
  selectors do not yet compile bodies that contain calls or loops.
- G37.02: unbounded recursion (running prefix, termination, divergence) is
  not covered. Source `recDepth` is unchanged.
- G38: payload and panic failures, the byte journal and world failure transport.
- G39: transient storage, reset and world composition.
- The P2 static-world premises (readonly-external) stay separate.

## Master integration review

Version 2 was merged as the module only; its controls stay on the
producer branch. Read-only reviews confirmed that each `SuccessfulEntry` or
`RevertingEntry` witness instantiates the matching claim, and found the
remaining weaknesses now listed above.

Version 1 was merged as the interface and its import closure only.
The other `RuntimeFrame*` modules were merged later (Result and Reference
with v3, the recursive components and call compilers below, and
`RuntimeFrameBytes.lean`); lane fixtures and the modules of other lanes on that
branch are not on master.

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

These are target-side and source-side pieces; the countdown components
below connect them for this family only. General bodies, recursive target
divergence and approved-profile provenance remain open (P1 lane).

## Integration record (v3)

Merged: `RuntimeFrameInterfaceV3` and its import closure (the modules above).
The lane's v3 interface controls, void-call and recursive descent/unwind
clients, their axiom-check scripts and the staged modules of other lanes are
not on master; most other `RuntimeFrame*` modules were merged later (see
below). On master the producers above are checked; their clients are
`RuntimeFrameV3CallProducerControls.lean`, the RefArray, RefTuple,
RefTupleFrame, StructDefault and StructRebind controls of
`RuntimeFrameV3CallProducerRef.lean`, and `RuntimeFrameV3CountdownWitness.lean`.
Read-only finder and skeptic reviews
confirmed the bare-revert closure and the remaining limits above.


## Recursive countdown components and call compilers

All concern the effect-free countdown
family of `RuntimeFrameV3RecursiveSource` and hand-written target images (no
compiler maps source syntax to them); none inhabits `PendingRecursiveReturns`.

- `RuntimeFrameV3RecursiveActivation`: `parameter_projection` rebases the
  caller's represented head into the callee parameter frame;
  `source_activation` matches the scalar update with the native call's
  evaluated arguments; `activation` executes the checked activation code from
  a `StateRepr` and derives the child `StateRepr`, stack, `BaseExtends`, cursor
  and saved words. Room, pointer separation, no-wrap and represented
  counter/reference stay explicit premises. `decrement_failure`: a reverting
  decrement makes the checked code revert; `zero_turn`: the false guard skips
  it. Zero allocation cost does not establish allocator ownership.
- `RuntimeFrameV3RecursiveDescent`: `complete` and `reached_prefix` give the
  descent at every `steps ≤ count` (counter `count - steps`, cursor advanced by
  `2 * steps`), from the reached `StateRepr` and the activation bridge, with no
  target run as premise. It reaches the deepest child, not the caller.
- `RuntimeFrameV3RecursiveHistory`: `activation_exterior` bounds one
  activation's writes to counter, cursor and the new two-word payload;
  `saved_history` derives every saved reference and parent counter in call
  order; `descend_then_pop` restores the nearest parent with
  `Restore.restoreCells`.
- `RuntimeFrameV3PairedUnwind.iter`: given a saved history, the paired return
  loop (reusing `RecursiveUnwind.condition`) restores the original reference
  and counter when `frames > 0`, with protected words, stack and bottom cursor.
- `RuntimeFrameV3RecursiveReturn.initialized_endpoint`: descent, private bottom
  initialization and all-parent unwind end in the original source `StateRepr`.
  Since the source returns its state unchanged, this is an endpoint
  correspondence; no per-parent representation during the unwind is proved.
  Native success holds at every depth above the count; too little unrolling
  stays exhaustion.
- `RuntimeFrameMutation.compileCall`: one call level whose callee body is
  call-free; `RuntimeFrameNested` composes nested calls.
  `Mutation.compileRecursive` and `Nested.compileNormalized` return `none` for
  every elaborated recursive unrolling (`Prog.recBase` is not compiled).
  `RuntimeFrameReferenceProgram` relates a reference-returning program without
  capture/restore; `RuntimeFrameCodeEquality` is a Boolean instruction-list
  equality that rejects `.loop` and has no client yet.

Open: general recursive bodies, signatures and layouts, divergence,
allocator-growth transport, approved-domain provenance (P1-PROFILE) and the
recursive V3 producer. The family has no represented bare-revert case.
The registered RuntimeFrameV3CountdownWitness below now supplies a core-only populated instance of the joint premises. Read-only finder and skeptic reviews found no Lean defect; their
doc and docstring findings are fixed here.

## P1-REVERT: bare-revert producer

`RuntimeFrameV3BareRevertProducer.lean` (from the v13-abi-world lane) builds
`PendingBareRevertProducer` instances of the frozen v3 interface.
`bare_revert` proves the reverting entry for any statement through
`CapturedProgram.bare_revert` and `CallAgreement.singleton_failure`.
`directProducer` and `callProducer` inhabit the structure on one concrete
input (frame 16, the `CompileExamples` fixture), whose `initial` is a real
`StateRepr`; `direct_source`/`call_source` are real out-of-bounds reverts and
`direct_endpoint`/`call_endpoint` a concrete `Evm.run … = .revert`.
`InitialInput` restates the `Entry` resource fields, so `coverage` is a
repackaging; `make` is not applied (the producers are built directly).
Approved-domain provenance stays external (`hprof`), as v3 requires.

## P1-THUNK: fixed-thunk producer

`RuntimeFrameV3FixedThunkProducer.lean` (from the v17-validation-release lane)
inhabits `PendingFixedCallRecProducer` for one bounds-sensitive array-writing
thunk: `producer` takes the approved-domain agreement (`hprof`) as its only
hypothesis; `coverage` is universal; the domain is non-vacuous (`member0`,
`member9`); success is a real index-0 run (`successful`) and the bare revert a
real out-of-bounds run (`reverting`). Holding at every recursion index is
immediate, because `Stmt.callRec` ignores its depth argument. The fixture
(`Witness`) currently lives in the producer module.
### Registered countdown witness

`RuntimeFrameV3CountdownWitness` imports the published nonempty memory fixture
and the recursive return emitter directly; it imports no test module. Actual
source/target prefixes set the counter and runtime header. The proof derives the
full caller representation, actual argument evaluation and callee projection,
then instantiates the checked return endpoint. `returned_caller` reconstructs all
four original caller bindings, including both older aliases, from the same
reached globals/heap and proved old-word agreement. `call_endpoint` couples actual
native call success at every depth greater than two to that executed target and
complete caller representation.

The full ordered stack/memory observation, protected older arena, wrong alias,
wrong cursor and insufficient native horizon controls are checked in-tree. A
builtin axiom guard pins the headline theorem to the standard three axioms.
This witnesses the premises; it does not turn the hand-written image into public
compiler output, provide per-parent unwind representations or instantiate the
recursive V3 producer/profile/growth/divergence obligations. The two prior guard
proofs retain only their successful `simp only` branches, with statements and
runtime behavior unchanged.

### Successful checked prefix followed by bare failure

`RuntimeFrameV3BarePrefix.after_prefix` consumes the published
`RuntimeFrameV3BareRevertProducer.bare_revert` theorem. A checked successful
prefix supplies the actual reached machine and fragment. Summed source allocation
capacity is transported through `GrowsAllocator.nextInput`; the checked footprint
preserves the real runtime cursor. The proof constructs the failure entry at that
same reached state and derives exact combined bare revert. No reached
representation, post-prefix capacity or target simulation is an input.

The populated core client changes the caller scalar from nine to two, with an
explicit checked prefix and owned `Mutation.compileProgram` selector equality,
then executes the
published callee out-of-bounds failure. It pins the complete ordered prefix words,
source sequence and exact halt class, with wrong-scalar and fault controls.
A builtin guard checks the headline theorem's axioms. This is execution transport,
not approved-domain provenance: the producer's `hprof` obligation is unchanged.
No failed output state, rollback, payload bytes or absence of prior effects is
inferred. Published readonly/world-call modules replace the old staged copies;
algebraic journal history still requires its actual execution linkage.

### Published physical memory dependency

The runtime byte-frame consumer imports the published P6 physical memory
modules, including the producer-owned control module. The original byte-image
fit and initial representation premises remain explicit; word-frame capacity
alone does not establish physical byte bounds. Local checkpoint restoration
does not imply world rollback or a general source-to-target call simulation.

### Recursive return allocator ownership

`RuntimeFrameV3AllocatorReturn` derives zero source-allocation transport from
the actual reached representation, cursor-cell equality and unchanged memory
above the frame. Initial live-object bounds and free-tail ownership are retained;
full machine equality and arbitrary-callee heap preservation are not assumed.
Its new callee-only client initializes the heap cursor to 22 beyond both nonempty
objects, proves ownership, and executes the existing two-level return image.
The final cursor, represented heap, protected stack and free tail survive. Wrong
cursor and nonzero free-tail writes reject ownership independently.

The older whole-caller fixture remains unchanged: its cell zero contains a
reference, so its allocator implication is explicitly conditional. Runtime
private-frame writes consume no source heap allocation. This component does not
prove allocating recursion, public recursive compiler admission, profile
provenance, general divergence or a V3 recursive producer.

### Allocator-backed recursive result client

`RuntimeFrameV3RecursiveResult.success` packages actual native countdown body
execution at every sufficient horizon and the same executed return image into
the existing `GrowingResult` relation. It includes reached representation,
unchanged older addresses, protected stack and zero-cost allocator transport
from the inhabited cursor-22 input. `shallow_refused` keeps native depth-two
exhaustion distinct: that source result cannot match either successful or
bare-reverting `GrowingResult`, despite success of the runtime image.

This is the fixed populated body client, not public compiler output, profile
coverage or an inhabitant of the dual-outcome general recursive interface.

### Typed first-parent unwind

`RuntimeFrameV3ParentRestore.restore` derives parent representation from the
reached child representation, typed counter update and actual saved words. It
executes the existing context restore and uses its local/exterior/field laws;
no restored representation or run is supplied as a premise. Generic saved words
remain input evidence, not a claim of arbitrary capture provenance.

The populated client derives its payload and child representation from the same
actual two-level descent and saved history. The first returned parent has
counter one, cursor twelve, old alias sixteen and inhabited allocator ownership
at twenty-two. Wrong parent-counter and alias controls distinguish it from the
outer caller. The corresponding source state is reached by the actual native
activation prefix. This is one parent leaf, not arbitrary unwind horizons,
recursive bodies or a completed general recursive producer.

### Typed running unwind prefixes

`RuntimeFrameV3ParentPrefixes.running_prefix` inducts over the existing target
`loopIterN`. Every reached horizon through the saved frame count has its exact
`sourceAt` parent, representation, stack, cursor, old reference, allocator growth
and exterior memory. Each step derives its execution and propagates the remaining
saved words and bottom marker from the actual context restore. Generic initial
saved words remain premises; no desired per-prefix simulation is assumed.

The populated client derives those words from its actual two-level descent and
inhabited allocator input. At horizons zero, one and two the counter rises from
zero to two as the runtime cursor falls from fourteen to ten. Complete older
object and saved-frame word lists, bottom marker and protected stack are retained;
the wrong next-horizon counter is rejected. Popping every frame is still a running
observation before the final false guard. This is typed countdown target-prefix
transport, not native source-trace correspondence, arbitrary recursive bodies,
divergence or completed V3/profile coverage.

### Stopping guard and completed unwind horizons

`RuntimeFrameV3ParentStop.complete` connects the represented all-frame-pop
running prefix to the actual final false guard. At frame count plus one, and
at every later observation horizon, the result is the same successful machine
with its parent representation, stack, cursor, old reference, allocator growth
and heap exterior. It consumes the existing loop iterator and public stopped
horizon law, not a new evaluator or assumed termination certificate.

The populated client composes real runtime-header initialization, descent and
unwind, retaining all prior heap and saved-word vectors and allocator ownership.
It rejects stopping before the last guard, revert and fault. An empty-history
client stops immediately without a pop and retains the same represented input.
This closes countdown target-unwind termination/stability, not native
source-trace equivalence, arbitrary recursive bodies, public compiler admission,
approved-profile provenance or a general V3 recursive producer.

### Native child returns and represented parent poststates

`RuntimeFrameV3NativeParents.clause` derives the actual positive guard, typed
argument evaluation, child-body execution and caller restoration for the indexed
parent family at every native horizon. The caller keeps counter `n+1`; a
same-typed child-counter export is rejected. Insufficient horizons remain
exhaustion, distinct from bare revert.

The populated client links these genuine native poststates to the same
represented target unwind parents one and two, retaining real allocator
ownership and complete ordered observations. This is poststate linkage: it does
not show that target execution beginning at each native caller simulates the
entire child-call trace, nor produce a general `GrowingResult`, recursive
compiler, approved profile or V3 producer. Native source execution and target
parent representation are both proved; the complete entry/trace bridge remains
an obligation.
