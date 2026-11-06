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

### Checked bounds-probe leaf

`RuntimeFrameV3ArrayProbe` consumes the published value compiler for an array
read indexed by the counter decrement. Its selector equation retains the actual
compiler link. Successful evaluation pushes the represented source word; the
wrong-read control distinguishes nine from seven before discarding it. The
checked probe followed by a pop returns the exact original machine. Actual bare
source failure yields target revert and absorbs the pop and any continuation.

Both populated inputs have genuine representation and allocator ownership: the
counter-two input reads index one, while counter three reads out of bounds.
Exhaustion is rejected as a classification of that read failure. This is a
bounds-probe building block; it does not yet embed the probe into recursive
execution or supply a recursive V3 producer, failed output state, rollback,
payload bytes or world correspondence. Published P1 modules are used directly;
omitted development controls remain local without replacing reviewed producers.

### Scoped probes in the recursive countdown

`RuntimeFrameV3GuardedRecursion` places the checked bounds read in an actual
scoped scalar declaration before the native recursive call. Successful evaluation
drops that local; an actual read failure propagates bare revert. Depth zero still
exhausts. The source child-call equations preserve the exact dependent caller
context instead of replacing recursion with a separate evaluator.

`failure_pair` couples a positive counter's actual source read failure to the
initialized target image, given reached representation and valid header bounds.
The populated client proves success for counter two at every sufficient source
quotation depth and failure for counter three at every positive depth, using the
same target code. Success retains both array objects, their ordered contents,
caller reference, protected stack, saved parent cells and allocator cursor. Its
complete sixteen-word observation is derived from actual activation and unwind
execution. A successful read with insufficient unrolling still exhausts; the
negative control rejects matching that result to the successful target image.

This is a witnessed family, not a `PendingRecursiveReturns` inhabitant. The target
image is an owned composition of checked value code and existing activation and
unwind code, not public recursive compiler output. Universal admitted callers,
profile provenance, recursive compiler admission and termination/divergence
correspondence remain open. No failed output state, rollback, payload, gas or
world correspondence follows from the revert result.

### Guarded arbitrary-counter prefixes and returns

`RuntimeFrameV3GuardedPrefixes` generalizes the scoped-probe consumer to an
arbitrary counter. `ReadDomain` states only the actual source scalar reads at
each positive lower counter on the unchanged heap. It contains no recursive
execution, target result or preservation equation. `all_horizons` derives the
exact successful-return versus exhaustion classification for every intrinsic
unrolling depth. The populated client discharges both reads of its retained
`[7,9]` array; a count-three input fails the domain rather than being silently
admitted. This domain is a local success condition, not an approved profile.

`reached_prefix` derives guarded and unprobed target execution at the same reached
machine for every horizon up to the counter. It retains the actual next typed
counter/reference, `StateRepr`, stack, `BaseExtends`, zero allocator growth and
saved-context cursor, under the existing physical frame and word-fit bounds.
The cursor counts captured contexts, not heap allocation. `success_endpoint`
uses the actual terminal guard and shares the existing unwind only after proving
that both images reached the same machine. Its final representation, low and
high memory frame, stack, pointer and saved-parent payload follow from execution.

The populated client instantiates zero/one/two running horizons and the returning
endpoint from its real representation and capacity. Cursor fourteen versus
twelve and stack seventy-seven versus eighty-eight are distinguished at the
same two-turn prefix; shallow native unrolling still exhausts. The earlier
complete sixteen-word observation remains unchanged. General recursive compiler
admission, approved-domain provenance, a `PendingRecursiveReturns` inhabitant,
divergence and byte/journal/transient/world composition remain open. The target
image remains the owned checked-code composition, not public recursive output.

### Guarded calls and complete caller tails

`RuntimeFrameV3GuardedCaller.call_all_horizons` transports the guarded body through
actual native argument evaluation, entry and return for an arbitrary typed caller
context. Sufficient source unrolling returns the complete original caller;
insufficient unrolling remains exhausted. `call_read_failure` separately
propagates an actual entered-frame read failure as bare revert.

The target `endpoint` handles countdown parameters followed by an arbitrary
caller tail. It projects the initial parameter representation, consumes the
guarded endpoint, then reconstructs the full caller representation from actual
low-memory equality and reached heap/global fields. Every caller cell is below
the derived frame bound. Tail alias flags and fragile evidence come from the
original caller representation with unchanged source state; no liveness
promotion or arbitrary-callee heap preservation is assumed.

The populated client executes its header write before deriving the represented
input. Its returning image preserves the complete legacy fifteen-word snapshot,
protected stack and bottom word, including both older aliases, the distinct
array object, scalar and physical parent cells. Wrong same-typed alias, lost
distinct object and wrong scalar controls follow from the same endpoint. The
bad caller has an actual representation and source/target bare-revert proofs;
fault and shallow-unrolling success are rejected separately. No old fixture or
expected observation is changed.

This base-zero caller stores a reference in word zero, so it does not witness
allocator ownership or `AllocationInput`. The target layout remains parameters
plus a tail, and the image remains owned checked-code composition rather than
public recursive compiler output. General layouts, mutating recursive callees,
approved-domain provenance, V3 producer coverage, divergence, failed-state
rollback and byte/journal/transient/world transport remain open.

### Protected caller tails during descent

`RuntimeFrameV3CallerPrefixes.history` extends saved-parent history to every
running prefix, including prefixes shorter than the counter. Actual activation
execution derives both the ordered payload and the exterior memory frame. The
guarded endpoint supplies the matching unprobed prefix, so no history or
preservation oracle is added.

`endpoint` reconstructs the represented active-parameter/protected-tail view
for countdown parameters followed by an arbitrary caller tail. Its counter is
the active child's counter; this is not a claim that descent mutates the
suspended native caller. The original tail environment and all lower caller
cells remain intact. A valid template scalar assignment is used only in the
proof; the actual counter word and preserved memory are derived from execution.
Heap/global representation and existing alias flags are retained without
promotion. Actual read validity and physical capacity remain premises.

The populated client proves complete ordered snapshots at horizons zero, one
and two, including both aliases, distinct array, old contents, scalar, protected
stack, header and saved parent cells. It then proves the third false guard
stops at that same zero-counter machine and every later horizon remains stopped.
Wrong cursor and alias controls follow from the same reached prefix. A separate
negative rejects representing the original count-two caller at the count-one
prefix, making the distinction between active and suspended frames explicit.

These are running descent frames, not completed returns, a new source trace or
general recursive compiler/V3/profile coverage. The legacy caller still has a
reference at word zero and supplies no allocator-ownership witness. No general
mutating-callee, divergence, byte/journal or transient/world result is inferred.

### Deriving the read domain from the selected heap object

`RuntimeFrameV3HeapDomain` consumes the published typed
`Heap.readAddr_index_isSome` law. Actual alias resolution and counter decrement
connect the guarded read to that address. `success_iff` and `failure_iff` give
the exact in-bounds successful read and out-of-bounds bare revert.
`domain_of_length` derives every required lower-counter read from the selected
object's length. `domain_iff` proves the converse for a genuine uint counter;
its word bound is required to avoid impossible-index vacuity.

The populated client obtains the domain from the `[7,9]` object's length two
rather than supplying individual successful reads. The distinct `[4]` object
and count-three controls reject the wrong local success bounds. This is not
compiler refusal or an approved-profile restriction: the out-of-bounds client
has actual native and checked target bare-revert proofs derived from the same
heap bound. Exhaustion remains a separate class.

The returning native-call horizon theorem and real represented target prefixes
consume the derived domain. New prefix machines are identified with the prior
ones by their actual executions of the same instructions, retaining complete
zero/one/two-horizon ordered snapshots without replaying full traces.

This local heap condition is not source/resource approved-domain provenance.
General recursive compiler admission, the V3 recursive producer, mutating
recursive callees, divergence and byte/journal/transient/world transport remain
open. Legacy whole-caller fixtures still do not establish allocator ownership.

### Read transport through actual allocation

`RuntimeFrameV3DomainTransport` consumes `Heap.Keeps.readAddr` to transport
the exact scalar probe value through a dependent heap extension and
`Heap.Keeps.len` to transport the local read domain. `allocation_domain`
discharges that heap premise with the published allocation law. This is not
an assumption that arbitrary mutating callees preserve old objects.

The populated client executes a scoped fresh `bool[3]` allocation and then
the scoped probe. Actual declaration correctness supplies the reached
representation and allocator cursor twenty-six from the genuine cursor
twenty-two input. Scope exit drops the private source binding while retaining
the grown heap and its physical pointer at cell four. The old reference is
weakened through the actual extension, still reads nine, and remains distinct
from the fresh object. Complete source/target execution and ordered observations
include both older arrays, fresh default values, stack and reserved frame words.
The target is checked-snippet composition, not a public compiler-selection
claim for this whole finite program or the recursive family. Its probe reads
and pops rather than materializing the dead private scalar slot. The actual
`growing_endpoint` records four reached cells, the extended map and represented
result for that same code and input.

A separate actual write through the retained old alias changes the probe from
nine to ninety-nine. Read-on-write correctness supplies the changed source and
target observations. The read domain remains valid because length is unchanged,
but `mutation_not_keeps` rejects heap-content preservation for that write. Thus
read existence is not confused with exact value preservation; `withinM` and
other mutability guards remain unchanged.

This prepares allocation-aware recursive clients. It does not yet place the
allocation inside every recursive activation, provide a general V3 producer,
approved-profile provenance, arbitrary mutation simulation or world transport.

### Allocating recursive activation and witnessed return

`RuntimeFrameV3AllocatingActivation` defines an actual intrinsic recursive
family: a positive counter selects a scoped `bool[3]` allocation, the scoped
probe, and `callRec` with the decremented counter and weakened old reference.
`source_positive` exposes the actual child call with the allocation extension
composed into its output at every quotation depth. The false guard skips the
allocation and probe; depth-zero exhaustion remains unchanged.

The generic `activation` theorem derives allocation, exact checked probe,
capture, evaluated native arguments and `CallRet.enterT` child representation
from initial representation, genuine ownership, read bounds and physical room.
It exports stack preservation, the extended address map, exact growth four,
saved parent words and exterior memory equality. No child run, target run or
reached midpoint is supplied as a simulation premise.

The populated count-one client executes a real allocating `callRec` and returns
the grown heap. Its target enters child zero, stops the loop and executes the
existing paired unwind. The closed `whole` result matches that returned parent
with the source result and growth four. Complete twenty-one-word snapshots
retain old arrays, fresh defaults, private physical cells, stack, frame payload
and allocator cursor. Returned observations are transported from the same
child snapshot using actual unwind preservation. A negative rejects treating
the entered child as the returned parent. Too-shallow source quotation still
exhausts and is explicitly rejected as a matching result.

Generic activation supports arbitrary valid positive counters; the completed
allocating return is presently a count-one witness. General allocating-prefix
induction, arbitrary recursive returns, approved-profile provenance and a V3
recursive producer remain open. The fixed image uses checked snippets, including
the dead-private-scalar read/pop optimization; public recursive compiler
selection, external bytecode/gas and world correspondence are not claimed.


### Allocating source recursion at arbitrary quotation indices

`RuntimeFrameV3AllocatingSource.success` proves the actual intrinsic allocating
countdown succeeds whenever the counter is below the quotation index and the
old array has sufficient elements. It derives exactly one additional heap
object per positive activation, complete caller-environment weakening through
the returned extension, and `Heap.Keeps` for this allocation-and-read-only body.
The proof composes published allocation and native call-export laws; neither a
successful child result nor the preservation conclusion is a premise.

`exhaustion` preserves the actual insufficient-quotation outcome under the same
valid-read bound. `call_success` and `call_exhaustion` consume genuinely evaluated
arguments and transport these results through the complete caller context.
These are source execution laws, not a new recursion admission cutoff.

The populated client executes two allocating recursive activations after a real
assignment prefix. Its result is selected from proved execution. Ordered local
observations retain counter two, two aliases to object zero and a distinct
object-one reference. Both complete older arrays retain their lengths and
contents, and the heap contains four objects. Countercontrols reject a changed
alias, scalar, old element, omitted object growth, and wrong reference bound;
insufficient quotation is exhaustion rather than success or bare revert.
The wrong-reference bound is a failed premise control, not runtime rejection.

No new target endpoint is claimed here. General allocating target prefixes and
per-parent returned representations, fresh-object content snapshots at arbitrary
counts, public recursive compiler selection, approved-domain provenance and the
full V3 producer remain open. The earlier allocating target witness and all its
observations are unchanged.


### Allocating recursive return coherence

`RuntimeFrameResultAgreement` composes successful-output agreement through the
existing `TRes` bind/map and typed `TRun.seq`, `TRun.call` and `TRun.ite`
operators. It introduces no execution semantics. The call consequence retains
the actual evaluated arguments, result-entry heap extension, scope drop and
`CallRet.leaveT` export. Agreement deliberately compares only two successful
outputs: it neither identifies different halt classes nor proves termination.
A control demonstrates that agreeing failed results can still be unequal.

`RuntimeFrameV3AllocatingCoherence.bodies` proves agreement for every pair of
quotation indices of the actual allocating family by induction on its finite
syntax. No read-validity, successful simulation or caller-result premise is
needed. `source_coherence` inhabits the exact frozen
`InterfaceV1.RecursiveReturnCoherence` field for arbitrary typed argument
expressions and complete caller contexts, with the family's no-result return.
The V3 signatures themselves remain unchanged.

The populated two-activation client witnesses this successful-return property.
For every sufficient quotation it returns the same complete dependent `Out`
already obtained from actual execution, preserving all earlier observations.
Wrong same-typed scalar and alias outputs are rejected for every such index.
The witness uses the existing source success theorem and the new coherence
proof, avoiding a new replay of the complete concrete recursive execution.

This closes the allocating family's source-coherence obligation only. General
target allocating prefixes, per-parent returned representations, genuine target
capacity/cost induction, public recursive compiler selection and approved-domain
provenance remain open. The other V3 producer fields and the full assignment
are not discharged by successful source-return agreement.


### Allocating target descent prefixes

`RuntimeFrameV3AllocatingPrefixes.reached` derives every reached running horizon
of the fixed allocating descent image. Its inputs are initial representation,
genuine allocator ownership, counter/reference bindings, an actual old-array
length bound, and frame/heap room for the reached turns. Each induction step
consumes the checked allocating activation, evaluated native arguments and
entry representation; no running endpoint or desired midpoint is an input.

The result includes some active child representation (an existential Source
state fitting the reached machine, not tied to a Source run), exact counter and weakened
old reference, object growth by the horizon, older-object preservation, stack,
address-map extension, allocator growth of four cells per reached turn, actual
reached allocator ownership and runtime cursor. A horizon is an observation
index, not a recursive compiler cutoff. `old_array` derives older primitive
array observations from the same reached heap and address map.

The genuinely owned populated client covers zero, one and two running turns.
Ordered observations pin allocator cursors 22/26/30, reference word 16, active
counters 2/1/0, runtime cursors 10/12/14, stack 77 and both complete older arrays
`[7,9]` and `[4]`. The next false guard stops without a third allocation;
published stopped-horizon stability and loop execution laws give the same
terminal active child. Wrong alias, content, horizon and composed allocation
cost are rejected against these actual endpoints.

This is active-parameter descent, not a returned caller. A control rejects
representing the stopped child as the original parent with counter two.
The theorem does not expose a native partial-call trace, saved-parent payload
history, arbitrary-count fresh-object snapshots, outer caller-tail word
preservation or general allocating unwind/source-return coupling. Those are
remaining runtime-frame obligations. Public recursive compiler selection,
approved-domain provenance, byte/gas/world behavior and the full V3 producer
are not implied. Earlier source and target fixtures remain unchanged.


### Source continuation and allocating descent

`RuntimeFrameV3AllocatingResume.coupled` strengthens the allocating-prefix
construction with a proved `Continuation` equation over the existing source
execution. Executing the residual body at the reached state, then applying
native no-result caller export, equals executing the original body at the
corresponding larger quotation. This is a derived equation, not an evaluator,
partial-trace semantics or an assumed simulation certificate.

`reexport` restores only the typed caller environment through the composed
extension. Every other state field comes from the actual output. The equation
transports errors unchanged through `map` without assigning them a failed
state. Its base case derives environment restoration from actual successful
source execution; its step uses evaluated arguments, native call execution
and dependent extension composition.

`complete` discharges residual source execution with the zero-counter body.
For arbitrary feasible counters it proves the completed source body's heap is
exactly the reached heap used by the terminating target descent loop. The
source has restored caller locals; the target still represents child zero.
They are deliberately not claimed to have the same local environment.

The populated two-turn client proves the completed native caller output equals
the earlier full dependent source output, and returns it at every sufficient
quotation. Target execution determinism transfers the unchanged ordered
prefix snapshots. It does not identify the older prefix theorem's logical
model states: consumers requiring continuation coupling must use the new
coupled witnesses. Shallow quotation remains exhaustion, distinct from bare
revert, and a negative rejects representing the descent machine as the actual
returned parent.

This closes source-continuation/heap coupling for this family. Outer caller-tail transport,
public compiler selection, approved-domain provenance and the remaining V3
producer duties stay open. No target failure-byte, rollback, transient/world,
physical bytecode or gas correspondence follows.


### Allocating descent history and matched return

`RuntimeFrameV3AllocatingHistory.history` derives the saved reference/counter
pairs from actual allocating loop execution. It also proves the protected
positive low-frame exterior needed by paired unwind. Each allocation is above
the caller frame; the private destination and active control cells are excluded.
No general heap-content preservation or alias-liveness premise is introduced.

`RuntimeFrameV3AllocatingReturn.endpoint` connects the completed native source
body to the target descent followed by paired parent restoration. It consumes
the proved continuation, derives saved-parent history, and invokes the checked
parent-prefix and stopping laws. The resulting `StateRepr` represents the
actual completed source output, with exact growth `4 * count`, `BaseExtends`,
unchanged evaluation stack, returned pointer and qualified low-frame exterior.
The instruction image is independent of the counter; feasibility still requires
real read bounds, allocator ownership, frame separation and capacity.

The registered two-turn client checks returned counter two, allocator cursor
thirty, restored pointer ten, stack seventy-seven, ordered saved pairs, both
old arrays and protected caller words. It rejects swapped saved counters,
retaining the descent pointer, a missing allocation cost, and matching a shallow
exhausted source quotation with the successful target. These are kernel source
and abstract-target results, not physical bytecode or gas tests.

The family remains restricted to its typed no-result countdown body. General
caller-tail and argument-entry transport, public recursive compiler selection,
approved-profile provenance and general V3 coverage remain open. No failed
state, whole-memory rollback, failure bytes or world/transient correspondence
is inferred.


### Allocating recursive read failure

`RuntimeFrameV3AllocatingFailure` covers the internal failure path of the same
allocating countdown image. Genuine allocation preserves the evaluated old
array read. At every positive source quotation, a bad index therefore yields
bare revert before the nested call; quotation zero remains exhausted. Native
caller propagation consumes actual evaluated arguments and preserves that halt.

The target proof executes the checked allocation, derives the reached
`StateRepr`, then applies the checked read certificate. Bare revert absorbs the
activation and any suffix, including parent restoration. This failure path
needs allocation room and capacity but no successful restoration arena bounds.
It does not relax any success-path bound or compiler admission.

The populated counter-three client allocates from cursor twenty-two to
twenty-six, preserving the old arrays and stack, then fails against the actual
two-element old array. Its complete pre-failure allocation snapshot includes the
private pointer, fresh length-three Boolean object and old alias identities.
The identical image has the counter-two successful return as a positive control.
Source exhaustion/panic and target fault/success are rejected as wrong outcomes.
The intermediate state comes from successful prefix execution, never from the
error-valued result. No failed frontier, rollback, absence of effects, payload
bytes, world or general V3/profile correspondence follows.


### Caller reconstruction over the reached recursive heap

`RuntimeFrameV3CallerReframe.reframe` rebuilds the caller representation from
its initial local representation, actual address-map extension and preserved
caller cells. Global, heap, struct and reference-field representation come from
the reached callee, so the lemma does not assert old heap contents were kept.
The fragment premise excludes fragile storage aliases; transporting those
requires actual reached liveness evidence and is not covered by this lemma.
This is a local theorem capability, not a change to source admission.

The populated client places a three-local caller at base one, leaving cell zero
for the genuine allocator. It contains scalar two and two aliases to the old
array. Actual evaluated arguments enter the base-two callee; native no-result
export produces the caller state represented at the already checked allocating
return machine. All sufficient source quotations yield this same output and
share the fixed target image. The endpoint retains exact growth eight, stack,
old address extension and the complete prior ordered return snapshot; wrong
alias identity and scalar controls consume that endpoint.

This closes whole-caller representation for this admitted no-result client,
not general argument marshalling, arbitrary contexts or recursive compiler
selection. The older base-zero whole-caller fixture is unchanged and is not
claimed to provide allocator ownership. General V3/profile, fragile liveness,
failure-byte and world/transient obligations remain open.


### Nonidentity scalar argument and stack-held caller save

`RuntimeFrameV3ScalarArgument` supplies a concrete nonidentity entry and return:
the caller scalar is nine, but the evaluated argument is literal two. Entry
loads the old scalar onto the actual target stack, executes the published
literal argument code and stores two into the callee cell. The allocating
recursive endpoint preserves that saved stack word; a final store consumes it
to restore nine. The restore proof uses the actual entry and body stack facts,
not a caller-restoration assumption.

The same native call output is represented at the completed target machine.
Genuine initial ownership and capacity yield cursor twenty-two to thirty,
stack seventy-seven, both caller aliases, old array contents and the ordered
recursive payloads. The new ordered snapshot contains caller scalar nine;
prior snapshots are unchanged. Wrong argument, omitted restoration and retained
save-word controls reject the respective alternate observations. The source
heap-content law applies only to this allocation/read family.

This is a checked concrete entry/body/restore composition. Literal selection
is linked to `compileSimple`; general recursive call compiler selection,
arbitrary argument layouts, fragile aliases, approved-profile/V3 coverage and
world/failure-byte correspondence remain open.


### Distinct memory argument and two-word caller restoration

`RuntimeFrameV3MemoryArgument` passes the older reference at address twenty
while the caller retains a different same-typed reference at sixteen and scalar
nine. Actual entry instructions load the old reference and scalar onto the
stack before selecting the older argument and literal one. `compilePtr` and
`compileSimple` equations pin the argument instruction leaves.

The allocating countdown executes on the selected one-element object and its
checked read yields four. Its real body endpoint preserves the two saved stack
words. Two final stores restore the caller scalar and original reference in
reverse order, with typed weakening and address extension proving identity.
The completed native call output has a full caller representation, growth four,
allocator cursor twenty-six and stack seventy-seven. The ordered snapshot
retains both distinct old arrays and the captured reference/counter pair.

Wrong argument identity, wrong restored reference, lost distinct caller alias,
leftover save words and wrong composed cost are rejected on this same endpoint.
This extends the concrete marshalling clients; it does not supply general
recursive compiler selection, approved-profile/V3 coverage, arbitrary layouts,
fragile storage liveness, or world/failure-byte correspondence.


### General typed argument declarations and checked entry frames

`RuntimeFrameV3ArgumentEntry.source` consumes the published ordered argument
law and recovers the exact native `Out`, including its unchanged heap extension.
`source_failure` preserves the original `THalt`. The proof inverts the actual
run behind the state projection; it does not equate `runC` with native execution
or introduce another argument evaluator.

`endpoint` consumes a genuine checked argument-declaration certificate, initial
representation, actual evaluated arguments, frame need and allocation input.
It derives the reached parameter/caller representation, retained caller frame
under the certificate's restricted fragment, unchanged stack, address extension
and exact producer cost. Retained fragile capabilities are those of the reached
fragment; no old liveness or fragment equality is assumed. `target_revert`
consumes only the producer's exact bare-revert alternative.

The populated successful client uses actual `Calls.compile` selection to place
the older memory reference and literal one at cells four and five. The original
caller references and scalar remain at cells one through three. Both the full
frame and base-four callee projection are proved, with zero allocation cost and
inhabited cursor twenty-two. `prepared` additionally derives scratch safety
from the actual four emitted instructions rather than accepting a safety field.

A second public compilation evaluates a valid memory argument followed by an
out-of-bounds scalar read. Exact source and target bare revert, suffix absorption
and exhaustion/fault negatives are proved; no failed state is reconstructed.
These results provide argument entry, not general recursive call compilation,
approved-profile/V3 coverage or world/failure-byte correspondence.


### Compiled argument entry followed by recursive return

`RuntimeFrameV3ArgumentCall` composes the actual public argument-declaration
code with the allocating recursive image at base four. The source child is
exactly the native no-result call entry and the parameter projection produced
by the checked prefix. Summed input capacity passes through the prefix's real
`GrowsAllocator.nextInput`; the body receives this reached ownership, not an
asserted midpoint. Cursor and bottom words follow the prefix's proved scratch
boundary.

The completed native call output is represented by the completed composed
target run. Caller reconstruction uses the reached caller frame and actual
body exterior. Exact source extension, stack, combined address extension and
allocation growth four are derived. The populated endpoint retains caller
references sixteen/twenty and scalar nine, while private parameter cells hold
twenty/one. The ordered snapshot includes the captured pair and untouched next
payload slots; numeric private allocation cell six is not separately claimed.

Wrong caller/parameter identity, cost eight and omitted allocation are rejected.
A shallow source quotation remains exhausted and cannot match target success.
A bad-argument native call and its publicly compiled failing prefix both retain
bare revert through the same recursive suffix, without a failed state or an
unreachable-body capacity requirement.

`source_indices` classifies every source quotation for this populated call:
quotations above one return the same actual output, while zero and one remain
exhausted. `indexed_endpoint` shares the fixed target image across every
sufficient quotation; it does not match target success with source exhaustion.

Public compiler selection covers the argument prefix, not the entire recursive
call image. General recursive compilation, approved-profile/V3 coverage,
arbitrary caller layouts, fragile liveness and world/failure-byte transport
remain open.


### Zero-counter calls without unreachable allocation ownership

`RuntimeFrameV3AllocatingZero.image` derives exact machine identity for the
same allocating return image when the represented counter is zero and the
runtime cursor equals the unwind bottom. Both guards stop before allocation
or restoration. No allocator owner, positive-body arena capacity or old-content
assumption is needed for this skipped body. `endpoint` retains the exact source
success and zero-cost growing-result statement; its growth implication does not
assert that an owner exists.

`native_call` restores the exact original source state for every positive
quotation and arbitrary caller context. `after_arguments` combines this law
with a real checked argument prefix and its derived scratch certificate. It
produces the completed target run and caller representation under the reached
restricted fragment. No extra fragile-alias exclusion is needed on this
identity-body path. This is the zero-counter case, not general positive-body
frame or liveness transport.

The populated client uses public compilation, two old memory objects and a
caller scalar. Its word zero cannot supply allocator ownership. Actual source
and target execution nevertheless succeed through the zero-cost prefix and
skipped body; the complete ordered snapshot and caller representation are
proved. Positive allocation input is rejected as a premise, not classified as
runtime failure. No output ownership or new approved-profile admission follows.
Quotation zero remains exhausted. General recursive compilation, profile/V3
coverage and world/failure-byte correspondence remain open.

## Allocating argument calls over arbitrary caller contexts

`RuntimeFrameV3AllocatingArguments.after_arguments` composes a real checked
argument-declaration prefix with the existing allocating countdown return
image for any positive feasible counter and any intrinsic caller context.
The summed allocation input supplies the prefix input; actual prefix growth
supplies the reached owner and body capacity. Parameter projection supplies
the body representation. The existing body endpoint supplies execution,
address extension, allocation cost and low-word framing; caller reconstruction
then drops private parameters. The reached caller fragment must contain no
fragile storage aliases. This restriction does not assert that arbitrary
mutation preserves fragile liveness.

Physical caller words are preserved from the reached argument machine, not
assumed equal to arbitrary initial unused cells. The inhabited public-prefix
client is tied by execution uniqueness to the complete earlier argument-call
endpoint, retaining both distinct old objects, aliases, scalar, private saved
cells, protected stack and allocator advance from 22 to 26. Wrong alias,
omitted allocation and wrong-cost controls retain their successful baseline.
`source_fields` proves the exact object-count extension, restored caller
environment and old contents for this particular allocating/read-only source
body; it is not generic heap-content preservation for arbitrary callees.

The zero-counter consumer remains separate and requires no unreachable body
allocation owner. Neither theorem establishes public recursive compilation,
source-approved-domain provenance, full V3 admission, failure rollback or
world correspondence. The existing frozen interfaces are unchanged.

## Source quotation coverage for the same allocating image

`RuntimeFrameV3AllocatingQuotations.source_classification` combines actual
native execution, success coherence and exhaustion for the valid-read
countdown domain. It classifies every source quotation: sufficient indices
return the same complete dependent output; shallow indices remain exhausted.
The argument/call endpoint is strengthened with this classification while
retaining its actual public-selected prefix, target image, reached capacity,
caller representation, address extension, allocator growth and saved words.
No source-index search or target admission cutoff is introduced.

The populated client instantiates the generic theorem and uses execution
uniqueness to retain the previous complete target observation vector.
`success_iff` pins the exact sufficient source-index domain. `shallow_mismatch`
records both shallow source exhaustion and success of the unchanged target
image, so this result cannot be read as all-index simulation or a claim that
source exhaustion is target revert. The source run never becomes bare revert
on the stated valid-read domain. Arbitrary recursive compilation,
approved-profile provenance, frozen V3 coverage and world transport remain
open; the frozen signatures and earlier zero/positive observations are unchanged.

## Callee failure after checked arguments and allocation

`RuntimeFrameV3ArgumentCalleeFailure.after_arguments` derives successful
argument entry, full parameter and retained caller representations, and
remaining allocation capacity from the real checked prefix and its summed
input. It then consumes the existing allocating-image failure theorem.
Every positive source quotation propagates exact bare revert, and the target
failure absorbs arbitrary appended instructions. No saved-stack scratch
bounds are needed for the unreachable capture/unwind instructions.

The populated client successfully evaluates its memory argument and counter
3, allocates a three-element private boolean object, then reads index 2 of
the selected one-element old array. The actual prefix-plus-allocation target
run reaches an independently represented machine with cursor 26, complete
old heap/local/alias observations and stack 77. The read then fails. This
successful intermediate is not a failed output state or a rollback theorem.
Quotation zero remains exhausted. A matched counter-1 client succeeds;
wrong-alias and omitted-allocation controls observe the pre-failure machine.

Public compiler selection is established for the argument-declaration
prefix; the recursive body image is the existing owned matched image, not
public general recursive compilation. No panic/payload, byte memory,
transaction/world, caller rollback or absence-of-effects claim follows.
This is retained InternalFlow failure transport, not a replacement for the
separately owned G38 failure-path compiler.

## Uniform allocating-family outcomes

`RuntimeFrameV3AllocatingOutcome.after_arguments` combines the existing zero,
allocating-return and first-read-failure producers for the same countdown
image. Its source-computed `demand` is `4*count` when all descending reads are
in bounds and four when the first read fails after allocation. `requiredDepth`
is `count+1` for return and one for that immediate failure. These are facts
about this family, not replacements for published loop cost or an approved
source/resource profile.

`ReturnRoom` contains physical inequalities, actual control-word equations
and the nonfragile caller restriction needed for returning execution. The
uniform theorem requests it only when reads are in bounds, and its positive
body bounds are conditional on a positive counter. Actual checked argument
execution, reached capacity, representation, allocator growth and exact halt
class still come from the existing producers; no desired execution is a
field of `ReturnRoom`.

Three clients discharge the uniform theorem: the populated allocating return,
the ownerless zero path, and a real failing-read path with deliberately
impossible return-frame bounds. The last still supplies real prefix/body
allocation capacity; it succeeds only in proving bare revert, not a failed
state. Complete previous ordered observations are retained. A wrong full-count
cost control and a zero-quotation mismatch prevent interpreting skipped
return work or source exhaustion as successful frame transport. General
recursive compiler selection, approved-profile provenance, V3 coverage and
world correspondence remain separate obligations.

## Emitted recursive ingress sentinel

`RuntimeFrameV3RecursiveIngress.code` reads the actual runtime cursor and
stores it in a private workspace bottom cell. `entry_prepared` derives the
initialized machine, the same frozen `Entry`, its allocation capacity and
protected runtime words from real execution. With the pointer at `localLimit`
and at least two private workspace cells beyond the caller context, the
bottom cell is `localLimit-1`; no initial bottom-word equation is required.
Representation and zero allocation growth come from the existing bounded
private-write laws, including heap/reference/struct and fragile capabilities.

`after_setup` composes these instructions with the actual allocating descent
and paired unwind. It derives the coupled native body output, target return,
representation, exact allocation growth, restored runtime cursor, ordered
saved parents and preservation of `[lo,start)` from the original machine.
The bottom workspace word changes outside that protected interval; this is
not whole-memory restoration or rollback.

A populated count-two client starts with bottom zero, executes the initializer
to reach the prior checked body input, and returns with cursor 30 and stack 77.
It inhabits the frozen `Returned` relation for that actual `Entry` and retains
the complete previous observation vector. Wrong copy-source and overlapping
caller-cell controls distinguish observation/representation failure from
runtime rejection. The demonstration plan has fixed count-two metadata;
no universal `ReturnClaim`, source-approved-domain agreement, public recursive
compiler selection or general V3 producer is claimed. Frozen signatures remain
unchanged.

## State-budgeted allocating recursive emission

`RuntimeFrameV3AllocatingEmission.family` specializes the initialized
`[uint, uint[] memory]` no-result self-entry family. It has one actual
prologue/descent/unwind code image at every source quotation. The uint counter comes from the typed
caller value's word, and the live old reference comes from reached input
representation. Metadata uses actual source data: returning inputs reserve
`max 3 (2*count)` arena words and consume `4*count` heap cells; a failing first
read reserves only the three Entry control words and consumes four cells.
The nullable fallback of the total metadata function does not admit null
references: existing `StateRepr` still requires initialized live pointers.

`family_returns` and `family_bare_revert` prove the frozen universal obligations
for every actual Entry and quotation. Success establishes read validity from
native source execution; emitted ingress and actual allocating return supply
representation, stack, old-address extension, allocation growth and protected
runtime words. Bare revert is proved separately from the actual first
allocation/read failure. Neither obligation assumes a desired target run.

The same image has real count-two success and count-three revert witnesses.
`Checks.producer` inhabits the frozen V2 recursive producer for this family;
the complete previous target vector is retained through actual execution
uniqueness. `make` assembles a V3 producer only when supplied independent
profile agreement, exact-input coverage and admitted real outcome witnesses.
Those source-domain duties remain open, not defined from the emitter.

These are the frozen success/bare-revert contracts, not all-outcome source
simulation: quotation-zero exhaustion is explicitly unmatched by target
success. The result does not prove general recursive compiler admission,
full-signature dispatch, divergence/payload/world behavior or original-lane
completion. Frozen V1/V2/V3 signatures are unchanged.

## Emission Entry to reached recursive prefixes

`RuntimeFrameV3EmissionPrefixes.running` derives every feasible allocating
descent horizon from the actual state-budgeted emission `Entry`. Read-validity
is an explicit source-data premise and the horizon is bounded by the actual
caller counter, not a compiler admission cutoff. The theorem derives emitted
ingress, reached source/target representation, remaining counter/reference,
exact heap growth and allocator consumption, old-address extension, protected
words and ordered native parent payload. Horizon zero needs no ownership
existence premise. `Heap.Keeps` is proved only for this allocating/read family.

The continuation equation now begins at the native outer call: a quotation
with the reached activations removed executes the residual body on the same
reached source witness, followed by the real caller reexport. Actual source
error classes are preserved; no failed output state is manufactured.
`full_stop` includes the extra false guard and proves stability at every later
target-loop horizon. That is a zero-counter child before unwind, not restored
caller representation.

The populated zero/one/two clients instantiate the actual emission Entry,
retain complete ordered heap/local/control/saved-parent observations and
allocator cursors 22/26/30, and execute the whole descent slice. Only target
machine equality is inferred from deterministic target execution; no source
state equality follows merely from observations. Wrong horizon, alias, saved
order and allocation cost controls preserve their positive baselines. Stopped
descent has pointer 14 and is proved distinct from the fully returned machine
with pointer 10. General recursive compilation, approved-profile provenance,
all-outcome/horizon world correspondence and frozen V3 closure remain open.

`EmissionPrefixes.failing` covers the complementary invalid-read Entry: the
actual first allocating loop turn is bare revert and every later target
horizon retains that exact outcome. Every positive native quotation has the
same bare-revert class. Only the successful ingress machine is exposed;
no failed state is inferred. Its populated client uses the same emission and
real four-cell allocation capacity, without unreachable return-frame payload.

## Emission descent to paired-unwind parent horizons

`RuntimeFrameV3EmissionUnwind.parents` starts from the same actual emission
`Entry` and derives its complete allocating descent before restoring any
requested feasible number of parent frames. The reached zero child, saved
reference/counter pairs and address extension come from that descent.
`ParentPrefixes.running_prefix` then supplies the restored local view's full
`StateRepr`, unchanged stack, zero additional allocation cost and exact frame
pointer. Composed growth retains the original descent cost and reached heap.
The restored source view is `sourceAt` over the actual child; this is not a
native intermediate-return trace or an assumed final source output.

The populated client retains all sixteen ordered heap, alias, local, marker,
private saved-pair and control cells. Allocator cursor 30 stays fixed while the
active counter advances from zero to two and the parent pointer moves from
14 through 12 to 10. Controls distinguish wrong horizon, same-typed alias,
allocation total, saved parent order and premature final pointer. The final
false guard and every later horizon return the same successful machine.
These are kernel source/target-frame consequences for the allocating countdown
family, not general recursive compiler admission, approved-profile provenance,
byte/world failure transport or full frozen-interface completion. Existing
failure classes and all previous observations remain unchanged.

## Scheduled integration review, 2026-11-03

The ce09575c increment adds 18 runtime-frame modules. Independent finder and
skeptic reviews found no semantic defect. Integration fixes move their module-map
rows into the runtime-frame table, record the kernel-checked `coupled` axiom pin,
and reject duplicate, contradictory or prefixed cap receipts. The narrow
AllocatingResume driver checks its 24 exact reports; `scripts/AxiomAudit.lean`
separately audits every imported safe declaration, including all 18 modules.
The integration audit checked 212971 Solidity declarations with zero findings.
The touched build, library build and `run-lean.sh` pass with serial Lean `-j1`
and the frozen 377-taclet rules file. These are bounded runtime-frame results;
all previously stated compiler/profile/world correspondence limits remain.


## Mutating native returns and represented unwind

`RuntimeFrameV3MutatingSource.success` and `call_success` derive genuine native
returns at every sufficient quotation index for the mutating countdown family.
They restore the full caller environment through the actual composed extension,
allocate exactly one object per positive activation, and preserve all older
array lengths. Contents may change. Valid accesses at an insufficient index
produce exhaustion, separately from bare revert. `bodies` and
`source_coherence` compare successful outputs of the actual syntax at any two
indices; they do not equate error classes.

The populated client composes an opaque inner return and its actual outer
native call. Every sufficient quotation returns the same full dependent output.
The caller scalar is two, its two old aliases remain object zero, and the
distinct old reference remains object one. The returned old arrays are
`[1,2]` and `[4]`; both private boolean arrays have length three and six
observed false elements. Wrong caller locals, wrong references and original
heap-content preservation are rejected. The source-construction equality
`root_state` identifies the whole internal body output with the reached
mutating child after parent-local restoration; it is not inferred from
equal target words.

`RuntimeFrameV3MutatingReturn.Checks.growing` couples that actual native body
output to the executed descent plus paired unwind. Saved history comes from
the previous complete snapshot, and the existing restore producer supplies
the same output's full parameter-frame representation. Growth eight, cursor
30, restored counter two, pointer ten, stack and all twenty-five ordered cells
are checked. A wrong cost-four allocator claim is contradicted by the real
cursor; this is a proof control, not runtime rejection of a failed premise.
Successful target execution is distinct from revert and fault. A genuinely
bad write makes the complete image bare revert, absorbing the unwind.

The target image is assembled from checked components. This populated
parameter-frame result is separate from the arbitrary-context source export,
and supplies no public general recursive compiler, approved-domain provenance,
all-counter native target return theorem or byte/world rollback. Frozen
interfaces and every earlier observation remain unchanged.


## Mutating prefixes with native continuations

`RuntimeFrameV3MutatingResume.coupled` strengthens each feasible mutating
descent horizon with an equation over actual residual native execution at
every quotation index. It uses the existing no-result export operator; no
second evaluator or source trace is introduced. Each positive induction step
consumes the real write/allocation/entry certificate on the preceding child.
Lengths and addresses transport without asserting old-content preservation.

`finish` and `complete` discharge the residual zero branch. For every valid
initial counter and actual frame/allocator capacity, the source body returns
the same reached heap with restored caller locals, while the actual descent
loop ends with its represented zero-counter child. The target at this point
is before parent unwind. Source quotation exhaustion is a separate outcome;
the continuation equation assigns no failed state or allocation frontier to
an error result.

The populated zero/one/two-horizon client reuses the complete twenty-one- and
twenty-five-cell snapshots. Whole source-output identity follows from actual
source executions, and `entered_state` recovers the exact earlier zero-child
state using its proved environment and export law. Only machine identities
come from target determinism. The actual caller export retains scalar two
and aliases `0,0,1`; the returned old arrays are `[1,2]` and unrelated `[4]`.
Controls distinguish quotation exhaustion from revert, the first and second
target horizons, missing mutation, and the restored source output from the
still-entered zero-counter target view.

This closes the native continuation/heap link for the specialized mutating
family. Generic saved history and paired target return, general recursive
compiler selection, approved-domain provenance and byte/world correspondence
remain separate obligations. Earlier interfaces, observations and refusals
are unchanged.


## Generic mutating saved history and paired completion

`RuntimeFrameV3MutatingHistory.history` derives every saved parent reference
and counter, the active reference word and the qualified reserved-frame
exterior from actual mutating descent. It consumes the activation's already
proved pre-turn payload/exterior facts directly. Only allocation after the
write uses `Heap.Keeps`; the write transports lengths instead of old contents.

`RuntimeFrameV3MutatingCompletion.endpoint` combines that history with the
actual native continuation and the existing paired restore. For every counter
with valid accesses and the stated real representation, allocator, frame,
capacity and pointer premises, it derives native success, actual image
execution and full representation of the returned output. Stack and old
addresses persist, growth is exactly `4 * count`, the parent pointer returns
to its start, and all saved pairs and qualified exterior words are proved.
`growing_at` uses an actual successful source run and whole-output coherence
to establish the same image at every sufficient quotation index.

The populated two-turn client discharges the generic premises from the same
real prefix and retains the complete twenty-five-cell return snapshot, old
mutation `[1,2]`, unrelated `[4]`, both aliases, private arrays, saved parents,
cursor 30 and restored pointer ten. Source-output identities come from source
execution; target determinism identifies machines only. Cost four, an
unfinished pointer and omitted mutation are rejected with successful baselines.

The zero client executes an actual source and target local assignment after
that populated prefix. The setup's code is linked to the public statement
compiler. Its representation and allocator are derived from that execution,
then the generic endpoint is inhabited at count zero. A separate execution
proof shows the entire same image returns the exact input machine: no
allocation or parent capture occurs, cursor 22 and old data remain. Charging
four cells is refuted using the genuine allocator; this is a proof control,
not runtime rejection of a false capacity premise.

The image is assembled from checked components, not emitted by a public
general recursive compiler. The theorem is for this no-result countdown
family and its parameter frame. Full caller-target export, other recursive
results/control, all-outcome behavior, approved-domain provenance and
byte/world correspondence remain open. Frozen interfaces and previous
observations are unchanged.


### Invalid first write before allocating recursive entry

`MutatingFailure.write_failure` derives out-of-bounds failure from the actual
receiver, index and value evaluation. `source_failure` and `call_failure`
propagate this bare revert through every positive native quotation and actual
evaluated entry arguments. The populated native-call control discharges its
argument premise; depth zero remains exhausted.

`target_suffix` consumes the public-selected write certificate at the reached
`StateRepr`, with its actual static frame need. Its nonallocating input is
derived from that constructor. The failure absorbs the allocating entry and
any following instructions. `target_image` applies the same completed image
as the successful mutating control, including its paired unwind. The bad
input has counter three and a two-element array; the successful counter-two
control retains its existing complete snapshot and growth proof. Neither
allocator ownership nor room for the unreachable private allocation is a
premise of the failure theorem.

This proves a represented callee-image endpoint, not public recursive call
selection or target argument/export compilation. Error outputs provide no
failed state, frontier, rollback, payload or absence-of-effects claim.


### Checked continuation after mutating recursive return

`MutatingContinuation.after_return` attaches a checked `Calls.Program` suffix
to the actual `MutatingCompletion.endpoint`. It derives the reached suffix
allocation input from initial summed capacity, the source-reached suffix cost
bound and the prefix's genuine allocator growth. Both success and bare revert
compose through the existing intrinsic block/program and target append laws.
The real suffix fragment, need, cost and code remain explicit.

`MutatingContinuation.Client` discharges these premises after the populated
two-turn recursive return. A publicly selected suffix writes 37 to element zero
of the restored old parameter alias, then allocates and drops a private boolean
array of length three. Its native output and exact target endpoint have growth
12, cursor 34, stack `[77]`, unchanged scalar two, and distinct old/private
identities. The complete ordered 29-cell snapshot retains earlier private and
saved-parent cells, includes the new object, and keeps sentinel 99. Alias,
scalar, root, omitted-allocation and wrong-cost controls project that endpoint.

The same target image matches every sufficient native quotation; shallow
quotations exhaust and are explicitly rejected by `GrowingResult`. This is a
specialized no-result recursive-image consumer. The old alias is retained by
native return, not produced by `CallRet.mem`. General recursive compiler
selection, approved-profile provenance, target caller argument/export transport
and byte/world correspondence remain open. Earlier observations are unchanged.


### Primitive scalar-result recursion

`ScalarRecursiveSource` uses the existing intrinsic `callRec`, a private uint
result binder and `CallRet.val`. Each true arm calls the next counter value,
receives the child's actual result, then consumes it in checked addition by
one. The zero arm writes zero. `all_horizons` proves that every sufficient
quotation returns the original counter in the result slot, leaving the
counter, reference and other state fields intact. Insufficient quotations
remain exhausted. The word-range bound is intrinsic; no new depth admission
cutoff is introduced.

`call_all_horizons` derives the exact native caller update from actual evaluated
arguments. `source_coherence` proves the frozen successful-output coherence
clause for this family and any compatible typed caller/result binder. It does
not equate errors or assume successful runs. Arithmetic, native return, arm
execution and induction use small separately checked proof boundaries and the
published `runR_eq` and sequence equations; execution semantics are unchanged.

`ScalarRecursiveSource.Controls` has two same-typed caller scalars: result
77 becomes 3 while the protected scalar stays 2. The private result starts at
zero and actually returns three. Ordered aliases remain 0/0/1 and heap values
7/9/4 remain intact. Controls reject the alternate destination, default result
and wrong alias, distinguish shallow exhaustion from revert, and prove actual
argument failure before callee entry at every index.

These are source/kernel results. No target recursive image, physical stack,
public compiler selection, approved-profile provenance, world relation or
`PendingRecursiveReturns` inhabitant is claimed. Existing target observations
and frozen interfaces remain unchanged.


### Pending approved-profile interface

`RuntimeFrameV3ApprovedProfile` is a generated version-one dependency contract.
It reuses `InterfaceV3.AdmissionAgreement` and `FamilyAdmissionAgreement`, and
the published P8 `ProducerAssembly.AdmissionHalf` and `SourceOrigins` types.
The source specification, origins, artifact and `SourceInputs` relation are
external parameters; the record does not choose them from an emitter's
entry predicate, execution or selected whitelist.

`sourceImage` retains checked frontend acceptance, well-formed and in-profile
source origins, allowed environments and admissible resources for the same
supplied artifact. `Pending` and `PendingFamily` expose the remaining source
image and runtime-admission equivalences at one index or every index.
The relation also receives the exact artifact explicitly. There is no
existential artifact replacement, extra failure-free restriction or depth cap.

No instance is supplied. Inhabiting these records alone does not establish
actual-source adequacy of `SourceInputs`, artifact provenance, nonvacuity,
P8 operational realization or full approved-profile coverage. An empty or
emitter-derived relation cannot be cited as original-profile evidence. Those
obligations remain open, as do the concrete runtime and recursive producers.
The existing frozen V3 call/fixed-thunk/recursive contracts are reused unchanged.

### Scalar parent return and populated caller

`RuntimeFrameV3ScalarParentRestore.restore` recovers the saved reference and
counter while retaining the live scalar result. `RuntimeFrameV3ScalarUnwind`
uses the published checked expression compiler to increment that result,
with an explicit no-overflow bound, and derives the reached representation,
stack preservation and zero source-allocation transport.

The registered facts and endpoint modules derive all three saved parent pairs
from actual native descent. The caller client saves its old scalar before
argument setup, returns scalar three through the checked increments, reloads
that saved scalar and reconstructs the whole caller representation. Its
controls couple all successful native quotation indices above three to that
same target endpoint and derive the complete ordered caller, payload and heap
observations by projection. Shallow quotations remain exhausted, distinct
from bare revert.

This is an explicit populated countdown image, not a public general recursive
compiler selection or an approved-domain producer. The concrete destination
shares the private result's physical cell; arbitrary result marshalling remains
open. No failure state, rollback, world correspondence, unconditional fragile
liveness or full runtime-frame completion follows. Frozen interfaces and the
existing source controls are unchanged.

### Scalar unwind horizons

`RuntimeFrameV3ScalarPrefixes.running_prefix` transports the live result,
restored parent locals and actual representation through every running
`Evm.loopIterN` horizon. It consumes the reached representation and saved
payloads, derives each checked scalar parent step and preserves protected
words and zero source-allocation growth. `ScalarStop.complete` executes the
final false guard with the same code image and proves stability at every
later horizon. The horizon is an observation index, not an admission cutoff;
the existing no-wrap and frame premises remain explicit.

The registered client reuses the actual populated native descent and adds
executed bottom-marker initialization. Every running horizon zero through
three and every stopped horizon from four onward is inhabited. Its running
and completed observations use the same final machine, including the entire
ordered twenty-word snapshot, both old object intervals, saved parent pairs,
protected stack, live scalar and both allocation/runtime cursor cells. Real
allocator ownership is derived at every running horizon. Wrong horizon,
scalar, alias, runtime cursor and halted-class controls retain their baselines.
The new bottom marker is an explicit initialization; earlier snapshots are
unchanged.

Intermediate typed `sourceAt` views are not a native partial-return trace.
The client additionally matches the full native scalar-body endpoint to this
one-image target result; general recursive compiler selection, arbitrary
source body transport, admission/profile provenance and a complete frozen V3
producer remain open. No failed state, rollback, world relation or physical
EVM execution is inferred.

### Arbitrary-count scalar family and distinct export

`RuntimeFrameV3ScalarDescent.reached` derives the actual zero child and saved
parent pairs from the initial represented frame, runtime-pointer value and
existing capacity bounds. Bottom initialization executes before descent.
`RuntimeFrameV3ScalarReturn.endpoint` connects this witness to all-parent
unwind and the finished source state for any count satisfying those bounds.
Its runtime image has neither a count nor a quotation-index parameter. The
source equation explicitly retains exhaustion at insufficient quotation
indices; it is not an unconditional source/target result equivalence.

`RuntimeFrameV3ScalarCallReturn.endpoint` starts from the source caller's
representation, evaluates the actual native memory/scalar arguments, enters
the private default result, executes that image and exports through the
existing checked result-copy law. The private slot is physically distinct
from the destination, with a separate proof of that distinction. The caller
destination is also the input counter, so its final source update is
value-preserving; this is not a changed-value destination client. Stack,
reference identity, zero source-allocation growth, runtime cursor and the
complete captured history are derived.

The registered controls discharge every premise for counts zero through
three using real initial allocator ownership and populated heap objects. The
same fixed image yields complete ordered twenty-word snapshots, including
active and inactive parent payload cells. Alias, private-result, allocator
and runtime cursor, source-exhaustion and target halt controls retain their
positive baselines. Older source, frame and horizon snapshots are unchanged.

This implements the specific typed scalar countdown family. The image is
manually assembled from checked components, not selected by a general public
recursive compiler. General argument/return shapes, original approved-domain
provenance, native partial-return traces and the complete V3 producer remain
open. It supplies no failed state, byte/world rollback or physical EVM test.


### Disjoint scalar caller restoration

`RuntimeFrameSameGlobals.reframe` transports the complete caller representation from a reached frame when source globals and heap are identical and protected local words are preserved. Fragile slots retain their original reached liveness evidence under that equality; this is not preservation under arbitrary heap mutation.

`RuntimeFrameV3DisjointScalarEntry` executes the checked scalar argument and memory-reference entry into separate callee cells. `RuntimeFrameV3DisjointScalarReturn.endpoint` connects that entry, the countdown image and actual private-result export to the original native recursive source call. The caller destination is unrestricted initially. The populated control changes destination cell four from 77 to 3 by copying private cell seven, retaining both aliases, protected scalar two, old heap, allocator and stack in a complete 22-word observation. The actual public scalar-value selector is checked; general recursive compiler selection and approved-profile provenance remain open.

The out-of-bounds argument control proves actual bare-revert prefix absorption, including source failure before depth-zero exhaustion. It supplies no failed state, rollback, payload or world-effect conclusion. These are scalar-family components, not a general recursive producer instance.


### Executable scalar-family selection

`RuntimeFrameV3ScalarEmitter.compile` selects the published value compiler and checks disjoint static caller/callee/control geometry. Its result contains only that checked value certificate and geometry, with no target-run premise. `selected_value` links every successful root selection to the exact public value-compiler result. Runtime cursor, actual source evaluation and payload capacity remain explicit in `RuntimeFrameV3ScalarEmitterSound.endpoint`, which derives the complete disjoint caller representation and actual execution. The original populated 22-word result and argument-failure prefix are witnessed through the selected code; overlapping layouts are refused.

This is an executable emitter for the fixed scalar countdown family. It does not inspect arbitrary recursive source syntax, replace the general recursive compiler, establish approved-domain provenance or inhabit the complete frozen V3 contract.


### Recursive image authentication

`RuntimeFrameCodeAuthentication` compares the existing instruction lists structurally, including both condition and body lists of nested loops. Its total recursion follows the finite code data, with no runtime horizon cutoff. Soundness gives exact instruction/list equality and therefore the complete existing execution outcome and common-suffix equality. Reflexivity and common-prefix equations share kernel-checked boundaries instead of repeatedly reducing well-founded proof data. The previous flat recognizer is unchanged.

The concrete candidate retains the selected scalar-family image, full populated caller representation and 22-word observation. Its full-image positive proof uses construction equality and generic reflexivity, rather than an independent full-image computational reduction. Nested condition/body/order, destination, cursor and trailing-instruction controls distinguish altered images. This authenticates code data; it does not select arbitrary source recursion, prove physical EVM execution, close approved-profile provenance or supply a general V3 producer.


### Frozen scalar plan entries

`RuntimeFrameV3ScalarPlan.plan` packages the selected scalar-family code in the unchanged frozen recursive-emission interface. Its index-based arena reserve is the maximum of mandatory control words and twice the predecessor index; it is independent of the caller and source success. `entered_capacity` derives actual payload capacity for a count below that index. With actual count evaluation and explicit bottom-below-pointer placement, `returned_of_eval` derives the complete frozen `Returned` relation, including protected older words.

The populated client has a real successful entry at index four and retains the exact 22-word endpoint. A separate bad-argument plan has a real reverting entry at index zero. Capacity, control-space and cursor negatives are checked. These different plans are not one dual-outcome V3 producer; approved-domain coverage and general recursive source selection remain open. The universal scalar-family transport is proved below. Index-reserve metadata is not an approved-profile characterization.


### Universal scalar-family claims

`RuntimeFrameV3ScalarClaims.returns` proves the unchanged frozen `ReturnClaim` for every Entry, source output and quotation index of the selected scalar family. Actual source success and the published value certificate supply its uint count; `word_val` identifies the canonical count, and the native source theorem derives sufficient depth and the exact returned output. Count evaluation and sufficient depth are no longer additional hypotheses of this frozen claim. `bare_revert` proves the corresponding universal frozen bare-revert claim, retaining the distinction from successful and exhausted source runs. The static bottom-below-pointer condition remains explicit.

Concrete clients obtain the target witness through ReturnClaim and retain the complete original 22-word observation by deterministic execution equality. A separate failing-argument plan exercises BareRevertClaim. These results do not supply same-plan dual-outcome V3 nonvacuity, approved-profile coverage, arbitrary recursive body selection or physical/world-call correspondence.


### Same-plan scalar success and revert

`RuntimeFrameArgumentAgreement` derives the exact common pushed word and unchanged machine from checked value certificates with equal actual source results. Disjoint-entry suffix agreement follows real prefix execution. `RuntimeFrameV3ScalarDual` uses that boundary for one selected conditional argument: the original protected scalar chooses a successful literal, while a second represented caller with scalar zero reaches an out-of-bounds read. One code image therefore has genuine successful and bare-reverting entries. The full populated 22-word success observation is retained through actual target execution equality. Input allocator evidence is not a failed-run output claim.

The frozen V2 recursive-return producer is inhabited using universal claims and source coherence. `with_domain` assembles V3 only from explicit external family agreement, universal Entry coverage and both witness memberships. Agreement alone does not authenticate approved-profile provenance. General recursive body selection, approved-domain coverage and full runtime/physical/world correspondence remain open.

The quotation-based plan retains a checked counterexample: the same caller and code succeed at index five, but its arena reserve rejects Entry. The actual-count constructor below repairs this case without changing that plan. Neither constructor establishes approved-profile coverage by itself.


### Actual-count arena demand

`RuntimeFrameV3ScalarDemand` provides a new plan constructor without altering the quotation-based plan. Its reserve is the mandatory control-space floor together with twice the actual checked argument count; a failed argument retains the floor. It uses the existing source value evaluator as natural resource metadata, not an admission predicate or another evaluator. Code, source semantics, fixed interfaces and proof/test/resource limits are unchanged.

The checked metadata bridge reuses the earlier capacity proof at the actual count. This is proof-only: the new universal `ReturnClaim` and `BareRevertClaim` keep their original source quotation index and the same machine/code. `RuntimeFrameV3ScalarDemandDual` instantiates the same successful and reverting callers, now with valid initial entries at every index. The old-plan rejection and new-plan admission at index five are both retained, while insufficient actual demand and insufficient control space still fail. Complete 22-word observations are unchanged.

This repairs the demonstrated reserve obstruction and supplies a V2 producer for the new metadata. V3 assembly still requires external admission agreement, universal initial-entry coverage and admitted witness memberships; none authenticates approved-source provenance by itself. General recursive source selection, full-domain coverage and world/physical correspondence remain open.


### Consuming a recursive scalar return

`RuntimeFrameReturnContinuation.after_return` composes an actual statement return with a checked `Calls.Program` suffix. The general theorem keeps the return claim, initial Entry, actual source success, suffix frame bound and summed allocation input explicit. It derives the suffix representation and allocation room from the same returned state and allocator growth, then preserves the successful representation, stack, base extension and composed growth or exact bare revert. It assumes no failed state or rollback relation.

`RuntimeFrameV3ScalarContinuation` discharges this composition for the existing populated scalar countdown caller. Its result changes from 77 to 3. A publicly selected memory-program suffix reads that returned scalar as the RHS of an old-array write and as the length of a scoped private allocation. The private local is dropped, the old aliases remain, and the heap gains a distinct three-element object. The actual target advances the allocator from 22 to 26 while keeping the protected evaluation stack. Controls check the full 26-word target snapshot, complete source bindings and object observations, old-scalar/frontier/private-identity negatives, argument-failure absorption and source exhaustion.

This is an inhabited return-consumption composition for the selected scalar family. It supplies no general recursive compiler selection, original-source approved-domain provenance, full-signature/world transport or physical byte/journal correspondence. The existing fixed interfaces and earlier fixture observations are unchanged.

`RuntimeFrameV3ScalarContinuationRevert` checks the distinct failure phase after a successful recursive return. The returned three becomes an invalid index into the old length-two array. The publicly selected suffix yields exact bare target revert; `returned_then_reverted` records the genuine successful midpoint and subsequent failure. This does not reconstruct a failed state, prove rollback, identify external payload bytes or assert absence of earlier effects.


### Re-entry after a growing caller continuation

`RuntimeFrameReturnReentry` derives a second frozen Entry from the actual reached representation, restored cursor and allocator growth of a completed return. The resource conditions remain explicit: equal pointer/local-limit layout, bounded next workspace and arena demand, the next context's control floor, its result-frame bound and genuine initial summed allocation input. `after_return` obtains the dynamic fields from the same `Returned` witness; neither theorem assumes a second Entry or target simulation.

`RuntimeFrameV3ScalarReentry` packages the actual mutation/allocation prefix and discharges those conditions at its reached state. The next publicly selected argument reads old-array element zero after its change from seven to three. `RuntimeFrameV3ScalarReentryEndpoint` composes the real source programs and target images, preserving the stack, source representation, bases and total allocator growth four. The pre-existing private object and the new object at base 22 survive the second call; the allocator remains 26. Complete source objects and the 26-word target snapshot are checked, including private workspace reuse and stale-count, wrong-frontier and wrong-object negatives.

These results establish frame re-entry and an inhabited scalar-family composition. General recursive source-body selection, approved-profile provenance, full-domain coverage and world/physical adequacy remain separate obligations. Exhausted source quotations are distinguished from successful calls; no failed state or rollback relation is inferred.


### Source-aware scalar recursive selection

`RuntimeFrameV3ScalarSourceCheck` inspects the actual typed quoted program. Its one-layer parser checks the guard, argument expressions/names, recursive name/index, return location, increment and zero branch while retaining the actual child thunk. Recursive verification checks each child at the existing quotation index and requires the exact exhausted base. A success carries a kernel-proved equality with the existing scalar body. `RuntimeFrameV3ScalarSourceCheckLaws` proves recognition at every quotation index; no new runtime fuel or admission cutoff is introduced.

`RuntimeFrameV3ScalarSourceCompiler` parses the supplied `callRec` statement and preserves its extracted arguments, result binder, names, index and thunk. It records the real body-check receipt and public argument-emitter receipt. Its conditional successful-return and bare-revert claims apply to that actual source statement. Outer binder labels are erased only by the existing native call evaluator; no target simulation is assumed. A small constructor equation shares those checked results instead of normalizing independent certificates.

The client selects the real post-allocation heap-reading call at every index, including the unchanged native default, with the same runtime image. Its reached Entry and return remain the complete earlier 26-word endpoint. A selected invalid argument has a real source and target bare revert. Negative controls include a program whose outer layer matches but whose deeper child changes canonical exhaustion into revert: complete verification rejects it. Wrong guard, return destination, increment, base and index are rejected too.

This is specialized intrinsic scalar-family selection, not general recursive compilation, elaborator/catalogue provenance or approved-profile coverage. The old `Mutation.compileRecursive` refusal is unchanged. A checked exhausted quotation can still select an image that succeeds; the explicit control records why the two frozen conditional claims are not a full failure/termination simulation. Physical/world correspondence and the original full validation obligations remain open.

### Scoped default locals around selected recursive bodies

`RuntimeFrameScopedSource` proves a full-outcome equation for an actual block that runs a body, introduces one unused default primitive local and drops it. Successful state, heap extension and every halt are preserved; this is a law of the existing evaluator, without heap-content preservation assumptions. The call law retains the same arguments and return binder.

`RuntimeFrameV3ScopedScalarCompiler` recognizes precisely that wrapper around a checked scalar body. It checks the inner final context, complete body receipt and public argument-emitter receipt. Its constructor equation links the actual public selector to the selected emission. It does not treat initialized locals, observable writes or extra inner locals as unused defaults.

The registered client accepts every primitive local type, name and quotation index, with the same target image. At the real post-mutation/allocation caller it discharges the reached Entry and source success, preserving the previous complete 26-word endpoint, aliases, private/new objects, result and stack. A selected invalid argument has a real source and target bare revert. Controls retain initialization/write/context/body refusals and distinguish source panic, payload and exhaustion; refused payload bodies have no target payload theorem.

This is specialized scoped source selection, not arbitrary recursive compilation, frontend/profile provenance or full failure/termination correspondence. The earlier exhausted-source/target-success boundary remains. Original mandatory validation and general profile/world obligations remain open.

### Scopes inside recursive quotations

`RuntimeFrameV3RecursiveScopeCheck` recognizes an optional exact unused-default-local wrapper at each scalar quotation level. `strip` proves full source evaluator equality for the inspected wrapper and checks its inner context. The checker then validates the actual head and stored index and recursively checks the actual child at the lower existing index. It introduces no new runtime cutoff. Double wrappers and arbitrary local effects remain unsupported.

`step_congr` transports the full child result through the existing native call, branch and sequence, including dependent successful outputs and every halt class. Explicit `base` and `turn` construction boundaries retain the same inspected core while building proof-bearing results. `RuntimeFrameV3RecursiveScopeLaws` proves full outcome agreement and actual recognition for a family whose body scopes a default local at every activation, for every primitive local type, name and quotation index. The recognizer constructs these proofs from syntax and congruence; it does not decide equality of arbitrary execution functions. These unused locals are elided from the common target image; no new physical slot or per-parent representation is inferred.

`RuntimeFrameV3RecursiveScopeCompiler` retains actual source fields, the complete semantic-check receipt and public argument-emitter receipt. Source execution equality transports the existing conditional success and bare-revert claims. The populated client discharges Entry and source success at the existing post-allocation caller, preserving the complete 26-word endpoint. A selected bad argument has real source and target bare revert. Controls accept mixed wrapped/plain levels, reject a deeper changed base with an observably different source halt, retain older-selector refusals and distinguish exhausted source from the common successful image.

These modules extend specialized intrinsic source selection inside recursion. They do not establish arbitrary recursive-body compilation, original frontend/profile provenance, full failure/termination correspondence, or physical/world adequacy. The frozen interfaces, original observations and mandatory gates are unchanged.

## General closure inventory and boundary (V12-P1 cloud lane, 2026-11-06)

This lane took over the V12 runtime-frame write scope from the Codex
`v12-flow-calls` lane (H75).

### Inventory: what P1 provides on master

- Frozen interfaces V1–V3 (`RuntimeFrameInterfaceV{1,2,3}`), unchanged.
- Ordinary calls: V3 `PendingCallProducer` instances from
  `RuntimeFrameV3CallProducer`/`…Ref` for selected checked call-free bodies
  (P1-CALL); `PendingBareRevertProducer` instances (P1-REVERT).
- Fixed thunks: `V3FixedThunkProducer.of_call` already transports any V3
  ordinary-call producer of `thunk ()` to `PendingFixedCallRecProducer` at
  every quotation index (general; P1-THUNK).
- Recursive families: V3 `PendingRecursiveReturns` for the scalar countdown
  (`ScalarDual`, `ScalarDemandDual`), its scoped variant
  (`FrozenScopeCoverage.with_profile`) and the allocating countdown, each
  taking only the external approved-domain agreement. No general recursive
  compiler: `Mutation.compileRecursive` still refuses every `recUnroll`.
- `RuntimeFrameRestoredRepresentation.restorationProducer` inhabits V1
  `PendingRestoration`.

### What G49 requests (H68, family 3 "P1 frame claims")

The H68 request (which the Codex lane's last report asked to receive as an
off-git payload) is also recorded in Git on the unmerged branch
`codex/solidity-h55-sol-20261106/g49-final-theorem` at `62377f31`, file
`docs/feature-work/h55-g49-final-theorem.md`, section "3. P1 frame claims":

```lean
p1_frame_bridge : (x : NativeContext_frame) → Approved_frame x →
  BridgeGoal (A_frame x) (B_frame x) (ps_frame x) (pt_frame x)
    (beta_frame x) (nu_frame x) (Local_frame x)
```

where `BridgeGoal A B ps pt beta nu Local` is a `PassCorrect
(Behaviour.ofLang A ps) (Behaviour.ofLang B pt)` with fixed `envAbs = beta`,
`need = nu` and `Local` the original `ReturnClaim`/`BareRevertClaim` plus V3
admission agreement, coverage and witnesses. `PassCorrect.back` requires every
target prefix of the canonical target language to map back to a source prefix,
and the request forbids turning success and bare-revert evidence into
all-outcome adequacy.

This bridge is not proved here, for three reasons this lane cannot remove:

1. `PassCorrect`, `Behaviour` and `BridgeGoal` exist only on the unmerged G49
   branch (`Solidity/Roadmap/G49Final/PassCorrect.lean`); master has none.
   Importing them would merge another lane's scope.
2. No canonical `Lang Event Outcome` for P1 endpoints (`A_frame`, `B_frame`)
   exists; the request names them as owner deliverables, and their
   definition is an interface design decision.
3. `PassCorrect.back` over a canonical EVM-side language needs panic, payload,
   exhaustion and divergence transport (G37.02, G38), which P1 does not have.

### General closure: boundary and the generic part

`RuntimeFrameV3GeneralBoundary` makes the scope of a "general P1 closure"
precise without changing any interface:

- `callRec_run` is the existing definitional `Stmt.run_callRec`: a
  `callRec` runs as the ordinary call of its body. `return_of_call`,
  `bare_revert_of_call`, `successful_of_call` and `reverting_of_call` carry
  each V3 field along it.
- `of_unrolled` and its converse `unrolled_returns` are a definitional
  repackaging, the recursive analogue of `V3FixedThunkProducer.of_call`: the
  V3 `PendingRecursiveReturns` for any `step` is exactly the ordinary-call
  obligations of each unrolled body `recUnroll Prog.recBase step n` with one
  code image. This reduces a general recursive closure to per-body ordinary
  calls; it proves no such call.
- `no_call_producer`, `no_fixed_producer`, `no_recursive_producer` restate
  formally the limitation the V3 docstring already records: each dual-outcome
  V3 structure is empty for a source that never bare-reverts.
  `trivial_never_reverts` and `no_unrestricted_closure`: for every contract
  and fragment, and in particular the full domain (an empty domain refutes it
  trivially), the uniform empty-body family has no V3 recursive producer, so
  "every family has a V3 producer" is false. A general closure must be stated
  over a source class, or with a success-only companion interface; a frozen
  interface change needs a versioned pair (H57) and a user decision.

Controls (`RuntimeFrameV3GeneralBoundaryControls`): `rebuilt` round-trips the
scoped scalar-family producer through `unrolled_returns`/`of_unrolled` with
the same plan (`rebuilt_plan`), which shows only that the repackaging is
faithful; the trivial family exhausts at index 0, succeeds at index 1
(`trivial_exhausts`, `trivial_succeeds`) and is empty at the full domain
(`trivial_empty`). The five pinned declarations (`no_unrestricted_closure`,
`of_unrolled`, `unrolled_returns`, `rebuilt`, `trivial_empty`) use only
`propext`, `Classical.choice` and `Quot.sound` (`#guard_msgs` and
`scripts/g07-axiom-pins.d`).

Reviews: read-only finder and skeptic reviews found no proof defect. Fixed
from their findings: the duplicate `callRec_run` proof now reuses
`Stmt.run_callRec`; the repackaging and restatement character is stated
plainly; `no_fixed_producer` needs one index only; the axiom claim names
the pinned declarations; the pins are recorded; docstrings tightened.

Still open: a general recursive compiler with per-body `ReturnClaim`
(the inputs to `of_unrolled` for arbitrary `step`), approved-profile
provenance, G37.02 divergence and G38 failure classes, and the G49 bridge.

Gate: `./run-lean.sh` built all 6416 default and SolkeyTestSuite jobs
("Build completed successfully"); its final `scripts/check-solkey.sh` step
reported 167 sort-annotation mismatches between the SolKey checkout beside the
repository (`5c448df`) and the annotation table. This change touches neither;
re-pinning is the SolKey migration's job (`docs/solkey-migration.md`).
Per-file Lean diagnostics of both new modules are clean.

## Frozen interface v4: success-only companion (H57 pair, user decision 2026-11-06)

The user chose a versioned success-only companion over the frozen V3
interface (Q1 of the V12-P1 result). `RuntimeFrameInterfaceV4.lean`,
namespace `…RuntimeFrame.InterfaceV4`, declares `PendingCallProducer`,
`PendingFixedCallRecProducer` and `PendingRecursiveReturns` with every V3
field except `required_reverting_entry`: the same external admission domain
and agreement, universal Entry coverage, an admitted successful entry, the
universal `ReturnClaim` and conditional `BareRevertClaim`, and for recursive
families source coherence. V3 is unchanged. No claim is weakened; only one
non-vacuity witness is dropped. Provenance of the approved domain stays
external.

### Closure under V4 and its boundary

- `RuntimeFrameV4TrivialFamily.producer` is a real V4 recursive producer for
  the never-reverting empty-body family, over the populated `CompileExamples`
  caller with the publicly selected void-call image at every index. Return
  claims are `NoneProducer.returns` at positive indices and vacuous at the
  exhausted index 0; the bare-revert claim holds vacuously at every index
  (the source never bare-reverts); coherence is derived from the
  source; coverage is universal over a physical domain with no index filter;
  the successful entry is a real admitted caller at index 1. `satisfiable`
  shows all V4 fields jointly satisfiable (with `approved := domain`, which
  is not provenance). `v3_empty`: V3 is empty for the same family and domain,
  so V4 strictly extends V3. This family is degenerate: `trivialStep` ignores
  its continuation, so no index recurses. A V4 producer for a genuinely
  recursive never-reverting family is not supplied; the populated recursive
  families reach V4 through `recursive_ofV3`
  (`RuntimeFrameV4MigrationControls`), but those can also revert.
- V4 still does not close every recursive family. By design it keeps the
  success witness, so `V4Migration.no_success_producer` empties it for a
  family that succeeds from no caller (`exhaustingStep`, `exhausting_empty`),
  although its return claim would hold vacuously; and it keeps source
  coherence, which one code image needs (`no_incoherent_producer`; no concrete
  incoherent family is exhibited). The remaining gap for a universal closure
  is a general recursive compiler: the inputs of `V4Migration.of_unrolled`
  (per-body ordinary-call `ReturnClaim`, with coverage, coherence and a
  success witness) for an arbitrary `step`. Only selected families have them.

### Migration notes for V3 consumers

- Nothing changes for V3 consumers: V3 is frozen and its producers remain.
- `V4Migration.call_ofV3`, `fixed_ofV3`, `recursive_ofV3` turn any V3
  producer into a V4 producer with the same plan. A consumer that uses only
  successful-return transport (ReturnClaim, coverage, coherence, the success
  witness) should take the V4 structure; it then also accepts success-only
  sources.
- `call_toV3`, `fixed_toV3`, `recursive_toV3` turn a V4 producer plus an
  admitted `RevertingEntry` for its plan back into V3;
  `recursive_round_trip`/`recursive_round_trip'` prove the two maps inverse
  (by `rfl`), and `RuntimeFrameV4MigrationControls.round_trip` checks it on
  the scoped scalar family.
- Without the reverting witness, a V4 `BareRevertClaim` may hold only
  vacuously (it does for every never-reverting source); it carries content
  only for sources that can bare-revert. Consumers that need the
  reverting witness keep asking for V3.
- `V4Migration.of_unrolled` is the V4 analogue of `V3GeneralBoundary.of_unrolled`.

### G49 bridge

The user chose to merge the G49 `PassCorrect` modules to master first (Q2);
they landed at `706e36825` (H85). See the next section.

Reviews: read-only finder and skeptic reviews found no proof defect or field
mismatch with V3. Fixed from their findings: the trivial family is described
as degenerate and its bare-revert claim as vacuous at every index; the V4
boundary wording matches `NeverSucceeds`; `no_incoherent_producer` replaces an
unproved docstring claim; full `rfl` round trips replace a plan-only check;
`exhausted_is_covered` states the Entry; the migration control is pinned.

## P1 frame bridge (H68 family 3, after H85)

`tests/h55/g49-final-theorem/bridge-requests.json` (family "P1 frame claims")
requests `p1_frame_bridge : (x : NativeContext_frame) → Approved_frame x →
BridgeGoal (A_frame x) (B_frame x) (ps_frame x) (pt_frame x) (beta_frame x)
(nu_frame x) (Local_frame x)`.

### Canonical languages

`RuntimeFrameP1Lang` defines `sourceLang` and `targetLang` of type
`Lang Event Outcome` for one P1 context. A context is a source family
`source : Nat → Stmt C Γ Δ`, an emitted code image and an admitted domain.

**Shared parts.**

- Both languages use the same `Input`: the `L frame caller base machine
  start` of `Entry`. `Allowed` is the admitted domain.
- The source resource is the quotation depth. The target resource is `Unit`,
  because `Evm.run` takes no resource index.
- The source language takes depth consistency as an argument. It is a fact
  that each family must prove.

**Observation.** It is deliberately coarsened to what `Evm.Out` can show,
since `Evm.Out` carries no data:

- `events = []`. This is canonical only for families without external calls
  or payments.
- Success is `success []`. Every source revert class is `revert []`: bare
  revert, panic, and revert with data. This matches the compiler's mapping of
  a panic to a bare `REVERT`.
- Depth exhaustion and divergence are unfinished.
- On the target side, `ok _ 0` is success and `revert` is revert. A fault, or
  an `ok` with a pending jump, is unfinished.

Typed states and machine facts are not observed; they live only in `Local`.
Whether this coarse observation is acceptable to G49, or counts as the
"trivial trace" the request rules out, is for the G49 lane to decide. A
richer canonical language needs revert data and events in the target model.

### Delivered bridge: a shape check

`RuntimeFrameP1Bridge.p1_frame_bridge` is proved for the degenerate V4
trivial family. It is a type-inhabitation and plumbing check of the requested
`BridgeGoal`, not evidence of P1 adequacy.

**Instantiation.**

- Native context: the external approved family.
- `Approved_frame`: the unchanged agreement with the producer's admitted
  domain. That domain has no index or outcome filter, and its provenance is
  not established.
- Programs: the actual family and its emitted image.
- `beta := id` and `nu := fun _ _ => ()`. These are forced by the joint
  `Input` environment and the `Unit` resource. Neither is shown uniform with
  the single public map.
- `Local_frame`: the actual V4 producer with this plan, not a restatement of
  its fields. Its bare-revert claim is vacuous here.

**What the `PassCorrect` proves.** All its fields are proved with no premise
beyond the agreement, but their content is small:

- the source is unfinished at depth 0 and succeeds at every positive depth;
- the target always succeeds, by `ReturnClaim` at depth 1.

**Fold entry.** The pass's `Input` environment matches no neighbouring G49
pass, so `fold_entry` folds only as a singleton.

**Controls.**

- `satisfiable` instantiates `approved := domain`. This is not provenance.
- Depth 0 is unfinished.
- A panic is observed as a completed revert.
- A pending jump is unfinished.
- The domain rejects a frame too small for the arena.

### Not delivered: general families

For general families, the bridge is not merely unproved: with this
observation it is false for some families.

- **Payment.** A paying call succeeds in the source, but the compiler's
  target reverts. So `success [] ≤ revert []` fails forward.
- **Revert data.** A family with a payload revert loses its data in the
  observation.
- **External calls.** A family with external calls has session events this
  language does not observe.
- **Depth consistency.** It is a per-family obligation, and no
  counterexample is exhibited.
- **Missing transports.** Even families without these features need
  backward transport of every target outcome. In particular, a target revert
  must match a source revert at some depth. That requires the
  panic/exhaustion transports of G37.02/G38, which P1 does not have; success
  and bare-revert evidence cannot stand in.

A general bridge therefore needs a richer canonical language, with revert
data and events on the target, plus those transports. The G49 lane must
verify this delivery; the request's `adapterStatus` stays theirs.

Reviews: read-only finder and skeptic reviews found the proofs sound and the
first observation too coarse. Panic and payload reverts had been unfinished,
which made their transport vacuous; this is fixed. The docs had overclaimed
the "full domain", the ordinary fold entry and the blockers; these are
corrected. `Local` now reuses the producer, and `ok` with a pending jump is no
longer success.
