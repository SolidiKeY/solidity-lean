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
