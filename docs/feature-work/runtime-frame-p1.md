# P1 runtime frames: foundation and frozen interfaces v1 and v2

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
Result, Reference, ReferenceProgram), the `tests/runtime-frame/` fixtures and
the modules of other lanes on that branch were not merged.

Read-only finder and skeptic reviews found no `sorry`, axiom or heartbeat
change, and no import or layer problem. They found the vacuity weakness above,
which is now documented. They also found overstated descriptions of
`local_repr`, `Arena` and the call selectors, which are now corrected in the
docs and docstrings. Signatures are unchanged.


## Further proved restoration components

`RuntimeFrameRestoredRepresentation` implements the exact v1 restoration
premise from the actual source-tail equation, reached representation, address
extension, current fragment compatibility and recovered context.
`RuntimeFrameCapturedProgram` composes actual capture, checked body and restore,
deriving full reached representation, stack and allocator transport. Its client
uses a private binder and actual old-object mutation. Bare failure after capture
absorbs following code without a failed-state or rollback claim. These results
still do not supply general call return/export scheduling or a runtime return
dispatcher, and do not discharge the static-world premises.


## Reference export after restoration

`RuntimeFrameCapturedReference.after_reference` composes actual capture, checked
body execution, restoration and a typed reference export into an old caller
destination. The exported identity is read from the reached representation;
private logical binders are dropped without erasing physical cells or changing
heap contents. Exact source caller-tail agreement and current fragment
compatibility remain explicit. The theorem exposes separate target phase
equations and the full exported representation.

`older_words` derives preservation of the older runtime interval, handling the
header through its restored cursor and other words through the actual capture
and body footprint. `then_program` derives the following caller's allocation
input from the reached growth and summed source cost, returning the final
representation, stack and older interval together with the reached scratch
footprint and result word. It allows ordinary caller writes.

The populated client captures both old aliases, mutates an old object, restores
the caller, exports the private reference, then writes through that returned
alias. The other alias to that object observes the mutation; the distinct
object retains its own contents. A nonzero older sentinel, restored header,
caller scalar and private physical word are pinned with the complete ordered
observations. Wrong reference, cursor, old contents, omitted caller write and
private erasure are rejected. The snapshot payload is observed at the actual
capture state, not asserted to be a world journal.

The client has zero heap cost at base zero. Its allocator transport is the
existing conditional law, not allocator ownership; the runtime header is a
distinct scratch cell. Bare body failure absorbs the export/use suffix without
claiming restoration ran after failure or reconstructing an error state.
These are finite checked-program consumers, not general call-return dispatch,
uncapped recursion, full-signature dispatch or byte/world/transient closure.


## Frozen interface v3: exact-input coverage and both outcomes

`RuntimeFrameInterfaceV3.lean`, namespace
`Solidity.Backend.InternalFlow.RuntimeFrame.InterfaceV3`, adds universal
coverage relative to explicitly supplied typed initial-input domains. V1 and
V2 remain unchanged. The module contains signatures and pending duties only.

`Admission` is a predicate over the exact layout, frame, caller, address map,
machine and cursor. `approved` and `admitted` are visible external parameters,
not fields chosen by an emitter. `AdmissionAgreement` is a named pointwise
equivalence duty. It does not authenticate the provenance of `approved`: its
correspondence to the original source/resource profile must be established
separately. A whitelist, an empty indexed domain or the candidate plan's own
Entry predicate cannot be presented as original-profile coverage without that
justification. No admission domain or producer instance is supplied here.

`EntryCoverage` requires Entry for each exact admitted input, without selecting
a different convenient caller or machine. `FamilyEntryCoverage` retains the
same index in the domain and `plan.at n`. It does not assert that every natural
index physically fits finite word memory; physical feasibility belongs to the
authenticated domain, without an emitter-imposed source depth cutoff.

Every return structure now requires independently quantified admitted success
and bare-revert witnesses, in addition to the existing correctness duties.
Thus it cannot discharge either outcome using only the other one. The fixed
thunk uses a single index-independent domain and requires both witnesses at
each quotation index. The recursive family uses one code image and indexed
coverage, together with its actual successful and reverting members.

A source that never bare-reverts cannot inhabit these dual-outcome structures.
This is an evidence-class limitation, not a source-language refusal or license
to fabricate an error. Its success-only transport remains a separate obligation.
Failure-specialized transport remains separately expressible. Panic, payload
failures, exhaustion, running prefixes and divergence are not conflated with
bare revert and are not supplied by this return/bare-revert interface.


## Implemented v2 void-call producers

`RuntimeFrameCallAgreement.output_of_call` inverts actual intrinsic success
into the evaluated arguments, entered body frame and exported caller result.
`none_tail` and `memory_tail` derive caller-environment transport for the
respective return forms without assuming that equation from a client.

`RuntimeFrameNoneProducer.plan` emits actual capture, the checked native void
call and restoration, keeping runtime arena words separate from checked heap
cost. `returns` and `bare_revert` derive the complete v1 duties. `make` therefore
constructs a v2 `PendingCallProducer` from the actual finite checked program,
fragment compatibility and successful-entry evidence, without taking a target
correctness claim as input. `make_failure` constructs the separately witnessed
failure producer. `make_fixed` transports the same scoped thunk across quotation
indices using the existing intrinsic callRec equation; it is not an unbounded
recursive-family implementation.

The populated client executes a caller prefix, evaluates an old memory alias
as a call argument, mutates the shared object and declares a private callee
alias. Actual ordinary and fixed-thunk producer values yield target endpoints
with the same caller scalar and aliases, changed object contents, untouched
distinct object, protected stack, runtime header and older sentinel. Source
callee bindings are dropped logically. Dead callee physical cells are not
observations promised by this `Returned` contract and are not claimed erased
or otherwise observed by this client.

An admitted bounds-failure body gives a genuine v2 failure producer and exact
target bare revert. The older scratch selector still refuses an explicit
`revert` body; the refusal is retained as an admission control, not described
as runtime rejection. The client has zero heap cost at base zero; allocator
transport remains conditional, not ownership. Memory-result production,
primitive result export, arbitrary workspace reuse, general runtime return
dispatch, unbounded recursion and world/byte/transient coupling remain open.

The separate v3 controls use an illustrative, independently specified resource
domain and real source success/revert inputs. They reject caller-dependent
arena masks, index masks and a whitelist disagreeing with that domain. Their
data-only plan has no asserted target-correctness instance. These controls do
not authenticate the original approved source/resource domain or produce a v3
call implementation.


## Recursive runtime descent foundation

`RuntimeFrameV3RecursiveProducer.descent_prefix` proves every actual reached
`Evm.loopIterN` horizon of the existing runtime-addressed save instructions.
The code is independent of the horizon. Actual caller representation, heap
address map and evaluation stack survive; the runtime cursor advances by that
horizon, while heap allocation cost is zero. Bounds require real frame room
and no word wrap at the requested horizon. Protected earlier words exclude
the deliberately updated pointer cell. Each turn saves the current source-cell
word; a general unchanged-source-word assertion is not part of this theorem.

The populated control reuses the previously checked caller prefix and its
representation. Two actual running turns save address16, retaining two aliases
to that nonempty object, a distinct object at20, scalar9, stack77 and sentinel99.
The complete ordered observation also pins both saved words and cursor12.
Wrong identity, scalar, cursor and horizon observations are rejected. A horizon
without room fails a theorem premise; there is no emitted runtime capacity
check in this slice. The base-zero allocator implication does not establish
allocator ownership.

Independent finder and skeptic source reviews found no correctness issue and
confirmed these boundaries. This is target descent-prefix evidence only.
Source recursive argument/body execution, recursive return/unwind and
termination/divergence correspondence remain to be connected; no
`InterfaceV3.PendingRecursiveReturns` inhabitant is supplied. Approved-domain
provenance additionally awaits the actual P8a interface. The frozen V3
signatures and the transferred ordinary-call, fixed-thunk and bare-revert
producer modules are unchanged.


## Runtime LIFO return control

`RuntimeFrameV3RecursiveUnwind.unwind_nonempty_iter` and `unwind_nonempty_run`
prove actual termination of the existing target loop for every positive frame
count, using one code image that reads the bottom cursor at runtime. Each turn
uses the existing checked pop/restore instructions. Saved frame words may differ;
the destination may initially be clobbered. The final destination contains the
actual bottom saved word. Cursor/destination/header separation and real no-wrap
bounds are explicit. The zero-frame law separately proves that the false guard
skips the body. No recursion evaluator or source admission cutoff is introduced.

`recover_clobbered` derives the complete final caller representation from an
actual represented pre-clobber snapshot, the captured bottom word and the actual
physical destination write. It does not take the desired final representation or
target run as a premise. Heap/world mutation between capture and return is not
covered. The earlier same-word special case remains available with its stronger
saved-equals-current-word premise.

The populated client executes the real caller prefix and two save slices,
writes a different reference20 into the upper saved frame, and physically
clobbers the caller alias to99. The first restore yields20; the return loop
finishes with the original alias16, the other old alias, distinct object20,
scalar9, complete old-object contents, stack77 and sentinel99 intact. Runtime
payloads16/20 remain written. The cursor returns from12 to10. A full instruction
run and complete ordered intermediate/final vectors are proved. The different
upper frame is an explicit target reserved-word write, not a source recursive
call frame. Wrong destination/order/alias/scalar/cursor controls and malformed
pointer fault (distinct from bare revert) are checked.

Independent read-only finder and skeptic reviews confirmed the actual-loop and
snapshot boundaries. Source recursive frame transitions, heterogeneous typed
context layouts, general return dispatch and termination/divergence agreement
remain open; no `InterfaceV3.PendingRecursiveReturns` inhabitant is supplied.
Approved-profile provenance still awaits the actual P8a producer. All frozen
interfaces and transferred producer modules remain unchanged.


## Actual recursive argument and return family

`RuntimeFrameV3RecursiveSource` defines a countdown solely with existing typed
`Stmt.callRec`, `Args`, `CallRet.none` and `recUnroll`. Each recursive activation
evaluates the same memory-reference argument and a checked uint decrement.
`all_horizons` proves actual execution for every natural unrolling horizon:
`count < depth` returns the complete original parameter-frame state; otherwise
the outcome is exactly `.exhausted`. `call_all_horizons` carries this through
actual evaluated outer arguments and exact caller-environment recovery, reusing
the published weakening law. This covers the actual shared heap, persistent and
transient roots, transaction observations and caller locals by full state
equality on success; it does not supply a target/world simulation.

`source_coherence` discharges `InterfaceV1.RecursiveReturnCoherence` for this
actual family and typed entry arguments, for every caller and pair of horizons.
It derives equality from actual execution rather than assuming coherence or
successful outputs. Unset memory arguments revert before body entry and cannot
produce a successful output. The populated client starts from a real caller
prefix and represented nonempty heap with two old aliases, a distinct object
and scalar2. Actual activations have counters2/1/0 and the same reference0;
each successful return recovers its own caller counter. Complete ordered
activation/caller alias/length/content observations and exhaustion/incorrect
horizon/incorrect private-counter controls are checked.

The mathematical horizon does not change frontend `recDepth`, source admission
or exhaustion semantics. A too-small horizon is not divergence or bare revert.
The unset-reference negative has no `StateRepr`, proved explicitly; it is not
an admitted V3 revert witness. The well-formed countdown success/exhaustion
family therefore does not supply V3's dual-outcome instance. No target recursive
call endpoint is asserted here: the shown target prefix only represents the
source caller setup. Connecting these actual recursive argument/frame/return
transitions to the runtime descent and LIFO-return code remains open, as do
general typed layouts, recursive target divergence and approved-profile
provenance. Independent finder and skeptic source reviews confirmed these
limits. Frozen interfaces and other owners' producer modules are unchanged.
