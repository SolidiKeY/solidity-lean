# V16 correctness consumers

Full source/compiler/runtime/deployment/specification correctness remains open.
The results below are scoped consumers of existing intrinsic definitions;
conditional composition and inhabited fixtures do not establish full coverage.

## Dynamic allocation memory preservation

[NewAllocation](../../Solidity/Roadmap/V16/SSCP2/NewAllocation.lean) proves an
SS-CP2 allocation-site consequence without changing the Source evaluator.
`newData_valid` derives `DataOK`, `Data.Top` and `Data.Inner` for every actual
successful `newData` result. Array defaults are proved nonreferences using the
published default-location law. `allocation_mem` composes this with the existing
`allocRef_mem'` theorem, keeping the full `MemOK` invariant on every halt as well
as success, and returning an agreeing reference on success.

`eval_new_mem` follows the actual `newArray` arm, including index conversion,
the allocation-size panic and allocation. It retains a child-memory-preservation
premise; that is not a proof of the entire evaluator walk. `local_new_mem`
discharges that premise from an actual typed uint256 local read, with no assumed
source success or desired simulation. Neither theorem claims general progress
or excludes `stuck` outcomes from the original semantics.

[The controls](../../Solidity/Roadmap/V16/SSCP2/NewAllocationControls.lean) begin
with a live byte object `[42,77]` at address0 and a protected caller reference.
Both pipelines allocate a zeroed Boolean array at address1, retain the old
object and complete caller locals, and preserve all nonheap state. MemOK and
the new reference's validity follow from the new local-length theorem. A wrong
result at address0 is rejected: that address contains bytes, not the new array.

The actual size `2^64` panics with exact allocation-panic data before allocation.
Horizons zero and one time out without changing the state. Separate helper
controls retain two different refusal phases: a nested-reference element type
has no default and is not `newable`; a storage-location byte object is allocated
before `allocRef` refuses its reference. Direct `allocation_mem` application
proves MemOK even for that grown failure heap. Those helper refusals are not
admitted `newArray` syntax witnesses or whole-transaction rollback results.
Thirteen generated guards pin the scoped dependencies to the observed axiom sets.

The environment/program/fixed-parameter controls establish inhabitance only.
They are not frontend acceptance, a reachable deployment, SourceSpec or physical
Source-to-EVM frame certificates. Source admission/lowering, the remaining full
MemOK walk, recorded hash preimages, arbitrary failure-plan execution, complete
backend/fetched-byte/resource adequacy and final deployment/transaction/SolKey
specification applications remain obligations.

Independent finder and skeptic review found no semantic defect. The requested
direct preservation control for the post-allocation refusal was added, together
with low-horizon timeout controls.


## Bounded Source transaction specification consumer

[SourceTransactionConsumer](../../Solidity/Roadmap/V16/SourceTransactionConsumer.lean)
consumes the published V08 `g` and `poke` executions at horizon20, in both
pipelines. These are actual `Source.runTx` computations, with complete returned
state records and ordered outcome pairs, rather than a replacement evaluator.
A reverted transaction completes as `.ok (.revert [])`, so a following
transaction runs. A horizon timeout is `.error .timeout`; the monadic suffix
is skipped and the actual unfinished state is retained. Timeout is not proof
of divergence or a completed rollback.

`after_revert_success` and `after_success_revert` use the published journal undo
certificate at the actual entry. The second reverting call rolls back to the
first committed world with x5, rather than the original world with x3.
`revert_success_prefix` and `success_revert_prefix` retain both exact outcomes
and the entire final state. `timeout_prefix` retains the actual early halt.
`success_revert_spec` constructs the existing Source Hoare triple: its inhabited
precondition is the exact populated initial state, its postcondition the exact
outcome pair and final state, and its halt postcondition false for these checked
bounded runs. This is not a full-profile termination assertion.

Old bytes are arbitrary; the populated caller locals, log structure and prior
event shape are fixed fixtures. Complete state equalities retain every field; `complete_vector`
extracts selected storage/transient/journal/heap/local/log observations and the
whole ordered event history. `wrong_original_rollback` rejects the incorrect
original-world endpoint for the actual two-run composition; `wrong_event_order`
shows the two fixture event histories differ; with `revert_success_prefix` and
`success_revert_prefix` this separates the two run orders. Nine generated
axiom guards pin the observed standard axiom sets. Independent read-only finder
and skeptic review found no semantic defect.

These are fixture executions, with inherited toyFixed selectors and fixed
horizons. No accepted-source, SourceSpec, least-completing-horizon session,
constructor-rooted reachability, source-to-intrinsic representation, ABI/world,
physical frame, bytecode, Osaka/resource or adversarial correctness is supplied.
SS-CP2 remains owned by MIC; its integrated allocation modules are unchanged.

Final finder and skeptic review corrected the distinction between arbitrary
payload bytes and fixed fixture locals/log/event shapes. No proof premise or
observation was changed.


## Native allocating-frame specification consumers

[NativeParentConsumer](../../Solidity/Roadmap/V16/NativeParentConsumer.lean)
consumes the published P1 native-unwind and mutating-activation certificates.
Its source is intrinsic `Prog`/`State`, distinct from the independent
`Solidity.Source` interpreter used above. `parent_specification` retains the
producer's actual frame entry, read bound and parent-index premises, all source
and target prefix/return facts, representation, stack, old addresses and allocator
growth. It derives a successful program run and genuine box/diamond counter
postconditions without a new success, non-exhaustion or simulation premise.

The inhabited countdown client returns at both parent horizons. Its counter is
n+1, not the child's n; `native_spec_iff` reduces either modality to its actual
returned state's postcondition. `native_return_transport` carries this to the
represented endpoint with the complete published ordered stack/16-word vector,
old addresses and actual eight-cell allocator growth.

The separate mutating-entry client writes an old array element before allocation
and argument/frame entry. `mutating_entry_transport` retains the real write,
argument evaluation, entry, target execution, representation, four-cell growth,
protected words and complete published stack/21-word vector. Its child has
counter1 and fixed element one equal to2. Counter2 and the old element value9
are rejected there; the actual mutation does not satisfy `Heap.Keeps`.
This entry is not the completed return of the readonly countdown family.

The represented bad-index client retains intrinsic bare revert and target revert:
a true diamond is false there even though its box is true. `recBase` still
exhausts and satisfies the approved exhausted-diamond reading. These controls
supply neither panic/revert-data transport nor divergence or physical gas facts.

All target results concern existing structured IR instructions and running
prefixes, not fetched bytes or the pinned EVM interpreter. No Source admission,
full P1 recursive selection/V3 profile, complete mutating caller return,
ABI/world/physical-store agreement, deployment or adversarial closure follows.
The existing physical-writer mismatch and other owners' obligations are unchanged.
Independent finder/skeptic review requested a direct returned-counter negative;
`wrong_returned_counter` now exercises the new positive return specification.


## Constructor-return byte postconditions

[CreationReturnConsumer](../../Solidity/Roadmap/V16/CreationReturnConsumer.lean)
consumes the published finite constructor-copy execution directly, without an
instance of the pending creation-return producer. `outcome_exact` fixes its
complete outcome; `returned_post` supplies an actual returned-output witness
exactly when a predicate holds on the complete linked/immutable runtime image.
`reject_post` and `not_reverted` retain the same artifact and execution.

The inhabited published fixture has two library locations, two immutable words,
nonempty arguments and a complete 105-byte returned image. Controls reject
argument leakage, a shifted observation window and relabelled revert outcomes.
Independent read-only finder and skeptic reviews found no semantic defect;
the first-byte/window wording was clarified after review. Scoped axiom guards
retain the standard axiom set.

These are constructor-copy byte postconditions, not Source constructor
specifications, account installation, physical EVM execution or gas adequacy.
No pending producer field, source admission, G50 deployment or full G51
specification obligation is discharged by this component.


## H55 historical calculus/compiler consumer port

The consumer, 24 semantic controls and strict interface audit are ported from
the exact eight-file historical export of `e5934822410d79093183ee16cae566d9e5616048`.
The archive and every file hash were verified before extraction outside Git.
All newer sections above are retained. The H55 work record is
[h55-g49-final-theorem.md](h55-g49-final-theorem.md).

[CalculusConsumer](../../tests/h55/g49-final-theorem/staging/CalculusConsumer.lean)
(staged outside the library until its absent `Solidity.Roadmap.V16.CompilerConsumer`
prerequisite lands; see the H55 work record) keeps the original six theorem signatures. Its checked
compiler Input rules out exhausted execution; the genuine calculus diamond
then gives a successful source postcondition. General target alternatives retain
payment refusal and candidate representation. The nonpaying theorem removes
that alternative only with the original syntactic pays equation. Box consumers
require an actual successful target; callback consumers retain the explicit
callback-free postcondition condition and do not prove callback bytecode behavior.
Residual frames remain empty. No formula, rule or approved exhaustion reading
is changed. These are scoped intrinsic-body consumers, not source admission or
G49/G50 public correctness.

The controls retain populated core and allocating-memory fixtures, protected
stack and representation, the complete named 11-element observation vector,
wrong value/post/alias/frame/allocation/failure controls, payment alternatives,
invalid input, callback guard, panic and exhausted false-diamond boundaries.
Their original fixture imports are currently missing from published master.
No historical pass is asserted as a current proof pass.

The strict audit retains all six contracts, 24 closed controls, dependency/axiom
pins, producer hashes, 19 corruptions and 2290 open inherited obligations. Its
original heap-audit dependency is also missing. The bulk premise JSON is not
tracked; the committed H55 staging manifest pins its exact bytes and provenance.
The audit accepts its external payload path as the fourth positional argument,
after metadata, accounting report and output path. Original producer-revision
and body checks remain unchanged; newer master additions are not overwritten
to satisfy historical hashes. Registration changes and the historical
LoopControls import are reserved for central integration.
