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


## H24 typed input boundary

[H24Input](../../Solidity/Roadmap/V16/H24Input.lean) is an additive frozen V1
interface generated by `scripts/roadmap-v16-h24-interface.py`. `Producer` names
the exact published declaration-graph admission companion. Both its H15
admissible-location graphs and actual Source local-declaration refusal obligation
remain required. No obsolete all-declarations/all-locations condition is added.
`CertifiedInput` names the unchanged checked P8b receipt at that same base
producer. `Request` requires that receipt and an artifact. `LoweringObligation`
names the separate unchanged P8b output: it is not constructed by a request.

These signatures introduce no producer, graph, accepted program, world emitter,
semantic certificate or correctness theorem. There is no concrete P8 inhabitant;
typechecking this interface is not a non-vacuity witness or G48 progress claim.
Frozen upstream interfaces, resource premises and supported profiles are unchanged.
External type-rejection checks cover a bare P8a base used as an H24 wrapper,
receipt reuse across unrelated bases without an equality, and omission of the
local-refusal field. Equal or definitionally identical bases may legitimately
share receipts; no wrapper identity property is asserted. Independent read-only
finder and skeptic review confirmed the signature boundary and these limits.
