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
