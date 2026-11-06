# Reading the actual changed slice cell into a scalar

`Solidity/Backend/MemoryOps/SourceUintSliceCompoundRead.lean` composes real
slice binding, compound addition and scalar read assignment into one Source
Items program. Initial byte/operand/window/bounds/capacity/arithmetic/MemOK
premises are the existing addition producer's premises. There is no supplied
reached state, successful read or final scalar value premise.

`source_uint_slice_bind_add_read` derives the new indexed value from the
actual write and preserved length, executes the resolved read, then binds that
value to the result local. That local may alias the index or RHS: its overwrite
happens after reading the unchanged prior index. The final observer, MemOK,
other-local/old-object/world frames and native heap update follow the same
executions. Original nps and context are retained; arbitrary runtime lengths
remain quantified. Sufficient horizons are binding expression fuel+5,
addition fuel+4, indexed read fuel+2, scalar read assignment fuel+3 and the
three-statement Items fuel+7. No minimum fuel or new admission bound is claimed.

`source_items_triple_error` is a compositional law for the existing evaluator,
with explicit actual sequential statement runs as premises. It returns only
reached globals on error. The inhabited timeout control supplies every premise
from actual operations; it does not assume a desired failure state.

The additive both-pipeline controls in
`Solidity/Backend/MemoryOps/SourceCalldataSliceControls.lean` preserve every
prior body/vector. Fresh [2,0,max] becomes [5,0,max], then the read returns5 and
stores5 in the index local. Old [7,0,max] and neighbor [8,9] remain unchanged.
Complete ordered Source/native object tables, local context, world fields and
actual intermediate expression results distinguish initial2 from reached5.
A subsequent indexed read uses the now-overwritten index5 and really panics;
it is not silently evaluated with the earlier index0.

At whole Items horizon6, actual binding and the2-to5 update complete before the
read-assignment times out. The returned globals retain that changed heap;
prefix locals are derived separate observations, not returned error locals.
The control reads the changed cell through actual Source memElem and preserves
complete tables/world frames. No transaction rollback or successful suffix is
invented.

This checkpoint supplies kernel Source/intrinsic Heap correspondence. It adds
no emitted fresh-payload allocation, full word append, ABI binding, physical
byte memory, external compiler/EVM execution or full Source/V10/target/world
closure. General paths/graphs/copies/all-profile failures remain open.
