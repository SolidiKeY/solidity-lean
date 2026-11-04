# Result-producing word adapter after actual RHS memory effects

`Backend/MemoryOps/SourceRhsValue.lean` builds on the existing discarded-result
statement certificate in `Backend/MemoryOps/SourceRhsAssignment.lean`.
`rhsAssignValueCode` is ordinary composition of two published word writes and
an existing scalar-local read. This is a concrete certified adapter, not a new
interpreter or proof of general Source-expression compiler selection/emission.

`rhs_assign_value_word` derives the actual Source Bool result, existing native
Prog2 writes and subsequent native local value read from INITIAL alignment,
SourceBoolMemoryAt/MemOK/bounds and published StateRepr. The actual reached
StateRepr and unchanged scalar local feed simple_sim/bool_inv; no desired result
word, reached relation or successful suffix is a premise. The final code pushes
that derived Bool word onto the retained caller tail. Reload changes no memory;
Source/native heap/other-object/world/local and allocator frames are conclusions.
The native model is Prog2 followed by a Val read; no intrinsic assignment-expression
AST is invented. Existing Source fuel+3 inner/fuel+4 whole expression is retained.

`rhs_assign_value_bounds_word` executes the real successful RHS prefix, then the
outer bounds error. Whole result code and every appended suffix halt BEFORE
reload. Source retains its actual RHS state; native/word revert returns no final
machine. No transaction rollback or target panic-byte equivalence follows.
These symbolic-word stack/result laws are not byte-slice checkedRun or physical
operand-stack/gas/active-memory/whole-EVM certificates.

Both pipelines and true/false values are inhabited. Initial LEFT[T,F,F],
RIGHT[F,T,F], old[LEFT], source[LEFT,RIGHT,LEFT], empty[] are represented using the
existing fixture. The INITIAL scalar Bool local is represented at cell7; this
setup is not claimed as Source declaration/local-assignment execution.
Actual writes give LEFT[T,v,F] then LEFT[v,v,F], before the result reload.
All five ordered Source/native objects and every cell of four24-word observations
(initial, first write, second write, reload) retain parents/aliases/neighbour/free48.
True returns word1 and false word0 over saved caller42. Dropping reload gives the
wrong stack; the true result differs from the old false RHS cell. Stack negatives
are exact observations, not execution of an alternative general compiler.
The late-failure client directly applies the new bounds theorem; existing complete
failed-prefix observations remain available without any invented suffix machine.
All prior fixture bodies/vectors/guards stay byte-preserved.

Five exact measured standard-only guards accompany these laws and clients.
This does not close general Source/native lowering, world/representation/physical
bytes, arbitrary reference/recursive graphs, ABI/storage/deep-copy, allocation
failures or final Source/V10/target composition. Original queues remain partial.
