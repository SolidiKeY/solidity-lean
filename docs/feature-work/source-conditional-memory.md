# Conditional selection of actual memory effects

`Backend/MemoryOps/SourceConditional.lean` factors the existing Source cond
computation without assuming a desired body run or state. Its equality is
parametric in the result type, horizon and branch expressions, including actual
success/failure states. The existing word conditionalCode is reused for an
effectful false branch or an actually successful/rejecting true branch. The
condition must really push its Bool on the same input machine. No pure-body
ValueSim assumption is used, and no general compiler or interpreter is added.

The additive controls in `Backend/MemoryOps/SourceReferenceReadControls.lean`
consume the genuine initial alignments, observers, MemOK and StateRepr of the
populated five-object fixture. Both pipelines select actual writes: true writes
LEFT1 then LEFT0; false clears LEFT0 then writes LEFT1. Their reached Source,
intrinsic Prog and complete existing word branches are derived, with full old
parent/child/alias/neighbour tables, scalar locals/world/ex/events/logs/fnLocals,
allocator/free48 and saved stack42 frames. Existing native ite selects the
same Prog, followed by the existing value read; no intrinsic expression AST is
invented. The added false-prefix/final/reload24-word vectors and typed objects
complement every older table/vector/guard, which remains byte-preserved.

Wrong-order evidence runs BOTH first writes from the SAME false initial state.
The selected prefix clears LEFT0; the alternative prefix does not. Complete
Source prefix tables and actual word prefix vectors differ. Because the two
writes commute at their final heap, a final vector alone does not establish
selection/order. This is an explicit prefix discriminator, not an inferred
whole-program compiler counterexample.

The selected true endpoint case really writes the RHS and then rejects outer3
on length3. Its Source failure state retains that actual changed prefix and all
observed frames. Native/word revert has no returned target machine; the
unselected local branch is not a fallback, rollback handler or executed suffix.
Exact Source panic bytes stay distinct from target revert. Horizons1/2 time out
before this body's writes; these are observations, not minimal-fuel or public
admission caps. Both actual successful branches and the failure client discharge
the compositional run premises through existing initial-state producers.

Exact standard-only axiom guards accompany the four core laws and six clients.
Symbolic-word/kernel checking does not establish physical bytes, external EVM,
general expression emission, Source/world/representation/liveness/recursive
copy/ABI/storage/all-profile allocation failure or final Source-V10-target
closure. The original queues and required final gates remain open.
