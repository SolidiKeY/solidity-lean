# Short-circuit control of actual memory-writing expressions

`Backend/MemoryOps/SourceShortCircuit.lean` consumes the independent Source
binary-and evaluator and published word binaryCode. A false scalar-local guard
skips an arbitrary Bool body without bounds or successful-body premises. A true
guard enters the body from the guard's actual unchanged state. Success returns
the body's Bool and reached state; error retains the actual body failure state.
The word laws run the existing dup/iszero/jump/pop sequence over an arbitrary
effectful right program. They require the actual left program to push its guard
on the same machine; they do not misuse ValueSim's pure-operand frame premise.
These are compositional control laws, not a general expression compiler.

`Backend/MemoryOps/SourceReferenceReadControls.lean` instantiates the laws using
the existing independently represented five-object fixture and actual nested
assignment body from `Backend/MemoryOps/SourceRhsValue.lean`. In BOTH pipelines,
a false guard skips a body whose separate actual execution clears LEFT[0];
a true guard performs the actual RHS and outer writes, and returns true over
saved caller42. The existing intrinsic ite chooses the same real Prog2 or nil.
All old source/native tables, complete24-word vectors, guards and bodies are
preserved verbatim. The added full24-word guard outputs identify retained
parents/shared aliases/neighbour/free48, and differ when the body is run.
Final source locals/world/ex/events/logs/fnLocals, heap observers, target
StateRepr/allocator and caller-stack facts derive from the actual body producer.
The native model uses a conditional Prog plus a value read, not a new
assignment-expression syntax.

A separately inhabited false-guard endpoint case has outer index3, length3:
the SAME represented initial state's unguarded body really rejects, while the
guard returns false without executing it. True endpoint rejection follows the
real material RHS prefix LEFT[T,F,F] to LEFT[T,T,F]. Its Source failure state,
all prefix objects, aliases/world and target prefix allocator/stack survive as
observations. Word/native revert erases the final state; no post-error target
machine, target panic bytes, transaction rollback or executed suffix is asserted.
Source horizon1 cannot read the guard; at horizon2 false skips this body and
true times out in this body. These are horizon observations, not minimal-fuel
or public admission limits. General body transport is parametric in fuel.

Exact standard-only axiom guards accompany five core laws and six controls.
Kernel/symbolic-word results do not prove compiler selection, physical bytes,
whole EVM/gas execution, general Source/native lowering, ABI/storage/reference
or recursive graph/deep-copy/liveness/all-profile allocation-failure/final
Source-V10-target closure. Original owned queues and final gates remain open.
