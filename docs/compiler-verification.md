# Compiler correctness boundary

The approved target is full source-to-executable-EVM correctness. Current
fragment theorems do not establish that endpoint. The compiler entry point and
its certificate constructors are in [Solidity/Evm](../Solidity/Evm/); their
statements, admission checks and tests define the supported fragment.
The final obligations are in [coverage-plan.md](coverage-plan.md).

## What is proved

`Compiler.Compilation.correct` relates admitted typed execution to the
repository's machine under the selected constructor's input/output relation.
Do not substitute this for source admission, solc bytecode equivalence,
physical layout agreement or a gas/fork theorem.

## The machine

The core machine is word-addressed. Its model assumptions differ from an
executable EVM; physical byte layout, actual resource charging and the selected
fork need their own checked bridges. Hash results remain conditional on the
explicit hash-model premises; no collision-free cryptographic theorem follows.

## Memory operations

Allocation capacity is an input theorem premise, not a runtime check inserted
by the fragment compiler. Preserve the admitted allocator, live-object
separation, reserved frame, cursor and successful-prefix capacity conditions.
An earlier revert owes no capacity for unreachable allocations. Different
compilation paths have different state relations; composing them requires the
actual preservation evidence, not just a successful admission check.

## Memory-storage-copy recovery checkpoint

Current admission, copy-independence and tail behavior are defined by the
compiler branches and their tests. Historical recovery steps and gate receipts
are retained in Git, rather than presented as current support evidence.
