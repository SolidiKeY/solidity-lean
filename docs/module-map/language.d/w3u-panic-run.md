| `Semantics/Panic/Run/Loop.lean` | Panic-carrying loop execution, termination witnesses, induction and exact failure propagation. |
| `Semantics/Panic/Run/Calls.lean` | Typed call arguments, internal frames, external outcomes and lazy self-catch dispatch using the actual callee code. |
| `Semantics/Panic/Run/Control.lean` | Panic-carrying conditions, assertions, sequences and loops; assertion-origin and actual-code trust links. |
| `Semantics/Panic/Run/Tests.lean` | Countdown, nested failure, skipped-branch, external-panic-byte and resource-halt regressions; exported Run proof API checks. |
| `Semantics/Panic/Run/Checked.lean` | Typed compound arithmetic and increments with sound local V1 projections. |
| `Semantics/Panic/Run/Updates.lean` | Panic-preserving storage, memory, local and array updates. |
| `Semantics/Panic/Run/UpdateProofs.lean` | Update failure ordering, capacity exhaustion and actual empty-pop origin proofs. |
| `Semantics/Panic/Run/UpdateTests.lean` | Update API availability and concrete compound-arithmetic panic-code regressions. |
| `Semantics/Panic/Run.lean` | Complete panic-carrying statement and program execution, separate from V1. |
| `Semantics/Panic/Run/Receivers.lean` | Storage-returning calls and deferred operands with exact failure propagation. |
| `Semantics/Panic/Run/Data.lean` | Rich revert-data evaluation, byte literals and actual-outcome catch-data execution. |
| `Semantics/Panic/Run/Contracts.lean` | Full-run failure propagation, actual assertion origins and self-catch code/resource contracts. |
| `Semantics/Panic/Run/RunTests.lean` | End-to-end self/oracle code distinction, external calls, resource failures, loops and catch-data regressions. |
