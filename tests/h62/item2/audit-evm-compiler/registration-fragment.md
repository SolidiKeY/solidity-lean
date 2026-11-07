# Registration fragment for coordinator review

No generated root, module map, core list or axiom pin was edited. These helpers
remain under the authorized tests prefix until area-owner-approved registration:

| Helper | Imports | Purpose |
|---|---|---|
| LayoutAudit | Solidity.Evm.Layout | Five joint-impossibility controls and individual occupancy witnesses |
| SuccessAudit | Solidity.Evm.Examples | Nonempty success, exact failure, four trivial-output controls |
| JointWitness | JointImpossible | Full dependent-telescope supplied-witness checking and ambient-assumption rejection control |
| JumpdestAudit | JointWitness, Solidity.Backend.Jumpdest | All 19 joint inputs and concrete byte-boundary controls |
| JointImpossible | Lean | External audit-only kernel-checked joint-impossibility command; no core import |
| IntentionalAudit | JointImpossible and frozen EVM modules | Eighteen H69 intentional joint-impossibility audits |
| OpcodeAudit | Solidity.Backend.Opcode | Sixteen joint input packages, two closed statements, total encoding and failure controls |
| HeadlineAudit | Solidity.Evm.Correct, SuccessAudit | Joint witnesses for five unchanged headlines and conditional generic success transfer |
| JointRefutation | JointImpossible | Definition-hidden Not inputs, full H69 joint refutation and checked guards |
| RefutationAudit | JointRefutation and frozen memory examples | Twenty-nine intentional refutations/separations with source reasons |
| JointFromCertificate | JointWitness | Complete joint tuple inferred from a closed existing certificate; unresolved-input rejection guards |
| EntryAudit | JointFromCertificate, Solidity.Evm.MemoryCallExamples | Ordinary Compilation.correct joint witness for nonempty allocation/internal-call program |
| InputFixture | Solidity.Evm.Compiler, Lean | Safe correlated audit fixtures from exact closed public Input certificates, with rejection guards |
| SelectorAudit | InputFixture, JointWitness, five frozen memory example modules | Five ordinary compiler selector-equivalence joint input packages |
| CopySelectorAudit | InputFixture, JointWitness, read-only copy/fixed-memory examples | Five complete premise packages; includes explicit copy-free guard and output-data equivalence without Rep/success claims |
| LoopSelectorAudit | SelectorAudit, Solidity.Evm.MemoryCompileExamples | Remaining five Compiler joint premise packages; nonempty loop certificates and arbitrary typed construction output, without Input/Room/Rep/success assertions |
| CheckedEntryAudit | HeadlineAudit, read-only Backend.Payments.EntrySuccess | Actual checked-entry admission/storage-write success and four excluded outputs for one intrinsic fixture |

The metadata inspector imports Lean only as an external tool. It is not part
of the dependency-free intrinsic core.
