# ABI-entry owner follow-up: H70

## Published dependency adoption

On 2026-11-06 this lane adopted published master
`5f7bb1441566aaad64a34436904afc61de762fd2` by rebasing its existing assigned
branch. The previous accepted head `211c7adf640e7b503de0c381c9918cdf56a6ae8b`
is an ancestor. Registration was regenerated without a source delta.
This checkpoint records dependency inspection only; it adds no Lean implementation
and does not complete G40, G46.02, G46.03 or an H68 bridge factory.

## H70 owner routing and exact remaining boundary

The coordinator supplied the H68 request inline, originating at H55/G49 head
`62377f3165a36dbc608e6ce553a9a750c8281fdc`. That object and its named JSON
attachment are unavailable in this checkout. The attachment checksum has not
been verified. Searching tracked Lean sources under Solidity and
Bridge/SolidityBridge found no `PassCorrect`, `Behaviour.ofLang`, `BridgeGoal`
or `p10_execution_bridge` declaration. The published roadmap contracts in
[Contracts](../../Solidity/Roadmap/Contracts.lean) provide Lang, Pass, Cert and
RefinesUnder; these are not silently substituted for the requested factory.

V15 owns the complete P10/G46.06/G47 factory. Its requested canonical opcode
languages, exact artifact/program endpoints, fixed environment abstraction,
independent resource calculation, approved native context and operational
observation equations remain required published inputs for this consumer.
H55/G49 owns integration of the full-package route. This lane retains ownership of the
G46.02 memory/calldata and G46.03 storage branch proof obligations; the ticket does not
transfer the complete P10 factory to this lane.

Existing reusable branch contracts include
[MemoryAccessCertificate](../../Bridge/SolidityBridge/AccessBridge/MemoryInterface.lean),
[charged MLOAD linkage](../../Bridge/SolidityBridge/AccessBridge/MemoryLoadExecutionInterface.lean)
and [byte-world linkage](../../Bridge/SolidityBridge/AccessBridge/ByteWorldInterface.lean).
Their local antecedents, all gate failures, zero/one fuel failures and
continuations remain intact. They do not establish complete session adequacy,
source-origin or a full-certificate factory. No assumed certificate, desired
run or narrowed approved domain is introduced by this checkpoint.

The existing [HostWriteControls](../../Bridge/SolidityBridge/AccessBridge/HostWriteControls.lean)
contains `charged_initial_image`, `charged_accepted` and
`charged_post_refused`: an initial P6 byte image admits an actual charged
MSTORE8 step at offset 2^64, yet its reached native memory fails the P6
writeSpan image. This retains the real host writer mismatch. It obstructs
unrestricted store-image preservation; it does not prove that the witness
has an approved Source origin, or refute an H68 factory whose canonical
Approved context has not been published. No writer repair or exclusion is
claimed. Nonzero copies, general store images and G46.03 storage remain open.

G40 still requires full entry/source/physical composition for the approved
profile and fixture replay. P6 concrete byte-world production (V11), G24.03
statement production (V09), P1 profile closure and Source admission remain
explicit dependencies where used; this note grants no replacement premise.
Independent work on the original queue remains open, so this checkpoint is
partial rather than a claim that the entire lane is blocked.

## Validation and review

This is a documentation-only checkpoint. Registration and documentation path
checks are recorded in its sealed evidence. No Lean build, axiom audit or
runtime gate was run for this note, and no RUNTIME_GATE_PASS is asserted.
Independent read-only finder and skeptic reviews are recorded below before
sealing. Historical full-gate receipts are not new validation of this head.

Finder and skeptic independently checked the source/theorem boundaries and
relative links without builds, Lean servers or writes. Both requested the
ownership wording above so open G46.03 obligations cannot read as completed
proofs; this was corrected. Their owner-routing check relies on the supplied
coordinator ticket, not independent authentication of its absent attachment.

Registration passed. The global documentation path check failed because
`docs/feature-work/after-roadmap-va1.md` references an absent Mathlib test
source in the local optional-package checkout. That file is outside this
lane; the raw output is retained. All five relative links in this new note
resolve. This external path-check failure remains recorded, without a full
gate or runtime pass claim.
