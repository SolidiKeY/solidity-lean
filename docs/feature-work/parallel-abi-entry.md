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


## H82 independent cf1 decoder replay

Added `tests/abi-entry/replay-cf1-length.py`, which extracts all 34 saved
legacy/viaIR observations from the first immutable cf1 fixture,
`calldata_array_length_v2.sol`. The generated Lean runtime check invokes
actual `Solidity.AbiEntry.entry` on the saved argument bytes with four inert
selector bytes prepended. It checks acceptance and the dynamic outer length
(or the declared fixed-array length) against the first saved return word.
Nested arrays retain their exact noncanonical input bytes. The first fixture
passed all 34 observations against a freshly compiled current AbiEntry module.
This is a bounded runtime regression, not a new kernel theorem, body execution,
full return-byte comparison or replay of the remaining 41 fixtures.

Initial harness attempts are retained in evidence: Except has no BEq instance,
and fixed-array reference lengths are zero rather than the declared array
length. The latter was a harness projection error, not a decoder/reference
mismatch. The corrected projection preserves all recorded observations.
Finder and skeptic independently caught the fixed-length and malformed-word
issues. Return parsing now validates complete hex word sequences; unexpected
value entries produce test errors, never fabricated semantic fuel failures.
Validation uses explicit exceptions even under Python optimization.

Remaining waits: V11/P6 concrete physical byte-world production; V09/G24.03
statement production; V15 canonical H68 P10 execution endpoints. Whole-decoder
execution is this lane's open G40 producer work, consumed by memory-reference-structs;
it is not a wait on that consumer. These do not prevent
continuing independent G40 controls or G46 branch work. G40 full composition,
remaining fixture replay, G46.02 and G46.03 stay open. No pending exact-file
request for these statement-preserving test additions is retained under H82.


## H82 consolidation intake

The surviving ABI-entry VM retains the existing goal and branch. The listed
predecessor `af9915007218b3213ee500d54bd0b6b0103264d4` is already an ancestor;
newer replay commit `3c20ce40590a18717ab802b516e8f06de9f9b24d` is preserved.
Published master `41f8b61be` was adopted without discarding committed work.
No audit-abi-world final relay exists under the local peer-input directory.
Its final head, authenticated cumulative bundle/checksums, frozen rendered
prompt, exact scope-manifest bytes and explicit stopped/goal-paused
acknowledgement remain an intake wait. No member scope is edited or merged,
no stop requested and no retirement acceptance asserted before that barrier.
The coordinator was asked for the relay; host receipt paths are not treated
as VM-readable files. No original audit scope is inferred from the summary.

Independent checks continue on this lane. Actual Lean/Lake versions and a
fresh successful `lake build Solidity.KeySort` are recorded in the intake
evidence (two jobs, 0.141 seconds shell wall time). This prerequisite alone
is not RUNTIME_GATE_PASS, full checkpoint validation or whole-lane completion.
The first timing wrapper failed because /usr/bin/time is absent; Bash timing
was used for the actual successful run. No known timing STOP was retried.
Retiring-member work is queued only after authenticated intake; original
G40 controls/replay/composition and G46 branch obligations remain open.


## Independent backfill while audit intake waits: exact truncation failures

Extended the existing cf1 generator with eight one-byte truncations, confined
to the saved single-dimensional uint256-array cases. All 34 unchanged saved
acceptance/length observations still pass; all eight derived inputs produce
exactly AbiEntry.entry `.error .revert`, excluding panic, fuel and acceptance.
The zero-length case truncates its length word; nonempty cases truncate the
last required element. Selector bytes remain present. No reference observation
is modified or relabelled and no body/failure bytes beyond decoder empty-revert
classification are inferred. This remains a runtime regression, not a kernel
proof or whole-entry/native correspondence.

A negative test passed an original unmodified accepted vector to the failure
check and correctly failed. Independent finder and skeptic reviews passed
with no findings; neither built, used a Lean server or wrote files. Fresh
current decoder checking took 1.613s and the 34+8 replay took 18.189s (Bash
wall time, serial Lean-j1 under 12GiB virtual-memory limit). Full checkpoint
gates remain pending; no RUNTIME_GATE_PASS is claimed. Retiring audit member
head/stopped acknowledgement and authenticated frozen prompt/scope remain
absent, and its scope remains untouched.


## Second cf1 decoder replay: saved bounds outcomes

The generator now also replays the six saved observations for
`array_exceeds_calldatasize_no_revert_string.sol`: two accepted empty arrays
and four exact empty reverts for lengths one/two with absent element bytes.
These are retained cf1 model observations, not a new solc/EVM run. Each failure
is checked against actual entry `.error .revert`; arbitrary body failures are
not reclassified as decoder failures. Exact fixture path, signature, Boolean
failure field, empty recorded outcome bytes and six/four inventory are checked.
The original 34 acceptance/length observations and eight derived truncations
still pass. All saved JSON bytes remain unchanged.

Fresh current decoder checking took 1.874s and the expanded runtime replay
23.410s. The earlier 18.189s replay had six fewer checks, so these are different
workloads, not a same-workload proof-checking slowdown measurement. No production
Lean proof, interface, definition, axiom or budget changed. Finder passed with
no findings; skeptic requested that the docstring name both fixtures, now fixed.
Both reviews were read-only, with no Lean server/build/write. The remaining
40 fixture files are unreplayed; this is not full body/native correspondence
or a new kernel theorem. Full checkpoint gates and all original proof queues
remain open, and the audit-member retirement barrier remains in force.

## Raw-derived uint view packing

RawUint.Execution now constructs every requested dynamic uint256 calldata view
from the actual frame bytes and proves simultaneous coherence of the finite
family. Requests may overlap or repeat, with no canonical-offset or length
cutoff. The published MemoryOps.CalldataViewPacking producer packs these views;
packedViews_uints derives each logical table lookup, and packedViews_transfer
feeds those values to the existing checked intrinsic transfer under its original
slice and destination bounds. No decoded payload, desired run or poststate is
supplied as a premise.

Controls retain the nonempty-prefix unequal words 7 and 42. Duplicate identities
share keys; shifted overlapping spans and equal offsets with unequal lengths
remain distinct. Independent read-only finder and skeptic reviews found no
semantic issues; their request to scope both control axiom reports was fixed.
New reports use only standard axioms. The stale G34 premise comment now points
to its published structural producer.

This is structural packing and intrinsic transfer, not native execution.
Source raw-reference/logical-key transport, mixed-type and recursive aggregate
coherence, reached-entry demand/guard composition, emitted decoder selection and
whole G40 execution remain open. Standalone missing words still zero-pad; this
does not assert that truncated guarded entries succeed. MRS remains a consumer
of the open whole-decoder result.

### Raw-view checkpoint validation

At source head 90a50be6d711ddc23ddbf812bb62886c3cbccfd0, the checkpoint
touched gate passed in 102 seconds and the library build passed all 6,049 jobs
in 1,482 seconds. Trust passed with 6,468 sources, 289 inventoried sites and
zero findings; orphan, layer, generated-root and fragment checks also passed.
The checkpoint remains failed: documentation paths report four missing
references in other owners' files, and axiom pins report zero errors but
4,483 unrecorded changes. An external proposal records the five new owned
standard-axiom pins; the shared inventory and checker are unchanged.

Independent read-only finder and skeptic reviews verified the exact seven-pass,
two-failure outcome and the five-pin proposal. Actual tools are Lean 4.24.0
(commit 797c613) and Lake 5.0.0-src+797c613; the explicit KeySort build passed
(two jobs). This is not RUNTIME_GATE_PASS, full run-lean validation or whole
G40/G46 completion. No unchanged heavy failed gate is scheduled again.

The old inactive helper cache was consolidated by verified no-overwrite copying
and duplicate-only cleanup; missing input mappings were added after the gate.
Six existing differing mappings were preserved. Cache conditions changed
during this run, so its timing is not a matched-cache before/after comparison.
The canonical retired-member thread-copy transcription remains e270551e; the
unavailable historical 22740ba5 rendering is UNVERIFIABLE under H30/H86 and
is neither claimed to match nor reconstructed.

## Complete cf1 model replay inventory

The existing unchanged runner replayed all 42 immutable cf1 fixtures at source
head fe92bcdeee42369ef7cac013dc0dd2f0141493b9 with pinned solc 0.8.38,
120,000 ms per job, fuel 1,000 and serial Lean under the original memory bound.
The 93-module replay import closure matched its exact current Lake artifacts.
All 42 reports are present: 31 working, 11 blocked, zero broken. Across 55
required pipeline reports, 390 observations match the saved after-baseline
exactly, including 271 successful and 119 failed observations. Neither top-level
nor pipeline classifications changed; the saved fixture SHA256 is unchanged.
Recorded per-fixture durations sum to 440,369 ms, not a compiler timing claim.

The eleven adapter blockers remain: one nominal-enum ABI adaptation, nine
physical calldata/memory assembly adaptations and one value-bearing expectation
format. They are not relabelled as passes or decoder failures. Consequently
the strict comparison exits 1 and all-runtime-working remains false, despite
zero comparison discrepancies. The original full compiled-decoder replay and
whole G40/G46 obligations are still open. These are Source/intrinsic model
observations, not backend compilation, native-EVM, gas or whole-session proofs.

Independent read-only finder and skeptic reviews verified the results and
identified two comparison gaps: provenance needed independent current-source
pins, and pipeline statuses needed explicit comparison. Both were fixed and
confirmed. Four intentional corrupt-report controls now detect uniformly stale
provenance, changed pipeline status, missing pipeline and changed return bytes.
Those controls mutate only disposable copies; they are not source witnesses
or genuine fixture failures. All raw reports, logs, the comparison scripts and
checksums are exported outside Git; fixtures and production runner are unchanged.
