# Raw calldata and access bridge packets

## H151: unavailable historical evidence

The inherited audit archive, member checksum manifest, lost historical run logs
and missing authenticated handoff exports are UNVERIFIABLE. Claims requiring
those bytes remain unproven, and these historical gaps are removed from waits.
The historical launcher rendering remains UNVERIFIABLE; no hash match is claimed
for the distinct authorized thread-copy transcription. Explicit scope approvals
remain operative; a missing full manifest is not reconstructed.

Fresh checks of available code and fixtures are independent evidence with their
own scope. The retained cf1 decoder subset does not replace a full fixture replay,
old audit timing, archived gas/fork observations or whole-decoder execution.
The pinned Mathlib cache is a toolchain input, not historical proof evidence.
Its delivery and unpacking do not discharge the original G40/G46 or audit obligations.

## Typed uint sequence agreement

`Solidity/Backend/AbiEntry/Consumers.lean` retains the existing byte-derived
fixed/dynamic uint view packing and checked intrinsic transfer. The new
UIntViews.semantic_uint_sequence theorem derives typed contents from the
actual semantic reader at every wrapped address, for every input, starting
index, count and fuel. Empty sequences succeed at every fuel; nonempty
sequences succeed exactly when count+2 is at most the fuel. All other cases
retain Fail.fuel. No decoded payload or successful run is supplied as a premise.

The sequence observation uses casesOn with a motive generalising both shape
and length, preserving Gate G0. Controls cover empty sequences at zero fuel,
insufficient fuel, unequal words 7 and 42 after an unaligned nonempty prefix,
and zero-padded reads from empty input at arbitrary starting addresses. The
empty-input proof simplifies missing bytes before reducing arithmetic; no
recursion or heartbeat limit was increased. Per-file diagnostics report zero
errors and warnings. Six scoped axiom reports are standard-only: the observer
has no axioms, and the theorem/controls use propext and Quot.sound.

This is standalone semantic traversal. Entry span/offset checks, reached
Source-reference/key transport, recursive mixed-element decoding, actual
compiler selection, native execution and full G40 composition remain open.
MRS still awaits this lane's whole-decoder execution result; this increment
does not supply it.

## Charged storage access

AccessBridge.Storage inhabits the StorageAccessCertificate contract using the
existing P10 decoder and actual charged driver. Its general SLOAD, TLOAD,
SSTORE and TSTORE laws retain every gate error, native account/transient update,
protected stack tail and low-fuel boundary, plus positive-fuel X continuation.
No desired run, successful gate or account-presence premise is supplied.

Concrete kernel-checked controls retain unequal persistent/transient payloads,
older stack words, exact read gas/PC/execution counts and actual gas/stack/static
and stipend refusal ordering. A separate control preserves the pinned behavior
that a write to an absent account does not create it; this is no new admission
restriction or claim of compiler correspondence.

Storage/hash dependencies remain separate from calldata/memory interfaces.
Symbolic compiler-slot transport, approved collision-premise realization,
transaction-end reset, frame rollback, Source/native origin and the full pass
bridge remain open. The delivered cache was verified and unpacked before
focused validation; transport integrity alone is not proof acceptance.

## Recovery and evidence boundary

The lane worktree and off-git evidence were absent after VM recovery. Published
Git recovered exact head dccc7456a0f593a547c282c8f79555b339a751e5; original-base
and published-master ancestry were verified before restoring the assigned
branch. The older clean work checkout was preserved. The lane fast-forwarded
to 05d2c25872c4bb963a0ca7f605905e6e1e99eedc; root registration was unchanged.

The interrupted checkpoint last reported library progress 5560/6134. Its raw
logs and later cache shipments are missing; no completed library or final gate
pass is claimed from that attempt. The operative retired-member prompt was
recovered and its authorized e270551e688138623f77863ab6253c6f770f357df01d42b98f846983b5bd5f9c
hash verified. Historical rendering 22740ba5 remains UNVERIFIABLE; its bytes
were not recreated.

Immediately after recovery, the cache had zero Mathlib ltar files. A bounded 23-root cache request
failed all 985 downloads with CONNECT 403; a single Docker-default-proxy probe
failed likewise. Both failures are retained. Cache restoration was then a named dependency; that wait is now resolved
by the verified relay and focused checks above. Neither the earlier failure
nor transport integrity alone establishes a proof or gate pass. The recovered core consumer import
closure was rebuilt; after reconnect lost the outer completion receipt, a
cached confirmation exited zero and reported 202 jobs in 0.266 seconds. That
confirmation time is not a cold-build timing or a matched performance claim.

Actual tools are Lean 4.24.0, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b,
and Lake 5.0.0-src+797c613. The owned helper retains the 12 GiB/no-swap cap,
LEAN_NUM_THREADS=1 and explicit Lean -j1. Checkpoint gates and final reviews
will be recorded with their actual outcomes. No RUNTIME_GATE_PASS or
whole-lane completion is claimed.

## Core checkpoint handoff

The new proof reuses AbiEntry.load_lt, W_eq, cval, celem and cseq directly.
It assumes no unfinished producer result. Existing decoder, dispatch and body
interfaces and all prior consumer statements remain unchanged. Independent
read-only finder and skeptic reviews found no issues in the actual proof,
controls or documentation; neither reviewer used Lean or edited files.

At the core checkpoint, the storage proposal was preserved in a scoped Git
stash and exported bundle outside that checkpoint tree. The dedicated module
is now present as the separately checked signature-only interface above.
Full checkpoint gates run after the core commit so their receipts identify the
exact tested head. The original G40/G46 queues and inherited audit validation
remain open; component success does not establish whole-lane completion.

## Completed local checkpoint and master adoption

The checkpoint on 6c5b823616dc0738216536f23edcf19bb7d9410b has finished.
The library build passed in 22044 seconds; layers, affected-module compilation,
trust, reachability and generated roots passed. The overall checkpoint exited
one: README fragment ordering was stale; the unrelated audit-evm-compiler
check_scope.py cited two missing synthetic paths; the central axiom inventory
reported 91 unrecorded changes with zero axiom errors. These are retained
failures, not a full gate pass. The earlier Node PATH failure is also retained.
No unchanged heavy gate is rerun, and no RUNTIME_GATE_PASS is asserted.

After the job released its writer lock, the assigned branch fast-forwarded to
published master 7ab10c15f81e0f3fec56a34f7ab996a9b755e498. Regenerating library
roots made no changes. These local gate results identify the earlier tested
head; they are not relabelled as validation of the adopted master.

The coordinator again authorized the three dedicated StorageInterface,
Storage and StorageControls modules under AccessBridge. The authorization is
recorded as an additive scope amendment; the missing authenticated full live
manifest is not reconstructed. The signature proposal remains preserved in
stash 300c05142654e541924567516f7e659c5e4444d7 and an exported bundle. That
earlier cache wait is superseded by the focused interface validation above.

The four standalone census tests and four portable checksum regression tests
pass. They do not authenticate the missing inherited archive. The broad Python
discovery failure is retained because artifact-dependent acceptance scripts
require their original inputs and CLI arguments. Historical missing bytes and
performance receipts are not recreated or reassigned to the current head.

## Array container composition

UIntViews.semantic_uint_containers reuses the typed byte-derived sequence in
the actual dynamic and fixed cval constructors, for every raw input, base,
count and fuel. Success requires positive fuel and either an empty container
or at least count+3 fuel. Fixed arrays ignore the arbitrary runtime length exactly as
the semantic decoder does. The same indexed sequence witnesses both forms;
no decoded payload, successful run or canonical layout is assumed.

Boundary controls distinguish empty containers at fuel zero/one and one-element
containers at fuel three/four, including arbitrary fixed-array runtime length.
The general theorem and derived one-element control use only propext,
Classical.choice and Quot.sound; the empty-container control is axiom-free.
These additions do not provide compiler selection, Source object transport,
native execution or whole-decoder dispatch/body composition. Those original
G40 obligations remain open. Evidence is archived privately under H145.

## Raw uint body outcomes

`UIntBindingBody.raw_executed` relates semantic single-uint entry to the publicly selected decoder/binding/body program for arbitrary bytes, uint widths and supported typed bodies: failure prevents body execution; success preserves its result, including revert/fault.
The fuel+2 boundary and initial word/size representation premises remain explicit; no successful decoding or desired execution is assumed. Recursive aggregate compilation, physical calldata loads, whole entry dispatch and Source-to-runtime correspondence remain open G40 obligations for memory-reference consumers.
