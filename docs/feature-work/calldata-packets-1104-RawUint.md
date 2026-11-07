# Raw calldata and access bridge packets

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

## Storage work awaiting dependencies

The approved storage interface is prepared as generic read/write opcode
families over the existing P10 site and driver, retaining gate errors, actual
state updates and separate driver fuel boundaries. It remains an unvalidated
proposal outside the lane branch tree while the pinned Mathlib cache is unavailable. No
certificate inhabitant, symbolic-path transport, reset/rollback or full pass
bridge is claimed. Existing interface statements are unchanged.

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

The restored cache has zero Mathlib ltar files. A bounded 23-root cache request
failed all 985 downloads with CONNECT 403; a single Docker-default-proxy probe
failed likewise. Both failures are retained. Cache restoration is a named
dependency, not a proof or gate pass. The recovered core consumer import
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

The storage proposal is preserved in a scoped Git stash and exported bundle;
it is outside this core checkpoint tree and still needs dependency validation.
Full checkpoint gates run after the core commit so their receipts identify the
exact tested head. The original G40/G46 queues and inherited audit validation
remain open; component success does not establish whole-lane completion.
