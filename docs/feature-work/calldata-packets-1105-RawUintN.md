# Raw uintN calldata-to-memory packet

The additive modules
[`RawUintN/Execution.lean`](../../Solidity/Backend/CalldataPackets/RawUintN/Execution.lean)
and [`RawUintN/Controls.lean`](../../Solidity/Backend/CalldataPackets/RawUintN/Controls.lean)
reuse the published raw uint256 packet and Source operations without modifying
them. V11 integrates this bounded packet. Both proof modules are published in
master `3ad22f66d8fc6431378c22e71823436c79dede7f`, byte-identical to the original
reviewed packet. Their root imports and standard-axiom inventory are registered
upstream. This remaining increment contains only the owning documentation and
test-support inventory/automation goal. No global roots, map rows or trust
inventory are edited locally. The earlier failed local checkpoint remains
failed; coordinator publication and combined gates do not retroactively change
that local receipt.

## Contract and proved behavior

`Width` intrinsically requires byte alignment, at least eight bits and fewer
than 256 bits, exactly uint8 through uint248. `Width.intTy` constructs the
existing Source integer type. `element` tests the exact integer range and
constructs a dependent integer value only on success. `range_iff` proves that
this test is precisely `w < 2^bits`. `decode_raw` proves agreement with the
actual `Source.decodeWord` on the actual `cdWordAt` bytes. The independent
32-byte bound rules out an implicit uint256 modulo assumption. High bits are
refused, not masked to the narrower width.

`values` computes the ordered runtime-length decoder traversal; `memory`
constructs its existing typed Source array representation. `copy_run` gives
the full result of the actual `Source.cdToMem` for every frame, offset, length
and initial state. Success allocates exactly that computed array at the prior
`heap.next`; failure preserves the entire state. `dirty_copy` proves this
refusal for a dirty element at any index. `copy_success_iff` characterizes
success by every requested raw word being in range; there is no supplied
decoded payload, desired successful execution or poststate premise.

`copy_state` preserves locals, all nonheap fields and every heap address other
than the initial allocation address. It does not claim preservation of an
arbitrary existing object at `heap.next`. `empty_copy` still allocates an empty
array. Standalone byte reads retain zero padding. `guarded_run` composes the
unchanged `cdTail` entry check before element decoding and preserves its exact
refusal. Its separate `data` and `F` arguments alone are not a calldata-coherence
premise: the positive/dirty entry fixtures explicitly use selector-prefixed
frames built from those same argument bytes. Strict entry bounds are distinct
from standalone padding.

`copyExpr`, `implicit_copy` and `eval_copy` use the existing resolved local
implicit conversion. The only local representation premise is the actual
calldata reference/offset/length; fuel is the existing two-step horizon.
No public compiler selection, generated opcode, external EVM or whole-world
adequacy follows from these Source-machine component laws.

## Controls, checks and review

The [control inventory](../../tests/calldata-packets-1105/RawUintN/README.md)
includes inhabited clean and dirty width boundaries, unequal/order controls,
existing heap prefix, padding, partial-byte refusal, empty allocation,
coherent dynamic entry, strict entry refusal and zero/one-horizon exhaustion.
Axiom reports are pinned with `#guard_msgs` to only `propext`, `Classical.choice`
and `Quot.sound`; no sorry, new axiom or native trust shortcut is used.

The first inline implicit certificate exceeded the unchanged default heartbeat
limit. An explicit `STy.same_refl` lemma removed the repeated normalization;
the subsequent per-file check took 1.52 seconds. A direct concrete entry
normalization exceeded the unchanged recursion limit; separate kernel-decided
word/length facts resolve it without increasing either budget. Failed attempts
remain failed in the retained evidence. Final focused module builds take under
60 seconds (execution 1.8 seconds; controls 4.4 seconds reported by Lake).
The serial whole-group limits remain 12 GiB, no swap and 4 GiB host reserve.

Independent read-only finder and skeptic found no range/state/coverage defect;
both require the explicit Source-only and generic-entry-coherence boundaries
recorded above. Neither ran a Lean server or build. Final-head review identities,
source hashes, all terminal commands/timings/resources and any gate failures
are recorded in the sealed handoff. Required commands are per-file diagnostics,
`gate.sh touched` and `gate.sh checkpoint`; registration-related failures cannot
be silently waived because global generated files are outside this packet's
exclusive scope.
