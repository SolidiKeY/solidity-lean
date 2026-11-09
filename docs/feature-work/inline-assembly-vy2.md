# Physical storage/memory assumptions

[Authoritative source](../../Solidity/Yul/Views).

Separation is local to the represented live ranges and demanded slot/hash preimages; do not assume global address/hash injectivity. Packed complements, dynamic ownership changes and residual bytes must survive the same actual writes. Ordinary heap preparation does not establish whole-store layout or a physical allocator. The [approved assembly scope](inline-assembly.md) governs any expansion.

<a id="dynamic-full-width-array-writeback-2026-10-31"></a>

<a id="simultaneous-heterogeneous-struct-writeback-2026-10-31"></a>

<a id="canonical-array-element-families-2026-10-31"></a>

<a id="retained-array-element-family-resizing-2026-10-31"></a>

<a id="canonical-scalar-memory-extension-2026-10-31"></a>

<a id="canonical-compatibility-and-genuine-aliases-2026-10-31"></a>

<a id="joint-ordinary-memory-writeback-2026-10-31"></a>

<a id="finite-owned-memory-inventory-2026-11-01"></a>


### H171 accepted import cost and H189 Horizon disposition

H171 accepts only the reviewed NestedMappingLayout import-cost increment,
superseding H164 Option A for that increment. The recorded matched external
candidate check gave median 0.38 s baseline versus 0.82 s (+115.8%), peak VmHWM
458,176 versus 1,089,336 KiB, on serial Lean4.24 with 12 GiB/no swap and a
300-second per-file bound. This is accepted cost, not speed neutrality.
Production retains the isolated SourceGraphEndpoints module; its registration
includes it in the full-library build. Ordinary integration gates remain required.

H189 separately releases the H125 Horizon timing STOP only. It does not certify
current Source checking, cache equivalence, any Lean/full gate or runtime result,
and changes no existing budget. No separate VY2 Horizon failure is asserted here.
Any concrete failure must retain its exact source/gate identity and validation
hold; a missing historical receipt is not a current measurement or a new STOP.

The endpoint proves slot identity only. Y04 physical adequacy and reached-state,
memory agreement, Source/Yul/compiler composition and full affected validation
remain open. H171 and H189 supply none of those obligations. All statements,
imports, premises, exclusions, interfaces, axioms and budgets remain unchanged.

Historical evidence stays private under H145. Missing historical h69 artifacts
remain UNVERIFIABLE under H151; the 23 original frozen obligations receive zero
original proof credit without checked original-type/premise correspondence.
Both preserved commits remain in Git history; the historical narrative is not
restored as current guidance. This reconciliation is comments/documentation only
and is not a validation, producer-completion or integration receipt.

R3 permits the additive `PhysicalByteWorldV2Interface` and `LoadV2Producer` split
next to frozen v1. Both current owners reviewed the exact names, signatures
and import direction. The interface keeps every v1 address, capacity, initial
32-byte-image and WordFrame premise, with the separately named `LoadV2.run`
endpoint. The concrete instance uses the existing cell-indexed PUSH/MLOAD code.
Controls construct an actual written high-word image and preserve a nonempty
tail; low-byte substitution and bare MLOAD on an empty stack are rejected.

This point-load contract does not realize frozen v1, migrate a compiler endpoint
or establish Y04 physical/reached-state adequacy. Actual compiler selection,
emission, Source origin, whole-program compatibility, gas/resource correspondence
and full affected validation remain separate obligations.
