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


### H171: accept the reviewed import cost with fresh bounded checks

H171 Option B supersedes the earlier Option A for the reviewed
NestedMappingLayout import increment. The exact historical patch was applied
only to an external candidate copy; production retains the existing isolated
SourceGraphEndpoints module and contains no duplicated declarations. Three
alternating matched checks on the same Lean4.24/cache/cwd/serial wrapper gave
median baseline 0.38 s versus candidate 0.82 s (+115.8%), with peak VmHWM
458,176 versus 1,089,336 KiB. Emission was disabled for both candidate copies;
the Docker limit remains 12 GiB with no swap and a 300-second per-file bound.
This cost is accepted specifically under H171, not under the usual 10% limit.

Fresh checks of the retained endpoint and its existing joint declaration and
wrong-root refusal controls pass, with the same standard axiom dependencies.
No existing declaration, proof, interface or budget changes. Documentation and
applicable static gates remain required, as do ordinary integration gates;
these checks do not assert a full build, cache equivalence or physical adequacy.
The independent Horizon STOP remains and no unchanged Horizon check was rerun.
Raw matched measurements, candidate/base source bytes and source identities are
private H145 evidence. The decision is acknowledged through the private inbox
once this bounded work and its available gates are recorded.
