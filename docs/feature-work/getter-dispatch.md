# Getter targets in finite dispatch admission

Integration status (2026-10-26): included in the shared checkout. Current
combined validation is tracked in [integration.md](integration.md).
Worker handoff statuses and isolated validation results below are historical;
they neither report the current combined checks nor establish full source support.

Native external dispatch now includes synthesized public getters through
`fnExternalEntry`. The source boundary must include the same entries before
claiming its typed candidate set overapproximates native dispatch. This repair
constructs getter candidates from the actual synthesized getter function's
primitive parameters and results, after its getter plan and source identity
have succeeded. Getter declaration IDs join the ordinary call dependency graph;
their stored source scope is the getter declaration header, not its mutable
initializer. Initializers still execute only for deployment.

Getter candidates retain source address/uint/byte kinds separately from their
native dispatch key. A native-compatible getter with a different source kind
rejects the dynamic call, rather than disappearing because it was originally a
VariableDeclaration instead of a FunctionDefinition. Generated getter model
names may differ from source names only because a validated SourceCallable.getter
identity supplies the real selector. Internal dynamic calls skip getters,
matching SourceFunction.internalValue and native fnInternal. Existing direct
static getter calls and self calls use their existing path unchanged.

This is a conservative extractor repair, not a source/native simulation theorem.
Unsupported or malformed getter plans remain explicit unknown candidates for
external dynamic dispatch. Such a contract's dynamic external calls are refused
with solidity.functionDispatch until an exact representable signature is known,
even when an unrelated ordinary target would otherwise be usable. Unrelated
static calls retain their admission behavior. The repair neither shortens
reference-valued getters nor guesses missing metadata, and it does not alter
ordinary identity metadata, operator dependencies, helper flags or whole-contract
transient-storage refusal.

## Review and validation

Worker handoff (historical): **patch_ready_unvalidated**. Prepared in a temporary artifact lane with
no shared-checkout writes, lock changes, Lean server, build or proof execution.
Only the new JavaScript test's syntax was checked by that preparation worker;
current combined validation is tracked in integration.md.

The production-import regressions require compatible primitive dynamic getter
calls and ordinary external calls alongside matching getters to remain proved;
an internal call with an address-key getter remains proved because the getter
is not an internal target. Negative admission checks cover mapping-key and
return address/uint collisions, unsupported getter results, malformed selector
and absent type metadata. A mutable initializer using excluded block.number
must affect deployment while an ordinary dynamic getter entry stays admitted.
All malformed-data checks go through the actual solc_import command and its
production source/specification callbacks.

After applying, diagnose Contract alone, rebuild the frontend and run:

    node --test scripts/getter-dispatch.test.mjs
    node --test scripts/public-getters.test.mjs
    node --test --test-name-pattern='function types:' scripts/test-solidity.test.mjs

Keep every positive verdict expectation. The coordinator owns Lean diagnostics,
source execution checks and a final read-only finder/skeptic review.
