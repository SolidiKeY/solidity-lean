# Owner-only integration fragment — NOT APPLY-READY

Historical proposal: this lane has not edited any
original family file, library root, central module map or axiom pin.

After the responsible migration owner repairs the pinned-v4.35.0 Syntax.Raw
closure, V17 must review the additive helper, prove its actual axiom sets and
choose its final module registration. The generated proposal currently imports
`tests.h62.item4.«generic-structuredflow».GenericMapped`. That test module is
not registered in any Lake library; the patch is an unvalidated proof proposal,
not a drop-in migration. `git apply --check` proves textual applicability only.

Suggested integration (not yet implemented): the staged helper is
`tests/h62/item4/generic-structuredflow/GenericMapped.lean`. Its proposed production
module name is `Solidity.Backend.StructuredFlow.GenericMapped`; no production
file at that proposed location is claimed to exist. Move the helper there,
retain axiom prints in a separate test, change the proposal import to
`Solidity.Backend.StructuredFlow.GenericMapped`, register through the repository
coord-tools, and supply this area module-map fragment:

| Module | Purpose |
|---|---|
| Proposed module `Solidity.Backend.StructuredFlow.GenericMapped` | Intrinsic typed mapped Boolean fixture and universal actual-compiler execution lemma; no new Source semantics. |

H82 withdraws the historical exact-file agreement wait for statement-preserving
proof edits. Statement, dependent-definition, interface, budget, axiom-set and
exclusion changes still require the applicable owner/versioned review. The
historical proposal targets these six paths:

- `Solidity/Backend/StructuredFlow/ForBreakCompilerControls.lean`
- `Solidity/Backend/StructuredFlow/WhileBreakCompilerControls.lean`
- `Solidity/Backend/StructuredFlow/ForReturnCompilerControls.lean`
- `Solidity/Backend/StructuredFlow/WhileReturnCompilerControls.lean`
- `Solidity/Backend/StructuredFlow/DoWhileBreakCompilerControls.lean`
- `Solidity/Backend/StructuredFlow/DoWhileContinueCompilerControls.lean`

Ten positive observed/nonzero-frame proof bodies are proposed. All 34 original
declarations in those files retain exact statements; the other 24 declaration
bodies (including all refusals) are byte-identical. Source `joined`/outcome
classification statements and proofs are untouched. Full family inventory
still includes all 179 Controls theorems and all 241 family theorems.

Owner acceptance remains: compile helper and all affected imports, check actual
axiom sets, prove exact instances without weakening, preserve all original
refusals/evaluations, run same-tree fresh-output before/after under identical
bounds, stop if slower by more than 10%, obtain both independent reviews, then
run the repository final gate serially. No root/map/axiom-pin change is made by
this fragment. No adoption or release-completion claim follows.
