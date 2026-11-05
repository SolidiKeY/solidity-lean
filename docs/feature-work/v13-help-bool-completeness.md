# G21 arbitrary literal-list selector completeness

The helper branch was rebased onto published master
27edf590 (full published revision in the sealed interface). No relevant
BoolErrorLowering/LiteralFailureLowering dependency changed since the preceding
checkpoint. Old commits and immutable seals remain preserved.

New modules: Solidity.Lowering.V08.BoolErrorCompleteness and
Solidity.Lowering.V08.BoolErrorCompletenessControls. Coordinator registration
only; Solidity.lean is untouched.

arguments_complete proves by actual indexed argument recursion that every
BoolErrorLowering.arguments list is selected and recovers the entire same
boolean list. emit_complete then proves selection of the actual intrinsic
custom-error statement for arbitrary E/context/declaration and every literal
list, retaining the declaration paramTys equality. No successful selector or
decoder result is a premise. emitted_complete derives exact existing Slice
execution of code obtained from the actual Option, retaining Fits and two
stack slots. There is no fallback-empty-code vacuity: emit_complete proves
some actual code. These theorems close supported-family completeness left
conditional in BoolErrorStatement.selected_correct. They do not add support
for runtime-local/effectful arguments or alter source admission.

Controls uniform_selection and uniform_client quantify over every literal
list using the actual typed declaration and populated published Source
caller/state. uniform_client proves the existing source result at the
original bits.length+extra+4 horizon and exact selected target code result.
Fits remains explicit for arbitrary lists; the old populated three-bit
fixture already discharges it. Empty and 64-element controls establish
selection only, not arbitrary target capacity or native gas adequacy.
No prior bytes/expected observations, profiles, exclusions, fuel/proof/node
budgets or semantics changed. Existing selected outputs equal the previous
emitter exactly; no new external compiler/EVM vector is claimed.

Automation was tried first. The indexed induction remained necessary;
simp only closes actual selector reduction. Initial syntax mistakes are kept
in raw evidence. Complete final per-file MCP diagnostics pass both files.
Focused toolkit checks and actual scoped axioms accompany the seal.
Independent read-only finder and skeptic review source and exact artifacts,
without Lean/build/server use. No full/Suite historical failed gate is retried.

All full G21 and original G40/G41/G42/A/B obligations stay partial. Unknown
runtime memory encoding, native/source/target ABI dispatch, arbitrary calls,
world/resource/transaction composition and final whole-lane gates stay open.
Published P1/P2/P3/P6/P10 interfaces do not discharge execution linkage,
profile provenance or source-origin facts automatically. P3 and G42.03 remain
readonly-external work; no reserved modules changed. Historical Suite124,
full1, cold124, bodyexport1, failed MCP attempts and raw docs1/frozen comparison1
remain failed. Prior/publication finding equality remains a separate gate.
Goal identity/status unchanged; no goal administration or publication.
