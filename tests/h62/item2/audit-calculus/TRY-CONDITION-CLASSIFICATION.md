# Typed try-condition classification

Guarded regression: exact try/catch characterizations must retain receiver and argument failure boundaries, clause failures, decoder/allocation outcomes and typed heap/scope transport rather than implying successful clause completion.

Complete frozen-selected Solidity/Semantics/TryConditions.lean:four named theorem signatures match frozen/adopted master. Prior1596 rows and owner map unchanged;1600 reviewed/3683 pending of5283;3806 confirmed owners/1477 unresolved. No owner guessed; zero fresh joint witnesses.

tryCall_eq_iff characterizes an arbitrary full typed result, including normal completion and halts. Receiver zero reverts; optional self dispatch uses actual call outcome. Self revert selects other; revertWith tries Error decoder before Panic, then other; primitive panic uses selfPanicCode; remaining halts propagate. External lookup absence reverts; successful return decoding may fail before the success clause; error/panic/other entries select their clauses. Actual clause runs retain failures, scope drops and composed heap extensions. This is the existing non-callback judgement and proves no arbitrary result is feasible.

catchData_eq_iff retains actual catchBytes failure, kind.decode rejection, literal-byte allocation and entire selected body result. Missing/malformed payloads or failures after allocation cannot be promoted into success. Its exact condition is not a separate producer of successful runs.

try_prefix_failure requires actual firstStep error and forwards its exact halt without entering rest. try_prefix_success requires actual firstStep ok out, calls rest on out.st and composes its heap extension. It does not assume continuation success or re-evaluate operands in the original state.

No source/statements/definitions/interfaces/budgets/axioms/exclusions/toolchain changes; no fresh Lean/kernel/replay acceptance or compiler-totality proof. H28 pauses and all STOPs remain. H145 evidence is prepared for private archival, publication pending receipt. Historical unavailable bytes remain UNVERIFIABLE; exact archive-backed duplicate evictions remain restorable.
