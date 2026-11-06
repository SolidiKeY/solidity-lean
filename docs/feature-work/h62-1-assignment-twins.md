# H62 item 1: assignment twins

Base: `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. This is a preparatory census, not a completed refactor or proof gate. Run `python3 scripts/h62/item1/assignment-twins/census.py` for the line-numbered declarations and explicit pipeline branches, and `python3 scripts/h62/item1/assignment-twins/test_census.py` for the frozen inventory check. The scanner is syntactic and does not parse Lean; the semantic accounting below was reviewed separately. Hashes in scanner output pin the six inputs.

## Declaration accounting

Each pass contains `value`, `reached`, `reached_value`, and `execution`: addition and multiplication abbreviate subtraction's `reached`, while subtraction defines it. The controls share the following declarations, all of which must remain available with their original types and attributes: `C`, `A`, `Γ`, `F`, `target`, `bases`, `machine`, `i`, `a`, `source`, `initial`, `compiled`, `operand`, `input`, `application`, private `successMachine`, irreducible `after`, `prefix_run`, `resultWord`, `code`, `emitted`, `source_execution`, `cells`, `complete_observations`, `different_pipelines`, `stale_rhs_refused`, `short_frame_refused`, and `corrupted_saved_tail`. Addition and multiplication also have `si`, `ti`, and `family`. Multiplication additionally has `unmasked`, `unmaskedCode`, `actual_unmasked`, and `unmasked_differs`; subtraction additionally has `reversed`, `reversed_source`, and `wrong_order_reverts`. The scanner records all 4 + 31, 4 + 35, and 4 + 31 declarations respectively, including private and attributed definitions.

## Semantic case and statement accounting

* Each `value` and `reached_value` has legacy and viaIR cases. Captures use `x` and `y` in legacy and `x` and `x` in viaIR. Preserve the differing operand order and the exact dependent values and evidence, not merely the resulting arithmetic.
* Addition and multiplication use unsigned widths satisfying divisibility by 8 and bounds 8 through 256, wrap the result, require the original `IntegerLocalFamily`, and return its updated form. Their source evaluation explicitly sets `checked := false`. Subtraction accepts general `Source.IntTy`, original individual source and target reads, arbitrary `SF`, and the explicit result-range premise `hz`; it returns the unwrapped integer. These premises and conclusions are not interchangeable.
* Each `execution` retains source result and state update, `IntValueRel`, actual compiled prefix and operand, original compilation input, representation, empty canonical stack, mapped output and both separate and concatenated runs for every stack tail. Addition and multiplication additionally retain the updated family. These are proof statements, not claims about external EVM or solc testing.
* The common positive controls quantify both pipelines via `p` and use `cases p`; the negative controls have the individual pipeline scopes stated below. Addition and multiplication use `x=255`, `y=1` in u8 with unchecked execution: legacy/viaIR results are 0/254 and 255/1 respectively. Subtraction uses `x=9`, `y=7`, gives 2/0, and quantifies both checked Boolean values. Addition and multiplication `family` cover both Boolean selectors and all four selector pairs.
* Each control's `successMachine` distinguishes `.ok m 0` from all other outcomes; `prefix_run` handles `.ok` with zero and successor residual, `.revert`, and `.fault`. `after` is irreducible. Preserve arbitrary tails, the separate `prefix_run`, `emitted`, and `source_execution` statements, and all observations. `complete_observations` concerns the selected 11 cells `[0,1,2,3,4,5,16,63,128,129,130]` and stack, not all memory or world state. Each file separately compares the two pipelines, refuses a specific stale RHS in viaIR, refuses a five-slot frame for either pipeline (requires six), and refuses a specific corrupted saved tail in legacy.
* Multiplication's raw viaIR `mulW` produces 65025 and is distinct from the masked result 1. Subtraction separately proves that applying the viaIR value to the legacy reached state reverts and that the corresponding compiled wrong-order sequence reverts for every tail. These are distinct negative controls, not generic claims of failure for all inputs.

## Reviews and handoff

Independent read-only finder and skeptic reviews, without a Lean server, both found the original scanner omitted the three attributed `after` declarations and the dotted constructors in the three value definitions. Both were fixed. The skeptic also identified the outcome cases, shorthand pipeline splits, selected-observation boundary, and stale KeySort statement; the accounting above records those distinctions. A second review confirmed the semantic accounting and found that the first test checked counts only. The test was strengthened to compare declaration names, branch sequences, and source hashes; its negative controls exercise those checks.

The six originals are V09-owned: `Solidity/Backend/Passes/AssignmentAdditionPass.lean`, `AssignmentAdditionControls.lean`, `AssignmentMultiplicationPass.lean`, `AssignmentMultiplicationControls.lean`, `AssignmentSubtractionPass.lean`, and `AssignmentSubtractionControls.lean` (all under that directory). The earlier exact-file request protocol for statement-preserving edits was superseded by H82; the successor live scope and producer boundaries still apply. Shared support, original-file migration, full acceptance, before/after timing, and final review remain outstanding. This assignment-twins lane changed no Lean statement, axiom, sorry, or proof budget. The bounded KeySort prerequisite passed on Lean 4.24.0 at the earlier lane base; it is not validation of this merge head.

## Authenticated scalar-passes successor intake

The successor verified the H82b archive, manifest and checksum-manifest hashes
and all 557 listed files. The delivered frozen assignment, live scope and
verified-final-stop metadata resolve the prior missing-assignment and
retirement waits. Exact stopped head
`7c5de4602fa754ea3c3cca44185ef26098df5ff2` is merged into the original
VY3/scalar-passes branch; no retired worker was resumed at that intake.

Fresh `test_census.py` acceptance passed for the six frozen source hashes,
declaration inventories, pipeline arms and its three mutation controls. This
is source validation, not a Lean proof or timing result. Prior worker runtime
logs and bundles remain separately unverified locally. H82 supersedes the
historical proof-only exact-file request protocol above, but the authenticated
scalar-passes live scope does not transfer the six V09 production originals.
The additive generic-passes support is already merged and should be reused,
not duplicated. Extraction/migration, typed proof validation, final gates and
paired timings remain unfinished; v4.35 dependency/overlay and live producer
boundaries remain binding.

## Frozen-text backfill after master fast-forward

`python3 -B scripts/h62/item1/assignment-twins/check_frozen.py` compares the six files against the original pinned base: declaration headers for theorems, complete text regions for definitions and abbreviations, and selected command lines and their positions. `python3 -B scripts/h62/item1/assignment-twins/test_frozen.py` exercises proof-only changes and adversarial statement, definition and command changes. This is a conservative text heuristic, not a Lean parser or proof of elaborated statement identity, unchanged axioms, trust, or semantics; further Lean and axiom gates remain mandatory. Independent finder and skeptic reviews found missing command checks; the guard and tests were expanded for their concrete examples. Unsupported Lean syntax and commands remain a limitation.

The lane was previously retired with its proof queue handed to `solidity-inline-assembly5-20261031/vy3-compilation`. A later coordinator message requested merging master and continuing. This backfill is isolated from that successor's proof implementation; no original Lean file was edited. The master fast-forward was to `5f14596531efea2be64f1a5e7a83afa5e151e865`, which contains the previous lane head `7c5de4602fa754ea3c3cca44185ef26098df5ff2`. The prior full baseline attempt was interrupted and is not a passing gate or timing measurement.

## Raw trust-indicator backfill

The frozen-text comparison also compares raw counts of `sorry`, `sorryAx`, `admit`, `native_decide`, `ofReduceBool`, `unsafe`, `run_tac`, and `axiom` in each of the six files against the original base. The raw scan intentionally includes comments and strings and can therefore report false positives; it also cannot detect indirect axiom dependencies, aliases, macros or arbitrary alternative syntax. The six pinned originals have zero occurrences of these raw indicators. In general, equal per-file counts can miss relocation of an existing indicator, while removals and identifiers such as `sorry'` can cause false positives. Its adversarial tests are textual controls only. The elaborated axiom audit, Lean verification and proof-budget checks remain mandatory. Independent finder and skeptic identified the missing literal proof-body indicators; the scanner and tests now cover their concrete examples.
