# Packet panic case accounting, H70 continuation

This is a read-only interpretation of existing declarations at base `c6f550e281a7e5affa9a99bc2cdaed556dec00e4`. It neither checks new Lean proofs nor changes reserved producers. Paths below are relative to `Solidity/Backend/PrimitivePackets/`. Declarations in `Controls` under `Fixture` are so qualified. Conditions, representations, checked flags, fuel, saved stack, frame, and original premises remain as stated in the source; this table is a navigation aid, not a substitute for those statements. Source panic data is an exact Source observation. A selected target `.revert` is coarse and proves no target panic bytes or reverted machine state.

The companion `declarations.py` enumerates 465 literal line-start declaration headers from 48 files in the ten packet families covered here. The unsigned checked subset has 163: Add 45, Sub 52, Mul 66. It records their paths, lines and raw-file hashes in the off-Git `declarations.json`; this syntactic census is not a Lean parser, a semantic dependency closure, or proof that all possible runtime cases are covered. `inventory.json` separately lists the 42 literal panicData occurrences, including the 13 named byte controls. The following additional case observations include declarations that never spell `panicData`.

## Unsigned checked packets

| Path and declarations | Cases and observations |
|---|---|
| Each `Checked{Add,Sub,Mul}/Selected.lean`: `value`, `selected`, `public_selection`, `original_guard` | Public selection and original checked guard, rather than a supplied desired run. |
| Each `Checked{Add,Sub,Mul}/Source.lean`: `source_success`; Add/Mul `source_overflow`, Sub `source_underflow` | In-range arithmetic succeeds with unchanged Source state; outside-range checked arithmetic returns Source arithmetic panic with unchanged state at the stated fuel. |
| Each `Checked{Add,Sub,Mul}/Target.lean`: `value_success`, `target_success`; Add/Mul `value_overflow`, `target_overflow`; Sub `value_underflow`, `target_underflow` | Value and selected-code success or failure under the read and representation premises. The selected target failure is coarse revert. |
| `CheckedAdd/Agreement.lean`: `overflow_iff`, `success`, `overflow` | For in-range unsigned inputs, sum outside range iff above the upper bound; joint public selection, Source result/panic and represented target success/revert. |
| `CheckedSub/Agreement.lean`: `underflow_iff`, `success_iff`, `success`, `underflow`, `classification`, `target_underflow_iff` | Difference fits iff `y ≤ x`; underflow iff `x < y`. `classification` has both branches; target revert iff underflow under its stated premises. |
| `CheckedMul/Agreement.lean`: `overflow_iff`, `success`, `overflow`, `source_overflow_exact`, `target_overflow_exact` | Product outside range iff above the upper bound for in-range unsigned inputs; both Source panic and coarse target revert have their own exact classifications under their premises. |
| `CheckedAdd/Controls.lean`: `Fixture.result`, `minimum`, `maximum`, `regular`, `overflow`, `double_overflow` | General fitted sum, 0+0, (W-1)+0, 7+9, (W-1)+1, (W-1)+(W-1); overflow cases observe target revert. |
| `CheckedSub/Controls.lean`: `Fixture.result`, `minimum`, `maximum`, `equal`, `regular`, `underflow`, `far_underflow`, `wrong_order_refused`, `underflow_does_not_wrap` | General fitted difference, 0-0, (W-1)-0, 7-7, 9-7, 0-1, 0-(W-1), 7-9 revert, and exclusion of a wrapped W-1 result for 0-1. |
| `CheckedMul/Controls.lean`: `Fixture.result`, `minimum`, `zero_left`, `zero_right`, `maximum`, `regular`, `overflow`, `double_overflow` | General fitted product, zero and boundary successes, and (W-1)*2 or (W-1)*(W-1) target reverts. |
| Each `Checked{Add,Sub,Mul}/Controls.lean`: `Fixture.jointSuccess`, Add/Mul `jointOverflow`, Sub `jointUnderflow`, `sourceSuccess`, Add/Mul `sourceOverflow`, Sub `sourceUnderflow` | Definitions instantiate the corresponding existing proofs for the pipeline parameter and, where present, arbitrary saved stack. They are distinct declarations and must not be dropped as mere duplicate bytes. Mul additionally has `jointMaximum`, `jointZeroLeft`, `jointZeroRight`. |
| Each unsigned Controls: `exact_panic_bytes`, `panic_not_truncated`, `panic_not_empty` | Three named Source-byte assertions per file: full arithmetic encoding, inequality to the five-byte truncated list, and inequality to empty. |
| Each unsigned Controls: `Fixture.wrong_value_refused`, `wrong_index_refused`, `protected_frame`, `low_fuel` | Correspondence refusals, protected caller frame, and timeout respectively; timeout is not a panic. Sub also has `corrupted_tail_refused`. Fixture definitions, range, family and representation lemmas are enumerated in `declarations.json`; Mul also has its 14 `Populated.lean` headers. |

## Signed checked packets

For `SignedCheckedAdd`, `SignedCheckedSub`, and `SignedCheckedMul`, the Source files have `source_success` and `source_overflow`; Target files have `value_success`, `value_overflow`, `target_success`, `target_overflow`; Agreement files have `success` and `overflow`. These retain in-range/read/family/representation premises, exact Source panic and coarse target revert. Sub and Mul also have `overflow_iff` for below-low or above-high; this was not asserted for Add. `Selected.lean` has `value`, `selected`, `public_selection`, `original_guard`; Mul also has `guard_is_sTail` and its original signed guard. Existing proof guards, including Mul `#guard_msgs`, remain excluded and untouched.

- `SignedCheckedAdd/Controls.lean`: `success`, `failure`; `maximum` (hi+0), `minimum` (lo+0), `mixedSigns` (-7+9), `positiveOverflow` (hi+1), `negativeOverflow` (lo-1); `panic_not_empty`, `exact_panic` are Source-byte controls.
- `SignedCheckedSub/Controls.lean`: `joint_success`, `joint_overflow`, `upper`, `lower`, `regular`, `minimum_success`, `maximum_success`; `upper_not_wrap`, `wrong_result`, `low_fuel`, `exact_panic`, and `family`. The low-fuel outcome is timeout.
- `SignedCheckedMul/Controls.lean`: `joint_success`, `joint_overflow`; overflow witnesses `minimum_minus`, `minus_minimum`, `upper`, `upper_negative`, `lower`, `lower_swapped`, `lower_maximum`; success witnesses `regular`, `regular_positive`, `regular_both_positive`, `regular_swapped`, `minimum_one`, `one_minimum`, `maximum_minus`, `minus_maximum`, `minimum_zero`, `zero_minimum`; `guard_classification`, `minimum_minus_not_wrap`, `minus_minimum_not_wrap`, `regular_exact`, `wrong_result`, `low_fuel`, `exact_panic`. The timeout and negative controls are not extra panic payload claims.

## Other packet panic contexts

- `SignedDiv/Origin.lean`: `source_zero` is divide-by-zero panic for either checked flag; `source_overflow` is checked minimum/-1 arithmetic panic; `source_unchecked_overflow` wraps; `source_ordinary` covers its ordinary nonzero premises. `Execution.lean` has `intrinsic_zero`, `intrinsic_overflow`, `zero_execution`, `overflow_execution`; `Contract.checked_contract` retains its explicit resource premises. `Controls.lean` includes `zero_both`, `overflow_both`, `panic_classes_differ`, `checked_not_wrap`, `truncation_both`, `no_floor_rounding`, `capacity_witness`.
- `SignedMod/Source.lean`: `source_zero`, `source_locals_zero`, `source_nonzero`, `source_locals_nonzero`; `Selection.selected_zero`, `selected_remainder`, `selected_success`; Controls include `source_failure`, `target_failure`, `raw_zero_differs`, success witnesses and `too_short_horizon`, `horizon_two_timeout`. In particular the minimum modulo -1 success is distinct from checked signed division overflow.
- `UnsignedDiv/Composition.lean`: `division_zero_packet`, `remainder_zero_packet`, `division_packet`, `remainder_packet`; `Execution.lean`: `selected_div_zero`, `selected_mod_zero`; `Witness.lean`: `witnessed_zero_division`, `witnessed_division`, `witnessed_remainder`; `Numeric.scalar_panic_bytes` connects scalar failure to Source divZero bytes, not target bytes.
- `SignedSub/Controls.lean`: `checked_overflow_boundary` observes checked Source panic bytes; `min_wrap`, `max_wrap`, `both_source_pipelines`, `both_source_max_wrap` concern unchecked wrap and `no_horizon_promotion` concerns timeout. This Source observation does not assert a revert for the unchecked target packet.

The coordinator reports owner ticket relays accepted but requires exact-file agreements before any edit to `CheckedAdd/Controls.lean` (VY4), `CheckedSub/Controls.lean` (MRS), and `CheckedMul/Controls.lean` (MIC); none has been supplied. This ledger is not full semantic dependency or external-test accounting. Remaining work includes complete case reconciliation outside these named observations, the shared helper and exact equivalence, all four original checkpoints and their proof/runtime/timing gates. No performance conclusion or new theorem is claimed.

## Per-declaration reconciliation of the three pending Controls files

`controls_ledger.py --declarations /workspace/h62-packet-panic-evidence/declarations.json` maps the current literal declaration census one-for-one to 102 manually reviewed observations: CheckedAdd 31, CheckedSub 35 and CheckedMul 36. The output is `/workspace/h62-packet-panic-evidence/controls-ledger.json` and records each original file path, line, raw-file SHA-256, name, category and observation. It pins the reviewed base hashes for all three files and compares each supplied line, kind and name to the literal headers in those bytes; it also checks namesets and duplicates. The input must be freshly generated by `declarations.py`; this reconciliation does not independently parse Lean or prove that the input includes every possible declaration syntax. In particular the 102 rows are declaration observations, not 102 independent semantic tests or 102 new proofs.

Descriptions preserve distinct Source byte controls and joint/target results. Each `protected_frame` is an initial fixture-memory assertion, not itself a post-revert frame theorem; `low_fuel` is timeout. For `sourceSuccess` and failure instantiations, theorem fuel parameter 0 corresponds to evaluation fuel 3. Sub's `jointSuccess` and `jointUnderflow` instantiate the existing conditional classification. Target revert conveys no payload. Saved tails and original proof premises remain as stated in the files. Original files are read only while exact-file agreements remain pending.

## Signed checked Controls per-declaration continuation

The additive `signed_controls_ledger.py` maps a fresh `declarations.py` census to 71 reviewed literal Controls headers: SignedCheckedAdd 11, SignedCheckedSub 21, SignedCheckedMul 39. Each row carries the original path, line, raw-file SHA-256, declaration kind, a category and an observation; reviewed raw hashes and ordered source headers are checked before output. The generated `signed-controls-ledger.json` stays off Git. Its categories distinguish fixture setup, Source success and panic, joint Source/target success or coarse revert, target guard, negative controls and timeout. They are declaration observations, not 71 independent tests, kernel proofs, full semantic dependency closure or target payload claims.

The ledger reads G25-reserved originals and does not edit them. Existing signed multiplication `#guard_msgs` and all other H55 proof guards are outside the edit scope and unchanged. The original premises, operand ordering, arbitrary saved tail and selected-code observations remain those of the cited files. The prior 102 unsigned rows and these 71 signed rows are separately accounted; other declarations and consumer/dependency proof obligations remain open.

## Six checked pipeline declarations

`checked_pipeline_ledger.py` maps 89 literal Source, Selected, Target and Agreement headers across the six unsigned/signed checked arithmetic families to manually reviewed observations: CheckedAdd 14, CheckedSub 17, CheckedMul 16, SignedCheckedAdd 13, SignedCheckedSub 14 and SignedCheckedMul 15. The generated `checked-pipeline-ledger.json` is off Git. It compares each complete source file byte-for-byte to the assigned base Git tree, checks its census hash and ordered literal headers, and records every mapped declaration with its source location. Changed source requires a fresh review; the script fails rather than silently transferring these descriptions to it.

The 89 pipeline rows are disjoint from the prior 102 unsigned and 71 signed Controls rows. Together they account for 262 of the 465 literal headers in the ten-family census; the other 203 remain unclassified by these per-declaration ledgers. Counts describe textual declarations and do not imply semantic or dependency completeness. Source failure rows specify Source panic data and state; intrinsic target failures and selected-machine reverts are recorded separately, with no invented target payload or reverted machine state. Every range, read, fuel, correspondence, representation and saved-tail premise remains as written in the original declaration. G25 originals and H55 proof guards were read-only.

## SignedMod Source

`signed_mod_source_ledger.py` records all 12 literal headers in SignedMod/Source.lean, pinned to the assigned base bytes. They include the signed type/range and remainder bound; arbitrary checked-flag Source nonzero and zero-divisor outcomes; local reads with fuel+3 and the complete retained Source state; sign identities; and the pure minimum remainder -1 equality. The latter is not an execution theorem. The observations do not assert target payloads, unlisted cases or Lean validation. With this ledger, 274 of 465 enumerated literal headers have manual per-declaration observations; 191 remain unclassified. This is still not full semantic or dependency closure.

## SignedMod Selection

The base-byte-pinned `signed_mod_selection_ledger.py` adds ten literal declarations: public selection, operator-level nonzero/zero results, representation uniqueness, combined Source and selected execution, and separate symbolic success, zero-revert and origin success. The combined numeric theorem requires the stated finite-word saved stack and both capacity hypotheses; symbolic success and zero-revert quantify a separate arbitrary EVM-word tail. This is manual textual accounting, not Lean validation or a target panic-payload claim. Together the ledgers account for 284 of 465 literal headers; 181 remain.

## SignedDiv Origin

The base-byte-pinned `signed_div_origin_ledger.py` covers ten literal declarations for Source signed division origins. It distinguishes zero divisor in both modes, checked minimum/-1 arithmetic panic, unchecked minimum/-1 success, and ordinary division with a nonzero divisor and the overflow pair excluded. Local origin retains the original reads, frame, fuel+3 and full Source state. This is a textual Source account, not a target proof. The ledgers now account for 294 of 465 literal headers; 171 remain unclassified.

## SignedDiv Selected

The base-byte-pinned `signed_div_selected_ledger.py` adds twelve literal declarations covering public compiler selection, checked raw division and the unchecked minimum/-1 conditional, intrinsic evaluation under local-read premises, and symbolic `ValOutT` under the original physical StateRepr and arbitrary EVM-word tail. This is not a numeric capacity proof, target panic-payload claim, Lean proof or complete semantic account. The ledgers now account for 306 of 465 literal headers; 159 remain unclassified.

## SignedDiv Execution

`signed_div_execution_ledger.py` records six base-pinned intrinsic and joint Source/selected symbolic execution declarations. Ordinary and zero-divisor cases retain both checked modes; the minimum/-1 case separately records checked arithmetic panic/coarse revert and unchecked minimum success. Original Source/target local reads, physical StateRepr and arbitrary EVM-word tail remain binding. This is textual accounting, not Lean validation or a target panic-payload assertion. The ledgers now account for 312 of 465 literal headers; 153 remain unclassified.

## UnsignedDiv Data and SourceOrigin

`unsigned_div_origin_ledger.py` records eleven base-pinned literal declarations across Data and SourceOrigin. These include operand contexts, local-tail ordering, Source and intrinsic div/mod expressions, and Source local div/mod outcomes at n+3 across both pipelines with the complete local/state pair retained. A private helper `SourceOrigin.lift_result` lies outside the 465 literal-header census and is a dependency of both origins. The ledgers now account for 323 of those 465 headers; 142 remain unclassified, and the 465 count does not include private headers. This is textual accounting, not Lean validation or complete dependency coverage.

## Additional private and protected headers

The original census matches only unmodified line-start headers and omitted private or protected declarations. `private_header_ledger.py` scans the same independently enumerated 48 pinned files and finds nine additional literal `private theorem` headers. Their manual observations cover fixture heap references, representation uniqueness, unsigned success/refusal observations, numeric conversion, Source result lifting, and local-word representation. With these separately counted rows, 332 of 474 observed literal headers have manual observations; 142 of the original 465 remain unclassified. Neither scanner is a Lean parser: modifier combinations, alternate formatting, comments and declarations beyond the fixed files may be missed or misidentified. These counts are not full declaration, semantic or dependency coverage.

## UnsignedDiv Selection and Numeric

`unsigned_div_selection_numeric_ledger.py` records eleven base-pinned literal declarations for public selection, two operand loads and binTail, nonzero operator results and Source transport. The scalar divisionFailure equality concerns Source panic bytes; symbolic EVM revert does not expose a payload. These textual observations are not Lean validation or complete dependency accounting. The ledgers now describe 343 of 474 observed literal headers; 131 of the original subtotal remain.

## UnsignedDiv Execution and Composition

`unsigned_div_execution_composition_ledger.py` adds ten base-pinned literal headers for intrinsic evaluation, selected execution and joint Source/target local cases. The original StateRepr and divisor premises, Source fuel n+3 and retained local/state pair remain binding; zero cases assert exact Source divZero panic data and coarse symbolic target revert. These are textual observations, not whole-state agreement, gas, ABI or target payload proofs. The ledgers now describe 353 of 474 observed literal headers; 121 of the original subtotal remain.

## UnsignedDiv Witness

`unsigned_div_witness_ledger.py` records eight base-pinned literal headers for the auxiliary initialized machine and StateRepr, arbitrary saved stack, nonzero Source div/mod success and zero-divisor Source divZero panic with coarse selected symbolic revert. Source local tails and state are retained as stated. There is no separately named witnessed zero-remainder theorem in this file; the general remainder-zero packet is a separate declaration in Composition. This is a textual auxiliary witness account, not deployment, native execution or target panic-payload proof. The ledgers now describe 361 of 474 observed literal headers; 113 of the original subtotal remain unclassified.

## SignedSub Execution

`signed_sub_execution_ledger.py` adds seven base-pinned literal declarations for unchecked signed subtraction, public selection and emitted code, arbitrary-tail symbolic execution and its retained StateRepr, and Source-only zero-horizon timeout. The original local-family, range, read and representation premises remain binding. Private `int_word_unique` is separately accounted and axiom guards remain untouched. This is textual accounting, not Lean proof or native execution. The ledgers now describe 368 of 474 observed literal headers; 106 of the original subtotal remain.

## SignedMod Controls

`signed_mod_controls_ledger.py` adds thirty base-pinned literal declarations for populated fixtures, Source and selected symbolic outcomes, separate raw/guarded numeric zero behavior, five signed remainder examples, low-horizon timeouts, saved-tail and short-frame refusals and an initial memory snapshot. Original ranges, checked/pipeline quantifiers and w77-prefixed arbitrary tails remain binding. Exact Source divZero data is not a symbolic target payload claim. The ledgers now describe 398 of 474 observed lexical headers; 76 of the original subtotal remain. This is not Lean proof or full semantic coverage.

## SignedDiv Controls

`signed_div_controls_ledger.py` adds twenty-one base-pinned literal declarations for the populated fixture, canonical word representation, zero-divisor and minimum/-1 Source/symbolic cases, -7/2 truncation, panic-class distinction, negative controls and numeric depth-4 stack bounds. It retains the original pipeline, checked-flag, fuel and arbitrary-tail quantifiers; Source exact panic data remains separate from coarse symbolic revert. Existing axiom guards are outside this ledger and were not edited. The ledgers now describe 419 of 474 observed lexical headers; 55 of the original subtotal remain. This is not Lean proof or full semantic coverage.

## Reconciled totals

`python3 scripts/h62/item1/packet-panic/ledger_totals.py --declarations <fresh-declarations.json>` regenerates the literal census and all sixteen ledgers, checks original-row membership and overlap, and emits per-ledger totals and unclassified rows. On this base-pinned tree it reports 465 original rows, nine private rows, 410 described original rows, 419 described total and 55 unclassified original rows. These replace prior hand addition of subtotals. The generator verifies textual identity and set membership; it does not mechanically verify the manual observation prose against Lean statements, establish proof validity or close the lexical/semantic gaps.

## Same-line attribute candidate scan

The earlier version of `attributed_header_scan.py` examined the same 48 base-validated files for a single simple `@[...]` attribute and declaration on one line, a form the original census skips. The current raw textual scan found zero candidates for that narrow pattern. It does not mask comments or parse nested/multiple attributes, multiline headers or other Lean syntax, and zero candidates does not show that attributed declarations are absent. Its synthetic fixture includes both matching examples and a deliberate block-comment false positive. The separately recorded private-header ledger covers nine private declarations; neither scan is full declaration or semantic closure.

## SignedSub Controls

`signed_sub_controls_ledger.py` describes forty base-pinned literal headers, identifying repeated Seed and outer namespace names by original line and name. The observations separate unchecked Source execution, symbolic target outcomes and projections, the checked Source overflow projection, initial fixture memory, low-horizon timeout and refusal cases. Existing axiom guards were not edited. After registering this ledger, reconciliation covers 459 of 474 observed lexical headers; 15 original headers remain unclassified. Manual prose and lexical headers are not Lean proof or complete semantic coverage.

## CheckedMul Populated

`checked_mul_populated_ledger.py` records fourteen base-pinned literal headers for the two-array heap, its aliases, concrete machine, ArrayRepr, HeapRepr and StateRepr. Base-map arguments 0 and 1 yield addresses 16 and 20. The two private helpers were separately recorded. The original G25 fixture remains read-only. Reconciliation describes 473 of 474 observed lexical headers; one original header remains. These observations do not prove Lean statements or complete semantic coverage.

## SignedDiv Contract

`signed_div_contract_ledger.py` records the full checked-contract literal declaration: original Source/target reads and StateRepr, saved finite words, and all three numeric zero-test, overflow-test and SDIV-body capacity premises remain explicit. Its Source mapped result, symbolic ValOutT and numeric outcome remain distinct. After registration, the reconciliation describes all 474 currently observed literal headers, including nine private headers; no original census row is unclassified. This is textual row accounting with manually reviewed prose, not complete Lean parsing, semantic case/dependency closure, proof validation, target payload correspondence or a runtime gate.

## Source-window review evidence

`source_windows.py` regenerates the reconciled ledgers and binds each manual observation to source text from its scanned literal header up to the next scanned header or end of file, with source and window SHA-256 hashes. Its 474-row generated JSON remains off Git. Windows omit preceding docstrings or attributes and may contain proof text, comments, namespace closures, axiom guards or unscanned declarations. They are navigational review evidence, not parsed theorem statements or mechanical confirmation that prose matches a proposition. Python text `splitlines` is broader than LF-only line splitting; independently checked current pinned sources contain no differing CR or Unicode separators.

## Panic occurrence navigation

`panic_occurrence_windows.py` scans current-tree PrimitivePackets raw text and maps every `panicData` regex hit to a regenerated lexical source window where one exists. At the earlier pre-registration snapshot the output had 42 raw matches and zero unmapped; source window files are base-pinned but other scanned files are not independently base-verified by this tool. Raw regex also matches comments, strings and `panicData` with an apostrophe suffix, and a containing window may include unrelated unscanned declarations. This is navigation, not Lean declaration attribution, semantic case completeness, proof or ownership clearance.

## Fail-closed panic occurrence follow-up

`panic_occurrence_windows.py` emits its JSON and exits 2 for zero raw matches or 3 for any unmapped match. Upstream registered the canonical `PanicBytes.lean` helper after the original 48-file census; its three headers receive separate navigation windows only after checking its bytes against registration commit `e9b89d553234b52e4ba9b38092ff691138c147c8`. The current scan has 45 raw matches, three supplemental helper windows and zero unmapped. The original 474-header ledger denominator is unchanged. Raw regex and lexical window limitations continue to apply; this is not semantic attribution or Lean proof.

## Masked panic lexical hints

The prior census comment/string/attribute mask was moved without changing its function body into `lexical_mask.py` and reused by the occurrence mapper. Every raw hit remains in output with a heuristic `lexical_candidate` flag; comments, strings, attributes and common identifier suffix/prefix cases are masked or rejected as candidates. On the current tree, 45 raw hits are all flagged candidates and zero are unmapped. Columns are one-based Python Unicode code-point offsets, not necessarily byte or UTF-16 offsets. The mask is not Lean name resolution: quoted identifiers, unusual syntax and conservative suffix rules may misclassify or miss cases, and current-tree files outside the pinned window set remain unverified. No semantic, ownership or proof claim follows.

## Expanded attribute candidate follow-up

The attribute scanner now uses the shared offset-preserving mask with attribute masking disabled, then recognizes certain nested, multiple and multiline attributes before `theorem`, `lemma`, `def` and `abbrev` headers. It reports the declaration token location and whether the original census covers that exact file, line, kind and name. The original mask default remains unchanged. The 48 pinned files yield zero candidates in this heuristic scan. Comments and strings are masked, but unsupported modifiers, quoted identifiers, syntax contexts and line-ending behavior may still cause misses or false positives; columns are Unicode code-point offsets. Synthetic tests cover nested and multiple attributes, multiline modifiers, masked comments and strings, malformed attributes and location alignment. This is not Lean parsing, semantic completeness or a proof.

## Raw strings and interpolation safety

The shared lexical mask now handles Lean raw strings with zero or more hash delimiters, preserving character positions and LF offsets, and rejects unterminated raw strings. It conservatively fails on an exclamation mark followed by a string or comment rather than silently masking possible interpolation terms. This can reject ordinary non-interpolation text and does not recognize all Lean syntax; it is not a Lean parser. Tests cover nested delimiters, Unicode and quoted macro spellings, comment-separated cases and masked contexts. The current pinned-tree occurrence output remains byte-identical to the earlier snapshot.
