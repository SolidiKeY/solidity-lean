# Size reduction

Coordinator findings of 2026-11-08 (H259), drawn from the
[direction audit](direction.md) and its tools under
[direction-tools](direction-tools/). Counts keep the base of the measurement
they cite: the direction audit's own bases
([direction](direction.md#measurement-boundary-and-headline-facts)), `d6fd95f08`
for the declaration graph, and `ffa76e1c0` for the Git history and file counts
added here. Figures marked as estimates are not measured. The planned area
studies at the end are to measure savings on pilots. The second audit round
found that the proof core is nearly complete and that all 39 executed mutants
were killed ([direction audit](direction.md#making-it-smaller)), so the size
question concerns the compiler layers.

## Which size is justified

At 1.31M Lean lines, the repository is 5–10× the size of CompCert. A fair
comparison counts every system this repository replaces:

| What this repository does | Reference size |
|---|---|
| Verified compiler | CompCert, 251k |
| Program-logic calculus with kernel-checked soundness | SolKey rule resources, 43k, plus soundness proofs neither reference has |
| EVM model | EvmYul, 12k; KEVM, 59k |
| Solidity semantics | Isabelle Solidity, 19k |
| Solidity-only obligations: storage layout, ABI, hashing, gas, reverts, callbacks, 256-bit words | none in C |

Together these account for roughly 400–500k lines (an estimate). The audit
judged six of the ten largest areas justified: Calculus, Evm, Frontend, Source,
Semantics and Examples. It judged Backend (279k lines), Yul (197k) and Lowering
(104k) as heading the wrong way. They hold most of the remaining 600–800k lines.

## Why Yul is 197k lines

- **Purpose.** The Yul area implements inline assembly (`assembly { … }`), not a
  compiler intermediate language. Lanes VY1–VY5 of batch
  `solidity-inline-assembly5-20261031` built it under scope decisions YQ1–YQ7
  ([solidity-scope](../solidity-scope.md#inline-assembly-decisions-2026-10-31)).
- **Timing.** Git history shows 6k lines on 1–2 November, 115k on 3 November,
  42k on 4 November and 36k on 5 November. Single integration commits added up
  to 43k lines each.
- **Shape.** `Yul/Views` has 879 files: one view per data shape, each with its
  own `…Controls.lean` file (286 Controls files, 23k lines).
  `Yul/Checks/Arithmetic` and `Yul/Checks/Shifts` consist of thousands of
  single-input theorems, `theorem vNNNN : … := by decide +kernel`, produced by a
  generator that is not in the repository.
- **Multiplying decisions.** Three decisions each multiplied the number of cases:
  - preserving dirty high bits per pipeline (YQ4, H11, H109);
  - nondeterministic allocation with a refinement proof (YQ3);
  - exact monetary values (H19, H25).
- **No link to a headline theorem.** The scope decisions authorised
  implementation, "not admission". No step required composing the views into an
  end-to-end statement. In the
  [declaration graph](direction-tools/declgraph/summary.json), 0 of the 17,904
  `Yul/Views` declarations are used by the 21 statements in
  `Solidity/Theorems.lean`. Another 40k lines are used only by the area's own
  checks.
- **Gates.** Merge gates check correctness (no `sorry`, axioms, build). They
  never check size or value. Some `Views` modules needed 6–8 GB each to check
  (H81).

## Reduction ideas

| Idea | Target | Expected effect (estimate) | Theorem strength |
|---|---|---|---|
| One theorem per opcode instead of per-input vectors; keep vectors as one data list checked by `decide` | `Yul/Checks` and similar families | ~30k → ~1k lines | stronger (universal) |
| One view defined by recursion over a layout description type, with read-after-write, frame and allocation lemmas proved once by induction | `Yul/Views` | ~75k → 5–10k lines | same or stronger |
| Dirty-bit cleaning as a parameter, not legacy/IR copies | Yul, Backend | halves the remaining cases | same |
| Controls derived as instances of the generic lemmas | 286 Controls files | ~23k → 1–2k lines | same |
| Translation validation: one verified checker per pass, plus a completeness theorem on the accepted fragment | Lowering, Backend, assembly blocks | large; depends on kernel check time | same once completeness is proved; before that, rejected inputs are refused, never miscompiled |
| One reusable invariant per pass instead of scenario families | Lowering | large (scenario G families) | same |
| Generic lemmas by anti-unification; merge exact duplicates | 2,743 same-statement clusters, 88 near-file clusters (26.6k lines) | at most 26.6k lines | same |
| Delete code that verifiably has no uses, after a rebuild | Yul/Views, Backend/InternalFlow, SolcValidation, Frontend/SolcJson | only after per-family removal rebuilds; none is verified yet | none lost |

Translation validation keeps a full proof. The checker's soundness is a
kernel-checked theorem, and the check of each program must run in the kernel,
not through `native_decide`. Its open questions are the kernel check time on
real contracts and whether completeness can be proved for the accepted fragment.
The acceptance conditions in the [direction audit](direction.md) still apply:
the checker plus its proofs must be at least 3× smaller than the proofs they
replace, and kernel checking of real contracts must stay within the gate budget.

The Yul and Lowering ideas above are estimates. The area studies measure them
on real slices.

## Process changes

- **Size budget.** A CI budget on Backend, Yul and Lowering: these areas may grow
  only when a change names the `@[goal]` it advances. Under that budget the
  growth of 3–5 November would have been stopped on the first day.
- **One goal per feature.** Every feature gets one headline goal that its code
  must reach. For assembly: memory-safe blocks refine their Yul semantics inside
  the Solidity end-to-end statement.
- **Product endpoint.** The product endpoint is still undecided:
  - (a) a small SolKey-compatible proof core;
  - (b) a verified compiler for an accepted fragment;
  - (c) production Solidity/EVM conformance.

  The measures of progress depend on this choice.

## Area studies

Two batches run the pilots. They are planned; until each study reports, no
saving here is measured.

- Translation validation for Yul, Backend and Lowering: lanes `tv-yul`,
  `tv-backend` and `gen-lowering` of batch `shrink-pilots-1108` (H258), plus
  `lowering-checker-p1`. Results go under `docs/audits/shrink/` and are
  summarised in [direction audit: making it smaller](direction.md#making-it-smaller).

- Yul views as one layout-indexed view: pending, lane size-yul-views.

- Test vectors as theorems (repo-wide): pending, lane size-test-vectors.

- Duplicates (repo-wide): pending, lane size-duplicates.

Each lane of batch `size-reduction-1108` replaces its own line above with a
link to its study and its measured result.
