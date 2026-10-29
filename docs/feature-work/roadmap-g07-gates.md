# Roadmap G07: proof/trust regression gates and contract controls

G07 closes wave 0 of [the roadmap](../coverage-plan.md) ("Establish
proof/trust regression gates, axiom inventories and inhabited
source-to-machine controls; record existing failures separately. Check that
malformed source, altered bytecode and always-revert output cannot satisfy the
planned contracts."). It is the first checkpoint of lane V03.

Base: `ceb0d54` with the roadmap-w1 branches `g00-manifest-rev`,
`g02-measure`, `g03-ledger`, `g05-frontend`, `g06-evm-interface` and
`g01-contracts-rev` merged (the G01 revision's document has a filled
`Handoff`).

## 1. Contract controls (`Solidity/Roadmap/Controls.lean`)

G01's contracts (`Solidity/Roadmap/Contracts.lean`) are statements over
parameters. A statement can fail two ways: it can be unsatisfiable (no
compiler could meet it), or too weak (a wrong compiler meets it). The module
checks both on one small instance, kernel-checked, with `#guard_msgs` axiom
pins.

**Inhabited control.** `toySource` reads source bytes as one of three
programs: `0 d…` succeeds with data `d`, `1 d…` reverts with `d`, `2` loops.
Every other text is malformed. Inputs carry both pipelines, the pragma's ABI
coder and a link map, which must be empty. `toyEvm` decodes the selected
unit's runtime bytes the same way, whatever the gas, and hashes nothing.
The intrinsic layer is the source language, with an identity pass and its
certificate (`idCert`). `toyCompiler` writes the parsed program's text as
the runtime bytes. Proved:

| Theorem | Statement |
|---|---|
| `toy_publicCorrectness` | Every field of `PublicCorrectness toySource toyEvm toyCompiler id toyExport`: coverage, both pipelines, environment, fixed parameters, the creation table, two-sided refinement under the per-run hash premise, `decode_reach`, `decode_commutes` |
| `toySource_nonVacuous` | `SourceSpec.NonVacuous`: success with data `[1]`, revert with `[7]`, divergence, at every artifact table |
| `toySource_approved`, `toyEvm_approved` | `SourceSpec.Approved` (idealized, precompiles fixed, `this` from deployment, settings recorded, empty link map) and `EvmSpec.Approved` (Keccak-256, every bound admissible) |

So the public contract can be met, with a non-vacuous source and both
approval conjuncts of the final statement.

**Negative controls**, on the same source and EVM, for every intrinsic layer
and state export:

| Theorem | Refuted | Through |
|---|---|---|
| `not_publicCorrectness_revertCompiler` | output that always reverts | `PublicCorrectness.not_alwaysRevert` (G01) |
| `not_publicCorrectness_alteredCompiler` | correct bytes with one byte appended (`0 1` succeeds with `[1, 0]`) | `PublicCorrectness.observes` (new) |
| `not_publicCorrectness_erasingCompiler` | revert data erased | `PublicCorrectness.observes` |
| `not_publicCorrectness_sloppyCompiler` | malformed text (the empty input) compiled | `PublicCorrectness.rejects` (new) |
| `not_admission_sloppy` | a frontend accepting malformed text | `Admission.rejects` (new) |
| `not_nonVacuous_emptySource` | a source whose grammar accepts nothing | `SourceSpec.not_nonVacuous_of_no_parse` (new) |

The new generic lemmas hold of every source, EVM and compiler:
`PublicCorrectness.observes` turns any completion of an admitted source
meaning without exhaustion into an EVM completion with the same outcome and
events under the per-run premise. `PublicCorrectness.rejects` refuses
non-admitted input. `SourceSpec.NonVacuous.admits` and
`SourceSpec.not_nonVacuous_of_no_parse` show that a malformed or empty source
definition cannot meet the `NonVacuous` conjunct.

**Scope of the controls.** The toy languages emit no events. They exercise
the outcome, coverage, settings and approval fields, not event traces,
callbacks or state decoding (`decode_reach` holds because the toy reaches no
boundary world). Event-level controls on real programs, and the concrete
pipeline run on them, belong to G49.03 (`docs/coverage-plan.md`, wave-0
row). The toy is not a correspondence claim about Solidity.

## 2. Gates

All gates run without Lean, in about 15 s, through one runner:

```
node scripts/check-g07.mjs [--log RUN_LEAN_LOG]
```

| Gate | Script | Rule |
|---|---|---|
| Trust lint | `scripts/check-trust.sh` (existing) | no `sorry`, axiom, `native_decide`, …; inventory unchanged |
| Layers, orphans | `scripts/check-layers.mjs`, `scripts/check-orphans.mjs` (existing) | core below the elaborator; every module built |
| Non-circularity | `scripts/check-noncircular.mjs` (new; tests `scripts/check-noncircular.test.mjs`) | G01's four-part gate, §3 |
| Axiom inventory | `scripts/check-axiom-pins.mjs` (new; tests `scripts/check-axiom-pins.test.mjs`; inventory `scripts/g07-axiom-pins.json`) | §4 |
| Doc paths | `scripts/check-doc-paths.sh` (existing) | no missing reference beyond the baseline |
| G03 ledger | `scripts/roadmap-g03-ledger.py --check` (existing) | no error line beyond the baseline |
| Build log | `--log` on a `./run-lean.sh` log | no Lean error outside the baselined out-of-memory module; SolKey mismatches at most the baseline |

The transitive Lean axiom audit stays `TrustAudit.lean`; G07 appended one
`run_cmd` block for the sixteen contract and control theorems (the G01
lemmas `PublicCorrectness.transfer` and `not_alwaysRevert`, the four new
generic lemmas and the ten control theorems). Run it as
[assurance.md](../assurance.md) describes, or open it in the Lean server.

## 3. Non-circularity, mechanically

G01's gate ([roadmap-g01-interfaces.md](roadmap-g01-interfaces.md#non-circularity-as-a-checkable-gate))
has four parts. `scripts/check-noncircular.mjs` implements them as follows:

1. **Import whitelist.** A module under `Solidity/Source/`, or any module
   that instantiates `SourceSpec` (`: SourceSpec where`, `:= …`,
   `SourceSpec.mk`), reaches transitively only `Solidity.Source.*`,
   `Solidity.Roadmap.Contracts`, `Solidity.Keccak` and the named datatype
   modules of `DATATYPES`. No non-Solidity import is allowed, not even `Lean`.
   `DATATYPES` is empty: no S00/S01 module reuses an intrinsic type. An entry
   names its correspondence theorem, which must be declared in its file.
2. **No meaning through the pipeline.** Source modules name none of
   `IntrinsicSpec`, `Lowering`, `Compilation`, `Execution`, `StateExport`,
   `EvmSpec`, `PublicCorrectness`. Comments are blanked; string literals count.
   The other half of the part, that the constants `Lowering.lower` unfolds to
   use no source constant beyond the whitelisted datatypes, needs a Lean-side
   constant audit once a real lowering exists. It is left to G16, recorded
   under [Remaining obligations](#remaining-obligations).
3. **The EVM end.** A module that instantiates `EvmSpec` reaches no compiler
   module (`Solidity.Evm.{Compile,Compiler,Correct,Interpreter,Sim,…}`, the
   memory compile/source modules), no frontend, elaborator or source module,
   and not `Solidity.Roadmap.TypedRun`.
4. **The artifact table is a variable.** Part 1 enforces it: the source
   closure holds no `Solidity.Evm.*` module, and `Contracts.lean` defines no
   compiler.

Control modules (`CONTROLS`: `Solidity.Roadmap.Controls`) build toy instances
of both ends and may import `Solidity.Roadmap.Contracts` only.

## 4. Axiom inventory

`scripts/check-axiom-pins.mjs` reads every `#guard_msgs`-pinned
`#print axioms` in `Solidity/`, `Bridge/`, `tests/` and the root modules
(317 pins at this revision: 274 on the three standard axioms, 25 on `propext`
alone, 6 on `propext` and `Quot.sound`, 12 on none). Lean checks each pin's
text when it builds the file. The script checks the text itself:

- a pin naming `sorryAx` or any other non-standard axiom is an error, since
  `#guard_msgs` would accept it;
- a recorded pin must stay, and its axiom set must not grow;
- a new pin, or a smaller set, is reported until
  `node scripts/check-axiom-pins.mjs --write` records it.

## 5. Existing failures, recorded separately

`scripts/g07-baseline.json` records the failures present at the base. They
are owned elsewhere and are not fixed here:

| Check | Baseline | Owner |
|---|---|---|
| `scripts/check-doc-paths.sh` | 46 missing references (the base count) | the citing documents' owners |
| `scripts/roadmap-g03-ledger.py --check` | 38 errors after the merges: the second-round decisions and the G01 revision (`typedRunPrefixes` moved to `TypedRun.lean`, the gas-cap decision renamed) have no G03 rows yet, and the G07 schedule and module acknowledgements are stale | G03 follow-up |
| `./run-lean.sh`, `lake build SolkeyTestSuite` | `TestSuite.Derived17` killed for memory (exit 137) on a cold build | Codex TestSuite lane |
| `scripts/check-solkey.sh` | 37 mismatches | Codex lane |

The gate fails only on a failure outside these lists.

## Remaining obligations

- The constant-level half of non-circularity part 2 (§3) waits for G16's
  lowering.
- Event-level controls, controls on real programs and the concrete pipeline
  (G49.03).
- Per-family rejection controls for the 30 exclusions (G03 decision D01).
  S00 provides the precise rejection (`Solidity/Source/Syntax.lean`'s
  profile classification); admission controls on source text follow with
  G08–G15.

## Review

To be filled after the finder/skeptic reviews.

## Handoff

To be filled at the end of the checkpoint.
