# Feature manifest citations (E3 / F8)

The manifest separates implementation status from evidence strength. A cited
name is a trace to a declaration, not a claim of complete Solidity support.
The source snapshot is `a0a9ca15ba35fd6e8d9a9be10e4b6b45dbf45d3e`.

## Scope contract

Schema version 2 retains existing fields and adds `theorems` per row. Each entry
has `name` (fully qualified Lean declaration), `module` (owning import module),
`class`, `premises` (named strings), and `direction` (`model` or `model-to-solc`).
Optional `citationNotes` explains a bounded claim and its remaining gap.
Optional `modelToSolcGap` is nonempty text recording an open agreement obligation.

- a: a general kernel theorem against repository semantics, including ordinary
  input-domain conditions; this does not imply source or solc correspondence.
- b: proof with explicit fragment, simulation, invariant or environment premises,
  listed in `premises`. Only b entries have a nonempty premises list.
- c: finite tested evidence, including constant kernel computations. A named
  implementation may anchor an external fixture; its test boundary is explicit.
- d: a definition, table or other implementation trace with no general theorem.

The checker imports each module and queries the elaborated environment for the
exact name, owning module and (for a/b) theorem kind. Source regex matching is
not name resolution. A `present` row needs a non-d citation. Class c remains
finite evidence even when the implementation status stays `present`. Empty lists
mean uncited, not a proof of absence. Semantic relevance and premise completeness
also require independent review; resolvability alone cannot establish either.

No proof statement or proof source may change. H112 requires reusing generic
interfaces; H117 forbids patching hard semantic problems here. H44 requires
reproducible generators and off-git bulk output. H136 confines this lane to its
lease. E3-Q1 (#167) permits only the reader's schema-version assertion and its
compatibility test. E3-Q2 / H138 also permits generated metadata in
`Solidity/Language/FeatureInfo.lean` and `docs/solidity-feature-inventory.md`;
regenerate those with the existing generator, never hand-edit them. H145 puts
receipts, reviews, timings, provenance, checksum manifests and handoffs in the
private coordination archive, not the code branch. No pin, workflow, generated
root or module-map changes are part of this lane.

## Citation map and limits

The original 13 present rows and the arithmetic under-citation are traced below.
Six definition-only rows become partial, with explicit reasons.

| Row | Current | Declaration (class, direction) | Scope and remaining gap |
|---|---|---|---|
| booleanLiterals | partial | `Solidity.Frontend.expr` (d, model) | Definition-only Boolean import branch; no general source/importer correspondence theorem. Downgraded present to partial under the non-d present gate (F8). |
| etherUnits | present | `Solidity.Source.TypingExamples.w_litUnit` (c, model)<br>`Solidity.unitFactor?` (d, model) | Concrete typed one-ether derivation only; factor table is definitional. No theorem covers all denomination folding and range checks. |
| timeUnits | partial | `Solidity.unitFactor?` (d, model) | Definition-only literal factor table; no unit-folding preservation theorem. Downgraded present to partial (F8). |
| boolType | partial | `Solidity.PrimTy.Denote` (d, model) | Boolean carrier is Bool by definition; no theorem of the full source typing requirement. Downgraded present to partial (F8). |
| parentheses | partial | `Solidity.expandExpr` (d, model) | Grouping macro branch only; no source evaluation-preservation theorem. Downgraded present to partial (F8). |
| ifStatement | present | `Solidity.iteStep_sound` (a, model)<br>`Solidity.Evm.compile_correct` (b, model) | Rule soundness is against intrinsic repository semantics. Compiler theorem additionally requires fragment admission, state simulation and local-room bound; neither proves source lowering or solc agreement. |
| breakStatement | present | `Solidity.lowerLoops` (c, model) | Class c traces lowerLoops plus guard-message regressions in Solidity/Examples/Tactics/Loops.lean:60-106; transformed syntax tests do not prove general lowering correctness (F3). |
| erc7201Builtin | present | `Solidity.Examples.Tactics.AbiFeatures.erc20_namespace` (c, model)<br>`Solidity.Examples.Tactics.AbiFeatures.empty_namespace` (c, model)<br>`Solidity.Examples.Tactics.AbiFeatures.utf8_namespace` (c, model) | Three concrete kernel namespace computations; no theorem relates runtime lowering to the ERC7201 root formula. General runtime formula agreement remains open. |
| msgSender | partial | `Solidity.TTx.msgSender` (d, model) | Definition-only uint256 context field, not address160 bound or external-self-call transition proof. Downgraded present to partial (F8). |
| blockTimestamp | partial | `Solidity.TTx.timestamp` (d, model) | Definition-only environment field; no clock guarantees asserted. Downgraded present to partial (F8). |
| typeName | present | `Solidity.Frontend.declarationMetadata` (c, model) | Importer definition tested by tests/solc/DeclarationMetadata.sol:26-29; compiler-supplied metadata, not an all-input source correspondence theorem. |
| interfaceId | present | `Solidity.Examples.Tactics.DeclarationMetadata.ownInterface` (c, model) | Concrete imported own-interface fixture only; selectors supplied by solc, not independently computed and proved equivalent. |
| errorEventSelector | present | `Solidity.Examples.Tactics.DeclarationMetadata.errorSelectors` (c, model)<br>`Solidity.Examples.Tactics.DeclarationMetadata.eventSelector` (c, model) | Concrete imported error/event selector fixtures only; no general signature-hash agreement theorem. |
| checkedArithmetic | partial | `Solidity.Evm.exp_tail` (a, model)<br>`Solidity.Evm.compile_correct` (b, model)<br>`Solidity.Evm.add_tail` (a, model)<br>`Solidity.Evm.sub_tail` (a, model)<br>`Solidity.Evm.mul_tail` (a, model)<br>`Solidity.Evm.div_tail` (a, model)<br>`Solidity.Evm.mod_tail` (a, model)<br>`Solidity.Evm.sadd_tail` (a, model)<br>`Solidity.Evm.ssub_tail` (a, model)<br>`Solidity.Evm.smul_tail` (a, model)<br>`Solidity.Evm.sdiv_tail` (a, model)<br>`Solidity.Evm.smod_tail` (a, model)<br>`Solidity.Evm.neg_run` (a, model)<br>`Solidity.Evm.tail_simT` (b, model)<br>`Solidity.Evm.compound_simT` (b, model)<br>`Solidity.Evm.bump_simT` (b, model) | uint256/int256 admitted symbolic-machine compiler fragment only. compile_correct has hP/hm/hL premises and permits coarse revert/fault outcomes; guards do not establish all source intermediate widths, pipeline orders or exact panic bytes. F8 under-citation corrected without upgrading partial. F1/F10 payment-disjunction and oracle limits, F2 source composition, F3 lowering, F4 symbolic storage, F5 coarse failures and F6 fragment boundaries remain open. |

## Partial rows and agreement gaps

All original partial rows have explicit mappings in
`scripts/check-feature-citations-partials.json`, in manifest order. They trace
relevant implementation definitions or narrow existing model theorems. A parser
branch is not an operational preservation theorem; a type constructor is not a
compiler typing theorem. Narrow storage/frame/creation laws do not establish
source or physical-EVM adequacy. Example/test-only traces remain class d with
notes; new kernel evidence is not inferred merely from a passing example.

The first twelve high-traffic rows comprise F8's nine sampled partial rows plus
checkedArithmetic, uncheckedArithmetic and evaluationOrder from its traceability
discussion. Ordinary external-call oracle semantics and the callback invariant
rule are distinguished from the self-body rule. Named class-b premises record
fragment, simulation, invariant and continuation boundaries.

The only model-to-solc citation is the finite numeric observation theorem and
paired external fixture validator. It covers 42 spellings and 18 accepted exact
values, retaining five lexical-versus-expression-stage differences. It does not
prove address checksum parity, hex byte-string decoding, denomination factors,
comment/specification preservation or general Yul/compiler correctness. Its
universal agreement gap remains open. Every other row explicitly records no
validated model-to-solc citation here, including legacy scope labels; those
labels are not new exclusions from the full compiler endpoint.

Bridge external-EVM instruction agreement, repository compiler simulation and
recorded coder-mode agreement are not solc compiler agreement. The historical
640-case generated matrix requires current semantic-input validation before it
can support this snapshot; retained historical results are not promoted here.

## Reproduction

The explicit mapping generator is `scripts/check-feature-citations-populate.py`;
it never upgrades current status. `scripts/check-feature-citations-docs.py`
reproduces this map and the roadmap metric. Metadata is regenerated only with
the existing `scripts/solidity-feature-audit.py`; its sole reader change accepts
schema versions 1 and 2 while retaining every other validation.

After building imports with the pinned toolchain:

```sh
python3 -I scripts/check-feature-citations-populate.py
python3 -I scripts/solidity-feature-audit.py
python3 -I scripts/check-feature-citations-docs.py --check
python3 -I scripts/check-feature-citations.test.py
python3 -I scripts/check-feature-citations-compat.test.py
python3 -I scripts/check-feature-citations.py --evidence-dir "$EVIDENCE_DIR"
```

The finite external numeric comparison is reproduced without modifying cases,
settings, expected outputs or pins:

```sh
python3 -I tests/sol-numeric-literals/generate-fixtures.py --check
node scripts/check-feature-citations-solc.mjs "$SOLJSON_0838"
python3 -I scripts/check-feature-citations-observations.py   --output tests/sol-numeric-literals/evidence/lean-fixtures.actual.json
python3 -I tests/sol-numeric-literals/differential.py
```

The observation-export command evaluates the imported observation definitions
fresh in a temporary Lean query, even when all imported artifacts are cached.
It supplies the ignored input required by differential.py; no expected fixture
is copied into that input. The original checker verifies the exact compiler
SHA256 and version. These
commands validate finite AST/numeric observations, not EVM execution or universal
compiler parity.

The citation checker command is the resolution recipe for every citation. It imports modules
and queries exact names and owning modules in the elaborated environment; a/b
require theorem declarations. It does not infer relevance or premise completeness
from a name. Stdlib modules and ordinary Lean identifier punctuation are supported.
Imports must be built; cache-fetched artifacts may need materializing. Queries
run serially with LEAN_NUM_THREADS=1, -j1 and an 8 GiB Lean memory cap. The optional
build-config generator adds weak bounded arguments without editing tracked pins.

Summary rowCells count a row once per cell, and can overlap across classes or
directions. Model-only/model-to-solc/uncited totals form a partition. A finite
model-to-solc citation does not close the general-agreement gap.

### Coordinator CI registration fragment

Place after library/example builds; do not change another lane's workflow here.
The explicit fetch supplies the old manifest required by the compatibility test
on a default shallow checkout. Regenerate the current integration tree's
document catalog with `python3 scripts/check-doc-navigation.py --write` after
staging this document, then run the navigation check before committing it.
The catalog and checker postdate this pinned base; do not backport a catalog
containing archived legacy evidence from the frozen tree.

```yaml
- name: Check feature theorem citations
  env:
    LEAN_NUM_THREADS: '1'
  run: |
    git fetch --no-tags --depth=1 origin a0a9ca15ba35fd6e8d9a9be10e4b6b45dbf45d3e
    python3 -I scripts/ci/restore-lake-artifacts.py
    python3 -I scripts/check-feature-citations-compat.test.py
    python3 -I scripts/check-feature-citations.test.py
    python3 -I scripts/check-feature-citations-docs.py --check
    python3 -I scripts/solidity-feature-audit.py --check
    python3 -I scripts/check-feature-citations.py
```

## Audit reconciliation and integration

This lane does not repair F1–F10. compile_correct retains F1/F10's payment
weaknesses, F2's missing general source composition, F3's unproved lowering,
F4's symbolic storage, F5's coarse failures and F6's fragment restriction.
Citations do not discharge F7's witness-build problem or F9's decision residue.
No theorem statement, proof budget, axiom, premise or exclusion is changed.

G00/G03 blocks are regenerated with their unchanged existing generators under
the E3-Q2/H82 doc-fix authorization. Regenerate them again from the eventual
integrated inputs. Routing/staging is not gate acceptance.
Library/full gates and independent final reviews are separate from name lookup.

Execution receipts, logs, timings, reviews and handoffs belong in the
[private coordination archive](https://github.com/SolidiKeY/solidity-lean-coord)
under `evidence/plan-e3-feature-citations-1107/e3-feature-citations/` (H145).
Exact archive commits and artifact hashes are supplied in CLOUDVM-RESULT.
