# Feature manifest citations (E3 / F8)

The manifest separates implementation status from evidence strength. A cited
name is a trace to a declaration, not a claim of complete Solidity support.
The source snapshot is `a0a9ca15ba35fd6e8d9a9be10e4b6b45dbf45d3e`.

## Scope contract

Schema version 2 retains existing fields and adds `theorems` per row. Each entry
has `name` (fully qualified Lean declaration), `module` (owning import module),
`class`, `premises` (named strings), and `direction` (`model` or `model-to-solc`).
Optional `citationNotes` explains a bounded claim and its remaining gap.

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

The original 13 present rows are traced below, together with the arithmetic
under-citation. Six definition-only rows are downgraded to partial; the reasons
are explicit rather than disguised by a stronger evidence class.

| Row | Current | Declaration (class) | Scope and remaining gap |
|---|---|---|---|
| booleanLiterals | partial | `Solidity.Frontend.expr` (d) | Definition-only Boolean import branch; no general source/importer correspondence theorem. Downgraded present to partial under the non-d present gate (F8). |
| etherUnits | present | `Solidity.Source.TypingExamples.w_litUnit` (c)<br>`Solidity.unitFactor?` (d) | Concrete typed one-ether derivation only; factor table is definitional. No theorem covers all denomination folding and range checks. |
| timeUnits | partial | `Solidity.unitFactor?` (d) | Definition-only literal factor table; no unit-folding preservation theorem. Downgraded present to partial (F8). |
| boolType | partial | `Solidity.PrimTy.Denote` (d) | Boolean carrier is Bool by definition; no theorem of the full source typing requirement. Downgraded present to partial (F8). |
| parentheses | partial | `Solidity.expandExpr` (d) | Grouping macro branch only; no source evaluation-preservation theorem. Downgraded present to partial (F8). |
| ifStatement | present | `Solidity.iteStep_sound` (a)<br>`Solidity.Evm.compile_correct` (b) | Rule soundness is against intrinsic repository semantics. Compiler theorem additionally requires fragment admission, state simulation and local-room bound; neither proves source lowering or solc agreement. |
| breakStatement | present | `Solidity.lowerLoops` (c) | Class c traces lowerLoops plus guard-message regressions in Solidity/Examples/Tactics/Loops.lean:60-106; transformed syntax tests do not prove general lowering correctness (F3). |
| erc7201Builtin | present | `Solidity.Examples.Tactics.AbiFeatures.erc20_namespace` (c)<br>`Solidity.Examples.Tactics.AbiFeatures.empty_namespace` (c)<br>`Solidity.Examples.Tactics.AbiFeatures.utf8_namespace` (c) | Three concrete kernel namespace computations; no theorem relates runtime lowering to the ERC7201 root formula. General runtime formula agreement remains open. |
| msgSender | partial | `Solidity.TTx.msgSender` (d) | Definition-only uint256 context field, not address160 bound or external-self-call transition proof. Downgraded present to partial (F8). |
| blockTimestamp | partial | `Solidity.TTx.timestamp` (d) | Definition-only environment field; no clock guarantees asserted. Downgraded present to partial (F8). |
| typeName | present | `Solidity.Frontend.declarationMetadata` (c) | Importer definition tested by tests/solc/DeclarationMetadata.sol:26-29; compiler-supplied metadata, not an all-input source correspondence theorem. |
| interfaceId | present | `Solidity.Examples.Tactics.DeclarationMetadata.ownInterface` (c) | Concrete imported own-interface fixture only; selectors supplied by solc, not independently computed and proved equivalent. |
| errorEventSelector | present | `Solidity.Examples.Tactics.DeclarationMetadata.errorSelectors` (c)<br>`Solidity.Examples.Tactics.DeclarationMetadata.eventSelector` (c) | Concrete imported error/event selector fixtures only; no general signature-hash agreement theorem. |
| checkedArithmetic | partial | `Solidity.Evm.exp_tail` (a)<br>`Solidity.Evm.compile_correct` (b)<br>`Solidity.Evm.add_tail` (a)<br>`Solidity.Evm.sub_tail` (a)<br>`Solidity.Evm.mul_tail` (a)<br>`Solidity.Evm.div_tail` (a)<br>`Solidity.Evm.mod_tail` (a)<br>`Solidity.Evm.sadd_tail` (a)<br>`Solidity.Evm.ssub_tail` (a)<br>`Solidity.Evm.smul_tail` (a)<br>`Solidity.Evm.sdiv_tail` (a)<br>`Solidity.Evm.smod_tail` (a)<br>`Solidity.Evm.neg_run` (a)<br>`Solidity.Evm.tail_simT` (b)<br>`Solidity.Evm.compound_simT` (b)<br>`Solidity.Evm.bump_simT` (b) | uint256/int256 admitted symbolic-machine compiler fragment only. compile_correct has hP/hm/hL premises and permits coarse revert/fault outcomes; guards do not establish all source intermediate widths, pipeline orders or exact panic bytes. F8 under-citation corrected without upgrading partial. F1/F10 payment-disjunction and oracle limits, F2 source composition, F3 lowering, F4 symbolic storage, F5 coarse failures and F6 fragment boundaries remain open. |

The owning module and full named premises are stored beside each declaration in
the manifest. Normal word-range hypotheses in arithmetic guard theorems state
the input domain; typed compiler interfaces additionally list fragment and
representation premises as class b. Private compiler helper names are not
invented: the public `tail_simT`, `compound_simT` and `bump_simT` interfaces are
reused. The exponentiation guard is included through `Evm.exp_tail`.

## Reproduction and integration

The audited mappings are explicit data in
`scripts/check-feature-citations-populate.py`. It never upgrades `current`.
The metadata generator remains `scripts/solidity-feature-audit.py`. Its version
assertion accepts 1 and 2; all other validation is retained. The compatibility
test covers both the exact old manifest and the new one, additive rendering,
unsupported versions and retained evidence-path validation.

After building imports with the pinned toolchain, use:

```sh
python3 -I scripts/check-feature-citations.test.py
python3 -I scripts/check-feature-citations-compat.test.py
python3 -I scripts/solidity-feature-audit.py --check
python3 -I scripts/check-feature-citations.py --evidence-dir "$EVIDENCE_DIR"
```

The final command is the evidence recipe for every row in the table. It emits
only a sorted JSON summary on stdout. `rowCells` counts rows once per cell and
can overlap across classes/directions; it is not a partition. Model-only,
model-to-solc and uncited row totals are a partition. Imports are checked
serially with `LEAN_NUM_THREADS=1`, `-j1`, and an 8 GiB Lean memory cap. The
optional build-config generator supplies bounded weak compiler arguments in an
off-git Lake configuration without changing tracked build settings.

### Coordinator CI registration fragment

Place after existing library/example builds. Cache-fetched artifacts must be
materialized before direct Lean queries. The fragment does not edit workflows.

```yaml
- name: Check feature theorem citations
  env:
    LEAN_NUM_THREADS: '1'
  run: |
    python3 -I scripts/ci/restore-lake-artifacts.py
    python3 -I scripts/check-feature-citations-compat.test.py
    python3 -I scripts/check-feature-citations.test.py
    python3 -I scripts/solidity-feature-audit.py --check
    python3 -I scripts/check-feature-citations.py
```

## Audit reconciliation

This lane cites existing results; it does not repair F1–F10. In particular,
`compile_correct` retains F1/F10 payment-disjunction and history-free oracle
limits, F2's missing general source composition, F3's unproved lowering, F4's
symbolic storage, F5's coarse failures, and F6's admitted fragment. F7's witness
build coverage and F9's decision-procedure residue are not discharged by adding
citations. Finite examples are not promoted to generic theorems. Ordinary model
or external-EVM agreement must not be mislabeled solc compiler agreement.

## Remaining queue and handoff

The high-traffic partial inventory, remaining partial rows, model-to-solc
citations/gaps and final metric are the next ordered checkpoints. Their final
reviews and library/full gates remain separate obligations. The frozen audit
summarizes nine sampled partial rows despite advertising twelve; the planned
first twelve also include checkedArithmetic, uncheckedArithmetic and
evaluationOrder, which F8 explicitly discusses under traceability.

Validation and handoff records live in the
[private coordination archive](https://github.com/SolidiKeY/solidity-lean-coord)
under `evidence/plan-e3-feature-citations-1107/e3-feature-citations/`.
The exact archive commit and artifact hashes are supplied in CLOUDVM-RESULT.
