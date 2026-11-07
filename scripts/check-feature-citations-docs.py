#!/usr/bin/env python3
"""Regenerate/check citation design documentation and the roadmap metric."""
import argparse
from collections import Counter
import importlib.util
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
BASE="a0a9ca15ba35fd6e8d9a9be10e4b6b45dbf45d3e"
spec=importlib.util.spec_from_file_location("citation_core",ROOT/"scripts/check-feature-citations.py")
core=importlib.util.module_from_spec(spec);spec.loader.exec_module(core)
BEGIN="<!-- BEGIN_E3_MANIFEST_CITATIONS -->"
END="<!-- END_E3_MANIFEST_CITATIONS -->"
SELECT={"booleanLiterals","etherUnits","timeUnits","boolType","parentheses","ifStatement","breakStatement","erc7201Builtin","msgSender","blockTimestamp","typeName","interfaceId","errorEventSelector","checkedArithmetic"}

def generated(data):
    _,summary=core.validate(data)
    statuses=Counter(r["current"] for r in data["features"])
    cited=Counter(r["current"] for r in data["features"] if r["theorems"])
    uncited=Counter(r["current"] for r in data["features"] if not r["theorems"])
    uncited_text=", ".join(f"{k}={v}" for k,v in sorted(uncited.items())) or "none"
    classes={c:sum(any(t["class"]==c for t in r["theorems"]) for r in data["features"]) for c in "abcd"}
    metric=(f"### Manifest citations\n\nDerived from source snapshot `{BASE}`: "
            f"{summary['rowsWithCitations']} of {summary['rows']} rows carry {summary['citationEntries']} citation entries; "
            f"Cited present rows: {cited['present']}/{statuses['present']}; cited partial rows: {cited['partial']}/{statuses['partial']}. "
            f"Uncited rows by current status: {uncited_text}. "
            f"Rows with class a/b/c/d citations: {classes['a']}/{classes['b']}/{classes['c']}/{classes['d']} "
            "(overlapping evidence tags, not counts of fully proved language features). "
            f"Model-only rows: {summary['modelOnlyRows']}; model-to-solc rows: {summary['modelToSolcRows']} "
            "(finite numeric fixtures, class c). Six definition-only original present rows were downgraded to partial; "
            f"all {summary['modelToSolcGapRows']} rows retain explicit general-agreement gaps. "
            "No universal solc-equivalence or full-source theorem is inferred from these counts. "
            "See [the citation map](feature-work/e3-feature-citations.md).\n\n"
            "| Current | Class | Direction | Rows |\n|---|---|---|---|\n")
    for cell in summary["rowCells"]:
        metric+=f"| {cell['current']} | {cell['class']} | {cell['direction']} | {cell['rows']} |\n"
    metric+="\nCells overlap when a row cites multiple classes/directions.\n"
    old=(ROOT/"docs/feature-work/e3-feature-citations.md").read_text()
    intro=old.split("## Citation map and limits",1)[0]
    if "Optional `modelToSolcGap`" not in intro:
        intro=intro.replace("Optional `citationNotes` explains a bounded claim and its remaining gap.","Optional `citationNotes` explains a bounded claim and its remaining gap.\nOptional `modelToSolcGap` is nonempty text recording an open agreement obligation.")
    lane=intro+"## Citation map and limits\n\nThe original 13 present rows and the arithmetic under-citation are traced below.\nSix definition-only rows become partial, with explicit reasons.\n\n| Row | Current | Declaration (class, direction) | Scope and remaining gap |\n|---|---|---|---|\n"
    for r in data["features"]:
        if r["id"] not in SELECT:continue
        ts="<br>".join("`"+t["name"]+"` ("+t["class"]+", "+t["direction"]+")" for t in r["theorems"])
        lane+="| "+r["id"]+" | "+r["current"]+" | "+ts+" | "+r["citationNotes"].replace("|","\\|")+" |\n"
    lane+="""
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
python3 -I tests/sol-numeric-literals/differential.py
```

The original checker verifies the exact compiler SHA256 and version. These
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

```yaml
- name: Check feature theorem citations
  env:
    LEAN_NUM_THREADS: '1'
  run: |
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

G00/G03 generated blocks remain coordinator-owned and must be regenerated from
the eventual integrated inputs. Routing/staging is not gate acceptance.
Library/full gates and independent final reviews are separate from name lookup.

Execution receipts, logs, timings, reviews and handoffs belong in the
[private coordination archive](https://github.com/SolidiKeY/solidity-lean-coord)
under `evidence/plan-e3-feature-citations-1107/e3-feature-citations/` (H145).
Exact archive commits and artifact hashes are supplied in CLOUDVM-RESULT.
"""
    return lane,metric

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--check",action="store_true");args=ap.parse_args()
    data=json.loads((ROOT/"docs/solidity-features.json").read_text());lane,metric=generated(data)
    plan=ROOT/"docs/coverage-plan.md";old=plan.read_text()
    block=BEGIN+"\n"+metric+END+"\n\n"
    if BEGIN in old:
        a=old.index(BEGIN);b=old.index(END,a)+len(END);text=old[:a]+block.rstrip()+old[b:]
    else:text=old.replace("## Final proof obligations",block+"## Final proof obligations",1)
    for path,want in [(ROOT/"docs/feature-work/e3-feature-citations.md",lane),(plan,text)]:
        if args.check:
            if path.read_text()!=want:raise SystemExit("stale citation documentation: "+str(path.relative_to(ROOT)))
        else:path.write_text(want)
    print("citation documentation current" if args.check else "citation documentation generated")

if __name__=="__main__":main()
