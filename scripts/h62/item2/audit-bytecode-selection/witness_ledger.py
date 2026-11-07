#!/usr/bin/env python3
"""Link reviewed exact-domain helpers to a frozen inventory; preserve every gap.

This is an evidence linker, not a second proof checker. The Lean-checked macro
establishes the hypothesis transformation. Predicate definitions, inherited
obligations and all unlinked records remain uncovered.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
from census import BASE, mask

HELPER_PATH = "tests/h62/item2/audit-bytecode-selection/HypothesisDomains.lean"
NAMESPACE = "Solidity.H62.BytecodeSelection.HypothesisAudit."
LINKS = [
    ("Solidity.Backend.Selection.V2.RuntimeConsumer.consume", "runtime_consume_domain", False),
    ("Solidity.Backend.Selection.V2.FrameCertificate.capacity", "capacity_domain", False),
    ("Solidity.Backend.Selection.V2.FrameCertificate.prefixes", "prefixes_domain", False),
    ("Solidity.Backend.Selection.V2.no_overfull_output", "no_overfull_domain", False),
    ("Solidity.Backend.Selection.V2.Controls.reject_push_program", "reject_push_domain_impossible", True),
]

FAILURE_GROUP = (
    "tests/h62/item2/audit-bytecode-selection/FailurePathsWitnesses.lean",
    "Solidity.H62.BytecodeSelection.FailureFixture.",
    [("Solidity.Backend.FailurePaths.literal_statement", "literal_statement_domain", False),
     ("Solidity.Backend.FailurePaths.encoded_return", "encoded_return_domain", False)],
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def link(inventory, checked, repo, groups=None):
    if inventory["base"] != BASE:
        raise ValueError("wrong frozen base")
    names = [row["name"] for row in inventory["records"]]
    if len(set(names)) != len(names):
        raise ValueError("duplicate inventory declaration")
    result = {row["name"]: dict(row, coverage="uncovered; linkage review required", witness=None) for row in inventory["records"]}
    claimed = set()
    for helper_path, namespace, links in groups or [(HELPER_PATH, NAMESPACE, LINKS)]:
        source = repo / helper_path
        matches = [row for row in checked if row["path"] == helper_path]
        if len(matches) != 1:
            raise ValueError("missing unique helper check")
        check = matches[0]
        if check["exit"] != 0 or check["stop"] or not check["source_unchanged_during_check"] or check["source_sha256"] != sha(source):
            raise ValueError("helper source check mismatch")
        output = Path(check["command"][check["command"].index("-o") + 1])
        if not check["output_sha256"] or sha(output) != check["output_sha256"]:
            raise ValueError("helper output check mismatch")
        log = Path(check["log"]).read_text()
        clean = mask(source.read_text())
        for target, helper, negative in links:
            if target in claimed:
                raise ValueError("duplicate witness target across groups")
            claimed.add(target)
            if target not in result or not result[target]["is_theorem"]:
                raise ValueError("target absent or not originally a theorem: " + target)
            prefix = r"¬\s*\(\s*" if negative else ""
            suffix = r"\s*\)\s*:=" if negative else r"\s*:="
            pattern = r"theorem\s+" + re.escape(helper) + r"\s*:\s*" + prefix + r"hypotheses_of%\s+" + re.escape(target) + suffix
            if len(re.findall(pattern, clean)) != 1:
                raise ValueError("exact helper/target linkage mismatch: " + helper)
            fq = namespace + helper
            axiom_match = re.findall(r"'" + re.escape(fq) + r"' depends on axioms: \[([^\]]*)\]", log)
            if len(axiom_match) != 1:
                raise ValueError("missing unique helper axiom output: " + helper)
            axioms = sorted(part.strip() for part in axiom_match[0].split(",") if part.strip())
            if not set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}:
                raise ValueError("unexpected helper axiom")
            result[target]["coverage"] = "intentional negative control: domain refuted" if negative else "simultaneous explicit hypothesis domain witnessed"
            result[target]["witness"] = dict(name=fq, source_path=helper_path, source_sha256=check["source_sha256"], output_sha256=check["output_sha256"], proof_log=check["log"], axioms=axioms, establishes_original_conclusion=False)
    return [result[name] for name in sorted(result)]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ["repo", "inventory", "checked", "output"]:
        p.add_argument("--" + name, type=Path, required=True)
    p.add_argument("--include-failure", action="store_true", help="also link the checked failure-path audit group")
    args = p.parse_args()
    inventory = json.loads(args.inventory.read_text())
    groups = [(HELPER_PATH, NAMESPACE, LINKS), FAILURE_GROUP] if args.include_failure else None
    rows = link(inventory, json.loads(args.checked.read_text()), args.repo.resolve(), groups=groups)
    summary = {"records": len(rows), "positive_domain_witnesses": sum(row["coverage"] == "simultaneous explicit hypothesis domain witnessed" for row in rows), "refuted_control_domains": sum(row["coverage"] == "intentional negative control: domain refuted" for row in rows), "uncovered_records": sum(row["witness"] is None for row in rows), "uninspected_files": len(inventory["uninspected_paths"])}
    args.output.write_text(json.dumps(dict(base=BASE, inventory_sha256=sha(args.inventory), verification_sha256=sha(args.checked), boundary=__doc__, summary=summary, uninspected_paths=inventory["uninspected_paths"], records=rows), indent=2, ensure_ascii=False) + "\n")
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
