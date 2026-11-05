#!/usr/bin/env python3
"""Reproduce a draft constructor census. Family heuristics are not acceptance."""
import hashlib
import json
from pathlib import Path
import re

BASE = "6f3eedf0788ee1f8a3bcf230558c712ecdca04d5"
INPUTS = ["Solidity/Calculus/Rules.lean", "Solidity/Calculus/RuleShapes.lean",
          "Solidity/TestSuite/Refuted.lean", "tests/upstream/README.md",
          "Solidity/Calculus/CallbackRules.lean"]
PATTERNS = {
    "overflow": r"Assign|Increment|decrement|increment|binop",
    "division-minimum": r"Div|Mod|div|mod|OpAssign|binop|Binop",
    "index-bounds": r"Index|index|\[ie\]",
    "push-tail-length": r"[Pp]ush",
    "pop-delete": r"[Pp]op|[Dd]elete|delAt",
    "alias-capture-once": r"Capture|capture|unfold|Unfold|Alias|alias",
    "guard-polarity": r"ifElse|require|assert|assume",
    "rollback-payment": r"transfer|send|tryCall|catch|revert|pay\(",
    "callback-frames": r"tryCall|Call|functionBody|transfer|send"}


def census(root):
    items = []
    for source in (INPUTS[0], INPUTS[-1]):
        lines = (root / source).read_text().splitlines(keepends=True)
        owner = None
        for i, line in enumerate(lines):
            match = re.match(r"inductive (\w+)", line)
            if match:
                owner = match[1]
            match = re.match(r"  \| (\w+)", line)
            if not match or owner not in ("Taclet", "LeanTaclet", "CallbackTaclet", "Rule"):
                continue
            name = match[1]
            end = next((j for j in range(i + 1, len(lines))
                        if re.match(r"  \| |^inductive |^end ", lines[j])), len(lines))
            text = "".join(lines[i:end])
            families = [family for family, pattern in PATTERNS.items()
                        if re.search(pattern, name + "\n" + text)]
            if owner == "CallbackTaclet" and "callback-frames" not in families:
                families.append("callback-frames")
            items.append({"id": owner + "." + name, "file": source,
                          "line_start": i + 1, "line_end": end,
                          "span_sha256": hashlib.sha256(text.encode()).hexdigest(),
                          "families": families,
                          "operator_instances": "pending" if re.search(r"OpAssign|binop|Binop|Increment", name) else None,
                          "disposition": "pending-oracle-review" if families else
                          "outside-requested-families-pending-review"})
    return {"schema": 1, "base": BASE, "state": "draft-not-frozen",
            "production_inputs": {p: hashlib.sha256((root / p).read_bytes()).hexdigest() for p in INPUTS},
            "inventory": items, "families": list(PATTERNS), "mutants": [],
            "outstanding": ["Clause and operator-instance coverage is not yet exhaustive.",
                            "Review heuristic family classification before freezing.",
                            "Select one-change mutations and real semantic/inhabited oracles.",
                            "No score exists: zero mutants have run."]}


def extended_census(root):
    data = census(root)
    source = INPUTS[0]
    lines = (root / source).read_text().splitlines(keepends=True)
    start = next(i for i, line in enumerate(lines) if line.strip() == "namespace Tms")
    end = next(i for i in range(start + 1, len(lines)) if lines[i].strip() == "end Tms")
    definitions = []
    for i in range(start + 1, end):
        match = re.match(r"^(?:@\[[^\]]+\]\s*)?(?:def|abbrev)\s+([\w.]+)", lines[i])
        if match:
            definitions.append((i, "Tms." + match[1]))
    helpers = []
    for n, (i, name) in enumerate(definitions):
        stop = definitions[n + 1][0] if n + 1 < len(definitions) else end
        text = "".join(lines[i:stop])
        families = [family for family, pattern in PATTERNS.items() if re.search(pattern, name + "\n" + text)]
        item = {"id": name, "kind": "term-helper", "file": source, "line_start": i + 1,
                "line_end": stop, "span_sha256": hashlib.sha256(text.encode()).hexdigest(),
                "families": families, "disposition": "pending-full-clause-and-operator-review"}
        if name == "Tms.Term.binopC":
            generic = [row["id"] for row in data["inventory"] if re.search(r"OpAssign$", row["id"])]
            fixed = ["Taclet.storagePush" + op + "Assign" for op in ("Add", "Sub", "Mul", "Div", "Mod")]
            item.update(affected_constructor_uses=generic + fixed,
                        attribution="RuleSyntax/Schemas.lean compoundOps and pushArithmetic specialize numeric operator terms; size arithmetic is excluded.",
                        mutation_effect="Fixed-sub replacement changes generic non-sub operators; storagePushSubAssign remains the same at its fixed sub operator.")
        helpers.append(item)
    data["schema"] = 2
    data["inventory"] += helpers
    data["coverage_note"] = "Constructor census plus every Tms term-helper definition. Full clause/operator candidate coverage remains pending."
    data["outstanding"] = ["Review helper uses and full constructor clauses/operator instances before full freeze.",
                           "Add all nine families and selected oracles; pilot and development runs are not full acceptance."]
    return data


if __name__ == "__main__":
    root = Path(__file__).resolve().parents[4]
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--with-term-helpers", action="store_true")
    args = parser.parse_args()
    print(json.dumps(extended_census(root) if args.with_term_helpers else census(root), indent=2))
