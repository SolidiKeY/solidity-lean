#!/usr/bin/env python3
"""Guard truncated, duplicate and stale witness logs from earning fresh audit credit.

This checks supplied local receipts, not their authenticity or historical replay.
Raw leading schemas remain distinct from semantic interface classification.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
from witness_plan import ROOT, code, unique
from witness_build import closure, validate_build

PREFIX = "H62_WITNESS_AUDIT "
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def reconcile(plan, log, receipt):
    unique(plan["rows"])
    if not plan["rows"] or any(plan[k] is not False for k in
                               ("kernel_checked", "historical_replay", "meaning_checked")):
        raise ValueError("fresh source-only plan required")
    if (receipt["exit"] != 0 or receipt["process_exit"] != 0 or
            receipt["resource_stop"] is not False or
            receipt["minimum_parent_headroom_bytes"] < 4 * 1024**3 or
            receipt["limits"] != {"memory_max": 12 * 1024**3,
                                  "memory_swap_max": 0, "lean_num_threads": 1}):
        raise ValueError("unsuccessful or out-of-policy runtime receipt")
    rows = []
    for line in log.splitlines():
        if PREFIX in line:
            if not line.startswith(PREFIX):
                raise ValueError("unexpected audit prefix context")
            row = json.loads(line[len(PREFIX):])
            n, p = row["leading_binders"], row["prop_binders"]
            if type(n) is not int or type(p) is not int or not 0 <= p <= n:
                raise ValueError("invalid binder counts")
            kind = "no-input-tuple" if n == 0 else (
                "inputs-without-premises" if p == 0 else "joint-premises")
            if row["kind"] != kind:
                raise ValueError("schema category mismatch")
            for key in ("witness_axioms", "target_axioms"):
                if not isinstance(row[key], list) or any(a not in ALLOWED for a in row[key]):
                    raise ValueError("unapproved axiom")
            rows.append(row)
    unique(rows)
    identity = lambda r: (r["witness"], r["target"])
    if {identity(r) for r in rows} != {identity(r) for r in plan["rows"]}:
        raise ValueError("audit rows do not exactly cover plan")
    return {"associations": len(rows), "kind_counts": dict(Counter(r["kind"] for r in rows)),
            "input_tuple_certificates": sum(r["leading_binders"] > 0 for r in rows),
            "rows": rows, "historical_replay": False, "meaning_checked": False,
            "semantic_interface_classification": "pending", "receipt_authenticity_checked": False}


def snapshot(plan_path, generated):
    sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
    plan = json.loads(plan_path.read_text())
    sources = {}
    for path, digest in plan["source_sha256"].items():
        source = Path(path)
        resolved = (ROOT / source).resolve()
        if source.is_absolute() or ".." in source.parts or not resolved.is_relative_to(ROOT):
            raise ValueError("invalid source path")
        sources[path] = sha(resolved)
        if sources[path] != digest:
            raise ValueError("stale source: " + path)
    planner = sha(Path(__file__).with_name("witness_plan.py"))
    if planner != plan["planner_sha256"] or sha(generated) != plan["generated_sha256"]:
        raise ValueError("planner or generated hash changed")
    if generated.read_bytes() != code(plan).encode():
        raise ValueError("generated code differs from source plan")
    return {"plan": sha(plan_path), "generated": sha(generated), "planner": planner,
            "sources": sources, "closure": closure(generated),
            "execution_scripts": {name: sha(Path(__file__).with_name(name)) for name in
                                  ("witness_build.py", "run_witness_results.py", "witness_results.py")}}


def audit_command(generated, compiled):
    return ["python3", str(Path(__file__).with_name("witness_build.py").resolve()),
            "--generated", str(generated.resolve()), "--build", str(compiled.with_suffix(".build").resolve()),
            "--record", str(compiled.resolve())]


def check_binding(binding, current, receipt, generated, log_sha, receipt_sha):
    if "compiled_record" not in binding or "compiled_sha256" not in binding:
        raise ValueError("fresh compiled closure binding required")
    compiled = Path(binding["compiled_record"])
    if (compiled.is_symlink() or compiled.resolve().is_relative_to(ROOT) or
            hashlib.sha256(compiled.read_bytes()).hexdigest() != binding["compiled_sha256"]):
        raise ValueError("compiled closure record substitution")
    validate_build(json.loads(compiled.read_text()), generated)
    if (binding["before"] != current or binding["after"] != current or
            binding["command"] != audit_command(generated, compiled) or
            receipt["command"] != binding["command"] or
            binding["log_sha256"] != log_sha or binding["receipt_sha256"] != receipt_sha):
        raise ValueError("execution inputs, command or outputs not bound")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("plan", "generated", "log", "receipt", "binding", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists() or args.output.is_symlink() or args.output.resolve().is_relative_to(ROOT):
        raise ValueError("new external output required")
    sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
    plan = json.loads(args.plan.read_text())
    current = snapshot(args.plan, args.generated)
    receipt = json.loads(args.receipt.read_text())
    if Path(receipt["log"]).resolve() != args.log.resolve():
        raise ValueError("receipt names a different log")
    check_binding(json.loads(args.binding.read_text()), current, receipt, args.generated,
                  sha(args.log), sha(args.receipt))
    result = reconcile(plan, args.log.read_text(), receipt)
    result["input_sha256"] = {name: sha(getattr(args, name)) for name in
                              ("plan", "generated", "log", "receipt", "binding")}
    with args.output.open("x") as out:
        out.write(json.dumps(result, sort_keys=True, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k not in ("rows", "input_sha256")}))


if __name__ == "__main__":
    main()
