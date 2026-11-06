#!/usr/bin/env python3
"""Revalidate immutable saved logs; this does not execute Lean again."""
import hashlib
import json
from pathlib import Path
import checked
import backend_controls


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def replay(root):
    evidence = root / "evidence/guard-checked-isolated"
    cases = json.loads((evidence / "cases.json").read_text())["cases"]
    result = json.loads((evidence / "result.json").read_text())
    if sha(evidence / "cases.json") != result["cases_sha256"]:
        raise ValueError("case snapshot drift")
    total = 0
    for case, record in zip(cases, result["cases"], strict=True):
        if case["id"] != record["id"] or record["status"] != "semantic-witness-development-pass":
            raise ValueError("missing case or failed development probe")
        for field in ("oracle", "witness"):
            if sha(evidence / case["id"] / (field + ".lean.txt")) != case[field + "_sha256"]:
                raise ValueError("executed source snapshot drift")
        if set(record["checks"]) != {phase + "-" + label for phase in ("baseline", "mutant") for label in ("compile", "oracle", "witness")}:
            raise ValueError("missing or unexpected phase/check")
        for key, check in record["checks"].items():
            log = evidence / case["id"] / (key + ".log")
            if sha(log) != check["log_sha256"]:
                raise ValueError("log hash drift")
            phase, label = key.split("-")
            if label == "compile": checked.success(check, log.read_text())
            elif (phase, label) in (("baseline", "witness"), ("mutant", "oracle")):
                expected = record["validation"][key]
                checked.source_link_rejection(check, log.read_text(), expected["file"], expected["line"])
            else: checked.success(check, log.read_text(), case[label + "_declarations"])
            total += 1
        if len(record["checks"]) != 6:
            raise ValueError("incomplete development case")
    controls = json.loads((root / "evidence/backend-controls-final/result.json").read_text())["checks"]
    for record in controls:
        log = root / "evidence/backend-controls-final" / (record["label"] + ".log")
        if not backend_controls.expected_outcome(record["label"], record, log.read_text()) or not record["container_cleaned"]:
            raise ValueError("backend control failed")
    if len(controls) != 4:
        raise ValueError("missing backend control")
    return {"semantic_checks_revalidated": total, "backend_controls_revalidated": len(controls),
            "scope_complete": False, "score": None, "boundary": "Saved-output validation replay, not a new Lean run"}


if __name__ == "__main__":
    print(json.dumps(replay(Path(__file__).resolve().parents[1]), indent=2))
