#!/usr/bin/env python3
"""Development probes only. This is not the whole frozen-manifest runner.

Every semantic counterexample must pass under the actual mutant and fail at
its source link under the normal baseline. No score is produced here. The
caller holds the writer lock, and production inputs remain read-only.
"""
import hashlib
import io
import json
import re
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import bounded
import checked
from runner import mutate


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_imports(imports, cache_data):
    base = {"Solidity.Calculus.Rules", "Solidity.Calculus.PremiseSound"}
    if imports == base:
        return
    callback = "Solidity.Calculus.CallbackHolds"
    if imports == base | {callback} and callback in cache_data["roots"] and callback in cache_data["ordered_modules"]:
        return
    raise ValueError("unreviewed oracle import or missing callback cache")


def probe(repo, cases_path, output, cache_tree, cache_manifest):
    cases_data = json.loads(cases_path.read_text())
    cache_data = json.loads(cache_manifest.read_text())
    if cases_data["base"] != "6f3eedf0788ee1f8a3bcf230558c712ecdca04d5":
        raise ValueError("development base mismatch")
    ids = [case["id"] for case in cases_data["cases"]]
    if len(ids) != len(set(ids)) or any(not re.fullmatch(r"[a-z0-9.-]+", item) for item in ids):
        raise ValueError("unsafe or duplicate case IDs")
    for case in cases_data["cases"]:
        for field in ("oracle", "witness"):
            name = Path(case[field])
            if name.is_absolute() or ".." in name.parts or str(name.parent) != "tests/h28-sol/mutation-testing/oracles":
                raise ValueError("oracle path is not in the owned oracle directory")
            source = (repo / name).read_text()
            clean = checked.oracle_code(source)
            imports = {ln[7:] for ln in clean.splitlines() if ln.startswith("import ")}
            validate_imports(imports, cache_data)
            if re.search(r"\b(axiom|sorry|admit|unsafe|native_decide|maxHeartbeats|elab|macro|run_cmd)\b|#eval", clean):
                raise ValueError("oracle contains an unapproved trust or execution construct")
    if not cache_data["complete"] or cache_data["base"] != cases_data["base"]:
        raise ValueError("incomplete or wrong-base cache")
    cache = cache_tree / ".lake/build/lib/lean"
    for artifact, expected in cache_data["artifact_sha256"].items():
        if sha(cache / artifact) != expected:
            raise ValueError("cache artifact identity mismatch")
    archive = subprocess.check_output(["git", "archive", cases_data["base"]], cwd=repo)
    output.mkdir(parents=True, exist_ok=False)
    (output / "cases.json").write_bytes(cases_path.read_bytes())
    result = {"development_only": True, "score": None, "scope_complete": False,
              "cases_sha256": sha(cases_path), "cache_manifest_sha256": sha(cache_manifest), "cases": []}
    for case in cases_data["cases"]:
        ev = output / case["id"]
        ev.mkdir()
        record = {"id": case["id"], "source_sha256": {}, "checks": {}, "validation": {}, "status": "pending"}
        result["cases"].append(record)
        # Copy exact oracle sources once, retaining immutable executed text.
        for field in ("oracle", "witness"):
            source = repo / case[field]
            if sha(source) != case[field + "_sha256"]:
                raise ValueError("oracle source drift")
            record["source_sha256"][case[field]] = sha(source)
            (ev / (field + ".lean.txt")).write_bytes(source.read_bytes())
        for phase in ("baseline", "mutant"):
            with tempfile.TemporaryDirectory(prefix="h28-" + phase + "-", dir="/workspace/h28-runtime") as scratch:
                tree = Path(scratch)
                with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
                    tar.extractall(tree, filter="data")
                for path, expected in cache_data["source_sha256"].items():
                    if sha(tree / path) != expected:
                        raise ValueError("pinned production source drift")
                for field in ("oracle", "witness"):
                    dest = tree / case[field]
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    dest.write_bytes((repo / case[field]).read_bytes())
                # The current guarded probes target Rules. All cached reverse
                # dependents of Rules are excluded; no stale proof about it may
                # be imported after changing its constructor type.
                forbidden = {"Solidity.Calculus.Rules", "Solidity.Calculus.Taclet",
                             "Solidity.Calculus.CallbackRules", "Solidity.Calculus.RuleKit"}
                if case["target"] != "Solidity/Calculus/Rules.lean":
                    raise ValueError("development prober supports Rules targets only")
                for module in cache_data["ordered_modules"]:
                    if module in forbidden:
                        continue
                    artifact = module.replace(".", "/") + ".olean"
                    dest = tree / ".lake/build/lib/lean" / artifact
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    dest.symlink_to(Path("/cache") / artifact)
                if phase == "mutant":
                    change = mutate(tree, case)
                    (ev / "mutant.patch").write_text(change.pop("diff"))
                    record["mutation"] = change
                for label, source, artifact in [
                    ("compile", case["target"], ".lake/build/lib/lean/Solidity/Calculus/Rules.olean"),
                    ("oracle", case["oracle"], None), ("witness", case["witness"], None)]:
                    key = phase + "-" + label
                    log = ev / (key + ".log")
                    check = bounded.lean(tree, source, log, output=artifact, cache=cache)
                    check["log_sha256"] = sha(log)
                    record["checks"][key] = check
                    (ev / "result.json").write_text(json.dumps(record, indent=2) + "\n")
                    (output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
                    text = log.read_text()
                    if label == "compile":
                        validation = checked.success(check, text)
                    elif (phase, label) in (("baseline", "witness"), ("mutant", "oracle")):
                        line = next(i for i, ln in enumerate((tree / source).read_text().splitlines(), 1)
                                    if ln.startswith("theorem source_link :"))
                        validation = checked.source_link_rejection(check, text, source, line)
                    else:
                        validation = checked.success(check, text, case[label + "_declarations"])
                    record["validation"][key] = validation
                    # Audit every pinned production input and both oracle files.
                    for path, expected in cache_data["source_sha256"].items():
                        actual = record.get("mutation", {}).get("after_sha256") if phase == "mutant" and path == case["target"] else expected
                        if sha(tree / path) != actual:
                            raise ValueError("source changed during Lean command")
                    for field in ("oracle", "witness"):
                        if sha(tree / case[field]) != case[field + "_sha256"]:
                            raise ValueError("oracle source changed during command")
                    (ev / "result.json").write_text(json.dumps(record, indent=2) + "\n")
                    print(case["id"], key, check["exit"], "validated", flush=True)
        record["status"] = "semantic-witness-development-pass"
        (ev / "result.json").write_text(json.dumps(record, indent=2) + "\n")
        (output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


if __name__ == "__main__":
    repo = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
    destination = Path(sys.argv[1]).resolve()
    try:
        probe(repo, repo / "tests/h28-sol/mutation-testing/guard-cases.draft.json", destination,
              Path("/workspace/h28-runtime/prepared-base-6f3eedf0"),
              repo / "tests/h28-sol/mutation-testing/evidence/cache-bootstrap/manifest.json")
    except Exception as exc:
        destination.mkdir(parents=True, exist_ok=True)
        (destination / "failure.json").write_text(json.dumps({"status": "development-error", "error": str(exc)}, indent=2) + "\n")
        raise
