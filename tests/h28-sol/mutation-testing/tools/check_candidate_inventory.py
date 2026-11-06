#!/usr/bin/env python3
"""Serial VM gate for the complete declaration census and finite operator tables.

Generated inputs/objects/logs stay outside Git. No production source is edited.
This gate never grants assignment acceptance or a mutation score.
"""
import argparse
import fcntl
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import tarfile
import time
import uuid
import bounded
import bulk_inputs
import candidate_inventory as census
import checked

LOCK = Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
CACHE_TREE = Path("/workspace/h28-runtime/prepared-base-6f3eedf0")
CACHE_RECEIPT = Path("tests/h28-sol/mutation-testing/evidence/cache-bootstrap/manifest.json")
CACHE_SHA = "edea3b40feb29c9dd7a792a037d0ae1f05dae13fef7381640b315b53836dc1ec"


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_printed_census(text, catalog):
    parsed = checked.messages(text); inventories = {}
    expected = {owner: {r["id"].split(".", 1)[1] for r in catalog["declarations"] if r["kind"] == "constructor" and r["id"].split(".")[0] == owner} for owner in census.OWNERS}
    expected.update({name: set(values) for name, values in catalog["enums"].items()})
    for owner, names in expected.items():
        messages = [m["data"] for m in parsed if re.match(r"inductive Solidity\." + re.escape(owner) + r"(?:\s|[.:])", m["data"])]
        if len(messages) != 1 or "constructors:" not in messages[0]:
            raise ValueError("missing complete printed constructor family: " + owner)
        constructors = messages[0].split("constructors:", 1)[1]
        actual = re.findall(r"Solidity\." + re.escape(owner) + r"\.(\w+)\s*:", constructors)
        if len(actual) != len(set(actual)) or set(actual) != names:
            raise ValueError("source/kernel constructor inventory mismatch: " + owner)
        inventories[owner] = sorted(actual)
    return inventories


def version_probe(output):
    guard = bounded.headroom(); start = time.monotonic(); name = "h28-inventory-version-" + uuid.uuid4().hex
    versions = bounded.DOCKER + ["run", "--name", name, "--pull=never", "--memory=2g", "--memory-swap=2g", "--network=none", "--mount", "type=bind,src=" + str(bounded.RUNTIME) + ",dst=/lean,readonly", bounded.IMAGE, "bash", "-c", "set -e; test $(cat /sys/fs/cgroup/memory.max) = 2147483648; test $(cat /sys/fs/cgroup/memory.swap.max) = 0; /lean/bin/lean --version; /lean/bin/lake --version"]
    completed = None; failure = None
    try:
        completed = subprocess.run(versions, env=bounded.docker_env(), capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.SubprocessError) as exc:
        failure = type(exc).__name__ + ": " + str(exc)
    finally:
        cleanup = bounded.remove_owned(name, bounded.docker_env())
        record = {"command": versions, "container_name": name, "exit": completed.returncode if completed else None,
                  "seconds": time.monotonic() - start, "preflight": guard, "container_memory_limit": 2 * 1024**3,
                  "swap_limit": 0, "cleanup_confirmed": cleanup, "failure": failure}
        text = completed.stdout + completed.stderr if completed else failure or "version probe did not execute"
        (output / "versions.log").write_text(text)
        record["log_sha256"] = sha(output / "versions.log"); save(output / "versions.json", record)
        if not cleanup:
            raise bounded.CleanupError({**record, "kind": "error"})
    if completed is None or completed.returncode != 0 or "Lean (version 4.24.0" not in completed.stdout or "Lake version 5.0.0-src+797c613" not in completed.stdout:
        raise ValueError("runtime version gate failed")
    return record, completed.stdout


def run(repo, output):
    output.mkdir(parents=True, exist_ok=False)
    result = {"gate_head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip(),
              "audit_complete": False, "scope_complete": False, "score": None, "checks": {}}
    save(output / "result.json", result)
    catalog = census.build(repo)
    data = bulk_inputs.read(repo, repo / CACHE_RECEIPT)
    if census.digest(data) != CACHE_SHA: raise ValueError("cache receipt trust anchor changed")
    cache = json.loads(data); cache_root = CACHE_TREE / ".lake/build/lib/lean"
    if not cache["complete"] or cache["base"] != census.BASE: raise ValueError("wrong/incomplete cache")
    for source, expected in cache["source_sha256"].items():
        frozen = subprocess.check_output(["git", "show", census.BASE + ":" + source], cwd=repo)
        if census.digest(frozen) != expected or sha(repo / source) != expected: raise ValueError("cache source drift")
    for artifact, expected in cache["artifact_sha256"].items():
        if sha(cache_root / artifact) != expected: raise ValueError("cache output drift")
    result["cache_manifest_sha256"] = census.digest(data)
    runtime_pins = set()
    for item in catalog["frozen_manifests"]:
        frozen = json.loads(bulk_inputs.read(repo, repo / item["file"]))
        runtime_pins.add((frozen["runtime_lean_sha256"], frozen["measurement_binary_sha256"]))
    if len(runtime_pins) != 1 or (sha(bounded.RUNTIME / "bin/lean"), sha(Path("/workspace/h28-runtime/measure"))) not in runtime_pins:
        raise ValueError("runtime/instrumentation identity drift")
    result["versions"], version_text = version_probe(output)
    tree = output / "tree"; tree.mkdir()
    archive = subprocess.check_output(["git", "archive", census.BASE], cwd=repo)
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar: tar.extractall(tree, filter="data")
    for artifact in cache["artifact_sha256"]:
        dest = tree / ".lake/build/lib/lean" / artifact; dest.parent.mkdir(parents=True, exist_ok=True)
        dest.symlink_to(Path("/cache") / artifact)
    for source, expected in cache["source_sha256"].items():
        if sha(tree / source) != expected: raise ValueError("private source drift")
    key = bounded.lean(tree, "Solidity/KeySort.lean", output / "keysort.log", cache=cache_root)
    checked.success(key, (output / "keysort.log").read_text()); result["checks"]["keysort"] = key
    save(output / "result.json", result)
    print(version_text.strip(), flush=True); print("KeySort exit=0; RUNTIME_GATE_PASS", flush=True)
    source, declarations = census.lean_source(catalog)
    (output / "InventoryAudit.lean").write_text(source); (tree / "InventoryAudit.lean").write_text(source)
    positive = bounded.lean(tree, "InventoryAudit.lean", output / "positive.log", output=".lake/build/lib/lean/InventoryAudit.olean", cache=cache_root)
    result["checks"]["positive"] = positive; save(output / "result.json", result)
    certificate = checked.success(positive, (output / "positive.log").read_text(), declarations)
    printed = check_printed_census((output / "positive.log").read_text(), catalog)
    catalog["kernel_constructor_inventories"] = printed
    catalog["helper_consumers"] = census.attach_kernel_references(catalog, certificate["signatures"])
    catalog["kernel_certificate"] = certificate
    artifact = tree / ".lake/build/lib/lean/InventoryAudit.olean"
    if artifact.is_symlink() or not artifact.is_file() or artifact.stat().st_size == 0:
        raise ValueError("successful gate lacks compiled object")
    (output / "InventoryAudit.olean").write_bytes(artifact.read_bytes())
    negative_source, _ = census.lean_source(catalog, corrupt=True)
    (output / "InventoryNegative.lean").write_text(negative_source); (tree / "InventoryNegative.lean").write_text(negative_source)
    negative = bounded.lean(tree, "InventoryNegative.lean", output / "negative.log", output=".lake/build/lib/lean/InventoryNegative.olean", cache=cache_root)
    result["checks"]["known-bad-table"] = negative; save(output / "result.json", result)
    errors = [m for m in checked.messages((output / "negative.log").read_text()) if m["severity"] in {"error", "warning"}]
    line = next(i for i, text in enumerate(negative_source.splitlines(), 1) if text.startswith("theorem accepts_all"))
    if negative["kind"] != "exit" or negative["exit"] != 1 or not errors or any(m["severity"] != "error" or m["fileName"] != "InventoryNegative.lean" or m["pos"]["line"] != line or not m["data"].startswith("Tactic `rfl` failed") for m in errors):
        raise ValueError("known-bad table was not independently rejected at its universal proof")
    if (tree / ".lake/build/lib/lean/InventoryNegative.olean").exists(): raise ValueError("failed negative control retained an object")
    for source, expected in cache["source_sha256"].items():
        if sha(tree / source) != expected or sha(repo / source) != expected: raise ValueError("production source changed during gate")
    for artifact, expected in cache["artifact_sha256"].items():
        if sha(cache_root / artifact) != expected: raise ValueError("normal cache changed during gate")
    catalog["state"] = "kernel-audited-source-census"
    save(output / "catalog.json", catalog)
    result.update(audit_complete=True, declaration_count=len(catalog["declarations"]), clause_count=sum(len(r["clauses"]) for r in catalog["declarations"]), kernel_export_count=len(certificate["axioms"]),
                  positive_source_sha256=sha(output / "InventoryAudit.lean"), artifact_sha256=sha(output / "InventoryAudit.olean"),
                  local_registration={"source": str(output / "InventoryAudit.lean"), "module": "InventoryAudit", "shared_roots_changed": False},
                  boundary="Declaration census and four universal finite operator facts only. Not rule soundness, a semantic kill score, or full assignment acceptance.")
    save(output / "result.json", result)
    print(json.dumps({k: v for k, v in result.items() if k not in {"checks", "versions"}}, indent=2), flush=True)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(); parser.add_argument("output", type=Path); args = parser.parse_args()
    repo = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
    with LOCK.open("a+") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        try: run(repo, args.output.resolve())
        except Exception as exc:
            args.output.mkdir(parents=True, exist_ok=True)
            save(args.output / "failure.json", {"audit_complete": False, "scope_complete": False, "score": None, "error": str(exc)})
            raise
