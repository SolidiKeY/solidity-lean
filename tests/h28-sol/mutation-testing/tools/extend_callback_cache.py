#!/usr/bin/env python3
"""Extend the immutable base cache with real callback semantics, serially.

The CLI acquires the writer lock; direct callers must own it. Reused outputs are byte-verified against the
committed original cache receipt; new outputs must pass bounded Lean checks.
Never edits or replaces the original cache or any production checkout source.
"""
import fcntl
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
import bulk_inputs
import bounded
import checked
from prepare_cache import BASE, closure

ROOT = "Solidity.Calculus.CallbackHolds"
ORIGINAL_SHA256 = "edea3b40feb29c9dd7a792a037d0ae1f05dae13fef7381640b315b53836dc1ec"
NEW_MODULES = {"Solidity.Calculus.FirstOrder", "Solidity.Semantics.Callback", ROOT}
LOCK = Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
PREFIX = Path("tests/h28-sol/mutation-testing")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cache_success(module, result, text):
    # The immutable producer has one existing unused-simp-argument warning.
    # Its complete diagnostic identity is pinned; owned witnesses still use
    # checked.success on their unfiltered output and reject every warning.
    parsed = checked.messages(text)
    warnings = [m for m in parsed if m["severity"] == "warning"]
    if module == "Solidity.Semantics.Callback":
        identity = hashlib.sha256(json.dumps(warnings, sort_keys=True).encode()).hexdigest()
        if identity != "3109c129e21b667903ffc2148a88cda158a7bcf784dcafd5a541aef38bf39ed2":
            raise ValueError("pinned producer warning identity changed")
    elif warnings:
        raise ValueError("unexpected producer warning")
    checked.success(result, "\n".join(json.dumps(m) for m in parsed if m["severity"] != "warning"))
    result["pinned_producer_warnings"] = warnings


def extend(repo, original_tree, tree, logs):
    receipt = repo / PREFIX / "evidence/cache-bootstrap/manifest.json"
    try:
        frozen = bulk_inputs.read(repo, receipt)
    except ValueError as exc:
        raise ValueError("original receipt is not the exact committed trust anchor") from exc
    if receipt.is_symlink() or receipt.read_bytes() != frozen or sha(receipt) != ORIGINAL_SHA256:
        raise ValueError("original receipt is not the exact committed trust anchor")
    original = json.loads(frozen)
    modules_old = original["ordered_modules"]
    if len(modules_old) != 68 or len(set(modules_old)) != 68 or set(original["source_sha256"]) != {m.replace(".", "/") + ".lean" for m in modules_old} or set(original["artifact_sha256"]) != {m.replace(".", "/") + ".olean" for m in modules_old}:
        raise ValueError("original cache module/source/artifact inventory mismatch")
    if not original["complete"] or original["base"] != BASE:
        raise ValueError("incomplete or wrong-base dependency cache")
    for artifact, expected in original["artifact_sha256"].items():
        path = original_tree / ".lake/build/lib/lean" / artifact
        if path.is_symlink() or not path.is_file() or path.stat().st_size == 0 or sha(path) != expected:
            raise ValueError("original cache artifact drift")
    tree.mkdir(parents=True, exist_ok=False)
    logs.mkdir(parents=True, exist_ok=False)
    archive = subprocess.check_output(["git", "archive", BASE], cwd=repo)
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        tar.extractall(tree, filter="data")
    roots = original["roots"] + [ROOT]
    modules = closure(tree, roots)
    old = set(original["ordered_modules"])
    if not old <= set(modules) or set(modules) - old != NEW_MODULES:
        raise ValueError("extension lost existing dependencies")
    sources = {m.replace(".", "/") + ".lean": sha(tree / (m.replace(".", "/") + ".lean")) for m in modules}
    for source, expected in sources.items():
        if sha(repo / source) != expected:
            raise ValueError("current production source differs from pinned base")
    for source, expected in original["source_sha256"].items():
        if sources.get(source) != expected:
            raise ValueError("reused source identity drift")
    for artifact in original["artifact_sha256"]:
        dest = tree / ".lake/build/lib/lean" / artifact
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(original_tree / ".lake/build/lib/lean" / artifact, dest)
    manifest = {"base": BASE, "roots": roots, "ordered_modules": modules,
                "source_sha256": sources, "archive_sha256": hashlib.sha256(archive).hexdigest(),
                "dependency_manifest": str(receipt), "dependency_manifest_sha256": sha(receipt),
                "reused_artifact_sha256": original["artifact_sha256"],
                "checks": [], "complete": False}
    def save():
        (logs / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    save()
    for module in modules:
        if module in old:
            continue
        source = module.replace(".", "/") + ".lean"
        artifact = ".lake/build/lib/lean/" + module.replace(".", "/") + ".olean"
        log = logs / (module + ".log")
        result = bounded.lean(tree, source, log, timeout=600, output=artifact)
        result.update(module=module, source_sha256=sources[source], log_sha256=sha(log))
        manifest["checks"].append(result)
        save()
        cache_success(module, result, log.read_text())
        output = tree / artifact
        if output.is_symlink() or not output.is_file() or output.stat().st_size == 0:
            raise ValueError("successful compiler did not produce a regular nonempty output")
        result["artifact_sha256"] = sha(output)
        save()
        print(module, "exit=0", result["seconds"], flush=True)
    for source, expected in sources.items():
        if sha(tree / source) != expected or sha(repo / source) != expected:
            raise ValueError("production source changed during cache extension")
    for artifact, expected in original["artifact_sha256"].items():
        if sha(tree / ".lake/build/lib/lean" / artifact) != expected:
            raise ValueError("reused artifact changed during extension")
    for module in modules:
        output = tree / (".lake/build/lib/lean/" + module.replace(".", "/") + ".olean")
        if output.is_symlink() or not output.is_file() or output.stat().st_size == 0:
            raise ValueError("final cache output is not regular and nonempty")
    manifest["artifact_sha256"] = {m.replace(".", "/") + ".olean": sha(tree / (".lake/build/lib/lean/" + m.replace(".", "/") + ".olean")) for m in modules}
    manifest["complete"] = True
    save()
    return manifest


if __name__ == "__main__":
    repo = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
    with LOCK.open("a+") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        extend(repo, Path("/workspace/h28-runtime/prepared-base-6f3eedf0"),
           Path("/workspace/h28-runtime/prepared-callback-base-6f3eedf0-v2"),
           repo / PREFIX / "evidence/callback-cache-bootstrap-v2")
