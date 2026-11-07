#!/usr/bin/env python3
"""Build a serial, source-pinned oracle dependency cache from the exact base.

No existing .olean is reused. Run under the global writer lock. Logs and
manifests remain after any failed build; failure is never a passing baseline.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile
import bounded

BASE = "6f3eedf0788ee1f8a3bcf230558c712ecdca04d5"
ROOTS = ["Solidity.Calculus.Rules", "Solidity.Calculus.PremiseSound", "Solidity.Calculus.CallbackRules"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def closure(tree, roots):
    done, active, ordered = set(), set(), []
    def visit(module):
        source = tree / (module.replace(".", "/") + ".lean")
        if not source.is_file():
            if module == "Solidity" or module.startswith("Solidity."):
                raise ValueError("missing local module: " + module)
            return
        if module in active:
            raise ValueError("import cycle")
        if module in done:
            return
        active.add(module)
        for line in source.read_text().splitlines():
            if line.startswith("import "):
                for dependency in line.split()[1:]:
                    visit(dependency)
        active.remove(module)
        done.add(module)
        ordered.append(module)
    for module in roots:
        visit(module)
    return ordered


def build(repo, tree, logs):
    tree.mkdir(parents=True, exist_ok=False)
    logs.mkdir(parents=True, exist_ok=False)
    archive = subprocess.check_output(["git", "archive", BASE], cwd=repo)
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        tar.extractall(tree, filter="data")
    modules = closure(tree, ROOTS)
    sources = {m.replace(".", "/") + ".lean": sha(tree / (m.replace(".", "/") + ".lean")) for m in modules}
    manifest = {"base": BASE, "roots": ROOTS, "ordered_modules": modules, "source_sha256": sources,
                "archive_sha256": hashlib.sha256(archive).hexdigest(), "checks": [], "complete": False}
    def save():
        (logs / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    save()
    for index, module in enumerate(modules):
        source = module.replace(".", "/") + ".lean"
        artifact = ".lake/build/lib/lean/" + module.replace(".", "/") + ".olean"
        result = bounded.lean(tree, source, logs / (module + ".log"), timeout=600, output=artifact)
        result.update(module=module, source_sha256=sources[source])
        manifest["checks"].append(result)
        save()
        print(f"{index + 1}/{len(modules)} {module}: {result['kind']} {result['exit']} {result['seconds']:.3f}s", flush=True)
        if result["kind"] != "exit" or result["exit"] != 0:
            raise RuntimeError("baseline dependency build failed: " + module)
        if any(sha(tree / path) != expected for path, expected in sources.items()):
            raise RuntimeError("production source changed during build")
        result["artifact_sha256"] = sha(tree / artifact)
        save()
    manifest["complete"] = True
    manifest["artifact_sha256"] = {m.replace(".", "/") + ".olean": sha(tree / (".lake/build/lib/lean/" + m.replace(".", "/") + ".olean")) for m in modules}
    save()
    return manifest


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("tree", type=Path)
    parser.add_argument("logs", type=Path)
    args = parser.parse_args()
    repo = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
    build(repo, args.tree.resolve(), args.logs.resolve())
