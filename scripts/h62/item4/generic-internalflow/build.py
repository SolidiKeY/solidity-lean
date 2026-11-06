#!/usr/bin/env python3
"""Serial per-file migration checks in a fresh 4.35-only artifact directory.
No Lake configuration, generated roots, or original source files are changed.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from census import ROOT, mask

ap = argparse.ArgumentParser()
ap.add_argument("--lean", type=Path, required=True)
ap.add_argument("--output", type=Path, required=True)
ap.add_argument("targets", nargs="+")
a = ap.parse_args()
a.output.mkdir(parents=True, exist_ok=True)
version = subprocess.check_output([str(a.lean), "--version"], text=True).strip()
if "version 4.35.0," not in version:
    raise SystemExit("wrong coordinator toolchain")
manifest_path = a.output / "manifest.json"
manifest = json.loads(manifest_path.read_text()) if manifest_path.exists() else {}
visited = {}
active = set()

def build(module):
    if module in visited:
        return visited[module]
    source = ROOT / (module.replace(".", "/") + ".lean")
    if not source.exists():
        return version  # toolchain modules use the official sysroot
    if module in active:
        raise SystemExit(f"import cycle: {module}")
    active.add(module)
    data = source.read_bytes()
    imports = []
    for line in mask(data.decode()).splitlines():
        m = re.match(r"^\s*(?:public\s+|private\s+)?import\s+(.+)$", line)
        if m:
            imports.extend(m[1].split())
    deps = [build(dep) for dep in imports]
    fingerprint = hashlib.sha256((version + data.hex() + json.dumps(deps)).encode()).hexdigest()
    olean = a.output / (module.replace(".", "/") + ".olean")
    if manifest.get(module) != fingerprint or not olean.exists():
        olean.parent.mkdir(parents=True, exist_ok=True)
        log = a.output / (module + ".log")
        env = dict(os.environ, LEAN_PATH=str(a.output), LEAN_NUM_THREADS="1")
        command = [sys.executable, str(Path(__file__).with_name("bounded.py")), "--seconds", "300", "--", str(a.lean), "-j1", "--tstack=131072", "-o", str(olean), str(source)]
        print("CHECK", module, flush=True)
        with log.open("w") as out:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=out, stderr=subprocess.STDOUT)
        if result.returncode:
            print(log.read_text()[-6000:], flush=True)
            raise SystemExit(f"FAIL {module}; see {log}")
        manifest[module] = fingerprint
        manifest_path.write_text(json.dumps(manifest, sort_keys=True, indent=2) + "\n")
    visited[module] = fingerprint
    active.remove(module)
    return fingerprint

for target in a.targets:
    if not (ROOT / (target.replace(".", "/") + ".lean")).is_file():
        raise SystemExit(f"requested source target missing: {target}")
for target in a.targets:
    build(target)
print("PASS", len(visited), "source modules", version)
