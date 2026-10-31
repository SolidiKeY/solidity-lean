#!/usr/bin/env python3
"""Read-only source/toolchain/cache inventory; never a full-build certificate.
Reuse the existing .lake tree. Do not materialize, rewrite or trust artifacts
from this report: Lake's bounded focused checks validate current inputs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument("--toolchain", required=True, type=Path)
parser.add_argument("--output", required=True, type=Path)
args = parser.parse_args()
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
owned = sorted(".".join(p.with_suffix("").parts) for p in Path("Solidity/Backend/InternalFlow").glob("*.lean"))
closure = set()
fixtures = {str(p): digest(p) for p in sorted(Path("tests/internal-flow").glob("*.lean"))}
pending = list(owned)
for fixture in fixtures:
    pending += re.findall(r"^import\s+(Solidity(?:\.[A-Za-z_0-9]+)*)", Path(fixture).read_text(), re.M)
while pending:
    module = pending.pop()
    if module in closure:
        continue
    source = Path(module.replace(".", "/") + ".lean")
    if not source.is_file():
        raise SystemExit("missing source: " + str(source))
    closure.add(module)
    pending += [name for name in re.findall(r"^import\s+(Solidity(?:\.[A-Za-z_0-9]+)*)", source.read_text(), re.M)
                if name not in closure]
versions = subprocess.check_output([str(args.toolchain / "bin/lean"), "--version"], text=True).strip()
configs = {str(p): digest(p) for p in map(Path, ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]) if p.is_file()}
sources = {m: digest(Path(m.replace(".", "/") + ".lean")) for m in sorted(closure)}
key_inputs = {"actual_lean_version": versions, "compiler_binary_sha256": digest(args.toolchain / "bin/lean"),
              "configuration_sha256": configs, "source_sha256": sources, "fixture_sha256": fixtures,
              "runtime_flags": ["-j1", "--tstack=131072"]}
key = hashlib.sha256(json.dumps(key_inputs, sort_keys=True).encode()).hexdigest()
artifacts = {}
for module in owned:
    stem = Path(".lake/build/lib/lean") / module.replace(".", "/")
    artifacts[module] = {suffix: {"exists": Path(str(stem) + suffix).is_file(),
        "sha256": digest(Path(str(stem) + suffix)) if Path(str(stem) + suffix).is_file() else None}
        for suffix in [".olean", ".trace"]}
result = {"kind": "inventory_only_not_validation", "git_head_at_inventory": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
          "source_toolchain_key": key, "key_inputs": key_inputs, "owned_artifacts": artifacts,
          "cache_strategy": "retain one existing .lake tree; Lake validates hashes; do not copy/relabel old oleans or alter targets/budgets",
          "full_gate": "original exit124/300s remains FAIL/incomplete; no identical full retry justified by this inventory"}
args.output.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"owned_modules": len(owned), "closure_sources": len(closure), "source_toolchain_key": key,
                  "owned_artifacts_ready": all(v[".olean"]["exists"] and v[".trace"]["exists"] for v in artifacts.values())}))
