#!/usr/bin/env python3
"""Reproducible off-Git native solc + EEST + independent EVM provisioning."""
import argparse
import json
import shutil
import subprocess
import urllib.request
from pathlib import Path
from pipeline import SOLC_BIN_COMMIT, SOLC_SHA, EEST_SHA, file_sha, verify_solc

p = argparse.ArgumentParser(__doc__)
p.add_argument("--bulk", type=Path, required=True)
a = p.parse_args()
r = a.bulk.resolve(); repo = Path(__file__).resolve().parents[4]
if r == repo or repo in r.parents: p.error("H44 bulk must stay outside repository")
up = r/"upstream"; up.mkdir(parents=True, exist_ok=True)
def get(url, destination, expected):
    if destination.exists() and file_sha(destination) == expected: return
    temporary = destination.with_suffix(destination.suffix+".download")
    with urllib.request.urlopen(url, timeout=60) as source, temporary.open("wb") as target:
        shutil.copyfileobj(source, target)
    if file_sha(temporary) != expected:
        temporary.unlink()
        raise ValueError("download checksum mismatch: " + url)
    temporary.replace(destination)
base = f"https://raw.githubusercontent.com/ethereum/solc-bin/{SOLC_BIN_COMMIT}/linux-amd64/"
get(base+"list.json", up/"solc-list.json", "b44c1d0e598ed0bcbf4ee49c86c5ae85b63718c1591689b02d12d7a11d45a2ac")
index = json.loads((up/"solc-list.json").read_text())
name = index["releases"]["0.8.38"]
row = next(x for x in index["builds"] if x["path"] == name)
assert row["sha256"].removeprefix("0x") == SOLC_SHA
get(base+name, up/"solc", SOLC_SHA)
(up/"solc").chmod(0o755)
print(json.dumps(verify_solc(up/"solc")))
get("https://github.com/ethereum/execution-spec-tests/releases/download/v5.3.0/fixtures_develop.tar.gz",
    up/"fixtures_develop-v5.3.0.tar.gz", EEST_SHA)
ref = r/"reference"; ref.mkdir(exist_ok=True)
for name in ("package.json", "package-lock.json"):
    shutil.copyfile(repo/"tests/h62/item3/g52-differential"/name, ref/name)
subprocess.run(["npm", "ci", "--ignore-scripts", "--no-audit", "--no-fund", "--prefix", str(ref)], check=True)
