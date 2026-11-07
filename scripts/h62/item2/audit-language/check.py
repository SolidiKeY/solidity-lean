#!/usr/bin/env python3
"""Serial isolated Lean checks of unchanged core imports and additive audit files.
No .lake or old-toolchain cache reuse. Exact core source bytes must match the
frozen base or an explicitly supplied authenticated proof-only receipt. Results are off Git; this focused check
does not replace run-lean.sh or certify unbuilt dependencies/Bridge packages.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[4]
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--lean", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--proof-overlays", type=Path, help="Authenticated H70 proof-only receipts, permitted under H82")
    p.add_argument("--gate-repair-manifest", type=Path, help="Exact user-requested proof revision manifest; original guards remain")
    p.add_argument("--memory-cap-gib", type=int, default=12, choices=range(1,13), help="Lower address-space cap for like-for-like checks; never exceeds existing12GiB")
    p.add_argument("files", type=Path, nargs="+")
    args = p.parse_args()
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    lib = args.output / "lib"
    lib.mkdir(exist_ok=False)
    env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(lib),
               XDG_CACHE_HOME=str(args.output / "cache"))
    results = []
    visited = set()
    overlays = {}
    if args.proof_overlays:
        from overlay_review import TRUSTED, reconstruct, fidelity, receipt_patch_path
        rows = json.loads(args.proof_overlays.read_text())
        if len(rows) != len(TRUSTED) or {r.get("label") for r in rows} != set(TRUSTED):
            raise RuntimeError("missing or duplicate authenticated receipts")
        for row in rows:
            trusted = TRUSTED[row["label"]]
            for supplied, key in (("owner", "owner"), ("expected_sha256", "sha256"),
                                  ("reported_ticket_head", "ticket"), ("reported_source_head", "source")):
                if row.get(supplied) != trusted[key]: raise RuntimeError("receipt identity differs")
            patch = receipt_patch_path(row).read_bytes()
            if hashlib.sha256(patch).hexdigest() != trusted["sha256"]:
                raise RuntimeError("receipt checksum differs")
            original = subprocess.check_output(["git", "show", f"{BASE}:{trusted['path']}"], cwd=ROOT)
            postimage, *_ = reconstruct(patch, original, trusted["path"])
            fidelity(trusted["path"], original, postimage)
            overlays[trusted["path"]] = postimage
    if args.gate_repair_manifest:
        from gate_repair import approved_revisions
        overlays.update(approved_revisions(args.gate_repair_manifest))
    for path, expected in overlays.items():
        if (ROOT / path).read_bytes() != expected:
            raise RuntimeError("source differs from authenticated proof postimage")
    reserve = 4 * 1024**3
    def available_memory():
        host = int(next(x.split()[1] for x in open("/proc/meminfo") if x.startswith("MemAvailable:"))) * 1024
        maximum = Path("/sys/fs/cgroup/memory.max").read_text().strip()
        current = int(Path("/sys/fs/cgroup/memory.current").read_text())
        return min(host, int(maximum) - current) if maximum != "max" else host

    def compile_file(path):
        if path in visited: return True
        visited.add(path)
        source = ROOT / path
        text = source.read_text()
        if str(path).startswith("Solidity/"):
            frozen = subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=ROOT)
            expected = overlays.get(str(path), frozen)
            if expected != source.read_bytes(): raise RuntimeError(f"source differs from exact snapshot or authenticated postimage: {path}")
        for line in text.splitlines():
            if line.startswith("import "):
                for name in line[7:].split():
                    if name.startswith("--"): break
                    if name.startswith("Solidity."):
                        dep = Path(name.replace(".", "/") + ".lean")
                        if not compile_file(dep): return False
                    elif not name.startswith(("Lean", "Std", "Init")):
                        raise RuntimeError(f"external import requires owner toolchain/package: {name}")
        available = available_memory()
        swap = int(next(x.split()[1] for x in open("/proc/meminfo") if x.startswith("SwapTotal:")))
        cap = min(args.memory_cap_gib * 1024**3, available - reserve - 256 * 1024**2)
        if cap < 1024**3 or swap:
            raise RuntimeError(f"resource guard: available={available}, swap={swap}")
        artifact = lib / path.with_suffix(".olean")
        artifact.parent.mkdir(parents=True, exist_ok=True)
        log = args.output / (str(path).replace("/", "__") + ".log")
        cmd = [str(args.lean), "-j1", "--tstack=131072", "-o", str(artifact), str(path)]
        start = time.monotonic()
        minimum_available = available
        outcome = "exit"
        def bound(): resource.setrlimit(resource.RLIMIT_AS, (cap, cap))
        with log.open("w") as f:
            process = subprocess.Popen(cmd, cwd=ROOT, env=env, stdout=f, stderr=subprocess.STDOUT,
                                       preexec_fn=bound, start_new_session=True)
            while process.poll() is None:
                free = available_memory()
                minimum_available = min(free, minimum_available)
                if free < reserve or time.monotonic() - start > 300:
                    outcome = "reserve-stop" if free < reserve else "timeout"
                    os.killpg(process.pid, signal.SIGKILL)
                    break
                time.sleep(0.1)
            code = process.wait()
        record = {"file": str(path), "source_snapshot": BASE, "proof_overlay_paths": sorted(overlays), "gate_repair_manifest": str(args.gate_repair_manifest) if args.gate_repair_manifest else None, "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                  "command": cmd, "exit": code, "outcome": outcome, "wall_seconds": time.monotonic()-start,
                  "log": str(log), "virtual_memory_cap": cap, "reserve": reserve,
                  "minimum_available": minimum_available,
                  "available_before": available, "swap_total": swap}
        results.append(record)
        (args.output / "checks.json").write_text(json.dumps(results, indent=2) + "\n")
        print(json.dumps(record), flush=True)
        return code == 0 and outcome == "exit"
    for path in args.files:
        if not compile_file(path): return 1
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
