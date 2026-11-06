#!/usr/bin/env python3
"""Serial, bounded smoke controls; not the historical timing benchmark."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
CASES = [
    ("ContextControls.lean", None), ("ScalarControls.lean", None),
    ("ChainControls.lean", None),
    ("ProveZeroBaseline.lean", "sol_prove: steps must be between 1 and 20000"),
    ("ProveZeroCandidate.lean", "sol_prove: steps must be between 1 and 20000"),
    ("ChainRefusalBaseline.lean", "sol_chain: no rule applies to"),
    ("ChainRefusalCandidate.lean", "sol_chain: no rule applies to"),
]
LIMIT_SECONDS = 180


def check_log(source, log, exit_code, refusal, proof_exists, timed_out=False, source_path=None):
    """Validate observations; kernel checking happens in the real Lean process."""
    errors = []
    names = re.findall(r"(?m)^#h28_audit\s+(\S+)", source)
    try:
        audits = [json.loads(s) for s in re.findall(r"H28_AUDIT (\{[^\n]+\})", log)]
    except json.JSONDecodeError:
        audits = []
        errors.append("malformed audit JSON")
    replays = re.findall(r"H28_REPLAY (\S+)", log)
    printed = {n: sorted(a.strip() for a in axioms.split(",") if a.strip())
               for n, axioms in re.findall(r"'([^'\n]+)' depends on axioms: \[([^]]*)\]", log)}
    printed.update({n: [] for n in re.findall(r"'([^'\n]+)' does not depend on any axioms", log)})
    if timed_out or exit_code != (1 if refusal else 0):
        errors.append("timeout or unexpected exit")
    if not names or len(names) != len(set(names)):
        errors.append("missing/duplicate source audit inventory")
    if sorted(a["name"] for a in audits) != sorted(names) or sorted(replays) != sorted(names):
        errors.append("incomplete theorem audit or kernel replay")
    for audit in audits:
        axioms = sorted(a["name"] for a in audit["axioms"])
        if printed.get(audit["name"]) != axioms:
            errors.append("literal axiom inventory mismatch")
        if not set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}:
            errors.append("nonstandard axiom")
    reference = next((a for a in audits if a["name"].startswith("Solidity.Examples.")),
                     next((a for a in audits if a["name"] == "ambientContextReflexive"), None))
    footprint = lambda a: sorted((x["name"], x["signature"]) for x in a["axioms"])
    if reference is None or any(footprint(a) != footprint(reference) for a in audits):
        errors.append("reference axiom footprint mismatch")
    diagnostics = re.findall(r"(?m)^(.+?\.lean):(\d+):(\d+): error: ([^\n]*)", log)
    if len(diagnostics) != log.count(": error:"):
        errors.append("unclassified error")
    if refusal:
        start = source.find("theorem rejected")
        end = source.find("#h28_codegen_outer", start)
        first = source.count("\n", 0, start) + 1
        last = source.count("\n", 0, end) if end >= 0 else len(source.splitlines())
        if start < 0 or len(diagnostics) != 2 or any(
                not (source_path is not None and Path(file).resolve() == Path(source_path).resolve()
                     and first <= int(line) <= last
                     and (message == refusal if refusal.startswith("sol_prove:") else message.startswith(refusal)))
                for file, line, _, message in diagnostics):
            errors.append("wrong refusal class/location/count")
        if "H28_REFUSAL_SETUP_OK" not in log:
            errors.append("positive refusal setup missing")
    elif diagnostics or not proof_exists:
        errors.append("positive proof/diagnostic failure")
    return {"passed": not errors, "errors": errors, "theorems": names,
            "axioms": {a["name"]: a["axioms"] for a in audits}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True, type=Path)
    parser.add_argument("--lake", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    maximum = Path("/sys/fs/cgroup/memory.max").read_text().strip()
    swap = Path("/sys/fs/cgroup/memory.swap.max").read_text().strip()
    if os.environ.get("LEAN_NUM_THREADS") != "1" or not maximum.isdigit() or not 0 < int(maximum) <= 12 * 1024**3 or swap != "0":
        parser.error("requires LEAN_NUM_THREADS=1, a <=12GiB cgroup and no swap; caller must reserve4GiB OS headroom")
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    state = {"kind": "seven-file smoke controls, not performance acceptance",
             "per_file_limit_seconds": LIMIT_SECONDS, "memory_max": maximum,
             "memory_swap_max": swap, "versions": {}, "cases": []}
    for name, executable in [("lean", args.lean), ("lake", args.lake)]:
        state["versions"][name] = subprocess.check_output([str(executable), "--version"], text=True).strip()
    for file, refusal in CASES:
        source = ROOT / file
        proof = out / (source.stem + ".olean")
        log = out / (source.stem + ".log")
        process_record = out / (source.stem + "-process.json")
        command = [str(args.lean), "-j1", "--tstack=131072", "-o", str(proof), str(source)]
        start = time.monotonic()
        process = subprocess.Popen([sys.executable, str(ROOT / "measure.py"), str(process_record), *command],
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, start_new_session=True)
        timed_out = False
        try:
            text, _ = process.communicate(timeout=LIMIT_SECONDS)
        except subprocess.TimeoutExpired:
            timed_out = True
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            text, _ = process.communicate()
        log.write_text(text)
        result = check_log(source.read_text(), text, process.returncode, refusal, proof.exists(), timed_out, source)
        result.update(file=file, command=command, exit=process.returncode,
                      timed_out=timed_out, wall_seconds=time.monotonic()-start,
                      source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                      log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
                      process=json.loads(process_record.read_text()) if process_record.exists() else None)
        state["cases"].append(result)
        state["passed"] = all(c["passed"] for c in state["cases"])
        (out / "summary.json").write_text(json.dumps(state, indent=2)+"\n")
    print(json.dumps({"passed": state["passed"], "cases": len(state["cases"]), "output": str(out)}))
    return 0 if state["passed"] and len(state["cases"]) == 7 else 1


if __name__ == "__main__":
    raise SystemExit(main())
