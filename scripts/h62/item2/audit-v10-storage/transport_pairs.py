#!/usr/bin/env python3
"""Exact source evidence for RO-DRIFT-H19H60-TRANSPORT, never proof transport.
Reuse the consumer lexical scanner. No Lean, Source edits or acceptance inference.
"""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath
import subprocess

ROOT = Path(__file__).resolve().parents[4]
PINS = "tests/h62/item2/audit-readonly-calls/signature-drift-pins.json"
PIN_SHA = "591e3420a112ae8a3f1414241809ff5a9b30ee70097e19b8d73c71877de738a3"
BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
EXPECTED = {"H19-balance-projection": 11, "H19-balance-domain": 1,
            "H60-typing-parameter": 7, "removed-private-identity": 3}
spec = importlib.util.spec_from_file_location("ro_pair_census",
    ROOT / "scripts/h62/item2/audit-readonly-calls/census.py")
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def context(row):
    return sha(json.dumps({k: row[k] for k in ["variable_context", "visibility"]},
        sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode())


def validate_pins(pins):
    if pins["original_base"] != BASE or Counter(p["kind"] for p in pins["cases"]) != EXPECTED:
        raise ValueError("exact original 19 pairs and three private gaps required")
    keys = [(p["file"], p["source_name"]) for p in pins["cases"]]
    if len(set(keys)) != len(keys):
        raise ValueError("duplicate pair identity")
    for path, _ in keys:
        rel = PurePosixPath(path)
        if rel.is_absolute() or ".." in rel.parts or not path.startswith("Solidity/") or not path.endswith(".lean"):
            raise ValueError("invalid source path")


def join_pair(pin, old, now):
    if old is None or old["signature_sha256"] != pin["original_signature_sha256"] or context(old) != pin["original_context_sha256"]:
        raise ValueError("original signature/context does not match consumer pin")
    matched = (now is None and pin["observed_signature_sha256"] is None) or (
        now is not None and now["signature_sha256"] == pin["observed_signature_sha256"]
        and context(now) == pin["observed_context_sha256"])
    return {"file": pin["file"], "source_name": pin["source_name"], "kind": pin["kind"],
        "original": old, "current": now, "current_matches_recorded_observation": matched,
        "h57_authorization": "not independently verified",
        "transport_proof": {"status": "not supplied", "reference": None},
        "kernel_fidelity": "pending; no Lean executed", "original_obligation_discharged": False}


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def run(output):
    output = output.resolve()
    if output.is_relative_to(ROOT):
        raise ValueError("bulk evidence must be outside checkout")
    raw = (ROOT / PINS).read_bytes()
    if sha(raw) != PIN_SHA:
        raise ValueError("consumer pin bytes changed; review required")
    pins = json.loads(raw)
    validate_pins(pins)
    head = git("rev-parse", "HEAD").decode().strip()
    output.mkdir(parents=True, exist_ok=False)
    sources = output / "sources"
    sources.mkdir()
    indexed = {}; blobs = []
    for revision, label in [(BASE, "original"), (head, "current")]:
        for path in sorted({p["file"] for p in pins["cases"]}):
            source = git("show", revision + ":" + path)
            destination = sources / label / path
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(source)
            rows = census.declarations_text(path, source.decode())
            table = {r["source_name"]: r for r in rows}
            if len(table) != len(rows):
                raise ValueError("duplicate scanned declaration identity")
            indexed[label, path] = table
            blobs.append({"revision": revision, "path": path, "sha256": sha(source),
                "artifact": str(destination.relative_to(output))})
    rows = [join_pair(p, indexed["original", p["file"]].get(p["source_name"]),
        indexed["current", p["file"]].get(p["source_name"])) for p in pins["cases"]]
    observed_available = subprocess.run(["git", "cat-file", "-e", pins["observed_head"] + "^{commit}"],
        cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
    result = {"schema_version": 1, "request": "RO-DRIFT-H19H60-TRANSPORT",
        "original_base": BASE, "current_head": head, "consumer_pins_sha256": PIN_SHA,
        "recorded_observed_head": pins["observed_head"],
        "recorded_observed_head_available": observed_available,
        "scanner_sha256": sha(Path(census.__file__).read_bytes()),
        "generator_sha256": sha(Path(__file__).read_bytes()), "sources": blobs,
        "pairs": [r for r in rows if r["kind"] != "removed-private-identity"],
        "private_identity_gaps": [r for r in rows if r["kind"] == "removed-private-identity"],
        "transport_proofs_supplied": 0, "original_obligations_discharged": 0,
        "boundary": "Exact lexical source/version extracts only, not H57 approval, kernel types, semantic equivalence, reachable ranges, typed-program evidence or transport proofs."}
    (output / "pairs.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"pairs": len(result["pairs"]), "private_gaps": len(result["private_identity_gaps"]),
        "current_matches": sum(r["current_matches_recorded_observation"] for r in rows),
        "proofs_supplied": 0, "observed_commit_available": observed_available}))
    return 0 if all(r["current_matches_recorded_observation"] for r in rows) else 1


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    raise SystemExit(run(parser.parse_args().output))
