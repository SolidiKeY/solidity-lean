#!/usr/bin/env python3
"""Validate feature citations using Lean's elaborated environment, serially.

Run with python3 -I. No source-text name resolution or third-party dependencies.
Imports must already be built for the pinned toolchain. Diagnostics go to stderr;
stdout contains only a sorted deterministic JSON summary on success.
"""
import argparse
from collections import Counter
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
IDENT = re.compile(r"[A-Za-z_][A-Za-z_0-9'?!]*(?:\.[A-Za-z_][A-Za-z_0-9'?!]*)*\Z")


def validate(data):
    if data.get("schemaVersion") != 2:
        raise ValueError("expected schemaVersion 2")
    rows = data.get("features")
    if not isinstance(rows, list):
        raise ValueError("features must be a list")
    seen = set()
    queries = set()
    counts = Counter()
    for row in rows:
        key = row.get("id")
        if not isinstance(key, str) or key in seen:
            raise ValueError("invalid/duplicate row id")
        seen.add(key)
        current = row.get("current")
        if current not in ("present", "partial", "missing", "notApplicable"):
            raise ValueError(f"{key}: invalid current")
        if "modelToSolcGap" in row and (not isinstance(row["modelToSolcGap"], str) or not row["modelToSolcGap"].strip()):
            raise ValueError(f"{key}: modelToSolcGap must be nonempty text")
        citations = row.get("theorems")
        if not isinstance(citations, list):
            raise ValueError(f"{key}: theorems must be a list")
        cells = set()
        local = set()
        for c in citations:
            if not isinstance(c, dict) or set(c) != {"name", "module", "class", "premises", "direction"}:
                raise ValueError(f"{key}: invalid citation fields")
            name, module, cls, direction = (c[k] for k in ("name", "module", "class", "direction"))
            if not isinstance(name, str) or not IDENT.fullmatch(name) or "." not in name:
                raise ValueError(f"{key}: fully qualified name required")
            if not isinstance(module, str) or not IDENT.fullmatch(module):
                raise ValueError(f"{key}: invalid module")
            if cls not in ("a", "b", "c", "d") or direction not in ("model", "model-to-solc"):
                raise ValueError(f"{key}: invalid class/direction")
            premises = c["premises"]
            if not isinstance(premises, list) or any(not isinstance(p, str) or not p.strip() for p in premises):
                raise ValueError(f"{key}: premises must be named strings")
            if len(premises) != len(set(premises)) or (cls == "b") != bool(premises):
                raise ValueError(f"{key}: only class b requires named premises")
            entry = (name, module, cls, tuple(premises), direction)
            if entry in local:
                raise ValueError(f"{key}: duplicate citation")
            local.add(entry)
            queries.add((module, name, cls in ("a", "b")))
            cells.add((cls, direction))
        if current == "present" and (not citations or all(c["class"] == "d" for c in citations)):
            raise ValueError(f"{key}: present row needs a non-d citation")
        for cls, direction in cells or {("uncited", "none")}:
            counts[(current, cls, direction)] += 1
    return sorted(queries), {
        "rows": len(rows),
        "citationEntries": sum(len(r["theorems"]) for r in rows),
        "modelToSolcGapRows": sum(bool(r.get("modelToSolcGap")) for r in rows),
        "rowsWithCitations": sum(bool(r["theorems"]) for r in rows),
        "modelOnlyRows": sum(bool(r["theorems"]) and all(c["direction"] == "model" for c in r["theorems"]) for r in rows),
        "modelToSolcRows": sum(any(c["direction"] == "model-to-solc" for c in r["theorems"]) for r in rows),
        "uncitedRows": sum(not r["theorems"] for r in rows),
        "rowCells": [{"current": a, "class": b, "direction": c, "rows": n} for (a,b,c),n in sorted(counts.items())],
    }


def query_text(module, entries):
    lines = ["import Lean", f"import {module}", "open Lean", "run_elab do", "  let env ← getEnv"]
    for _, name, theorem in entries:
        # Identifiers are restricted above; never interpolate arbitrary Lean code.
        lines += [f'  let n := "{name}".toName',
                  f'  let some info := env.find? n | throwError "missing declaration: {name}"',
                  f'  let some idx := env.getModuleIdxFor? n | throwError "missing module origin: {name}"',
                  f'  unless env.header.moduleNames[idx.toNat]! == "{module}".toName do',
                  f'    throwError "wrong module origin: {name}"']
        if theorem:
            lines += ['  match info with', '  | .thmInfo _ => pure ()', f'  | _ => throwError "class a/b requires a theorem: {name}"']
        else:
            lines += ['  let _ := info']
    lines += ['  logInfo "CITATIONS_RESOLVED"', '']
    return "\n".join(lines)


def resolve(queries, evidence=None):
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    for module in sorted({q[0] for q in queries}):
        entries = [q for q in queries if q[0] == module]
        source = query_text(module, entries)
        with tempfile.TemporaryDirectory(prefix="feature-citations-") as temp:
            path = Path(temp) / "Query.lean"
            path.write_text(source)
            result = subprocess.run(["lake", "env", "lean", "-j1", "-M8192", "--tstack=131072", str(path)],
                                    cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if evidence:
            evidence.mkdir(parents=True, exist_ok=True)
            (evidence / (module + ".query.txt")).write_text(source)
            (evidence / (module + ".log")).write_text(result.stdout)
        if result.returncode or "CITATIONS_RESOLVED" not in result.stdout:
            raise ValueError(f"Lean resolution failed for {module}:\n{result.stdout}")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--manifest", type=Path, default=ROOT / "docs/solidity-features.json")
    p.add_argument("--evidence-dir", type=Path)
    args = p.parse_args()
    try:
        queries, summary = validate(json.loads(args.manifest.read_text()))
        resolve(queries, args.evidence_dir)
    except (ValueError, OSError) as exc:
        print(str(exc), file=sys.stderr)
        return 1
    print(json.dumps(summary, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    sys.exit(main())
