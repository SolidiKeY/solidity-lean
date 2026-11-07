#!/usr/bin/env python3
"""Guard regression: standalone rows lose unresolved execution requirements.

Lexical hints are not parsed Lean, driver attribution or an execution recipe.
"""
import hashlib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
HINT = re.compile(r"\bimport\b|#eval!?\b|#guard_msgs\b|\brun_cmd\b|\bIO\.FS\b|\bextern\b")


def classify(root, manifest):
    root = pathlib.Path(root)
    rows = manifest.get("rows") if isinstance(manifest, dict) else None
    if not isinstance(rows, list) or not rows:
        raise ValueError("nonempty candidate rows required")
    seen, out = set(), []
    for row in rows:
        if not isinstance(row, dict):
            raise ValueError("invalid candidate row")
        path, digest, context = row.get("path"), row.get("sha256"), row.get("context")
        if (not isinstance(path, str) or not path.endswith(".lean") or path.startswith("/")
                or "\\" in path or any(x in ("", ".", "..") for x in path.split("/"))
                or path in seen or context not in ("standalone-root-review", "standalone-bridge-review")
                or not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest)):
            raise ValueError("invalid or duplicate candidate")
        seen.add(path)
        target = root / path
        if target.is_symlink() or not target.is_file() or target.resolve() != target:
            raise ValueError("missing or symlinked source")
        raw = target.read_bytes()
        if hashlib.sha256(raw).hexdigest() != digest:
            raise ValueError("source changed since census")
        lines = raw.decode("utf-8").splitlines()
        hints = [{"line": i, "tokens": sorted(set(m.group(0) for m in HINT.finditer(line)))}
                 for i, line in enumerate(lines, 1) if HINT.search(line)]
        out.append({"path": path, "sha256": digest, "candidate_context": context, "original_candidate": dict(row),
                    "lexical_hints": hints, "driver": "unresolved", "expected_outcome": "unresolved",
                    "auxiliary_inputs": "unresolved", "side_effects": "unresolved"})
    return out


def main():
    if len(sys.argv) != 2:
        print("usage: standalone_hints.py CENSUS.json", file=sys.stderr)
        return 2
    try:
        manifest_bytes = pathlib.Path(sys.argv[1]).read_bytes()
        manifest = json.loads(manifest_bytes)
        if not isinstance(manifest, dict):
            raise ValueError("candidate manifest must be an object")
        print(json.dumps({"source_manifest_sha256": hashlib.sha256(manifest_bytes).hexdigest(),
                          "source_scope_unverified": manifest.get("scope"), "source_head_unverified": manifest.get("head"),
                          "status": "lexical-hints-not-acceptance", "coverage": "unverified-subsets-accepted",
                          "rows": classify(ROOT, manifest)}, indent=2, sort_keys=True))
    except (OSError, ValueError, UnicodeError) as exc:
        print(f"standalone hints unavailable: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
