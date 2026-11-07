#!/usr/bin/env python3
"""Map raw panicData tokens to lexical source windows without claiming semantics."""
import argparse, hashlib, json, pathlib, re, subprocess, sys

DIRECTORY = pathlib.Path(__file__).resolve().parent
TOKEN = re.compile(r"\bpanicData\b")

def occurrences(file, data):
    digest = hashlib.sha256(data).hexdigest()
    return [{"file": file, "source_sha256": digest, "line": n, "column": m.start() + 1}
            for n, line in enumerate(data.decode("utf-8").splitlines(), 1) for m in TOKEN.finditer(line)]

def link(rows, windows):
    mapping = []
    for row in rows:
        matches = [w for w in windows if w["file"] == row["file"] and w["line"] <= row["line"] <= w["end_line"]]
        if len(matches) > 1:
            raise ValueError("overlapping windows")
        if matches and matches[0]["source_sha256"] != row["source_sha256"]:
            raise ValueError("source digest mismatch")
        w = matches[0] if matches else None
        mapping.append({**row, "window": ({k: w[k] for k in ("line", "end_line", "kind", "name", "ledger", "window_sha256")} if w else None)})
    return mapping

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--declarations", type=pathlib.Path, required=True)
    args = p.parse_args()
    raw = subprocess.check_output([sys.executable, str(DIRECTORY / "source_windows.py"), "--declarations", str(args.declarations)])
    windows = json.loads(raw)["windows"]
    root = pathlib.Path.cwd()
    base = root / "Solidity/Backend/PrimitivePackets"
    if not base.is_dir(): p.error("missing PrimitivePackets root")
    rows = []
    for path in sorted(base.rglob("*.lean")):
        rows.extend(occurrences(path.relative_to(root).as_posix(), path.read_bytes()))
    mapping = link(rows, windows)
    print(json.dumps({"method": "current-tree raw panicData regex matches across PrimitivePackets mapped to base-pinned lexical windows; includes comments, strings and identifier suffix false positives; files outside the window set are not base-verified; windows can contain unrelated or unscanned declarations; not Lean parsing, ownership or semantic case closure", "occurrences": len(mapping), "unmapped": sum(row["window"] is None for row in mapping), "rows": mapping}, ensure_ascii=False, indent=2))

if __name__ == "__main__": main()
