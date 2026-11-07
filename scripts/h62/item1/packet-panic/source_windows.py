#!/usr/bin/env python3
"""Bind each manual observation to a byte-pinned lexical source window."""
import argparse, collections, hashlib, json, pathlib, subprocess, sys
import ledger_totals

DIRECTORY = pathlib.Path(__file__).resolve().parent

def windows(ledgers, source_bytes):
    grouped = collections.defaultdict(list)
    for ledger, rows in ledgers:
        for row in rows:
            grouped[row["file"]].append((ledger, row))
    result = []
    for file in sorted(grouped):
        data = source_bytes[file]
        digest = hashlib.sha256(data).hexdigest()
        lines = data.decode("utf-8").splitlines(keepends=True)
        entries = sorted(grouped[file], key=lambda pair: pair[1]["line"])
        starts = [row["line"] for _, row in entries]
        if len(set(starts)) != len(starts) or any(n < 1 or n > len(lines) for n in starts):
            raise ValueError(file + ": duplicate or out-of-range window start")
        for index, (ledger, row) in enumerate(entries):
            if row["sha256"] != digest:
                raise ValueError(file + ": source digest mismatch")
            start = row["line"]
            end = starts[index + 1] - 1 if index + 1 < len(starts) else len(lines)
            text = "".join(lines[start - 1:end])
            result.append({"ledger": ledger, "file": file, "source_sha256": digest, "line": start,
                "end_line": end, "kind": row["kind"], "name": row["name"],
                "observation": row["observation"], "window_sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(), "window": text})
    return result

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--declarations", type=pathlib.Path, required=True)
    args = p.parse_args()
    census = json.loads(args.declarations.read_text())["declarations"]
    fresh = json.loads(subprocess.check_output([sys.executable, str(DIRECTORY / "declarations.py")]))["declarations"]
    ledger_totals.validate_census(census, fresh)
    ledgers = []
    for name in ledger_totals.LEDGERS:
        raw = subprocess.check_output([sys.executable, str(DIRECTORY / name), "--declarations", str(args.declarations)])
        ledgers.append((name, json.loads(raw)["declarations"]))
    totals = ledger_totals.summarize(census, ledgers)
    sources = {row["file"]: (pathlib.Path.cwd() / row["file"]).read_bytes() for _, rows in ledgers for row in rows}
    rows = windows(ledgers, sources)
    print(json.dumps({"method": "manual observations beside source text from the literal header to just before the next scanned header, or EOF; windows omit preceding docstrings or attributes and may include comments, namespaces, guards and neighboring unscanned declarations; not Lean parsing or semantic proof", "reconciliation": {k: totals[k] for k in ("original_census", "private_rows", "observed_headers", "described_total", "unclassified_original")}, "windows": rows}, ensure_ascii=False, indent=2))

if __name__ == "__main__": main()
