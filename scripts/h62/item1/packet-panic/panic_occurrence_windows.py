#!/usr/bin/env python3
"""Map raw panicData tokens to lexical source windows without claiming semantics."""
import argparse, hashlib, json, pathlib, re, subprocess, sys
from lexical_mask import mask_comments_and_strings

DIRECTORY = pathlib.Path(__file__).resolve().parent
TOKEN = re.compile(r"\bpanicData\b")
LEXICAL_TOKEN = re.compile(r"(?<![\w'])panicData(?![\w'.!?])")
HELPER_COMMIT = "e9b89d553234b52e4ba9b38092ff691138c147c8"
HELPER_PATH = "Solidity/Backend/PrimitivePackets/PanicBytes.lean"
HELPER_NAMES = ("exact_panic_bytes", "panic_not_truncated", "panic_not_empty")

def occurrences(file, data):
    digest = hashlib.sha256(data).hexdigest()
    source = data.decode("utf-8")
    masked = mask_comments_and_strings(source)
    raw_lines = source.splitlines()
    masked_lines = masked.splitlines()
    if len(raw_lines) != len(masked_lines):
        raise ValueError("mask changed line count")
    result = []
    for n, (raw, visible) in enumerate(zip(raw_lines, masked_lines), 1):
        candidates = {m.start() for m in LEXICAL_TOKEN.finditer(visible)}
        for match in TOKEN.finditer(raw):
            result.append({"file": file, "source_sha256": digest, "line": n, "column": match.start() + 1,
                "lexical_candidate": match.start() in candidates})
    return result

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

def canonical_helper_windows(root):
    data = (root / HELPER_PATH).read_bytes()
    pinned = subprocess.check_output(["git", "show", HELPER_COMMIT + ":" + HELPER_PATH], cwd=root)
    if data != pinned:
        raise ValueError("canonical helper differs from registered upstream snapshot")
    digest = hashlib.sha256(data).hexdigest()
    lines = data.decode("utf-8").splitlines(keepends=True)
    headers = [(n, m.group(1)) for n, line in enumerate(lines, 1)
               if (m := re.match(r"^theorem (exact_panic_bytes|panic_not_truncated|panic_not_empty)\s*:", line))]
    if tuple(name for _, name in headers) != HELPER_NAMES:
        raise ValueError("canonical helper headers differ from registered snapshot")
    result = []
    for i, (start, name) in enumerate(headers):
        end = headers[i + 1][0] - 1 if i + 1 < len(headers) else len(lines)
        text = "".join(lines[start - 1:end])
        result.append({"file": HELPER_PATH, "source_sha256": digest, "line": start, "end_line": end,
            "kind": "theorem", "name": name, "ledger": "supplemental-registered-helper@" + HELPER_COMMIT,
            "window_sha256": hashlib.sha256(text.encode("utf-8")).hexdigest()})
    return result

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--declarations", type=pathlib.Path, required=True)
    args = p.parse_args()
    raw = subprocess.check_output([sys.executable, "-B", str(DIRECTORY / "source_windows.py"), "--declarations", str(args.declarations)])
    windows = json.loads(raw)["windows"]
    root = pathlib.Path.cwd()
    supplemental = canonical_helper_windows(root)
    windows.extend(supplemental)
    base = root / "Solidity/Backend/PrimitivePackets"
    if not base.is_dir(): p.error("missing PrimitivePackets root")
    rows = []
    for path in sorted(base.rglob("*.lean")):
        rows.extend(occurrences(path.relative_to(root).as_posix(), path.read_bytes()))
    mapping = link(rows, windows)
    unmapped = sum(row["window"] is None for row in mapping)
    print(json.dumps({"method": "current-tree raw panicData regex matches across PrimitivePackets mapped to base-pinned lexical windows; includes comments, strings and identifier suffix false positives; the registered helper has separate upstream-snapshot windows; other files outside the window set are not base-verified; windows can contain unrelated or unscanned declarations; lexical candidates mask comments, strings and attributes but are not Lean parsing, ownership or semantic case closure", "supplemental_helper_commit": HELPER_COMMIT, "supplemental_helper_windows": len(supplemental), "occurrences": len(mapping), "lexical_candidates": sum(row["lexical_candidate"] for row in mapping), "unmapped": unmapped, "rows": mapping}, ensure_ascii=False, indent=2))
    if not mapping:
        print("no raw panicData matches", file=sys.stderr)
        return 2
    if unmapped:
        print(f"{unmapped} raw panicData matches lack a source window", file=sys.stderr)
        return 3
    return 0

if __name__ == "__main__": raise SystemExit(main())
