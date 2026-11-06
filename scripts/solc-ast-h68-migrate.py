#!/usr/bin/env python3
"""H68 fixture migration for the existing `solc_import` route (CR).

H68 (human, 2026-11-06): the AST producer retains compiler
`typeDescriptions.typeIdentifier` and `FunctionCall.tryCall` for modern
fixtures; compatibility fixtures migrate.  This tool re-runs
`scripts/solc-ast.mjs` for every modern fixture under `tests/solc` with the
fixture's own recorded compiler (by sha256) and solkey commit, and classifies:

  current    the committed bytes already equal the regenerated ones
  exact      the regenerated AST equals the committed one after removing only
             the H68 fields (non-UDVT typeIdentifier, tryCall); header equal
  drift      other differences too (listed by key); not migrated by --apply
  no-source  the recorded source path is absent from this checkout
  failed     the producer refused (message kept)

Default is a dry run into --work; the committed tree is not touched.  --apply
rewrites only `exact` fixtures in place and every `hash 0x...` literal that
pins the old bytes in a tracked .lean file naming that fixture.  Sha256
manifests owned by other lanes are reported, never rewritten.

Usage:
  scripts/solc-ast-h68-migrate.py --compiler DIR --solkey-root DIR --work DIR
      [--receipt FILE] [--apply]
DIR for --compiler holds soljson files; each is matched by sha256.
--solkey-root holds one checkout per recorded commit, named solkey-<commit>,
and `no-solkey` (a directory with keyext.solidity.core/build.gradle only) for
fixtures whose recorded commit is `unknown`.
"""
import argparse, collections, glob, hashlib, json, os, re, subprocess, sys

H68_KEYS = ("tryCall",)


def strip_h68(n):
    if isinstance(n, dict):
        out = {}
        for k, v in n.items():
            if k in H68_KEYS:
                continue
            if k == "typeDescriptions" and isinstance(v, dict):
                v = {a: b for a, b in v.items()
                     if not (a == "typeIdentifier" and not str(b).startswith("t_userDefinedValueType"))}
            out[k] = strip_h68(v)
        return out
    if isinstance(n, list):
        return [strip_h68(x) for x in n]
    return n


def diff_keys(a, b, acc):
    if isinstance(a, dict) and isinstance(b, dict):
        for k in set(a) | set(b):
            if k not in a or k not in b:
                acc[k] += 1
            else:
                diff_keys(a[k], b[k], acc)
    elif isinstance(a, list) and isinstance(b, list) and len(a) == len(b):
        for x, y in zip(a, b):
            diff_keys(x, y, acc)
    elif a != b:
        acc["<value>"] += 1
    return acc


def fnv1a64(data):
    h = 0xcbf29ce484222325
    for byte in data:
        h = ((h ^ byte) * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
    return h


def sha256(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--compiler", required=True)
    ap.add_argument("--solkey-root", required=True)
    ap.add_argument("--work", required=True)
    ap.add_argument("--receipt")
    ap.add_argument("--apply", action="store_true")
    a = ap.parse_args()
    compilers = {sha256(p): p for p in glob.glob(os.path.join(a.compiler, "*.js"))}
    os.makedirs(a.work, exist_ok=True)
    rows = []
    for f in sorted(glob.glob("tests/solc/*.ast.json")):
        j = json.load(open(f))
        h = j.get("header", {})
        if "provenanceVersion" not in h:
            continue  # explicit legacy fixtures keep their historical serialization
        row = {"fixture": f, "source": h.get("source"), "compilerSha256": h.get("compilerSha256"),
               "solkeyCommit": h.get("solkeyCommit"), "oldSha256": sha256(f)}
        rows.append(row)
        if not os.path.exists(h.get("source", "")):
            row["status"] = "no-source"
            continue
        comp = compilers.get(h.get("compilerSha256"))
        if comp is None:
            row["status"] = "failed"; row["message"] = "recorded compiler not supplied"
            continue
        sk = h.get("solkeyCommit")
        solkey = os.path.join(a.solkey_root, "no-solkey" if sk == "unknown" else "solkey-" + sk)
        out = os.path.join(a.work, os.path.basename(f))
        settings = h.get("settings", {})
        args = ["node", "scripts/solc-ast.mjs", "--compiler-file", comp,
                "--compiler-sha256", h["compilerSha256"], "--solkey", solkey,
                "--source", h["source"], "--no-wrapper", "--out", out]
        if settings.get("viaIR"):
            args.append("--via-ir")
        if settings.get("evmVersion", "osaka") != "osaka":
            args += ["--evm-version", settings["evmVersion"]]
        if '"abstract"' in json.dumps(j["ast"]):
            args.append("--world-metadata")
        r = subprocess.run(args, capture_output=True, text=True)
        if r.returncode:
            row["status"] = "failed"; row["message"] = r.stderr.strip()[-400:]
            continue
        n = json.load(open(out))
        same_header = n.get("header") == h
        extra = diff_keys(j["ast"], strip_h68(n["ast"]), collections.Counter())
        row["newSha256"] = sha256(out)
        row["typeIdentifiers"] = json.dumps(n["ast"]).count('"typeIdentifier"')
        row["tryCallFlags"] = json.dumps(n["ast"]).count('"tryCall"')
        if row["newSha256"] == row["oldSha256"]:
            row["status"] = "current"
        elif same_header and not extra:
            row["status"] = "exact"
        else:
            row["status"] = "drift"
            row["driftKeys"] = dict(extra) | ({} if same_header else {"<header>": 1})
    tracked = subprocess.check_output(["git", "ls-files"], text=True).split()
    for row in rows:
        base = os.path.basename(row["fixture"])
        mentions = [p for p in tracked if not p.endswith(".ast.json") and
                    base in open(p, errors="replace").read()] if os.path.exists(row["fixture"]) else []
        row["leanPins"] = [p for p in mentions if p.endswith(".lean")]
        row["otherReferences"] = [p for p in mentions if not p.endswith(".lean")]
    if a.apply:
        for row in rows:
            if row["status"] != "exact":
                continue
            old = fnv1a64(open(row["fixture"], "rb").read())
            new_path = os.path.join(a.work, os.path.basename(row["fixture"]))
            new = fnv1a64(open(new_path, "rb").read())
            os.replace(new_path, row["fixture"])
            for p in row["leanPins"]:
                text = open(p).read()
                pat = re.compile(r"0x0*%x\b" % old)
                text2 = pat.sub("0x%016x" % new, text)
                if text2 != text:
                    open(p, "w").write(text2)
            row["applied"] = True
    counts = collections.Counter(r["status"] for r in rows)
    result = {"authority": "H68 option 1", "producer": "scripts/solc-ast.mjs",
              "applied": a.apply, "counts": dict(counts), "fixtures": rows}
    text = json.dumps(result, indent=1, sort_keys=True) + "\n"
    if a.receipt:
        open(a.receipt, "w").write(text)
    print(json.dumps(dict(counts)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
