#!/usr/bin/env python3
"""Conservative source census; lexical evidence is NOT a Lean witness certificate.

Every named theorem/lemma in the frozen module-map surface is retained, even
controls with no explicit assumptions. The exact header and in-scope variable
commands are preserved. Kernel elaboration and hypothesis feasibility remain
separate gates; none is inferred from an inhabited premise structure.
"""
import argparse
import glob
import hashlib
import json
import re
import subprocess
from pathlib import Path

BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
MAP = "docs/module-map/readonly-calls.md"
ROOT = Path(__file__).resolve().parents[4]


def sha(s):
    return hashlib.sha256(s.encode()).hexdigest()


def mask(text):
    # Preserve offsets/newlines while removing nested comments and strings.
    out = list(text)
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i+2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i:i+2] = "  "
                depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif string:
            if text[i] == "\\":
                out[i] = " "
                i += 1
                if i < len(text):
                    out[i] = " "
                    i += 1
            elif text[i] == '"':
                out[i] = " "
                string = False
                i += 1
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            out[i:i+2] = "  "
            depth = 1
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = len(text) if j == -1 else j
            out[i:j] = " " * (j-i)
            i = j
        elif text[i] == '"':
            out[i] = " "
            string = True
            i += 1
        else:
            i += 1
    if depth or string:
        raise ValueError("unterminated comment/string")
    return "".join(out)


def modules():
    text = (ROOT / MAP).read_text()
    paths = set()
    last_parent = None
    for spec in re.findall(r"`([^`]+\.lean)`", text):
        if "/" not in spec:
            if last_parent is None:
                raise ValueError(spec)
            spec = str(last_parent / spec)
        else:
            spec = "Solidity/" + spec
        found = sorted(glob.glob(str(ROOT / spec)))
        if not found:
            raise ValueError("unresolved module-map entry: " + spec)
        for name in found:
            paths.add(str(Path(name).relative_to(ROOT)))
        last_parent = Path(spec).parent
    return sorted(paths)


def owner(path):
    # Source tags are the frozen G22/G42 module-map + assignment owner keys.
    if "/WorldCalls/" in path:
        return "V13 (v12-v17/v13-abi-world)"
    if "/V08/" in path:
        return "V08 (v07-v11/v08-world-lowering)"
    return "RO (compiler10/readonly-external)"


def declarations(path):
    return declarations_text(path, (ROOT / path).read_text())


def declarations_text(path, source):
    """Apply the same scoped lexical census to explicitly supplied source bytes."""
    clean = mask(source)
    scopes = []
    variables = []
    rows = []
    # Namespace/section commands are anchored to avoid tactic-local names.
    commands = re.compile(r"(?m)^[ \t]*(?:(namespace|section|end)\b([^\n]*)|((?:(?:private|protected|noncomputable)\s+)*)(theorem|lemma)\s+([^\s({:]+)|variable\b)")
    for m in commands.finditer(clean):
        if m.group(1):
            cmd, value = m.group(1), m.group(2).strip()
            if cmd == "end":
                if not scopes:
                    raise ValueError(f"unmatched end: {path}:{m.start()}")
                _, _, nvars = scopes.pop()
                variables = variables[:nvars]
            else:
                scopes.append((cmd, value, len(variables)))
        elif m.group(4):
            start = m.start()
            i = m.end()
            depth = 0
            while i < len(clean):
                c = clean[i]
                if c in "({[⦃":
                    depth += 1
                elif c in ")}]⦄":
                    depth -= 1
                if depth == 0 and clean.startswith(":=", i):
                    break
                i += 1
            else:
                raise ValueError("no theorem body separator: " + path)
            name = m.group(5)
            ns = ".".join(value for cmd, value, _ in scopes if cmd == "namespace")
            fq = name.removeprefix("_root_.") if name.startswith("_root_.") else ".".join(filter(None, [ns, name]))
            signature = source[start:i].strip()
            rows.append(dict(source_name=fq, kernel_name=None if "private" in m.group(3) else fq, file=path, line=source.count("\n", 0, start)+1,
                signature=signature, signature_sha256=sha(signature),
                variable_context=list(variables), owner=owner(path),
                dependency_owners=(["V12 (v12-v17/v12-flow-calls); frozen P1 owner, no audit edits"]
                    if path.endswith("/P1Consumers.lean") or path.endswith("/Callbacks.lean") else []),
                owner_source="frozen readonly-calls module-map G22/G42 and assignment owner keys",
                visibility=m.group(3).strip() or "public",
                scope="conservative-all-named-theorems", witness_status="pending",
                premise_assessment="unclassified; structure inhabitance does not establish per-input feasibility"))
        else:
            # Read a multiline variable command through balanced binders.
            i = m.end()
            depth = 0
            while i < len(clean):
                c = clean[i]
                if c in "({[⦃":
                    depth += 1
                elif c in ")}]⦄":
                    depth -= 1
                if c == "\n" and depth == 0:
                    break
                i += 1
            variables.append(source[m.start():i].strip())
    if scopes:
        raise ValueError("unclosed scope: " + path)
    return rows


def census():
    paths = modules()
    # Byte-for-byte comparison before stamping the frozen revision. This also
    # rejects imported-interface changes anywhere in the existing core tree.
    for path in [MAP, *paths]:
        frozen = subprocess.check_output(["git", "show", f"{BASE}:{path}"], cwd=ROOT)
        if (ROOT/path).read_bytes() != frozen:
            raise ValueError("FROZEN_DRIFT: " + path)
    subprocess.run(["git", "diff", "--exit-code", BASE, "--", "Solidity", "lakefile.toml", "lean-toolchain"],
        cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
    rows = [r for path in paths for r in declarations(path)]
    keys = [(r["file"], r["source_name"]) for r in rows]
    if len(keys) != len(set(keys)):
        raise ValueError("duplicate declaration identity")
    # Compare a simpler, independent lexical count; fail rather than drop cases.
    for path in paths:
        expected = len(re.findall(r"\b(?:theorem|lemma)\s+", mask((ROOT/path).read_text())))
        actual = sum(r["file"] == path for r in rows)
        if expected != actual:
            raise ValueError(f"declaration count mismatch {path}: {actual} != {expected}")
    return dict(schema=1, base=BASE, module_map=MAP,
        map_sha256=sha((ROOT/MAP).read_text()),
        modules=[dict(file=p, sha256=sha((ROOT/p).read_text()), owner=owner(p)) for p in paths],
        theorem_count=len(rows), declarations=rows,
        boundary="Frozen source headers and lexical variable context only; open/notation resolution, elaborated binders, private kernel names and witnesses require Lean export")


def attach_elaboration(result, exported):
    # Reparse the complete log under its successful, hash-bound Lean receipt.
    # A copied provenance dictionary or raw Expr hash does not bind binder data.
    import importlib.util
    spec = importlib.util.spec_from_file_location("signature_export_verifier", Path(__file__).with_name("export_signatures.py"))
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    verifier.verify_artifact(exported, result)
    rows = result["declarations"]
    items = exported["declarations"]
    by_name = {r["source_name"]: r for r in items}
    if len(by_name) != len(items) or set(by_name) != {r["source_name"] for r in rows}:
        raise ValueError("elaborated census identity mismatch")
    if exported["base"] != BASE:
        raise ValueError("elaborated census base mismatch")
    for row in rows:
        item = by_name[row["source_name"]]
        module = row["file"][:-5].replace("/", ".")
        expected = ("_private."+module+".0." if "private" in row["visibility"] else "")+row["source_name"]
        if item["kernel_name"] != expected or item["module"] != module or item["signature_sha256"] != row["signature_sha256"]:
            raise ValueError("elaborated statement binding mismatch: " + row["source_name"])
        if sha(item["raw_type_expr"]) != item["raw_type_sha256"]:
            raise ValueError("elaborated type hash mismatch")
        row["kernel_name"] = item["kernel_name"]
        row["elaborated"] = {k: item[k] for k in ["raw_type_sha256", "level_parameters", "forall_binders"]}
        row["premise_assessment"] = "Elaborated binder shape exported; no structure-inhabitance or per-input feasibility inferred"
        if not item["forall_binders"]:
            row["premise_assessment"] = "Syntactically binder-free under nonreducing telescope; definitions may hide premises. Semantic/H69 refutation accounting remains pending."
        row["binder_inspection"] = "nonreducing; never discharges an audit obligation"
    result["elaboration_boundary"] = "Exact imported theorem identities/types with successful hash-bound Lean receipt; binder shape is not a joint witness"
    result["elaboration_provenance"] = exported["provenance"]
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", type=Path)
    parser.add_argument("--coverage", type=Path)
    parser.add_argument("--elaborated", type=Path)
    parser.add_argument("--semantic", type=Path)
    parser.add_argument("--semantic-policy", type=Path)
    args = parser.parse_args()
    result = census()
    if args.elaborated:
        result = attach_elaboration(result, json.loads(args.elaborated.read_text()))
    if args.coverage:
        entries = json.loads(args.coverage.read_text())["entries"]
        by_name = {r["source_name"]: r for r in result["declarations"]}
        seen = set()
        for entry in entries:
            name = entry["source_name"]
            if name in seen or name not in by_name:
                raise ValueError("duplicate/unknown coverage identity: " + name)
            seen.add(name)
            row = by_name[name]
            if row["signature_sha256"] != entry["signature_sha256"]:
                raise ValueError("coverage signature drift: " + name)
            row["witness_status"] = entry["status"]
            row["coverage"] = entry
        result["coverage_boundary"] = "Manual binding to saved successful Lean evidence; Python does not certify proofs"
    if args.semantic:
        if not args.elaborated or not args.semantic_policy:
            raise ValueError("semantic classification requires exact export and reviewed policy")
        import importlib.util
        spec = importlib.util.spec_from_file_location("semantic_export_verifier", Path(__file__).with_name("semantic_census.py"))
        semantic = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(semantic)
        semantic.attach(result, json.loads(args.semantic.read_text()), json.loads(args.elaborated.read_text()), json.loads(args.semantic_policy.read_text()))
    payload = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    if args.check:
        if args.check.read_text() != payload:
            raise SystemExit("CENSUS_DRIFT: source or inventory differs")
    if args.output:
        args.output.write_text(payload)
    from collections import Counter
    states = dict(sorted(Counter(r["witness_status"] for r in result["declarations"]).items()))
    print(f"CENSUS_PASS modules={len(result['modules'])} named_theorems={result['theorem_count']} statuses={json.dumps(states, sort_keys=True)}")


if __name__ == "__main__":
    main()
