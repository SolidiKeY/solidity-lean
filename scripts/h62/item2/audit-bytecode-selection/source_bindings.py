#!/usr/bin/env python3
"""Guard against rebinding a passing source prefix to changed sources or products.

This checks saved receipt consistency, not process attestation, a complete source
closure gate, an executed inspection, statement correspondence or witnesses.
It never starts Lean and never retries a stopped proof.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys

import census
import kernel_metadata
import linkage_manifest
import verify

from census import BASE, mapped_paths, mask
from kernel_metadata import parse_json
from verify import import_path

LEAN = "/workspace/.setup/tools/lean-4.24.0-linux/bin/lean"
BOUNDARY = "Saved source/product receipt bindings only; no process attestation, closure-gate or inspection acceptance, statement correspondence or witness."


def file_digest(path, advise=False):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
        if advise:
            os.posix_fadvise(stream.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)
    return digest.hexdigest()


def safe_file(root, relative):
    path = Path(relative)
    if path.is_absolute() or ".." in path.parts:
        raise ValueError("artifact path escapes root")
    target = root / path
    if any(p.is_symlink() for p in (target, *target.parents)):
        raise ValueError("symlink input refused")
    if not target.is_file():
        raise ValueError("missing artifact: " + str(relative))
    return target


def closure(repo, roots):
    """Same import interpretation as the serial verifier; no compilation."""
    seen, active, order, hashes = set(), set(), [], {}
    def visit(path):
        if path in active:
            raise ValueError("dependency cycle")
        if path in seen:
            return
        source = safe_file(repo, path)
        raw = source.read_bytes()
        original = subprocess.check_output(["git", "show", BASE + ":" + path], cwd=repo)
        if raw != original:
            raise ValueError("frozen source differs: " + path)
        active.add(path)
        for imports in re.findall(r"(?m)^import[ \t]+([^\n]+)", mask(raw.decode())):
            for module in imports.split():
                dep = import_path(module)
                if (repo / dep).is_file():
                    visit(dep)
                elif not any(module == root or module.startswith(root + ".") for root in ("Lean", "Init", "Std")):
                    raise ValueError("unresolved import: " + module)
        active.remove(path)
        seen.add(path)
        order.append(path)
        hashes[path] = hashlib.sha256(raw).hexdigest()
    for root in roots:
        visit(root)
    return order, hashes


def bind_records(repo, evidence, roots):
    """Pure receipt binding; terminal RED remains RED regardless of prefix size."""
    names = ("closure-plan.json", "workload-result.json", "container.exit",
             "workload.id", "source-check/verification.json")
    snapshots = {name: safe_file(evidence, name).read_bytes() for name in names}
    order, source_hashes = closure(repo, roots)
    def read(name):
        return parse_json(snapshots[name].decode())
    plan = read("closure-plan.json")
    if (plan["frozen_base"] != BASE or plan["roots"] != roots
            or plan["root_count"] != len(roots) or plan["source_closure_count"] != len(order)
            or plan["order"] != order or plan["source_sha256"] != source_hashes):
        raise ValueError("source plan differs from frozen dependency closure")
    # Require a terminal workload receipt; an active prefix is not stable evidence.
    terminal = read("workload-result.json")
    exit_text = snapshots["container.exit"].decode().strip()
    if exit_text not in ("0", "1") or terminal["status"] not in ("pass", "red"):
        raise ValueError("unsupported terminal state")
    if (exit_text == "0") != (terminal["status"] == "pass"):
        raise ValueError("terminal receipts disagree")
    if (terminal.get("exit") is not None and type(terminal["exit"]) is not int):
        raise ValueError("invalid terminal exit")
    if terminal["status"] == "pass" and terminal.get("exit") != 0:
        raise ValueError("claimed pass with nonzero or missing workload exit")
    if not isinstance(terminal.get("workload_id"), str) or not re.fullmatch(r"[0-9a-f]{64}", terminal["workload_id"]):
        raise ValueError("invalid workload identity")
    if snapshots["workload.id"].decode().strip() != terminal["workload_id"]:
        raise ValueError("workload identity differs")
    rows = read("source-check/verification.json")
    if not isinstance(rows, list) or not rows or len(rows) > len(order):
        raise ValueError("empty or oversized source prefix")
    if terminal["status"] == "pass" and len(rows) != len(order):
        raise ValueError("claimed terminal pass with incomplete source prefix")
    if [row["path"] for row in rows] != order[:len(rows)]:
        raise ValueError("source prefix order differs")
    result = []
    for i, row in enumerate(rows):
        path = row["path"]
        product = safe_file(evidence, "source-check/lean/" + str(Path(path).with_suffix(".olean")))
        log = safe_file(evidence, "source-check/" + str(i).zfill(3) + "-" + Path(path).stem + ".log")
        command = [LEAN, "-j1", "-M8192", "--tstack=131072", "-o", str(product), path]
        seconds = row["seconds"]
        if (row["command"] != command or row["log"] != str(log)
                or type(row["exit"]) is not int or row["exit"] != 0
                or row["stop"] is not None or row["source_unchanged_during_check"] is not True
                or isinstance(seconds, bool) or not isinstance(seconds, (int, float))
                or not math.isfinite(seconds) or not 0 < seconds <= 300
                or row["source_sha256"] != source_hashes[path]):
            raise ValueError("invalid passing source receipt: " + path)
        product_hash = file_digest(product, advise=True)
        if row["output_sha256"] != product_hash:
            raise ValueError("compiled product changed: " + path)
        result.append({"path": path, "source_sha256": source_hashes[path],
                       "output_sha256": product_hash, "log_sha256": file_digest(log),
                       "seconds": seconds})
    for name, before in snapshots.items():
        if safe_file(evidence, name).read_bytes() != before:
            raise ValueError("receipt changed during binding: " + name)
    return {"receipt_sha256": {name: hashlib.sha256(raw).hexdigest() for name, raw in snapshots.items()},
            "log_boundary": "Current-file capture only; no historical log digest was supplied by the verifier.",
            "schema_version": 1, "base": BASE, "boundary": BOUNDARY,
            "terminal_workload_status": terminal["status"], "container_exit": int(exit_text),
            "roots": roots, "source_product_bindings": result,
            "pending_planned_sources": order[len(rows):],
            "summary": {"planned_sources": len(order), "bound_saved_records": len(result),
                        "pending_sources": len(order) - len(rows),
                        "inspection_accepted": False, "witnesses_established": 0}}


def classify_inputs(repo, paths, bindings):
    """Associate frozen lexical candidates only; no kernel identity is inferred."""
    from census import declarations
    import census
    from linkage_manifest import classify_source, inherited_candidates
    if len(set(paths)) != len(paths):
        raise ValueError("duplicate classification source")
    by_path = {r["path"]: r for r in bindings}
    if len(by_path) != len(bindings):
        raise ValueError("duplicate source/product binding")
    files, private, structures, notes = [], [], [], []
    theorem_count = 0
    for path in paths:
        raw = safe_file(repo, path).read_bytes()
        if raw != subprocess.check_output(["git", "show", BASE + ":" + path], cwd=repo):
            raise ValueError("frozen classification source differs: " + path)
        source_hash = hashlib.sha256(raw).hexdigest()
        binding = by_path.get(path)
        if binding is not None and binding["source_sha256"] != source_hash:
            raise ValueError("source/product classification mismatch: " + path)
        association = {"path": path, "source_sha256": source_hash,
                       "saved_product_sha256": binding["output_sha256"] if binding else None,
                       "source_product_status": "saved_receipt_bound" if binding else "not_in_saved_prefix",
                       "kernel_status": "uninspected; no identity or proof type accepted"}
        files.append(association)
        result = classify_source(path, raw.decode(), census)
        theorem_count += len(declarations(raw.decode()))
        for row in result["private_declarations"]:
            private.append(dict(row, **association))
        for row in result["structures"]:
            # The source structure already carries its path.
            structures.append(dict(row, **association))
        notes.extend(dict(row, path=path) for row in result["scope_notes"])
    return {"boundary": "Lexical private/inherited candidates plus saved source-product associations only.",
            "files": files, "private_candidates": private, "structure_candidates": structures,
            "inherited_candidates": inherited_candidates(structures), "scope_notes": notes,
            "summary": {"files": len(files), "mapped_files_with_saved_product": sum(r["saved_product_sha256"] is not None for r in files),
                        "private_candidates": len(private), "structure_candidates": len(structures),
                        "named_theorem_candidates": theorem_count,
                        "direct_field_candidates": sum(len(r["fields"]) for r in structures),
                        "source_parent_edges": sum(len(r["parents"]) for r in structures),
                        "kernel_links_accepted": 0, "instantiated_inherited_obligations_accepted": 0,
                        "witnesses_established": 0}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    repo, evidence = args.repo.resolve(), args.evidence.resolve()
    if any(p.is_symlink() for p in (args.repo, *args.repo.parents, args.evidence, *args.evidence.parents)):
        raise ValueError("symlink input directory refused")
    output = args.output
    if (output.exists() or any(p.is_symlink() for p in (output, *output.parents))
            or any(output.resolve().is_relative_to(r) for r in (repo, Path(__file__).resolve().parents[4], evidence))):
        raise ValueError("output must be fresh, nonsymlink and outside repositories/input evidence")
    paths, _ = mapped_paths(repo)
    roots = [p for p in paths if p.startswith("Solidity/")]
    tool_paths = [Path(__file__).resolve()] + [Path(m.__file__).resolve() for m in
                                               (census, kernel_metadata, linkage_manifest, verify)]
    tool_hashes = {str(p): file_digest(p) for p in tool_paths}
    result = bind_records(repo, evidence, roots)
    result["static_classification"] = classify_inputs(repo, paths, result["source_product_bindings"])
    if any(file_digest(Path(p)) != digest for p, digest in tool_hashes.items()):
        raise ValueError("binding tool/helper changed during execution")
    result["tool_sources_sha256"] = tool_hashes
    result["python_version"] = sys.version
    with output.open("x") as stream:
        stream.write(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result["summary"], sort_keys=True))
    print(BOUNDARY)


if __name__ == "__main__":
    main()
