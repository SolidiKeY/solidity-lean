#!/usr/bin/env python3
"""Reconcile a resumed source tree without transferring proof credit.

Original records remain complete and immutable in the output. Lexical joins
are navigation aids only; even byte-identical files need dependency validation.
Bulk output belongs off Git (H44).
"""
import argparse
import collections
import fcntl
import hashlib
import json
import pathlib
import subprocess
import census

ORIGINAL_BASE = "c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
ORIGINAL_CENSUS_SHA256 = "1a6f4f9352a0004aa3cfcc67e8e3abd313e5c83864dfe436880aeeb0cb2adcde"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def git(*args):
    return subprocess.check_output(["git", *args])


def tree(commit):
    entries = {}
    for line in git("ls-tree", "-r", commit).decode().splitlines():
        mode, kind, oid, path = line.split(None, 3)
        if kind == "blob":
            entries[path] = oid
    return entries


def blob_hashes(oids):
    # communicate drains stdout while submitting requests; no pipe deadlock.
    ordered = sorted(set(oids))
    result = subprocess.run(["git", "cat-file", "--batch"],
        input="".join(oid + "\n" for oid in ordered).encode(),
        stdout=subprocess.PIPE, check=True).stdout
    hashes = {}; offset = 0
    for oid in ordered:
        end = result.index(b"\n", offset)
        name, kind, size = result[offset:end].decode().split()
        if name != oid or kind != "blob":
            raise ValueError("unexpected Git blob response: " + oid)
        offset = end + 1; size = int(size)
        hashes[oid] = digest(result[offset:offset + size])
        offset += size
        if result[offset:offset + 1] != b"\n":
            raise ValueError("invalid Git blob framing")
        offset += 1
    if offset != len(result):
        raise ValueError("unconsumed Git blob response")
    return hashes


def unique_ids(rows, label):
    ids = [row["id"] for row in rows]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate " + label + " declaration ID")


def reconcile(original_path, current_base):
    raw = original_path.read_bytes()
    if digest(raw) != ORIGINAL_CENSUS_SHA256:
        raise ValueError("original census checksum mismatch")
    original = json.loads(raw)
    if original["base"] != ORIGINAL_BASE or not original["frozen_blobs_verified"]:
        raise ValueError("original baseline provenance mismatch")
    base = git("rev-parse", "--verify", current_base + "^{commit}").decode().strip()
    subprocess.run(["git", "merge-base", "--is-ancestor", ORIGINAL_BASE, base], check=True)
    old_tree, new_tree = tree(ORIGINAL_BASE), tree(base)
    original_files = original["files"]
    if len({f["path"] for f in original_files}) != len(original_files):
        raise ValueError("duplicate original source file")
    hashes = blob_hashes(old_tree[f["path"]] for f in original_files)
    for f in original_files:
        if hashes[old_tree[f["path"]]] != f["sha256"]:
            raise ValueError("original frozen blob mismatch: " + f["path"])
    selected, unmatched = census.files()
    if unmatched:
        raise ValueError("unmatched current module-map patterns: " + repr(unmatched))
    paths = sorted(set(selected) | {str(census.MAP)})
    actual = subprocess.check_output(
        ["git", "hash-object", "--stdin-paths"], input="".join(p + "\n" for p in paths).encode())
    for path, oid in zip(paths, actual.decode().splitlines(), strict=True):
        if new_tree.get(path) != oid:
            raise ValueError("current source differs from baseline: " + path)
    file_rows = []
    original_paths = {f["path"] for f in original_files}
    for path in sorted(original_paths | set(selected)):
        was = path in original_paths; now = path in selected
        state = ("added_to_scope" if not was else "removed_from_scope" if not now else
                 "same_blob" if old_tree[path] == new_tree[path] else "changed_blob")
        file_rows.append(dict(path=path, state=state, original_blob=old_tree.get(path),
            current_blob=new_tree.get(path), current_scope_reasons=selected.get(path, [])))
    states = {f["path"]: f["state"] for f in file_rows}
    current = [row for path in sorted(selected) for row in census.declarations(path)]
    old = original["declarations"]
    unique_ids(old, "original"); unique_ids(current, "current")
    by_id = {row["id"]: i for i, row in enumerate(current)}
    by_name = collections.defaultdict(list)
    for i, row in enumerate(current):
        if row["kind"] != "example":
            by_name[(row["file"], row["kind"], row["source_name"], row["visibility"])].append(i)
    old_names = collections.Counter((r["file"], r["kind"], r["source_name"], r["visibility"])
        for r in old if r["kind"] != "example")
    reconciled = []; linked = set()
    for row in old:
        key = (row["file"], row["kind"], row["source_name"], row["visibility"])
        if states[row["file"]] == "same_blob":
            matches = [by_id[row["id"]]] if row["id"] in by_id else []
        elif row["kind"] != "example" and old_names[key] == 1:
            matches = by_name[key]
        else:
            matches = []
        if len(matches) == 1:
            linked.update(matches)
        reconciled.append(dict(original=row, file_state=states[row["file"]],
            lexical_navigation_status="unique" if len(matches) == 1 else "ambiguous" if matches else "unmatched",
            lexical_navigation_matches=matches, current_proof_status="requires_fresh_validation",
            match_is_statement_fidelity_proof=False))
    return dict(original_base=ORIGINAL_BASE, current_base=base,
        original_census_sha256=digest(raw), current_module_map_sha256=digest(census.MAP.read_bytes()),
        files=file_rows, original_declarations=reconciled, current_lexical_declarations=current,
        current_unlinked_declaration_indices=sorted(set(range(len(current))) - linked),
        summary=dict(original_files=len(original_files), current_files=len(selected),
            file_states=dict(collections.Counter(f["state"] for f in file_rows)),
            original_declarations=len(old), current_lexical_declarations=len(current),
            original_kinds=dict(collections.Counter(r["kind"] for r in old)),
            current_lexical_kinds=dict(collections.Counter(r["kind"] for r in current)),
            original_credit=dict(collections.Counter(r["witness_status"] for r in old)),
            current_verified_witnesses=0, current_verified_refutations=0,
            runtime_gate_pass=False),
        limitations=["Original obligations are retained even when removed from current scope.",
            "Lexical navigation links do not prove signature or hypothesis fidelity.",
            "No old typed/proof evidence is promoted to the new baseline.",
            "Current owners are provisional area-derived labels; exact owner reconciliation remains open."])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--original-census", type=pathlib.Path, required=True)
    ap.add_argument("--base", required=True)
    ap.add_argument("--output", type=pathlib.Path, required=True)
    args = ap.parse_args()
    lock_path = pathlib.Path("/tmp/solidity-lean-feature-groups-20261025/writer.lock")
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        result = reconcile(args.original_census, args.base)
        args.output.mkdir(parents=True, exist_ok=True)
        (args.output / "inventory.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
        (args.output / "summary.json").write_text(json.dumps(result["summary"], indent=2, sort_keys=True) + "\n")
        print(json.dumps(result["summary"], sort_keys=True))


if __name__ == "__main__":
    main()
