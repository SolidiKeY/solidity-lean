#!/usr/bin/env python3
"""Read-only census of tracked G07 inventory and fragments; no pin changes."""
import collections
import hashlib
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
DIRECTORIES = ("scripts/g07-axiom-pins.d/", "scripts/axiom-pins/")
HELPER = ROOT / "scripts/check-axiom-pins.mjs"
INVENTORY = "scripts/g07-axiom-pins.json"

def parse(data):
    duplicates = []
    def pairs(items):
        obj = {}
        for key, value in items:
            if key in obj:
                duplicates.append(key)
            obj[key] = value
        return obj
    obj = json.loads(data.decode("utf-8"), object_pairs_hook=pairs)
    return obj, duplicates

def main():
    files = subprocess.check_output(["git", "ls-files", "-z", "--", *DIRECTORIES], cwd=ROOT).decode().split("\0")
    files = sorted(f for f in files if f)
    untracked = subprocess.check_output(["git", "ls-files", "--others", "--exclude-standard", "-z", "--", *DIRECTORIES], cwd=ROOT).decode().split("\0")
    untracked = sorted(f for f in untracked if f)
    digest = hashlib.sha256()
    merged = {}
    errors = []
    raw_fragments = {}
    for directory in DIRECTORIES:
        path = ROOT / directory.rstrip("/")
        if path.is_symlink() or (path.exists() and not path.is_dir()):
            errors.append(f"non-directory or symbolic fragment root: {directory}")
    for name in files:
        path = ROOT / name
        try:
            if any(p.is_symlink() for p in [path, *path.parents] if p != ROOT and ROOT in p.parents):
                raise OSError("symbolic fragment path")
            data = path.read_bytes()
        except OSError as exc:
            errors.append(f"unreadable fragment {name}: {exc}")
            continue
        raw_fragments[name] = data.decode("utf-8", errors="replace")
        digest.update(name.encode() + b"\0" + hashlib.sha256(data).digest())
        if not name.endswith(".json"):
            errors.append(f"non-json tracked fragment: {name}")
            continue
        try:
            obj, duplicates = parse(data)
        except (ValueError, UnicodeDecodeError) as exc:
            errors.append(f"invalid JSON {name}: {exc}")
            continue
        if not isinstance(obj, dict):
            errors.append(f"not an object: {name}")
            continue
        errors.extend(f"duplicate key in {name}: {k}" for k in duplicates)
        for key, value in obj.items():
            pos = key.find(".lean:")
            if pos <= 0 or not key[pos + 6:]:
                errors.append(f"wrong fragment: {key} in {name}")
            if not isinstance(value, list) or not all(isinstance(x, str) for x in value):
                errors.append(f"invalid axiom list: {key}")
            if key in merged:
                errors.append(f"duplicate across fragments: {key}")
            merged[key] = value
    checked = subprocess.run(["node", str(HELPER), "--fragment-op"],
                             input=json.dumps({"root": str(ROOT), "op": "validate", "files": raw_fragments}).encode(),
                             capture_output=True)
    if checked.returncode: errors.append(checked.stderr.decode().strip())
    else:
        # Retain the independent raw JSON/duplicate checks above; validate placement
        # with the same immutable-seed/hash contract as both generators.
        assert json.loads(checked.stdout)["merged"] == merged
    try:
        inventory_bytes = (ROOT / INVENTORY).read_bytes()
        inventory, duplicates = parse(inventory_bytes)
        if not isinstance(inventory, dict):
            raise ValueError("inventory is not an object")
    except (OSError, ValueError, UnicodeDecodeError) as exc:
        print(json.dumps({"fatal": f"invalid or unreadable inventory: {exc}"}, sort_keys=True))
        return 1
    errors.extend(f"duplicate inventory key: {k}" for k in duplicates)
    only_inventory = sorted(inventory.keys() - merged.keys())
    only_fragments = sorted(merged.keys() - inventory.keys())
    different = sorted(k for k in inventory.keys() & merged.keys() if inventory[k] != merged[k])
    counts = collections.Counter(json.dumps(v, ensure_ascii=True, separators=(",", ":")) for v in merged.values())
    report = {"scope": "tracked fragments versus combined inventory; no Lean source scan", "untracked_fragments": untracked, "tracked_fragments": len(files), "fragment_pins": len(merged), "inventory_pins": len(inventory),
              "inventory_only": len(only_inventory), "fragments_only": len(only_fragments),
              "different_values": len(different), "inventory_only_keys": only_inventory, "fragments_only_keys": only_fragments, "different_value_keys": different, "errors": errors, "axiom_lists": dict(sorted(counts.items())),
              "fragment_manifest_sha256": digest.hexdigest(),
              "inventory_sha256": hashlib.sha256(inventory_bytes).hexdigest()}
    print(json.dumps(report, indent=2, ensure_ascii=True, sort_keys=True))
    return int(bool(errors or untracked or only_inventory or only_fragments or different))

if __name__ == "__main__":
    sys.exit(main())
