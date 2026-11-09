#!/usr/bin/env python3
"""Guard regression: current shared-request fixtures are mistaken for historical or runtime acceptance."""
import hashlib
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
PREFIX = "tests/directruntime-20261104/shared-translator/"
DOC = "docs/feature-work/directruntime-shared-translator.md"
ROLES = {
    "IntrinsicControls.lean": ("typed builder, callback and refusal controls", []),
    "SelectionControls.lean": ("DirectRuntime request selection and listing controls", ["artifacts/h68-bulk/ReaderFixtures.ast.json", "artifacts/h68-bulk/UnsupportedContract.ast.json"]),
    "PrimitiveReturnControls.lean": ("finite primitive-return model and checker controls", ["artifacts/primitive-return/PrimitiveReturnRuntime.ast.json", "artifacts/primitive-return/ControlTuples.ast.json"]),
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def regular(root, relative):
    root = pathlib.Path(root).resolve()
    path = root / relative
    cursor = root
    for part in pathlib.Path(relative).parts:
        cursor = cursor / part
        if cursor.is_symlink():
            raise ValueError("unsafe fixture path: " + relative)
    if not path.exists() and not path.is_symlink():
        return {"path": relative, "status": "absent", "sha256": None}
    if path.is_symlink() or not path.is_file() or path.resolve() != path:
        raise ValueError("unsafe fixture path: " + relative)
    return {"path": relative, "status": "present-unverified", "sha256": digest(path.read_bytes())}


def observe(root, staged, head):
    root = pathlib.Path(root).resolve()
    staged = pathlib.Path(staged)
    if staged.is_symlink() or not staged.is_absolute() or not staged.is_dir():
        raise ValueError("invalid staged root")
    doc = regular(root, DOC)
    if doc["status"] != "present-unverified":
        raise ValueError("missing current source handoff")
    tracked_doc = subprocess.check_output(["git", "-C", str(root), "show", head + ":" + DOC])
    if digest(tracked_doc) != doc["sha256"]:
        raise ValueError("handoff differs from committed head")
    rows = []
    for name, (role, fixtures) in ROLES.items():
        relative = PREFIX + name
        src = regular(root, relative)
        if src["status"] != "present-unverified":
            raise ValueError("missing source: " + relative)
        tracked = subprocess.check_output(["git", "-C", str(root), "show", head + ":" + relative])
        if digest(tracked) != src["sha256"]:
            raise ValueError("source differs from committed head: " + relative)
        items = []
        for fixture in fixtures:
            path = PREFIX + fixture
            items.append({"checkout": regular(root, path), "staged": regular(staged, path)})
        rows.append({"source": src, "role": role, "fixtures": items,
                     "effects": ("Lean diagnostics; may write artifacts/primitive-return/control-tuple-results.json if reached"
                                 if name == "PrimitiveReturnControls.lean" else "Lean diagnostics; other driver effects unresolved"),
                     "outcome": "unverified; no source adequacy, native closure, proof or timing acceptance"})
    return {"status": "fresh-static-subset-not-execution-acceptance", "head": head,
            "document": doc, "rows": rows,
            "limitations": "presence is sampled, not execution; auxiliary inputs, ignored/generated files, toolchain and non-atomic changes remain unverified; prior history is not reconstructed"}


def main():
    if len(sys.argv) != 2:
        print("usage: fresh_shared_request.py STAGED_ROOT", file=sys.stderr)
        return 2
    try:
        head = subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip()
        result = observe(ROOT, sys.argv[1], head)
        result["tree"] = subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", "HEAD^{tree}"], text=True).strip()
        result["observer_sha256"] = digest(pathlib.Path(__file__).read_bytes())
        result["staged_root"] = str(pathlib.Path(sys.argv[1]).resolve())
        if subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip() != head:
            raise ValueError("HEAD changed during observation")
        print(json.dumps(result, indent=2, sort_keys=True))
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        print("fresh shared request unavailable: " + str(exc), file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
