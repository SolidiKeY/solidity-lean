#!/usr/bin/env python3
"""Prepare input lists or quarantine removed modules' build artifacts.
Use only in a disposable pilot checkout, under the repository writer lock.
Arguments: lists|quarantine EXTERNAL_OUTPUT_DIRECTORY
This never deletes source or modifies a Git ref.
"""
import json, pathlib, shutil, subprocess, sys
here = pathlib.Path(__file__).resolve().parent
root = pathlib.Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
mode, output = sys.argv[1:]
out = pathlib.Path(output).resolve(); out.mkdir(parents=True, exist_ok=True)
assert not out.is_relative_to(root)
modules = json.loads((here / "family.json").read_text())
assert modules and all(m.startswith("Solidity.Backend.InternalFlow.") for m in modules)
if mode == "lists":
    (out / "modules.txt").write_text("\n".join(modules) + "\n")
    (out / "paths.txt").write_text("\n".join(m.replace(".", "/") + ".lean" for m in modules) + "\n")
    (out / "imports-after.txt").write_text("Solidity\n")
    print("PILOT_INPUT_LISTS_PASS", len(modules))
elif mode == "quarantine":
    build = root / ".lake/build"; moved = []
    assert not (root / ".lake").is_symlink() and not build.is_symlink(), "private real build required"
    assert build.resolve().is_relative_to(root), "shared build quarantine refused"
    for module in modules:
        for prefix in ("lib/lean", "ir"):
            stem = build / prefix / module.replace(".", "/")
            for source in stem.parent.glob(stem.name + ".*"):
                assert source.resolve().is_relative_to(build.resolve()) and not source.is_symlink(), "shared artifact refused"
                target = out / source.relative_to(build)
                assert not target.exists(), "quarantine must be fresh"
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.move(source, target); moved.append(str(source.relative_to(build)))
    (out / "files.json").write_text(json.dumps(moved, indent=2) + "\n")
    print("REMOVED_ARTIFACTS_QUARANTINED", len(moved))
else:
    raise SystemExit("usage: artifacts.py lists|quarantine EXTERNAL_OUTPUT_DIRECTORY")
