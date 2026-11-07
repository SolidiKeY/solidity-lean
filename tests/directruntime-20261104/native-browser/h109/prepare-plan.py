"""Guard H109 target/source drift before any authenticated serial runner starts.

Preparation only: this inventories committed sources and emits no executable
commands or measurement verdict. It never runs Lean, Lake, Docker or CI.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import tomllib


SLOW = tuple("Solidity.Examples." + suffix for suffix in (
    "DecisionAPF", "DecisionBlocks", "DecisionGapCore", "DecisionGapHashes",
    "DecisionGapKInt", "DecisionGaps", "DecisionLedger", "DecisionOperators",
    "DecisionRefutations", "DecisionResidue", "DecisionStorageArrays",
    "DecisionThreeKindCoverage", "Tactics.OpenLoops", "Tactics.OpenLoops.RowsNine",
    "Tactics.RevertData"))


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args])


def regular_bytes(root, name, size):
    parts = name.split("/")
    if any(p in ("", ".", "..") for p in parts) or name.startswith("/"):
        raise ValueError("Unsafe source path")
    directory = os.open(root, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    descriptor = None
    try:
        for part in parts[:-1]:
            child = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=directory)
            os.close(directory)
            directory = child
        descriptor = os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                             dir_fd=directory)
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode) or before.st_size != size:
            raise ValueError(f"Non-regular or changed source: {name}")
        chunks, remaining = [], size + 1
        while remaining:
            chunk = os.read(descriptor, min(remaining, 1024 * 1024))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        after = os.fstat(descriptor)
        if (before.st_size, before.st_mtime_ns, before.st_ctime_ns) != (
                after.st_size, after.st_mtime_ns, after.st_ctime_ns):
            raise ValueError(f"Source changed while reading: {name}")
        return b"".join(chunks), stat.S_IMODE(before.st_mode)
    finally:
        if descriptor is not None:
            os.close(descriptor)
        os.close(directory)


def prepare(root, head, context="lane-end"):
    if context not in ("ci", "lane-end"):
        raise ValueError("Unsupported execution context")
    root = Path(root).resolve()
    if not re.fullmatch(r"[0-9a-f]{40}", head):
        raise ValueError("Expected full authenticated commit")
    if git(root, "rev-parse", "--show-toplevel").decode().strip() != str(root):
        raise ValueError("Expected repository root")
    if git(root, "rev-parse", "HEAD").decode().strip() != head:
        raise ValueError("Unexpected source head")
    if git(root, "diff", "HEAD", "--name-only"):
        raise ValueError("Tracked source changes")
    if git(root, "rev-parse", "--show-object-format").strip() != b"sha1":
        raise ValueError("Unsupported Git object format")
    inventory, captured = [], {}
    for row in git(root, "ls-tree", "-rlz", "--full-tree", head).split(b"\0"):
        if not row:
            continue
        meta, raw_name = row.split(b"\t", 1)
        mode, kind, blob, size = meta.decode().split()
        name = raw_name.decode()
        if kind != "blob" or mode not in ("100644", "100755"):
            raise ValueError(f"Unsupported source entry: {name}")
        data, observed_mode = regular_bytes(root, name, int(size))
        actual = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if actual != blob:
            raise ValueError(f"Source blob mismatch: {name}")
        inventory.append({"path": name, "mode": mode, "blob": blob,
                          "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest(),
                          "observedFileMode": observed_mode})
        if name in ("lakefile.toml", "SoliditySlowExamples.lean"):
            captured[name] = data.decode()
    config = tomllib.loads(captured["lakefile.toml"])
    libraries = [x for x in config["lean_lib"] if x["name"] == "SoliditySlowExamples"]
    if len(libraries) != 1 or "SoliditySlowExamples" in config["defaultTargets"]:
        raise ValueError("Slow library must remain non-default")
    if any(k in libraries[0] for k in ("roots", "srcDir", "globs", "needs", "extraDepTargets")):
        raise ValueError("Unsupported slow library mapping")
    imports = []
    for line in captured["SoliditySlowExamples.lean"].splitlines():
        if line.startswith("import "):
            imports.extend(line[7:].split())
        elif line.strip() and not line.startswith("--"):
            raise ValueError("Unexpected slow root syntax")
    sources = {e["path"] for e in inventory}
    rows_nine = "Solidity.Examples.Tactics.OpenLoops.RowsNine"
    if rows_nine.replace(".", "/") + ".lean" in sources and rows_nine not in SLOW:
        raise ValueError("RowsNine requires reviewed central slow-root and runner registration")
    if tuple(imports) != SLOW:
        raise ValueError("Slow root target inventory changed")
    if any(module.replace(".", "/") + ".lean" not in sources for module in SLOW):
        raise ValueError("Missing committed slow source")
    if git(root, "diff", "HEAD", "--name-only") or git(root, "rev-parse", "HEAD").decode().strip() != head:
        raise ValueError("Source changed during inventory")
    return {"schemaVersion": 1, "status": "prepared-not-executed", "head": head,
            "tree": git(root, "rev-parse", "HEAD^{tree}").decode().strip(),
            "sourceInventory": inventory, "slowModules": list(SLOW),
            "rootGate": "SoliditySlowExamples", "executionContext": context,
            "measurementDeadlineSeconds": 300,
            "slowLibraryDeadlineSeconds": 600 if context == "ci" else 300,
            "slowModuleDeadlineSeconds": {
                module: 600 if context == "ci" else 300
                for module in SLOW},
            "derived17ReplayDeadlineSeconds": 600 if context == "ci" else 300,
            "deadlinePolicy": "Default/VM module maximum remains300seconds. Coordinator explicitly "
                              "extends600seconds to the H109 slow library in CI; default/VM STOPs remain. "
                              "Original Derived17 CI600/local300 replay scope is retained. "
                              "The library deadline is not multiplied by its15members. "
                              "No non-slow module/VM increase. Context is a plan input, not CI attestation.",
            "workerPolicy": {"memoryMaxBytes": 12884901888, "swapMaxBytes": 0,
                             "leanThreads": 1, "lakeJobs": 1, "outerReserveBytes": 4294967296},
            "preparerSha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "boundary": "Committed regular source bytes only; ignored/untracked files are excluded. "
                        "Execution must use a sealed read-only source snapshot, never this live tree. "
                        "No cache/toolchain/resource authentication, measurement, runtime or CI pass yet."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--head", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--context", choices=("ci", "lane-end"), default="lane-end")
    args = parser.parse_args()
    plan = prepare(args.root, args.head, args.context)
    # Exclusive creation: no stale plan can be overwritten or mistaken for a run.
    descriptor = os.open(args.output, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(descriptor, "w") as stream:
        json.dump(plan, stream, indent=2)
        stream.write("\n")
