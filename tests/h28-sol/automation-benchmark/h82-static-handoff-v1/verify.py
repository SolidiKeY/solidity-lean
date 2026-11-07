"""Guard historical packet byte identity after explicit path relocation.

Only static hash/source/dry-run checks: no Lean execution or proposal application.
Historical manifest paths and hashes remain unchanged; missing or changed bytes fail.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys


def path_maps(pairs):
    """Explicit absolute prefix mappings, most specific first; no ambiguous duplicate."""
    result = []
    seen = set()
    for old, new in pairs:
        old, new = Path(old), Path(new)
        if not old.is_absolute() or not new.is_absolute() or ".." in old.parts or ".." in new.parts:
            raise ValueError("path-map roots must be absolute without parent traversal")
        if old in seen:
            raise ValueError("duplicate historical path-map root")
        if not new.is_dir():
            raise ValueError("relocated path-map root is not an existing directory")
        seen.add(old)
        result.append((old, new.resolve()))
    return sorted(result, key=lambda pair: len(pair[0].parts), reverse=True)


def source_path(recorded, mappings):
    source = Path(recorded)
    if not source.is_absolute() or ".." in source.parts:
        raise ValueError("historical evidence path must be absolute without parent traversal")
    for old, new in mappings:
        if source.is_relative_to(old):
            relocated = (new / source.relative_to(old)).resolve()
            if not relocated.is_relative_to(new):
                raise ValueError("relocated evidence escapes mapped root")
            return relocated
    return source


def verify_entries(entries, mappings=()):
    if not isinstance(entries, list) or len(entries) != 20:
        raise ValueError("expected exactly 20 historical evidence entries")
    for entry in entries:
        source = source_path(entry["path"], mappings)
        if source.stat().st_size != entry["bytes"]:
            raise ValueError(f"size mismatch: {source}")
        if hashlib.sha256(source.read_bytes()).hexdigest() != entry["sha256"]:
            raise ValueError(f"SHA256 mismatch: {source}")


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    pairs = []
    if argv:
        import argparse
        parser = argparse.ArgumentParser(description=__doc__)
        parser.add_argument("--path-map", nargs=2, action="append", default=[],
                            metavar=("HISTORICAL_ROOT", "EXISTING_ROOT"))
        pairs = parser.parse_args(argv).path_map
    packet = Path(__file__).resolve().parent
    repo = packet.parents[3]
    try:
        verify_entries(json.loads((packet / "evidence-manifest.json").read_text()), path_maps(pairs))
        state = json.loads((packet / "reconciliation.json").read_text())
        if state["runtime_gate_pass"] or state["audit_calculus"]["merged"]:
            raise ValueError("historical reconciliation must retain its unaccepted/unmerged status")
        for name in ["tests/h28-sol/automation-benchmark/ContextControls.lean",
                     "Solidity/Automation/H28/Context.lean", "lean-toolchain"]:
            committed = subprocess.check_output(["git", "show", "HEAD:" + name], cwd=repo)
            if committed != (repo / name).read_bytes():
                raise ValueError(f"live source differs from HEAD: {name}")
        subprocess.run(["git", "apply", "--check", str(packet / "API-only.unvalidated.patch")],
                       cwd=repo, check=True)
    except OSError as error:
        print(f"UNVERIFIABLE: historical bytes unavailable: {error}", file=sys.stderr)
        return 1
    except (ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        print(f"FAIL: static packet verification: {error}", file=sys.stderr)
        return 1
    print("PASS: 20 source/receipt hashes; live sources and pin unchanged; patch dry-run only")
    print("No Lean execution or formal/runtime/trust acceptance")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
