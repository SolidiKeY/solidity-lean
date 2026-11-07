#!/usr/bin/env python3
"""Guard regression: standalone runtime probes are treated as ordinary proofs.

Static source references only; no execution, complete recipe or acceptance.
"""
import hashlib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
UPSTREAM = "tests/upstream/"
G49 = "tests/h55/g49-final-theorem/"
YUL = "tests/yul-composition/"
G49_ROLES = {"FoldedPublicControls.lean": "axiom-control", "PassCorrectAdapterControls.lean": "axiom-control",
             "PassCorrectControls.lean": "synthetic-pass-control", "PremiseInventory.lean": "premise-inventory",
             "staging/CalculusConsumer.lean": "staged-snapshot", "staging/CalculusControls.lean": "staged-snapshot"}
HELD = {"held/FailureDriver.lean", "held/FailurePhysical.lean", "held/IndexedWritePhysical.lean", "held/ReturningPhysical.lean"}
UPSTREAM_NODE = {"EnumAbiRanges.lean", "AbiEntryReplay.lean", "Replay.lean"}
YUL_DRIVERS = {"AttemptDriver.lean", "CatchFunctionDriver.lean", "ComponentDriver.lean",
               "DoWhileDriver.lean", "ForDriver.lean", "FunctionDriver.lean",
               "HeapCatchDriver.lean", "LocalDriver.lean", "ModifierDriver.lean",
               "ModifierPostDriver.lean", "NestedModifierDriver.lean", "PhysicalDriver.lean",
               "RawCatchDriver.lean", "RecursiveDriver.lean", "RethrowDriver.lean",
               "RuntimeBlockDriver.lean", "ScopeCatchDriver.lean", "UncheckedLoopDriver.lean"}
TOKENS = re.compile(r"solc_import|#eval!?|#guard_msgs|#print\s+axioms|IO\.FS")


def classify(root, manifest):
    if not isinstance(manifest, dict) or not isinstance(manifest.get("rows"), list):
        raise ValueError("invalid census")
    root = pathlib.Path(root)
    out, seen = [], set()
    for entry in manifest["rows"]:
        if not isinstance(entry, dict) or not isinstance(entry.get("path"), str):
            raise ValueError("invalid census row")
        path = entry["path"]
        groups = ((UPSTREAM, "upstream"), (G49, "g49"), (YUL, "yul-composition"))
        found = [(prefix, group) for prefix, group in groups if path.startswith(prefix)]
        if not found:
            continue
        prefix, group = found[0]
        rel = path[len(prefix):]
        if (path in seen or not path.endswith(".lean") or "\\" in path
                or any(p in ("", ".", "..") for p in path.split("/"))):
            raise ValueError("invalid selected path")
        seen.add(path)
        source = root / path
        if source.is_symlink() or not source.is_file() or source.resolve() != source:
            raise ValueError("invalid source")
        raw = source.read_bytes()
        if hashlib.sha256(raw).hexdigest() != entry.get("sha256"):
            raise ValueError("source differs from census")
        lines = raw.decode("utf8").splitlines()
        hints = [{"line": i, "tokens": sorted(set(m.group(0) for m in TOKENS.finditer(line)))}
                 for i, line in enumerate(lines, 1) if TOKENS.search(line)]
        if group == "upstream":
            role = "unresolved-upstream-fixture"
            driver = "scripts/test-solidity.test.mjs" if rel in UPSTREAM_NODE else "unresolved"
            effects = "unverified; solc AST, evaluation or I/O hints require review"
        elif group == "g49":
            role = G49_ROLES.get(rel)
            if role is None:
                raise ValueError("unreviewed G49 file")
            driver = ("unresolved-staged-snapshot" if role == "staged-snapshot" else
                      "scripts/h55/g49-final-theorem/check-pass-chain.py" if rel == "PremiseInventory.lean" else
                      "scripts/h55/g49-final-theorem/check-pass-correct.py")
            effects = "driver may write private oleans, logs and receipts; exact invocation unverified"
        else:
            if rel in HELD:
                role, driver = "held-source-producer-unresolved", "unresolved"
            elif rel in YUL_DRIVERS:
                role, driver = "external-runtime-driver", "per-file external driver unverified"
            elif rel in ("RethrowControls.lean", "V16Signatures.lean"):
                role, driver = "control-or-signature", "unresolved"
            else:
                raise ValueError("unreviewed Yul composition file")
            effects = ("--run driver may print JSON; external callers may write evidence; exact invocation unverified"
                       if role == "external-runtime-driver" else "unverified; held or non-driver control")
        out.append({"candidate": entry, "group": group, "role": role, "driver_reference": driver,
                    "expected_outcome": "unresolved per current invocation", "auxiliary_inputs": "unresolved per invocation",
                    "side_effects": effects, "lexical_hints": hints, "status": "static-reference-not-execution-acceptance"})
    return out


def main():
    if len(sys.argv) != 2:
        print("usage: standalone_runtime_classify.py CENSUS.json", file=sys.stderr)
        return 2
    try:
        raw = pathlib.Path(sys.argv[1]).read_bytes()
        print(json.dumps({"status": "partial-static-classification-not-acceptance", "coverage": "unverified-subsets-accepted",
                          "census_sha256": hashlib.sha256(raw).hexdigest(), "rows": classify(ROOT, json.loads(raw))}, indent=2, sort_keys=True))
        return 0
    except (OSError, UnicodeError, ValueError) as exc:
        print(f"classification unavailable: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
