#!/usr/bin/env python3
"""Validate frozen measurements, removal scope, manifests and audit-only handoff."""
import json, pathlib, subprocess
here = pathlib.Path(__file__).resolve().parent
summary = json.loads((here / "summary.json").read_text())
family = json.loads((here / "family.json").read_text())
located = json.loads((here / "statements.json").read_text())
native = json.loads((here / "native-statements.json").read_text())
def git(*args): return subprocess.check_output(["git", *args], text=True).strip()
base = summary["base"]; prototype = summary["prototype_commit"]
assert base == "381328f608032dd19c405373c2b265e83a969850"
subprocess.run(["git", "merge-base", "--is-ancestor", base, prototype], check=True)
paths = {m.replace(".", "/") + ".lean" for m in family}
deleted = set(git("diff", "--name-only", "--diff-filter=D", base, prototype, "--", "Solidity/").splitlines())
assert deleted == paths
assert not git("diff", "--name-only", "--diff-filter=M", base, prototype, "--", "Solidity/")
assert sum(len(subprocess.check_output(["git", "show", base + ":" + path], text=True).splitlines()) for path in paths) == summary["before"]["physical_lines"]
assert len(family) == summary["before"]["files"] == 178
assert sum(map(len, located.values())) == summary["before"]["public_source_located_theorems"] == 1158
assert len(native) == len(set(native)) == summary["before"]["public_emitted_native_theorems"] == 2714
assert {r["name"] for rs in located.values() for r in rs} <= set(native)
assert summary["after"]["physical_lines"] == summary["after"]["lexical_declarations"] == 0
assert summary["kernel_check"]["before_checked_theorems"] == 2931
assert summary["kernel_check"]["after_checked_theorems"] == summary["kernel_check"]["after_seconds"] == 0
assert summary["kernel_check"]["negative_control_rejected"] is True
assert summary["theorem_preservation"]["all_family_exports_preserved"] is False
assert not git("diff", base, prototype, "--", "Solidity/Theorems.lean")
assert summary["verdict"] == "GO" and summary["after"]["physical_lines"] * 3 <= summary["before"]["physical_lines"]
changed = git("diff", "--name-only", base, "HEAD").splitlines()
assert changed and all(path.startswith("docs/audits/shrink/tv-backend/") for path in changed)
print("TV_BACKEND_AUDIT_PASS", len(family), "files; removal prototype valid; final diff audit-only")
