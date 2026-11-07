#!/usr/bin/env python3
"""Regression acceptance for the confirmed independent-review findings."""
import importlib.util
import pathlib
import tempfile
import subprocess
import sys

root = pathlib.Path(__file__).resolve().parents[4]
spec = importlib.util.spec_from_file_location("census",root/"scripts/h62/item2/audit-memory-operations/census.py")
census = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census)
fixture = """namespace A
/- theorem hidden : False := by /- nested -/ sorry -/
private theorem retained (n : Nat) :
    let x := n
    x = n := by rfl
structure Contract : Prop where
  success : True
  feasible : ∃ n : Nat, n = 1

def unrelated : Nat := 0
section S
variable (P : Prop)
theorem conditional (h : P) : P := h
end S
end A
"""
with tempfile.TemporaryDirectory() as directory:
    p = pathlib.Path(directory)
    (p/"Fixture.lean").write_text(fixture)
    rows = census.scan(p,"Fixture.lean")
    assert [r["name"] for r in rows] == ["A.retained","A.Contract","A.conditional"]
    assert rows[0]["visibility"] == "private"
    assert "let x := n" in rows[0]["source_command_region"]
    assert "x = n := by rfl" in rows[0]["source_command_region"]
    assert "unrelated" not in rows[1]["source_command_region"]
    assert "feasible" in rows[1]["source_command_region"]
    for row in rows:
        assert row["source_command_region"] == fixture[row["source_start"]:row["source_end"]]
        assert row["source_region_sha256"] == census.digest(row["source_command_region"])
        assert row["status"] == "unverified"
        assert "not a kernel FQN" in row["name_kind"]
    # Private source spellings can repeat across files; path identities must survive.
    (p/"Other.lean").write_text(fixture)
    other = census.scan(p,"Other.lean")
    assert rows[0]["name"] == other[0]["name"] and rows[0]["path"] != other[0]["path"]
with tempfile.TemporaryDirectory() as directory:
    result = subprocess.run([sys.executable,
        str(root/"scripts/h62/item2/audit-memory-operations/bounded-build.py"),
        "--lean", "/nonexistent/lean", "--evidence", directory,
        "Missing.Audit.Target"],cwd=root,capture_output=True,text=True)
    assert result.returncode != 0 and "TARGET_BLOCK" in result.stderr
source,modules,missing = census.modules(root)
assert len(modules) == 550 and not missing
assert len(modules) == len(set(modules))
print("PASS: let-conclusion retention, structure boundaries, private identity, nested comments, source offsets, all 550 mapped modules")
