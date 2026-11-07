"""Shared fail-closed proof/source/runtime receipt validation; no Lean calls."""
import hashlib,json,re
from pathlib import Path
import census as canonical
root=Path(__file__).resolve().parents[4]

def checked_receipt(path, evidence):
    receipt = json.loads((evidence/(path.stem+".json")).read_text())
    assert receipt.get("isError") is False
    audit = receipt["_audit"]
    assert audit["tool"] == "lean_diagnostic_messages"
    assert audit["file"] == str(path)
    assert audit["arguments"]["file_path"] == str(path.relative_to(root))
    assert audit["arguments"].get("interactive") is False
    assert set(audit["arguments"]) <= {"file_path", "interactive", "timeout_s", "severity"}, "partial diagnostic selection"
    assert audit["base"] == canonical.BASE and audit["frozen_sources_clean"] is True
    assert audit["lean_version"] == "Lean (version 4.24.0, x86_64-unknown-linux-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release)"
    assert audit["lean_num_threads"] == 1
    assert audit["support_before"] == audit["support_after"]
    support_paths = {"tests/h62/item2/audit-abi-world/H62AbiWorld/WitnessSchema.lean",
        "tests/h62/item2/audit-abi-world/serial.lakefile.toml",
        "scripts/h62/item2/audit-abi-world/mcp_call.py", "scripts/h62/item2/audit-abi-world/bin/lake",
        "lean-toolchain", "lakefile.toml"}
    assert set(audit["support_before"]) == support_paths
    for support, digest in audit["support_before"].items():
        assert hashlib.sha256((root/support).read_bytes()).hexdigest() == digest, f"stale dependency: {support}"
    resource = json.loads((evidence/(path.stem+"-resource.json")).read_text())
    assert resource["guard_sha256"] == hashlib.sha256((root/"scripts/h62/item2/audit-abi-world/bounded.py").read_bytes()).hexdigest(), "stale resource guard"
    assert resource["stdout_file"] == str((evidence/(path.stem+".json")).resolve())
    assert resource["stdout_sha256"] == hashlib.sha256((evidence/(path.stem+".json")).read_bytes()).hexdigest(), "proof output digest mismatch"
    assert resource["reason"] is None and resource["exit_code"] == 0
    assert resource["cleanup_complete"] is True and resource["subreaper"] is True
    assert resource["swap_active_seen"] is False and resource["lean_num_threads"] == 1
    assert resource["reserve_bytes"] == 4*1024**3 and resource["task_cap_bytes"] == 12*1024**3
    assert resource["hard_cgroup_limit_bytes"] == 16*1024**3 and resource["address_space_limit"] is None
    assert resource["minimum_available_bytes"] >= resource["reserve_bytes"]
    assert resource["peak_task_rss_bytes"] <= resource["task_cap_bytes"]
    assert resource["max_heavy_lean_jobs"] <= 1
    if path.stem == "RuntimeVectors":
        assert resource["command"] == [".venv/bin/python","-B","scripts/h62/item2/audit-abi-world/vectors_call.py"]
    elif path.stem == "Fidelity":
        assert resource["command"] == [".venv/bin/python","-B","scripts/h62/item2/audit-abi-world/fidelity_call.py"]
    else:
        assert len(resource["command"]) == 5
        assert resource["command"][:4] == [".venv/bin/python","-B","scripts/h62/item2/audit-abi-world/mcp_call.py","lean_diagnostic_messages"]
        assert json.loads(resource["command"][4]) == audit["arguments"]
    data = receipt["structuredContent"]["result"]
    assert data.get("success") is True and data.get("partial") is False and data.get("timed_out") is False
    assert not data.get("failed_dependencies")
    assert not any(item.get("severity") == "error" for item in data.get("items", []))
    actual_hash = hashlib.sha256(path.read_bytes()).hexdigest()
    assert audit["source_sha256"] == actual_hash == audit["after_sha256"]
    for item in data["items"]:
        message = item.get("message", "")
        if "depends on axioms:" in message:
            match = re.search(r"depends on axioms: \[([^\]]*)\]", message)
            assert match
            axioms = {a.strip() for a in match[1].split(",") if a.strip()}
            assert axioms <= {"propext", "Classical.choice", "Quot.sound"}, message
    return data, actual_hash
