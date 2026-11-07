#!/usr/bin/env python3
"""Check the six frozen files' declaration names and explicit pipeline arms."""
import pathlib
import subprocess
import sys

script = pathlib.Path(__file__).with_name("census.py")
out = subprocess.check_output([sys.executable, str(script)], text=True)
sections = [s for s in out.split("Solidity/Backend/Passes/") if s.strip()]
common = set("C A Γ F target bases machine i a source initial compiled operand input application successMachine after prefix_run resultWord code emitted source_execution cells complete_observations different_pipelines stale_rhs_refused short_frame_refused corrupted_saved_tail".split())
extras = {
    "Addition": {"si", "ti", "family"},
    "Multiplication": {"si", "ti", "family", "unmasked", "unmaskedCode", "actual_unmasked", "unmasked_differs"},
    "Subtraction": {"reversed", "reversed_source", "wrong_order_reverts"},
}
expected_files = {f"Assignment{op}{kind}.lean" for op in extras for kind in ("Pass", "Controls")}
hashes = {
    "AssignmentAdditionPass.lean": "ddae871cd72fd0f2c5accfc3ffae28ab77bd1f6aa8798baeb6219aea838a98b7",
    "AssignmentAdditionControls.lean": "b99a10a9537fa350078beabf3d9bb6d61dec26837bf09d4e8e348174756ea991",
    "AssignmentMultiplicationPass.lean": "e6c77a1f0c6274c4ea9c30e10eb104391ca29a32ea63b34546d1f13d617bce9f",
    "AssignmentMultiplicationControls.lean": "9b6c09136923d9e6e4555d515ba4f6364c9579a9d9c4f839c3bd96bb0ff1db5a",
    "AssignmentSubtractionPass.lean": "9a42ebfa8977f69f9cf9c18e36e016fe6a85a78ef666aa134c138afe6da153d4",
    "AssignmentSubtractionControls.lean": "575a56350da76cce4b5846304628a75e1a6e5d70b0905c77cb747069c6b6232a",
}
def validate(sections):
    seen = set()
    for section in sections:
        lines = section.splitlines()
        name = lines[0].split()[0]
        assert name in expected_files and name not in seen, name
        seen.add(name)
        assert lines[0].split()[1] == "sha256=" + hashes[name], name
        op = next(op for op in extras if name.startswith("Assignment" + op))
        entries = [line.strip().split(": ", 1)[1].split() for line in lines[1:]]
        declarations = [entry[1] for entry in entries if entry[0] != "branch"]
        branches = [entry[1] for entry in entries if entry[0] == "branch"]
        expected = common | extras[op] if "Controls" in name else {"value", "reached", "reached_value", "execution"}
        assert len(declarations) == len(set(declarations)) and set(declarations) == expected, (name, declarations)
        assert branches == ([] if "Controls" in name else ["legacy", "viaIR", "legacy", "viaIR"]), (name, branches)
    assert seen == expected_files, (seen, expected_files)

validate(sections)
for original, replacement in (("def after", "def after_renamed"),
                              ("branch viaIR", "branch legacy"),
                              ("sha256=ddae", "sha256=0000")):
    altered = out.replace(original, replacement, 1)
    assert altered != out, original
    try:
        validate([s for s in altered.split("Solidity/Backend/Passes/") if s.strip()])
    except AssertionError:
        pass
    else:
        raise AssertionError("negative control accepted: " + original)
print("census: six frozen files, declaration names and explicit pipeline branches OK")
