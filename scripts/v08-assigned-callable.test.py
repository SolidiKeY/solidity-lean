#!/usr/bin/env python3
"""Assigned callable source/certificate integrity; no Lean/Docker execution."""
import copy, hashlib, json, pathlib, re, runpy, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parent.parent
LEGACY = runpy.run_path(str(ROOT / "scripts/v08-effectful-callable.test.py"), run_name="preserved_checker")
FILE = LEGACY["FILE"]
NAMESPACE = "Solidity.Lowering.V08.AssignedIntegerCallable."
NAMES = set("argument_actual source_expression transport signed_client target_vector static_inputs static_client wrong_source_read wrong_target_read skipped_write reached_timeout zero_horizon unsigned_inputs unsigned_maximum closed_boundary payload_clients populated_fields".split())
BASE = "c18368cd1881d586809a6b579769ad278d4b9d1c"
PUBLIC = "312ed47a9ff23fd6b0e9f0206770e8deac0246e2"
PRODUCERS = ["Solidity/Lowering/V07/AssignmentOperands.lean", "Solidity/Lowering/V08/IntegerCallable.lean", "Solidity/Lowering/V08/SourceCallable.lean", "Solidity/Lowering/V08/SignedCallableControls.lean"]
def digest(data): return hashlib.sha256(data).hexdigest()
def validate(source, before, result, log, bindings):
    LEGACY["validate"](source, before, result, log, bindings)
    text = source.decode()
    prefix = text.split("/-! Environment/context/width-polymorphic assignment-argument application.")[0]
    previous = subprocess.check_output(["git", "show", BASE + ":" + FILE], cwd=ROOT).decode()
    assert prefix.rstrip() == previous.rstrip(), "entire predecessor source/guards preserved"
    found = re.findall(r"/-- info: '" + re.escape(NAMESPACE) + r"(\w+)' depends on axioms: \[([^\]]*)\] -/\s*#guard_msgs in\s*#print axioms " + re.escape(NAMESPACE) + r"\1", text)
    assert len(found) == len(NAMES) and {name for name, _ in found} == NAMES
    assert all(set(re.findall(r"[\w.]+", axioms)) == LEGACY["STANDARD"] for _, axioms in found)
    for file in PRODUCERS:
        current = (ROOT / file).read_bytes()
        published = subprocess.check_output(["git", "show", PUBLIC + ":" + file], cwd=ROOT)
        assert current == published and before["source"][file] == digest(published), "exact checked published producer"

def main():
    run = pathlib.Path(sys.argv[1])
    source = (ROOT / FILE).read_bytes()
    before = json.loads((run / "before.json").read_text())
    result = json.loads((run / "result.json").read_text())
    log = (run / "build.log").read_bytes()
    bindings = json.loads((run / "log-bindings.json").read_text())
    validate(source, before, result, log, bindings)
    count = 0
    def reject(s=source, b=before, r=result, l=log, k=bindings):
        nonlocal count
        try: validate(s, b, r, l, k)
        except AssertionError: count += 1; return
        raise AssertionError("corrupt evidence accepted")
    reject(s=source+b" ")
    for field, value in [("actual_exit", 1), ("source_and_controls_checked", False), ("peak_aggregate_rss", 12884901889)]:
        bad = copy.deepcopy(result); bad[field] = value; reject(r=bad)
    for file in PRODUCERS:
        bad = copy.deepcopy(before); bad["source"][file] = "0"*64; reject(b=bad)
    key = "/workspace/v08-world-lowering-evidence/integrated-source-deployment-20261102/coord-access/current-file.txt"
    bad = copy.deepcopy(before); bad["controls"][key] = digest(b"wrong file\n"); reject(b=bad)
    # Rebind to reach the exact NEW guard checks rather than only the hash check.
    for old, new in [
        (b"#guard_msgs in\n#print axioms " + NAMESPACE.encode() + b"transport", b"#print axioms " + NAMESPACE.encode() + b"transport"),
        (b"'" + NAMESPACE.encode() + b"closed_boundary' depends on axioms: [propext,", b"'" + NAMESPACE.encode() + b"closed_boundary' depends on axioms: [sorryAx,"),
    ]:
        corrupt = source.replace(old, new); assert corrupt != source
        bad = copy.deepcopy(before); bad["source"][FILE] = digest(corrupt); reject(s=corrupt,b=bad)
    print(f"PASS exact17 new +14 predecessor guards, full predecessor source, four published producers and checked-file/run binding; {count} corruptions; no Lean/Docker")
if __name__ == "__main__": main()
