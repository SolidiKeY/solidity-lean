#!/usr/bin/env python3
"""Exact source/run evidence controls; this script does not execute Lean/Docker."""
import copy, hashlib, json, pathlib, re, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parent.parent
FILE = "Solidity/Lowering/V08/LocalCallableTransport.lean"
NAMESPACE = "Solidity.Lowering.V08.EffectfulCallableArgument."
NAMES = set("arguments_actual source_actual reversed_arguments_actual reversed_actual transport inhabited target_vector closed_client populated_retained wrong_order wrong_read skipped_write zero_horizon reached_timeout".split())
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
BASE = "3474cac74e7fb589d570ccf95a7d6a264f7f26dc"
def digest(data): return hashlib.sha256(data).hexdigest()
def validate(source, before, result, log, bindings):
    assert before["source"][FILE] == digest(source), "checked source binding"
    assert result["exit"] == result["actual_exit"] == 0
    assert result["source_and_controls_checked"] and result["cleanup_stopped"]
    assert result["H1"] and result["minimum_free_ram"] >= 4294967296
    assert result["peak_aggregate_rss"] <= 12884901888
    assert result["log_sha256"] == bindings["decoded_sha256"] == digest(log)
    assert b"H1_TARGET=@shared-file" in log and b"Build completed successfully (2 jobs)." in log
    assert b"error:" not in log
    target_file = "/workspace/v08-world-lowering-evidence/integrated-source-deployment-20261102/coord-access/current-file.txt"
    assert before["controls"][target_file] == digest((str(ROOT / FILE) + "\n").encode()), "exact checked module"
    text = source.decode()
    prefix = text.split("/-! A producer-backed G20 ARGUMENT component.")[0]
    for line in ["import Solidity.Lowering.V07.EffectfulCondition\n", "import Solidity.Lowering.V08.SourceCallableControls\n"]:
        assert prefix.count(line) == 1
        prefix = prefix.replace(line, "")
    original = subprocess.check_output(["git", "show", BASE + ":" + FILE], cwd=ROOT).decode()
    assert prefix.rstrip() == original.rstrip(), "all old source/guards unchanged"
    found = re.findall(r"/-- info: '" + re.escape(NAMESPACE) + r"(\w+)' depends on axioms: \[([^\]]*)\] -/\s*#guard_msgs in\s*#print axioms " + re.escape(NAMESPACE) + r"\1", text)
    assert len(found) == len(NAMES) and {name for name, _ in found} == NAMES
    assert all(set(re.findall(r"[\w.]+", axioms)) == STANDARD for _, axioms in found)
    for file in ["scripts/v08-coord-file.py", "scripts/v08-coord-file-run.py", "scripts/v08-integrated-check.sh"]:
        absolute = str(ROOT / file)
        assert before["controls"][absolute] == digest((ROOT / file).read_bytes()), "bridge/control binding"

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
    reject(s=source + b" ")
    for field, value in [("actual_exit", 1), ("source_and_controls_checked", False), ("cleanup_stopped", False), ("minimum_free_ram", 0), ("peak_aggregate_rss", 12884901889)]:
        bad = copy.deepcopy(result); bad[field] = value; reject(r=bad)
    bad = copy.deepcopy(before); bad["source"][FILE] = "0" * 64; reject(b=bad)
    bad = copy.deepcopy(before); bad["controls"][str(ROOT / "scripts/v08-coord-file.py")] = "0" * 64; reject(b=bad)
    bad = copy.deepcopy(before)
    bad["controls"]["/workspace/v08-world-lowering-evidence/integrated-source-deployment-20261102/coord-access/current-file.txt"] = digest((str(ROOT / "Solidity/Lowering/V08/SourceClockTransactions.lean") + "\n").encode())
    reject(b=bad)
    reject(l=log + b"error: corruption")
    # Rebind the corrupted source so this specifically reaches guard validation.
    bad_source = source.replace(b"#guard_msgs in\n#print axioms " + NAMESPACE.encode() + b"transport", b"#print axioms " + NAMESPACE.encode() + b"transport")
    assert bad_source != source
    bad = copy.deepcopy(before); bad["source"][FILE] = digest(bad_source)
    reject(s=bad_source, b=bad)
    print(f"PASS exact14 guards, old source unchanged, current source/control/log/resource binding; {count} corruption controls; no Lean/Docker")
if __name__ == "__main__": main()
