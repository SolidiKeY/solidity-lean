#!/usr/bin/env python3
"""Guard generated-constant omissions and stale fixture-census promotion.

Live execution only. The validator alone is not a completeness or authenticity
check. Results describe imported constants from one pinned fixture module,
not source-line correspondence, unloaded/private artifact levels, arbitrary
project declarations or ownership.
"""
import argparse
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from bind_signature_fixture import (ROOT, FIXTURES, module_from, sha, regular,
    check_inputs, rebuild, writer_lease, clean_environment, checked_process,
    runtime_files, companion_artifacts, observer, scanner, expected_log_hash, verify_process_logs)

PINS = FIXTURES / "kernel-census-pins.json"
PREFIX = "H62_KERNEL_CENSUS "
MODULE = ["str", ["anonymous"], "SignatureFingerprint"]
KINDS = {"axiom", "definition", "theorem", "opaque", "quotient", "inductive", "constructor", "recursor"}


def name_key(value):
    if value == ["anonymous"]:
        return ()
    if not isinstance(value, list) or len(value) != 3 or value[0] not in ("str", "num"):
        raise ValueError("malformed constant name")
    parent = name_key(value[1])
    if value[0] == "str":
        if not isinstance(value[2], str) or not value[2]:
            raise ValueError("malformed string name component")
    elif type(value[2]) is not int or value[2] < 0:
        raise ValueError("malformed numeric name component")
    return parent + ((value[0], value[2]),)


def validate(value, expected_module=MODULE):
    """Structural refusal controls only; a saved packet cannot authorize a run."""
    if (not isinstance(value, dict) or set(value) != {"format", "module", "total", "rows"}
        or type(value["format"]) is not int or value["format"] != 1 or value["module"] != expected_module
        or type(value["total"]) is not int or value["total"] <= 0
        or not isinstance(value["rows"], list) or len(value["rows"]) != value["total"]):
        raise ValueError("census header/count mismatch")
    seen = set()
    for row in value["rows"]:
        if not isinstance(row, dict) or row.get("kind") not in KINDS:
            raise ValueError("census row kind")
        status = row.get("status")
        if status == "serialized":
            if set(row) != {"declaration", "kind", "status", "signature"} or not isinstance(row["signature"], list):
                raise ValueError("serialized row fields")
        elif status == "unsupported":
            if set(row) != {"declaration", "kind", "status", "reason"} or not isinstance(row["reason"], str) or not row["reason"]:
                raise ValueError("unsupported row fields")
        else:
            raise ValueError("census status")
        key = name_key(row["declaration"])
        if not key or key in seen:
            raise ValueError("duplicate/anonymous constant")
        seen.add(key)
    return value


def verify_fixture_controls(value, known_records):
    """Guard actual generated recursor/matcher and namespace/type separations."""
    by_name = {name_key(row["declaration"]): row for row in value["rows"]}
    for known in known_records:
        row = by_name.get(name_key(known["declaration"]))
        if not row or row.get("status") != "serialized" or row.get("signature") != known["signature"]:
            raise ValueError("five-record contract absent or changed in module census")
    def key(parts):
        return tuple(("str", part) for part in ("H62Signature", *parts))
    required = {
        ("Controls", "Indexed", "rec"): "recursor",
        ("Controls", "Indexed", "mk"): "constructor",
        ("Controls", "Indexed", "casesOn"): "definition",
        ("encodeExpr", "match_1"): "definition",
    }
    for parts, kind in required.items():
        row = by_name.get(key(parts))
        if not row or row["kind"] != kind or row["status"] != "serialized":
            raise ValueError("required generated fixture constant absent/refused: "+".".join(parts))
    pairs = [(("alphaA",), ("differentBinder",), False),
             (("universeA",), ("universeB",), True),
             (("First", "sameSpelling"), ("Second", "sameSpelling"), False)]
    for left, right, equal in pairs:
        a, b = by_name.get(key(("Controls", *left))), by_name.get(key(("Controls", *right)))
        if not a or not b or a["status"] != "serialized" or b["status"] != "serialized":
            raise ValueError("required fixture separation constant absent/refused")
        if (a["signature"] == b["signature"]) != equal:
            raise ValueError("fixture namespace/binder/universe separation failed")
    return {"generated_constants": len(required), "type_comparisons": len(pairs),
            "original_records": len(known_records)}


def read_log(path, expected_sha256=None):
    raw = observer.read_log_bytes(path, expected_sha256)
    lines = raw.decode("utf-8").splitlines()
    env = [line for line in lines if line.startswith(observer.PREFIX)]
    census = [line for line in lines if line.startswith(PREFIX)]
    if len(env) != 1 or len(census) != 1 or len(lines) != 2:
        raise ValueError("unexpected census log lines")
    return (observer.json_load(env[0][len(observer.PREFIX):].encode()),
            validate(observer.json_load(census[0][len(PREFIX):].encode())))


def run(output):
    """Caller must hold writer lease through rebuild, probe and artifact checks."""
    pins = json.loads(PINS.read_text())
    probe = FIXTURES / "SignatureKernelCensus.lean"
    if regular(probe)["sha256"] != pins["probe_sha256"]:
        raise ValueError("census probe pin drift")
    if sha(FIXTURES / "local-rebuild-pins.json") != pins["local_rebuild_pins_sha256"]:
        raise ValueError("census local rebuild contract drift")
    if not output.is_absolute():
        raise ValueError("census output must be absolute")
    output.mkdir(mode=0o700, exist_ok=False)
    receipt = {"schema": 1, "kind": "trusted-local-fixture-kernel-census", "status": "failed",
               "driver_sha256": sha(Path(__file__)), "probe_sha256": pins["probe_sha256"],
               "pins_sha256": sha(PINS), "steps": [],
               "boundary": "Trusted live fixture enumeration only; no source-line mapping, general project coverage, ownership or remote attestation."}
    try:
        live = rebuild(output / "rebuild")
        # Reuse the existing receipt seal with its minimal regular-file capability.
        receipt["rebuild_receipt_sha256"] = scanner.live_receipt_hash(SimpleNamespace(regular=regular),output / "rebuild",live)
        compiler_pins = json.loads((FIXTURES / "local-rebuild-pins.json").read_text())
        compiler = check_inputs(compiler_pins)
        original_env, _, _ = observer.read_log(output / "rebuild/logs/consumer.log",expected_log_hash(live["steps"],output / "rebuild/logs/consumer.log"))
        before = observer.capture_environment(original_env)
        if observer.canonical(before["artifacts"]) != observer.canonical(live["compiled_artifacts"]):
            raise ValueError("rebuild artifacts changed before census")
        companions = companion_artifacts(before["artifacts"])
        runtime = runtime_files(compiler)
        staged = output / "SignatureKernelCensus.lean"
        staged.write_bytes(probe.read_bytes()); staged.chmod(0o444)
        if regular(staged)["sha256"] != pins["probe_sha256"]:
            raise ValueError("staged census probe pin drift")
        env = dict(clean_environment(compiler), LEAN_PATH=str(output / "rebuild/compiled"))
        log = output / "census.log"
        checked_process([str(compiler), "-j1", "--tstack=131072", "--root="+str(output), str(staged)],
                        env, log, receipt["steps"])
        observed, census = read_log(log,expected_log_hash(receipt["steps"],log))
        old, current = dict(original_env), dict(observed)
        if observer.name_parts(old.pop("main_module")) != ("SignatureObservedConsumer",):
            raise ValueError("unexpected rebuild main module")
        if observer.name_parts(current.pop("main_module")) != ("SignatureKernelCensus",):
            raise ValueError("unexpected census main module")
        if observer.canonical(old) != observer.canonical(current):
            raise ValueError("census import environment differs")
        after = observer.capture_environment(observed)
        if observer.canonical(before["artifacts"]) != observer.canonical(after["artifacts"]):
            raise ValueError("census dependency artifacts changed")
        if companions != companion_artifacts(after["artifacts"]) or runtime != runtime_files(compiler):
            raise ValueError("census companion/runtime drift")
        if sha(staged) != pins["probe_sha256"] or regular(probe)["sha256"] != pins["probe_sha256"]:
            raise ValueError("census source changed during execution")
        check_inputs(compiler_pins)
        controls = verify_fixture_controls(census, live["records"])
        counts = {status: sum(row["status"] == status for row in census["rows"])
                  for status in ("serialized", "unsupported")}
        (output / "census.json").write_text(json.dumps(census, sort_keys=True, indent=2)+"\n")
        verify_process_logs(receipt["steps"]); verify_process_logs(live["steps"])
        scanner.live_receipt_hash(SimpleNamespace(regular=regular),output / "rebuild",live)
        receipt.update(status="pass", total=census["total"], counts=counts, controls=controls,
                       census_sha256=sha(output / "census.json"),
                       original_five_record_contract_unchanged=True,
                       imported_module_artifact_count=len(after["artifacts"]))
    except Exception as exc:
        receipt["error"] = str(exc)
        raise
    finally:
        (output / "receipt.json").write_text(json.dumps(receipt, indent=2)+"\n")
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        with writer_lease():
            result = run(args.output)
    except (OSError, ValueError, RecursionError, subprocess.SubprocessError) as exc:
        parser.exit(1, "KERNEL_CENSUS_REJECT: "+str(exc)+"\n")
    print("LOCAL_KERNEL_CENSUS_PASS "+json.dumps({k:result[k] for k in ("total", "counts")}))


if __name__ == "__main__":
    main()
