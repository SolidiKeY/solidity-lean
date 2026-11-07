"""Guard continuation after only the retained invariantCountsToBound stack failure.

Returning zero permits independent controls to continue; the original browser
gate stays failed. This does not release the stack or performance STOP.
"""

import argparse
import hashlib
import json
import re
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def retained_inputs(report_path):
    """Bind report fields to retained inputs, baseline sources and ClosedSpecs."""
    root = Path(__file__).resolve().parents[4]
    names = ["additionSimple", "storageRootReadWrite", "storageIndexRootMapping",
             "whileCountsUp", "invariantCountsToBound", "requireFalseLiteral"]
    identities = []
    for i in range(7):
        source = report_path.parent / f"browser-control-completion-inputs/control-{i}.sol"
        fixture = source.with_suffix(".ast.json")
        canonical = (root / "docs/benchmarks/directruntime-2026-11-04/before/existing-controls"
                     / (names[i] + ".sol") if i < 6 else root / "tests/automation/ClosedSpecs.sol")
        require(source.read_bytes() == canonical.read_bytes(), "Retained control source changed")
        data = fixture.read_bytes()
        decoded = json.loads(data)
        contract = next(n for n in decoded["ast"]["nodes"] if n["nodeType"] == "ContractDefinition")
        request = {"contract": contract}
        if i < 6:
            request["function"] = names[i]
        wire = json.dumps(request, separators=(",", ":"), ensure_ascii=False).encode()
        source_hash = hashlib.sha256(source.read_bytes()).hexdigest()
        require(decoded["header"]["sourceSha256"] == source_hash, "Retained fixture source mismatch")
        identities.append({"sourceHash": source_hash, "fixtureSha256": hashlib.sha256(data).hexdigest(),
                           "wireSha256": hashlib.sha256(wire).hexdigest(),
                           "compilerHeader": decoded["header"]})
    runner = root / "tests/directruntime-20261104/native-browser/bounded-command.py"
    return identities, hashlib.sha256(runner.read_bytes()).hexdigest()


def allow_continuation(gate, report, build, status, inputs):
    identities, runner_hash = inputs
    require(status == 1 and gate["exitCode"] == 1, "Unexpected browser gate exit")
    require(gate["command"] == ["node", "tests/directruntime-20261104/native-browser/browser-control-completion.cjs"],
            "Unexpected browser gate command")
    require(gate["resourceStop"] is False, "Resource STOP cannot be bypassed")
    require(gate["runnerSha256"] == runner_hash, "Runner identity mismatch")
    require(gate["scope"] == {"memoryMaxBytes": 12884901888, "memorySwapMaxBytes": 0},
            "Unexpected bounded scope")
    require(gate["minimumOuterHeadroomBytes"] >= 4294967296, "Insufficient outer headroom")
    require(report["passed"] is False and "failure" not in report, "Incomplete browser report")
    for name in ("errors", "forbiddenAssetRequests", "externalRequests"):
        require(report[name] == [], f"Unexpected {name}")
    binary = build["wasm"]
    require(re.fullmatch(r"[0-9a-f]{64}", binary) is not None, "Invalid binary identity")
    require(report["binarySha256"] == binary, "Binary identity mismatch")
    boots = report["workerBoots"]
    require(len(boots) == 7 and report["boot"] == boots[0], "Incomplete worker boots")
    require(all(b["kind"] == "generated-c-wasm" and b["build"] == binary for b in boots),
            "Worker backend/binary mismatch")
    names = ["additionSimple", "storageRootReadWrite", "storageIndexRootMapping",
             "whileCountsUp", "invariantCountsToBound", "requireFalseLiteral",
             "fresh eight specifications"]
    expected = [[[name, ["pending", "refuted"]]] for name in names[:5]]
    expected += [[["requireFalseLiteral", ["proved"]]], [
        ["maximum", ["proved"]], ["falseMaximum", ["refuted"]],
        ["storeMaximum", ["proved"]], ["twoChoices", ["proved"]],
        ["constantOne", ["proved"]], ["falseConstant", ["refuted"]],
        ["store", ["proved"]], ["falseStore", ["refuted"]]]]
    requests = report["requests"]
    require(len(requests) == 7, "Incomplete browser requests")
    require(report["failures"] == [{"index": 4, "record": requests[4]}],
            "Unexpected browser failure set")
    for i, request in enumerate(requests):
        require(all(request[field] == value for field, value in identities[i].items()),
                "Retained request/fixture/source identity mismatch")
        require(request["name"] == names[i] and request["expected"] == expected[i],
                "Changed browser control expectations")
        require(request["workerEpoch"] == i + 1, "Worker epoch mismatch")
        require(request["wireSha256"] == request["observedSerializedParamsSha256"],
                "Request identity mismatch")
        require(request["compilerHeader"]["sourceSha256"] == request["sourceHash"],
                "Compiler source identity mismatch")
        reply = request["reply"]
        if i == 4:
            require(request["wireSha256"] == "f17d932db443b445b74ea755a2eb06c3bac593a41c2d3a280aeb914b3243e8fb"
                    and request["fixtureSha256"] == "89f5b5dea9547361a37a579cd366bfb5a42cbfa209a3090e6295541e4900d955",
                    "Changed reviewed invariant request/fixture")
            require(request["sourceHash"] == "12fe08c7ebcb4bced15227fa6d6829b63cce545b88229ff173f03b4ad4efc0fd",
                    "Changed known failing source")
            require(set(reply) == {"workerError"}, "Unexpected invariant reply")
            error = reply["workerError"]
            require(error["message"] == "Maximum call stack size exceeded",
                    "Unexpected invariant error")
            require(error["stack"].startswith("RangeError: Maximum call stack size exceeded\n")
                    and "wasm-function[" in error["stack"], "Unexpected invariant stack")
        else:
            require("workerError" not in reply, "Unexpected sibling worker failure")
            timings = reply["timings"]
            require(timings["backend"] == "generated-c-wasm" and timings["checkSequence"] == 1
                    and timings["environmentImports"] == 0, "Unexpected sibling backend/imports")
            rows = reply["results"]
            require(len(rows) == len(expected[i]), "Incomplete sibling results")
            require(all(row["function"] == spec[0] and row["status"] in spec[1]
                        for row, spec in zip(rows, expected[i])), "Unexpected sibling verdict")
    print("KNOWN_FAIL_RETAINED invariantCountsToBound stack overflow; "
          "independent checks may continue; browser gate remains FAIL")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("gate", type=Path)
    parser.add_argument("report", type=Path)
    parser.add_argument("build", type=Path)
    parser.add_argument("status", type=int)
    args = parser.parse_args()
    allow_continuation(*(json.loads(p.read_text()) for p in (args.gate, args.report, args.build)),
                       args.status, retained_inputs(args.report))
