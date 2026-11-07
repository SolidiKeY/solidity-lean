"""Guard against hiding unrelated browser failures behind the known stack STOP.

Use retained external receipts; no browser, runtime or stopped workload runs.
"""

import argparse
import contextlib
import copy
import io
import json
from pathlib import Path
import runpy


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("gate", "report", "build"):
        parser.add_argument(name, type=Path)
    args = parser.parse_args()
    gate, report, build = (json.loads(p.read_text()) for p in (args.gate, args.report, args.build))
    module = runpy.run_path(str(Path(__file__).with_name("known-stack-continuation.py")))
    check = module["allow_continuation"]
    inputs = module["retained_inputs"](args.report)
    with contextlib.redirect_stdout(io.StringIO()) as output:
        check(gate, report, build, 1, inputs)
    assert "KNOWN_FAIL_RETAINED" in output.getvalue() and "remains FAIL" in output.getvalue()
    cases = []

    def reject(name, edit, reason, status=1):
        g, r, b = copy.deepcopy((gate, report, build))
        edit(g, r, b)
        try:
            check(g, r, b, status, inputs)
        except (ValueError, KeyError) as error:
            assert reason in str(error), (name, str(error))
        else:
            raise AssertionError(f"Accepted unrelated failure: {name}")
        cases.append(name)

    reject("timeout", lambda g, r, b: None, "Unexpected browser gate exit", 124)
    reject("runner-exit", lambda g, r, b: g.update(exitCode=2), "Unexpected browser gate exit")
    reject("resource-stop", lambda g, r, b: g.update(resourceStop=True), "Resource STOP")
    reject("runner-identity", lambda g, r, b: g.update(runnerSha256="0" * 64), "Runner identity mismatch")
    reject("scope", lambda g, r, b: g.update(scope={}), "bounded scope")
    reject("headroom", lambda g, r, b: g.update(minimumOuterHeadroomBytes=0), "headroom")
    reject("incomplete", lambda g, r, b: r.update(failure="timeout"), "Incomplete browser report")
    reject("page-error", lambda g, r, b: r["errors"].append("unrelated"), "Unexpected errors")
    reject("forbidden-load", lambda g, r, b: r["forbiddenAssetRequests"].append("x.olean"), "forbiddenAssetRequests")
    reject("external-load", lambda g, r, b: r["externalRequests"].append("https://other/"), "externalRequests")
    reject("binary", lambda g, r, b: b.update(wasm="0" * 64), "Binary identity mismatch")
    reject("boots", lambda g, r, b: r["workerBoots"].pop(), "Incomplete worker boots")
    reject("extra-failure", lambda g, r, b: r["failures"].append({"index": 0}), "failure set")
    reject("missing-request", lambda g, r, b: r["requests"].pop(), "Incomplete browser requests")
    # Keep the duplicated failure record consistent, so each later control
    # reaches the specific invariant/sibling guard instead of the set guard.
    def change_request(index, edit):
        def apply(g, r, b):
            edit(r["requests"][index])
            if index == 4:
                r["failures"][0]["record"] = copy.deepcopy(r["requests"][index])
        return apply
    reject("changed-source", change_request(4, lambda q: q.update(sourceHash="0" * 64,
           compilerHeader={"sourceSha256": "0" * 64})), "Retained request/fixture/source identity mismatch")
    reject("different-error", change_request(4, lambda q: q["reply"]["workerError"].update(message="out of memory")), "Unexpected invariant error")
    reject("non-wasm-stack", change_request(4, lambda q: q["reply"]["workerError"].update(stack="RangeError: Maximum call stack size exceeded\n at js")), "Unexpected invariant stack")
    reject("different-expectations", change_request(0, lambda q: q.update(expected=[])), "Changed browser control expectations")
    reject("wrong-verdict", change_request(0, lambda q: q["reply"]["results"][0].update(status="proved")), "Unexpected sibling verdict")
    reject("request-identity", change_request(0, lambda q: q.update(observedSerializedParamsSha256="0" * 64)), "Request identity mismatch")
    reject("coordinated-wire", change_request(4, lambda q: q.update(wireSha256="0" * 64,
           observedSerializedParamsSha256="0" * 64)), "Retained request/fixture/source identity mismatch")
    reject("coordinated-sibling-source", change_request(0, lambda q: q.update(sourceHash="0" * 64,
           compilerHeader={"sourceSha256": "0" * 64})), "Retained request/fixture/source identity mismatch")
    reject("changed-fixture", change_request(4, lambda q: q.update(fixtureSha256="0" * 64)),
           "Retained request/fixture/source identity mismatch")
    reject("backend", change_request(0, lambda q: q["reply"]["timings"].update(backend="other")), "sibling backend/imports")
    for field in ("wireSha256", "fixtureSha256"):
        g, r, b, changed_inputs = copy.deepcopy((gate, report, build, inputs))
        r["requests"][4][field] = changed_inputs[0][4][field] = "0" * 64
        if field == "wireSha256":
            r["requests"][4]["observedSerializedParamsSha256"] = "0" * 64
        r["failures"][0]["record"] = copy.deepcopy(r["requests"][4])
        try:
            check(g, r, b, 1, changed_inputs)
        except ValueError as error:
            assert "Changed reviewed invariant request/fixture" in str(error)
        else:
            raise AssertionError(f"Accepted changed reviewed pin: {field}")
        cases.append("coordinated-input-" + field)
    print(json.dumps({"knownFailureRetained": True, "rejected": cases,
                      "historicalWorkloadExecuted": False}, indent=2))


if __name__ == "__main__":
    main()
