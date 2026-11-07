"""Guard B journal delivery against substitution, selector drift and AST value drift.

This compares retained observations with the exact delivered original84 requests;
it does not replay new requests or infer semantic equivalence from metadata.
"""
import argparse, collections, copy, hashlib, json
from pathlib import Path

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def require(ok, message):
    if not ok:
        raise ValueError(message)

def compare(incoming, observed):
    counts = collections.Counter()
    def walk(a, b):
        require(type(a) is type(b), "AST value/type drift")
        if isinstance(a, dict):
            counts.update("incomingOnly:" + k for k in a.keys() - b.keys())
            counts.update("observedOnly:" + k for k in b.keys() - a.keys())
            for k in a.keys() & b.keys():
                walk(a[k], b[k])
        elif isinstance(a, list):
            require(len(a) == len(b), "AST list length drift")
            for x, y in zip(a, b):
                walk(x, y)
        else:
            require(a == b, "AST value/type drift")
    walk(incoming, observed)
    return counts

def selector(request):
    functions = [n for n in request["contract"]["nodes"]
                 if n.get("nodeType") == "FunctionDefinition"
                 and n.get("name") == request["function"]]
    require(len(functions) == 1 and functions[0]["id"] == request["sourceId"],
            "sourceId selector mismatch")

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--inbox", type=Path, default=Path("/workspace/h62-coordinator-inputs/router-20261106T200314Z"))
    ap.add_argument("--observations", type=Path, default=Path("/workspace/scratch/browser-chain/h81-memory"))
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    pins = {"browser-handoff.json": "53c9438eb30010736432d9bcde121ef94272efcfa243c25acfc034cb79c4879f",
            "requests.jsonl": "ae658ff7ea04b163a9d3939f58fc4b30acc15cf4cbe5487ca4abf5baddbb7f1d"}
    inputs = [args.inbox / n for n in pins] + [args.observations / n for n in
              ["control-inventory-with-guard.json", "browser-attempts-with-guard.jsonl"]]
    def snapshot():
        return {str(p): (digest(p), p.stat().st_ino, p.stat().st_size,
                        p.stat().st_mtime_ns, p.stat().st_ctime_ns) for p in inputs}
    before = snapshot()
    for name, pin in pins.items():
        require(digest(args.inbox / name) == pin, "delivered file hash mismatch: " + name)
    handoff = json.loads(inputs[0].read_text())
    raw = inputs[1].read_bytes().splitlines()
    delivered = [json.loads(line) for line in raw]
    inventory = json.loads(inputs[2].read_text())
    wires = [json.loads(line) for line in inputs[3].read_text().splitlines()]
    require(handoff["requestsSha256"] == pins["requests.jsonl"], "journal pin mismatch")
    require(len(delivered) == len(wires) == len(handoff["cases"]) == len(inventory["requests"]) == 84,
            "incomplete84 case denominator")
    require(len(inventory["native"]) == len(inventory["browser"]) == 84,
            "incomplete backend observation denominator")
    counts = collections.Counter()
    rows = []
    key = lambda c: c["id"] + "." + c["modality"] + (".ir" if c["viaIR"] else ".non-ir")
    require(len({key(c) for c in handoff["cases"]}) == 84, "duplicate case identity")
    for case, request, line, wire, observation, native, browser in zip(
            handoff["cases"], delivered, raw, wires, inventory["requests"], inventory["native"], inventory["browser"]):
        case_key = key(case)
        require(case_key == observation["caseKey"] == native["caseKey"] == browser["caseKey"], "case order mismatch")
        require(case["sourceSha256"] == observation["sourceHash"] == digest(Path(observation["original"])), "source hash mismatch")
        require(handoff["compilerPin"] == observation["compilerHeader"]["compilerSha256"], "compiler pin mismatch")
        old_wire = wire["wire"]
        require(hashlib.sha256(old_wire.encode()).hexdigest() == wire["wireSha256"] == observation["wireSha256"] == native["wireSha256"] == browser["wireSha256"], "observed wire mismatch")
        selector(request)
        counts.update(compare(request, json.loads(old_wire)))
        require(native["reply"]["results"] == browser["reply"]["results"], "saved backend result mismatch")
        status = native["reply"]["results"][0]["status"]
        require(case["requiredProven"] == (status == "proved"), "required-positive mismatch")
        rows.append({"caseKey": case_key, "sourceSha256": case["sourceSha256"],
                     "deliveredLineSha256": hashlib.sha256(line).hexdigest(),
                     "observedWireSha256": wire["wireSha256"], "sourceId": request["sourceId"],
                     "exactRequestObjectEqual": request == json.loads(old_wire), "savedStatus": status})
    # Confirm the reconciliation rejects drift instead of accepting all comparisons.
    bad = copy.deepcopy(delivered[0]); bad["sourceId"] += 1
    try:
        selector(bad)
    except ValueError as e:
        require(str(e) == "sourceId selector mismatch", "wrong selector failure")
    else:
        raise ValueError("selector negative was accepted")
    bad = copy.deepcopy(delivered[0]); bad["function"] = "different"
    try:
        compare(bad, json.loads(wires[0]["wire"]))
    except ValueError as e:
        require(str(e) == "AST value/type drift", "wrong value failure")
    else:
        raise ValueError("AST negative was accepted")
    require(snapshot() == before, "input metadata changed")
    report = {"deliveredFiles": [{"path": str(args.inbox / n), "sha256": pin} for n, pin in pins.items()],
              "observedFiles": [{"path": str(p), "sha256": before[str(p)][0]} for p in inputs[2:]],
              "cases": rows, "commonValueDifferences": 0, "fieldPresenceCounts": dict(sorted(counts.items())),
              "exactRequestObjectsEqual": sum(r["exactRequestObjectEqual"] for r in rows),
              "controls": ["selector drift rejected", "AST value drift rejected"],
              "primaryFilesUnchanged": True,
              "boundary": "Exact original journal received;84 source/compiler/case identities reconcile. Complete request equality is reported per case. Common fields match; absent fields are inventoried, not restricted to metadata by this checker. Only four primary files have before/after metadata snapshots; referenced sources are content-hashed once. This checker reconciles saved data; it does not execute backends or prove semantic equivalence. Existing STOPs/pending/refusals remain."}
    with args.output.open("x") as f:
        f.write(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"cases": len(rows), "commonValueDifferences": 0,
                      "exactRequestObjectsEqual": report["exactRequestObjectsEqual"], "primaryFilesUnchanged": True}))

if __name__ == "__main__":
    main()
