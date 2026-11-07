"""Evidence-backed coordination contacts; never transfers producer ownership."""
import fnmatch
import hashlib
import json
from pathlib import Path


def inventory(paths, inputs=Path("/workspace/h62-coordinator-inputs")):
    expected = json.loads((inputs/"sha256.json").read_text())["ownership.json"]
    data = (inputs/"ownership.json").read_bytes()
    if hashlib.sha256(data).hexdigest() != expected:
        raise RuntimeError("coordinator ownership snapshot checksum mismatch")
    snapshot = json.loads(data)
    rows = [r for r in snapshot["items"] if r["id"].startswith("H30-WRITER")]
    result = {}
    for path in paths:
        contacts = []
        for row in rows:
            include = [p.strip() for p in row.get("writeScope", "").split(";") if p.strip()]
            exclude = [p.strip() for p in row.get("writeExclusions", "").split(";") if p.strip()]
            if any(fnmatch.fnmatchcase(path,p) for p in include) and not any(fnmatch.fnmatchcase(path,p) for p in exclude):
                contacts.append({"owner":row["owner"],"record":row["id"],"status":row["status"],
                                 "role":"coordination contact; semantic producer not inferred"})
        if len({r["owner"] for r in contacts}) > 1:raise RuntimeError("conflicting writer contacts: "+path)
        route = None
        if path.startswith("Solidity/Backend/Creation/"):
            route={"gate":"G44.02","owner_key":"V14","evidence":"docs/feature-work/backend-creation-artifacts.md:1"}
        elif path.startswith("Solidity/Backend/Failure/"):
            route={"gate":"G38","owner_key":"V12","evidence":"docs/feature-work/backend-failure-emission.md:1"}
        elif path in {"Solidity/Calculus/StaticInvocation.lean","Solidity/Calculus/PrimitiveReturnTransport.lean","Solidity/Calculus/StaticStorageTransport.lean"}:
            route={"gate":"P2/P3","owner_key":"RO","evidence":"coordinator ownership snapshot P2/P3 entries"}
        if route:route["status"]="producer-family routing; exact-file confirmation pending"
        result[path]={"writer_contacts":contacts,"producer_route":route,
                      "owner_status":"exact semantic producer pending",
                      "ownership_snapshot_sha256":expected}
    return result
