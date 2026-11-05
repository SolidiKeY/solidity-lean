#!/usr/bin/env python3
"""Freeze the whole H28 manifest (schema 3) from the mechanical site census
(`sites.py`), the reviewed semantic cases of the frozen pilot manifests and
the runner's negative controls.  Writes `manifests/h28-full.json`."""
import glob
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).parent))
import sites

LANE = Path(__file__).resolve().parents[1]
ROOT = LANE.parents[2]


def sha(p):
    return hashlib.sha256((ROOT / p).read_bytes()).hexdigest()


def main():
    data = sites.manifest(ROOT)
    semantic, seen = [], set()
    for f in sorted(glob.glob(str(LANE / "manifests/*-pilot.json"))):
        for c in json.loads(Path(f).read_text())["cases"]:
            if c["id"] in seen or c["kind"] not in ("mutant", "negative-control", "known-kill", "equivalent-control"):
                continue
            seen.add(c["id"])
            witness = c.get("witness") or c.get("equivalence")
            semantic.append({"id": c["id"], "kind": c["kind"], "family": c["family"],
                             "constructor": c.get("constructor_id"), "target": c["target"],
                             "old": c["old"], "new": c["new"], "oracle": c["oracle"],
                             "oracle_sha256": sha(c["oracle"]), "witness": witness,
                             "witness_sha256": sha(witness), "from_pilot": Path(f).name})
    cbr = (ROOT / "Solidity/Calculus/CallbackRules.lean").read_text()
    old = '        ; "send failed": { pv := false } ⟨[ ]⟩ }\n  | sendWithCallbackDiamond'
    assert cbr.count(old) == 1
    semantic.append({"id": "callback-table.failed-send-flag-true", "kind": "mutant", "family": "callback-frames",
                     "constructor": "CallbackTaclet.sendWithCallbackBox", "target": "Solidity/Calculus/CallbackRules.lean",
                     "old": old, "new": old.replace("pv := false", "pv := true"),
                     "oracle": "tests/h28-sol/mutation-testing/oracles/CallbackTacletBaseline.lean",
                     "oracle_sha256": sha("tests/h28-sol/mutation-testing/oracles/CallbackTacletBaseline.lean"),
                     "witness": "tests/h28-sol/mutation-testing/oracles/CallbackTacletFailureKill.lean",
                     "witness_sha256": sha("tests/h28-sol/mutation-testing/oracles/CallbackTacletFailureKill.lean"),
                     "from_pilot": None, "note": "separate callback table (H28 queue item 4)"})
    guard = next(c for c in semantic if c["id"] == "guard.require-success-false")
    pop = next(c for c in semantic if c["id"] == "pop.empty-skipped")
    # Runner self-test: a real witness of another constructor must never kill.
    semantic.append(dict(guard, id="control.cross-witness-survivor", kind="runner-survivor-control",
                         witness=pop["witness"], witness_sha256=pop["witness_sha256"],
                         expect="surviving",
                         note="guard mutant checked with the pop witness: its source link names popSave, so no kill"))
    rules = (ROOT / sites.RULES if hasattr(sites, "RULES") else ROOT / "Solidity/Calculus/Rules.lean").read_text()
    req = next(r for r in data["mutants"] if r["constructor"] == "Taclet.requireSimple")
    controls = [
        {"id": "control.proof-invalid-syntax", "constructor": "Taclet.requireSimple", "operator": "control",
         "family": "guard-polarity", "target": req["target"], "old": req["old"],
         "new": req["old"].replace('"Holds": se = true', '"Holds": se = )'), "affected": ["Taclet.requireSimple"],
         "expect": "invalid-compilation"},
        {"id": "control.proof-label-renamed", "constructor": "Taclet.requireSimple", "operator": "control",
         "family": "guard-polarity", "target": req["target"], "old": req["old"],
         "new": req["old"].replace('"Holds"', '"holds"'), "affected": ["Taclet.requireSimple"],
         "expect": "recorded",
         "note": "branch labels: detected if toStep compares them, equivalent-certified otherwise"},
    ]
    for c in controls:
        assert c["old"] != c["new"]
    data.update(schema=3, state="frozen", scope="whole-declared-manifest",
                proof_baselines=[{"id": "rules-taclet", "mode": "full", "target": "Solidity/Calculus/Rules.lean",
                                  "oracle": "Solidity/Calculus/Taclet.lean"},
                                 {"id": "rules-taclet-rows", "mode": "rows", "target": "Solidity/Calculus/Rules.lean",
                                  "oracle": "Solidity/Calculus/Taclet.lean, every row by #h28_toStep_row"},
                                 {"id": "callback-totaclet", "mode": "callback",
                                  "target": "Solidity/Calculus/CallbackRules.lean",
                                  "oracle": "CallbackTaclet.toTaclet (in the target)"}],
                oracle_sha256={"Solidity/Calculus/Taclet.lean": sha("Solidity/Calculus/Taclet.lean")},
                controls=[c["id"] for c in controls] + ["control.cross-witness-survivor"],
                semantic_cases=semantic)
    pilots = [{"id": "pilot." + c["id"], "constructor": c["constructor"], "operator": "pilot-hand-selected",
               "family": c["family"], "target": c["target"], "old": c["old"], "new": c["new"],
               "affected": [c["constructor"]] if c["constructor"].split(".")[0] in ("Taclet", "LeanTaclet", "CallbackTaclet") else ["*"]}
              for c in semantic if c["kind"] in ("mutant", "negative-control", "known-kill", "equivalent-control")]
    data["mutants"] = data["mutants"] + pilots + controls
    out = LANE / "manifests/h28-full.json"
    out.write_text(json.dumps(data, indent=1, ensure_ascii=False) + "\n")
    print(out.relative_to(ROOT), len(data["mutants"]), "proof entries,", len(semantic), "semantic cases")


if __name__ == "__main__":
    main()
