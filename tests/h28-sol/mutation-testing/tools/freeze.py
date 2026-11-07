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
            # The pilots' "negative-control" label meant a second mutant of the
            # family (e.g. the erased increment), scored like any other.
            semantic.append({"id": c["id"], "kind": "mutant" if c["kind"] == "negative-control" else c["kind"],
                             "pilot_kind": c["kind"], "family": c["family"],
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
                     "from_pilot": None, "note": "separate callback table (H28 queue item 4)",
                     "require": ["checked_kill", "checked_callback_frames"]})
    # Census mutants with their own witnesses (Claude VM, 2026-11-05).
    census = {m["id"]: m for m in data["mutants"]}
    for cid, fam, base, kill in [
            ("ifElseSplit.guard-true-to-false.1", "guard-polarity", "IfElseBaseline", "IfThenPolarityKill"),
            ("ifElseSplit.guard-false-to-true.1", "guard-polarity", "IfElseBaseline", "IfElsePolarityKill"),
            ("transferNoCallbackBox.payment-amount-zeroed.1", "rollback-payment", "TransferBaseline", "TransferZeroKill"),
            ("transferDiamond.close-false-to-true.1", "rollback-payment", "TransferDiamondBaseline", "TransferDiamondTrueKill"),
            ("storageRootDelete.delete-dropped.1", "pop-delete", "RootDeleteBaseline", "RootDeleteSkippedKill"),
            ("storageRootIncrement.increment-step-dropped.1", "overflow", "RootIncBaseline", "RootIncSkipKill")]:
        m = census[cid]
        assert m["family"] == fam
        o, w = (f"tests/h28-sol/mutation-testing/oracles/{n}.lean" for n in (base, kill))
        semantic.append({"id": "census." + cid, "kind": "mutant", "family": fam, "constructor": m["constructor"],
                         "target": m["target"], "old": m["old"], "new": m["new"], "oracle": o,
                         "oracle_sha256": sha(o), "witness": w, "witness_sha256": sha(w),
                         "from_pilot": None, "census_id": cid})
    guard = next(c for c in semantic if c["id"] == "guard.require-success-false")
    pop = next(c for c in semantic if c["id"] == "pop.empty-skipped")
    # Runner self-test: a real witness of another constructor must never kill.
    semantic.append(dict(guard, id="control.cross-witness-survivor", kind="runner-survivor-control",
                         witness=pop["witness"], witness_sha256=pop["witness_sha256"],
                         expect="link-mismatch",
                         note="guard mutant checked with the pop witness: its source link names popSave, so no kill"))
    rules = (ROOT / sites.RULES if hasattr(sites, "RULES") else ROOT / "Solidity/Calculus/Rules.lean").read_text()
    req = next(r for r in data["mutants"] if r["constructor"] == "Taclet.requireSimple")
    controls = [
        {"id": "control.proof-invalid-syntax", "constructor": "Taclet.requireSimple", "operator": "control",
         "family": "guard-polarity", "target": req["target"], "old": req["old"],
         "new": req["old"].replace('"Holds": se = true', '"Holds": se = )'), "affected": ["Taclet.requireSimple"],
         "expect": "invalid-compilation"},
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
                controls=[c["id"] for c in controls] + ["control.cross-witness-survivor",
                                                         "control.guard-label-equivalent", "control.revert-diamond-true"],
                semantic_cases=semantic)
    # A hand-selected case whose mutated file equals a census mutant's is that
    # census mutant (one proof entry); the others get their own proof entry.
    texts = {t: (ROOT / t).read_text() for t in ("Solidity/Calculus/Rules.lean", "Solidity/Calculus/CallbackRules.lean")}
    by_text = {(m["target"], texts[m["target"]].replace(m["old"], m["new"], 1)): m["id"] for m in data["mutants"]}
    pilots = []
    for c in semantic:
        if c["kind"] == "runner-survivor-control":
            continue
        same = by_text.get((c["target"], texts[c["target"]].replace(c["old"], c["new"], 1)))
        if same:
            c["census_id"] = same
            continue
        pilots.append({"id": "pilot." + c["id"], "constructor": c["constructor"], "operator": "pilot-hand-selected",
                       "family": c["family"], "target": c["target"], "old": c["old"], "new": c["new"],
                       "affected": [c["constructor"]] if c["constructor"].split(".")[0] in
                       ("Taclet", "LeanTaclet", "CallbackTaclet") else ["*"]})
        if c["kind"] == "equivalent-control":
            pilots[-1]["expect"] = "equivalent-certified"
    data["mutants"] = data["mutants"] + pilots + controls
    out = LANE / "manifests/h28-full.json"
    out.write_text(json.dumps(data, indent=1, ensure_ascii=False) + "\n")
    print(out.relative_to(ROOT), len(data["mutants"]), "proof entries,", len(semantic), "semantic cases")


if __name__ == "__main__":
    main()
