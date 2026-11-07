#!/usr/bin/env python3
"""Freeze the final H28 manifest (schema 3), `manifests/h28-final.json`.

It is the frozen `manifests/h28-full.json` unchanged (the 30-operator census,
the pilot and census semantic cases, the controls), plus:

* the clause-level inventory of the 98 constructors the census does not reach
  (`clauses.py`) with its 119 one-change fixtures, run through the proof oracle;
* per-family census witnesses for the families whose semantic verdict rested
  on a pilot or helper edit only (index-bounds, push-tail-length and
  alias-capture-once on census sites; division-minimum on a clause fixture,
  since its only compiled census site, the `Tms.Term.binop` operand swap,
  reaches length arithmetic, not a division);
* per-family negative controls: a family's real kill witness checked against
  another mutant (same constructor, or for alias and the helper families a
  related one), which must not kill; these fail at the link;
* semantic negative controls for four families: the kill argument with its
  premise replaced by the production one, which must fail after the link.

`scope` names what `accept.py` checks for `scope_complete`.
"""
import copy
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import clauses  # noqa: E402

LANE = Path(__file__).resolve().parents[1]
ROOT = LANE.parents[2]
O = "tests/h28-sol/mutation-testing/oracles/"


def sha(p):
    return hashlib.sha256((ROOT / p).read_bytes()).hexdigest()


def case(cid, kind, family, m, oracle, witness, **extra):
    c = {"id": cid, "kind": kind, "family": family, "constructor": m["constructor"], "target": m["target"],
         "old": m["old"], "new": m["new"], "oracle": O + oracle + ".lean", "oracle_sha256": sha(O + oracle + ".lean"),
         "witness": O + witness + ".lean", "witness_sha256": sha(O + witness + ".lean"), "from_pilot": None}
    c.update(extra)
    return c


def main():
    full = json.loads((LANE / "manifests/h28-full.json").read_text())
    data = copy.deepcopy(full)
    rows, fixtures = clauses.inventory(ROOT)
    clauses.check(rows)
    census = {m["id"]: m for m in full["mutants"] + fixtures}
    cases = {c["id"]: c for c in full["semantic_cases"]}

    new = []
    # Per-family census witnesses (families whose only semantic verdict was a
    # hand-typed pilot or helper edit).
    for cid, fam, kind, base, wit in [
            ("storageIndexReadArrayFind.index-constant-zero.1", "index-bounds", "mutant",
             "BoundsBaseline", "BoundsZeroKill"),
            ("clause.binopAssignment.operands-swapped.1", "division-minimum", "mutant",
             "DivAssignBaseline", "DivisionOperandsKill"),
            ("storagePushAddAssign.last-slot-is-length.1", "push-tail-length", "mutant",
             "PushOrderBaseline", "PushLastSlotKill"),
            ("storageLengthRead_unfold_rightFst.receiver-reevaluated.1", "alias-capture-once", "sound-survivor",
             "LengthReadBaseline", "LengthReevalSound")]:
        m = census[cid]
        assert m["family"] == fam, (cid, m["family"])
        extra = {"census_id": cid}
        new.append(case("census." + cid, kind, fam, m, base, wit, **extra))

    # Negative controls: a real kill witness, a different mutant.  Each must
    # end in `witness-failed` (same constructor) or `link-mismatch`.
    for fam, mid, src, expect in [
            ("pop-delete", "storagePopSave.last-slot-is-length.1", "pop.empty-skipped", "witness-failed"),
            ("index-bounds", "storageIndexReadArrayFind.index-constant-zero.1", "bounds.array-read-skipped",
             "witness-failed"),
            ("push-tail-length", "storagePushAddAssign.last-slot-is-length.1", "push.compound-updates-swapped",
             "witness-failed"),
            ("overflow", "binopC.helper-compound-operands-swapped.1", "overflow.compound-sub-helper-max",
             "witness-failed"),
            ("division-minimum", "binop.helper-binop-args-swapped.1", "division.div-sub-helper-min-and-zero",
             "witness-failed"),
            ("alias-capture-once", "storagePush_unfold_leftFstReceiver.receiver-reevaluated.1",
             "alias.receiver-getter-twice", "link-mismatch"),
            ("callback-frames", "sendWithCallbackBox.send-flag-true-to-false.1",
             "callback-table.failed-send-flag-true", "witness-failed"),
            ("rollback-payment", "sendNoCallbackBox.send-flag-false-to-true.1", "payment.success-flag-false",
             "witness-failed"),
            ("guard-polarity", "requireSimple.guard-false-to-true.1", "guard.require-success-false",
             "witness-failed")]:
        m, s = census[mid], cases[src]
        c = {"id": f"control.negative.{fam}", "kind": "negative-control", "family": fam,
             "constructor": m["constructor"], "target": m["target"], "old": m["old"], "new": m["new"],
             "oracle": s["oracle"], "oracle_sha256": s["oracle_sha256"], "witness": s["witness"],
             "witness_sha256": s["witness_sha256"], "from_pilot": None, "expect": expect,
             "note": f"the {src} kill witness checked against {mid}: it must not kill"}
        if "require" in s:
            c["require"] = s["require"]
        new.append(c)

    # Semantic negative controls: a real kill argument aimed at the production
    # premise.  The link elaborates on the unchanged table; the argument must
    # then fail (`semantic-witness-failed`); a pass would show the rule unsound.
    for fam, ctor, base, wit in [
            ("index-bounds", "Taclet.storageIndexReadArrayFind", "BoundsBaseline", "BoundsZeroOnProduction"),
            ("push-tail-length", "Taclet.storagePushAddAssign", "PushOrderBaseline", "PushLastSlotOnProduction"),
            ("division-minimum", "Taclet.binopAssignment", "DivAssignBaseline", "DivisionOperandsOnProduction"),
            ("pop-delete", "Taclet.storageRootDelete", "RootDeleteBaseline", "RootDeleteSkippedOnProduction")]:
        new.append({"id": f"control.semantic.{fam}", "kind": "semantic-control", "family": fam,
                    "constructor": ctor, "target": "Solidity/Calculus/Rules.lean",
                    "oracle": O + base + ".lean", "oracle_sha256": sha(O + base + ".lean"),
                    "witness": O + wit + ".lean", "witness_sha256": sha(O + wit + ".lean"),
                    "from_pilot": None, "expect": "semantic-witness-failed",
                    "note": "the family's kill argument, aimed at the production premise, must fail after the link"})

    data["mutants"] = full["mutants"] + fixtures
    data["semantic_cases"] = full["semantic_cases"] + new
    data["controls"] = full["controls"] + [c["id"] for c in new if c["kind"] in ("negative-control",
                                                                                "semantic-control")]
    data["clause_inventory"] = rows
    data["base_manifest"] = {"path": "tests/h28-sol/mutation-testing/manifests/h28-full.json",
                             "sha256": sha("tests/h28-sol/mutation-testing/manifests/h28-full.json")}
    data["generator"] = [full["generator"], "tests/h28-sol/mutation-testing/tools/clauses.py",
                         "tests/h28-sol/mutation-testing/tools/freeze_final.py"]
    data["scope"] = "whole-declared-manifest+clause-inventory"
    ids = [m["id"] for m in data["mutants"]]
    assert len(ids) == len(set(ids))
    sids = [c["id"] for c in data["semantic_cases"]]
    assert len(sids) == len(set(sids))
    out = LANE / "manifests/h28-final.json"
    out.write_text(json.dumps(data, indent=1, ensure_ascii=False) + "\n")
    print(out.relative_to(ROOT), len(data["mutants"]), "proof entries,", len(data["semantic_cases"]),
          "semantic cases,", len(rows), "clause rows")


if __name__ == "__main__":
    main()
