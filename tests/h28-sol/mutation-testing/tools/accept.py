#!/usr/bin/env python3
"""H28 acceptance: is the final run scope-complete?

Reads a frozen schema-3 manifest with a clause inventory
(`manifests/h28-final.json`) and the run directory `mcprun.py` wrote for it,
recomputes the summary from the per-check records (each record's own
classification is read as stored; `mcprun.py` made it from the record's
diagnostics), and checks every obligation below.  `scope_complete` is true
only if all hold; each failure is listed.

1. The run is of this manifest (sha256) and has a summary; the summary equals
   the one recomputed from the records.
2. Every proof baseline passes.
3. Every proof entry (census sites, helper edits, clause fixtures, pilots,
   controls) has a record and none is `unrun` or `error`.
4. Every constructor of the four tables is accounted for: it has census
   sites, or a clause-inventory row whose every clause has a fixture with a
   record, or a stated reason; and the two sets partition the constructors.
5. Every one of the nine families has a census- or clause-linked semantic
   verdict (`killed` or `survivor-sound`) of a mutant of that family whose
   proof entry is in the manifest.
6. Every semantic case has a decision, none `unrun` or `error`; every
   control meets its expectation; and every family has a semantic negative
   control (a witness check that must not kill) that passed.  Constructors
   with no compiled mutant are listed, not failed.
"""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import mcprun  # noqa: E402

FAMILIES = ["guard-polarity", "overflow", "division-minimum", "index-bounds", "push-tail-length",
            "pop-delete", "alias-capture-once", "rollback-payment", "callback-frames"]
# semantic checks that must not kill (a proof-oracle control is not one)
NEGATIVE = {"witness-failed", "link-mismatch", "equivalent", "semantic-witness-failed"}


def accept(manifest_path, run_dir):
    manifest_path, run_dir = Path(manifest_path), Path(run_dir)
    manifest = json.loads(manifest_path.read_text())
    fails = []
    stored = json.loads((run_dir / "summary.json").read_text()) if (run_dir / "summary.json").exists() else None
    if stored is None:
        fails.append("no summary.json")
    elif stored.get("manifest_sha256") != mcprun.sha(manifest_path.read_bytes()):
        fails.append("summary is of another manifest")
    if stored and stored.get("dirty_development_run"):
        fails.append("development run (uncommitted inputs)")
    summary = mcprun.summarize(manifest, run_dir)
    if stored is not None:
        for k in ("controls", "proof_baselines", "proof_oracle", "semantic", "mutants"):
            if stored.get(k) != summary.get(k):
                fails.append("stored summary differs from the records: " + k)
    # 2
    bad = {k: v for k, v in summary["proof_baselines"].items() if v != "pass"}
    if bad:
        fails.append(f"baselines not passing: {bad}")
    # 3
    bad = {k: v["outcome"] for k, v in summary["mutants"].items() if v["outcome"] in ("unrun", "error")}
    if bad:
        fails.append(f"{len(bad)} proof entries unrun or in error: {sorted(bad)[:10]}")
    # 4
    all_ctors = {r["id"] for r in manifest["constructors"]}
    with_sites = {r["id"] for r in manifest["constructors"] if r["sites"] > 0}
    rows = {r["constructor"]: r for r in manifest.get("clause_inventory", [])}
    if with_sites & set(rows):
        fails.append(f"constructors both in the census and the clause inventory: {sorted(with_sites & set(rows))}")
    missing = all_ctors - with_sites - set(rows)
    if missing:
        fails.append(f"{len(missing)} constructors unaccounted for: {sorted(missing)[:10]}")
    for cid in with_sites:
        if not any(m["constructor"] == cid and summary["mutants"].get(m["id"], {}).get("outcome") not in
                   (None, "unrun", "error") for m in manifest["mutants"]):
            fails.append(f"census constructor without a decided site: {cid}")
    for cid, r in rows.items():
        if not r["clauses"]:
            fails.append(f"clause row without clauses: {cid}")
        for c in r["clauses"]:
            if c["fixture"] is None:
                if not c.get("reason"):
                    fails.append(f"clause without fixture or reason: {cid}: {c['clause']}")
            elif summary["mutants"].get(c["fixture"], {}).get("outcome") in (None, "unrun", "error"):
                fails.append(f"clause fixture undecided: {c['fixture']}")
    # 5
    fam_of_mutant = {m["id"]: m["family"] for m in manifest["mutants"]}
    verdicts = {}
    for c in manifest["semantic_cases"]:
        o = summary["semantic"][c["id"]]["outcome"]
        # the verdict counts for a family only if the mutant it is about
        # carries that family
        if fam_of_mutant.get(c.get("census_id")) == c["family"] and \
                c["kind"] in ("mutant", "known-kill", "sound-survivor") and o in ("killed", "survivor-sound"):
            verdicts.setdefault(c["family"], []).append(c["id"])
    for f in FAMILIES:
        if f not in verdicts:
            fails.append(f"family without a census-linked semantic verdict: {f}")
    # 6
    bad = {k: v["outcome"] for k, v in summary["semantic"].items()
           if v["outcome"] in ("unrun", "error", "unrun-or-error")}
    if bad:
        fails.append(f"semantic cases unrun or in error: {bad}")
    if not summary["controls_pass"]:
        fails.append("controls: " + json.dumps({k: v for k, v in summary["controls"].items()
                                                if v["expect"] != v["actual"]}))
    fam_of = {c["id"]: c["family"] for c in manifest["semantic_cases"]}
    fam_of.update({m["id"]: m["family"] for m in manifest["mutants"]})
    negatives = {}
    for k, v in summary["controls"].items():
        if v["expect"] in NEGATIVE and v["expect"] == v["actual"]:
            negatives.setdefault(fam_of.get(k), []).append(k)
    for f in FAMILIES:
        if f not in negatives:
            fails.append(f"family without a passing negative control: {f}")
    compiled = {m["constructor"] for m in manifest["mutants"]
                if summary["mutants"].get(m["id"], {}).get("outcome") in ("detected", "equivalent-certified")}
    no_compiled = sorted(c for c in all_ctors if c not in compiled)
    semantic_negatives = {f: [k for k in v if fam_of.get(k) == f and
                              summary["controls"][k]["expect"] == "semantic-witness-failed"]
                          for f, v in negatives.items()}
    return {"scope_complete": not fails, "failures": fails,
            # disclosed, not a failure: every one-change edit of these the
            # census or the inventory tried is refused by the rule language
            # (or the constructor is a premise-less wrapper)
            "constructors_without_compiled_mutant": no_compiled,
            "family_semantic_negative_controls": {f: v for f, v in semantic_negatives.items() if v},
            "manifest": str(manifest_path), "manifest_sha256": mcprun.sha(manifest_path.read_bytes()),
            "run": run_dir.name, "head": stored and stored.get("head"),
            "constructors": len(all_ctors), "census_constructors": len(with_sites),
            "clause_rows": len(rows),
            "clause_fixtures": sum(1 for r in rows.values() for c in r["clauses"] if c["fixture"]),
            "clauses_with_reason": sum(1 for r in rows.values() for c in r["clauses"] if not c["fixture"]),
            "proof_entries": len(summary["mutants"]),
            "family_verdicts": verdicts, "family_negative_controls": negatives,
            "proof_oracle": summary["proof_oracle"]["all_entry_counts"],
            "semantic_counts": summary["semantic_witness_validation"]["counts"]}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("manifest")
    ap.add_argument("run")
    ap.add_argument("--write", help="write the acceptance record here")
    a = ap.parse_args()
    r = accept(a.manifest, a.run)
    text = json.dumps(r, indent=1, ensure_ascii=False) + "\n"
    if a.write:
        Path(a.write).write_text(text)
    print(text)
    sys.exit(0 if r["scope_complete"] else 1)
