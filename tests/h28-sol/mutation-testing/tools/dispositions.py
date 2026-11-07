#!/usr/bin/env python3
"""Per-constructor dispositions of a whole-manifest run.

Joins the frozen manifest's census (all 215 constructors), the draft
heuristic family tags (`inventory.draft.json`, kept unchanged) and a run's
`summary.json`.  Every constructor gets exactly one disposition:

* `sites-run`: it has family-operator sites; their outcomes are listed.
* `no-premise-text`: its premise is a named function (`blockEmpty`,
  `tryCallSelfBox`, `catchDataBox`, ...) or it is a `Rule` wrapper, so no
  table text exists to mutate; the function lives outside the read-only
  rule-table inputs.
* `no-family-site`: its premise text matches no operator of the nine
  families (for a heuristic tag, the tag came from its name or a capture,
  not from a family clause).

Helper (`Tms`) mutants and the hand-selected pilot cases are listed apart.
Writes `dispositions.json` into the run directory and prints a Markdown table
of family counts.
"""
import json
from pathlib import Path
import sys


def main(manifest_path, run_dir):
    lane = Path(__file__).resolve().parents[1]
    manifest = json.loads(Path(manifest_path).read_text())
    summary = json.loads((Path(run_dir) / "summary.json").read_text())
    draft = {r["id"]: r["families"] for r in json.loads((lane / "inventory.draft.json").read_text())["inventory"]}
    by_ctor = {}
    for m in manifest["mutants"]:
        by_ctor.setdefault(m["constructor"], []).append(m["id"])
    root = lane.parents[2]
    texts = {}
    def mutated(t, old, new):
        if t not in texts:
            texts[t] = (root / t).read_text()
        return t, texts[t].replace(old, new, 1)
    semantic_of = {}
    for c in manifest.get("semantic_cases", []):
        if c["kind"] in ("mutant", "negative-control", "known-kill"):
            semantic_of[mutated(c["target"], c["old"], c["new"])] = (c["id"], summary["semantic"][c["id"]]["outcome"])
    sem = {m["id"]: semantic_of.get(mutated(m["target"], m["old"], m["new"])) for m in manifest["mutants"]}
    rows = []
    for c in manifest["constructors"]:
        ids = [i for i in by_ctor.get(c["id"], []) if not i.startswith(("pilot.", "control."))]
        if ids:
            disp = "sites-run"
        elif not c["premise_written"]:
            disp = "no-premise-text"
        else:
            disp = "no-family-site"
        rows.append({"constructor": c["id"], "line": c["line"], "file": c["file"],
                     "heuristic_families": draft.get(c["id"], []), "disposition": disp,
                     "mutants": {i: summary["mutants"][i]["outcome"] for i in ids},
                     "semantic": {i: {"case": sem[i][0], "outcome": sem[i][1]} for i in ids if sem.get(i)}})
    extra = {m["id"]: summary["mutants"][m["id"]]["outcome"] for m in manifest["mutants"]
             if m["id"].startswith(("pilot.", "control.")) or m["constructor"].startswith("Tms.")}
    out = {"manifest_sha256": summary["manifest_sha256"], "head": summary["head"],
           "constructors": len(rows), "rows": rows, "helpers_pilots_controls": extra}
    (Path(run_dir) / "dispositions.json").write_text(json.dumps(out, indent=1) + "\n")
    counts = {}
    for r in rows:
        counts[r["disposition"]] = counts.get(r["disposition"], 0) + 1
    linked = {i: v for r in rows for i, v in r["semantic"].items()}
    out["census_mutants_with_semantic_witness"] = linked
    (Path(run_dir) / "dispositions.json").write_text(json.dumps(out, indent=1) + "\n")
    print("constructors:", len(rows), counts)
    print("census mutants with a semantic case:", len(linked),
          {o: sum(v["outcome"] == o for v in linked.values()) for o in {v["outcome"] for v in linked.values()}})
    fam = summary["proof_oracle"]["by_family"]
    keys = sorted({k for v in fam.values() for k in v})
    print("| family | " + " | ".join(keys) + " |")
    print("|---|" + "---|" * len(keys))
    for f in sorted(fam):
        print(f"| {f} | " + " | ".join(str(fam[f].get(k, 0)) for k in keys) + " |")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
