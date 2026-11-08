#!/usr/bin/env python3
"""Rank connected runtime-frame removal candidates at the frozen pilot base.
Run from repository root: python3 -I docs/audits/shrink/tv-backend/inventory.py OUTPUT
Reads Git blobs, never the build cache. Generated Solidity umbrella import edges
are deliberately omitted: they express inventory policy, not semantic consumers.
The reflective scripts/AxiomAudit.lean consumer must be rebuilt separately.
"""
import argparse, collections, hashlib, json, pathlib, re, runpy, subprocess, sys
BASE = "381328f608032dd19c405373c2b265e83a969850"
PREFIX = "Solidity.Backend.InternalFlow."
ROOT = pathlib.Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
mask = runpy.run_path(str(ROOT / "docs/audits/direction-tools/statements/scan.py"))["mask"]
def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True)
def imports(raw):
    clean = mask(raw)
    return {name for line in clean.splitlines() if re.match(r"^\s*import\s", line)
            for name in line.split()[1:]}
def closure(graph, roots):
    seen, todo = set(), list(roots)
    while todo:
        name = todo.pop()
        if name in seen: continue
        seen.add(name)
        todo.extend(graph.get(name, set()) - seen)
    return seen
def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=pathlib.Path)
    parser.add_argument("--write-family", type=pathlib.Path)
    parser.add_argument("--check-family", action="store_true")
    args = parser.parse_args()
    assert not args.output.resolve().is_relative_to(ROOT), "inventory evidence must be external"
    paths = [p for p in git("ls-tree", "-r", "--name-only", BASE).splitlines() if p.endswith(".lean")]
    raw = {p[:-5].replace("/", "."): git("show", BASE + ":" + p) for p in paths}
    paths = {p[:-5].replace("/", "."): p for p in paths}
    graph = {m: imports(text) for m, text in raw.items()}
    umbrella_consumers = sorted(m for m, ds in graph.items() if "Solidity" in ds)
    graph["Solidity"] = set()
    family = {m for m in graph if m.startswith(PREFIX)}
    needed = closure(graph, set(graph) - family - {"Solidity"}) & family
    candidates = family - needed
    adjacent = {m: graph[m] & candidates for m in candidates}
    for m, ds in list(adjacent.items()):
        for d in list(ds): adjacent[d].add(m)
    components, seen = [], set()
    for m in sorted(candidates):
        if m in seen: continue
        component = closure(adjacent, [m]); seen |= component
        components.append(sorted(component))
    components.sort(key=lambda c: (-sum(len(raw[m].splitlines()) for m in c), c))
    selected = set(components[0])
    assert not any(ds & selected for m, ds in graph.items() if m not in selected)
    declaration = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(theorem|lemma|def|abbrev|structure|inductive|opaque|axiom)\s+([^\s:({\[]+)", re.M)
    def count(modules):
        kinds = collections.Counter(match[1] for m in modules for match in declaration.finditer(mask(raw[m])))
        return {"files": len(modules), "physical_lines": sum(len(raw[m].splitlines()) for m in modules),
                "lexical_declarations": sum(kinds.values()), "declaration_kinds": dict(sorted(kinds.items()))}
    result = {"base": BASE, "selection": "largest undirected import component after external dependency closure, omitting generated Solidity umbrella edges",
              "umbrella_consumers": umbrella_consumers, "directory": count(family), "externally_needed": count(needed),
              "candidate_total": count(candidates), "ranked_components": [dict(count(c), first=c[0]) for c in components],
              "selected": count(selected), "modules": sorted(selected),
              "sources": [{"path": paths[m], "sha256": hashlib.sha256(raw[m].encode()).hexdigest()} for m in sorted(selected)],
              "facade_import_overlap": sorted(closure(graph, ["Solidity.Theorems"]) & selected),
              "retained_import_edges_to_selected": 0,
              "limitations": ["Static import graph; no claim about dynamic or reflective consumers.", "Deleted theorem exports are not preserved by the prototype; no retained statement is edited."]}
    assert not result["facade_import_overlap"]
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    if args.write_family:
        args.write_family.write_text(json.dumps(result["modules"], indent=2) + "\n")
    if args.check_family:
        assert json.loads(pathlib.Path(__file__).with_name("family.json").read_text()) == result["modules"]
        print("FAMILY_SELECTION_CHECK_PASS", len(result["modules"]))
    print("INVENTORY_PASS", result["selected"])
if __name__ == "__main__": main()
