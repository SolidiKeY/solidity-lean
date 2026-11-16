#!/usr/bin/env python3
"""Reproduce public, source-located theorem names from native graph + ILeans.
Arguments: GRAPH_JSONL MATCHED_ARTIFACT_VIEW OUTPUT_JSON
Generate graph using direction-tools/declgraph/Export.lean and family.json modules.
Includes source-located generated auxiliary theorems; private names are excluded.
"""
import json, pathlib, sys
here = pathlib.Path(__file__).resolve().parent
graph, view, output = sys.argv[1:4]
native = {r["name"]: r for line in pathlib.Path(graph).read_text().splitlines() for r in [json.loads(line)]}
family = json.loads((here / "family.json").read_text())
assert all(r["module"] in set(family) for r in native.values()), "graph must contain only selected modules"
result = {}
for module in family:
    data = json.loads((pathlib.Path(view) / (module.replace(".", "/") + ".ilean")).read_text())
    rows = []
    for key, value in data["references"].items():
        const = json.loads(key).get("c", {}); name = const.get("n"); info = native.get(name, {})
        if value["definition"] is not None and info.get("kind") == "theorem" and not name.startswith("_private"):
            assert const.get("m") == module
            rows.append({"name": name, "line": value["definition"][0] + 1})
    if rows: result[module] = sorted(rows, key=lambda r: r["name"])
pathlib.Path(output).write_text(json.dumps(result, indent=2) + "\n")
print("THEOREM_MANIFEST_PASS", sum(map(len, result.values())))

if len(sys.argv) == 5:
    emitted = sorted(r["name"] for r in native.values() if r["kind"] == "theorem" and not r["name"].startswith("_private"))
    pathlib.Path(sys.argv[4]).write_text(json.dumps(emitted, indent=2) + "\n")
    print("PUBLIC_EMITTED_THEOREMS", len(emitted))
