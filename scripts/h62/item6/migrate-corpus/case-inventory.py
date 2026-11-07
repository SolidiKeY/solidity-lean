#!/usr/bin/env python3
"""Record every original corpus expected row, retaining unsupported/refuted cases."""
import collections, hashlib, json, pathlib, subprocess, sys
root=pathlib.Path(__file__).resolve().parents[4]
base="c6f550e281a7e5affa9a99bc2cdaed556dec00e4"
raw=subprocess.check_output(["git","show",base+":tests/solkey/expected.tsv"],cwd=root)
assert (root/"tests/solkey/expected.tsv").read_bytes()==raw,"expected rows changed from frozen base"
contracts={"TestSuite","SolcExpressions","SolcStructs","SolcArrays","SolcMemory","SolcMappings","SolcControlFlow"}
rows=[x.split("\t") for x in raw.decode().splitlines() if x.split("\t")[1] in contracts]
keys=[tuple(x[:3]) for x in rows]
assert len(set(keys))==len(keys),"duplicate original case"
summary=dict(base=base,expected_tsv_sha256=hashlib.sha256(raw).hexdigest(),scope_cases=len(rows),
 by_contract=dict(sorted(collections.Counter(x[1] for x in rows).items())),
 by_status=dict(sorted(collections.Counter(x[3] for x in rows).items())),
 scope_rows_sha256=hashlib.sha256(json.dumps(rows,separators=(",",":")).encode()).hexdigest())
out=pathlib.Path(sys.argv[1]); out.mkdir(parents=True,exist_ok=True)
(out/"case-inventory.json").write_text(json.dumps(dict(summary=summary,cases=rows),indent=2)+"\n")
(out/"case-summary.json").write_text(json.dumps(summary,indent=2)+"\n")
print(json.dumps(summary))
