#!/usr/bin/env python3
# Frozen coordinator static audit contract. This is not Lean verification.
import hashlib,json,pathlib,re,subprocess,sys
ROOT=pathlib.Path(subprocess.check_output(["git","rev-parse","--show-toplevel"],text=True).strip())
HERE=pathlib.Path(__file__).resolve().parent
CONTRACT={'id': 'NV-Selection', 'base': 'b6ba0696102a7a038afe2ed333c09dff397cc5b2', 'prefix': 'Solidity/Backend/Selection', 'files': {'Solidity/Backend/Selection/FrameCapacityV2.lean': {'sha256': 'da93c8332c310dfa451fa646c24216ec8b2d87df8145215197e0c8e2c4d5d330'}, 'Solidity/Backend/Selection/Interface.lean': {'sha256': '07faf4434d6ef93a5cbcdc2c317a58b8773f32d0c89231e6479d387655b36250'}, 'Solidity/Backend/Selection/InterfaceV2.lean': {'sha256': '0c4d31640864ac6e9a4f16765d03e03298ed3699f6e70ca67713bfbb02b360e4'}, 'Solidity/Backend/Selection/InterfaceV2Controls.lean': {'sha256': 'c1eed9cda5b87d21539c9423526def3698e00112884cb34b54a70d2a761355a5'}, 'Solidity/Backend/Selection/Premises.lean': {'sha256': '95e3ac7e486a8749fab1383b2ad503bef93d4d18153740789ce33c6137f6921f'}, 'Solidity/Backend/Selection/PremisesV2.lean': {'sha256': 'fe5eacf6561b9c9e5b899338083281eafa8106b8b546fbccdd166b740734fc76'}}, 'scan_regex': '^\\s*(?:(?:private|protected|noncomputable|partial|unsafe)\\s+)*(?:def|abbrev|theorem|lemma|opaque|axiom|structure|class|inductive|instance)\\b|^\\s*[A-Za-z_][A-Za-z0-9_\\u0027]*\\s*(?:\\([^\\n]*\\)|\\{[^\\n]*\\}|\\[[^\\n]*\\])*\\s*:', 'dimensions': ['inhabited_domain', 'nonempty_execution', 'nontrivial_observation', 'capacity_or_identity', 'premise_provenance', 'positive_and_negative_controls'], 'output': 'tests/terra-20261103/audit-selection'}
def main():
    required={str(HERE.relative_to(ROOT)/n) for n in ["accept.py","audit.json","README.md"]}
    actual={str(p.relative_to(ROOT)) for p in HERE.rglob("*") if p.is_file() and "__pycache__" not in p.parts}
    assert actual==required, ("all output paths",actual^required)
    if len(sys.argv)>1:
        commit=sys.argv[1]
        changed=set(subprocess.check_output(["git","diff-tree","--no-commit-id","--name-only","-r",commit],text=True).splitlines())
        assert changed==required, ("one item per commit",changed^required)
        assert subprocess.check_output(["git","show",commit+":"+str(HERE.relative_to(ROOT)/"accept.py")])==pathlib.Path(__file__).read_bytes()
    paths=sorted(str(p.relative_to(ROOT)) for p in (ROOT/CONTRACT["prefix"]).rglob("*.lean"))
    assert paths==sorted(CONTRACT["files"]), "input inventory drift: stop for coordinator re-pin"
    data=json.loads((HERE/"audit.json").read_text())
    assert data["base"]==CONTRACT["base"] and data["boundary"]=="static review only; no kernel verification"
    rows=data["files"]; assert len(rows)==len(paths) and {r["path"] for r in rows}==set(paths)
    count=0
    for row in rows:
        path=row["path"]; raw=(ROOT/path).read_bytes(); want=CONTRACT["files"][path]
        assert hashlib.sha256(raw).hexdigest()==want["sha256"]==row["sha256"],path
        lines=raw.decode().splitlines(); expected=[i for i,l in enumerate(lines,1) if re.search(CONTRACT["scan_regex"],l)]
        entries=row["entries"]; assert len(entries)==len(expected) and sorted(e["line"] for e in entries)==expected,path
        for e in entries:
            assert e["text"]==lines[e["line"]-1]
            assert e["assessment"] in ["risk","witness-present","not-a-contract","unresolved"]
            assert isinstance(e["explanation"],str) and len(e["explanation"].strip())>=40
            assert e["evidence"] and all(isinstance(n,int) and 1<=n<=len(lines) for n in e["evidence"])
            count+=1
        dimensions=row["dimensions"]
        assert set(dimensions)==set(CONTRACT["dimensions"]),path
        for v in dimensions.values():
            assert v["status"] in ["risk","witness-present","not-applicable","unresolved"]
            assert len(v["explanation"].strip())>=40 and v["lines"] and all(isinstance(n,int) and 1<=n<=len(lines) for n in v["lines"])
    assert len((HERE/"README.md").read_text().strip())>=200
    print(json.dumps({"item":CONTRACT["id"],"files":len(rows),"entries":count,"status":"PASS","boundary":data["boundary"]}))
if __name__=="__main__":main()
