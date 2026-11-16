#!/usr/bin/env python3
"""Regression: pinned blob reads work with all live source-file reads prohibited.
python3 docs/audits/direction-tools/mutation/check_base_sources.py
"""
import argparse,hashlib,json,subprocess,sys,tempfile
from pathlib import Path
from unittest.mock import patch
sys.dont_write_bytecode=True
from base_tree import BASE,ROOT,read_base_blobs
PATHS=["Solidity/Frontend/Admission/DeclarationOccurrences.lean","docs/feature-work/h62-3-g52-differential.md","tests/solkey/expected.tsv"]
def deny(*args,**kwargs):raise AssertionError("live filesystem source read attempted")
def main():
    ap=argparse.ArgumentParser();ap.add_argument("--audit-static",action="store_true");args=ap.parse_args()
    # These source paths may be absent or changed in the checkout: no filesystem
    # source read is permitted, while Git must still return exactly BASE bytes.
    with patch.object(Path,"read_text",deny),patch.object(Path,"read_bytes",deny):
        blobs=read_base_blobs(PATHS)
    assert set(blobs)==set(PATHS)
    for path,data in blobs.items():
        expected=subprocess.check_output(["git","show",BASE+":"+path],cwd=ROOT)
        assert data==expected,path
    integration="not requested"
    if args.audit_static:
        import audit
        scope=Path(__file__).resolve().parent
        original_text=Path.read_text;original_bytes=Path.read_bytes;original_exists=Path.exists
        def guard(method):
            def checked(path,*a,**k):
                resolved=path.resolve()
                if resolved.is_relative_to(ROOT) and not resolved.is_relative_to(scope):
                    raise AssertionError("live repository source access: "+str(path))
                return method(path,*a,**k)
            return checked
        with tempfile.TemporaryDirectory(prefix="mutation-pinned-static-") as tmp:
            output=Path(tmp)
            with patch.object(audit,"OUT",output),patch.object(sys,"argv",["audit.py"]),patch.object(Path,"read_text",guard(original_text)),patch.object(Path,"read_bytes",guard(original_bytes)),patch.object(Path,"exists",guard(original_exists)):
                audit.main()
            for name in ["inventory.json","mutants.json","constraints.json"]:
                assert json.loads((output/name).read_text())==json.loads((scope/name).read_text()),name
        integration="PASS: full static entry point with live repository reads/presence checks prohibited; outputs identical"
    print(json.dumps({"integration":integration,"base":BASE,"live_source_reads":"prohibited during regression","bindings":{path:{"sha256":hashlib.sha256(data).hexdigest(),"lines":len(data.splitlines())} for path,data in blobs.items()}},sort_keys=True))
if __name__=="__main__":main()
