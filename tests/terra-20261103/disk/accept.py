#!/usr/bin/env python3
# Frozen coordinator contract. Do not edit or weaken.
import hashlib, importlib.util, json, os, pathlib, subprocess, sys, unittest
ROOT = pathlib.Path(subprocess.check_output(["git","rev-parse","--show-toplevel"],text=True).strip())
HERE = pathlib.Path(__file__).resolve().parent
CONTRACT = {'id': 'TF-disk', 'source': 'scripts/coord-tools/disk.sh', 'sha256': '312f186ae07e0ad0bdd27ccb3743077b78b0ebf243954269e7c56bf3ce8bd3e5', 'cases': ['report_only', 'missing_cgroup', 'real_worktree_build', 'symlink_lake_preserved', 'symlink_build_preserved', 'main_build_preserved', 'extra_seal_file_preserved', 'invalid_checksum_preserved', 'git_directory_preserved', 'newest_seal_preserved', 'older_valid_seal_removed', 'exited_containers_only', 'invalid_usage'], 'output': 'tests/terra-20261103/disk'}
def main():
    target=ROOT/CONTRACT["source"]
    assert hashlib.sha256(target.read_bytes()).hexdigest()==CONTRACT["sha256"], "source drift: review a new snapshot, never edit production tools"
    required={str(HERE.relative_to(ROOT)/name) for name in ["accept.py","test_cases.py","README.md"]}
    assert {str(p.relative_to(ROOT)) for p in HERE.rglob("*") if p.is_file() and "__pycache__" not in p.parts}==required, "all artifact paths must be covered"
    for p in required: assert (ROOT/p).stat().st_size>40, p
    if len(sys.argv)>1:
        commit=sys.argv[1]
        changed=set(subprocess.check_output(["git","diff-tree","--no-commit-id","--name-only","-r",commit],text=True).splitlines())
        assert changed==required, ("one item per commit; unexpected/missing paths",changed^required)
        assert subprocess.check_output(["git","show",commit+":"+str(HERE.relative_to(ROOT)/"accept.py")])==pathlib.Path(__file__).read_bytes(), "acceptance changed after commit"
    spec=importlib.util.spec_from_file_location("terra_item",HERE/"test_cases.py")
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    suite=unittest.defaultTestLoader.loadTestsFromModule(mod)
    def flatten(s):
        for t in s:
            if isinstance(t,unittest.TestSuite): yield from flatten(t)
            else: yield t
    tests=list(flatten(suite)); names=[t.id().rsplit(".",1)[-1] for t in tests]
    expected=["test_"+s for s in CONTRACT["cases"]]
    assert sorted(names)==sorted(expected), ("every case exactly once",names,expected)
    result=unittest.TextTestRunner(verbosity=2).run(unittest.TestSuite(tests))
    assert result.testsRun==len(expected) and not result.skipped and not result.expectedFailures and not result.unexpectedSuccesses
    assert result.wasSuccessful(), "fixture failure: report a production defect, never bless it"
    print(json.dumps({"item":CONTRACT["id"],"cases":names,"count":result.testsRun,"status":"PASS"}))
if __name__=="__main__":main()
