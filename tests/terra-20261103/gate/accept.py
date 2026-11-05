#!/usr/bin/env python3
# Frozen coordinator contract. Do not edit or weaken.
import hashlib, importlib.util, json, os, pathlib, subprocess, sys, unittest
ROOT = pathlib.Path(subprocess.check_output(["git","rev-parse","--show-toplevel"],text=True).strip())
HERE = pathlib.Path(__file__).resolve().parent
CONTRACT = {'id': 'TF-gate', 'source': 'scripts/coord-tools/gate.sh', 'sha256': '11a0f2ac693d9fb0a55fbb7064902b01ddfa60664eb5839426cb4dd268bf2a15', 'cases': ['usage', 'per_file_relative_paths', 'relative_logs', 'head_stamp', 'changed_module', 'reverse_import_closure', 'deleted_module_importers', 'renamed_module_importers', 'diverged_base_merge_base', 'root_module', 'untracked_module', 'scratch_excluded', 'failure_exit', 'checkpoint_all_gates', 'full_extra_gates'], 'output': 'tests/terra-20261103/gate'}
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
