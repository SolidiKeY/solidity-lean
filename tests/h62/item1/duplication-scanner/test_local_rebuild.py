"""Guard stale build reuse, forged completion, import shadowing and failed gates."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT=Path(__file__).resolve().parents[4]
spec=importlib.util.spec_from_file_location("local_binding",ROOT/"scripts/h62/item1/duplication-scanner/bind_signature_fixture.py")
binding=importlib.util.module_from_spec(spec);spec.loader.exec_module(binding)


class LocalRebuildControls(unittest.TestCase):
    def setUp(self):
        self.pins=json.loads(binding.PINS.read_text())
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)

    def test_real_pinned_sources_and_compiler(self):
        self.assertEqual(binding.check_inputs(self.pins),Path(self.pins["lean_path"]))

    def test_same_version_compiler_substitution_is_rejected(self):
        pins=copy.deepcopy(self.pins);pins["lean_sha256"]="0"*64
        with self.assertRaisesRegex(ValueError,"compiler binary"):
            binding.check_inputs(pins)

    def test_source_pin_drift_is_rejected(self):
        pins=copy.deepcopy(self.pins);pins["fixture_sources"]["SignatureFingerprint.lean"]="0"*64
        with self.assertRaisesRegex(ValueError,"source pin"):
            binding.check_inputs(pins)

    def fixture_copy(self):
        dest=self.root/"sources";dest.mkdir()
        for name in self.pins["fixture_sources"]:(dest/name).write_bytes((binding.FIXTURES/name).read_bytes())
        return dest

    def test_symlink_source_is_rejected_even_with_same_bytes(self):
        dest=self.fixture_copy();target=dest/"SignatureFingerprint.lean";target.unlink();target.symlink_to(binding.FIXTURES/target.name)
        with mock.patch.object(binding,"FIXTURES",dest),self.assertRaisesRegex(ValueError,"symlink"):
            binding.check_inputs(self.pins)

    def test_forbidden_indirect_source_import_rejected_before_execution(self):
        dest=self.fixture_copy();p=dest/"SignatureFingerprint.lean"
        p.write_text(p.read_text().replace("import Lean","import Lean\nimport Solidity.Backend.WorldCalls.Premises",1))
        pins=copy.deepcopy(self.pins);pins["fixture_sources"][p.name]=binding.sha(p)
        with mock.patch.object(binding,"FIXTURES",dest),self.assertRaisesRegex(ValueError,"forbidden transitive"):
            binding.check_inputs(pins)

    def test_stale_output_and_broken_symlink_are_rejected(self):
        p=self.root/"Old.olean";p.write_bytes(b"old")
        with self.assertRaisesRegex(ValueError,"stale"):binding.fresh_output(p)
        p.unlink();p.symlink_to("missing")
        with self.assertRaisesRegex(ValueError,"stale"):binding.fresh_output(p)

    def test_inherited_search_and_loader_injection_removed(self):
        with mock.patch.dict(os.environ,{"LEAN_PATH":"shadow","LEAN_SYSROOT":"shadow","LD_PRELOAD":"shadow","LD_LIBRARY_PATH":"shadow"}):
            env=binding.clean_environment(Path(self.pins["lean_path"]))
        self.assertNotIn("LEAN_PATH",env);self.assertNotIn("LEAN_SYSROOT",env)
        self.assertNotIn("LD_PRELOAD",env);self.assertNotIn("LD_LIBRARY_PATH",env)
        self.assertEqual(env["LEAN_NUM_THREADS"],"1")

    def test_failed_process_with_plausible_output_is_rejected(self):
        steps=[]
        with self.assertRaisesRegex(ValueError,"failed"):
            binding.checked_process([sys.executable,"-c","print('H62_SIGNATURE {}'); raise SystemExit(1)"],os.environ.copy(),self.root/"fail.log",steps)
        self.assertEqual(steps[0]["exit"],1)

    def test_timeout_cannot_be_a_successful_receipt(self):
        steps=[]
        with self.assertRaisesRegex(ValueError,"timed out"):
            binding.checked_process([sys.executable,"-c","import time;time.sleep(10)"],os.environ.copy(),self.root/"timeout.log",steps,timeout=0.1)
        self.assertTrue(steps[0]["timed_out"])
        self.assertNotEqual(steps[0]["exit"],0)

    def test_fresh_failed_run_never_promotes_a_consistent_old_packet(self):
        output=self.root/"run"
        with mock.patch.object(binding,"runtime_files",return_value=[]),mock.patch.object(binding,"compile_module",side_effect=ValueError("refused live build")):
            with self.assertRaisesRegex(ValueError,"refused live build"):binding.rebuild(output)
        receipt=json.loads((output/"receipt.json").read_text())
        self.assertEqual(receipt["status"],"failed");self.assertNotIn("records",receipt)
        with self.assertRaises(FileExistsError):binding.rebuild(output)

    def test_late_error_log_not_accepted_by_prefix_count(self):
        log=self.root/"late.log"
        log.write_text('H62_ENVIRONMENT {}\n'+(binding.FIXTURES/"signature-records.expected.jsonl").read_text()+'error: late failure\n')
        with self.assertRaisesRegex(ValueError,"unexpected observation"):
            binding.observer.read_log(log)

    def test_foreign_dependency_and_empty_closure_rejected(self):
        toolchain=Path(self.pins["lean_path"]).parent.parent
        foreign={"artifacts":[{"module":["str",["anonymous"],"Solidity"],"base":{"realpath":str(toolchain/"lib/lean/Solidity.olean")}}]}
        with self.assertRaisesRegex(ValueError,"forbidden"):binding.standard_closure(foreign,toolchain)
        with self.assertRaisesRegex(ValueError,"empty"):binding.standard_closure({"artifacts":[]},toolchain)

    def test_copy_time_mutation_stops_before_any_subprocess(self):
        output=self.root/"mutated-run"
        write=Path.write_bytes
        def altered(path,data):
            if path.name=="SignatureFingerprint.lean" and path.parent.name=="sources":data+=b"\n-- copy-time mutation\n"
            return write(path,data)
        with mock.patch.object(Path,"write_bytes",altered),mock.patch.object(binding,"runtime_files") as runtime,mock.patch.object(binding,"compile_module") as compiler:
            with self.assertRaisesRegex(ValueError,"staged source"):
                binding.rebuild(output)
        runtime.assert_not_called();compiler.assert_not_called()
        self.assertEqual(json.loads((output/"receipt.json").read_text())["status"],"failed")

    def test_available_minus_reserve_is_real_child_address_limit(self):
        gib=1024**3
        state={"memory_max":16*gib,"memory_current":11*gib,"host_available":5*gib,"swap_current":0}
        steps=[];log=self.root/"cap.log"
        with mock.patch.object(binding,"guard",return_value=state):
            binding.checked_process([sys.executable,"-c","import resource;print(resource.getrlimit(resource.RLIMIT_AS)[0])"],os.environ.copy(),log,steps)
        self.assertEqual(int(log.read_text()),gib)
        self.assertEqual(steps[0]["address_space_cap_bytes"],gib)

    def test_runtime_guard_change_kills_and_drains_owned_group(self):
        healthy=binding.guard();steps=[]
        with mock.patch.object(binding,"guard",side_effect=[healthy,ValueError("simulated reserve loss")]):
            with self.assertRaisesRegex(ValueError,"failed"):
                binding.checked_process([sys.executable,"-c","import time;time.sleep(10)"],os.environ.copy(),self.root/"guard.log",steps)
        self.assertIn("reserve loss",steps[0]["stop_reason"])
        self.assertEqual(steps[0]["live_owned_descendants"],0)

    def test_zero_exit_parent_cannot_leave_live_child_or_pass(self):
        steps=[]
        command=[sys.executable,"-c","import subprocess,sys;subprocess.Popen([sys.executable,'-c','import time;time.sleep(10)'])"]
        with self.assertRaisesRegex(ValueError,"failed"):
            binding.checked_process(command,os.environ.copy(),self.root/"descendant.log",steps)
        self.assertEqual(steps[0]["exit"],0)
        self.assertIn("descendants",steps[0]["stop_reason"])
        self.assertEqual(steps[0]["live_owned_descendants"],0)

    def test_ir_companion_change_and_new_sidecar_are_observed(self):
        base=self.root/"Lean.olean";base.write_bytes(b"olean")
        artifacts=[{"base":{"path":str(base)}}]
        before=binding.companion_artifacts(artifacts)
        ir=self.root/"Lean.ir";ir.write_bytes(b"IR")
        added=binding.companion_artifacts(artifacts)
        self.assertNotEqual(before,added)
        ir.write_bytes(b"changed IR")
        self.assertNotEqual(added,binding.companion_artifacts(artifacts))
        native=self.root/"Lean.so";native.symlink_to(ir)
        with self.assertRaisesRegex(ValueError,"symlink"):
            binding.companion_artifacts(artifacts)

    def test_coverage_retains_unbound_same_spelling_and_rejected_rows(self):
        rows=[{"path":"A.lean","line":1,"name":"same","kind":"theorem","reject_reason":None,"fixture_signature":{}},
              {"path":"B.lean","line":1,"name":"same","kind":"theorem","reject_reason":None},
              {"path":"A.lean","line":9,"name":"unsupported","kind":"def","reject_reason":"missing-top-level-definition"}]
        report=binding.scanner.signature_coverage(rows)
        self.assertEqual(report["counts"],{"local-fixture-linkage":1,"unresolved":2})
        self.assertEqual([(r["path"],r["line"],r["status"]) for r in report["rows"]],
                         [("A.lean",1,"local-fixture-linkage"),("B.lean",1,"unresolved"),("A.lean",9,"unresolved")])
        self.assertEqual(report["rows"][-1]["lexical_reject_reason"],"missing-top-level-definition")
        self.assertFalse(report["complete_signature_coverage"])
        self.assertFalse(report["ownership_verified"])

    def test_empty_scope_cannot_claim_complete_signature_coverage(self):
        self.assertFalse(binding.scanner.signature_coverage([])["complete_signature_coverage"])

    def scan(self,root,pattern,output):
        return subprocess.run([sys.executable,"-B",str(ROOT/"scripts/h62/item1/duplication-scanner/scan.py"),str(root),pattern,"--fixture-binding-output",str(output)],capture_output=True,timeout=10)

    def test_scanner_gate_rejects_foreign_root(self):
        result=self.scan(self.root,"*.lean",self.root/"new-output")
        self.assertNotEqual(result.returncode,0)
        self.assertIn(b"real checkout",result.stderr)
        self.assertFalse((self.root/"new-output").exists())

    def test_scanner_gate_rejects_scope_without_supported_five_records(self):
        output=self.root/"new-output"
        result=self.scan(ROOT,"tests/h62/item1/duplication-scanner/SignatureEnvironment.lean",output)
        self.assertNotEqual(result.returncode,0)
        self.assertIn(b"five fixture declarations",result.stderr)
        self.assertFalse(output.exists())

    def test_scanner_gate_never_accepts_replayed_success_packet(self):
        output=self.root/"old-output";output.mkdir()
        (output/"receipt.json").write_text('{"status":"pass","records":[]}')
        result=self.scan(ROOT,"tests/h62/item1/duplication-scanner/SignatureFingerprint.lean",output)
        self.assertNotEqual(result.returncode,0)
        self.assertIn(b"saved receipts are not accepted",result.stderr)


if __name__=="__main__":unittest.main()
