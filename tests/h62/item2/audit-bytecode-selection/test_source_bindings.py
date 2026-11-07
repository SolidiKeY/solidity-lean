"""Guard regression: changed source/product receipts must not inherit prefix success.

Products below are synthetic bytes, not Lean artifacts or process attestations.
"""
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "scripts/h62/item2/audit-bytecode-selection"))
import source_bindings as link


class SourceBindingTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo, self.evidence = self.root / "repo", self.root / "evidence"
        self.repo.mkdir(); self.evidence.mkdir()
        self.sources = {"Solidity/Dep.lean": b"def dep := 1\n",
                        "Solidity/Root.lean": b"import Solidity.Dep\ndef root := dep\n"}
        for name, raw in self.sources.items():
            p = self.repo / name; p.parent.mkdir(exist_ok=True); p.write_bytes(raw)
        self.roots = ["Solidity/Root.lean"]
        self.order = list(self.sources)
        self.hashes = {p: hashlib.sha256(v).hexdigest() for p, v in self.sources.items()}
        self.write("closure-plan.json", {"frozen_base": link.BASE, "roots": self.roots,
                   "root_count": 1, "source_closure_count": 2, "order": self.order,
                   "source_sha256": self.hashes})
        self.write("workload-result.json", {"status": "red", "exit": -15, "workload_id": "a" * 64})
        (self.evidence / "workload.id").write_text("a" * 64 + "\n")
        (self.evidence / "container.exit").write_text("1\n")
        self.rows = []
        for i, name in enumerate(self.order):
            product = self.evidence / "source-check/lean" / Path(name).with_suffix(".olean")
            product.parent.mkdir(parents=True, exist_ok=True); product.write_bytes(b"synthetic " + name.encode())
            log = self.evidence / ("source-check/" + str(i).zfill(3) + "-" + Path(name).stem + ".log")
            log.write_text("fixture only\n")
            self.rows.append({"path": name, "command": [link.LEAN, "-j1", "-M8192", "--tstack=131072",
                              "-o", str(product), name], "exit": 0, "stop": None, "seconds": 1.0,
                              "source_unchanged_during_check": True, "source_sha256": self.hashes[name],
                              "output_sha256": hashlib.sha256(product.read_bytes()).hexdigest(), "log": str(log)})
        self.write("source-check/verification.json", self.rows[:1])
        def git_show(cmd, cwd):
            self.assertEqual(cmd[:2], ["git", "show"])
            self.assertEqual(cwd, self.repo)
            return self.sources[cmd[2].split(":", 1)[1]]
        self.mock = patch.object(link.subprocess, "check_output", side_effect=git_show)
        self.mock.start(); self.addCleanup(self.mock.stop)

    def write(self, name, data):
        p = self.evidence / name; p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(data))

    def bind(self):
        return link.bind_records(self.repo, self.evidence, self.roots)

    def test_red_prefix_retained_with_no_acceptance(self):
        result = self.bind()
        self.assertEqual(result["summary"]["bound_saved_records"], 1)
        self.assertEqual(result["pending_planned_sources"], ["Solidity/Root.lean"])
        self.assertEqual(result["terminal_workload_status"], "red")
        self.assertFalse(result["summary"]["inspection_accepted"])
        self.assertEqual(result["summary"]["witnesses_established"], 0)

    def test_all_records_still_do_not_accept_inspection(self):
        self.write("source-check/verification.json", self.rows)
        result = self.bind()
        self.assertEqual(result["summary"]["pending_sources"], 0)
        self.assertFalse(result["summary"]["inspection_accepted"])
        self.assertEqual(result["terminal_workload_status"], "red")

    def test_changed_source_product_and_symlink_refused(self):
        source = self.repo / self.order[0]
        source.write_text("def dep := 2\n")
        with self.assertRaises(ValueError): self.bind()
        source.write_bytes(self.sources[self.order[0]])
        product = Path(self.rows[0]["command"][-2])
        product.write_bytes(b"changed")
        with self.assertRaises(ValueError): self.bind()
        product.unlink(); product.symlink_to(source)
        with self.assertRaises(ValueError): self.bind()

    def test_missing_terminal_and_disagreement_refused(self):
        (self.evidence / "container.exit").unlink()
        with self.assertRaises(ValueError): self.bind()
        (self.evidence / "container.exit").write_text("0\n")
        with self.assertRaises(ValueError): self.bind()

    def test_order_commands_budget_and_record_mutations_refused(self):
        variants = []
        for field, value in [("seconds", True), ("seconds", 301), ("seconds", float("nan")),
                             ("exit", False), ("stop", "timeout"), ("source_unchanged_during_check", False)]:
            row = copy.deepcopy(self.rows[0]); row[field] = value; variants.append([row])
        row = copy.deepcopy(self.rows[0]); row["command"][1] = "-j2"; variants.append([row])
        variants += [list(reversed(self.rows)), [self.rows[0], self.rows[0]], []]
        for rows in variants:
            with self.subTest(rows=rows):
                self.write("source-check/verification.json", rows)
                with self.assertRaises(ValueError): self.bind()

    def test_self_rehashed_plan_cannot_replace_frozen_sources(self):
        plan = json.loads((self.evidence / "closure-plan.json").read_text())
        plan["source_sha256"][self.order[0]] = "0" * 64
        self.write("closure-plan.json", plan)
        with self.assertRaises(ValueError): self.bind()

    def test_terminal_exit_identity_and_incomplete_pass_refused(self):
        for status, exitcode, identity in [("pass", -15, "a"*64), ("pass", False, "a"*64),
                                          ("red", -15, "not-a-container"), ("pass", 0, "a"*64)]:
            self.write("workload-result.json", {"status": status, "exit": exitcode, "workload_id": identity})
            (self.evidence / "container.exit").write_text("0" if status == "pass" else "1")
            with self.subTest(status=status, exitcode=exitcode, identity=identity):
                with self.assertRaises(ValueError): self.bind()

    def test_receipt_snapshot_changes_refused(self):
        original=link.file_digest
        def changed(path, advise=False):
            result=original(path, advise=advise)
            self.write("workload-result.json", {"status":"red","exit":-9,"workload_id":"a"*64})
            return result
        with patch.object(link, "file_digest", side_effect=changed):
            with self.assertRaises(ValueError): self.bind()

    def test_misspelled_external_root_refused(self):
        self.sources[self.order[0]] = b"import LeanEvil.Dependency\n"
        (self.repo / self.order[0]).write_bytes(self.sources[self.order[0]])
        with self.assertRaises(ValueError): self.bind()

    def test_dependency_cycle_and_unknown_import_refused(self):
        self.sources[self.order[0]] = b"import Solidity.Root\n"
        (self.repo / self.order[0]).write_bytes(self.sources[self.order[0]])
        with self.assertRaises(ValueError): self.bind()
        self.sources[self.order[0]] = b"import Missing.Dependency\n"
        (self.repo / self.order[0]).write_bytes(self.sources[self.order[0]])
        with self.assertRaises(ValueError): self.bind()

    def test_static_private_and_inherited_candidates_never_gain_kernel_status(self):
        self.sources[self.order[0]] = b"structure Parent where\n  proof : True\nprivate theorem hidden : True := True.intro\n"
        self.sources[self.order[1]] = b"import Solidity.Dep\nstructure Child extends Parent where\n  value : Nat\n"
        for path, raw in self.sources.items(): (self.repo/path).write_bytes(raw)
        binding={"path":self.order[0],"source_sha256":hashlib.sha256(self.sources[self.order[0]]).hexdigest(),
                 "output_sha256":"b"*64}
        result=link.classify_inputs(self.repo,self.order,[binding])
        self.assertEqual(result["summary"]["private_candidates"],1)
        self.assertEqual(result["summary"]["source_parent_edges"],1)
        self.assertEqual(result["summary"]["mapped_files_with_saved_product"],1)
        self.assertEqual(result["summary"]["kernel_links_accepted"],0)
        self.assertIsNone(result["private_candidates"][0]["observed_kernel_name"])
        self.assertTrue(all(not s["kernel_identity_verified"] for s in result["structure_candidates"]))
        self.assertTrue(all(g["kernel_obligations_verified"]==0 for g in result["inherited_candidates"]))

    def test_static_binding_mismatch_and_duplicate_inputs_refused(self):
        binding={"path":self.order[0],"source_sha256":"0"*64,"output_sha256":"a"*64}
        with self.assertRaises(ValueError):link.classify_inputs(self.repo,self.order,[binding])
        with self.assertRaises(ValueError):link.classify_inputs(self.repo,self.order,[binding,binding])
        with self.assertRaises(ValueError):link.classify_inputs(self.repo,[self.order[0],self.order[0]],[])

    def test_cli_records_all_imported_tool_hashes(self):
        import contextlib, io
        output=self.root/"cli-report.json"
        argv=["source_bindings.py","--repo",str(self.repo),"--evidence",str(self.evidence),"--output",str(output)]
        with patch.object(sys,"argv",argv), patch.object(link,"mapped_paths",return_value=(self.roots,1)):
            with contextlib.redirect_stdout(io.StringIO()):link.main()
        report=json.loads(output.read_text())
        self.assertEqual(len(report["tool_sources_sha256"]),5)
        self.assertTrue(all(len(h)==64 for h in report["tool_sources_sha256"].values()))
        self.assertFalse(report["summary"]["inspection_accepted"])

    def test_cli_refuses_imported_helper_hash_change(self):
        helper=Path(link.linkage_manifest.__file__).resolve()
        original=link.file_digest;seen=0
        def changed(path,advise=False):
            nonlocal seen
            value=original(path,advise=advise)
            if Path(path).resolve()==helper:
                seen+=1
                if seen==2:return "0"*64
            return value
        output=self.root/"changed-report.json"
        argv=["source_bindings.py","--repo",str(self.repo),"--evidence",str(self.evidence),"--output",str(output)]
        with patch.object(sys,"argv",argv), patch.object(link,"mapped_paths",return_value=(self.roots,1)):
            with patch.object(link,"file_digest",side_effect=changed):
                with self.assertRaises(ValueError):link.main()
        self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
