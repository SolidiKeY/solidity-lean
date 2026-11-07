"""Adversarial metadata controls; these are not Lean or compiler proof gates."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("premise_tools", ROOT / "scripts/h55/g49-final-theorem/premise-tools.py")
tool = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tool)


class PremiseControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inventory = tool.read_inventory(Path("/workspace/h55-g49-evidence/pass-chain-final/premise-inventory.log").read_text())
        cls.policy = tool.decode(tool.POLICY.read_bytes())
        cls.owners = tool.decode(Path("/workspace/h55-ownership-after.json").read_bytes())
        cls.manifest = tool.decode(tool.MANIFEST.read_bytes())
        cls.archive = Path("/workspace/h55-staging-e59348224.tar").read_bytes()

    def test_actual_telescope_and_data_premises(self):
        report = tool.account(self.inventory, self.policy, self.owners)
        self.assertEqual((report["totalBinders"], report["openProducerPremises"],
                          report["callerProofConditions"], report["quantifiedParameters"]), (14, 4, 3, 7))
        rows = {r["name"]: r for r in report["premises"]}
        self.assertFalse(rows["backend"]["isProp"])
        self.assertEqual(rows["backend"]["role"], "producer")
        self.assertEqual(rows["backend"]["owner"], "solidity-h55-sol-20261106/g49-final-theorem")
        self.assertEqual(rows["lowering"]["owner"], "V16 (v12-v17/v16-correctness-transfer)")
        self.assertFalse(report["finalPublicTheoremComplete"])

    def test_reject_statement_premise_and_owner_corruptions(self):
        def missing_owner(o):
            o["items"] = [r for r in o["items"] if r["id"] != "P8b"]
        def empty_owner(o):
            next(r for r in o["items"] if r["id"] == "P8b")["owner"] = ""
        changes = [
            ("missing data certificate", lambda i,p,o:i["premises"].pop(4)),
            ("new assumed desired result", lambda i,p,o:i["premises"].append(i["premises"][-1])),
            ("erased output observations", lambda i,p,o:i.update(type="True")),
            ("changed dependent type", lambda i,p,o:i["premises"][11].update(closedExpr="True")),
            ("false readable type", lambda i,p,o:i["premises"][4].update(type="True")),
            ("false type constants", lambda i,p,o:i["premises"][4].update(constants=[])),
            ("hidden row status", lambda i,p,o:i["premises"][4].update(discharged=True)),
            ("wrong declaration", lambda i,p,o:i.update(name="different")),
            ("hidden axiom", lambda i,p,o:i["axioms"].append("sorryAx")),
            ("hidden dependency", lambda i,p,o:i["dependencies"].append("Solidity.Roadmap.PublicCorrectness")),
            ("binder reorder", lambda i,p,o:i["premises"].reverse()),
            ("unknown role", lambda i,p,o:p["bindings"][4].update(role="proved")),
            ("typed certificate hidden", lambda i,p,o:p["bindings"][4].update(role="parameter",obligation=None)),
            ("Prop hidden", lambda i,p,o:p["bindings"][8].update(role="parameter",obligation=None)),
            ("Prop flag hidden", lambda i,p,o:i["premises"][8].update(isProp=False)),
            ("unknown obligation", lambda i,p,o:p["bindings"][4].update(obligation="UNKNOWN")),
            ("missing owner", lambda i,p,o:missing_owner(o)),
            ("empty owner", lambda i,p,o:empty_owner(o)),
            ("duplicate owner ID", lambda i,p,o:o["items"].append(o["items"][0]))]
        for label, mutate in changes:
            with self.subTest(label=label):
                inventory, policy, owners = copy.deepcopy((self.inventory,self.policy,self.owners))
                mutate(inventory,policy,owners)
                with self.assertRaises(tool.Invalid):
                    tool.account(inventory,policy,owners)

    def test_original_archive_regenerates_exact_bulk_bytes(self):
        data = tool.payload_bytes(self.archive, self.manifest)
        self.assertEqual(tool.digest(data), self.manifest["files"][tool.PAYLOAD])
        self.assertEqual(data, Path("/workspace/h55-staging-e59348224/tests/roadmap-v16/parallel-premises.json").read_bytes())

    def test_archive_and_member_corruptions(self):
        with self.assertRaises(tool.Invalid):
            tool.payload_bytes(self.archive[:-1]+bytes([self.archive[-1]^1]), self.manifest)
        manifest = copy.deepcopy(self.manifest)
        manifest["files"][tool.PAYLOAD] = "0"*64
        with self.assertRaises(tool.Invalid):
            tool.payload_bytes(self.archive, manifest)
        manifest["files"].pop(tool.PAYLOAD)
        with self.assertRaises(tool.Invalid):
            tool.payload_bytes(self.archive, manifest)

    def test_no_bulk_in_git_and_no_clobber(self):
        with self.assertRaises(tool.Invalid):
            tool.external_write(ROOT/"tests/roadmap-v16/parallel-premises.json", b"x")
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp)/"policy.json"
            target.write_bytes(b"original")
            with self.assertRaises(tool.Invalid):
                tool.external_write(target, b"changed")
            self.assertEqual(target.read_bytes(), b"original")

    def test_gate_evidence_cannot_be_reused(self):
        spec = importlib.util.spec_from_file_location("gate_runner", ROOT / "scripts/h55/g49-final-theorem/check-pass-chain.py")
        runner = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(runner)
        with tempfile.TemporaryDirectory() as tmp:
            evidence = Path(tmp)/"run"
            runner.prepare_evidence(evidence)
            self.assertEqual(json.loads((evidence/"run-status.json").read_text()), {"status":"pending"})
            old = evidence/"results.json"
            old.write_bytes(b"previous results")
            with self.assertRaises(FileExistsError):
                runner.prepare_evidence(evidence)
            self.assertEqual(old.read_bytes(), b"previous results")

    def test_ambiguous_or_duplicate_inventory_rejected(self):
        with self.assertRaises(tool.Invalid):
            tool.decode("{\"a\":1,\"a\":2}")
        with self.assertRaises(tool.Invalid):
            tool.read_inventory("")
        log = "G49-PREMISES "+json.dumps(self.inventory)+"\n"
        with self.assertRaises(tool.Invalid):
            tool.read_inventory(log+log)


if __name__ == "__main__":
    unittest.main(verbosity=2)
