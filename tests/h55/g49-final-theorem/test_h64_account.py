"""Accounting integrity controls, separate from the checked Lean proofs."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
SPEC = importlib.util.spec_from_file_location("h64_account", ROOT/"scripts/h55/g49-final-theorem/h64-account.py")
tool = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(tool)
RUN = Path(os.environ.get("H64_CHECK_RUN", "/workspace/h64-g49-evidence/folded-final"))


class H64AccountingControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inventory, _ = tool.load_inventory(RUN)
        cls.registry = tool.decode(tool.REGISTRY.read_bytes())
        cls.ownership = tool.decode(Path("/workspace/h55-ownership-after.json").read_bytes())

    def test_actual_obligations_and_single_implementation(self):
        result = tool.account(self.inventory,self.registry,self.ownership)
        self.assertEqual((result["publicObligationFields"], result["fullCertificatePackages"],
                          result["implementationParameters"], result["interfaceParameters"]), (15,3,2,4))
        self.assertEqual((result["implementedSemanticShapes"],result["carrierAdapterEntrypoints"]),(1,5))
        self.assertFalse(result["exhaustiveLaneCoverage"])
        self.assertTrue(all(r["owner"] and not r["discharged"] for r in result["premises"]))

    def test_reject_premise_adapter_and_owner_corruptions(self):
        def ctor(i):
            return next(r for r in i["declarations"] if r["name"].endswith("PublicObligations.mk"))["binders"]
        def remove_owner(o):
            o["items"] = [r for r in o["items"] if r["id"] != "P8b"]
        def swap_supported(r):
            r["families"][0]["supported"] = False
            r["families"][-1]["supported"] = True
        mutations = [
            ("missing public premise",lambda i,r,o:ctor(i).pop()),
            ("hidden Prop",lambda i,r,o:ctor(i)[9].update(isProp=False)),
            ("wrong named type owner",lambda i,r,o:ctor(i)[9].update(name="keccak")),
            ("new axiom",lambda i,r,o:i["declarations"][0]["axioms"].append("sorryAx")),
            ("missing endpoint theorem",lambda i,r,o:i["declarations"].pop()),
            ("duplicate declaration",lambda i,r,o:i["declarations"].append(i["declarations"][0])),
            ("duplicate adapter",lambda i,r,o:r["carrierAdapters"].append(r["carrierAdapters"][0])),
            ("missing adapter",lambda i,r,o:r["carrierAdapters"].pop()),
            ("bypassed common adapter",lambda i,r,o:next(x for x in i["declarations"] if x["name"].endswith("compilation_adapter")).update(dependencies=[])),
            ("false full coverage",lambda i,r,o:r.update(exhaustiveLaneCoverage=True)),
            ("false shape fit",lambda i,r,o:r["families"][1].update(supported=True)),
            ("swap supported identity",lambda i,r,o:swap_supported(r)),
            ("unknown obligation owner",lambda i,r,o:r["owners"].update(lowering="UNKNOWN")),
            ("missing owner",lambda i,r,o:remove_owner(o)),
            ("duplicate owner",lambda i,r,o:o["items"].append(o["items"][0]))]
        for label, mutate in mutations:
            with self.subTest(label=label):
                inventory, registry, ownership = copy.deepcopy((self.inventory,self.registry,self.ownership))
                mutate(inventory,registry,ownership)
                with self.assertRaises(tool.BASE.Invalid):
                    tool.account(inventory,registry,ownership)

    def test_tampered_readable_inventory_log_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            rows = tool.decode((RUN/"results.json").read_bytes())
            log = directory/"controls.log"
            log.write_bytes(Path(rows[-1]["log"]).read_bytes())
            rows[-1]["log"] = str(log)
            data = (json.dumps(rows)+"\n").encode()
            (directory/"results.json").write_bytes(data)
            (directory/"run-status.json").write_text(json.dumps(dict(status="pass",resultsSha256=tool.digest(data))))
            tool.load_inventory(directory)
            log.write_text(log.read_text().replace("S.Approved", "True"))
            with self.assertRaises(tool.BASE.Invalid):
                tool.load_inventory(directory)

    def test_stale_or_failed_run_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            data = (RUN/"results.json").read_bytes()
            (directory/"results.json").write_bytes(data)
            (directory/"run-status.json").write_text(json.dumps(dict(status="pending",resultsSha256=tool.digest(data))))
            with self.assertRaises(tool.BASE.Invalid):
                tool.load_inventory(directory)
            (directory/"run-status.json").write_text(json.dumps(dict(status="pass",resultsSha256="0"*64)))
            with self.assertRaises(tool.BASE.Invalid):
                tool.load_inventory(directory)


if __name__ == "__main__":
    unittest.main(verbosity=2)
