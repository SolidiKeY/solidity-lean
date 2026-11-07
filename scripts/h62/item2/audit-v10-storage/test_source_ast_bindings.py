"""Identity-loss mutations of the existing LibraryTry inputs, not new cases."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location("bindings", Path(__file__).with_name("source_ast_bindings.py"))
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


class SourceBindingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.legacy = json.loads((m.ROOT / "tests/solc/LibraryTry.ast.json").read_text())
        cls.ir = json.loads((m.ROOT / "tests/solc/LibraryTryIR.ast.json").read_text())

    def test_existing_binding_requirements(self):
        report = m.pair(self.legacy, self.ir)
        functions = {(f["owner"], f["name"]): f for f in report["legacy"]["functions"]}
        self.assertEqual(set(functions), {("L", "integer"), ("L", "stru"), ("C", "f"), ("C", "g")})
        formal = functions[("L", "stru")]["parameters"][0]
        self.assertEqual((formal["type"], formal["storage_location"]), ("struct L.S", "storage"))
        for name in ["f", "g"]:
            self.assertEqual([(x["type"], x["storage_location"]) for x in functions[("C", name)]["returns"]],
                             [("uint256", "default"), ("string", "memory")])
        calls = [c for c in report["legacy"]["calls"] if c["target_ast_id"] == functions[("L", "stru")]["ast_id"]]
        root = next(d for d in report["legacy"]["declarations"] if d["owner_contract"] == "C" and d["state_variable"] is True)
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0]["receiver_ast_id"], root["ast_id"])

    def test_alias_and_string_drift_rejected(self):
        for field in ["storage", "string"]:
            with self.subTest(field=field):
                candidate = copy.deepcopy(self.ir)
                contracts = {c["name"]: c for c in candidate["ast"]["nodes"] if c.get("nodeType") == "ContractDefinition"}
                if field == "storage":
                    fn = next(f for f in contracts["L"]["nodes"] if f.get("name") == "stru")
                    fn["parameters"]["parameters"][0]["storageLocation"] = "memory"
                else:
                    fn = next(f for f in contracts["C"]["nodes"] if f.get("name") == "g")
                    fn["returnParameters"]["parameters"][1]["typeDescriptions"]["typeString"] = "bytes"
                with self.assertRaises(ValueError):
                    m.pair(self.legacy, candidate)

    def test_duplicate_identity_rejected(self):
        candidate = copy.deepcopy(self.legacy)
        candidate["ast"]["nodes"][0]["id"] = candidate["ast"]["id"]
        with self.assertRaises(ValueError):
            m.inspect(candidate)

    def test_missing_provenance_rejected(self):
        first, second = copy.deepcopy(self.legacy), copy.deepcopy(self.ir)
        del first["header"]["sourceSha256"]
        del second["header"]["sourceSha256"]
        with self.assertRaises(ValueError):
            m.pair(first, second)

    def test_pipeline_and_compiler_drift_rejected(self):
        for field in ["pipeline", "compiler"]:
            candidate = copy.deepcopy(self.ir)
            if field == "pipeline":
                candidate["header"]["settings"]["viaIR"] = False
            else:
                candidate["header"]["compilerSha256"] = "0" * 64
            with self.assertRaises(ValueError):
                m.pair(self.legacy, candidate)


if __name__ == "__main__":
    unittest.main()
