"""Guard regression: fixture side effects or pending checks become implicit passes."""
import hashlib
import importlib.util
import pathlib
import tempfile
import unittest

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/fixture_effects.py"
spec = importlib.util.spec_from_file_location("fixture_effects", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class FixtureEffects(unittest.TestCase):
    def test_vt_driver_skip_and_generator_are_explicit(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            entries = []
            for relative in (module.VT + "IrParseChecks.lean", module.VT + "IrLeanGen.lean"):
                source = root / relative
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text("import Lean\n")
                entries.append({"path": relative, "sha256": hashlib.sha256(source.read_bytes()).hexdigest()})
            rows = module.classify(root, {"rows": entries})
            self.assertIn("VT1_SKIP_LEAN=1", rows[0]["driver_reference"])
            self.assertIn("writes fixture .term", rows[1]["side_effects"])

    def test_pending_and_generator_effects_are_explicit(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            entries = []
            for relative in (module.PRE + "StipendControl.lean", module.VT + "IrCensusGen.lean"):
                source = root / relative
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text("import Lean\n")
                entries.append({"path": relative, "sha256": hashlib.sha256(source.read_bytes()).hexdigest()})
            rows = module.classify(root, {"rows": entries})
            self.assertEqual("historically-unchecked-pending", rows[0]["role"])
            self.assertIn("writes fixtures/census-tree.txt", rows[1]["side_effects"])
            self.assertTrue(all(r["expected_outcome"] == "unresolved per current invocation" for r in rows))
            (root / entries[1]["path"]).write_text("changed")
            with self.assertRaises(ValueError):
                module.classify(root, {"rows": entries})


if __name__ == "__main__":
    unittest.main()
