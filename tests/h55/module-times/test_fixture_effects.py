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

    def test_graph_census_and_readonly_overlay_remain_unresolved(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            paths = (module.GRAPH + "Census.lean", module.BIND + "overlay/Solidity/Lowering/Readonly/CapturePhases.lean",
                     module.ROADMAP + "WitnessObstruction.lean")
            entries = []
            for relative in paths:
                source = root / relative
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text("import Lean\n")
                entries.append({"path": relative, "sha256": hashlib.sha256(source.read_bytes()).hexdigest()})
            graph, overlay, obstruction = module.classify(root, {"rows": entries})
            self.assertEqual("unresolved", graph["driver_reference"])
            self.assertIn("write JSON", graph["side_effects"])
            self.assertEqual("overlay-copy", overlay["role"])
            self.assertIn("writes copies", overlay["side_effects"])
            self.assertEqual("intentional-contradiction-and-toy-control", obstruction["role"])
            self.assertEqual("unresolved per current invocation", obstruction["expected_outcome"])

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
