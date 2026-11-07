"""Bridge package/name/source boundary tests; never invoke Lean."""
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "scripts/h62/item2/audit-bytecode-selection"))
import bridge_inspection as bridge


class BridgeInspectionTests(unittest.TestCase):
    def test_strip_only_bridge_package_directory(self):
        self.assertEqual(bridge.module_name("Bridge/SolidityBridge/AccessBridge/AbiWord.lean"),
                         "SolidityBridge.AccessBridge.AbiWord")
        for path in ["Solidity/Backend/Selection/Interface.lean", "Bridge/Other/A.lean",
                     "Bridge/SolidityBridge/../A.lean", "Bridge/SolidityBridge/A.lean;evil",
                     "Bridge/SolidityBridge/A-B.lean"]:
            with self.subTest(path=path), self.assertRaises(ValueError):
                bridge.module_name(path)

    def test_empty_unknown_duplicate_and_core_module_refused(self):
        paths = ["Solidity/Backend/Selection/Interface.lean", "Bridge/SolidityBridge/A.lean"]
        self.assertEqual(bridge.selected_sources(paths, None),
                         {"SolidityBridge.A": "Bridge/SolidityBridge/A.lean"})
        for selected in [[], ["SolidityBridge.Missing"], ["Solidity.Backend.Selection.Interface"],
                         ["SolidityBridge.A", "SolidityBridge.A"]]:
            with self.subTest(selected=selected), self.assertRaises(ValueError):
                bridge.selected_sources(paths, selected)
        with self.assertRaises(ValueError):
            bridge.selected_sources(paths + [paths[1]], None)

    def test_template_is_literal_and_unique_no_code_execution(self):
        source = b'raise RuntimeError("must not execute")\nTEMPLATE = "MODULES FINGERPRINT"\n'
        self.assertEqual(bridge.extract_template(source), "MODULES FINGERPRINT")
        for raw in [b'TEMPLATE = function()\n', b'TEMPLATE = 3\n',
                    b'TEMPLATE = "MODULES"\n', b'TEMPLATE = "MODULES FINGERPRINT"\nTEMPLATE = "x"\n']:
            with self.subTest(raw=raw), self.assertRaises((ValueError, TypeError)):
                bridge.extract_template(raw)

    def fixture(self, root):
        path = "Bridge/SolidityBridge/A.lean"
        source = root / path
        source.parent.mkdir(parents=True)
        source.write_bytes(b"-- immutable source fixture\n")
        expected = source.read_bytes()
        scanner = ("BASE = 'fixture-base'\ndef mapped_paths(repo): return ([" + repr(path) + "], 1)\n").encode()
        original_template = bridge.extract_template((ROOT / bridge.GENERATOR).read_bytes())
        generator = ("TEMPLATE = " + repr(original_template) + "\n").encode()
        def git(repo, *args):
            self.assertEqual(args[0], "show")
            if args[1] == bridge.MEMBER + ":" + bridge.CENSUS: return scanner
            if args[1] == bridge.MEMBER + ":" + bridge.GENERATOR: return generator
            if args[1] == "fixture-base:" + path: return expected
            raise AssertionError(args)
        return source, git, original_template

    def test_generation_keeps_exact_template_and_is_deterministic(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _, fake_git, template = self.fixture(root)
            with patch.object(bridge, "git", side_effect=fake_git):
                source, pins = bridge.generate(root)
                source2, pins2 = bridge.generate(root)
            self.assertEqual((source, pins), (source2, pins2))
            self.assertEqual(pins["modules"], ["SolidityBridge.A"])
            self.assertEqual(pins["execution_status"], "not run")
            self.assertEqual(pins["inspection_template_sha256"], bridge.sha(template.encode()))
            expected_body = template.replace("MODULES", "`SolidityBridge.A").replace("FINGERPRINT", pins["manifest_sha256"])
            self.assertEqual(source, "import Lean\nimport SolidityBridge.A\n" + expected_body)
            self.assertEqual(pins["inspection_sha256"], bridge.sha(source.encode()))
            self.assertNotIn("set_option maxHeartbeats", source)

    def test_changed_frozen_source_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, fake_git, _ = self.fixture(root)
            source.write_bytes(b"-- changed source fixture\n")
            with patch.object(bridge, "git", side_effect=fake_git), self.assertRaisesRegex(ValueError, "frozen source differs"):
                bridge.generate(root)

    def test_same_byte_source_symlink_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, fake_git, _ = self.fixture(root)
            target = root / "same-bytes"
            target.write_bytes(source.read_bytes())
            source.unlink()
            source.symlink_to(target)
            with patch.object(bridge, "git", side_effect=fake_git), self.assertRaisesRegex(ValueError, "symlink"):
                bridge.generate(root)


if __name__ == "__main__":
    unittest.main()
