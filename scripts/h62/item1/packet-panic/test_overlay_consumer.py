import pathlib
import subprocess
import sys
import tempfile
import tomllib
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[4]
SCRIPT = pathlib.Path(__file__).with_name("mcp_serial_diagnostic.py")
PROJECT = ROOT / "tests/h62/item1/packet-panic/closure-project-overlay"
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from diagnostic_policy import validated_target

class OverlayConsumerTest(unittest.TestCase):
    def test_isolated_project_and_unrelated_path_refused(self):
        config = tomllib.loads((PROJECT / "lakefile.toml").read_text())
        libs = {item["name"]: item for item in config["lean_lib"]}
        self.assertEqual(libs["PanicBytes"]["srcDir"], ".")
        self.assertEqual((PROJECT / libs["Solidity"]["srcDir"]).resolve(), ROOT)
        self.assertTrue(all("-j1" in item["weakLeanArgs"] for item in libs.values()))
        self.assertEqual((PROJECT / "lean-toolchain").read_text().strip(), "leanprover/lean4:v4.35.0")
        with tempfile.TemporaryDirectory() as tmp:
            result = subprocess.run(["/workspace/solidity-lean/.venv/bin/python", str(SCRIPT), "--project", tmp], capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("outside the two authorized isolated diagnostic paths", result.stderr)
            self.assertFalse((pathlib.Path(tmp) / ".lake").exists())

    def test_helper_target_refuses_symlink_and_other_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            project = root / "project"
            project.mkdir()
            external = root / "outside.lean"
            external.write_text("outside")
            helper = project / "PanicBytes.lean"
            helper.symlink_to(external)
            with self.assertRaisesRegex(ValueError, "must not be a symlink"):
                validated_target(project, helper)
            helper.unlink()
            helper.write_text("helper")
            self.assertEqual(validated_target(project, helper), helper)
            with self.assertRaisesRegex(ValueError, "not the project helper"):
                validated_target(project, external)

if __name__ == "__main__": unittest.main()
