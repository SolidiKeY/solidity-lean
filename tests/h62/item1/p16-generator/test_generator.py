#!/usr/bin/env python3
"""Black-box drift controls against a disposable miniature checkout."""
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[4]
LANE = pathlib.Path("scripts/h62/item1/p16-generator")
TARGET = pathlib.Path("Solidity/Yul/Interfaces/P16.lean")


class GeneratorControls(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.tmp.name)
        shutil.copytree(ROOT / LANE, self.root / LANE)
        (self.root / TARGET).parent.mkdir(parents=True)
        shutil.copyfile(ROOT / TARGET, self.root / TARGET)
        for p in (self.root / LANE / "imports").glob("*.txt"):
            source = self.root / (p.read_text().strip().replace(".", "/") + ".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.touch()
        self.original = (self.root / TARGET).read_text()

    def tearDown(self):
        self.tmp.cleanup()

    def run_gen(self, arg):
        return subprocess.run([sys.executable, str(self.root / LANE / "generate.py"), arg], text=True, capture_output=True)

    def check_drift(self, text, message):
        (self.root / TARGET).write_text(text)
        result = self.run_gen("--check")
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn(message, result.stdout)

    def test_exact(self):
        self.assertEqual(self.run_gen("--check").returncode, 0)
        self.assertEqual(self.run_gen("--render").stdout, self.original)

    def test_missing_and_extra(self):
        line = self.original.splitlines(keepends=True)[0]
        self.check_drift(self.original.removeprefix(line), "missing import")
        self.check_drift(self.original + "\nimport Solidity.Yul.Extra\n", "extra import")

    def test_duplicate_order_and_body(self):
        lines = self.original.splitlines(keepends=True)
        self.check_drift(lines[0] + self.original, "non-generated")
        lines[0], lines[1] = lines[1], lines[0]
        self.check_drift("".join(lines), "non-generated")
        self.check_drift(self.original + "-- drift\n", "non-generated")

    def test_missing_target_render_and_migration_patch(self):
        target = self.root / TARGET
        patch = self.run_gen("--patch").stdout
        self.assertEqual(patch, "")
        command = [sys.executable, str(self.root / LANE / "generate.py"), "--migration"]
        migration = subprocess.run(command + ["--render"], text=True, capture_output=True, check=True).stdout
        diff = subprocess.run(command + ["--patch"], text=True, capture_output=True, check=True).stdout
        applied = subprocess.run(["patch", "-p1"], cwd=self.root, input=diff, text=True, capture_output=True)
        self.assertEqual(applied.returncode, 0, applied.stderr)
        self.assertEqual(target.read_text(), migration)
        self.assertEqual(subprocess.run(command + ["--check"], capture_output=True).returncode, 0)
        self.assertEqual(self.run_gen("--check").returncode, 1)
        target.unlink()
        self.assertEqual(self.run_gen("--render").stdout, self.original)

    def test_fragment_and_source_drift(self):
        entries = sorted((self.root / LANE / "imports").glob("*.txt"))
        source = self.root / (entries[0].read_text().strip().replace(".", "/") + ".lean")
        source.unlink()
        self.assertEqual(self.run_gen("--check").returncode, 2)
        source.touch()
        extra = self.root / LANE / "imports" / "999-Extra.txt"
        extra.write_text("Solidity.Yul.Extra\n")
        (self.root / "Solidity/Yul/Extra.lean").touch()
        self.assertIn("missing import Solidity.Yul.Extra", self.run_gen("--check").stdout)
        extra.unlink()
        entries[0].unlink()
        self.assertEqual(self.run_gen("--check").returncode, 1)
        body = next((self.root / LANE / "body").glob("*.txt"))
        body.unlink()
        self.assertEqual(self.run_gen("--check").returncode, 1)

    def test_bad_input(self):
        entries = sorted((self.root / LANE / "imports").glob("*.txt"))
        entries[1].write_text(entries[0].read_text())
        self.assertEqual(self.run_gen("--check").returncode, 2)
        entries[1].write_text("not a module\n")
        self.assertEqual(self.run_gen("--check").returncode, 2)
        entries[1].write_text("Solidity.Yul.Missing\n")
        self.assertEqual(self.run_gen("--check").returncode, 2)


if __name__ == "__main__":
    unittest.main()
