import importlib.util
import json
import shutil
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("fixture_controls", ROOT / "scripts/h55/vectors-tables/fixture_controls.py")
f = importlib.util.module_from_spec(spec)
spec.loader.exec_module(f)

class FixtureControlsTests(unittest.TestCase):
    def test_full_inventory(self):
        self.assertEqual(f.inventory(ROOT), json.loads(f.MANIFEST.read_text()))
        self.assertEqual([f.render(i) for i in range(f.COUNT)], [f.render(i) for i in range(f.COUNT)])
    def test_mutations_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / f.DATA).parent.mkdir(parents=True)
            shutil.copyfile(ROOT / f.DATA, root / f.DATA)
            shutil.copytree(ROOT / f.CONTROL, root / f.CONTROL)
            control = root / f.CONTROL / f.names()[0]
            original = control.read_bytes()
            control.unlink()
            with self.assertRaises(ValueError): f.inventory(root)
            control.write_bytes(original)
            extra = root / f.CONTROL / "Case45.lean"; extra.write_bytes(original)
            with self.assertRaises(ValueError): f.inventory(root)
            extra.unlink()
            control.write_bytes(original.replace(b"decide +kernel", b"rfl"))
            with self.assertRaises(ValueError): f.inventory(root)
            control.write_bytes(original)
            control.write_bytes(f.render(1))
            with self.assertRaises(ValueError): f.inventory(root)
            control.write_bytes(original)
            data = root / f.DATA; source = data.read_bytes()
            data.write_bytes(source.replace(b"def statementFixture0 : StatementFixture :=", b"def statementFixture99 : StatementFixture :="))
            with self.assertRaises(ValueError): f.inventory(root)

if __name__ == "__main__": unittest.main()
