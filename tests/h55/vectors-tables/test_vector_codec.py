import copy
import json
import subprocess
import tempfile
import importlib.util
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts/h55/vectors-tables"))
import vector_census as census
import vector_codec as codec

class CodecTests(unittest.TestCase):
    def test_all_original_bytes_and_determinism(self):
        total = 0
        for path in census.PATHS:
            original = (ROOT / path).read_bytes()
            records = codec.extract(path, original)
            total += len(records)
            self.assertEqual(codec.render(path, records), original, path)
            self.assertEqual(codec.render(path, records), codec.render(path, copy.deepcopy(records)), path)
        self.assertEqual(total, 6903)

    def test_emit_cli_and_reject_changed_output(self):
        data = {"schema": 1, "files": {p: codec.extract(p, (ROOT / p).read_bytes()) for p in census.PATHS}}
        with tempfile.TemporaryDirectory() as temp:
            base = Path(temp); records = base / "records.json"; dest = base / "generated"
            records.write_text(json.dumps(data))
            command = [sys.executable, "-B", str(ROOT / "scripts/h55/vectors-tables/vector_codec.py"), "emit", str(records), "--output", str(dest)]
            self.assertEqual(subprocess.run(command, capture_output=True).returncode, 0)
            for p in census.PATHS: self.assertEqual((dest / p).read_bytes(), (ROOT / p).read_bytes())
            self.assertNotEqual(subprocess.run(command, capture_output=True).returncode, 0)
            data["files"][census.PATHS[0]][0]["result"] = "999"
            records.write_text(json.dumps(data)); rejected = base / "rejected"
            command[-1] = str(rejected)
            self.assertNotEqual(subprocess.run(command, capture_output=True).returncode, 0)
            self.assertFalse(rejected.exists())

    def test_mutations_for_every_file(self):
        for path in census.PATHS:
            original = (ROOT / path).read_bytes()
            records = codec.extract(path, original)
            variants = {}
            variants["missing"] = records[1:]
            variants["extra"] = records + [records[-1]]
            variants["order"] = records[1:2] + records[:1] + records[2:]
            bad = copy.deepcopy(records); bad[0]["unexpected"] = 1; variants["schema"] = bad
            bad = copy.deepcopy(records); bad[0]["result"] = str(int(bad[0]["result"]) + 1); variants["output"] = bad
            for label, variant in variants.items():
                with self.subTest(path=path, mutation=label):
                    try: output = codec.render(path, variant)
                    except ValueError: continue
                    self.assertNotEqual(output, original)

if __name__ == "__main__": unittest.main()
