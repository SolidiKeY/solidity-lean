import copy
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
