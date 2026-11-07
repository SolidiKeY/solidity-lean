import hashlib
import importlib.util
import pathlib
import sys
import unittest

DIRECTORY = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(DIRECTORY))
spec = importlib.util.spec_from_file_location("source_windows", DIRECTORY / "source_windows.py")
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class WindowsTest(unittest.TestCase):
    def test_fidelity_and_negative_controls(self):
        data = b"heading\ndef a := 1\n-- comment\nprivate theorem b : True := by trivial\nend N\n"
        digest = hashlib.sha256(data).hexdigest()
        def row(line, name):
            return {"file": "test.lean", "sha256": digest, "line": line, "kind": "def", "name": name, "observation": "manual"}
        a, b = row(2, "a"), row(4, "b")
        result = module.windows([("one", [a, b])], {"test.lean": data})
        self.assertEqual([r["window"] for r in result], ["def a := 1\n-- comment\n", "private theorem b : True := by trivial\nend N\n"])
        self.assertEqual(result[0]["end_line"], 3)
        self.assertEqual(result[1]["end_line"], 5)
        self.assertEqual(result[0]["window_sha256"], hashlib.sha256(result[0]["window"].encode()).hexdigest())
        with self.assertRaises(ValueError): module.windows([("one", [a, a])], {"test.lean": data})
        with self.assertRaises(ValueError): module.windows([("one", [row(99, "bad")])], {"test.lean": data})
        with self.assertRaises(ValueError): module.windows([("one", [a])], {"test.lean": data + b"x"})

if __name__ == "__main__": unittest.main()
