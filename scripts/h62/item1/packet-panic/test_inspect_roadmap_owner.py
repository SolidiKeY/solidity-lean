import hashlib
import importlib.util
import pathlib
import unittest

spec = importlib.util.spec_from_file_location("inspect_roadmap_owner", pathlib.Path(__file__).with_name("inspect_roadmap_owner.py"))
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class OwnerInspectionTest(unittest.TestCase):
    def test_guard_and_invalid_inputs(self):
        data = ("/-- info: expected -/\n" + module.GUARD + "\n").encode()
        result = module.inspect(data)
        self.assertEqual(result["guard_line"], 2)
        self.assertEqual(result["sha256"], hashlib.sha256(data).hexdigest())
        for malformed in (b"", module.GUARD.encode(), data + data):
            with self.assertRaises(ValueError): module.inspect(malformed)
        self.assertEqual(module.commit("a" * 40), "a" * 40)
        for invalid in ("main", "-x", "A" * 40, "a" * 39):
            with self.assertRaises(module.argparse.ArgumentTypeError): module.commit(invalid)

if __name__ == "__main__": unittest.main()
