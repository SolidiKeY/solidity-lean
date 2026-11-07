import unittest
from live_inventory import reconcile


class ReconciliationTests(unittest.TestCase):
    def sample(self):
        return dict(files=[dict(path="old.lean", sha256="old"),
                           dict(path="new.lean", sha256="new")],
                    declarations=[dict(path="old.lean", name="original"),
                                  dict(path="new.lean", name="added")], summary=dict(files=2))

    def test_additions_are_explicit_not_original_cases(self):
        result = reconcile(self.sample(), {"old.lean": "old"})
        self.assertEqual(result["original_files"], 1)
        self.assertEqual(result["original_declarations"], 1)
        self.assertEqual(result["live_summary"], dict(files=2))
        self.assertEqual(result["additions"][0]["path"], "new.lean")
        self.assertEqual(result["additions"][0]["declarations"][0]["name"], "added")

    def test_changed_original_rejected(self):
        with self.assertRaisesRegex(ValueError, "changed"):
            reconcile(self.sample(), {"old.lean": "different"})

    def test_missing_original_rejected(self):
        with self.assertRaisesRegex(ValueError, "missing"):
            reconcile(self.sample(), {"absent.lean": "old"})

    def test_duplicate_file_rejected(self):
        data = self.sample()
        data["files"].append(data["files"][0])
        with self.assertRaisesRegex(ValueError, "duplicate"):
            reconcile(data, {"old.lean": "old"})


if __name__ == "__main__":
    unittest.main()
