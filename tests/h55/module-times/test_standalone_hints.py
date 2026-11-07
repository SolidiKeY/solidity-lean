"""Guard regression: source drift or lexical hints become accepted recipes."""
import contextlib
import hashlib
import io
import json
from unittest import mock
import importlib.util
import pathlib
import tempfile
import unittest

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/standalone_hints.py"
spec = importlib.util.spec_from_file_location("standalone_hints", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class StandaloneHints(unittest.TestCase):
    def test_malformed_top_level_fails_without_traceback(self):
        with tempfile.TemporaryDirectory() as tmp:
            manifest = pathlib.Path(tmp) / "manifest.json"
            for value in (None, []):
                manifest.write_text(json.dumps(value))
                stderr = io.StringIO()
                with mock.patch.object(module.sys, "argv", ["standalone_hints.py", str(manifest)]), contextlib.redirect_stderr(stderr):
                    self.assertEqual(1, module.main())
                self.assertIn("candidate manifest must be an object", stderr.getvalue())

    def test_cli_labels_subset_and_binds_manifest_bytes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            source = root / "A.lean"
            source.write_text("#check 1\n")
            row = {"path": "A.lean", "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                   "context": "standalone-root-review"}
            manifest = root / "manifest.json"
            manifest.write_text(json.dumps({"head": "caller-value", "scope": "caller-scope", "rows": [row]}))
            stdout = io.StringIO()
            with mock.patch.object(module, "ROOT", root), mock.patch.object(module.sys, "argv", ["standalone_hints.py", str(manifest)]), contextlib.redirect_stdout(stdout):
                self.assertEqual(0, module.main())
            result = json.loads(stdout.getvalue())
            self.assertEqual("unverified-subsets-accepted", result["coverage"])
            self.assertEqual("caller-value", result["source_head_unverified"])
            self.assertEqual("caller-scope", result["source_scope_unverified"])
            self.assertEqual(hashlib.sha256(manifest.read_bytes()).hexdigest(), result["source_manifest_sha256"])

    def test_hints_do_not_resolve_and_source_drift_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            file = root / "A.lean"
            file.write_text("-- import in comment\n#guard_msgs in #check 1\n#eval 2\n")
            row = {"path": "A.lean", "sha256": hashlib.sha256(file.read_bytes()).hexdigest(),
                   "context": "standalone-root-review"}
            row["category"] = "control-review"
            result = module.classify(root, {"rows": [row]})[0]
            self.assertEqual(row, result["original_candidate"])
            self.assertEqual([1, 2, 3], [hint["line"] for hint in result["lexical_hints"]])
            for key in ("driver", "expected_outcome", "auxiliary_inputs", "side_effects"):
                self.assertEqual("unresolved", result[key])
            file.write_text("changed")
            with self.assertRaises(ValueError):
                module.classify(root, {"rows": [row]})
            with self.assertRaises(ValueError):
                module.classify(root, {"rows": [row, row]})


if __name__ == "__main__":
    unittest.main()
