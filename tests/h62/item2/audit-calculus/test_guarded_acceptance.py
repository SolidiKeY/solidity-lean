"""Regression: failed validation must preserve old aggregates and reject stale runtime inputs."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[4] / "scripts/h62/item2/audit-calculus"))
from guarded_acceptance import digest, evidence_view, publish_json, runtime_binding, stage_baseline, complete_exit


class AcceptanceIntegrityControls(unittest.TestCase):
    def test_existing_aggregate_preserved(self):
        with tempfile.TemporaryDirectory() as name:
            target = Path(name) / "acceptance.json"
            prior = b"prior aggregate bytes\n"
            target.write_bytes(prior)
            with self.assertRaises(FileExistsError):
                publish_json(target, {"replacement": True})
            self.assertEqual(target.read_bytes(), prior)
            self.assertEqual(list(target.parent.iterdir()), [target])

    def test_publication_is_complete_and_fresh(self):
        with tempfile.TemporaryDirectory() as name:
            target = Path(name) / "new.json"
            publish_json(target, {"boundary": "control data only"})
            self.assertEqual(json.loads(target.read_text()), {"boundary": "control data only"})

    def test_truncated_census_cannot_create_view(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            census = root / "census.json"
            census.write_text("{}")
            with self.assertRaisesRegex(ValueError, "census"):
                evidence_view(root / "view", census, root)
            self.assertFalse((root / "view").exists())

    def test_runtime_bindings_refuse_mixed_receipts_and_tampering(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            (root / "bin").mkdir()
            (root / "lib").mkdir()
            (root / "bin/lean").write_bytes(b"fingerprint control, never executed")
            artifact = root / "lib/import.olean"
            artifact.write_bytes(b"import fingerprint control, never loaded")
            manifest = root / "imports.json"
            manifest.write_text(json.dumps({"@toolchain/lib/import.olean": digest(artifact)}))
            lean, imports = digest(root / "bin/lean"), digest(manifest)
            records = [{"schema": 2, "lean_sha256": lean}]
            self.assertEqual(runtime_binding(records, root, lean, manifest, imports), 1)
            with self.assertRaisesRegex(ValueError, "mixed"):
                runtime_binding([{"schema": 2, "lean_sha256": "different"}], root, lean, manifest, imports)
            with self.assertRaisesRegex(ValueError, "manifest"):
                runtime_binding(records, root, lean, manifest, "wrong")
            artifact.write_bytes(b"changed import")
            with self.assertRaisesRegex(ValueError, "toolchain import differs"):
                runtime_binding(records, root, lean, manifest, imports)

    def test_receipt_ledger_is_frozen_not_symlinked(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            original = root / "baseline"
            original.mkdir()
            ledger = original / "lean-commands.jsonl"
            ledger.write_bytes(b"validated ledger bytes")
            stage_baseline(root / "view", original, ledger.read_bytes())
            ledger.write_bytes(b"changed ledger after preflight")
            self.assertEqual((root / "view/lean-commands.jsonl").read_bytes(), b"validated ledger bytes")
            self.assertFalse((root / "view/lean-commands.jsonl").is_symlink())

    def test_missing_historical_binding_blocks_complete_success(self):
        self.assertEqual(complete_exit(0, False), 89)
        self.assertEqual(complete_exit(1, False), 1)
        self.assertEqual(complete_exit(88, True), 88)

    def test_empty_receipts_cannot_bind_runtime(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            (root / "bin").mkdir()
            (root / "bin/lean").write_bytes(b"not executable")
            manifest = root / "imports.json"
            manifest.write_text("{}")
            with self.assertRaisesRegex(ValueError, "receipts"):
                runtime_binding([], root, digest(root / "bin/lean"), manifest, digest(manifest))


if __name__ == "__main__":
    unittest.main()
