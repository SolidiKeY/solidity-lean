"""Input-stage regressions: no empty verification, traversal or duplicate pins.

These controls exercise identity checking only, not full static/Lean acceptance.
"""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from acceptance import verify_inputs


class InputManifestControls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.inputs = self.root / "inputs"
        self.inputs.mkdir()

    def files(self, count):
        pins = {}
        for i in range(count):
            name = f"input-{i}.json"
            data = f"fixture {i}".encode()
            (self.inputs / name).write_bytes(data)
            pins[name] = hashlib.sha256(data).hexdigest()
        return pins

    def manifest(self, pins):
        (self.inputs / "sha256.json").write_text(json.dumps(pins))

    def test_valid_five_and_truthful_count(self):
        pins = self.files(5)
        self.manifest(pins)
        self.assertEqual(verify_inputs(self.inputs), 5)
        self.manifest(dict(list(pins.items())[:2]))
        self.assertEqual(verify_inputs(self.inputs), 2)

    def test_empty_manifest_refused(self):
        self.manifest({})
        with self.assertRaises(ValueError):
            verify_inputs(self.inputs)

    def test_changed_input_refused(self):
        self.manifest(self.files(1))
        (self.inputs / "input-0.json").write_bytes(b"changed")
        with self.assertRaises(ValueError):
            verify_inputs(self.inputs)

    def test_escaping_and_noncanonical_paths_refused(self):
        outside = self.root / "outside"
        outside.write_bytes(b"fixture")
        digest = hashlib.sha256(b"fixture").hexdigest()
        for name in ("../outside", str(outside), "./outside", "dir//outside"):
            with self.subTest(name=name):
                self.manifest({name: digest})
                with self.assertRaises(ValueError):
                    verify_inputs(self.inputs)

    def test_escaping_symlink_refused(self):
        outside = self.root / "outside"
        outside.write_bytes(b"fixture")
        (self.inputs / "link").symlink_to(outside)
        self.manifest({"link": hashlib.sha256(b"fixture").hexdigest()})
        with self.assertRaises(ValueError):
            verify_inputs(self.inputs)

    def test_duplicate_object_keys_refused(self):
        name, digest = next(iter(self.files(1).items()))
        pair = f'{json.dumps(name)}: {json.dumps(digest)}'
        (self.inputs / "sha256.json").write_text("{" + pair + "," + pair + "}")
        with self.assertRaises(ValueError):
            verify_inputs(self.inputs)

    def test_nonobject_manifest_refused(self):
        for pins in ([], [["input", "0" * 64]], None, "input"):
            with self.subTest(pins=pins):
                self.manifest(pins)
                with self.assertRaises(ValueError):
                    verify_inputs(self.inputs)

    def test_wrong_digest_refused(self):
        pins = self.files(1)
        pins["input-0.json"] = "0" * 64
        self.manifest(pins)
        with self.assertRaises(ValueError):
            verify_inputs(self.inputs)


if __name__ == "__main__":
    unittest.main()
