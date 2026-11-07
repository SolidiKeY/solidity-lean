import hashlib
import importlib.util
import pathlib
import tempfile
import unittest

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/lean_command.py"
spec = importlib.util.spec_from_file_location("lean_command", path)
command = importlib.util.module_from_spec(spec)
spec.loader.exec_module(command)


class LeanCommand(unittest.TestCase):
    def test_fixed_flags_identity_and_paths(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            binary = root / "lean"
            binary.write_bytes(b"fake-lean-test-only")
            binary.chmod(0o700)
            source = root / "Bridge" / "X.lean"
            source.parent.mkdir()
            source.write_text("-- fixture")
            pin = hashlib.sha256(binary.read_bytes()).hexdigest()
            result = command.prepare(binary, pin, root, "Bridge/X.lean", "bridge", {"LEAN_NUM_THREADS": "9"})
            self.assertEqual([str(binary), "-j1", "--tstack=131072", "X.lean"], result["argv"])
            self.assertEqual("1", result["env"]["LEAN_NUM_THREADS"])
            for invalid_path, context, digest in [("../X.lean", "root", pin),
                                                   ("Bridge/X.lean", "root", pin),
                                                   ("Bridge/X.lean", "bridge", "0" * 64)]:
                with self.subTest(path=invalid_path, context=context), self.assertRaises(ValueError):
                    command.prepare(binary, digest, root, invalid_path, context, {})
            for key in ["LD_PRELOAD", "LD_LIBRARY_PATH", "LEAN_OPTS", "LEAN_EXTRA_OPTS"]:
                with self.subTest(env=key), self.assertRaises(ValueError):
                    command.prepare(binary, pin, root, "Bridge/X.lean", "bridge", {key: "unverified"})
            (root / "alias.lean").symlink_to(source)
            with self.assertRaises(ValueError):
                command.prepare(binary, pin, root, "alias.lean", "root", {})


if __name__ == "__main__":
    unittest.main()
