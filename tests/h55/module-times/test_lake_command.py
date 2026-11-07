"""Guard regression: per-file checks bypass Lake or rebuild imports in parallel."""
import hashlib
import importlib.util
import pathlib
import tempfile
import unittest

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/lake_command.py"
spec = importlib.util.spec_from_file_location("lake_command", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class LakeCommand(unittest.TestCase):
    def test_pinned_no_build_serial_command(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            bin_dir = root / "bin"
            bin_dir.mkdir()
            lake, lean = bin_dir / "lake", bin_dir / "lean"
            lake.write_bytes(b"fixture lake")
            lean.write_bytes(b"fixture lean")
            lake.chmod(0o700)
            lean.chmod(0o700)
            source = root / "Bridge" / "X.lean"
            source.parent.mkdir()
            source.write_text("-- fixture")
            lp, np = (hashlib.sha256(p.read_bytes()).hexdigest() for p in (lake, lean))
            env = {"PATH": str(bin_dir) + ":/usr/bin", "LEAN_NUM_THREADS": "4"}
            result = module.prepare(lake, lp, lean, np, root, "Bridge/X.lean", "bridge", env)
            self.assertEqual([str(lake), "--no-build", "lean", "X.lean", "--", "-j1", "--tstack=131072"], result["argv"])
            self.assertEqual("1", result["env"]["LEAN_NUM_THREADS"])
            self.assertEqual(str(root / "Bridge"), result["cwd"])
            for bad_env in [{"PATH": "/usr/bin"}, {"PATH": str(bin_dir) + ":."},
                            {"PATH": str(bin_dir), "LEAN_PATH": "/unverified"},
                            {"PATH": str(bin_dir), "LD_PRELOAD": "/unverified"},
                            {"PATH": str(bin_dir), "LAKE_OVERRIDE_LEAN": "true", "LEAN": "/other/lean"},
                            {"PATH": str(bin_dir), "LAKE_CACHE_DIR": "/unverified"}]:
                with self.subTest(env=bad_env), self.assertRaises(ValueError):
                    module.prepare(lake, lp, lean, np, root, "Bridge/X.lean", "bridge", bad_env)
            with self.assertRaises(ValueError):
                module.prepare(lake, lp, lean, "0" * 64, root, "Bridge/X.lean", "bridge", env)
            with self.assertRaises(ValueError):
                module.prepare(lake, lp, lean, np, root, "../X.lean", "root", env)


if __name__ == "__main__":
    unittest.main()
