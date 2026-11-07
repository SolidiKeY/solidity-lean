"""Guard regression: mutations in selected Lake inputs escape observation."""
import importlib.util
import os
import pathlib
import tempfile
import unittest

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/lake_workspace.py"
spec = importlib.util.spec_from_file_location("lake_workspace", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class LakeWorkspace(unittest.TestCase):
    def test_selected_config_dependency_cache_and_command_changes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            config = root / "lakefile.toml"
            config.write_text("name = fixture\n")
            deps = root / "packages"
            deps.mkdir()
            dep = deps / "manifest"
            dep.write_text("one")
            cache = root / "cache"
            cache.mkdir()
            artifact = cache / "artifact"
            artifact.write_text("one")
            command = {"argv": ["lake", "lean"], "cwd": str(root), "env": {}, "tool_sha256": {}}
            files, trees = {"config": config}, {"dependencies": deps, "cache": cache}
            before = module.capture(files, trees, command)
            self.assertTrue(module.unchanged(before, module.capture(files, trees, command)))
            for target in (config, dep, artifact):
                old = target.read_text()
                target.write_text(old + "changed")
                self.assertFalse(module.unchanged(before, module.capture(files, trees, command)))
                target.write_text(old)
                before = module.capture(files, trees, command)
            os.link(config, root / "hardlink")
            self.assertFalse(module.unchanged(before, module.capture(files, trees, command)))
            (root / "hardlink").unlink()
            before = module.capture(files, trees, command)
            timestamp = config.stat().st_mtime_ns
            os.utime(config, ns=(timestamp + 1_000_000_000, timestamp + 1_000_000_000))
            self.assertFalse(module.unchanged(before, module.capture(files, trees, command)))
            before = module.capture(files, trees, command)
            command["env"]["HOME"] = "/other"
            self.assertFalse(module.unchanged(before, module.capture(files, trees, command)))
            command["argv"].append("sensitive-sentinel")
            self.assertNotIn("sensitive-sentinel", repr(module.capture(files, trees, command)))
            command["env"]["SECRET_TOKEN"] = "fixture"
            with self.assertRaises(ValueError):
                module.capture(files, trees, command)
            del command["env"]["SECRET_TOKEN"]
            with self.assertRaises(ValueError):
                module.capture({}, trees, command)
            with self.assertRaises(ValueError):
                module.capture(files, {}, command)

    def test_explicit_xdg_cache_must_match_selected_tree(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            config = root / "lakefile.toml"
            config.write_text("fixture")
            cache, other = root / "cache", root / "other"
            cache.mkdir()
            other.mkdir()
            command = {"argv": ["lake"], "cwd": str(root),
                       "env": {"XDG_CACHE_HOME": str(cache)}, "tool_sha256": {}}
            with self.assertRaisesRegex(ValueError, "XDG cache home"):
                module.capture({"config": config}, {"xdg_cache_home": other}, command)
            with self.assertRaisesRegex(ValueError, "XDG cache home"):
                module.capture({"config": config}, {"other": cache}, command)
            before = module.capture({"config": config}, {"xdg_cache_home": cache}, command)
            (cache / "lake").mkdir()
            after = module.capture({"config": config}, {"xdg_cache_home": cache}, command)
            self.assertFalse(module.unchanged(before, after))
            command["env"]["XDG_CACHE_HOME"] = "relative"
            with self.assertRaisesRegex(ValueError, "XDG cache home"):
                module.capture({"config": config}, {"xdg_cache_home": cache}, command)

    def test_symlink_and_missing_paths_fail(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            config = root / "config"
            config.write_text("x")
            link = root / "link"
            link.symlink_to(config)
            command = {"argv": [], "cwd": str(root), "env": {}, "tool_sha256": {}}
            with self.assertRaises(ValueError):
                module.capture({"config": link}, {"tree": root}, command)
            with self.assertRaises(ValueError):
                module.capture({"config": config}, {"tree": root / "missing"}, command)


if __name__ == "__main__":
    unittest.main()
