"""Guard regression: child-only CPU settings hide ancestor restrictions."""
import importlib.util
import pathlib
import tempfile
import unittest
from unittest.mock import patch

path = pathlib.Path(__file__).resolve().parents[3] / "scripts/h55/module-times/cpu_ancestry.py"
spec = importlib.util.spec_from_file_location("cpu_ancestry", path)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class CpuAncestry(unittest.TestCase):
    def write(self, path, quota, cpus="0-3", mems="0"):
        path.mkdir(exist_ok=True)
        (path / "cpu.max").write_text(quota)
        (path / "cpu.max.burst").write_text("0")
        (path / "cpu.weight").write_text("100")
        (path / "cpu.idle").write_text("0")
        (path / "cpuset.cpus.effective").write_text(cpus)
        (path / "cpuset.mems.effective").write_text(mems)

    def test_parent_limit_changes_visible_snapshot(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            parent, leaf = root / "docker", root / "docker" / ("a" * 64)
            self.write(root, "max 100000")
            self.write(parent, "50000 100000")
            self.write(leaf, "max 100000")
            before = module.read_chain(root, leaf)
            self.assertEqual(["/", "/docker", "/docker/" + "a" * 64], [r["path"] for r in before])
            (parent / "cpu.max").write_text("25000 100000")
            self.assertNotEqual(before, module.read_chain(root, leaf))
            item = {"mount_root": "/..", "ancestor_complete": False, "container_id": "a" * 64, "pid": "123", "start_ticks": "456", "visible_chain": before}
            self.assertEqual("matching-visible-unattested", module.compare(item, item))
            other_chain = [*before[:-1], {**before[-1], "path": "/docker/" + "b" * 64}]
            other_run = {**item, "container_id": "b" * 64, "pid": "321", "start_ticks": "654", "visible_chain": other_chain}
            self.assertEqual("mismatch", module.compare(item, other_run))
            self.assertEqual("matching-visible-unattested", module.compare_visible_policies(item, other_run))
            changed_burst = {**other_run, "visible_chain": [{**other_chain[0], "cpu_burst": "1"}, *other_chain[1:]]}
            self.assertEqual("mismatch", module.compare_visible_policies(item, changed_burst))
            for field, value in [("cpu_weight", "200"), ("cpu_idle", "1")]:
                changed_field = {**other_run, "visible_chain": [{**other_chain[0], field: value}, *other_chain[1:]]}
                self.assertEqual("mismatch", module.compare_visible_policies(item, changed_field))
            for field, value in [("cpu_burst", "²"), ("cpu_burst", "٠"), ("cpu_burst", str(1 << 64)), ("cpu_max", "١ ١"),
                                 ("cpu_max", "9" * 5000 + " 100000"), ("cpu_weight", "١٠٠"),
                                 ("cpu_weight", "0"), ("cpu_idle", "2"), ("cpus_effective", "9" * 5000)]:
                invalid = {**other_run, "visible_chain": [{**other_chain[0], field: value}, *other_chain[1:]]}
                self.assertEqual("invalid", module.compare_visible_policies(item, invalid))
            for field in ("cpu_burst", "cpu_weight", "cpu_idle"):
                missing_row = dict(other_chain[0])
                del missing_row[field]
                invalid = {**other_run, "visible_chain": [missing_row, *other_chain[1:]]}
                self.assertEqual("invalid", module.compare_visible_policies(item, invalid))
            changed_quota = {**other_run, "visible_chain": [{**other_chain[0], "cpu_max": "1 100000"}, *other_chain[1:]]}
            self.assertEqual("mismatch", module.compare_visible_policies(item, changed_quota))
            self.assertEqual("invalid", module.compare(item, {**item, "visible_chain": []}))
            changed = {**item, "visible_chain": module.read_chain(root, leaf)}
            self.assertEqual("mismatch", module.compare(item, changed))
            malformed = {"ancestor_complete": False, "visible_chain": ["not-a-cgroup"]}
            self.assertEqual("invalid", module.compare(malformed, malformed))
            root_only = {**item, "visible_chain": before[:1]}
            self.assertEqual("invalid", module.compare(root_only, root_only))
            reversed_range = {**item, "visible_chain": [{**before[0], "cpus_effective": "3-1"}, *before[1:]]}
            self.assertEqual("invalid", module.compare(reversed_range, reversed_range))

    def test_pid_identity_or_membership_change_is_rejected(self):
        """Guard regression: a replaced process inherits stale cgroup evidence."""
        chain = [{"path": "/", "cpu_max": "max 100000", "cpu_burst": "0", "cpu_weight": "100", "cpu_idle": "0", "cpus_effective": "0-3", "mems_effective": "0"}]
        with patch.object(module, "process_identity", side_effect=[("1", "old"), ("2", "new")]), \
             patch.object(module, "local_mount_supported", return_value=True), \
             patch.object(module, "read_chain", return_value=chain):
            with self.assertRaises(ValueError):
                module.local_snapshot("a" * 64, "123")

    def test_malformed_missing_and_symlink_fail(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp).resolve()
            self.write(root, "max 100000")
            bad = root / "bad"
            self.write(bad, "0 100000")
            with self.assertRaises(ValueError):
                module.read_chain(root, bad)
            (bad / "cpu.max").write_text("max 100000")
            (bad / "cpuset.cpus.effective").unlink()
            with self.assertRaises(OSError):
                module.read_chain(root, bad)
            alias = root / "alias"
            alias.symlink_to(bad, target_is_directory=True)
            with self.assertRaises(ValueError):
                module.read_chain(root, alias)


if __name__ == "__main__":
    unittest.main()
