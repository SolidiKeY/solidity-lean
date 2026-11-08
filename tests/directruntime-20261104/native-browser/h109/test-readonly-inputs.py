"""Guard H127 input mount observations against writable, nested and drifted views.

Synthetic mount fixtures do not establish a real sealed worker or mount setup.
Actual local negative controls create no mounts and execute no worker.
"""
import importlib.util
import os
from pathlib import Path
import tempfile
import types
import unittest
from unittest import mock

spec = importlib.util.spec_from_file_location("inputs", Path(__file__).with_name("readonly-inputs.py"))
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
TABLE = "40 1 0:23 /source /input ro,nosuid,nodev - tmpfs tmpfs rw\n"


class InputMountControls(unittest.TestCase):
    def row(self, text=TABLE):
        return m.parse(text)

    def test_readonly_bind_with_writable_superblock_is_observation_only(self):
        # Per-mount ro may coexist with superblock rw (e.g. read-only bind).
        row = m.validate_mount(self.row(), 40, "/input", os.makedev(0, 23), os.ST_RDONLY)
        self.assertIn("rw", row["superOptions"])

    def test_writable_mount_or_kernel_flag_refused(self):
        for text, flags in ((TABLE.replace("ro,nosuid", "rw,nosuid"), os.ST_RDONLY), (TABLE, 0)):
            with self.subTest(text=text, flags=flags), self.assertRaisesRegex(m.MountError, "writable"):
                m.validate_mount(self.row(text), 40, "/input", os.makedev(0, 23), flags)

    def test_exact_mountpoint_and_device_required(self):
        for mid, path, device in ((41, "/input", os.makedev(0,23)), (40, "/input/sub", os.makedev(0,23)), (40, "/input", os.makedev(0,24))):
            with self.subTest(mid=mid, path=path, device=device), self.assertRaises(m.MountError):
                m.validate_mount(self.row(), mid, path, device, os.ST_RDONLY)

    def test_nested_and_stacked_mounts_refused_even_when_readonly(self):
        for point in ("/input/sub", "/input"):
            extra = f"41 40 0:24 / {point} ro - tmpfs tmpfs rw\n"
            with self.subTest(point=point), self.assertRaisesRegex(m.MountError, "nested or stacked"):
                m.validate_mount(self.row(TABLE+extra),40,"/input",os.makedev(0,23),os.ST_RDONLY)
        sibling = "41 1 0:24 / /input-sibling rw - tmpfs tmpfs rw\n"
        m.validate_mount(self.row(TABLE+sibling),40,"/input",os.makedev(0,23),os.ST_RDONLY)

    def test_parser_escapes_and_malformed_tables(self):
        escaped = TABLE.replace("/input", r"/input\040space\134slash")
        self.assertEqual(self.row(escaped)[40]["point"], "/input space\\slash")
        for text in ("", TABLE+TABLE, TABLE.replace("ro,nosuid", "ro,rw"), TABLE.replace("/input", r"/bad\077"), TABLE.replace(" - ", " "), TABLE.replace("0:23", "bad")):
            with self.subTest(text=text), self.assertRaises(m.MountError):
                self.row(text)

    def test_real_symlink_and_traversal_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            link=Path(tmp)/"alias"
            link.symlink_to(tmp,target_is_directory=True)
            for path in (str(link), str(Path(tmp)/"missing"), str(tmp)+"/../x", "relative", "/"):
                with self.subTest(path=path), self.assertRaises((OSError,m.MountError)):
                    m.observe(path)

    def test_observe_flags_and_drift_with_real_fds_synthetic_mounts(self):
        with tempfile.TemporaryDirectory() as tmp:
            info=os.stat(tmp)
            device=f"{os.major(info.st_dev)}:{os.minor(info.st_dev)}"
            text=TABLE.replace("0:23",device).replace("/input",tmp)
            base = dict(table_text=mock.Mock(return_value=text),mount_id=mock.Mock(return_value=40))
            with mock.patch.multiple(m, **base), mock.patch.object(m.os,"fstatvfs",return_value=types.SimpleNamespace(f_flag=os.ST_RDONLY)):
                result=m.observe(tmp)
                self.assertTrue(result["readOnlyMountObserved"])
                for field in ("contentAuthenticated","immutableHostStorageAuthenticated","lifetimeSealed","workerExecutionAuthorized"):
                    self.assertIs(result[field],False)
            with mock.patch.object(m,"table_text",side_effect=[text,text+"41 1 0:24 / /other rw - tmpfs tmpfs rw\n"]), mock.patch.object(m,"mount_id",return_value=40), mock.patch.object(m.os,"fstatvfs",return_value=types.SimpleNamespace(f_flag=os.ST_RDONLY)):
                with self.assertRaisesRegex(m.MountError,"drift"):
                    m.observe(tmp)

    def test_actual_writable_temporary_input_never_passes(self):
        with tempfile.TemporaryDirectory() as tmp:
            if os.statvfs(tmp).f_flag & os.ST_RDONLY:
                self.skipTest("temporary filesystem is read-only")
            with self.assertRaises(m.MountError):
                m.observe(tmp)


if __name__ == "__main__":
    unittest.main()
