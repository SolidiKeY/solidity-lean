"""Guard pre-create lease ownership with real private files and harmless processes.

Constants use fixture locks/stores; production reservation is never changed.
No container, worker, Lean or measurement command is run.
"""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

spec=importlib.util.spec_from_file_location("precreate",Path(__file__).with_name("precreate-controller.py"))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


class PreparationControls(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.root=Path(self.tmp.name);self.store=self.root/"store";self.store.mkdir(mode=0o700)
        self.pin=m.journal.provision(self.store);self.writer=self.root/"writer.lock";self.writer.touch()
        self.patch=mock.patch.multiple(m,WRITER=self.writer,FENCE=self.root/"fence")
        self.patch.start();self.addCleanup(self.patch.stop)

    def lease(self):return m.PreparationLease(self.store,self.pin,"a"*64,"sha256:"+"b"*64)

    def test_real_writer_and_journal_held_but_no_create_authority(self):
        with self.lease() as lease:
            result=lease.observation()
            self.assertIs(result["containerCreationAuthorized"],False)
            self.assertIs(result["workerExecutionAuthorized"],False)
            contender=subprocess.run([sys.executable,"-B","-c","import fcntl,sys;f=open(sys.argv[1],'r+');fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)",str(self.writer)],capture_output=True,timeout=3)
            self.assertNotEqual(contender.returncode,0)
            with self.assertRaises(m.journal.Busy):
                with m.journal.Journal(self.store,self.pin):pass
        self.assertEqual(json.loads((self.store/"active.json").read_text())["events"][-1]["state"],"reserved")
        with self.assertRaises(m.journal.Unresolved):
            with self.lease():pass

    def test_exception_never_implicitly_releases_reservation(self):
        with self.assertRaisesRegex(RuntimeError,"fixture"):
            with self.lease():raise RuntimeError("fixture")
        self.assertTrue((self.store/"active.json").exists())

    def test_only_explicit_precreate_abort_releases_fixture_barrier(self):
        with self.lease() as lease:
            receipt=lease.abort_pre_create()
            self.assertTrue((self.store/receipt).exists())
            self.assertFalse((self.store/"active.json").exists())
        with self.lease() as lease:lease.abort_pre_create()

    def test_postcreate_state_cannot_be_aborted(self):
        with self.lease() as lease:
            lease._journal.advance("create-intent",{})
            with self.assertRaises(m.journal.Unresolved):lease.abort_pre_create()
        self.assertEqual(json.loads((self.store/"active.json").read_text())["events"][-1]["state"],"create-intent")

    def test_existing_fence_denies_before_journal_mutation(self):
        m.FENCE.write_text("unknown or historical reservation")
        with self.assertRaises(m.journal.Unresolved):
            with self.lease():pass
        self.assertFalse((self.store/"active.json").exists())

    def test_deadline_denies_work_but_known_precreate_abort_can_finish(self):
        with self.lease() as lease:
            with mock.patch.object(m.time,"monotonic_ns",return_value=lease._deadline):
                with self.assertRaises(TimeoutError):lease.observation()
                lease.abort_pre_create()
        self.assertFalse((self.store/"active.json").exists())

    def test_durable_reserve_overrun_never_returns_admission_or_drops_barrier(self):
        lease=self.lease();real=lease._journal.reserve
        def expires_during_reserve(*args):
            result=real(*args);lease._deadline=0;return result
        with mock.patch.object(lease._journal,"reserve",side_effect=expires_during_reserve),self.assertRaisesRegex(TimeoutError,"durable reservation"):
            with lease:self.fail("late admission returned")
        self.assertIsNone(lease._writer);self.assertIsNone(lease._journal.fd)
        with m.journal.Journal(self.store,self.pin) as held:
            self.assertEqual(held.read_active()["events"][-1]["state"],"reserved")

    def test_writer_replacement_and_fork_use_refused(self):
        with self.lease() as lease:
            with mock.patch.object(m.os,"getpid",return_value=-1),self.assertRaises(m.journal.JournalError):lease.observation()
            self.writer.rename(self.root/"old-writer");self.writer.touch()
            with self.assertRaisesRegex(m.journal.JournalError,"replaced"):lease.observation()
        self.assertTrue((self.store/"active.json").exists())


if __name__=="__main__":unittest.main()
