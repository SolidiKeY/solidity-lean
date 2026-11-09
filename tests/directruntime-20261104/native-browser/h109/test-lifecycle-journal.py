"""Guard H127 crash barriers with real filesystem, process and SIGKILL controls.

These tests execute no Docker or Lean and establish no cleanup/measurement pass.
"""
import importlib.util
import json
import os
import pathlib
import selectors
import signal
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

SCRIPT = pathlib.Path(__file__).with_name("lifecycle-journal.py")
spec = importlib.util.spec_from_file_location("journal", SCRIPT)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
PLAN, IMAGE = "a"*64, "sha256:"+"b"*64


class JournalControls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = pathlib.Path(self.temp.name)/"store"
        self.root.mkdir(mode=0o700)
        self.pin = m.provision(str(self.root))

    def journal(self):
        return m.Journal(str(self.root), self.pin)

    def child(self, body):
        prefix = """import importlib.util, os, sys, signal, json
s=importlib.util.spec_from_file_location("journal",sys.argv[1])
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
j=m.Journal(sys.argv[2],json.loads(sys.argv[3]))
"""
        p = subprocess.Popen([sys.executable, "-B", "-c", prefix+body, str(SCRIPT), str(self.root), json.dumps(self.pin)], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        self.addCleanup(self.kill, p)
        return p

    @staticmethod
    def kill(p):
        if p.poll() is None:
            p.kill()
        p.wait(timeout=5)
        p.stdout.close()
        p.stderr.close()

    def ready(self, p):
        with selectors.DefaultSelector() as selector:
            selector.register(p.stdout, selectors.EVENT_READ)
            self.assertTrue(selector.select(5), "child did not reach crash boundary")
        self.assertEqual(p.stdout.readline().strip(), "READY")

    def test_abort_before_creation_seals_before_release(self):
        with self.journal() as j:
            identity = j.reserve(PLAN, IMAGE)
            with self.assertRaises(m.Unresolved):
                j.reserve(PLAN, IMAGE)
            receipt = j.seal_pre_create_abort()
            self.assertFalse((self.root/"active.json").exists())
            sealed = json.loads((self.root/receipt).read_text())
            self.assertEqual(sealed["identity"], identity)
            self.assertEqual(sealed["events"][-1]["state"], "aborted-before-create")
            self.assertNotEqual(j.reserve(PLAN, IMAGE)["nonce"], identity["nonce"])

    def test_post_create_and_unknown_never_release(self):
        with self.journal() as j:
            j.reserve(PLAN, IMAGE)
            j.advance("create-intent", {})
            j.advance("create-unknown", {"approval": True})
            with self.assertRaises(m.Unresolved):
                j.seal_pre_create_abort()
            with self.assertRaises(m.Unresolved):
                j.reserve(PLAN, IMAGE)
            with self.assertRaises(m.JournalError):
                j.advance("created", {"containerId": "c"*64})

    def test_drain_observation_is_not_authenticated_cleanup(self):
        with self.journal() as j:
            j.reserve(PLAN, IMAGE)
            j.advance("create-intent", {})
            j.advance("created", {"containerId": "c"*64})
            j.advance("drain-observed", {"populated": 0, "dockerAbsent": True})
            with self.assertRaises(m.Unresolved):
                j.seal_pre_create_abort()
            self.assertTrue((self.root/"active.json").exists())

    def test_real_sigkill_after_create_intent_preserves_barrier(self):
        p = self.child("""with j:
 j.reserve("a"*64,"sha256:"+"b"*64)
 j.advance("create-intent",{})
 print("READY",flush=True)
 signal.pause()
""")
        self.ready(p)
        p.send_signal(signal.SIGKILL)
        p.wait(timeout=5)
        with self.journal() as j:
            self.assertEqual(j.read_active()["events"][-1]["state"], "create-intent")
            with self.assertRaises(m.Unresolved):
                j.reserve(PLAN, IMAGE)

    def test_sigkill_before_atomic_replace_keeps_old_barrier(self):
        p = self.child("""with j:
 j.reserve("a"*64,"sha256:"+"b"*64)
 def crash(*a,**kw):
  print("READY",flush=True)
  signal.pause()
 m.os.replace=crash
 j.advance("create-intent",{})
""")
        self.ready(p)
        p.kill(); p.wait(timeout=5)
        self.assertEqual(len(list(self.root.glob("stage-*.json"))), 1)
        with self.journal() as j:
            self.assertEqual(j.read_active()["events"][-1]["state"], "reserved")
            with self.assertRaises(m.Unresolved):
                j.reserve(PLAN, IMAGE)
            # The controller never received a committed intent, so never called Docker.
            j.seal_pre_create_abort()

    def test_sigkill_after_abort_receipt_before_unlink_is_recoverable(self):
        p = self.child("""with j:
 j.reserve("a"*64,"sha256:"+"b"*64)
 def crash(*a,**kw):
  print("READY",flush=True)
  signal.pause()
 m.os.unlink=crash
 j.seal_pre_create_abort()
""")
        self.ready(p)
        p.kill(); p.wait(timeout=5)
        self.assertEqual(len(list(self.root.glob("abort-*.json"))), 1)
        with self.journal() as j:
            j.seal_pre_create_abort()
            self.assertIsNone(j.read_active())

    def test_real_second_process_cannot_take_live_lease(self):
        with self.journal():
            p = self.child("""try:
 with j: pass
except m.Busy:
 print("READY",flush=True)
""")
            self.ready(p)
            self.assertEqual(p.wait(timeout=5), 0)

    def test_symlinks_hardlinks_fifo_and_insecure_root_refused(self):
        target = pathlib.Path(self.temp.name)/"foreign"
        target.write_bytes(b"do-not-change")
        os.chmod(target, 0o600)
        for kind in ["symlink", "hardlink", "fifo"]:
            p = self.root/"active.json"
            if kind == "symlink":p.symlink_to(target)
            elif kind == "hardlink":os.link(target, p)
            else:os.mkfifo(p, 0o600)
            with self.journal() as j:
                with self.assertRaises((m.JournalError, OSError)):
                    j.reserve(PLAN, IMAGE)
            p.unlink()
            self.assertEqual(target.read_bytes(), b"do-not-change")
        alias = pathlib.Path(self.temp.name)/"alias";alias.symlink_to(self.root, target_is_directory=True)
        with self.assertRaises(OSError):
            with m.Journal(str(alias), self.pin):pass
        os.chmod(self.root, 0o755)
        with self.assertRaises(m.JournalError):
            with self.journal():pass

    def test_replaced_directory_cannot_reset_pinned_store(self):
        with self.journal() as j:
            j.reserve(PLAN, IMAGE)
            self.root.rename(self.root.with_name("old"))
            self.root.mkdir(mode=0o700)
            with self.assertRaises(m.JournalError):j.read_active()
            with self.assertRaises(m.JournalError):
                with self.journal():pass
        self.assertTrue((self.root.with_name("old")/"active.json").exists())

    def test_replaced_lease_blocks_both_old_and_new_controllers(self):
        with self.journal() as j:
            j.reserve(PLAN, IMAGE)
            lease = self.root/"controller.lock"
            lease.rename(self.root/"original.lock")
            lease.write_bytes(b"")
            os.chmod(lease, 0o600)
            with self.assertRaises(m.JournalError):j.read_active()
            p = self.child("""try:
 with j: pass
except m.JournalError:
 print("READY",flush=True)
""")
            self.ready(p)
            self.assertEqual(p.wait(timeout=5), 0)
            with self.assertRaises(m.JournalError):m.provision(str(self.root))
            self.assertTrue((self.root/"active.json").exists())

    def test_in_place_lease_content_change_is_refused(self):
        with self.journal() as j:
            j.reserve(PLAN, IMAGE)
            lease = self.root/"controller.lock"
            lease.write_bytes(b"0"*64+b"\n")
            with self.assertRaises(m.JournalError):j.read_active()
            with self.assertRaises(m.JournalError):
                with self.journal():pass
            self.assertTrue((self.root/"active.json").exists())

    def test_corruption_clock_and_boot_drift_fail_closed(self):
        with self.journal() as j:
            j.reserve(PLAN, IMAGE)
            with mock.patch.object(m.time, "monotonic_ns", return_value=0):
                with self.assertRaises(m.JournalError):j.advance("create-intent", {})
            with mock.patch.object(m, "current_boot_id", return_value="0"*8+"-"+"0"*4+"-"+"0"*4+"-"+"0"*4+"-"+"0"*12):
                with self.assertRaises(m.Unresolved):j.advance("create-intent", {})
            (self.root/"active.json").write_bytes(b"{truncated")
            with self.assertRaises(m.JournalError):j.read_active()
            with self.assertRaises(m.JournalError):j.reserve(PLAN, IMAGE)

    def test_fsync_failure_does_not_remove_active_barrier(self):
        with self.journal() as j:
            j.reserve(PLAN, IMAGE)
            with mock.patch.object(m.os, "fsync", side_effect=OSError("injected I/O failure")):
                with self.assertRaises(OSError):j.advance("create-intent", {})
            with self.assertRaises(m.Unresolved):j.reserve(PLAN, IMAGE)

    def test_post_replace_fsync_failure_retains_create_intent(self):
        with self.journal() as j:
            j.reserve(PLAN, IMAGE)
            original = m.os.fsync
            calls = [0]
            def fail_after_replace(fd):
                calls[0] += 1
                if calls[0] == 3:
                    raise OSError("injected post-replace directory sync failure")
                return original(fd)
            with mock.patch.object(m.os, "fsync", side_effect=fail_after_replace):
                with self.assertRaises(OSError):j.advance("create-intent", {})
            self.assertEqual(j.read_active()["events"][-1]["state"], "create-intent")
            with self.assertRaises(m.Unresolved):j.seal_pre_create_abort()

    def test_fork_inherited_api_lease_is_refused(self):
        with self.journal() as j:
            j.reserve(PLAN, IMAGE)
            pid = os.fork()
            if pid == 0:
                try:
                    j.read_active()
                except m.JournalError:
                    os._exit(0)
                os._exit(1)
            _, status = os.waitpid(pid, 0)
            self.assertEqual(os.waitstatus_to_exitcode(status), 0)

    def test_conflicting_receipt_and_invalid_inputs_never_clear(self):
        with self.journal() as j:
            with self.assertRaises(m.JournalError):j.reserve("bad", IMAGE)
            self.assertFalse((self.root/"active.json").exists())
            identity = j.reserve(PLAN, IMAGE)
            name = self.root/("abort-"+identity["nonce"]+".json")
            name.write_bytes(b"{}\n");os.chmod(name, 0o600)
            with self.assertRaises(m.JournalError):j.seal_pre_create_abort()
            self.assertTrue((self.root/"active.json").exists())
            with self.assertRaises(m.JournalError):j.__enter__()


if __name__ == "__main__":
    unittest.main()
