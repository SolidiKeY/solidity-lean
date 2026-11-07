"""Guard gate admission against unlocked work and forged resource environment flags.

No Lean, Docker, MCP or actual replay. Positive scope values are fixtures;
real process tests use a harmless fixed shell body and real advisory lease.
"""
import fcntl
import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

SCRIPT=Path(__file__).with_name("validation-admission.py").resolve()
spec=importlib.util.spec_from_file_location("admission",SCRIPT)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)


class AdmissionControls(unittest.TestCase):
    def test_entry_import_caches_disabled_before_admission(self):
        self.assertTrue(m.sys.dont_write_bytecode)
        self.assertEqual(os.environ.get("PYTHONDONTWRITEBYTECODE"),"1")
        for rel in m.ENTRIES.values():
            self.assertIn("exec python3 -B ",(m.ROOT/rel).read_text())

    def test_real_entry_refuses_without_scope_before_mutations(self):
        for rel in m.ENTRIES.values():
            with tempfile.TemporaryDirectory() as tmp:
                env=dict(os.environ,NATIVE_BROWSER_BOUNDED_GATE="",LEAN_NUM_THREADS="1")
                result=subprocess.run(["bash",str(m.ROOT/rel)],cwd=m.ROOT,env=env,capture_output=True,text=True,timeout=3)
                self.assertNotEqual(result.returncode,0)
                self.assertIn("bounded-command admission",result.stderr)

    def test_numeric_scope_and_reserve_checks_cannot_be_bypassed_by_flag(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);scope=root/"scope";outer=root/"outer";scope.mkdir();outer.mkdir()
            values={scope/"memory.max":"12884901888",scope/"memory.swap.max":"0",scope/"cpu.max":"100000 100000",outer/"memory.max":"17179869184",outer/"memory.current":"1000000"}
            for p,value in values.items():p.write_text(value)
            with mock.patch.multiple(m,CGROUP=scope,OUTER=outer),mock.patch.object(m.os,"sched_getaffinity",return_value={0}),mock.patch.dict(os.environ,NATIVE_BROWSER_BOUNDED_GATE="1",LEAN_NUM_THREADS="1"):
                m.resources()
                for p,bad in ((scope/"memory.max","max"),(scope/"memory.swap.max","max"),(scope/"cpu.max","200000 100000"),(outer/"memory.current","17179869184")):
                    p.write_text(bad)
                    with self.subTest(path=p),self.assertRaises(RuntimeError):m.resources()
                    p.write_text(values[p])
                with mock.patch.object(m.os,"sched_getaffinity",return_value={0,1}):m.resources()
                with mock.patch.object(m.os,"sched_getaffinity",return_value=set()),self.assertRaises(RuntimeError):m.resources()

    def test_real_writer_lease_blocks_recipe_until_release(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);lock=root/"writer.lock";ready=root/"ready";ran=root/"ran"
            (root/"recipe.sh").write_text(m.MARKER+"if flock -n writer.lock -c true; then exit 91; fi\ntouch ran\n")
            timer=root/"tests/directruntime-20261104/native-browser/readbounds/invocation-deadline.py"
            timer.parent.mkdir(parents=True)
            timer.write_bytes((m.ROOT/"tests/directruntime-20261104/native-browser/readbounds/invocation-deadline.py").read_bytes())
            launcher=root/"launcher.py"
            launcher.write_text("import importlib.util,sys\nfrom pathlib import Path\ns=importlib.util.spec_from_file_location('a',sys.argv[1]);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)\nm.ROOT=Path.cwd();m.LOCK=m.ROOT/'writer.lock';m.ENTRIES={'registration-parent':'recipe.sh'}\nm.resources=lambda:None;m.serial_setup=lambda:None\nsys.argv=[sys.argv[0],'registration-parent'];Path('ready').touch();m.main()\n")
            with lock.open("w") as held:
                fcntl.flock(held,fcntl.LOCK_EX)
                child=subprocess.Popen([sys.executable,str(launcher),str(SCRIPT)],cwd=root,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
                try:
                    deadline=time.monotonic()+3
                    while not ready.exists():
                        if child.poll() is not None or time.monotonic()>deadline:self.fail("admission fixture did not reach lease")
                        time.sleep(.01)
                    time.sleep(.05)
                    self.assertIsNone(child.poll());self.assertFalse(ran.exists())
                    fcntl.flock(held,fcntl.LOCK_UN)
                    _,stderr=child.communicate(timeout=3)
                    self.assertEqual(child.returncode,0,stderr.decode());self.assertTrue(ran.exists())
                finally:
                    if child.poll() is None:child.kill();child.wait()
                    child.stdout.close();child.stderr.close()

    def test_writer_wait_counts_toward_fixed_local_deadline(self):
        with tempfile.TemporaryDirectory() as tmp:
            lock=Path(tmp)/"writer.lock"
            with lock.open("w") as held:
                fcntl.flock(held,fcntl.LOCK_EX)
                with mock.patch.object(m,"LOCK",lock),mock.patch.object(m,"resources"),mock.patch.object(m.time,"monotonic_ns",side_effect=[0,300_000_000_001]),mock.patch.object(sys,"argv",[str(SCRIPT),"registration-parent"]),mock.patch.object(m.subprocess,"Popen") as spawn:
                    with self.assertRaisesRegex(TimeoutError,"writer-lease deadline"):
                        m.main()
                    spawn.assert_not_called()

    def test_recipe_and_cached_shim_drift_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            with mock.patch.object(m,"ROOT",root),mock.patch.object(m,"ENTRIES",{"fixture":"recipe"}):
                (root/"recipe").write_text("missing delimiter")
                with self.assertRaisesRegex(ValueError,"delimiter"):m.recipe("fixture")
                (root/"lakefile.toml").write_text('weakLeanArgs = ["--tstack=131072"]')
                (root/".lake").mkdir();(root/".lake/native-browser-serial.toml").write_text("stale")
                with self.assertRaisesRegex(RuntimeError,"serial Lake"):m.serial_setup()


if __name__=="__main__":unittest.main()
