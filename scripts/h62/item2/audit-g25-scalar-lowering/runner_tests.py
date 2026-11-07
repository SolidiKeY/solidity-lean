#!/usr/bin/env python3
"""An exceptional memory guard must not orphan its real subprocess."""
import os
import contextlib
import io
import json
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
import bounded_lean


class RunnerTests(unittest.TestCase):
    def test_quoted_module_path(self):
        self.assertEqual(bounded_lean.module_name("tests.«audit-g25».Witness"), "tests.audit-g25.Witness")
        with self.assertRaises(ValueError): bounded_lean.module_name("tests.«bad.path».Witness")

    def test_cache_invalidation_and_direct_import_guard(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)
            (root/"Dependency.lean").write_text("namespace Dependency\nend Dependency\n")
            (root/"Fixture.lean").write_text("import Dependency\n")
            (root/"bin").mkdir(); (root/"lib").mkdir()
            lean=root/"bin"/"lean"
            lean.write_text("#!/usr/bin/env python3\nimport sys\nfrom pathlib import Path\np=Path(__file__).parent.parent/'invocations'\np.write_text(p.read_text()+'x' if p.exists() else 'x')\nPath(sys.argv[sys.argv.index('-o')+1]).write_bytes(b'fake-test-output')\n")
            lean.chmod(0o755)
            argv=["bounded_lean.py","--repo",str(root),"--toolchain",str(root),"--artifacts",str(root/"artifacts"),"--reuse","Fixture"]
            previous={sig:signal.getsignal(sig) for sig in (signal.SIGINT,signal.SIGTERM)}
            def run(direct=False):
                with patch.object(sys,"argv",argv+(["--direct"] if direct else [])), contextlib.redirect_stdout(io.StringIO()):
                    bounded_lean.main()
            def count(): return len((root/"invocations").read_text())
            try:
                run(); self.assertEqual(count(),2)
                run(); self.assertEqual(count(),2)
                (root/"Dependency.lean").write_text("-- changed\nnamespace Dependency\nend Dependency\n")
                with self.assertRaisesRegex(RuntimeError,"validated import receipt"): run(True)
                run(); self.assertEqual(count(),4)
                dep=root/"artifacts/lib/lean/Dependency.olean"
                dep.write_bytes(b"corrupted")
                with self.assertRaisesRegex(RuntimeError,"validated import receipt"): run(True)
                run(); self.assertEqual(count(),5)
                index=json.loads((root/"artifacts/cache-index.json").read_text())
                Path(index['Dependency']['receipt']).unlink()
                with self.assertRaisesRegex(RuntimeError,"validated import receipt"): run(True)
                run(); self.assertEqual(count(),6)
                (root/"lib/core.olean").write_bytes(b"distribution-change")
                run(); self.assertEqual(count(),8)
            finally:
                for sig,handler in previous.items(): signal.signal(sig,handler)

    def test_direct_rejects_multiple_targets(self):
        argv=["bounded_lean.py","--toolchain","/unused","--artifacts","/unused","--direct","A","B"]
        previous={sig:signal.getsignal(sig) for sig in (signal.SIGINT,signal.SIGTERM)}
        try:
            with patch.object(sys,"argv",argv), contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as error: bounded_lean.main()
            self.assertEqual(error.exception.code,2)
        finally:
            for sig,handler in previous.items(): signal.signal(sig,handler)

    def test_keep_going_checks_independent_modules_but_blocks_clients(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); (root/"bin").mkdir()
            (root/"Bad.lean").write_text("-- fixture\n")
            (root/"Good.lean").write_text("-- fixture\n")
            (root/"Both.lean").write_text("import Bad\nimport Good\n")
            lean=root/"bin/lean"
            lean.write_text("#!/usr/bin/env python3\nimport sys\nfrom pathlib import Path\nif Path(sys.argv[-1]).stem == 'Bad': sys.exit(1)\nPath(sys.argv[sys.argv.index('-o')+1]).write_bytes(b'fixture-output')\n")
            lean.chmod(0o755)
            argv=["bounded_lean.py","--repo",str(root),"--toolchain",str(root),"--artifacts",str(root/"artifacts"),"--keep-going","Both"]
            previous={sig:signal.getsignal(sig) for sig in (signal.SIGINT,signal.SIGTERM)}
            try:
                with patch.object(sys,"argv",argv),contextlib.redirect_stdout(io.StringIO()):
                    with self.assertRaises(SystemExit) as error: bounded_lean.main()
                self.assertEqual(error.exception.code,1)
                rows=json.loads((root/"artifacts/results.json").read_text())
                self.assertEqual([(r['module'],r['exit']) for r in rows],[('Bad',1),('Good',0),('Both',None)])
                self.assertEqual(rows[-1]['status'],'blocked-import')
                self.assertFalse((root/"artifacts/lib/lean/Both.olean").exists())
            finally:
                for sig,handler in previous.items(): signal.signal(sig,handler)

    def test_emitted_evidence_is_fresh_and_tampering_invalidates_reuse(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/"bin").mkdir();(root/"evidence").mkdir()
            (root/"Fixture.lean").write_text("-- fixture\n")
            evidence=root/"evidence/produced.json";evidence.write_text("stale")
            lean=root/"bin/lean"
            lean.write_text("#!/usr/bin/env python3\nimport sys\nfrom pathlib import Path\np=Path(__file__).parent.parent\n(p/'evidence/produced.json').write_text('fresh')\nPath(sys.argv[sys.argv.index('-o')+1]).write_bytes(b'fixture-output')\n")
            lean.chmod(0o755)
            argv=["bounded_lean.py","--repo",str(root),"--toolchain",str(root),"--artifacts",str(root/"artifacts"),"--reuse","--evidence","Fixture="+str(evidence),"Fixture"]
            previous={sig:signal.getsignal(sig) for sig in (signal.SIGINT,signal.SIGTERM)}
            def run():
                with patch.object(sys,"argv",argv),contextlib.redirect_stdout(io.StringIO()): bounded_lean.main()
                return json.loads((root/"artifacts/results.json").read_text())[0]
            try:
                self.assertFalse(run()['cache_hit']);self.assertEqual(evidence.read_text(),'fresh')
                self.assertTrue(run()['cache_hit'])
                evidence.write_text('forged-witness-type-False')
                self.assertFalse(run()['cache_hit']);self.assertEqual(evidence.read_text(),'fresh')
                evidence.unlink();self.assertFalse(run()['cache_hit'])
                self.assertTrue(list((root/"artifacts/emitted-history/Fixture").iterdir()))
            finally:
                for sig,handler in previous.items(): signal.signal(sig,handler)

    def test_guard_exception_terminates_and_reaps_child(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root/"Fixture.lean").write_text("namespace Fixture\nend Fixture\n")
            (root/"bin").mkdir()
            lean = root/"bin"/"lean"
            lean.write_text("#!/usr/bin/env python3\nimport time\ntime.sleep(30)\n")
            lean.chmod(0o755)
            children = []
            real_popen = subprocess.Popen
            def spawn(*args, **kwargs):
                child = real_popen(*args, **kwargs)
                children.append(child)
                return child
            argv = ["bounded_lean.py", "--repo", str(root), "--toolchain", str(root),
                    "--artifacts", str(root/"artifacts"), "Fixture"]
            old_handlers = {s: signal.getsignal(s) for s in (signal.SIGINT, signal.SIGTERM)}
            try:
                with patch.object(sys, "argv", argv), \
                     patch("bounded_lean.available", side_effect=[8*1024**3, RuntimeError("swap detected")]), \
                     patch("bounded_lean.subprocess.Popen", side_effect=spawn):
                    with self.assertRaisesRegex(RuntimeError, "swap detected"):
                        bounded_lean.main()
                self.assertEqual(len(children), 1)
                self.assertIsNotNone(children[0].poll())
                with self.assertRaises(ChildProcessError): os.waitpid(children[0].pid, os.WNOHANG)
            finally:
                for s, handler in old_handlers.items(): signal.signal(s, handler)
                for child in children: bounded_lean.terminate(child)

class ScopeRegressionTests(unittest.TestCase):
    def test_interrupt_during_popen_creation_still_reaps(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/"bin").mkdir()
            (root/"Fixture.lean").write_text("-- fixture\n")
            tool=root/"bin/lean";tool.write_text("#!/usr/bin/env python3\nimport time;time.sleep(30)\n");tool.chmod(0o755)
            children=[];original=subprocess.Popen
            def spawn(*a,**kw):
                proc=original(*a,**kw);children.append(proc)
                bounded_lean.interrupted(signal.SIGTERM,None)
                return proc
            argv=["bounded_lean.py","--repo",str(root),"--toolchain",str(root),"--artifacts",str(root/"cache"),"Fixture"]
            handlers={sig:signal.getsignal(sig) for sig in (signal.SIGTERM,signal.SIGINT)}
            try:
                with patch.object(sys,"argv",argv),patch("bounded_lean.subprocess.Popen",side_effect=spawn):
                    with self.assertRaises(SystemExit) as stopped: bounded_lean.main()
                self.assertEqual(stopped.exception.code,143)
                self.assertEqual(len(children),1)
                self.assertIsNotNone(children[0].poll())
                self.assertFalse((root/"cache/cache-index.json").exists())
            finally:
                for sig,handler in handlers.items():signal.signal(sig,handler)
                for proc in children: bounded_lean.terminate(proc)

    def test_late_completion_is_rejected(self):
        self.assertFalse(bounded_lean.deadline_expired(1,300.999))
        self.assertTrue(bounded_lean.deadline_expired(1,301))
        self.assertTrue(bounded_lean.deadline_expired(1,301.001))

    def test_detached_child_is_terminated_and_reaped(self):
        bounded_lean.subreaper()
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/"child.pid"
            code=("import subprocess,sys;from pathlib import Path;"
                  "p=subprocess.Popen([sys.executable,'-c','import time;time.sleep(30)'],start_new_session=True);"
                  "Path(sys.argv[1]).write_text(str(p.pid));p.wait()")
            proc=subprocess.Popen([sys.executable,"-c",code,str(path)],start_new_session=True)
            deadline=time.monotonic()+5
            try:
                while not path.exists() and time.monotonic()<deadline: time.sleep(.01)
                self.assertTrue(path.exists())
                child=int(path.read_text())
                bounded_lean.workload_rss_kib(proc)
                bounded_lean.terminate(proc)
                self.assertIsNotNone(proc.poll())
                self.assertFalse(Path(f"/proc/{child}").exists())
            finally: bounded_lean.terminate(proc)

    def test_separate_child_sessions_are_counted(self):
        rows = {1:(0,1,100), 2:(1,2,200), 3:(2,3,300), 4:(0,4,400)}
        self.assertEqual(bounded_lean.scoped_pids(rows, 1), {1,2,3})
        self.assertEqual(sum(rows[p][2] for p in bounded_lean.scoped_pids(rows,1)),600)

if __name__ == "__main__": unittest.main()
