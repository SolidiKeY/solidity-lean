#!/usr/bin/env python3
"""No Lean/build: actual bounded Bash fence tests and unchanged guard controls.
The completion busywait has no fork/exec helpers; production timeout stays10s.
"""
import subprocess,tempfile,time,unittest,importlib.util,sys,os,signal
from pathlib import Path
sys.dont_write_bytecode=True
root=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('observe',root/'scripts/roadmap-v15-bounded-observe.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
class Fence(unittest.TestCase):
 def test_source_only_postworkload_changed(self):
  s=(root/'scripts/roadmap-v15-bounded-observe.py').read_text()
  self.assertIn("'until test -e '+shlex.quote(str(ackPath))+'; do :; done')",s)
  self.assertIn('timeout 10 bash -c ',s)
  self.assertIn('do sleep 0.05; done',s) # startup remains unchanged
 def fence(self,code,ack):
  with tempfile.TemporaryDirectory() as d:
   marker=Path(d)/'done';ready=Path(d)/'ack'
   command='printf "%s\n" "$1" > "$2"; until test -e "$3"; do :; done; exit "$1"'
   p=subprocess.Popen(['timeout','10','bash','-c',command,'fence',str(code),str(marker),str(ready)],start_new_session=True)
   try:
    deadline=time.monotonic()+2
    while not marker.exists() and time.monotonic()<deadline:time.sleep(.005)
    self.assertTrue(marker.exists());self.assertEqual(marker.read_text(),str(code)+'\n')
    if ack:ready.touch()
    self.assertEqual(p.wait(timeout=12),code if ack else 124)
   finally:
    try:os.killpg(p.pid,signal.SIGKILL)
    except ProcessLookupError:pass
    p.wait(timeout=2)
 def test_success(self):self.fence(0,True)
 def test_failure(self):self.fence(7,True)
 def test_missing_ack_deadline(self):self.fence(0,False)
if __name__=='__main__':unittest.main()
