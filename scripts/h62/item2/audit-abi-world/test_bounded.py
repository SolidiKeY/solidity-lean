#!/usr/bin/env python3
"""Exercise resourceguard lifecycle using isolated fake workers, never Lean."""
import argparse
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time

parser=argparse.ArgumentParser()
parser.add_argument("--evidence",type=Path,required=True)
args=parser.parse_args()
launcher=Path(__file__).with_name("bounded.py").resolve()

def gone(pid):
    return not Path(f"/proc/{pid}").exists()

def run_case(folder,name,program,expected,timeout=10,cancel=False):
    receipt=folder/(name+".json")
    pidfile=folder/(name+".pid")
    code=program.replace("PIDFILE",repr(str(pidfile)))
    command=[sys.executable,"-B",str(launcher),"--receipt",str(receipt),"--timeout",str(timeout),"--",sys.executable,"-c",code]
    process=subprocess.Popen(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
    if cancel:
        deadline=time.monotonic()+5
        while not pidfile.exists() and time.monotonic()<deadline: time.sleep(0.02)
        assert pidfile.exists(), "worker did not start"
        process.send_signal(signal.SIGTERM)
    stdout,stderr=process.communicate(timeout=15)
    report=json.loads(receipt.read_text())
    assert report["reason"] == expected,(name,report,stderr)
    assert (process.returncode==0) == (expected is None),(name,process.returncode,stderr)
    assert report["cleanup_complete"] is True and report["subreaper"] is True
    if pidfile.exists():
        for pid in json.loads(pidfile.read_text()): assert gone(pid),(name,"surviving worker",pid)
    print(name+": pass")
    shutil.copyfile(receipt,args.evidence/("guard-test-"+name+".json"))

with tempfile.TemporaryDirectory(prefix="guard-tests-",dir=args.evidence) as directory:
    folder=Path(directory)
    run_case(folder,"normal","pass",None)
    child="import time; time.sleep(30)"
    orphan="import subprocess,sys,json; from pathlib import Path; p=subprocess.Popen([sys.executable,'-c',"+repr(child)+"]); Path(PIDFILE).write_text(json.dumps([p.pid]))"
    run_case(folder,"orphan",orphan,"launcher exited with live descendants")
    sleeping=orphan+"; import time; time.sleep(30)"
    run_case(folder,"timeout",sleeping,"bounded timeout",timeout=0.5)
    run_case(folder,"cancel",sleeping,"cancelled",cancel=True)
    # Give Python the executable basename 'lean' solely to test process
    # classification. It does no proof work and is removed with the temp dir.
    fake=folder/"lean";shutil.copyfile(sys.executable,fake);fake.chmod(0o755)
    parallel="import subprocess,json,time,os,sys; from pathlib import Path; workers=[subprocess.Popen(["+repr(str(fake))+",'-c','import time;time.sleep(30)','fixture.lean'],env=dict(os.environ,PYTHONHOME=sys.prefix)) for _ in range(2)]; Path(PIDFILE).write_text(json.dumps([p.pid for p in workers])); time.sleep(30)"
    run_case(folder,"parallel",parallel,"parallel heavy Lean jobs detected")
