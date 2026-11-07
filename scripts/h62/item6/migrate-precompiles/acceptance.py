#!/usr/bin/env python3
"""Executable negative controls for source census and build-status evidence.
Uses fake compiler subprocesses only; these tests are not Lean proofs.
"""
import fcntl,importlib.util,json,os,shutil,signal,subprocess,tempfile,time
from pathlib import Path
from unittest.mock import patch
ROOT=Path.cwd(); HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location("census",HERE/"census.py"); c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
base=c.census(ROOT)
assert base["migration_matches"] and len(base["files"])==11 and len(base["topological_closure"])==16
point=next(x for x in base["files"] if x["path"].endswith("PointEval.lean"))
assert all(any(("def "+name+" ") in d["source"] for d in point["declarations"]) for name in ("decode","verifies"))
osaka=next(x for x in base["files"] if x["path"].endswith("Osaka.lean"))
assert sum(g["source"].startswith("#guard_msgs") for g in osaka["guards"])==3
with tempfile.TemporaryDirectory(prefix="h62-controls-",dir="/workspace/h62-migrate-precompiles") as td:
    temp=Path(td); tree=temp/"tree";tree.mkdir()
    for m in base["topological_closure"]:
        rel=m.replace(".","/")+".lean"; dest=tree/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/rel,dest)
    original=subprocess.check_output
    def show(cmd,**kw): return original(cmd,cwd=ROOT)
    with patch.object(c.subprocess,"check_output",side_effect=show):
        for entry in base["files"]:
            p=tree/entry["path"]; data=p.read_bytes();p.write_bytes(data+b"\n-- changed source negative control\n")
            assert not c.census(tree)["migration_matches"],p
            p.write_bytes(data)
        missing=tree/base["files"][0]["path"];data=missing.read_bytes();missing.unlink()
        try:c.census(tree);raise AssertionError("missing module passed")
        except ValueError:pass
        missing.write_bytes(data)
        extra=tree/"Solidity/Precompiles/Unexpected.lean";extra.touch()
        try:c.census(tree);raise AssertionError("extra module passed")
        except ValueError:pass
        extra.unlink()
        field=tree/"Solidity/Precompiles/Field.lean";data=field.read_bytes();field.write_bytes(b"import Solidity.Precompiles.Basic\n"+data)
        try:c.census(tree);raise AssertionError("cycle passed")
        except ValueError:pass
    tc=temp/"fake";(tc/"bin").mkdir(parents=True)
    fake="""#!/usr/bin/env python3
import os,sys,time
from pathlib import Path
if '--version' in sys.argv:print('FAKE TEST COMPILER');raise SystemExit(0)
if os.environ.get('H62_FAKE_PID_FILE'):Path(os.environ['H62_FAKE_PID_FILE']).write_text(str(os.getpid()))
if os.environ.get('H62_FAKE_HOLD'):time.sleep(30)
time.sleep(0.3)
if os.environ.get('H62_FAKE_FAIL') and sys.argv[-1].endswith('Roadmap/Evm.lean'):raise SystemExit(7)
if not os.environ.get('H62_FAKE_NO_OUTPUT'):Path(sys.argv[sys.argv.index('-o')+1]).write_bytes(b'fake')
"""
    for exe in ("lean","lake"):
        p=tc/"bin"/exe;p.write_text(fake);p.chmod(0o755)
    runner=["python3",str(HERE/"bounded-build.py"),"--toolchain",str(tc),"--out"]
    for label,env,status in (("fail",dict(H62_FAKE_FAIL="1"),"fail"),("no-output",dict(H62_FAKE_NO_OUTPUT="1"),"fail"),("success",{},"pass")):
        out=temp/label
        proc=subprocess.Popen(runner+[str(out)],stdout=subprocess.DEVNULL,stderr=subprocess.PIPE,env=dict(os.environ,**env))
        observed=False
        while proc.poll() is None:
            report=out/"summary.json"
            if report.exists():
                try:s=json.loads(report.read_text())
                except json.JSONDecodeError:continue
                if s["completed_modules"]<len(s["expected_modules"]):
                    assert s["status"]!="pass";observed=True
            time.sleep(0.02)
        assert proc.returncode==(0 if status=="pass" else 1),proc.stderr.read().decode()
        s=json.loads((out/"summary.json").read_text());assert s["status"]==status
        if status=="pass":assert observed and s["completed_modules"]==16
        repeat=subprocess.run(runner+[str(out)],capture_output=True)
        assert repeat.returncode!=0 and b"output exists" in repeat.stderr
    pid_file=temp/"child.pid"
    proc=subprocess.Popen(runner+[str(temp/"parent-death")],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,
        env=dict(os.environ,H62_FAKE_PID_FILE=str(pid_file),H62_FAKE_HOLD="1"))
    deadline=time.monotonic()+10
    while not pid_file.exists():
        assert proc.poll() is None and time.monotonic()<deadline
        time.sleep(0.02)
    child_pid=int(pid_file.read_text())
    try:
        proc.terminate();proc.wait(timeout=5)
        with open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a") as lock:
            try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);raise AssertionError("child lost inherited lock")
            except BlockingIOError:pass
    finally:
        os.killpg(child_pid,signal.SIGKILL)
    with open("/tmp/solidity-lean-feature-groups-20261025/writer.lock","a") as lock:
        deadline=time.monotonic()+5
        while True:
            try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);break
            except BlockingIOError:
                assert time.monotonic()<deadline;time.sleep(0.02)
print('PASS: 11 source-mutation controls; missing/extra/cyclic inventory; attributed declarations; guard_msgs; partial/failure/missing-olean/full-build status; nonempty-cache refusal; inherited lock survives parent death')
