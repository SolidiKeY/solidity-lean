#!/usr/bin/env python3
"""Serial clean per-file elaboration; no shared Lake cache or source edits.
Pass a toolchain directory and a NEW absolute evidence directory. Uses the
repository per-file command (lake env lean), explicit -j1, and a 12 GiB address
space ceiling. Refuses swap and stops at <4 GiB effective memory headroom.
"""
import argparse, hashlib, json, os, pathlib, resource, signal, subprocess, time
ap = argparse.ArgumentParser()
ap.add_argument("toolchain", type=pathlib.Path)
ap.add_argument("output", type=pathlib.Path)
ap.add_argument("--pinned-base", action="store_true", help="native snapshot sources from the pinned base")
ap.add_argument("--production-extra", action="store_true")
ap.add_argument("--fixture", action="store_true")
ap.add_argument("--lake-overlay", action="store_true", help="clean canonical-name private Lake/native build")
ap.add_argument("--extra", action="store_true", help="check API inventory and finite controls after fixtures")
a = ap.parse_args()
a.toolchain = a.toolchain.resolve()
a.output = a.output.resolve()
a.output.mkdir(parents=True, exist_ok=False)
root = pathlib.Path.cwd()
cap = 12 * 1024**3
reserve = 4 * 1024**3

def available():
    mem = {x.split(":")[0]: int(x.split()[1])*1024 for x in pathlib.Path("/proc/meminfo").read_text().splitlines()}
    if mem["SwapTotal"]: raise RuntimeError("swap configured; refusing")
    cg = pathlib.Path("/sys/fs/cgroup")
    maximum = (cg/"memory.max").read_text().strip()
    free = mem["MemAvailable"]
    if maximum != "max": free = min(free, int(maximum)-int((cg/"memory.current").read_text()))
    return free

def limits():
    resource.setrlimit(resource.RLIMIT_AS, (cap, cap))
    os.setsid()

env = dict(os.environ, PATH=str(a.toolchain/"bin")+":"+os.environ["PATH"],
           LEAN_NUM_THREADS="1", LEAN_PATH=str(a.output/"lib"),
           XDG_CACHE_HOME=str(a.output/"cache"))
records = []
for exe in ("lean", "lake"):
    records.append({"command":[str(a.toolchain/"bin"/exe),"--version"],
                    "output":subprocess.check_output([str(a.toolchain/"bin"/exe),"--version"],text=True)})
(a.output/"versions.json").write_text(json.dumps(records, indent=2)+"\n")
records = []
workdir = root
if a.lake_overlay:
    assert not a.extra
    workdir = a.output/"source"
    for name in ("KeySort", "Hash/CollisionBound", "Hash/Adaptive"):
        path = "Solidity/"+name+".lean"
        source = root/path
        if a.fixture and name.startswith("Hash/"):
            source = root/"tests/h62/item6/migrate-hash"/(name.split("/")[-1]+".lean")
        text = (subprocess.check_output(["git","show","c6f550e281a7e5affa9a99bc2cdaed556dec00e4:"+path],text=True) if a.pinned_base else source.read_text()).replace("import tests.h62.item6.«migrate-hash».CollisionBound", "import Solidity.Hash.CollisionBound")
        dest = workdir/path
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(text)
    (workdir/"lakefile.toml").write_text('name = "hash-migration"\nversion = "0.1.0"\nenableArtifactCache = false\n[[lean_lib]]\nname = "Solidity"\nroots = ["Solidity.KeySort", "Solidity.Hash.CollisionBound", "Solidity.Hash.Adaptive"]\nweakLeanArgs = ["--tstack=131072", "-j1"]\n')
modules = ("Solidity.KeySort", "Solidity.Hash.CollisionBound", "Solidity.Hash.Adaptive")
if a.fixture and not a.lake_overlay:
    modules = ("Solidity.KeySort", "tests.h62.item6.migrate-hash.CollisionBound", "tests.h62.item6.migrate-hash.Adaptive")
if a.extra:
    assert a.fixture, "--extra requires --fixture"
    modules += ("tests.h62.item6.migrate-hash.Inventory", "tests.h62.item6.migrate-hash.Controls")
if a.production_extra:
    assert not a.fixture and not a.lake_overlay
    modules += ("tests.h62.item6.migrate-hash.ProductionInventory", "tests.h62.item6.migrate-hash.ProductionControls")
if a.pinned_base: assert a.lake_overlay and not a.fixture
source_hashes = {}
for module in modules:
    path = module.replace(".", "/")+".lean"
    data = (workdir/path).read_bytes()
    source_hashes[path] = hashlib.sha256(data).hexdigest()
    snapshot = a.output/"inputs"/path
    snapshot.parent.mkdir(parents=True, exist_ok=True)
    snapshot.write_bytes(data)
(a.output/"settings.json").write_text(json.dumps({"repository":str(root),"source_sha256":source_hashes,"head":subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip(),"address_space_cap":cap,"reserve":reserve,"threads":1,"tstack":131072,"timeout_seconds":300,"swap_total_bytes":0,"private_cache":env["XDG_CACHE_HOME"],"initial_headroom":available()},indent=2)+"\n")
for module in modules:
    if available() < reserve: raise RuntimeError("insufficient available headroom")
    source = module.replace(".", "/")+".lean"
    dest = a.output/"lib"/(module.replace(".", "/")+".olean")
    dest.parent.mkdir(parents=True, exist_ok=True)
    cmd = [str(a.toolchain/"bin"/"lake"),"env","lean","--tstack=131072","-j1", "-o",str(dest), source]
    if a.lake_overlay:
        cmd = [str(a.toolchain/"bin"/"lake"),"--no-cache","-v","build",module+":o"]
    start = time.monotonic()
    with (a.output/(module+".log")).open("w") as log:
        child = subprocess.Popen(cmd,
                                 env=env, cwd=workdir, stdout=log, stderr=subprocess.STDOUT, preexec_fn=limits)
        stopped = False
        try:
            while True:
                pid, status, usage = os.wait4(child.pid, os.WNOHANG)
                if pid: break
                if available() < reserve or time.monotonic()-start > 300:
                    stopped = True
                    # Immediate process-group kill ensures no ignored TERM can hang.
                    os.killpg(child.pid, signal.SIGKILL)
                    _, status, usage = os.wait4(child.pid, 0)
                    break
                time.sleep(0.02)
            code = os.waitstatus_to_exitcode(status)
            child.returncode = code
        finally:
            if child.returncode is None:
                try: os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError: pass
                child.wait()
    records.append({"module":module,"command":cmd,"exit":code,"wall_seconds":time.monotonic()-start,"resource_stop":stopped,"input_unchanged":all(hashlib.sha256((workdir/path).read_bytes()).hexdigest()==digest for path,digest in source_hashes.items()),"max_rss_kib":usage.ru_maxrss,"user_seconds":usage.ru_utime,"system_seconds":usage.ru_stime})
    (a.output/"results.json").write_text(json.dumps(records,indent=2)+"\n")
    print(json.dumps(records[-1]), flush=True)
    if code or stopped: raise SystemExit(code or 125)
