#!/usr/bin/env python3
"""Serial import-closure build/probe; NOT run-lean.sh/full acceptance.
Use --lean-arts for matching library .olean/.ilean/C output facets.
One Lean process (-j1), no artifact-cache restores, 12GiB aggregate RSS guard,
4GiB available-memory reserve, existing 16GiB hard VM cap. Virtual stack
reservations are not constrained as though they were resident memory.
Logs and measurements live outside Git. Stop on first failed dependency.
"""
import argparse, fcntl, json, os, resource, signal, subprocess, sys, time
sys.dont_write_bytecode = True
from pathlib import Path
from census import census
GIB = 1024**3

def handle_termination(signum, frame):
    raise InterruptedError("termination signal " + str(signum))

def signal_group(proc, signum):
    try: os.killpg(proc.pid, signum)
    except ProcessLookupError: pass

def limits():
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

def build(root, toolchain, output, fixtures=(), prebuilt_lib=None, lean_arts=False):
    if prebuilt_lib is not None and len(fixtures) != 1: raise SystemExit("prebuilt imports are permitted only for one explicitly named fixture/probe")
    if output.exists(): raise SystemExit("refusing non-clean output directory")
    output.mkdir(parents=True)
    data = census(root)
    by_name = {}
    for top in [root / "Solidity", root / "vendor/LeanTeX"]:
        for path in top.rglob("*.lean"):
            name = str(path.relative_to(top if top.name == "LeanTeX" else root)).removesuffix(".lean").replace("/", ".")
            by_name[name] = path
    from census import imports
    ordered, seen, active = [], set(), set()
    forced = {str(f).removesuffix(".lean").replace("/", ".") for f in fixtures}
    def visit(name):
        if name in seen or name not in by_name: return
        if name not in forced and prebuilt_lib is not None and (prebuilt_lib / (name.replace(".", "/") + ".olean")).exists(): return
        if name in active: raise RuntimeError("import cycle: " + name)
        active.add(name)
        for imp in imports(by_name[name].read_text()): visit(imp)
        active.remove(name); seen.add(name); ordered.append(name)
    visit("Solidity.KeySort")
    if fixtures:
        for fixture in fixtures:
            path = root / fixture
            name = str(fixture).removesuffix(".lean").replace("/", ".")
            by_name[name] = path; visit(name)
    else:
        for row in data["modules"]: visit(row["module"])
    env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=(str(prebuilt_lib) + os.pathsep if prebuilt_lib is not None else "") + str(output / "lib"), LEAN_ABORT_ON_PANIC="1")
    result = {"command": [str(toolchain / "bin/lean"), "-j1", "--tstack=131072", "-o", "<isolated-lib/module.olean>", "<source>"],
        "toolchain": str(toolchain), "clean": prebuilt_lib is None, "full_acceptance": False, "prebuilt_lib": str(prebuilt_lib) if prebuilt_lib is not None else None, "lean_arts": lean_arts, "kind": "serial leanArts-output import closure" if lean_arts else "serial olean import closure/probe; not full acceptance", "modules_planned": ordered,
        "status": "running", "limits": {"rss_bytes": 12*GIB, "available_reserve_bytes": 4*GIB, "hard_vm_cap_bytes": int(Path("/sys/fs/cgroup/memory.max").read_text()), "threads": 1}, "modules": []}
    for exe in ["lean", "lake"]:
        result[exe + "_version"] = subprocess.check_output([str(toolchain / "bin" / exe), "--version"], text=True).strip()
    start = time.monotonic(); peak = 0
    for name in ordered:
        dest = output / "lib" / (name.replace(".", "/") + ".olean"); dest.parent.mkdir(parents=True, exist_ok=True)
        ilean = dest.with_suffix(".ilean")
        c_file = output / "ir" / (name.replace(".", "/") + ".c")
        if lean_arts: c_file.parent.mkdir(parents=True, exist_ok=True)
        log = output / (name + ".log")
        cmd = [str(toolchain / "bin/lean"), "-j1", "--tstack=131072", "-o", str(dest)]
        if lean_arts: cmd.extend(["-i", str(ilean), "-c", str(c_file)])
        cmd.append(str(by_name[name].relative_to(root)))
        began = time.monotonic(); why = None; module_peak = 0
        with log.open("w") as stream:
            proc = subprocess.Popen(cmd, cwd=root, env=env, stdout=stream, stderr=subprocess.STDOUT, start_new_session=True, preexec_fn=limits)
            try:
                while proc.poll() is None:
                    rss = 0
                    for stat in Path("/proc").glob("[0-9]*/stat"):
                        try:
                            fields = stat.read_text().rsplit(")", 1)[1].split()
                            if int(fields[2]) == proc.pid: rss += int(fields[21]) * os.sysconf("SC_PAGE_SIZE")
                        except (OSError, ValueError, IndexError): pass
                    module_peak = max(module_peak, rss)
                    mem = {l.split(":")[0]: int(l.split()[1])*1024 for l in Path("/proc/meminfo").read_text().splitlines() if l.startswith("MemAvailable:")}
                    cg = Path("/sys/fs/cgroup")
                    raw_capacity = (cg / "memory.max").read_text().strip()
                    capacity = int(raw_capacity) if raw_capacity != "max" else mem["MemAvailable"] + int((cg / "memory.current").read_text()); used = int((cg / "memory.current").read_text())
                    if rss > 12*GIB or min(mem["MemAvailable"], capacity-used) < 4*GIB or int((cg / "memory.swap.current").read_text()) != 0:
                        why = "RESOURCE_STOP"; signal_group(proc, signal.SIGTERM); break
                    time.sleep(0.2)
            except BaseException as exc:
                why = "MONITOR_INTERRUPTED:" + type(exc).__name__
            finally:
                signal_group(proc, signal.SIGTERM)
                try: code = proc.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    signal_group(proc, signal.SIGKILL); code = proc.wait()
        if code == 0 and lean_arts and not all(p.is_file() for p in [dest, ilean, c_file]):
            why = "MISSING_BUILD_ARTIFACTS"
        peak = max(peak, module_peak)
        row = {"module": name, "command": cmd, "exit": code, "wall_seconds": time.monotonic()-began, "peak_aggregate_rss_bytes_sampled": module_peak, "log": str(log), "blocker": why, "artifacts": {"olean": str(dest), "ilean": str(ilean) if lean_arts else None, "c": str(c_file) if lean_arts else None}}
        result["modules"].append(row)
        result.update(status="failed" if code != 0 or why else ("complete" if len(result["modules"]) == len(ordered) else "running"), wall_seconds=time.monotonic()-start, peak_aggregate_rss_bytes_sampled=peak, passed=code == 0 and why is None and len(result["modules"]) == len(ordered))
        (output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
        print(f"{name}: exit={code} wall={row['wall_seconds']:.2f}s rss={module_peak} {why or ''}", flush=True)
        if code != 0 or why: return 1
    return 0

if __name__ == "__main__":
    ap = argparse.ArgumentParser(); ap.add_argument("--root", type=Path, required=True); ap.add_argument("--toolchain", type=Path, required=True); ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--fixture", type=Path, action="append", default=[])
    ap.add_argument("--prebuilt-lib", type=Path)
    ap.add_argument("--lean-arts", action="store_true")
    args = ap.parse_args()
    signal.signal(signal.SIGTERM, handle_termination)
    lock = open("/tmp/solidity-lean-feature-groups-20261025/writer.lock", "a")
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    if subprocess.check_output(["git", "status", "--porcelain"], cwd=args.root, text=True):
        print("Working tree status (review before continuing):", flush=True)
        subprocess.run(["git", "status", "--short"], cwd=args.root, check=True)
    raise SystemExit(build(args.root, args.toolchain, args.output, args.fixture, args.prebuilt_lib, args.lean_arts))
