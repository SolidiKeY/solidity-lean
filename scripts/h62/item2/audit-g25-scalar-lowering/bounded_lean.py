#!/usr/bin/env python3
"""Serial source check into a toolchain-isolated off-git cache.

No interface edits or proof-budget overrides; source-hashed local cache reuse.
Each imported repository module is compiled once in topological order. This
is per-file dependency validation; it DOES NOT replace ./run-lean.sh final gate.
"""
import argparse
import ctypes
import hashlib
import re
import json
import os
from pathlib import Path
import resource
import signal
import shutil
import subprocess
import time
import census

INTERRUPTED = None
RESOURCE_POLICY = "vm16GiB-reserve4GiB-treeRss10GiB-AS12GiB-time300s-no-swap-v3"


def available():
    mem = dict(line.split(":", 1) for line in Path("/proc/meminfo").read_text().splitlines())
    host = int(mem["MemAvailable"].split()[0]) * 1024
    cg = Path("/sys/fs/cgroup")
    cap = (cg/"memory.max").read_text().strip()
    if cap != "max": host = min(host, int(cap)-int((cg/"memory.current").read_text()))
    if int((cg/"memory.swap.current").read_text()): raise RuntimeError("nonzero cgroup swap")
    return host


def module_name(raw):
    def unquote(match):
        text = match.group(1)
        if "." in text or "/" in text: raise ValueError("unsupported quoted module component")
        return text
    result = re.sub(r"«([^«»]+)»", unquote, raw)
    if "«" in result or "»" in result: raise ValueError("malformed quoted module name")
    return result


def digest_file(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024*1024), b""): digest.update(block)
    return digest.hexdigest()


def distribution_hash(toolchain):
    digest = hashlib.sha256()
    paths = sorted(p for part in ("bin", "lib") for p in (toolchain/part).rglob("*") if p.is_file())
    for path in paths:
        digest.update(str(path.relative_to(toolchain)).encode())
        digest.update(digest_file(path).encode())
    return digest.hexdigest()


def dependencies(repo, targets):
    seen, active, ordered = set(), set(), []
    def visit(module):
        if module in seen: return
        if module in active: raise ValueError("cyclic dependency: " + module)
        path = repo / (module.replace(".", "/") + ".lean")
        if not path.exists():
            if module.startswith(("Lean", "Init", "Std")): return
            raise ValueError("missing repository import: " + module)
        active.add(module)
        for line in census.mask(path.read_text()).splitlines():
            if line.startswith("import "):
                for imp in line[7:].split(): visit(module_name(imp))
        active.remove(module); seen.add(module); ordered.append(module)
    for target in targets: visit(target)
    return ordered


def limits():
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    soft, hard = resource.getrlimit(resource.RLIMIT_AS)
    existing = [x for x in (soft, hard) if x != resource.RLIM_INFINITY]
    ceiling = min([12*1024**3] + existing)
    resource.setrlimit(resource.RLIMIT_AS, (ceiling, ceiling))


def scoped_pids(records, group):
    chosen = {pid for pid, (_, pgrp, _) in records.items() if pgrp == group}
    while True:
        more = {pid for pid, (parent, _, _) in records.items() if parent in chosen}
        if more <= chosen: return chosen
        chosen |= more


def workload_rss_kib(proc=None):
    """Include descendant process groups, including the separate Lean session."""
    records = {}
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit(): continue
        try:
            stat = (entry/"stat").read_text(); fields = stat[stat.rfind(")")+2:].split()
            rss = int((entry/"statm").read_text().split()[1]) * os.sysconf("SC_PAGE_SIZE") // 1024
            records[int(entry.name)] = (int(fields[1]), int(fields[2]), rss)
        except (OSError, ValueError): continue
    if proc is not None: remember_children(proc)
    if os.getpid() not in records: raise RuntimeError("runner RSS could not be measured")
    return sum(records[pid][2] for pid in scoped_pids(records, os.getpgrp()))


def process_tree():
    records = {}
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit(): continue
        try:
            stat = (entry/"stat").read_text(); fields = stat[stat.rfind(")")+2:].split()
            records[int(entry.name)] = (int(fields[1]), fields[19])
        except (OSError, ValueError): continue
    return records


def remember_children(proc):
    records = process_tree()
    # This runner is a child subreaper and runs only one Lean child at a time.
    chosen = {proc.pid} | {p for p, (parent, _) in records.items() if parent == os.getpid()}
    while True:
        more = {p for p, (parent, _) in records.items() if parent in chosen}
        if more <= chosen: break
        chosen |= more
    known = getattr(proc, "_audit_children", {})
    known.update({p: records[p][1] for p in chosen if p in records and p != os.getpid()})
    proc._audit_children = known


def signal_children(proc, sig):
    remember_children(proc)
    current = process_tree()
    for pid, started in proc._audit_children.items():
        if pid == proc.pid: continue
        if pid in current and current[pid][1] == started:
            try: os.kill(pid, sig)
            except ProcessLookupError: pass


def terminate(proc, force=False):
    if force:
        # Resource/interrupt stops must not grant a growing workload a grace
        # period in which it can consume the VM reserve. Preserve PID identity
        # checks for detached descendants, then reap the owned process group.
        signal_children(proc, signal.SIGKILL)
        if proc.poll() is None:
            try: os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError: pass
            proc.wait()
        signal_children(proc, signal.SIGKILL)
        for pid in proc._audit_children:
            if pid == proc.pid: continue
            try: os.waitpid(pid, 0)
            except ChildProcessError: pass
        return
    signal_children(proc, signal.SIGTERM)
    if proc.poll() is None:
        try: proc.wait(timeout=.2)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGTERM)
            try: proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL); proc.wait()
    signal_children(proc, signal.SIGKILL)
    for pid in proc._audit_children:
        if pid == proc.pid: continue
        try: os.waitpid(pid, 0)
        except ChildProcessError: pass


def subreaper():
    # Linux PR_SET_CHILD_SUBREAPER: detached grandchildren remain owned/reapable.
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(36, 1, 0, 0, 0) != 0:
        raise RuntimeError("cannot establish child subreaper: " + str(ctypes.get_errno()))


def deadline_expired(start, end):
    return end-start >= 300


def interrupted(signum, _frame):
    # Defer until the active Popen object is protected by its cleanup finally.
    global INTERRUPTED
    INTERRUPTED = signum


def main():
    global INTERRUPTED
    INTERRUPTED = None
    subreaper()
    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, default=Path.cwd())
    p.add_argument("--toolchain", type=Path, required=True)
    p.add_argument("--artifacts", type=Path, required=True)
    p.add_argument("--recheck-targets",action="store_true",help="always recompile named targets; verified imports may be reused")
    p.add_argument("--evidence",action="append",default=[],metavar="MODULE=PATH",help="bind a producer's freshly emitted evidence file to its successful receipt")
    p.add_argument("--keep-going", action="store_true", help="check independent files serially after a failure; never check clients of failed imports")
    p.add_argument("--reuse", action="store_true", help="reuse only source/dependency/toolchain/output-hash-verified local artifacts")
    p.add_argument("--direct", action="store_true",
                   help="check only named files; require imports already built in this isolated cache")
    p.add_argument("modules", nargs="+")
    a = p.parse_args()
    a.modules = [module_name(name) for name in a.modules]
    if a.direct and len(a.modules) != 1:
        p.error("--direct accepts exactly one file")
    repo, artifacts = a.repo.resolve(), a.artifacts.resolve()
    cache = artifacts/"lib"/"lean"
    cache.mkdir(parents=True, exist_ok=True)
    logs = artifacts/"logs"; logs.mkdir(exist_ok=True)
    env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(cache))
    summary = []
    emitted={}
    for binding in a.evidence:
        name,path=binding.split("=",1)
        path=Path(path).resolve()
        if not path.is_relative_to(artifacts.parent): raise ValueError("emitted evidence must stay in the owned artifact tree")
        emitted.setdefault(module_name(name),[]).append(path)
    index_path = artifacts/"cache-index.json"
    index = json.loads(index_path.read_text()) if index_path.exists() else {}
    compiler = distribution_hash(a.toolchain)
    fingerprints = {}
    def fingerprint(module):
        if module in fingerprints: return fingerprints[module]
        path = repo/(module.replace(".", "/")+".lean")
        if not path.exists(): return compiler
        imports = []
        for line in census.mask(path.read_text()).splitlines():
            if line.startswith("import "):
                imports.extend(module_name(name) for name in line[7:].split())
        data = {"source":census.digest(path.read_bytes()),"compiler":compiler,
                "flags":["-j1","--tstack=131072"],
                "resource_policy":RESOURCE_POLICY,
                "imports":{name:fingerprint(name) for name in imports}}
        result = census.digest(json.dumps(data,sort_keys=True).encode())
        fingerprints[module] = result
        return result
    def valid_cache(module):
        old = index.get(module, {})
        output = cache/(module.replace(".", "/")+".olean")
        try:
            receipt = Path(old["receipt"])
            if old.get("receipt_sha256") != digest_file(receipt): return False
            row = json.loads(receipt.read_text())
            expected = fingerprint(module)
            recorded=row.get("emitted_evidence",{})
            if any(str(path) not in recorded for path in emitted.get(module,[])): return False
            if any(digest_file(Path(path)) != sha for path,sha in recorded.items()): return False
            actual_output = digest_file(output)
            return (old.get("fingerprint") == expected == row.get("fingerprint")
                    and old.get("output_sha256") == actual_output == row.get("output_sha256")
                    and row.get("module") == module and row.get("exit") == 0
                    and row.get("resource_stop") is False and row.get("cache_hit") is False)
        except (KeyError, OSError, ValueError): return False
    ordered = dependencies(repo, a.modules)
    if a.direct:
        for imported in ordered:
            if imported not in a.modules and not valid_cache(imported):
                raise RuntimeError("direct check requires validated import receipt: "+imported)
    failed = set()
    for module in (a.modules if a.direct else ordered):
        if INTERRUPTED is not None: raise SystemExit(128+INTERRUPTED)
        if available() < 4*1024**3: raise RuntimeError("less than 4 GiB headroom")
        source = repo/(module.replace(".", "/")+".lean")
        imported = [module_name(name) for line in census.mask(source.read_text()).splitlines() if line.startswith("import ") for name in line[7:].split()]
        blocked = [name for name in imported if name in failed]
        if blocked:
            failed.add(module)
            row = dict(module=module,status="blocked-import",blocked_by=blocked,exit=None)
            summary.append(row)
            (artifacts/"results.json").write_text(json.dumps(summary,indent=2)+"\n")
            print(json.dumps(row),flush=True)
            if not a.keep_going: raise SystemExit(1)
            continue
        output = cache/(module.replace(".", "/")+".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        log = logs/(module+".log")
        cmd = [str(a.toolchain/"bin"/"lean"), "-j1", "--tstack=131072",
               "--root="+str(repo), "-o", str(output), str(source)]
        expected = fingerprint(module)
        old = index.get(module, {})
        if a.reuse and not (a.recheck_targets and module in a.modules) and valid_cache(module):
            row = dict(module=module, cache_hit=True, fingerprint=expected,
                       exit=0, receipt=old.get("receipt"), seconds=0)
            summary.append(row)
            (artifacts/"results.json").write_text(json.dumps(summary,indent=2)+"\n")
            print(json.dumps(row),flush=True)
            continue
        for path in emitted.get(module,[]):
            if path.exists():
                history=artifacts/"emitted-history"/module
                history.mkdir(parents=True,exist_ok=True)
                shutil.copy2(path,history/(path.name+"."+digest_file(path)))
                path.unlink()
        start = time.monotonic()
        before_usage = resource.getrusage(resource.RUSAGE_CHILDREN)
        with log.open("w") as stream:
            proc = subprocess.Popen(cmd, cwd=repo, env=env, stdout=stream,
                                    stderr=subprocess.STDOUT, start_new_session=True, preexec_fn=limits)
            resource_stop = False
            sampled_peak_rss_kib = 0
            sampled_peak_workload_rss_kib = 0
            stop_reason = None
            abnormal = True
            try:
                if INTERRUPTED is not None: raise SystemExit(128+INTERRUPTED)
                while proc.poll() is None:
                    if INTERRUPTED is not None: raise SystemExit(128+INTERRUPTED)
                    try:
                        rss_kib = int(Path(f"/proc/{proc.pid}/statm").read_text().split()[1]) * os.sysconf("SC_PAGE_SIZE") // 1024
                    except FileNotFoundError: rss_kib = 0
                    sampled_peak_rss_kib = max(sampled_peak_rss_kib, rss_kib)
                    workload_rss = workload_rss_kib(proc)
                    sampled_peak_workload_rss_kib = max(sampled_peak_workload_rss_kib, workload_rss)
                    if deadline_expired(start, time.monotonic()):
                        resource_stop = True; stop_reason = "per-file-timeout"
                        terminate(proc, force=True)
                        break
                    if available() < 4*1024**3 or workload_rss > 10*1024**2:
                        resource_stop = True
                        stop_reason = "reserve-or-workload-rss"
                        terminate(proc, force=True)
                        break
                    try: proc.wait(timeout=.1)
                    except subprocess.TimeoutExpired: pass
                code = proc.wait()
                if INTERRUPTED is not None: raise SystemExit(128+INTERRUPTED)
                if deadline_expired(start, time.monotonic()):
                    resource_stop = True; stop_reason = "per-file-timeout"
                abnormal = False
            finally:
                terminate(proc, force=abnormal or resource_stop or INTERRUPTED is not None)
        usage = resource.getrusage(resource.RUSAGE_CHILDREN)
        row = dict(module=module, command=cmd, exit=code, resource_stop=resource_stop,
                   cache_hit=False, fingerprint=expected,
                   cpu_seconds=round(usage.ru_utime+usage.ru_stime-before_usage.ru_utime-before_usage.ru_stime,6),
                   max_child_rss_since_runner_start_kib=usage.ru_maxrss,
                   sampled_peak_rss_kib=sampled_peak_rss_kib,
                   sampled_peak_workload_rss_kib=sampled_peak_workload_rss_kib, stop_reason=stop_reason,
                   seconds=round(time.monotonic()-start, 3), log=str(log),
                   source_sha256=census.digest(source.read_bytes()))
        if code == 0 and not resource_stop:
            missing=[str(path) for path in emitted.get(module,[]) if not path.exists()]
            if missing:
                row["exit"]=code=1
                row["missing_emitted_evidence"]=missing
            else:
                row["emitted_evidence"]={str(path):digest_file(path) for path in emitted.get(module,[])}
        if code == 0 and not resource_stop:
            row["output_sha256"] = digest_file(output)
            receipt = artifacts/"receipts"/(module+"."+expected+".json")
            receipt.parent.mkdir(exist_ok=True)
            receipt.write_text(json.dumps(row,indent=2)+"\n")
            index[module] = {"fingerprint":expected,"output_sha256":row["output_sha256"],"receipt":str(receipt),"receipt_sha256":digest_file(receipt)}
            index_path.write_text(json.dumps(index,indent=2)+"\n")
        summary.append(row)
        (artifacts/"results.json").write_text(json.dumps(summary,indent=2)+"\n")
        print(json.dumps(row), flush=True)
        if code or resource_stop:
            failed.add(module)
            if not a.keep_going: raise SystemExit(1)
    if failed: raise SystemExit(1)

if __name__ == "__main__": main()
