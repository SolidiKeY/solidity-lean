"""Guard H127 worker input admission against unlisted packages and ambient paths.

Binds four independently pinned complete input inventories to a prepared Git
source plan and a fixed environment. Reads only: no worker, toolchain binary,
Git, Lake, mount or container is executed. Caller owns the writer lease.
This is input binding, not image/namespace/CI authentication or lifetime sealing.
"""
import sys
sys.dont_write_bytecode=True
import hashlib
import importlib.util
import json
import os
import tomllib
from pathlib import Path


def module(name,file):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file))
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value

copy=module("input_set_copy","input-copy.py")
plan_module=module("input_set_plan","prepare-plan.py")
ROLES=("source","toolchain","packages","cache")
ENVIRONMENT={
    "PATH":"/input/toolchain/bin:/usr/bin:/bin", "HOME":"/output/home",
    "TMPDIR":"/output/tmp", "XDG_CACHE_HOME":"/output/cache",
    "LC_ALL":"C", "LANG":"C", "TZ":"UTC", "LEAN_NUM_THREADS":"1",
    "LEAN_SYSROOT":"/input/toolchain", "LAKE_HOME":"/input/toolchain",
    "LAKE_CACHE_DIR":"/output/cache/lake", "PYTHONDONTWRITEBYTECODE":"1",
    "GIT_CONFIG_NOSYSTEM":"1", "GIT_CONFIG_GLOBAL":"/dev/null",
    "GIT_NO_REPLACE_OBJECTS":"1", "GIT_NO_LAZY_FETCH":"1",
    "GIT_OPTIONAL_LOCKS":"0", "GIT_TERMINAL_PROMPT":"0",
}


def safe_name(name):
    if not isinstance(name,str) or name.startswith("/") or any(x in ("",".","..") for x in name.split("/")):
        raise ValueError("unsafe source plan path")


def bind_source(plan,observed):
    if (not isinstance(plan,dict) or type(plan.get("schemaVersion")) is not int or plan["schemaVersion"]!=1 or plan.get("status")!="prepared-not-executed" or
            plan.get("slowModules")!=list(plan_module.SLOW) or plan.get("rootGate")!="SoliditySlowExamples"):
        raise ValueError("unknown prepared slow-source plan")
    import re
    if any(not isinstance(plan.get(k),str) or not re.fullmatch("[0-9a-f]{40}",plan[k]) for k in ("head","tree")):
        raise ValueError("exact source head/tree required")
    table={r["contentMetadata"]["path"]:r["contentMetadata"] for r in observed["records"]}
    names=set()
    entries=plan.get("sourceInventory")
    if not isinstance(entries,list) or not entries:raise ValueError("complete source plan required")
    for entry in entries:
        name=entry["path"];safe_name(name)
        if name in names or name==".git" or name.startswith(".git/"):
            raise ValueError("duplicate source or Git metadata in tracked plan")
        names.add(name)
        current=table.get(name)
        mode={"100644":0o644,"100755":0o755}.get(entry.get("mode"))
        if (current is None or current["kind"]!="file" or mode is None or
                current["mode"]!=mode or current["bytes"]!=entry.get("bytes") or
                current["sha256"]!=entry.get("sha256")):
            raise ValueError("source plan content/mode mismatch")
    # The materializer provides private Git metadata. It is fully receipt-pinned
    # here, but Git object semantics remain source-snapshot.py's separate gate.
    allowed_dirs={"."}
    for name in names:
        parts=name.split("/")
        allowed_dirs.update("/".join(parts[:i]) for i in range(1,len(parts)))
    for name,item in table.items():
        if name==".git" or name.startswith(".git/"):continue
        if item["kind"]=="directory" and name in allowed_dirs:continue
        if name not in names:raise ValueError("unlisted source input")
    for required in ("lake-manifest.json","lean-toolchain","lakefile.toml","SoliditySlowExamples.lean"):
        if required not in names:raise ValueError("required source input absent")
    if any(module.replace(".","/")+".lean" not in names for module in plan_module.SLOW):
        raise ValueError("selected slow source absent")
    return table


def read_source(source,name,entry):
    raw,mode=plan_module.regular_bytes(source,name,entry["bytes"])
    if mode!=entry["mode"] or hashlib.sha256(raw).hexdigest()!=entry["sha256"]:
        raise ValueError("source metadata changed during binding")
    return raw


def admit(plan_path,plan_sha256,inputs):
    if not isinstance(inputs,dict) or set(inputs)!=set(ROLES):
        raise ValueError("exact source/toolchain/packages/cache input set required")
    plan=copy.receipt(plan_path,plan_sha256)
    observations={};pins={};roots={};directories={}
    for role in ROLES:
        spec=inputs[role]
        if not isinstance(spec,dict) or set(spec)!={"root","receipt","sha256"}:
            raise ValueError("exact role root/receipt/pin required")
        expected=copy.receipt(spec["receipt"],spec["sha256"])
        observed=copy.inventory.inventory(spec["root"])
        if observed!=expected or observed["externalHardlinkAliases"]:
            raise ValueError("input identity drift or external hardlink alias")
        observations[role]=observed;pins[role]=spec["sha256"];roots[role]=Path(observed["root"])
        directories[role]={(r["observedIdentity"]["device"],r["observedIdentity"]["inode"])
                           for r in observed["records"] if r["contentMetadata"]["kind"]=="directory"}
    for i,role in enumerate(ROLES):
        for other in ROLES[i+1:]:
            if (roots[role].is_relative_to(roots[other]) or roots[other].is_relative_to(roots[role]) or
                    directories[role].intersection(directories[other])):
                raise ValueError("input roles overlap or alias")
    table=bind_source(plan,observations["source"])
    manifest=json.loads(read_source(roots["source"],"lake-manifest.json",table["lake-manifest.json"]),object_pairs_hook=copy.pairs)
    # H109's core library is dependency-free. No package resolving or new
    # dependency dialect is selected implicitly; Bridge is a different job.
    if (not isinstance(manifest,dict) or manifest.get("version")!="1.1.0" or
            manifest.get("packagesDir")!=".lake/packages" or manifest.get("lakeDir")!=".lake" or
            manifest.get("packages")!=[]):
        raise ValueError("H109 core requires the existing empty package manifest")
    config=tomllib.loads(read_source(roots["source"],"lakefile.toml",table["lakefile.toml"]).decode())
    if config.get("require",[])!=[]:
        raise ValueError("unlisted Lake dependency in source configuration")
    libraries=config.get("lean_lib",[])
    slow=[lib for lib in libraries if isinstance(lib,dict) and lib.get("name")=="SoliditySlowExamples"]
    if (len(slow)!=1 or "SoliditySlowExamples" in config.get("defaultTargets",[]) or
            any(k in slow[0] for k in ("roots","srcDir","globs","needs","extraDepTargets"))):
        raise ValueError("slow library must retain its non-default source mapping")
    imports=[]
    for line in read_source(roots["source"],"SoliditySlowExamples.lean",table["SoliditySlowExamples.lean"]).decode().splitlines():
        if line.startswith("import "):imports.extend(line[7:].split())
        elif line.strip() and not line.startswith("--"):raise ValueError("unknown slow root syntax")
    if tuple(imports)!=plan_module.SLOW:raise ValueError("slow root denominator changed")
    if len(observations["packages"]["records"])!=1:
        raise ValueError("unlisted package input")
    if read_source(roots["source"],"lean-toolchain",table["lean-toolchain"])!=b"leanprover/lean4:v4.24.0\n":
        raise ValueError("unsupported pinned worker toolchain selection")
    tools={r["contentMetadata"]["path"]:r["contentMetadata"] for r in observations["toolchain"]["records"]}
    for name in ("bin/lean","bin/lake"):
        if name not in tools or tools[name]["kind"]!="file" or not tools[name]["mode"]&0o111:
            raise ValueError("pinned toolchain executable missing")
    for role in ROLES:
        if copy.inventory.inventory(roots[role])!=observations[role]:
            raise ValueError("input changed during admission")
    return {"status":"bound-input-observations-only","head":plan["head"],"tree":plan["tree"],
            "planSha256":plan_sha256,"inputReceiptPins":pins,
            "toolchainExecutables":{name:tools[name]["sha256"] for name in ("bin/lean","bin/lake")},
            "environment":dict(ENVIRONMENT),"ciBudgetAuthorized":False,
            "sourceGitSemanticsAuthenticated":False,"imageAuthenticated":False,
            "toolchainVersionAuthenticated":False,"writableCacheInitialized":False,
            "networkIsolationAuthenticated":False,
            "readOnlyMountAuthenticated":False,"lifetimeSealed":False,
            "workerExecutionAuthorized":False,
            "boundary":"Complete pinned input observations and fixed environment only. Caller must authenticate private Git semantics, runtime image including system executables, namespaces, mount mapping, CI context, resources, lifetime and cleanup."}
