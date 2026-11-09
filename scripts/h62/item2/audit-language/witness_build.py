#!/usr/bin/env python3
"""Guard stale compiled witness substitution with a fresh, isolated import closure.

Every repository import is rebuilt, without Lake or its cache. Toolchain files,
source bytes and produced objects are bound before/after the generated audit.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
from census import mask

ROOT = Path(__file__).resolve().parents[4]
MODULE = r"(?:[A-Za-z_]\w*|«[^»\n/]+»)(?:\.(?:[A-Za-z_]\w*|«[^»\n/]+»))*"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def imports(text):
    # Import headers only; a later import or any unfamiliar header fails closed.
    lines = mask(text).splitlines()
    result, ended = [], False
    for line in lines:
        line = line.strip()
        if not line:
            continue
        if line == "prelude" and not result and not ended:
            continue
        if re.match(r"(?:public\s+|private\s+)?import\b", line):
            if ended or not line.startswith("import "):
                raise ValueError("unsupported import header")
            names = line[7:].split()
            if not names or any(not re.fullmatch(MODULE, n) for n in names):
                raise ValueError("unsupported import syntax")
            result.extend(n.replace("«", "").replace("»", "") for n in names)
        else:
            ended = True
    return result


def closure(generated, root=ROOT):
    ordered, active, seen, sources = [], set(), set(), {}

    def visit(name):
        if name in active:
            raise ValueError("import cycle")
        if name in seen:
            return
        if not re.fullmatch(r"[\w-]+(?:\.[\w-]+)*", name):
            raise ValueError("unsupported module identity")
        path = root / (name.replace(".", "/") + ".lean")
        if not path.exists():
            if name.split(".")[0] not in {"Init", "Lean", "Lake", "Std"}:
                raise ValueError("unresolved repository import: " + name)
            return
        if path.is_symlink() or path.resolve() != path or not path.is_file():
            raise ValueError("unsafe source path")
        active.add(name)
        raw = path.read_bytes()
        sources[str(path.relative_to(root))] = hashlib.sha256(raw).hexdigest()
        for dep in imports(raw.decode()):
            visit(dep)
        active.remove(name)
        seen.add(name)
        ordered.append(name)

    for name in imports(generated.read_text()):
        visit(name)
    return {"modules": ordered, "sources": sources}


def loader_environment():
    return {k: v for k, v in os.environ.items()
            if k not in {"LD_PRELOAD", "LD_LIBRARY_PATH", "LD_AUDIT"}
            and not k.startswith("DYLD_")}


def toolchain(executable=None):
    # Preserve elan proxy dispatch while asking for the selected toolchain.
    invocation = Path(executable or shutil.which("lean") or "").absolute()
    if not invocation.is_file():
        raise ValueError("Lean executable unavailable")
    prefix = Path(subprocess.check_output([str(invocation), "--print-prefix"],
                                         env=loader_environment(), text=True).strip()).resolve()
    lean = (prefix / "bin/lean").resolve()
    if not lean.is_file():
        raise ValueError("selected Lean executable unavailable")
    files = sorted({invocation.resolve(), lean} |
                   {p for p in (prefix / "lib").rglob("*")
                    if p.is_file() and (p.suffix in {".olean", ".so", ".dll", ".dylib"}
                                        or ".so." in p.name)})
    return {"lean": str(lean), "invocation": str(invocation), "prefix": str(prefix),
            "files": {str(p): sha(p) for p in files}}


def environment(build, prefix):
    env = loader_environment()
    for key in list(env):
        if key.startswith(("LEAN_", "LAKE_")):
            del env[key]
    env.update(LEAN_PATH=str(build) + os.pathsep + str(Path(prefix) / "lib/lean"),
               LEAN_NUM_THREADS="1")
    return env


def compile_closure(generated, build, root=ROOT):
    if build.exists() or build.is_symlink() or build.resolve().is_relative_to(root):
        raise ValueError("new external build directory required")
    build.mkdir(parents=True)
    before = closure(generated, root)
    generated_hash = sha(generated)
    compiler = toolchain()
    env = environment(build, compiler["prefix"])
    commands = []
    allowed = [build.resolve(), Path(compiler["prefix"]) / "lib/lean"]

    def run(source, output=None):
        package_root = root if output is not None else generated.parent
        deps = subprocess.check_output([compiler["lean"], "--deps", str(source)],
                                       cwd=build, env=env, text=True)
        for line in deps.splitlines():
            path = Path(line).resolve()
            if not any(path.is_relative_to(p) for p in allowed) or not path.is_file():
                raise ValueError("dependency escaped isolated artifacts: " + line)
        command = [compiler["lean"], "--root=" + str(package_root), "--tstack=131072", "-j1"]
        if output is not None:
            output.parent.mkdir(parents=True, exist_ok=True)
            command += ["-o", str(output)]
        command += [str(source)]
        commands.append(command)
        subprocess.run(command, cwd=build, env=env, check=True)

    for module in before["modules"]:
        run(root / (module.replace(".", "/") + ".lean"),
            build / (module.replace(".", "/") + ".olean"))
    artifacts = {str(build / (m.replace(".", "/") + ".olean")):
                 sha(build / (m.replace(".", "/") + ".olean")) for m in before["modules"]}
    run(generated)
    if (before != closure(generated, root) or sha(generated) != generated_hash or
            compiler != toolchain() or any(sha(Path(p)) != h for p, h in artifacts.items())):
        raise ValueError("compilation inputs or outputs changed")
    return {"closure": before, "generated_sha256": generated_hash, "compiler": compiler,
            "artifacts": artifacts, "commands": commands, "search_path": env["LEAN_PATH"]}


def validate_build(record, generated):
    generated = generated.resolve()
    if record["closure"] != closure(generated) or record["generated_sha256"] != sha(generated):
        raise ValueError("stale compiled source closure")
    if record["compiler"] != toolchain(record["compiler"]["invocation"]):
        raise ValueError("changed toolchain")
    artifacts = record["artifacts"]
    modules = record["closure"]["modules"]
    if not modules or len(artifacts) != len(modules):
        raise ValueError("incomplete compiled artifacts")
    suffix = modules[0].replace(".", "/") + ".olean"
    paths = [p for p in artifacts if p.endswith(suffix)]
    if len(paths) != 1:
        raise ValueError("artifact module mapping mismatch")
    build = Path(paths[0][:-len(suffix)])
    if build.resolve().is_relative_to(ROOT) or build.is_symlink():
        raise ValueError("non-isolated artifacts")
    expected = {str(build / (m.replace(".", "/") + ".olean")) for m in modules}
    if set(artifacts) != expected or any(Path(p).is_symlink() or sha(Path(p)) != h
                                       for p, h in artifacts.items()):
        raise ValueError("compiled artifact substitution")
    commands = []
    for module in modules:
        output = build / (module.replace(".", "/") + ".olean")
        commands.append([record["compiler"]["lean"], "--root=" + str(ROOT),
                         "--tstack=131072", "-j1", "-o", str(output),
                         str(ROOT / (module.replace(".", "/") + ".lean"))])
    commands.append([record["compiler"]["lean"], "--root=" + str(generated.parent),
                     "--tstack=131072", "-j1", str(generated)])
    if record["commands"] != commands:
        raise ValueError("compiled source/module commands differ")
    if record["search_path"] != environment(build, record["compiler"]["prefix"])["LEAN_PATH"]:
        raise ValueError("unbound import search path")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ("generated", "build", "record"):
        p.add_argument("--" + name, type=Path, required=True)
    args = p.parse_args()
    if args.record.exists() or args.record.is_symlink() or args.record.resolve().is_relative_to(ROOT):
        raise ValueError("new external build record required")
    record = compile_closure(args.generated.resolve(), args.build.resolve())
    with args.record.open("x") as out:
        out.write(json.dumps(record, sort_keys=True, indent=2) + "\n")


if __name__ == "__main__":
    main()
