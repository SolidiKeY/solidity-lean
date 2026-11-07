#!/usr/bin/env python3
"""Generate (never execute) an inspection for the frozen mapped Bridge files.

Reuses the exact retired all-constant Lean template. Bridge module names omit
only the package-root directory; no source definitions or proof options change.
The original core generator and its manifest format remain unchanged.
"""
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
import types

MEMBER = "7a9f8aa5b391696c70e3cb23b76135869f79bacb"
CENSUS = "scripts/h62/item2/audit-bytecode-selection/census.py"
GENERATOR = "scripts/h62/item2/audit-bytecode-selection/elaborated_census.py"
BOUNDARY = "Generated only; no Lean execution, kernel inspection, source-to-kernel linkage, witness or acceptance."


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


def extract_template(raw):
    tree = ast.parse(raw)
    values = [statement.value for statement in tree.body
              if isinstance(statement, ast.Assign)
              and any(isinstance(target, ast.Name) and target.id == "TEMPLATE"
                      for target in statement.targets)]
    if len(values) != 1:
        raise ValueError("missing unique frozen template")
    value = ast.literal_eval(values[0])
    if not isinstance(value, str):
        raise ValueError("frozen template is not literal text")
    if value.count("MODULES") != 1 or value.count("FINGERPRINT") != 1:
        raise ValueError("frozen template placeholders differ")
    return value


def module_name(path):
    prefix = "Bridge/"
    if not path.startswith(prefix) or not path.endswith(".lean"):
        raise ValueError("not a Bridge source path")
    pieces = path[len(prefix):-5].split("/")
    if pieces[0] != "SolidityBridge" or not all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", piece) for piece in pieces):
        raise ValueError("unsupported or escaping Bridge module path")
    return ".".join(pieces)


def selected_sources(paths, requested):
    available = {module_name(path): path for path in paths if path.startswith("Bridge/")}
    if len(available) != sum(path.startswith("Bridge/") for path in paths):
        raise ValueError("duplicate Bridge module mapping")
    modules = sorted(available) if requested is None else sorted(requested)
    if not modules or len(set(modules)) != len(modules):
        raise ValueError("empty or duplicate module selection")
    if not set(modules) <= set(available):
        raise ValueError("requested module outside frozen mapped Bridge")
    return {module: available[module] for module in modules}


def generate(repo, requested=None):
    repo = repo.resolve()
    # Read authenticated final-head tools from immutable Git objects, never
    # import unverified mutable source paths. The final head was merged first.
    census_raw = git(repo, "show", MEMBER + ":" + CENSUS)
    generator_raw = git(repo, "show", MEMBER + ":" + GENERATOR)
    template = extract_template(generator_raw)
    scanner = types.ModuleType("h82_frozen_bytecode_census")
    scanner.__file__ = MEMBER + ":" + CENSUS
    exec(compile(census_raw, scanner.__file__, "exec"), scanner.__dict__)
    paths, _ = scanner.mapped_paths(repo)
    selected = selected_sources(paths, requested)
    pins = {}
    for module, path in selected.items():
        source = repo / path
        if any(parent.is_symlink() for parent in (source, *source.parents) if parent != repo):
            raise ValueError("symlink source path: " + path)
        raw = source.read_bytes()
        if raw != git(repo, "show", scanner.BASE + ":" + path):
            raise ValueError("frozen source differs: " + path)
        pins[path] = sha(raw)
    payload = {"schema_version": 2, "package_root": "Bridge",
               "base": scanner.BASE, "member_head": MEMBER,
               "module_sources": selected, "modules": list(selected),
               "source_sha256": pins, "inspection_template_sha256": sha(template.encode()),
               "census_tool_sha256": sha(census_raw), "generator_tool_sha256": sha(generator_raw),
               "execution_status": "not run", "boundary": BOUNDARY,
               "emitter_sha256": sha(Path(__file__).read_bytes())}
    fingerprint = sha(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode())
    imports = "import Lean\n" + "".join("import " + name + "\n" for name in selected)
    source = imports + template.replace("MODULES", ", ".join("`" + name for name in selected)).replace("FINGERPRINT", fingerprint)
    return source, dict(payload, manifest_sha256=fingerprint, inspection_sha256=sha(source.encode()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--module", action="append")
    args = parser.parse_args()
    pin_path = args.output.with_suffix(".pins.json")
    for path in (args.output, pin_path):
        if path.resolve().is_relative_to(args.repo.resolve()) or path.resolve().is_relative_to(Path(__file__).resolve().parents[4]):
            raise ValueError("H44: generated output must be outside both repositories")
        if path.exists() or any(parent.is_symlink() for parent in (path, *path.parents)):
            raise ValueError("refusing existing or symlink output")
    source, pins = generate(args.repo, args.module)
    with args.output.open("x") as out:
        out.write(source)
    with pin_path.open("x") as out:
        out.write(json.dumps(pins, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"modules_generated": len(pins["modules"]), "package_root": "Bridge", "execution_status": "not run", "boundary": BOUNDARY}))


if __name__ == "__main__":
    main()
