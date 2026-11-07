"""Guard regression: a 14-candidate audit must not stand in for a full census.

Inventory the existing producer-selected C, source fingerprints and ELF symbols.
This is finite provenance accounting, not a C parser, semantic classifier,
exhaustive forbidden-functionality proof, or native/browser acceptance gate.
It does not load Lean, execute the verifier, or change the producer closure.
"""
import hashlib
import importlib.util
import json
import pathlib
import re
import subprocess
import sys

if not __debug__:
    raise RuntimeError("Census checks require ordinary Python; optimization is unsupported")
repo, prefix, native, out = [pathlib.Path(x).resolve() for x in sys.argv[1:]]
out.mkdir(parents=True, exist_ok=False)

def sha(path):
    with pathlib.Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

def digest(data):
    return hashlib.sha256(data).hexdigest()

def emit(name, rows):
    with (out/name).open("w") as stream:
        for row in rows:
            stream.write(json.dumps(row, sort_keys=True)+"\n")

manifest = json.loads((native/"build.json").read_text())
setup = json.loads((repo/".lake/build/ir/Solidity/Tools/DirectRuntime.setup.json").read_text())
expected_sources = {n for n in setup["importArts"] if n.startswith("Solidity.")} | {"Solidity.Tools.DirectRuntime"}
assert {r["module"] for r in manifest["sourceFiles"]} == expected_sources
assert len(manifest["sourceFiles"]) == len(expected_sources)
assert sha(native/"direct-check") == manifest["executable"]
# Reconstruct the unchanged producer provenance_paths() domain independently.
expected_inputs = {repo/"scripts/build-direct-native.py", repo/"scripts/direct-runtime-closure.py", repo/"web/browser/direct-bridge.c", repo/"lean-toolchain", repo/"lakefile.toml", pathlib.Path(manifest["compilerCommand"])}
expected_inputs.update(prefix/"bin"/n for n in ["lean", "lake", "leanc", "clang", "ld.lld", "llvm-ar"])
expected_inputs.update((prefix/"include").rglob("*.h"))
expected_inputs.update((prefix/"lib").rglob("*.a"))
assert set(manifest["buildInputs"]) == {str(p) for p in expected_inputs}, "Incomplete producer build-input domain"
for path, expected in manifest["buildInputs"].items():
    assert sha(path) == expected, path
producer = repo/"scripts/direct-runtime-closure.py"
assert sha(producer) == manifest["closureScriptSha256"]
spec = importlib.util.spec_from_file_location("existing_producer", producer)
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
inputs, closure = helper.extract(repo, native/"runtime", native_roots=manifest["closure"]["nativeRoots"])
assert closure == manifest["closure"]
objects = json.loads((out.parent/"native-closure/evidence.json").read_text())["objects"]
object_map = {row["module"]: row for row in objects}
assert len(object_map) == len(objects) == len(inputs) == closure["modules"]

# Account for every generated-C input visited by the existing import traversal.
# Fingerprinting unselected source modules does not mean they were linked.
all_sources = {}
pending = ["Solidity.Tools.DirectRuntime"]
while pending:
    module = pending.pop()
    if module in all_sources:
        continue
    path = (repo/".lake/build/ir" if module.startswith("Solidity.") else native/"runtime/lib/temp") / (module.replace(".", "/")+".c")
    data = path.read_bytes()
    header = re.search(rb"^// Imports: ?([^\n]*)$", data, re.M)
    assert header is not None, module
    imports = header[1].decode().split()
    all_sources[module] = {"module": module, "path": str(path), "sha256": digest(data), "bytes": len(data), "imports": imports, "selected": module in object_map}
    pending.extend(imports)
assert len(all_sources) == closure["sourceModules"]
emit("generated-sources.jsonl", [all_sources[k] for k in sorted(all_sources)])

# Check each manifest source against working bytes, generated C and exact HEAD.
head = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip()
source_rows = []
for entry in manifest["sourceFiles"]:
    relative = entry["module"].replace(".", "/")
    source = repo/(relative+".lean")
    generated = repo/".lake/build/ir"/(relative+".c")
    assert sha(source) == entry["sourceSha256"]
    assert sha(generated) == entry["cSha256"]
    committed = subprocess.check_output(["git", "-C", str(repo), "show", head+":"+relative+".lean"])
    assert digest(committed) == entry["sourceSha256"]
    source_rows.append(dict(entry, path=str(source), committedHead=head))
assert len({r["module"] for r in source_rows}) == len(source_rows)
emit("lean-source-fingerprints.jsonl", source_rows)

selected_dir = out/"selected-c"
selected_dir.mkdir()
functions = {}
module_rows = []
for module, text, original, expected in inputs:
    row = object_map[module]
    assert sha(original) == expected == row["originalSha256"]
    assert digest(text.encode()) == row["compiledCSha256"]
    assert sha(row["object"]) == row["objectSha256"]
    snapshot = selected_dir/(module+".c")
    snapshot.write_text(text)
    module_rows.append(dict(row, selectedC=str(snapshot)))
    for match in helper.FUNC.finditer(text):
        name = match[1]
        assert name not in functions, name
        body = text[match.start():helper.end_brace(text, match.start())]
        functions[name] = (module, body)
assert sum(not n.startswith("initialize_") for n in functions) == closure["functions"]
assert sum(n.startswith("initialize_") for n in functions) == closure["modules"]
emit("selected-modules.jsonl", module_rows)
# Every retained closed value is assigned by the producer-rewritten initializer.
closed_rows = []
for module, text, original, expected in inputs:
    initializer = functions["initialize_"+module.replace(".", "_")][1]
    for global_name, value_init in re.findall(r"^(\w+) = (_init_\w+)\(\);$", initializer, re.M):
        assert value_init in functions
        value_module, value_body = functions[value_init]
        closed_rows.append({"name": global_name, "module": module, "valueInitializer": value_init, "valueInitializerModule": value_module, "valueInitializerSha256": digest(value_body.encode()), "moduleInitializerSha256": digest(initializer.encode()), "persistentMark": "lean_mark_persistent("+global_name+");" in initializer})
assert len({r["name"] for r in closed_rows}) == len(closed_rows) == closure["closedValues"]
emit("closed-values.jsonl", sorted(closed_rows, key=lambda row: row["name"]))


# Lexical references are conservative token accounting, not a call-graph proof.
origin = re.compile(r"Lean_(?:Elab|Meta|Parser|Environment|Kernel|Compiler|Server|Widget)")
forbidden = re.compile(r"\b(?:lean_expr_\w*|lean_environment_\w*|lean_kernel_\w*|lean_import_modules|l_Lean_Expr_\w*|l_Lean_Environment_\w*|l_Lean_Kernel_\w*)\b")
call_spelling = re.compile(r"\b([A-Za-z_]\w*)\s*\(")
ignored = {"if", "for", "while", "switch", "sizeof", "return"}
external_users = {}
function_rows = []
for name, (module, body) in sorted(functions.items()):
    tokens = set(helper.IDENT.findall(body))
    refs = sorted((tokens & functions.keys()) - {name})
    calls = sorted(set(call_spelling.findall(body)) - functions.keys() - ignored)
    for call in calls:
        external_users.setdefault(call, []).append(name)
    function_rows.append({"name": name, "module": module, "initializer": name.startswith("initialize_"), "bodySha256": digest(body.encode()), "bytes": len(body.encode()), "generatedReferences": refs, "otherCallSpellings": calls, "originNameCandidate": bool(origin.search(name)), "forbiddenLexicalHits": sorted(set(forbidden.findall(body)))})
emit("functions.jsonl", function_rows)
emit("other-call-spellings.jsonl", [{"spelling": k, "users": v, "boundary": "Unclassified lexical call spelling; may be native runtime, macro, cast, or indirect call."} for k, v in sorted(external_users.items())])

def nm_rows(args, filename):
    raw = subprocess.check_output(["nm", *args, "--format=posix", str(native/"direct-check")], text=True)
    (out/filename).write_text(raw)
    rows = []
    for line in raw.splitlines():
        fields = line.split()
        assert 2 <= len(fields) <= 4, line
        name, kind = fields[:2]
        rows.append({"name": name, "type": kind, "address": fields[2] if len(fields)>2 else None, "size": fields[3] if len(fields)>3 else None, "exactGeneratedDefinition": name in functions})
    return rows

defined = nm_rows(["-S", "--defined-only"], "defined-symbols.txt")
undefined = nm_rows(["--undefined-only"], "undefined-symbols.txt")
emit("defined-symbols.jsonl", defined)
emit("undefined-symbols.jsonl", undefined)
text_symbols = [r for r in defined if r["type"] in "TtWwIi"]
linked = {r["name"] for r in defined}
emit("generated-link-presence.jsonl", [{"name": n, "exactELFSymbolPresent": n in linked, "boundary": "Absent exact names may be inlined, optimized, or discarded; no equivalence inferred."} for n in sorted(functions)])
# Account for remaining text symbols without declaring their implementations safe.
# Matching names in input objects/archives are candidates, not a linker map.
native_names = {r["name"] for r in text_symbols if not r["exactGeneratedDefinition"]}
origins = {n: [] for n in native_names}
archive_rows = []
input_objects = [pathlib.Path(r["object"]) for r in objects] + [native/"bridge.o"]
archives = [pathlib.Path(p) for p in manifest["buildInputs"] if p.endswith(".a")]
for path in input_objects + archives:
    process = subprocess.Popen(["nm", "-A", "--defined-only", "--format=posix", str(path)], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    scanned = 0
    for line in process.stdout:
        symbol_origin, separator, tail = line.rstrip().partition(": ")
        assert separator, line
        fields = tail.split()
        assert 2 <= len(fields) <= 4, line
        scanned += 1
        if fields[0] in origins and fields[1] in "TtWwIi":
            origins[fields[0]].append({"input": str(path), "objectOrMember": symbol_origin, "symbolType": fields[1]})
    stderr = process.stderr.read()
    assert process.wait() == 0, stderr
    if path.suffix == ".a":
        archive_rows.append({"path": str(path), "sha256": sha(path), "definedSymbolRowsScanned": scanned})
        assert sha(path) == manifest["buildInputs"][str(path)]
emit("archive-fingerprints.jsonl", archive_rows)
demangled = subprocess.check_output(["c++filt"], input="\n".join(sorted(native_names))+"\n", text=True).splitlines()
assert len(demangled) == len(native_names)
emit("native-text-origins.jsonl", [{"name": n, "demangled": demangled[i], "candidateOrigins": origins[n], "boundary": "Name-based candidate origins only; not exact link attribution or semantic approval."} for i, n in enumerate(sorted(native_names))])
emit("build-input-fingerprints.jsonl", [{"path": p, "sha256": h} for p, h in sorted(manifest["buildInputs"].items())])
# These are observed retained link inputs, not a recovered compiler link map.
bridge_source = native/("bridge-"+manifest["bridgeSha256"]+".c")
assert sha(bridge_source) == manifest["bridgeSha256"]
link_inputs = [native/"bridge.o", native/"initialize.c", bridge_source]
emit("retained-link-input-fingerprints.jsonl", [{"path": str(p), "sha256": sha(p), "bytes": p.stat().st_size, "boundary": "Current retained input fingerprint; intermediate initializer object and exact linker attribution unavailable."} for p in link_inputs])

# Snapshot current dynamic resolution; this does not retroactively pin prior runs.
ldd = subprocess.check_output(["ldd", str(native/"direct-check")], text=True)
(out/"dynamic-resolution.txt").write_text(ldd)
dynamic_paths = sorted(set(re.findall(r"(?:=>\s+|^\s*)(/[^\s]+)", ldd, re.M)))
emit("dynamic-library-fingerprints.jsonl", [{"path": p, "sha256": sha(p), "bytes": pathlib.Path(p).stat().st_size, "boundary": "Current census environment resolution only; not source/compiler adequacy."} for p in dynamic_paths])
summary = {"schema": "memory-runtime-census-v1", "checkedHead": head, "censusScriptSha256": sha(pathlib.Path(__file__)), "binarySha256": manifest["executable"], "producerSha256": sha(producer), "closure": closure, "leanSourceFingerprints": len(source_rows), "generatedSourceFingerprints": len(all_sources), "selectedModules": len(inputs), "selectedFunctions": len(functions), "nonInitializerFunctions": closure["functions"], "initializerFunctions": closure["modules"], "closedValueFingerprints": len(closed_rows), "definedELFSymbols": len(defined), "undefinedELFSymbols": len(undefined), "textELFSymbols": len(text_symbols), "textSymbolsWithoutExactGeneratedName": sum(not x["exactGeneratedDefinition"] for x in text_symbols), "originNameCandidates": sum(x["originNameCandidate"] for x in function_rows), "functionsWithForbiddenLexicalHits": sum(bool(x["forbiddenLexicalHits"]) for x in function_rows), "otherCallSpellings": len(external_users), "nativeTextSymbolsWithCandidateOrigins": sum(bool(v) for v in origins.values()), "nativeTextSymbolsWithoutCandidateOrigins": sum(not v for v in origins.values()), "archiveFingerprints": len(archive_rows), "buildInputFingerprints": len(manifest["buildInputs"]), "dynamicLibraryFingerprints": len(dynamic_paths), "retainedLinkInputFingerprints": len(link_inputs), "coverage": "Every producer-selected function/initializer and closed value, every traversed generated-C source, every sourceFiles entry, and every nm defined/undefined row is enumerated. No row excluded by a safety classification.", "limitations": ["Finite source/object/symbol inventory, not C-parser completeness or semantic certification.", "Lexical references and names do not prove absence of forbidden functionality, including indirect calls or native runtime code.", "Native and dynamically linked code beyond generated definitions remains unclassified; no RUNTIME_GATE_PASS.", "No compiler/source adequacy, browser execution, or closure of four pending storage diamonds."], "files": []}
for f in sorted(out.rglob("*")):
    if f.is_file():
        summary["files"].append({"path": str(f.relative_to(out)), "bytes": f.stat().st_size, "sha256": sha(f)})
(out/"summary.json").write_text(json.dumps(summary, indent=2)+"\n")
print(json.dumps({k:v for k,v in summary.items() if k != "files"}, sort_keys=True))
