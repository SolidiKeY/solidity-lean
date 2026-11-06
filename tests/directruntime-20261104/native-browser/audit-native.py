"""External binary/trace evidence for the native baseline; not a kernel proof."""
import hashlib
import json
import pathlib
import re
import subprocess
import sys
import types

root = pathlib.Path.cwd()
output = root / "docs/benchmarks/directruntime-2026-11-04/before"
if (output/"native-audit.json").exists() or (output/"native-build.json").exists():
    raise SystemExit("Refusing to overwrite baseline audit evidence")
runtime = root / ".lake/direct-native"
prefix = pathlib.Path("/workspace/.setup/tools/lean-4.24.0-linux")
sha = lambda b: hashlib.sha256(b).hexdigest()
file_sha = lambda p: sha(p.read_bytes())
manifest = json.loads((runtime / "build.json").read_text())
inputs = json.loads((output / "inputs/inputs.json").read_text())
binary = runtime / "direct-check"
if file_sha(binary) != manifest["executable"]:
    raise ValueError("binary changed")
for entry in manifest["sourceFiles"]:
    if file_sha(root / (entry["module"].replace(".", "/") + ".lean")) != entry["sourceSha256"]:
        raise ValueError("stale source: " + entry["module"])
    if file_sha(root / ".lake/build/ir" / (entry["module"].replace(".", "/") + ".c")) != entry["cSha256"]:
        raise ValueError("stale generated C: " + entry["module"])
if file_sha(root / "web/browser/direct-bridge.c") != manifest["bridgeSha256"]:
    raise ValueError("stale bridge")
(output / "native-build.json").write_text(json.dumps(manifest, indent=2)+"\n")
closure_file = root / "scripts/direct-runtime-closure.py"
closure_bytes = closure_file.read_bytes()
helper = types.ModuleType("closure")
exec(compile(closure_bytes, str(closure_file), "exec"), helper.__dict__)
undefined = subprocess.check_output(["nm", "--undefined-only", "--format=posix", str(prefix/"lib/lean/libleanrt.a")], text=True)
extracted, stats = helper.extract(root, runtime/"runtime", native_roots=set(re.findall(r"^(\w+) U ", undefined, re.M)))
if stats != manifest["closure"]:
    raise ValueError("closure no longer matches build")
identity = {
    "closureScriptSha256": sha(closure_bytes),
    "closure": stats,
    "modules": [{"module": name, "originalCSha256": original, "compiledCSha256": sha(text.encode())}
                for name, text, path, original in extracted],
    "headers": {str(p.relative_to(prefix)): file_sha(p) for p in sorted((prefix/"include/lean").rglob("*.h"))},
    "compilers": {str(p): file_sha(p) for p in [prefix/"bin/lean", prefix/"bin/lake", prefix/"bin/leanc", prefix/"bin/clang", pathlib.Path("/usr/bin/x86_64-linux-gnu-gcc-14")]},
    "runtimeArchives": {str(p.relative_to(prefix)): file_sha(p)
                        for p in sorted(set((prefix/"lib").glob("*.a")) | set((prefix/"lib/lean").glob("*.a")) | set((prefix/"lib/glibc").glob("*.a")))},
    "linkFlags": subprocess.check_output([str(prefix/"bin/leanc"), "--print-ldflags"], text=True).strip(),
    "nativeRuntimeSourceCommit": subprocess.check_output(["git", "-C", str(root/".lake/native-browser-lean4"), "rev-parse", "HEAD"], text=True).strip(),
    "nativeRuntimeSourceStatus": subprocess.check_output(["git", "-C", str(root/".lake/native-browser-lean4"), "status", "--porcelain"], text=True),
    "binarySha256": file_sha(binary), "binaryBytes": binary.stat().st_size,
    "boundary": "Post-build external identity inventory; supplements the original incomplete native build manifest.",
}
(output/"native-input-identities.json").write_text(json.dumps(identity, indent=2)+"\n")
symbols = subprocess.check_output(["nm", "-C", "--defined-only", str(binary)], text=True)
dynamic = subprocess.check_output(["readelf", "-d", str(binary)], text=True)
(output/"native-symbols.txt").write_text(symbols)
(output/"native-dynamic.txt").write_text(dynamic)
blocked = re.compile(r"\b(?:lean_initialize|lean_import_modules|l_Lean_importModules|l_Lean_(?:Elab|Meta|Environment|Kernel)_\w*|initialize_Lean_(?:Elab|Meta|Environment|Kernel)\w*)\b|lean::(?:environment|type_checker|module_mgr)\b")
symbol_failures = [line for line in symbols.splitlines() if blocked.search(line)]
wire, transcript = [], []
for round in range(3):
    for trial in inputs["trials"]:
        source = pathlib.Path(trial["source"])
        fixture = pathlib.Path(trial["fixture"])
        encoded = json.dumps(trial["request"], separators=(",", ":"), ensure_ascii=False).encode()
        # JS JSON.stringify escapes neither ordinary Unicode nor slashes for this AST.
        if sha(encoded) != trial["requestSha256"] or file_sha(source) != trial["sourceHash"] or file_sha(fixture) != trial["fixtureSha256"]:
            raise ValueError("request/source/AST identity changed: " + trial["name"])
        wire.append(encoded+b"\n")
        transcript.append({"round": round, "name": trial["name"], "sourceSha256": trial["sourceHash"], "requestSha256": sha(encoded)})
payload = b"".join(wire)
trace = output/"native-runtime.strace"
command = ["strace", "-f", "-qq", "-e", "trace=%file,%process,%network", "-o", str(trace), str(binary)]
run = subprocess.run(command, input=payload, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
(output/"native-trace-results.jsonl").write_bytes(run.stdout)
(output/"native-trace-stderr.txt").write_bytes(run.stderr)
rows = [json.loads(line) for line in run.stdout.splitlines()]
if not rows or rows[0] != {"ready": True}:
    raise ValueError("missing actual native startup handshake")
replies = rows[1:]
failures = []
for i, reply in enumerate(replies):
    expected = transcript[i] if i < len(transcript) else {}
    result = reply.get("results", [])
    if len(result) != 1 or result[0].get("status") != "proved" or result[0].get("function") != expected.get("name"):
        failures.append({"index": i, "expected": expected, "reply": reply})
loads = trace.read_text()
load_failures = [line for line in loads.splitlines()
                 if re.search(r"\.(?:olean|ilean)(?:\W|$)|execve\(\"[^\"]*/(?:lean|lake)\"", line)]
result = {
    "command": command, "exitCode": run.returncode, "requests": transcript,
    "wireSha256": sha(payload), "binarySha256": file_sha(binary), "backend": "generated-c-native",
    "expectedRequests": 249, "actualReplies": len(replies), "semanticFailures": failures,
    "blockedDefinedSymbols": symbol_failures, "forbiddenRuntimeLoads": load_failures,
    "traceSha256": file_sha(trace),
    "passed": run.returncode == 0 and len(replies) == 249 and not failures and not symbol_failures and not load_failures,
    "boundary": "Untimed external binary and syscall observations. Source hashes identify sent requests; the binary does not attest source hashes. Not intrinsic semantic equivalence or the missing exact Identity diamond proof.",
}
(output/"native-audit.json").write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps({k: result[k] for k in ["passed", "expectedRequests", "actualReplies", "blockedDefinedSymbols", "forbiddenRuntimeLoads"]}))
if not result["passed"]:
    raise SystemExit(1)
