"""Check hardened extraction against the exact saved pre-change native closure."""
import hashlib, json, pathlib, re, subprocess, types
root=pathlib.Path.cwd()
evidence=root/"docs/benchmarks/directruntime-2026-11-04"
out=evidence/"closure-hardening.json"
if out.exists(): raise SystemExit("refusing evidence overwrite")
script=root/"scripts/direct-runtime-closure.py"
helper=types.ModuleType("closure")
exec(compile(script.read_bytes(),str(script),"exec"),helper.__dict__)
undefined=subprocess.check_output(["nm","--undefined-only","--format=posix","/workspace/.setup/tools/lean-4.24.0-linux/lib/lean/libleanrt.a"],text=True)
roots=set(re.findall(r"^(\w+) U ",undefined,re.M))
outputs,stats=helper.extract(root,root/".lake/direct-native/runtime",native_roots=roots)
before=json.loads((evidence/"before/native-input-identities.json").read_text())
modules=[dict(module=n,originalCSha256=s,compiledCSha256=hashlib.sha256(t.encode()).hexdigest()) for n,t,p,s in outputs]
assert stats==before["closure"]
assert modules==before["modules"]
subprocess.run(["python3","scripts/test-direct-runtime-closure.py"],check=True)
subprocess.run(["python3","tests/directruntime-20261104/native-browser/closure-regressions.py"],check=True)
out.write_text(json.dumps(dict(passed=True,syntheticTests=9,closureUnchanged=True,moduleHashesUnchanged=True,nativeArchiveUndefinedRoots=len(roots),closure=stats,closureScriptSha256=hashlib.sha256(script.read_bytes()).hexdigest(),boundary="Extraction and targeted fail-closed regression only; no rebuilt binary or after-performance claim"),indent=2)+"\n")
print("PASS: 9 tests; exact current 200-module extracted C unchanged")
