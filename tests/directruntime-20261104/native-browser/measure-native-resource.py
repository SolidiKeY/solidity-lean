"""Measure the native process alone; no compiler or tracing in its rusage."""
import hashlib,json,pathlib,resource,subprocess,time
root=pathlib.Path.cwd();out=root/"docs/benchmarks/directruntime-2026-11-04/before"
if (out/"native-process-resource.json").exists():raise SystemExit("Refusing resource receipt overwrite")
inputs=json.loads((out/"inputs/inputs.json").read_text());manifest=json.loads((root/".lake/direct-native/build.json").read_text())
binary=root/".lake/direct-native/direct-check"
sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(binary.read_bytes())==manifest["executable"]
requests=[];names=[]
for round in range(3):
 for trial in inputs["trials"]:
  encoded=json.dumps(trial["request"],separators=(",",":"),ensure_ascii=False).encode()
  assert sha(encoded)==trial["requestSha256"]
  assert sha(pathlib.Path(trial["source"]).read_bytes())==trial["sourceHash"]
  requests.append(encoded+b"\n");names.append(trial["name"])
wire=b"".join(requests);start=time.monotonic()
run=subprocess.run([str(binary)],input=wire,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120)
wall=time.monotonic()-start;usage=resource.getrusage(resource.RUSAGE_CHILDREN)
rows=[json.loads(line) for line in run.stdout.splitlines()]
failures=[]
for i,row in enumerate(rows[1:]):
 r=row.get("results",[])
 if len(r)!=1 or r[0].get("status")!="proved" or i>=len(names) or r[0].get("function")!=names[i]:
  failures.append({"index":i,"reply":row})
passed=run.returncode==0 and rows[0]=={"ready":True} and len(rows)==250 and not failures
result={"passed":passed,"backend":"generated-c-native","binarySha256":manifest["executable"],"wireSha256":sha(wire),"expectedRequests":249,"actualReplies":len(rows)-1,"exitCode":run.returncode,"wallSeconds":wall,"nativeMaxRssKiB":usage.ru_maxrss,"userSeconds":usage.ru_utime,"systemSeconds":usage.ru_stime,"failures":failures,"stderr":run.stderr.decode(),"boundary":"Fresh untimed-throughput run for native process rusage only. Per-request latency remains the independent unchanged benchmark's three-round report; no compiler or trace process is in this rusage."}
(out/"native-process-resource.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result))
if not passed:raise SystemExit(1)
